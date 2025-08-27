## Dev notes

There are three main dialects of IR we want to support - these must exist in the same textual language and be loaded 
from the frontend.

Specifically

### The executable IR

This IR can be interpreted over over single states, or the meet-of-all-traces solution computed with
abstract interpretation.

- We want to be able to transform this IR to improve the abstraction and readability notably:
  - Introduce procedure parameters
  - Introduce SSA form
  - simplify binary operations
  - perform type analysis to perform various kinds of strength reduction (e.g. reduce bitvector widths)
  - perform memory shape analysis to scalarise memory accesses, and lift the memory access patterns
  - infer the shape of the memory stack and move it to the abstract stack; similar to mem2reg
  - replace general precise operations with more specific abstract operations
    - E.g. bitvector to integer conversion
    - Stack memory access to `alloca`/`free`
    - Memory access to scalar accesses

This means at differnet points in time the IR contains a different set of primitive operations: it is more convenient to be
able to write an analysis over the specific set of primitive operations that are used, and have the type checker tell you
what this set is.

This also applies to the high level structure: the call/return structure, and control flow structure e.g. paramter lists: different statement types?
E.g. rather than the dynamic structural invariant that every procedures in and out parametter list is empty we want an IR dialect that does not contain parameter 
lists.

- ocamlgraph etc make it easier to redefine the CFG with different edge types to only expose the information an analysis cares about.
  - e.g. paramter forms and SSA forms
  - binsec/codex/tai make the expression tree parametric in the variable type to make it more convenient to describe non-SSA and SSA form in an ideal way
  - it is crucial that it is trivial to relate a CFG back to a textual represetnation for debugging, and that this representation is stable and not (too) lossy.

```ocaml
type 'var expr_node = private 
    | E_Var of 'var
    | E_Const of Z.t
    | E_Binop of 'var expr * binop * 'var expr
    | E_Unop of unop * 'var expr
    | E_IfThenElse of 'var expr * 'var expr * 'var expr
and 'var expr = 'var expr_node Hashconsing.hash_consed
```

- a reasonable middle ground is to have IR that is parametric (at compile time) in the set of primitive operations it contains.

> We do not want this to prevent code reuse however.

#### Analysis Efficiency

- We want to make it easy to define integer identifiers for efficient use as keys in mergeable ordered maps
  - Hashconsing provides this but keys are not contiguous
  - We can use declarations lists to make a contiguous set of integer identifiers for variables that are looked up
    by name and can be used as keys for arrays/bitsets

### The specification IR

Consider a specification of strlen for information flow:

```
/**
@requires \exists n :: mem[str + n] == '\0' && \forall i:size_t :: str <= i < str + n . mem[str + i] != '\0'
@ensures \forall n:size_t, i:size_t :: str <= i < str + n && mem[str + i] != '\0' && mem[str + n] == '\0' . str[i] == old(i) && gamma(str[i]) == old(gamma(str[i]))  
  && str[n] == old(n) && gamma(str[n]) == old(gamma(str[n])) 
@ensures mem[str + out] = '\0' && gamma(out) = (\min i:size_t :: str <= i < str + mem . gamma(mem[str + i]))
*/
strlen(bv64 str) -> (out:bv64) ;
```


For this we requrie the members of the expression tree which are interleaved with the executable-subset operations (`<=`, `==`, `+`),
but are not possible directly evaluate:

- quantifiers `\forall`, `\exists`
- pure (non-side-effecting) memory accesses (`mem[str]`)
- aggregates (`\min`) - although this is executable and needed to encode gamma flow
- requires and ensures specification attached to procedures

> we would like to reuse the definitions of substitution etc to encode this specification

- in some cases we would like ti to be possible to interpret this specification in static analyses
  - the current case is an interproc copyprop analysis may want to keep unneeded paramters that can be inlined 
    (e.g those which are constants) so it is possible to prove a specification about them later, or discharge the proof immediately.
    - this means at least sharing the variable representation so free variables are compatible.

### Macro IR

Currently basil specifications look like:

```
Globals: 
z: bv32
x: bv32
secret: bv32

L: z -> true, x -> z != 1bv32, secret -> false
Rely: old(Gamma_x) ==> Gamma_x, old(z) == 1bv32 ==> z == old(z)
Guarantee: old(z) == 2bv32 ==> old(z) == z && old(x) == x
```

This is fairly abstract and is re-interpreted with different binaries and different structures. 

- You can write `R0` to refer to registers, the parameter analysis then rewrites thesee along with the analysis so they continue to match the IR representation
- `x`, `z` are global variables which get lowered to pure memory accesses in specification and assertions driven by the symbol table, they are also given a different
  interpretation for each binary.
- `L` gets lowered to an `ite` ONLY int he boogie level and is not currently representible in the IR
- Infix operations like `!=` get inferred to the correct type and lowered to the correct operations

The upshot of this is:

- the specification acts like a macro system, this improves the reusablility of the specification but makes its semantics much less clear and its evaluation more complicated.
  Especially since it is in a different ast to the IR.
  - I would rather lean on the side of a clearer evaluation system than maximal code re-use (ie. enforece an evaluation order tied to the IR with the same semantics) and
    obvious referents of every spec symbol in some IR structure.
- Even without this we would likely want some level of desugaring from the IR into the minimal subset that is more convenient for analysis or verifier encoding.

> Is this a separate AST or some superset of the executble + specification AST?


# Other Constraints

- verification ease, e.g. with Why3 camelier
