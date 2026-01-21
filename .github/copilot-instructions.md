# Clean - Lean4 ZK Circuit DSL

## Project Overview
Clean is an embedded Lean DSL for writing formally verified zero-knowledge circuits. It targets arithmetizations like AIR, PLONK, and R1CS. Circuits are defined in Lean4, proven correct, and can be compiled to backends like plonky3.

## Build & Development
```bash
lake build          # Build the project
```
Open in VS Code with the `lean4` extension for inline compiler feedback.

## Architecture

### Circuit Monad (`Clean/Circuit/`)
The `Circuit F α` monad accumulates `Operation`s (constraints, witness creation, lookups) using `do` notation:
```lean
def myCircuit : Circuit F Unit := do
  let x ← witness (fun _ => 1)   -- witness a variable
  assertZero (x - 1) * x         -- add constraint
```

### Formal Circuits (`FormalCircuit`, `GeneralFormalCircuit`, `FormalAssertion`)
Circuits require proofs of **soundness** and **completeness**:
- `FormalCircuit`: Function-like circuits with input→output specs
- `GeneralFormalCircuit`: Mixed assertion/function behavior (e.g., `toBits` which constrains input range as side effect)
- `FormalAssertion`: Pure constraints without output

### Provable Types (`ProvableType`)
Types usable in circuits must implement `ProvableType`, enabling flattening to/from field element vectors. Custom structs must derive this. See `Clean/Types/` for examples like `U32`, `U64`, `Byte`.

### Gadgets (`Clean/Gadgets/`)
Reusable circuit building blocks: `Boolean`, `Bits`, `Equality`, `Addition32`, `Rotation64`, etc. New gadgets should follow the `FormalCircuit` pattern with soundness/completeness proofs.

### Tables & Lookups (`Clean/Table/`, `Clean/Circuit/Lookup.lean`)
`Table` models lookup tables via a `Contains` predicate. Use `StaticTable` or `LookupCircuit` constructions to guarantee instantiability.

## Proof Tactics

### Opening Proofs
```lean
soundness := by
  circuit_proof_start [MySubgadget.circuit]  -- unfolds and introduces hypotheses
  simp only [circuit_norm]                    -- normalize to standard forms
```

### Key Tactics
- `circuit_proof_start`: Introduces proof context (env, input_var, h_holds, etc.)
- `simp only [circuit_norm]`: Normalizes circuit expressions; add custom unfolds: `simp only [circuit_norm, MyDef]`
- **Avoid unfolding loops** like `Circuit.foldl`—use `circuit_norm` to get `∀ i < m, ...` statements

### Closing Branches
When goal reduces to pure math:
- `omega`/`linarith` for naturals and arithmetic
- `ring_nf`/`field_simp` for field arithmetic
- `simp_all`, `aesop`, `grind` for simple goals

## Code Conventions

### Simp Sets
**Never use `@[simp]`**. Add lemmas to `@[circuit_norm]` instead:
```lean
@[circuit_norm] lemma my_lemma : ...
```

### Formatting (differs from Mathlib)
- Named parameters: `(F:=F)` (no spaces around `:=`)
- Polynomial multiplication: `2*a*b` (no spaces)
- Exponents: `2^(n+1)` (no spaces inside parens)

## Backend Integration
The `backends/plonky3/` directory contains a Rust backend that:
1. Imports Clean circuits as plonky3 AIR
2. Generates execution traces
3. Proves/verifies using plonky3

## Key File Patterns
- **New gadget**: Create in `Clean/Gadgets/`, define `main`, `Spec`, prove `soundness`/`completeness`
- **New table**: Add to `Clean/Tables/`, use `StaticTable.fromStatic` or `LookupCircuit`
- **New type**: Add to `Clean/Types/`, implement `ProvableType`
