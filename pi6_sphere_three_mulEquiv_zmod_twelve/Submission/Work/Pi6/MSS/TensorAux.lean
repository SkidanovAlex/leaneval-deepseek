import Mathlib
import Submission.Work.Pi6.MSS.TensorDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Auxiliary complexes for `Work.Pi6.MSS.tensorDual`

This file collects the two "naive" coefficient-extended complexes used in the proof of
`Work.Pi6.MSS.tensorDual`:

* `Work.Pi6.MSS.expTens 𝕜 C V` — the *chain* complex with `n`-th term `C.X n ⊗ V` and differential
  `C.d (n+1) n ▷ V` (the naive form of `Work.Pi6.MSS.tensorC 𝕜 C V`);
* `Work.Pi6.MSS.coTensC 𝕜 K W` — the *cochain* complex with `n`-th term `K.X n ⊗ W` and
  differential `K.d n (n+1) ▷ W`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

noncomputable section

/-- The "naive" coefficient extension of a chain complex `C` by a module `V`: the chain complex
with `n`-th term `C.X n ⊗ V` and differential `C.d (n+1) n ▷ V`.  It is the object which
`Work.Pi6.MSS.tensorC 𝕜 C V = C ⊗ (single₀ V)` is isomorphic to. -/
abbrev expTens (𝕜 : Type) [CommRing 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (V : ModuleCat 𝕜) :
    ChainComplex (ModuleCat 𝕜) ℕ :=
  ChainComplex.of (fun n => C.X n ⊗ V) (fun n => C.d (n + 1) n ▷ V) (fun n => by
    rw [← MonoidalCategory.comp_whiskerRight,
      HomologicalComplex.d_comp_d C (n + 1 + 1) (n + 1) n]
    simp)

@[simp]
theorem expTens_X (𝕜 : Type) [CommRing 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (V : ModuleCat 𝕜)
    (n : ℕ) : (expTens 𝕜 C V).X n = C.X n ⊗ V := rfl

@[simp]
theorem expTens_d (𝕜 : Type) [CommRing 𝕜] (C : ChainComplex (ModuleCat 𝕜) ℕ) (V : ModuleCat 𝕜)
    (n : ℕ) : (expTens 𝕜 C V).d (n + 1) n = C.d (n + 1) n ▷ V :=
  ChainComplex.of_d (fun n => C.X n ⊗ V) (fun n => C.d (n + 1) n ▷ V) n

/-- The "naive" coefficient extension of a cochain complex `K` by a module `W`: the cochain complex
with `n`-th term `K.X n ⊗ W` and differential `K.d n (n+1) ▷ W`. -/
abbrev coTensC (𝕜 : Type) [CommRing 𝕜] (K : CochainComplex (ModuleCat 𝕜) ℕ) (W : ModuleCat 𝕜) :
    CochainComplex (ModuleCat 𝕜) ℕ :=
  CochainComplex.of (fun n => K.X n ⊗ W) (fun n => K.d n (n + 1) ▷ W) (fun n => by
    rw [← MonoidalCategory.comp_whiskerRight,
      HomologicalComplex.d_comp_d K n (n + 1) (n + 1 + 1)]
    simp)

@[simp]
theorem coTensC_X (𝕜 : Type) [CommRing 𝕜] (K : CochainComplex (ModuleCat 𝕜) ℕ) (W : ModuleCat 𝕜)
    (n : ℕ) : (coTensC 𝕜 K W).X n = K.X n ⊗ W := rfl

@[simp]
theorem coTensC_d (𝕜 : Type) [CommRing 𝕜] (K : CochainComplex (ModuleCat 𝕜) ℕ) (W : ModuleCat 𝕜)
    (n : ℕ) : (coTensC 𝕜 K W).d n (n + 1) = K.d n (n + 1) ▷ W :=
  CochainComplex.of_d (fun n => K.X n ⊗ W) (fun n => K.d n (n + 1) ▷ W) n

/-- The `𝕜`-dual of a module, as an object of `ModuleCat 𝕜`. -/
abbrev dualMod (𝕜 : Type) [CommRing 𝕜] (V : ModuleCat 𝕜) : ModuleCat 𝕜 :=
  ModuleCat.of 𝕜 (↥V →ₗ[𝕜] 𝕜)

end

end Work.Pi6.MSS
