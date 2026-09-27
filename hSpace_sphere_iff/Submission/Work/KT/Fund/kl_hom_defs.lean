import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kl_defs

/-!
# `Work.KT.Fund.kl_hom_defs` — the linear homotopy `z • E + t • (E b) + (1 - E)`

This file defines the interpolation between the two matrices

* `klV X n b E = z • E + E b + (1 - E)`  (the "inside" factor, `t = 1`), and
* `klV0 X n E   = z • E + (1 - E)`       (the Bott unit, `t = 0`),

used in `Work.KT.Fund.kl_v_cls`: the homotopy
`H(x, t, z) = z • E(x) + t • (E b)(x) + (1 - E(x))` over `(X × I) × S¹`.

The two slices of `klHom` are `klV` and `klV0` (`klHom_slice1`, `klHom_slice0`), and the
pointwise evaluation formula is `klHom_apply`.
-/

namespace Work.KT.Fund

open Matrix

noncomputable section

/-- The continuous map `I → ℂ`, `t ↦ t`. -/
def uintCoe : C(unitInterval, ℂ) :=
  ⟨fun t => (t : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

@[simp] lemma uintCoe_apply (t : unitInterval) : uintCoe t = (t : ℂ) := rfl

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The `t`-coordinate on `(X × I) × S¹`, as a `ℂ`-valued continuous function. -/
def tCoeff : C((X × unitInterval) × Sph ℂ, ℂ) :=
  uintCoe.comp ((ContinuousMap.snd : C(X × unitInterval, unitInterval)).comp
    (ContinuousMap.fst : C((X × unitInterval) × Sph ℂ, X × unitInterval)))

@[simp] lemma tCoeff_apply (p : (X × unitInterval) × Sph ℂ) :
    tCoeff X p = ((p.1.2 : unitInterval) : ℂ) := rfl

/-- Pull a matrix over `C(X, ℂ)` back along the projection `X × I → X`. -/
def pullI {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C(X × unitInterval, ℂ) :=
  M.map (fun f => f.comp (ContinuousMap.fst : C(X × unitInterval, X)))

@[simp] lemma pullI_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n)
    (q : X × unitInterval) : pullI X M i j q = M i j q.1 := rfl

/-- The homotopy matrix `z • E + t • (E b) + (1 - E)` over `(X × I) × S¹`. -/
def klHom (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n) (Fin n) C((X × unitInterval) × Sph ℂ, ℂ) :=
  klz (X × unitInterval) • klP (X × unitInterval) (pullI X E)
  + tCoeff X • klP (X × unitInterval) (pullI X (E * b))
  + (1 - klP (X × unitInterval) (pullI X E))

end

end Work.KT.Fund
