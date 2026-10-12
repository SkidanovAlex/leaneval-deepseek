import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.CentreBox
import Submission.Work.BoseB4.AntiNormal
import Submission.Work.BoseB4.DGamma_diag
import Submission.Work.BoseB4.DGamma_one
import Submission.Work.BoseB4.DGamma_quadform
import Submission.Work.BoseB4.Kafz_lower_bound_H2nd
import Submission.Work.BoseB4.Kafz_lower_bound_pointwise
import Submission.Work.BoseB4.a0_comp_a0d_sq
import Submission.Work.BoseB4.annC_creC_ccr
import Submission.Work.BoseB4.dGamma_diag_nonneg
import Submission.Work.BoseB4.monoOp_11_00_numOp
import Submission.Work.BoseB4.monoOp_lift_basic
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDict` — the box ↔ model dictionary, upstream vocabulary (BF3b)

This module is a **decoupled copy** of the vocabulary that the box → model dictionary
(BF3b of `Submission/Work/BoseBoxFock/box_to_model`) needs.  It imports only the
*upstream* layers (`Work.BoseB4`, `Work.BoseK15`, the root corpus module `CentreBox`),
never `Work.BoseBoxFock.Defs`, so that the dictionary can be developed and delegated
while the box-side a-priori subtree (`Work.BoseFixB1B`) is being rewritten by other
agents.  The definitions here are syntactically the ones of
`Submission/Work/BoseBoxFock/bridge_defs.lean` (`realIPn`, `modeMult`, `modeProd`,
`boxCoeff`, `boxCompress`) plus the two maps of the dictionary:

* `boxRealise` — the isometric realisation of the model monomials `x^α` on the box,
  `x^α ↦ (α!/√(d!)) • M_α` (`M_α = modeProd e d α`).  See
  `BF3B_PLAN_S4.md` §0: the constant `α!/√(d!)` is forced by `‖M_α‖² = d!/α!` and the
  model's derivative convention `(∂_l p) α = α_l p(α−e_l)`;
* `boxAnn` — the box annihilation of the mode `e l` on the `d`-particle space,
  `(boxAnn e l Θ)(y) = √(d+1)·∫_z conj(e l z)·Θ(z,y)`.

The two dictionary identities to be proved about them are

    ∫ conj(boxRealise e d Ψ)(boxRealise e d Ψ) = bomb m Ψ Ψ        (isometry)
    boxRealise e d (ann m l Ψ) = boxAnn e l d (boxRealise e (d+1) Ψ) (intertwining)

on the degree-`(d+1)` (resp. `d`) part; together with the orthonormality of the mode
products they give every row of the model Hamiltonian as the corresponding row of the
first-quantised box word (`Work.BoseB4.bomb_dGamma_expand`, `DGamma_quadform`).

The final assembly in `box_to_model.lean` is bridged to this vocabulary by `rfl`
(the defining terms are identical).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The one-particle space of the box (definitionally `Submission.BoseGases.X 1`). -/
abbrev Sp : Type := EuclideanSpace ℝ (Fin 3)

/-- The `n`-particle configuration space (definitionally `Submission.BoseGases.X n`). -/
abbrev Xn (n : ℕ) : Type := Fin n → Sp

/-! ## 1. The mode products -/

/-- The real part of the `n`-body `L²` pairing of complex functions. -/
noncomputable def realIPn (n : ℕ) (f g : Xn n → ℂ) : ℝ :=
  ∫ x : Xn n, ((starRingEnd ℂ) (f x) * g x).re

/-- The complex `n`-body `L²` pairing of complex functions. -/
noncomputable def cIPn (n : ℕ) (f g : Xn n → ℂ) : ℂ :=
  ∫ x : Xn n, (starRingEnd ℂ) (f x) * g x

/-- The occupation multi-index of a labelling `σ : Fin n → Fin m`. -/
noncomputable def modeMult {m n : ℕ} (σ : Fin n → Fin m) : Fin m →₀ ℕ :=
  ∑ k : Fin m, Finsupp.single k ((Finset.univ.filter fun i => σ i = k).card)

/-- The **symmetric mode product** of a multi-index `α` in the mode family `e`. -/
noncomputable def modeProd {m : ℕ} (e : Fin m → Sp → ℂ) (n : ℕ) (α : Fin m →₀ ℕ)
    (x : Xn n) : ℂ :=
  ∑ σ : Fin n → Fin m, (if modeMult σ = α then (1 : ℂ) else 0) * ∏ i : Fin n, e (σ i) (x i)

/-! ## 2. The realisation of the model on the box -/

/-- **The realisation of the model monomials on the box**: the `ℝ`-linear map sending
`Finsupp.single α 1` (the monomial `x^α`) to `(α!/√(d!)) • modeProd e d α` when
`|α| = d`, and to `0` on the other degrees.  It is an isometry from the degree-`d` part of
`RealFock m` (with the Bombieri form) into `L²(Xn d; ℂ)`. -/
noncomputable def boxRealise {m : ℕ} (e : Fin m → Sp → ℂ) (d : ℕ) :
    Work.BoseB4.RealFock m →ₗ[ℝ] (Xn d → ℂ) :=
  Finsupp.lsum ℝ fun α : Fin m →₀ ℕ =>
    if α.sum (fun _ k => k) = d then
      LinearMap.toSpanSingleton ℝ (Xn d → ℂ)
        ((Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) • modeProd e d α)
    else 0

/-- The defining value of `boxRealise` on a single monomial. -/
@[simp]
lemma boxRealise_single {m : ℕ} (e : Fin m → Sp → ℂ) (d : ℕ) (α : Fin m →₀ ℕ) :
    boxRealise e d (Finsupp.single α (1 : ℝ))
      = (if α.sum (fun _ k => k) = d then
          (Work.BoseB4.mfac α / Real.sqrt (d.factorial : ℝ) : ℝ) else 0) • modeProd e d α := by
  classical
  rw [boxRealise, Finsupp.lsum_single]
  by_cases h : α.sum (fun _ k => k) = d
  · rw [if_pos h, if_pos h, LinearMap.toSpanSingleton_apply, one_smul]
  · rw [if_neg h, if_neg h, LinearMap.zero_apply, zero_smul]

/-- The box annihilation of the mode `e l` on the `d`-particle space, with the
normalisation of the model's `Work.BoseB4.ann`: `(boxAnn e l Θ)(y) = √(d+1) ∫_z conj(e l z)
Θ(z,y)`.  (`Fin.cons z y` is the point `(z, y_0, …, y_{d-1})`.) -/
noncomputable def boxAnn {m : ℕ} (e : Fin m → Sp → ℂ) (l : Fin m) (d : ℕ)
    (Θ : Xn (d + 1) → ℂ) : Xn d → ℂ :=
  fun y => (Real.sqrt ((d : ℝ) + 1) : ℂ) * ∫ z : Sp, (starRingEnd ℂ) (e l z) * Θ (Fin.cons z y)

/-! ## 3. The compression (the vocabulary of `bridge_defs.lean`) -/

/-- The **model coefficient** of the box state `Φ` at the multi-index `α`. -/
noncomputable def boxCoeff {m : ℕ} (e : Fin m → Sp → ℂ) (n : ℕ) (ℓ : ℝ)
    (Φ : Xn n → ℝ) (α : Fin m →₀ ℕ) : ℝ :=
  (∫ x in Submission.BoseGases.abox n ℓ, (modeProd e n α x).re * Φ x)
    / Real.sqrt (n.factorial : ℝ)

/-- **The compression of a box state to the model** (`BF3b`). -/
noncomputable def boxCompress {m : ℕ} (e : Fin m → Sp → ℂ) (n : ℕ) (ℓ : ℝ)
    (Φ : Xn n → ℝ) : Work.BoseB4.RealFock m :=
  ∑ α ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin m)) n,
    Finsupp.single α (boxCoeff e n ℓ Φ α)

end Work.BoseDict
