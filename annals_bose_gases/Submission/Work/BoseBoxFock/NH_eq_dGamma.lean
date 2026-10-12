import ChallengeDeps
import Submission.Work.BoseBoxFock.boxTwinDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.NH_eq_dGamma` — the `NH` row of the honest family is a `dGamma`

`Work.BoseBoxFock.tildeDataHon` sets the honest `n₊^H` to the ladder sum

    `NH = (1/32) Σ_{k ∈ excited} η_H(k) · (creOf (f k) ∘ annOf (f k))`

on the model Fock space `RealFock m`.  The one-body dictionary
(`Work.BoseDict.bomb_dGamma_slot`, `Work.BoseDict.boxRealise_dGamma`) needs that operator
written as the second quantisation `dGamma m T` of a one-particle operator `T`; this file
identifies

    `T = (1/32) Σ_{k ∈ excited} η_H(k) · |f k⟩⟨f k|`

via the rank-one bridge `creOf w ∘ annOf v = dGamma (|w⟩⟨v|)`
(`Work.BoseB4.creOf_annOf_eq_dGamma`) and the two structural facts about `dGamma`:

* `dGamma_smul` — `dGamma m` is `ℝ`-homogeneous in the one-particle operator;
* `dGamma_finsetSum` — `dGamma m` is additive over finite sums;

both immediate from the defining double sum `dGamma T = Σ_{ij} (T e_j)_i · a_i† a_j`.

Everything here is `sorry`-free and elementary.
-/

noncomputable section

open scoped BigOperators

open Work.BoseB4

namespace Work.BoseBoxFock

set_option autoImplicit false

/-! ## 1. `dGamma` is linear in the one-particle operator -/

/-- `dGamma m` is homogeneous: the second quantisation of `c • T` is `c • dGamma m T`
(immediate from the defining double sum, whose coefficients `(T e_j)_i` are linear in `T`). -/
theorem dGamma_smul {m : ℕ} (c : ℝ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseB4.dGamma m (c • T) = c • Work.BoseB4.dGamma m T := by
  rw [Work.BoseB4.dGamma, Work.BoseB4.dGamma, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, mul_smul]

/-- `dGamma m` is additive over finite sums of one-particle operators. -/
theorem dGamma_finsetSum {m : ℕ} {ι : Type*} (s : Finset ι)
    (T : ι → (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Work.BoseB4.dGamma m (∑ i ∈ s, T i) = ∑ i ∈ s, Work.BoseB4.dGamma m (T i) := by
  simp only [Work.BoseB4.dGamma, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_smul]
  calc ∑ x : Fin m, ∑ x_1 : Fin m, ∑ i ∈ s, (T i) (evec m x_1) x • cre m x ∘ₗ ann m x_1
      = ∑ x : Fin m, ∑ i ∈ s, ∑ x_1 : Fin m, (T i) (evec m x_1) x • cre m x ∘ₗ ann m x_1 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm
    _ = ∑ i ∈ s, ∑ x : Fin m, ∑ x_1 : Fin m, (T i) (evec m x_1) x • cre m x ∘ₗ ann m x_1 :=
        Finset.sum_comm
    _ = ∑ i ∈ s, ∑ i_1 : Fin m, ∑ j : Fin m, (T i) (evec m j) i_1 • cre m i_1 ∘ₗ ann m j := rfl

/-- **The `NH` row.**  A finite weighted sum of rank-one words
`Σ_k η_k · (creOf (f k) ∘ annOf (f k))` is the second quantisation of
`Σ_k η_k · |f k⟩⟨f k|`.  This is the form in which `Work.BoseBoxFock.tildeDataHon`'s `NH`
(and hence every one-body row of `Work.BoseBoxFock.H2ndF`) is consumed by the box
dictionary. -/
theorem dGamma_rankSum {m : ℕ} {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (η : Mode → ℝ) :
    Work.BoseB4.dGamma m ((1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode, η k • rankOne (f k))
      = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode, η k •
          ((Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k))) := by
  rw [dGamma_smul, dGamma_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dGamma_smul]
  congr 1
  exact (Work.BoseB4.creOf_annOf_eq_dGamma (f k) (f k)).symm

/-! ## 2. The `NH` of the honest family -/

/-- The `η_H`-weight of the honest `NH`, read off `Work.BoseBoxFock.tildeDataHon`:
`κ = ((K_L d²)⁻¹)·√(μa)`. -/
noncomputable def nhEta (v : ℝ³ → ℝ) (fu : Work.BoseBoxFix.LowCut) (μ : ℝ)
    {N : ℕ} (k : Lab N) : ℝ :=
  etaH fu
    (((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
      * Real.sqrt (μ * BoseGases.a v))
    (kmomLab (ellH v μ) N k)

/-- **The `NH` of the honest box family is a `dGamma`**, with the one-particle operator
`T = (1/32) Σ_{k ∈ excited} η_H(k) · |f k⟩⟨f k|`. -/
theorem NH_eq_dGamma (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    ∃ T : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ),
      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH :
          Work.BoseB4.RealFock (HM μ).m →ₗ[ℝ] Work.BoseB4.RealFock (HM μ).m)
        = Work.BoseB4.dGamma (HM μ).m T := by
  refine ⟨(1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
      nhEta v fu μ k • rankOne ((HM μ).f k), ?_⟩
  dsimp only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.tildeDataHon,
    Work.BoseBoxFock.nhEta]
  exact (dGamma_rankSum (f := (HM μ).f)
    (η := fun k => nhEta v fu μ k)).symm

end Work.BoseBoxFock
