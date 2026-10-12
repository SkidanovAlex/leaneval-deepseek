import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.Main` — the assembled `Q3Kernel` and `IntKernel`

This module assembles the kernel interface of FS §10 out of the honest
primitives of `Work.BoseK15.K15Input` together with the derived χ-side and
potential-side facts (`ChiSmall.lean`, `ChiSums.lean`, `ChiForm.lean`,
`Pot.lean`; the lemmas `chi_small_of_decay`, `chi_sums_of_decay`,
`hatChiSq_form_upper`, `count_PL_le`, `sum_W1sq_le`, `A_ge_and_AB_of_taurad`).

The two headline results are

* `Work.BoseK15.K15Input.toQ3Kernel` — `Q3Kernel K₀ F T E` from a `K15Input K₀`,
  the χ/potential consequences, the global `AB` (one of the fields on which FS's
  data and the design's statement genuinely differ; see `Derive.lean`'s header) and
  **K5's `intOne` passed explicitly** — so that it can be supplied either by the
  bundle (`Work.BoseK15.K15Input.intOne_holds`) or *derived* from
  `Work.BoseB7A.estIntegralOneA` (`Work.BoseK15.IntOne`);
* `Work.BoseK15.K15Input.toIntKernel` — `IntKernel K₀ R F E gHat` from the same
  data.

Every constant is absolute: it is the single `K₀` of the bundle, which the bundle
declares to dominate every auxiliary constant (`Cchi`, `Csum`, `Ctail`, `Ccard`,
`Calpha`, `Cint`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

namespace K15Input

/-- `ρ_z = z²/ℓ³ ≥ 0` (the box side is positive because it is the environment's
`E.ell > 0`). -/
theorem rho_nonneg (h : K15Input K₀ F T E) : 0 ≤ E.rho := by
  have hpos : 0 < E.ell := by rw [← h.ell_eq_E]; exact h.ell_pos
  show 0 ≤ E.z ^ 2 / E.ell ^ 3
  exact div_nonneg (sq_nonneg _) (by positivity)

/-- `α`'s Lipschitz bound (K3) with the chapter constant: the bundle's `Calpha`
is dominated by `K₀`. -/
theorem alpha_lip_holds (h : K15Input K₀ F T E) (p q : Mode)
    (hp : F.PHq E.KH E.aScat p) (hq : F.PHq E.KH E.aScat q) :
    |E.alpha p - E.alpha q| ≤ K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖ := by
  refine le_trans (h.halpha_lip p q hp hq) ?_
  have hnn : 0 ≤ E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖ := by
    have hl : 0 ≤ E.lille := by
      show 0 ≤ E.mu * E.aScat ^ 3 * E.KH ^ 2
      exact mul_nonneg (mul_nonneg h.mu_pos.le (pow_nonneg h.aScat_pos.le 3)) (sq_nonneg _)
    exact mul_nonneg (mul_nonneg hl (mul_nonneg h.KH_pos.le h.aScat_pos.le)) (norm_nonneg _)
  calc h.Calpha * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖
      = h.Calpha * (E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖) := by ring
    _ ≤ K₀ * (E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖) :=
        mul_le_mul_of_nonneg_right h.K₀_alpha hnn
    _ = K₀ * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖ := by ring

/-- FS `eq:CompIntegrals-Final` with the chapter constant: the bundle's `Cint` is
dominated by `K₀`. -/
theorem intOne_holds (h : K15Input K₀ F T E) :
    |E.rho * E.W1omega0 - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
      ≤ K₀ * E.rho * E.aScat * E.KH⁻¹ := by
  refine le_trans h.hintOne ?_
  have h0 : 0 ≤ E.rho * E.aScat * E.KH⁻¹ :=
    mul_nonneg (mul_nonneg h.rho_nonneg h.aScat_pos.le)
      (inv_nonneg.mpr h.KH_pos.le)
  calc h.Cint * E.rho * E.aScat * E.KH⁻¹
      = h.Cint * (E.rho * E.aScat * E.KH⁻¹) := by ring
    _ ≤ K₀ * (E.rho * E.aScat * E.KH⁻¹) := mul_le_mul_of_nonneg_right h.K₀_int h0
    _ = K₀ * E.rho * E.aScat * E.KH⁻¹ := by ring

/-- **The assembled `Q3Kernel`.**  The extra hypotheses are the conclusions of the
chapter's derived lemmas, so that this theorem is the single place where the
twenty-seven fields are collected. -/
theorem toQ3Kernel (h : K15Input K₀ F T E)
    (hhatChi_small : ∀ q : Mode, F.PHq E.KH E.aScat q → |E.hatChi q| ≤ K₀ * eta E)
    (hccrX_small : ∀ s q : Mode, E.fL s ≠ 0 → F.PHq E.KH E.aScat q →
      |T.ccrX s q| ≤ K₀ * eta E)
    (hsum : ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀)
    (htail : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
      ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)))
    (hform_nonneg : ∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H),
      0 ≤ ∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
    (hform_upper : ∀ (S : Finset Mode) (c : Mode → ℝ) (v : Mode → F.H),
      (∑ s ∈ S, ∑ s' ∈ S, c s * c s' * E.hatChiSq (s' - s) * F.bp (v s') (v s))
        ≤ K₀ * ∑ s ∈ S, c s ^ 2 * F.bp (v s) (v s))
    (hcount : (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ)
      ≤ K₀ * (E.Kl * E.KL) ^ 3)
    (hsumW1sq : E.ell ^ (-(3 : ℝ)) *
      ∑ q ∈ (excited Mode).filter (fun q => F.PHq E.KH E.aScat q),
        E.W1 q ^ 2 / ‖F.kmom q‖ ^ 2 ≤ K₀ * E.aScat)
    (hA_ge : ∀ q : Mode, F.PHq E.KH E.aScat q → ‖F.kmom q‖ ^ 2 / 2 ≤ E.A q)
    (hAB : ∀ k : Mode, |E.B k| ≤ E.A k)
    (hhasKernel : ∀ i j : Mode, F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j)
    (hintOne' : |E.rho * E.W1omega0
        - E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
      ≤ K₀ * E.rho * E.aScat * E.KH⁻¹) :
    Q3Kernel K₀ F T E where
  W1_le := h.W1_le_holds
  W1_even := h.W1_even_holds
  A_even := h.A_even_holds
  B_even := h.B_even_holds
  B_eq := h.B_eq_holds
  AB := hAB
  A_ge := hA_ge
  fL_nonneg := h.fL_nonneg_holds
  fL_le_one := h.fL_le_one_holds
  fL_even := h.fL_even_holds
  fL_supp := h.fL_supp_holds
  kmom_sub := h.kmom_sub_holds
  hasKernel := hhasKernel
  hatChiSq_le := h.hatChiSq_le_holds
  hatChi_le := h.hatChi_le_holds
  hatChi_even := h.hatChi_even_holds
  hatChiSq_even := h.hatChiSq_even_holds
  hatChi_small := hhatChi_small
  ccrX_small := hccrX_small
  hatChiSq_form := fun S c v _ => ⟨hform_nonneg S c v, hform_upper S c v⟩
  count_PL := hcount
  sum_hatChiSq := hsum
  tail_hatChiSq := htail
  sum_W1sq := hsumW1sq
  alpha_lip := h.alpha_lip_holds
  W1omega0_nonneg := h.W1omega0_nonneg_holds
  W1omega0_le := h.W1omega0_le_holds
  intOne := hintOne'
  q2exLower := h.q2exLower_holds

/-- **The assembled `IntKernel`** (the `lem:EstimateIntegral` input bundle).  The
`PH`-form of `A_ge`/`AB` is what the `IntKernel` fields ask; the `P_H ⊆ P_H^q`
inclusion (`Work.BoseB7A.PH_subset_PHq_sub`) converts the chapter's `P_H^q`
bounds when the smallness of `K_L√(μa)·K_Ha` is available. -/
theorem toIntKernel (h : K15Input K₀ F T E) (R : ℝ)
    (hA_ge : ∀ k : Mode, F.PH E.KH E.aScat k → ‖F.kmom k‖ ^ 2 / 2 ≤ E.A k)
    (hABq : ∀ k : Mode, F.PH E.KH E.aScat k → 2 * |E.B k| ≤ E.A k)
    (hkmom_ne : ∀ k ∈ excited Mode, F.kmom k ≠ 0)
    (htau_PH : ∀ k : Mode, F.PH E.KH E.aScat k →
      0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k ∧ ‖F.kmom k‖ ^ 2 - E.tau k
        ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell))
    (hsumW1sqPH : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ K₀ * E.aScat) :
    IntKernel K₀ R F E h.gHat where
  W1_le := h.W1_le_holds
  
  gHat_le := h.gHat_le
  B_eq := h.B_eq
  A_eq := h.A_eq
  A_pos := by
    intro k hk
    have h1 := hA_ge k hk
    have hnorm : 0 < ‖F.kmom k‖ := by
      have h2 : 0 < 1 / (2 * E.KH * E.aScat) := by
        have := h.KH_pos; have := h.aScat_pos; positivity
      exact lt_of_lt_of_le h2 hk
    have : 0 < ‖F.kmom k‖ ^ 2 / 2 := by positivity
    linarith
  AB_kernel := hABq
  kmom_ne := fun k hk => h.kmom_ne_holds hk
  tau_PH := htau_PH
  omega_lattice := by simpa only [h.kmom_eq] using h.omega_lattice
  low_sum := by simpa only [h.kmom_eq] using h.low_sum
  sum_inv4 := by simpa only [h.kmom_eq] using h.sum_inv4
  sum_inv6 := by simpa only [h.kmom_eq] using h.sum_inv6
  sum_inv3 := by simpa only [h.kmom_eq] using h.sum_inv3
  sum_W1sq := hsumW1sqPH
  sum_diff := by simpa only [h.kmom_eq] using h.sum_diff R

end K15Input

end Work.BoseK15
