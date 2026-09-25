import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false

noncomputable section

/-- Positivity of the scaling factor `2^y`. -/
private lemma two_rpow_pos (y : ℝ) : (0 : ℝ) < (2 : ℝ) ^ y :=
  Real.rpow_pos_of_pos (by norm_num) y

/-- `2^y · 2^{-y} = 1`. -/
private lemma two_rpow_mul_two_rpow_neg (y : ℝ) :
    (2 : ℝ) ^ y * (2 : ℝ) ^ (-y) = 1 := by
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num)]
  exact mul_inv_cancel₀ (ne_of_gt (two_rpow_pos y))

/-- The value of the scaled bump at a point of the inner ball is `1`: if `|z| ≤ 2^{-y}/4` then
`|2^y z| ≤ 1/4`, and `η` is `1` there.  (This is the `β₀`-summand computation, in the shape in
which it is used below.) -/
private lemma abs_two_rpow_mul_le_quarter {y z : ℝ}
    (h : |z| ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-y)) : |(2 : ℝ) ^ y * z| ≤ 1 / 4 := by
  rw [abs_mul, abs_of_pos (two_rpow_pos y)]
  have hmul : (2 : ℝ) ^ y * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-y)) = 1 / 4 := by
    have h1 : (2 : ℝ) ^ y * ((1 / 4 : ℝ) * (2 : ℝ) ^ (-y))
        = (1 / 4 : ℝ) * ((2 : ℝ) ^ y * (2 : ℝ) ^ (-y)) := by ring
    rw [h1, two_rpow_mul_two_rpow_neg, mul_one]
  have := mul_le_mul_of_nonneg_left h (le_of_lt (two_rpow_pos y))
  rwa [hmul] at this

/-- **The converse**: a nonzero value of the scaled bump forces the point into the ball of radius
`2^{-y}/2`. -/
private lemma abs_le_half_mul_of_abs_two_rpow_mul_le {y z : ℝ}
    (h : |(2 : ℝ) ^ y * z| ≤ 1 / 2) : |z| ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-y) := by
  have hc := two_rpow_pos y
  rw [abs_mul, abs_of_pos hc] at h
  have h1 : ((2 : ℝ) ^ y)⁻¹ * ((2 : ℝ) ^ y * |z|) = |z| := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
  have h2 : ((2 : ℝ) ^ y)⁻¹ * (1 / 2) = (1 / 2 : ℝ) * (2 : ℝ) ^ (-y) := by
    rw [Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num), mul_comm]
  calc |z| = ((2 : ℝ) ^ y)⁻¹ * ((2 : ℝ) ^ y * |z|) := h1.symm
    _ ≤ ((2 : ℝ) ^ y)⁻¹ * (1 / 2) :=
        mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hc))
    _ = (1 / 2 : ℝ) * (2 : ℝ) ^ (-y) := h2

/-- The level bump `η_n` vanishes outside the ball of radius `2^{-n(d-χ)}/2` — the contrapositive of
the support condition `η x = 0` for `1/2 < |x|`. -/
private lemma mstEta_eq_zero_of_half_lt_norm {d n : ℕ} {χ : ℝ} {η : ℝ → ℂ}
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) {ξ : Work.BourgainPlan.IonescuWainger.Circle}
    (h : (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) < ‖ξ‖) :
    mstEta d χ η n ξ = 0 := by
  rw [mstEta_apply]
  rw [norm_eq_abs_iwRep] at h
  by_contra hne
  have hle : |(2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep ξ| ≤ 1 / 2 := by
    by_contra hlt
    exact hne (hη2 _ (lt_of_not_ge hlt))
  have hz := abs_le_half_mul_of_abs_two_rpow_mul_le hle
  linarith

/-- **Geometry of the level-`n` projection symbol `Ξ_n`** (MST §4.1, the support/disjointness half). Given that the points of `mstU l n` (`= 𝒰(n)`, the Farey fractions of denominator `≤ n^l`) are `sep`-separated with the level width below `sep`, the bump sum `mstXi l d χ η n ξ = Σ_{β ∈ 𝒰(n)} η(2^{n(d-χ)} · iwRep(ξ-β))` has norm at most `M` — at most one summand is nonzero because the supports are disjoint — and it equals `1` as soon as `ξ` lies in the *inner* ball of some `β₀ ∈ 𝒰(n)`.

Toolkit: `Work.BourgainPlan.IonescuWainger.norm_arcSymbol_le` (in `IonescuWainger/OpArcDefs.lean`, reachable through `iw_superset`/`mst_level_defs`) gives the first conjunct directly with `φ := mstEta d χ η n`, `ε := (1/2)·2^{-n(d-χ)}`, `δ := sep` and `hδε := hsep_gt`; for `hφsupp` use that `mstEta d χ η n ζ ≠ 0` forces `|iwRep ζ| ≤ (1/2)2^{-n(d-χ)}` (contrapositive of `hη2`). The useful circle/lift facts (`iwRep` lands in `Ioc (-1/2) (1/2]`, `coe_iwRep`, `‖ξ‖ = |iwRep ξ|`, `|iwRep ξ| ≤ 1/2`) can either be reproved in two lines each from `AddCircle.equivIoc`/`AddCircle.norm_coe_eq_abs_iff`, or imported from the leaf module `Submission.Work.BourgainPlan.Maximal.memLp_scaled_bump` (which has `iwRep_mem_Ioc`, `abs_iwRep_le`, `coe_iwRep`, `norm_eq_abs_iwRep`; do NOT import it together with `khatZMult_coeFn_star_mstWeyl`, whose `coe_iwRep` name it duplicates). For the second conjunct, the `β₀` summand is `1` by `hη1`, and any other contributing `β` would satisfy `‖β - β₀‖ ≤ (3/4)2^{-n(d-χ)} < sep ≤ ‖β - β₀‖`, a contradiction (use `hsep_gt` and the triangle inequality). -/
theorem mstXi_bound_and_eq_one {l d : ℕ} {χ : ℝ} {η : ℝ → ℂ} {n : ℕ} {sep M : ℝ}
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hsep : ∀ β ∈ Work.BourgainPlan.Maximal.mstU l n,
      ∀ β' ∈ Work.BourgainPlan.Maximal.mstU l n, β ≠ β' → sep ≤ ‖β - β'‖)
    (hsep_gt : (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) < sep)
    (ξ : Work.BourgainPlan.IonescuWainger.Circle) :
    ‖Work.BourgainPlan.Maximal.mstXi l d χ η n ξ‖ ≤ M ∧
      (∀ β₀ ∈ Work.BourgainPlan.Maximal.mstU l n,
        |Work.BourgainPlan.Maximal.iwRep (ξ - β₀)|
            ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) →
        Work.BourgainPlan.Maximal.mstXi l d χ η n ξ = 1) := by
  constructor
  · -- the norm bound: at most one bump is nonzero
    have hbound := norm_arcSymbol_le (φ := mstEta d χ η n) (E := mstU l n)
      (ε := (1 / 2) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ)))) (δ := sep) (M := M)
      (fun ζ => by simpa only [mstEta_apply] using hηbd ((2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep ζ))
      (fun ζ hζ => mstEta_eq_zero_of_half_lt_norm hη2 hζ)
      hsep
      (by
        have he : (2 : ℝ) * ((1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))))
            = (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by ring
        rw [he]
        exact hsep_gt)
      ξ
    have hrfl : mstXi l d χ η n ξ = arcSymbol (mstEta d χ η n) (mstU l n) ξ := rfl
    rw [hrfl]
    exact hbound
  · -- the value at an inner point: only the `β₀`-summand survives, and it is `1`
    intro β₀ hβ₀ hinner
    rw [mstXi_apply]
    have hterm : ∀ β ∈ mstU l n, β ≠ β₀ → mstEta d χ η n (ξ - β) = 0 := by
      intro β hβ hne
      rw [mstEta_apply]
      by_contra hval
      have hle : |(2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ)) * iwRep (ξ - β)| ≤ 1 / 2 := by
        by_contra hlt
        exact hval (hη2 _ (lt_of_not_ge hlt))
      have hb := abs_le_half_mul_of_abs_two_rpow_mul_le hle
      have hn1 : ‖ξ - β‖ ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
        rw [norm_eq_abs_iwRep]
        exact hb
      have hn0 : ‖ξ - β₀‖ ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * ((d : ℝ) - χ))) := by
        rw [norm_eq_abs_iwRep]
        exact hinner
      have htri : ‖β - β₀‖ ≤ ‖β - ξ‖ + ‖ξ - β₀‖ := by
        have : β - β₀ = (β - ξ) + (ξ - β₀) := by abel
        rw [this]
        exact norm_add_le _ _
      have hbξ : ‖β - ξ‖ = ‖ξ - β‖ := norm_sub_rev β ξ
      nlinarith [hsep β hβ β₀ hβ₀ hne, htri, hn1, hn0, hbξ, hsep_gt,
        two_rpow_pos (-((n : ℝ) * ((d : ℝ) - χ)))]
    rw [Finset.sum_eq_single β₀ hterm (fun h => absurd hβ₀ h)]
    rw [mstEta_apply]
    exact hη1 _ (abs_two_rpow_mul_le_quarter hinner)

end

end Work.BourgainPlan.Maximal
