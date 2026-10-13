/-
# `Weil/remSourceFacts` — the three facts about the remainder source `RemSource α ψ`

`Work.FTS.PhiStar.RemSource α ψ = fun z θ => α^2 * 𝒜φ(z) * ψ(θ)` (with `𝒜φ = VocabO.phiA α`) is
the separable `O(α^2)` source of the `Φ_*` decomposition.  The Weyl route to the smoothness of
the mode series `psiSeries α (RemSource α ψ)` (`Weil/Assembly.weakIdentity`, and hence
`Weil/Main`) consumes exactly the three facts proved here:

1. `SmoothOpen (RemSource α ψ)` — the uncurried source is `C^∞` on the open quadrant
   `Q0 = (0,∞) × (0,π/2)`.  It is a separable product: `𝒜φ` is a rational function whose only
   pole is at `z = -1` (`Work.FTS.PhiStar.contDiffAt_phiA_of`), hence `C^n` on `(0,∞)` for every
   `n`, while `ψ` is `C^n` on `(0,π/2)` for every `n` (`AngModel.smooth`); the elementary closure
   fact `sep_mul_smoothOpen_quad` glues the two factors.  (It is the open-interval version of
   `Work.FTS.EllipticEst.SmoothOpen.sep_mul`, which asks the angular factor to be smooth on *all*
   of `ℝ`.)
2. `OrthCond (RemSource α ψ)` — the angular moment `F_*(z) = ∫ ψ sinθcos²θ` of the source
   vanishes identically: the `θ`-integral factors out, and `∫ θ in Iθ, ψ θ * sinCos2 θ = 0` is
   exactly `AngModel.moment`.  This is the solvability condition of `prop:L2`.
3. `IntegrableOn (RemSource α ψ)² (Ioi 0 ×ˢ Ioo 0 (π/2))` — the source is square integrable on
   the quadrant.  It is separable, so it suffices that `(𝒜φ)²` is integrable on `(0,∞)`
   (`phiA_sq_integrableOn'` below: `𝒜φ` is a rational function vanishing linearly at `0` and
   like `1/z` at `∞`) and that `ψ²` is integrable on `(0,π/2)` (continuity on the closed
   interval: `continuousOn_sq_integrableOn_Ioo`); `integrableOn_prod_mul` multiplies the two.

## Notation

The statement of `remSourceFacts` is the one fixed by the assignment, verbatim; this file opens
the `Real` scope so that its `π` means `Real.pi`.  (Without that scope `π` is *not* the notation
for `Real.pi`: with `autoImplicit = false`, as fixed by the workspace `lakefile.toml`, it is not
even a bound variable and the statement does not elaborate at all.  Every consumer of this lemma
— `Weil/Assembly`, `Weil/Main` — opens the `Real` scope, so `Real.pi` is the intended reading.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.phiAj_smooth2
import Submission.Work.FTS.PhiStar.Series.phiA_abs_le_inv
import Submission.Work.Elliptic.WtoH_IntZ
import Submission.Work.FTS.PhiStar.Series.Weil.continuousOn_sq_integrableOn_Ioo
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-! ## The closure of `SmoothOpen` under separable products with open-interval factors -/

/-- The separable product `(z,θ) ↦ A z * B θ` of a radial factor which is `C^n` on `(0,∞)` for
every `n` and an angular factor which is `C^n` on `(0,π/2)` for every `n` is `C^∞` on the open
quadrant. -/
private theorem sep_mul_smoothOpen_quad {A B : ℝ → ℝ}
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (Set.Ioi 0))
    (hB : ∀ m : ℕ, ContDiffOn ℝ m B (Set.Ioo 0 (π / 2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => A z * B θ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => A z * B θ)) Work.FTS.EllipticEst.Q0
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => A p.1 * B p.2) Work.FTS.EllipticEst.Q0
  rw [show (fun p : ℝ × ℝ => A p.1 * B p.2)
      = (fun p : ℝ × ℝ => A p.1) * (fun p : ℝ × ℝ => B p.2) from rfl]
  have hAinfty : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A (Set.Ioi 0) :=
    contDiffOn_infty.mpr hA
  have hBinfty : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B (Set.Ioo 0 (π / 2)) :=
    contDiffOn_infty.mpr hB
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A p.1)
      Work.FTS.EllipticEst.Q0 :=
    hAinfty.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => B p.2)
      Work.FTS.EllipticEst.Q0 :=
    hBinfty.comp contDiffOn_snd fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).2
  exact h1.mul h2

/-! ## The size and the `L²`-integrability of the radial factor `𝒜φ` -/

/-- **`𝒜φ = phiA α` is `O(1/z)` at infinity and `O(z)` at the origin**: for `z > 0`,
`|𝒜φ(z)| ≤ K/(1+z)` with the explicit `α`-dependent constant
`K = |2α - 10| + 8|α| + |10 + 2α|`. -/
private theorem phiA_abs_le_inv_one_add (α : ℝ) {z : ℝ} (hz : 0 < z) :
    |Work.FTS.VocabO.phiA α z|
      ≤ (|2 * α - 10| + 8 * |α| + |10 + 2 * α|) / (1 + z) := by
  set K : ℝ := |2 * α - 10| + 8 * |α| + |10 + 2 * α| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _)))
      (abs_nonneg _)
  have hz0 : (0 : ℝ) ≤ z := hz.le
  have hz1 : z ≠ -1 := by linarith
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  have hz3 : (0 : ℝ) ≤ z ^ 3 := pow_nonneg hz0 3
  have hs1 : (0 : ℝ) < 1 + z := by linarith
  have h4 : (0 : ℝ) < (1 + z) ^ 4 := pow_pos hs1 4
  -- coefficient bounds splitting the numerator `M z = (2α-10)z³ - 8αz² + (10+2α)z` into the
  -- three nonnegative pieces `A = |2α-10|z³`, `B = 8|α|z²`, `C = |10+2α|z`
  have hA1 : (2 * α - 10) ≤ |2 * α - 10| := le_abs_self _
  have hA2 : -(2 * α - 10) ≤ |2 * α - 10| := neg_le_abs _
  have hB1 : 8 * α ≤ 8 * |α| := by linarith [le_abs_self α]
  have hB2 : -(8 * α) ≤ 8 * |α| := by linarith [neg_le_abs α]
  have hC1 : (10 + 2 * α) ≤ |10 + 2 * α| := le_abs_self _
  have hC2 : -(10 + 2 * α) ≤ |10 + 2 * α| := neg_le_abs _
  have hnum : |(2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z|
      ≤ |2 * α - 10| * z ^ 3 + 8 * |α| * z ^ 2 + |10 + 2 * α| * z := by
    rw [abs_le]
    constructor
    · have e1 : -(2 * α - 10) * z ^ 3 ≤ |2 * α - 10| * z ^ 3 :=
        mul_le_mul_of_nonneg_right hA2 hz3
      have e2 : 8 * α * z ^ 2 ≤ 8 * |α| * z ^ 2 :=
        mul_le_mul_of_nonneg_right hB1 hz2
      have e3 : -(10 + 2 * α) * z ≤ |10 + 2 * α| * z :=
        mul_le_mul_of_nonneg_right hC2 hz0
      nlinarith [e1, e2, e3]
    · have e1 : (2 * α - 10) * z ^ 3 ≤ |2 * α - 10| * z ^ 3 :=
        mul_le_mul_of_nonneg_right hA1 hz3
      have e2 : -(8 * α) * z ^ 2 ≤ 8 * |α| * z ^ 2 :=
        mul_le_mul_of_nonneg_right hB2 hz2
      have e3 : (10 + 2 * α) * z ≤ |10 + 2 * α| * z :=
        mul_le_mul_of_nonneg_right hC1 hz0
      nlinarith [e1, e2, e3]
  have hsum : |2 * α - 10| * z ^ 3 + 8 * |α| * z ^ 2 + |10 + 2 * α| * z
      ≤ K * (z ^ 3 + z ^ 2 + z) := by
    rw [hK]
    have hz2z : (0 : ℝ) ≤ z ^ 2 + z := by linarith
    have hz3z : (0 : ℝ) ≤ z ^ 3 + z := by linarith
    have hz3z2 : (0 : ℝ) ≤ z ^ 3 + z ^ 2 := by linarith
    nlinarith [mul_nonneg (abs_nonneg (2 * α - 10)) hz2z,
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (abs_nonneg α)) hz3z,
      mul_nonneg (abs_nonneg (10 + 2 * α)) hz3z2]
  have hMM : |(2 * α - 10) * z ^ 3 - 8 * α * z ^ 2 + (10 + 2 * α) * z|
      ≤ K * (z ^ 3 + z ^ 2 + z) := le_trans hnum hsum
  have h3 : z ^ 3 + z ^ 2 + z ≤ (1 + z) ^ 3 := by nlinarith [hz0, sq_nonneg z]
  have hstep : |Work.FTS.VocabO.phiA α z| ≤ K * (1 + z) ^ 3 / (1 + z) ^ 4 := by
    rw [Work.FTS.PhiStar.Series.phiA_combined α z hz1, abs_div, abs_of_pos h4]
    exact div_le_div_of_nonneg_right
      (le_trans hMM (mul_le_mul_of_nonneg_left h3 hK0)) h4.le
  have hfinal : K * (1 + z) ^ 3 / (1 + z) ^ 4 = K / (1 + z) := by
    have hs1n : (1 + z) ≠ 0 := ne_of_gt hs1
    have hs4n : (1 + z) ^ 4 ≠ 0 := pow_ne_zero 4 hs1n
    field_simp
  rw [hfinal] at hstep
  exact hstep

/-- **`(𝒜φ)²` is integrable on `(0,∞)`** for every real `α`: `𝒜φ = phiA α` is a rational
function with its only pole at `z = -1` (outside `(0,∞)`), vanishing like `z` at `0` and like
`1/z` at `∞`, so it is dominated by `K/(1+z)`, whose square is integrable on `Iz = [0,∞)`
(`Work.Elliptic.WtoH_IntZ`). -/
private theorem phiA_sq_integrableOn' (α : ℝ) :
    MeasureTheory.IntegrableOn (fun z : ℝ => Work.FTS.VocabO.phiA α z ^ 2) (Set.Ioi 0) := by
  set K : ℝ := |2 * α - 10| + 8 * |α| + |10 + 2 * α| with hK
  have hbase : MeasureTheory.IntegrableOn (fun z : ℝ => 1 / (1 + z) ^ 2) (Set.Ioi 0) := by
    refine Work.Elliptic.WtoH_IntZ.1.mono_set ?_
    intro z hz
    rw [Work.Spaces.Iz]
    exact Set.mem_Ici.mpr hz.le
  have hmaj : MeasureTheory.IntegrableOn (fun z : ℝ => K ^ 2 * (1 / (1 + z) ^ 2))
      (Set.Ioi 0) := hbase.const_mul (K ^ 2)
  have hsqu : ∀ z : ℝ, (K / (1 + z)) ^ 2 = K ^ 2 * (1 / (1 + z) ^ 2) := by
    intro z
    rw [div_pow, div_eq_mul_inv]
    ring
  refine hmaj.mono' ?_ ?_
  · have hcont : ContinuousOn (fun z : ℝ => Work.FTS.VocabO.phiA α z ^ 2) (Set.Ioi 0) :=
      fun z hz =>
        (((Work.FTS.PhiStar.contDiffAt_phiA_of α 0 hz).continuousAt).pow 2).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    change ‖Work.FTS.VocabO.phiA α z ^ 2‖ ≤ K ^ 2 * (1 / (1 + z) ^ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hbdd : |Work.FTS.VocabO.phiA α z| ≤ K / (1 + z) := phiA_abs_le_inv_one_add α hz
    have hsq : (Work.FTS.VocabO.phiA α z) ^ 2 ≤ (K / (1 + z)) ^ 2 := by
      have h2 : |Work.FTS.VocabO.phiA α z| ^ 2 ≤ (K / (1 + z)) ^ 2 := by
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (abs_nonneg (Work.FTS.VocabO.phiA α z)) hbdd
      rwa [sq_abs] at h2
    rw [← hsqu z]
    exact hsq

/-! ## The three facts about the source -/

theorem remSourceFacts (α : ℝ) (ψ : ℝ → ℝ) (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.RemSource α ψ) ∧
    Work.Elliptic.OrthCond (Work.FTS.PhiStar.RemSource α ψ) ∧
    MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Work.FTS.PhiStar.RemSource α ψ p.1 p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ## 1. the source is `C^∞` on the open quadrant: it is a separable product
    refine sep_mul_smoothOpen_quad (A := fun z : ℝ => α ^ 2 * Work.FTS.VocabO.phiA α z)
      (B := ψ) ?_ ?_
    · -- the `z`-factor `α^2 · 𝒜φ` is `C^n` on `(0,∞)` for every `n`
      intro m z hz
      exact ((contDiffAt_const (c := α ^ 2)).mul
        (Work.FTS.PhiStar.contDiffAt_phiA_of α m hz)).contDiffWithinAt
    · -- the `θ`-factor `ψ` is `C^n` on `(0,π/2)` for every `n`
      intro m
      exact contDiffOn_iff_forall_nat_le.mp hψ.smooth m le_top
  · -- ## 2. the angular moment of the source vanishes
    intro z
    have hF : Work.Elliptic.Fstar (Work.FTS.PhiStar.RemSource α ψ) z
        = (α ^ 2 * Work.FTS.VocabO.phiA α z)
          * (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) := by
      simp only [Work.Elliptic.Fstar, Work.FTS.PhiStar.RemSource]
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hF, hψ.moment, mul_zero]
  · -- ## 3. the source is square integrable on the quadrant: both factors are `L²`
    have hpsi2 : MeasureTheory.IntegrableOn (fun θ : ℝ => ψ θ ^ 2) (Set.Ioo 0 (π / 2)) :=
      continuousOn_sq_integrableOn_Ioo (a := 0) (b := π / 2)
        (by linarith [Real.pi_pos]) hψ.cont
    have hphi2 : MeasureTheory.IntegrableOn
        (fun z : ℝ => (α ^ 2 * Work.FTS.VocabO.phiA α z) ^ 2) (Set.Ioi 0) := by
      have hscaled : MeasureTheory.IntegrableOn
          (fun z : ℝ => α ^ 4 * Work.FTS.VocabO.phiA α z ^ 2) (Set.Ioi 0) :=
        MeasureTheory.Integrable.const_mul (phiA_sq_integrableOn' α) (α ^ 4)
      exact hscaled.congr_fun (fun z _ => by ring) measurableSet_Ioi
    have hprod : MeasureTheory.IntegrableOn
        (fun p : ℝ × ℝ => (α ^ 2 * Work.FTS.VocabO.phiA α p.1) ^ 2 * ψ p.2 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      integrableOn_prod_mul hphi2 hpsi2
    refine hprod.congr_fun (fun p _ => ?_) (measurableSet_Ioi.prod measurableSet_Ioo)
    simp only [Work.FTS.PhiStar.RemSource]
    ring

end Work.FTS.PhiStar.Series.Weil
