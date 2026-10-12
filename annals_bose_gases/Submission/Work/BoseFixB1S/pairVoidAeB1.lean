import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.mfHoleVoidVanishesB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- **The localised pair kernel is nonzero wherever its three factors are.**

`wSmallPair M ℓ d u v x y = χ_{B(u)}(x)·(v(x−y)/((χ_M⋆χ_M)((x−y)/(ℓd))·(χ⋆χ)((x−y)/ℓ)))·χ_{B(u)}(y)`
(`wSmallScaled M c h z = h z/(χ_M⋆χ_M)(z/c)`), so the kernel vanishes only if one of
`χ_{B(u)}(x)`, `v(x−y)`, `χ_{B(u)}(y)` vanishes, **provided** the numerator `v` is supported in
`ball 0 R` with `R ≤ ℓd/16` (so that `(χ_M⋆χ_M)((x−y)/(ℓd)) ≠ 0`, `conv3Small_ne_zero_of_norm_le`)
and `1/2 ≤ (χ⋆χ)((x−y)/ℓ)` on `ball 0 R` (so that the ℓ-scale denominator is nonzero).

This is the converse of the "void" lemma `mfHoleVoidVanishesB1` — the pointwise ingredient of
`pairVoidAeB1`. -/
lemma wSmallPair_ne_zero_of_chiSmallB {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    (hR16 : R ≤ ℓ * d / 16) (u x y : EuclideanSpace ℝ (Fin 3))
    (hzR : ‖x - y‖ ≤ R) (hvxy : v (x - y) ≠ 0)
    (hx : Submission.BoseGases.chiSmallB M ℓ d u x ≠ 0)
    (hy : Submission.BoseGases.chiSmallB M ℓ d u y ≠ 0) :
    Submission.BoseGases.wSmallPair M ℓ d u v x y ≠ 0 := by
  have hcpos : (0 : ℝ) < ℓ * d := mul_pos hℓ hd
  have hz16 : ‖x - y‖ ≤ ℓ * d / 16 := le_trans hzR hR16
  have hconvSmall : Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) ≠ 0 := by
    rw [Submission.BoseGases.convScaleSmall]
    exact Submission.BoseGases.conv3Small_ne_zero_of_norm_le hM _
      (Submission.BoseGases.norm_inv_smul_le hcpos (x - y) hz16)
  have hconv : Submission.BoseGases.convScale ℓ (x - y) ≠ 0 := by
    have h := hden (x - y) hzR
    rw [Submission.BoseGases.convScale]
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) h)
  rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled]
  exact mul_ne_zero (mul_ne_zero hx (div_ne_zero (div_ne_zero hvxy hconvSmall) hconv)) hy

theorem pairVoidAeB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Ψ = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Ψ x ≠ 0 →
        ∀ i j : Fin n, i ≠ j →
          Submission.BoseGases.chiSmallB M ℓ d u (x i) * v (x i - x j)
            * Submission.BoseGases.chiSmallB M ℓ d u (x j) = 0 := by
  classical
  set G : Submission.BoseGases.X n → ℝ := fun x => (Ψ x) ^ 2 *
    ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
      Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) with hG
  -- the state-level pair integrand is integrable over the box (from `MemLp v 1` and the regime)
  have hInt : MeasureTheory.Integrable G
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    rw [hG]
    exact Work.BoseFixB1.integrableOn_pairSumIntegrand (v := v) (R0 := R) hv_supp hR hv1 hM hℓ hd
      hR16 hRχ u hΨc
  -- the vanishing hypothesis is the vanishing of the integral of `G`
  have hzero : ∫ x, G x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)) = 0 := by
    rw [hG, ← hpair]
    rw [Work.BoseFixB1.pairSum]
  -- the integrand is pointwise nonnegative
  have hfnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] G := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [hG]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun p _ => Work.BoseFixB1.perBoxMFCase_wSmallPair_nonneg (f := v) hv))
  -- hence it vanishes a.e.
  have hae : G =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hfnn hInt).mp hzero
  filter_upwards [hae] with x hx
  intro hΨne i j hij
  have hx' : (Ψ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
      Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) = 0 := by
    rw [hG] at hx
    exact hx
  -- the sum of pair kernels vanishes (sum of nonnegative terms, state nonzero at `x`)
  have hsum0 : ∑ p ∈ Submission.BoseGases.pairSet n,
      Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) = 0 := by
    have h1 : (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) = 0 := by
      rcases mul_eq_zero.mp hx' with h2 | h2
      · exact absurd h2 (pow_ne_zero 2 hΨne)
      · exact h2
    linarith
  by_contra hbad
  -- so the kernel at the pair `(i, j)` vanishes
  have hw0 : Submission.BoseGases.wSmallPair M ℓ d u v (x i) (x j) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
      Work.BoseFixB1.perBoxMFCase_wSmallPair_nonneg (f := v) hv)).mp hsum0 (i, j) ?_
    rw [Submission.BoseGases.pairSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hij⟩
  -- but none of its three factors vanishes
  have hvij : v (x i - x j) ≠ 0 := by
    intro h0
    exact hbad (by rw [h0, mul_zero, zero_mul])
  have hxi : Submission.BoseGases.chiSmallB M ℓ d u (x i) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hbad).1).1
  have hxj : Submission.BoseGases.chiSmallB M ℓ d u (x j) ≠ 0 :=
    (mul_ne_zero_iff.mp hbad).2
  -- the support hypothesis puts `x i - x j` inside `ball 0 R`
  have hzR : ‖x i - x j‖ ≤ R := by
    have hmem : x i - x j ∈ Function.support v := hvij
    have hball := hv_supp (subset_closure hmem)
    have hlt := Metric.mem_ball.mp hball
    simpa [dist_eq_norm] using hlt.le
  exact absurd hw0 (wSmallPair_ne_zero_of_chiSmallB hM hℓ hd hden hR16 u (x i) (x j) hzR hvij
    hxi hxj)

end

end Work.BoseFixB1S
