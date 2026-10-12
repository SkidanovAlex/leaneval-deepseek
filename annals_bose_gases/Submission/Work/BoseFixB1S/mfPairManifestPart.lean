import ChallengeDeps
import Submission.Work.BoseFixB1S.mfRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.mfPairManifestPart` — the pair part of the manifest identity

With `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `M = (paramsAt μ (a v)).M`,
`A = boxA v μ u = dlBox ℓ d u` and `w = boxW h μ u` (the localised pair kernel
`wSmallPair M ℓ d u v` of `Submission.BoseGases`), this module proves the *pair half* of the
manifest form of the per-box `Q`-sum (`Submission.Work.BoseFixB1S.mfQSumManifestEq`,
`qLHSwordB = … + ½Σ_p∫(1_A(x_{p.1})(1_A(x_{p.2})Φ x))²w − …`):

    ∫_{abox n ℓ} Φ²·(½Σ_{p∈pairSet n} w(x_{p.1},x_{p.2}))
      = ½ Σ_{p∈pairSet n} ∫_{abox n ℓ} (1_A(x_{p.1})·(1_A(x_{p.2})·Φ x))²·w(x_{p.1},x_{p.2}) .

The content is purely structural: the localised kernel `w` carries the cutoff
`chiSmallB M ℓ d u` in *both* slots, and the support of that cutoff lies in `A = dlBox ℓ d u`
(`Work.SlotWord.chiSmallB_support_mem_dlBox`), so `w(x,y) = 0` as soon as `x ∉ A` or `y ∉ A`.
Hence the two box indicators may be inserted pointwise,

    Φ²·w(x_{p.1},x_{p.2}) = (1_A(x_{p.1})·(1_A(x_{p.2})·Φ x))²·w(x_{p.1},x_{p.2})   (all x),

and finite-sum linearity of the Bochner integral over the compact box finishes.  The
integrability needed by `MeasureTheory.integral_finsetSum` is
`Work.BoseFixB1.integrableOn_slot_wSmallPair`, which needs only the uniform bound of the
continuous state `Φ` on the compact box (`abox_compact`), the `L¹` potential `v`
(`Submission.BoseGases.v_integrable`) and the support-radius hypotheses `R ≤ ℓd/16`,
`R ≤ ℓ·chiR0`.
-/

namespace Work.BoseFixB1S

open MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

theorem mfPairManifestPart {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 ≤ μ)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < mfV v μ u)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          (boxW h μ u) (x p.1) (x p.2)))
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1))
                * ((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
              * (boxW h μ u) (x p.1) (x p.2)) := by
  classical
  -- the regularity exponent of the localisation cutoff is `mValue = 48 ≥ 1`
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  -- the kernel vanishes as soon as one of its arguments leaves the sliding box `A = boxA v μ u`
  have hzL : ∀ (a b : EuclideanSpace ℝ (Fin 3)), a ∉ boxA v μ u → (boxW h μ u) a b = 0 := by
    intro a b ha
    have h0 : Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u a = 0 := by
      by_contra hc
      exact ha (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hc)
    simp only [Work.BoseFixB1S.boxW, Submission.BoseGases.wSmallPair, h0, zero_mul]
  have hzR : ∀ (a b : EuclideanSpace ℝ (Fin 3)), b ∉ boxA v μ u → (boxW h μ u) a b = 0 := by
    intro a b hb
    have h0 : Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u b = 0 := by
      by_contra hc
      exact hb (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hc)
    simp only [Work.BoseFixB1S.boxW, Submission.BoseGases.wSmallPair, h0, mul_zero]
  -- hence the two box indicators may be inserted pointwise, for every pair `p`
  have hpt : ∀ (x : Submission.BoseGases.X n) (p : Fin n × Fin n),
      (Φ x) ^ 2 * (boxW h μ u) (x p.1) (x p.2)
        = (((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1))
            * ((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * (boxW h μ u) (x p.1) (x p.2) := by
    intro x p
    by_cases h1 : x p.1 ∈ boxA v μ u
    · by_cases h2 : x p.2 ∈ boxA v μ u
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]; ring
      · rw [hzR (x p.1) (x p.2) h2]; ring
    · rw [hzL (x p.1) (x p.2) h1]; ring
  -- integrability of each pair integrand on the compact box
  obtain ⟨C0, hC0⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  set C : ℝ := max C0 0 with hCdef
  have hC0n : 0 ≤ C := le_max_right _ _
  have hΦb : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      |Φ x| ≤ C := by
    intro x hx
    have hx' := hC0 x hx
    rw [Real.norm_eq_abs] at hx'
    exact le_trans hx' (le_max_left _ _)
  have hΦsqm : MeasureTheory.AEStronglyMeasurable (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
    (hΦc.pow 2).aestronglyMeasurable
  have hΦsqb : ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      |(Φ x) ^ 2| ≤ C ^ 2 :=
    (MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n _)).mpr
      (Filter.Eventually.of_forall (fun x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hΦb x hx) 2))
  have hIntPair : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * (boxW h μ u) (x p.1) (x p.2))
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      MeasureTheory.volume := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by
      have hp' := hp
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
      exact hp'
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair
      (N := n) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (R := R)
      hℓ hd (Submission.BoseGases.v_integrable hv1)
      (fun z hz => Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz)
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM hR hRχ u hpne
      hΦsqm (pow_nonneg hC0n 2) hΦsqb
  -- assembly: pull the sum out of the integral and use the pointwise identity termwise
  calc
    (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          (boxW h μ u) (x p.1) (x p.2)))
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
            (Φ x) ^ 2 * (boxW h μ u) (x p.1) (x p.2) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [show (Φ x) ^ 2 * ((1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
              (boxW h μ u) (x p.1) (x p.2))
            = (1 / 2) * ((Φ x) ^ 2 * ∑ p ∈ Submission.BoseGases.pairSet n,
              (boxW h μ u) (x p.1) (x p.2)) by ring]
        congr 1
        exact Finset.mul_sum _ _ _
    _ = (1 / 2) * ∫ x in Submission.BoseGases.abox n
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          ∑ p ∈ Submission.BoseGases.pairSet n,
            (Φ x) ^ 2 * (boxW h μ u) (x p.1) (x p.2) := by
        rw [MeasureTheory.integral_const_mul]
    _ = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Φ x) ^ 2 * (boxW h μ u) (x p.1) (x p.2) := by
        rw [MeasureTheory.integral_finsetSum _ (fun p hp => by
          simpa [MeasureTheory.IntegrableOn] using hIntPair p hp)]
    _ = (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1))
                * ((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
              * (boxW h μ u) (x p.1) (x p.2) := by
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        exact hpt x p

end

end Work.BoseFixB1S
