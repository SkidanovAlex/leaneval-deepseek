import Mathlib
import ChallengeDeps
import Submission.PotAppFull
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, brick S5e - the potapp-family cross-word bounds (FS lm:potapp,
# eq:d11apriori, eq:d2apriori, eq:d13apriori), corpus expectation form

For the chosen-branch stack (`h : ∃w, IsRadial w ∧ IsScatteringSolution w v`,
`w₀ := Classical.choose h`, kernels `w₁ := wPairC(ℓ, g0 v h)`,
`w₂ := wPairC(ℓ, g2 v h)`), every continuous `Φ` over the centred box
satisfies the three *unconditional* cross-word estimates (no Q₄ term, no
a-priori hypothesis; the constant is universal, χ-dependent):

* `qcross_d11` (FS eq:d11apriori): |q1word(μ, w₁, w₂) Φ| ≤ C·a·(N̂²/ℓ³+μ²ℓ³)·∫Φ²
* `qcross_d2` (FS eq:d2apriori, the PᵢPⱼ·w₁·QⱼQᵢ summand of q2word):
  |Σ_{p∈pairSet}∫(P P Φ)(Q Q Φ)·w₁| ≤ C·a·N̂²/ℓ³·∫Φ²
* `qcross_d13` (FS eq:d13apriori, Q′=Q): |q3word(w₁) Φ| ≤ C·a·N̂²/ℓ³·∫Φ²

ROUTE (uniform): (i) per-pair peel bounds (PotAppPeel.peel_sq_kernel_le with
fibre constants from KernelFibreBound.w1c_fibre_abs_le / w2c_fibre_abs_le on
the kernels |w₁| / |w₂|); (ii) projection contraction + exact count identities
of CentredSector (cS1_le_norm_sq, cnPlus_le_norm_sq, cnPlus_add_cS1,
pair_contract, sum_pairSet_second_eq); (iii) Cauchy-Schwarz on the pair sums;
(iv) AM-GM μ·N̂ ≤ ½(μ²ℓ³+N̂²/ℓ³) for the linear-μ term of q1word.
Explicit universal constant: `qcrossC`; proofs may end with any explicit
bound whose constant is ≤ qcrossC.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Universal (χ-dependent) constant for the potapp-family bounds. -/
noncomputable def qcrossC : ℝ := 1000000 * chiSup ^ 2 * (8 * π)


/-- Chosen-branch cube-fibre bound for `|w₂| = |wPair(g₂)|`:
`|∫_y in acube |w₂(x,y)|| ≤ chiSup²·2·(16π·a v)` pointwise. -/
lemma w2abs_fibre_acube_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |(∫ y in acube ℓ, |wPair ℓ (g2 v h) x y|)| ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
  let hAbs : ℝ³ → ℝ := fun z => |g2 v h z|
  have hAbsI : MeasureTheory.Integrable hAbs := by
    have hi := g2_integrable hR hv_nonneg hvrad hv_supp h
    simpa [hAbs, Real.norm_eq_abs] using hi.abs
  have hAbs_supp : ∀ z : ℝ³, R ≤ ‖z‖ → hAbs z = 0 := by
    intro z hz
    dsimp [hAbs]
    rw [g2_zero_of_norm_ge hv_supp hz h, abs_zero]
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g2 v h z := g2_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hAbs_eq : (∫ z : ℝ³, |hAbs z|) = ∫ z : ℝ³, g2 v h z := by
    have hEq1 : (∫ z : ℝ³, |hAbs z|) = ∫ z : ℝ³, |g2 v h z| := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp [hAbs]
      exact abs_abs (g2 v h z)
    rw [hEq1]
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  have hint : (∫ y in acube ℓ, |wPair ℓ (g2 v h) x y|)
      = ∫ y in acube ℓ, wPair ℓ hAbs x y := by
    apply integral_congr_ae
    filter_upwards with y
    exact wPair_abs_eq ℓ (g2 v h) x y
  have hleInt : (∫ z : ℝ³, g2 v h z) ≤ 16 * π * a v :=
    (g2_integral_bounds hR hv_nonneg hvrad hv_supp h).2
  have hnnC : 0 ≤ chiSup ^ 2 * 2 := by
    exact mul_nonneg (sq_nonneg chiSup) (by norm_num)
  calc
    |(∫ y in acube ℓ, |wPair ℓ (g2 v h) x y|)|
        = |∫ y in acube ℓ, wPair ℓ hAbs x y| := by
            rw [hint]
    _ ≤ chiSup ^ 2 * 2 * (∫ z : ℝ³, |hAbs z|) := by
            exact fibre_acube_abs_le (h := hAbs) hℓ (le_of_lt hR) hRℓ hAbsI hAbs_supp x
    _ = chiSup ^ 2 * 2 * (∫ z : ℝ³, g2 v h z) := by
            rw [hAbs_eq]
    _ ≤ chiSup ^ 2 * 2 * (16 * π * a v) := by
            exact mul_le_mul_of_nonneg_left hleInt hnnC


/-- Generic per-pair peel bound for an absolute-value pair kernel
`|wPair(ℓ,h)|` at `(x i, x j)` with an even, integrable numerator `h` whose
absolute cube-fibre is bounded by `C`. -/
lemma peel_sq_wPair_abs_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hh : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (heven : ∀ z : ℝ³, h (-z) = h z)
    {C : ℝ} (hfib : ∀ x : ℝ³, |(∫ y in acube ℓ, |wPair ℓ h x y|)| ≤ C)
    {i j : Fin N} (hij : i ≠ j) {Ψ : XN N → ℝ} (hΨc : Continuous Ψ) :
    (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 * |wPair ℓ h (x i) (x j)|)
      ≤ C * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2) := by
  classical
  let k : ℝ³ → ℝ³ → ℝ := fun a b => |wPair ℓ h a b|
  have hPic : Continuous (aP ℓ i Ψ) := aP_continuous hℓ i hΨc
  have hsym (x y : ℝ³) : |wPair ℓ h x y| = |wPair ℓ h y x| := by
    have hw : wPair ℓ h x y = wPair ℓ h y x := by
      simpa [wPairC] using wPairC_sym heven ℓ x y
    rw [hw]
  -- integrability of the peel-integrand (absolute kernel at (x j)(x i))
  have hki : IntegrableOn (fun x : XN N => (aP ℓ i Ψ x) ^ 2 * k (x j) (x i))
      (abox N ℓ) volume := by
    have hs : IntegrableOn (fun x : XN N =>
        (aP ℓ i Ψ x) ^ 2 * |wPair ℓ h (x j) (x i)|) (abox N ℓ) volume := by
      have hs' : IntegrableOn (fun x : XN N =>
          (aP ℓ i Ψ x) ^ 2 * |wPair ℓ h (x i) (x j)|) (abox N ℓ) volume :=
        sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ hij hPic
      refine hs'.congr ?_
      filter_upwards with x
      exact congrArg (fun t : ℝ => (aP ℓ i Ψ x) ^ 2 * t) (hsym (x i) (x j))
    simpa [k] using hs
  have hpeel := peel_sq_kernel_le hℓ hij (k := k) (C := C) hfib (Ψ := Ψ) hΨc hki
  -- convert the peel conclusion to the desired orientation (x i)(x j)
  have hEq : (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 * |wPair ℓ h (x i) (x j)|)
      = ∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 * k (x j) (x i) := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [k]
    exact congrArg (fun t : ℝ => (aP ℓ i Ψ x) ^ 2 * t) (hsym (x i) (x j))
  calc
    (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 * |wPair ℓ h (x i) (x j)|)
        = ∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2 * k (x j) (x i) := hEq
    _ ≤ C * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (aP ℓ i Ψ x) ^ 2) := by
        simpa [k] using hpeel


/-- AM–GM cross-term bound: `|∫ f·g·wPair| ≤ ½∫f²|wPair| + ½∫g²|wPair|`
for continuous `f,g` on the box. -/
lemma abs_integral_mul_mul_wPair_le_half {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {h : ℝ³ → ℝ} (hh : Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * chiR0) {i j : Fin N} (hij : i ≠ j) {f g : XN N → ℝ}
    (hfc : Continuous f) (hgc : Continuous g) :
    |∫ x in abox N ℓ, f x * (g x * wPair ℓ h (x i) (x j))|
      ≤ (1 / 2) * (∫ x in abox N ℓ, (f x) ^ 2 * |wPair ℓ h (x i) (x j)|) +
        (1 / 2) * (∫ x in abox N ℓ, (g x) ^ 2 * |wPair ℓ h (x i) (x j)|) := by
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  let k : ℝ³ → ℝ³ → ℝ := fun a b => |wPair ℓ h a b|
  have hfi : Integrable (fun x : XN N => (f x) ^ 2 * k (x i) (x j)) μ := by
    have hs : IntegrableOn (fun x : XN N => (f x) ^ 2 * |wPair ℓ h (x i) (x j)|)
        (abox N ℓ) volume := sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ hij hfc
    simpa [k, μ, IntegrableOn] using hs
  have hgi : Integrable (fun x : XN N => (g x) ^ 2 * k (x i) (x j)) μ := by
    have hs : IntegrableOn (fun x : XN N => (g x) ^ 2 * |wPair ℓ h (x i) (x j)|)
        (abox N ℓ) volume := sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ hij hgc
    simpa [k, μ, IntegrableOn] using hs
  let R : XN N → ℝ := fun x => (1 / 2) * ((f x) ^ 2 * k (x i) (x j))
      + (1 / 2) * ((g x) ^ 2 * k (x i) (x j))
  have hR : Integrable R μ := by
    dsimp [R]
    exact (hfi.const_mul (1 / 2)).add (hgi.const_mul (1 / 2))
  -- |f g k| is integrable (dominated by R)
  have hk_aesm : AEStronglyMeasurable (fun x : XN N => k (x i) (x j)) μ := by
    have hs : IntegrableOn (fun x : XN N => |wPair ℓ h (x i) (x j)|) (abox N ℓ) volume := by
      simpa using (sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ hij
        (S := fun _ : XN N => (1 : ℝ)) (by fun_prop : Continuous (fun _ : XN N => (1 : ℝ))))
    simpa [k, μ, IntegrableOn] using hs.aestronglyMeasurable
  have hfgk_eq (x : XN N) :
      |f x| * (|g x| * k (x i) (x j)) = |f x * (g x * wPair ℓ h (x i) (x j))| := by
    dsimp [k]
    rw [← abs_mul, ← abs_mul]
  have hfgk_aesm : AEStronglyMeasurable (fun x : XN N => |f x * (g x * wPair ℓ h (x i) (x j))|) μ := by
    have hmul : AEStronglyMeasurable (fun x : XN N => |f x| * (|g x| * k (x i) (x j))) μ := by
      exact (hfc.aestronglyMeasurable.norm.mul (hgc.aestronglyMeasurable.norm.mul hk_aesm))
    refine hmul.congr ?_
    filter_upwards with x
    exact hfgk_eq x
  have hfgk_dom : ∀ᵐ x ∂μ, |f x * (g x * wPair ℓ h (x i) (x j))| ≤ R x := by
    refine ae_of_all _ (fun x => ?_)
    have h2 : 2 * (|f x| * |g x|) ≤ (f x) ^ 2 + (g x) ^ 2 := by
      simpa [sq_abs] using abs_two_mul_le_sq_sq (f x) (g x)
    have hk0 : 0 ≤ k (x i) (x j) := abs_nonneg _
    have h1 : |f x| * |g x| * k (x i) (x j) ≤
        (1 / 2) * ((f x) ^ 2 + (g x) ^ 2) * k (x i) (x j) := by
      have hline : |f x| * |g x| ≤ (1 / 2) * ((f x) ^ 2 + (g x) ^ 2) := by
        nlinarith [h2]
      exact mul_le_mul_of_nonneg_right hline hk0
    have hdom : |f x| * (|g x| * k (x i) (x j)) ≤ R x := by
      dsimp [R]
      calc
        |f x| * (|g x| * k (x i) (x j)) = |f x| * |g x| * k (x i) (x j) := by ring
        _ ≤ (1 / 2) * ((f x) ^ 2 + (g x) ^ 2) * k (x i) (x j) := h1
        _ = (1 / 2) * ((f x) ^ 2 * k (x i) (x j)) + (1 / 2) * ((g x) ^ 2 * k (x i) (x j)) := by ring
    rw [← hfgk_eq x]
    exact hdom
  have hfgk_int : Integrable (fun x : XN N => |f x * (g x * wPair ℓ h (x i) (x j))|) μ := by
    refine Integrable.mono' hR hfgk_aesm ?_
    filter_upwards [hfgk_dom] with x hx
    simpa [Real.norm_eq_abs] using hx
  calc
    |∫ x in abox N ℓ, f x * (g x * wPair ℓ h (x i) (x j))|
        ≤ ∫ x in abox N ℓ, |f x * (g x * wPair ℓ h (x i) (x j))| := by
            simpa using (abs_integral_le_integral_abs (μ := μ)
              (f := fun x : XN N => f x * (g x * wPair ℓ h (x i) (x j))))
    _ ≤ ∫ x in abox N ℓ, R x := by
            exact integral_mono_ae (μ := μ) hfgk_int hR hfgk_dom
    _ = (1 / 2) * (∫ x in abox N ℓ, (f x) ^ 2 * k (x i) (x j)) +
        (1 / 2) * (∫ x in abox N ℓ, (g x) ^ 2 * k (x i) (x j)) := by
            calc
              (∫ x in abox N ℓ, R x)
                  = (∫ x in abox N ℓ, (1 / 2) * ((f x) ^ 2 * k (x i) (x j))) +
                      (∫ x in abox N ℓ, (1 / 2) * ((g x) ^ 2 * k (x i) (x j))) := by
                        dsimp [R]
                        rw [integral_add (hfi.const_mul (1 / 2)) (hgi.const_mul (1 / 2))]
              _ = (1 / 2) * (∫ x in abox N ℓ, (f x) ^ 2 * k (x i) (x j)) +
                  (1 / 2) * (∫ x in abox N ℓ, (g x) ^ 2 * k (x i) (x j)) := by
                        rw [integral_const_mul]
                        rw [integral_const_mul]




/-- The pair word of `q1word` (one `Q` on one side): bounded by the two
absolute `wPair`-masses via AM–GM. -/
lemma q1pair_abs_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
          wPair ℓ h (x p.1) (x p.2)|
      ≤ (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|) := by
  classical
  calc
    |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
          wPair ℓ h (x p.1) (x p.2)|
        ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
              wPair ℓ h (x p.1) (x p.2)| := by
          simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N)
            (f := fun p : Fin N × Fin N => ∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) *
                wPair ℓ h (x p.1) (x p.2)))
    _ ≤ ∑ p ∈ pairSet N,
          ((1 / 2) * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
            + (1 / 2) * (∫ x in abox N ℓ,
              (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hf : Continuous (aP ℓ p.1 (aQ ℓ p.2 Φ)) :=
            aP_continuous hℓ p.1 (aQ_continuous hℓ p.2 hΦc)
          have hg : Continuous (aP ℓ p.1 (aP ℓ p.2 Φ)) :=
            aP_continuous hℓ p.1 (aP_continuous hℓ p.2 hΦc)
          simpa [mul_assoc] using (abs_integral_mul_mul_wPair_le_half hℓ hh hsupp hRℓ hne
            (f := aP ℓ p.1 (aQ ℓ p.2 Φ)) (g := aP ℓ p.1 (aP ℓ p.2 Φ)) hf hg)
    _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|) := by
          rw [Finset.sum_add_distrib]
          simp_rw [← Finset.mul_sum]

/-- Peeled mass sum, `(P P)`-family: `Σ_p∫(P_{p.1}P_{p.2}Φ)²·|wPair| ≤ C·(ℓ³)⁻¹·Σ_p∫(P_{p.1}P_{p.2}Φ)²`. -/
lemma masssum_PP_abs_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hh : Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (heven : ∀ z : ℝ³, h (-z) = h z)
    {C : ℝ} (hfib : ∀ x : ℝ³, |(∫ y in acube ℓ, |wPair ℓ h x y|)| ≤ C)
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
      ≤ C * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
  classical
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
        ≤ ∑ p ∈ pairSet N, C * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hΨc : Continuous (aP ℓ p.2 Φ) := aP_continuous hℓ p.2 hΦc
          exact peel_sq_wPair_abs_le hℓ hR hRℓ hh hsupp heven hfib hne
            (i := p.1) (j := p.2) (Ψ := aP ℓ p.2 Φ) hΨc
    _ = C * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
          rw [← Finset.mul_sum]

/-- Peeled mass sum, `(P Q)`-family: `Σ_p∫(P_{p.1}Q_{p.2}Φ)²·|wPair| ≤ C·(ℓ³)⁻¹·Σ_p∫(P_{p.1}Q_{p.2}Φ)²`. -/
lemma masssum_PQ_abs_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hh : Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (heven : ∀ z : ℝ³, h (-z) = h z)
    {C : ℝ} (hfib : ∀ x : ℝ³, |(∫ y in acube ℓ, |wPair ℓ h x y|)| ≤ C)
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
      ≤ C * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := by
  classical
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
        ≤ ∑ p ∈ pairSet N, C * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hΨc : Continuous (aQ ℓ p.2 Φ) := aQ_continuous hℓ p.2 hΦc
          exact peel_sq_wPair_abs_le hℓ hR hRℓ hh hsupp heven hfib hne
            (i := p.1) (j := p.2) (Ψ := aQ ℓ p.2 Φ) hΨc
    _ = C * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := by
          rw [← Finset.mul_sum]


/-- The `|w₂|`-weighted `(P P)`-pair mass is bounded by `C₂·(ℓ³)⁻¹·N̂²·∫Φ²`,
`C₂ := chiSup²·2·(16·π·a v)`. -/
lemma q1massPP_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  let C2 : ℝ := chiSup ^ 2 * 2 * (16 * π * a v)
  have hmm := masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
    (fun z hz => g2_zero_of_norm_ge hv_supp hz h) (g2_even hvrad h)
    (C := C2) (fun x => w2abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
  have hC2nn : 0 ≤ C2 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    have h16p : 0 ≤ 16 * π := by nlinarith [Real.pi_nonneg]
    have h16 : 0 ≤ 16 * π * a v := mul_nonneg h16p hav0
    dsimp [C2]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) h16
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hJ : 0 ≤ (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|) := by
            simp [wPairC]
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
            simpa [C2] using hmm
    _ = C2 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
            rw [pairSum_A_eq]
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cS1 ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (cS2_le_n_mul_cS1 hℓ hΦc)
              (mul_nonneg hC2nn hLinv)
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2nn hLinv)
            exact mul_le_mul_of_nonneg_left (cS1_le_norm_sq hℓ hΦc) hN0
    _ = C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by ring
    _ = (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by rfl

/-- The `|w₂|`-weighted `(P Q)`-pair mass is bounded by `C₂·(ℓ³)⁻¹·N̂²·∫Φ²`. -/
lemma q1massPQ_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  let C2 : ℝ := chiSup ^ 2 * 2 * (16 * π * a v)
  have hmm := masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
    (fun z hz => g2_zero_of_norm_ge hv_supp hz h) (g2_even hvrad h)
    (C := C2) (fun x => w2abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
  have hC2nn : 0 ≤ C2 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    have h16p : 0 ≤ 16 * π := by nlinarith [Real.pi_nonneg]
    have h16 : 0 ≤ 16 * π * a v := mul_nonneg h16p hav0
    dsimp [C2]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) h16
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hJ : 0 ≤ (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
        = (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|) := by
            simp [wPairC]
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := by
            simpa [C2] using hmm
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC2nn hLinv)
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
    _ = C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by ring
    _ = (chiSup ^ 2 * 2 * (16 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by rfl


set_option maxHeartbeats 8000000

/-- FS eq:d11apriori, corpus expectation form: |q1word| ≤ C·(a v)·(N̂²/ℓ³ + μ²ℓ³)·∫Φ². -/
theorem qcross_d11 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ| ≤
      qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g0 v h)
  let w2 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g2 v h)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let Xbig : ℝ := (N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3
  let M1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |w2 (x p.1) (x p.2)|
  let M2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |w2 (x p.1) (x p.2)|
  let T1 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2)
  let T2 : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ w1 (x i))
  let S : ℝ := ∑ i : Fin N, ∫ x in abox N ℓ,
      (aP ℓ i Φ x) * (∫ y in acube ℓ, wPair ℓ (g0 v h) (x i) y) * (aQ ℓ i Φ x)
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let C2 : ℝ := chiSup ^ 2 * 2 * (16 * π * a v)
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hX0 : 0 ≤ Xbig := by
    have h1 : 0 ≤ (N : ℝ) ^ 2 / ℓ ^ 3 := by positivity
    have h2 : 0 ≤ μ ^ 2 * ℓ ^ 3 := by positivity
    dsimp [Xbig]
    nlinarith
  have hC0nn : 0 ≤ C0 := by
    have h16 : 0 ≤ 8 * π * a v := by
      have h8 : 0 ≤ 8 * π := by nlinarith [Real.pi_nonneg]
      exact mul_nonneg h8 hav0
    dsimp [C0]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) h16
  have hC2nn : 0 ≤ C2 := by
    have h16 : 0 ≤ 16 * π * a v := by
      have h8 : 0 ≤ 16 * π := by nlinarith [Real.pi_nonneg]
      exact mul_nonneg h8 hav0
    dsimp [C2]
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : (0 : ℝ) ≤ 2)) h16
  -- the decomposition of q1word into its pair part and one-body part
  have hq1eq : q1word (N := N) ℓ μ w1 w2 Φ = 2 * T1 - 2 * μ * T2 := by
    dsimp [q1word, T1, T2, w1, w2]
  -- absolute value split
  have hB1 : |q1word (N := N) ℓ μ w1 w2 Φ| ≤ 2 * |T1| + |2 * μ * T2| := by
    rw [hq1eq]
    calc
      |2 * T1 - 2 * μ * T2| = |2 * T1 + (-(2 * μ * T2))| := by rw [sub_eq_add_neg]
      _ ≤ |2 * T1| + |-(2 * μ * T2)| := abs_add_le (2 * T1) (-(2 * μ * T2))
      _ = |2 * T1| + |2 * μ * T2| := by rw [abs_neg]
      _ = 2 * |T1| + |2 * μ * T2| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  -- pair part: |T1| ≤ ½M1 + ½M2
  have hpair : |T1| ≤ (1 / 2) * M1 + (1 / 2) * M2 := by
    have hg2i : MeasureTheory.Integrable (g2 v h) :=
      g2_integrable hR hv_nonneg hvrad hv_supp h
    have hg2s : ∀ z : ℝ³, R ≤ ‖z‖ → g2 v h z = 0 :=
      fun z hz => g2_zero_of_norm_ge hv_supp hz h
    have h := q1pair_abs_le hℓ hg2i hg2s hRℓ (h := g2 v h) hΦc
    simpa [T1, M1, M2, w2, wPairC] using h
  have hpairb : 2 * |T1| ≤ M1 + M2 := by
    calc
      2 * |T1| ≤ 2 * ((1 / 2) * M1 + (1 / 2) * M2) :=
            mul_le_mul_of_nonneg_left hpair (by norm_num)
      _ = M1 + M2 := by ring
  -- one-body part: |2·μ·T2| ≤ μ·C0·N̂·J
  have hTS : T2 = S := by
    dsimp [T2, S]
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    filter_upwards with x
    dsimp [w1]
    simp [w1Fibre, wPairC]
    ring
  have hob : |2 * μ * T2| ≤ μ * C0 * (N : ℝ) * J := by
    have hcross := onebody_cross_abs_le (N := N) hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hμ hΦc
    have hcross' : |2 * μ * S| ≤ μ * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
      simpa [C0] using hcross
    have h : |2 * μ * S| ≤ μ * C0 * (N : ℝ) * J := by
      calc
        |2 * μ * S| ≤ μ * C0 * (cS1 ℓ Φ + cnPlus ℓ Φ) := hcross'
        _ = μ * C0 * (cnPlus ℓ Φ + cS1 ℓ Φ) := by ring
        _ = μ * C0 * (N : ℝ) * J := by
              rw [cnPlus_add_cS1 hℓ hΦc]
              dsimp [J]
              ring
    rw [hTS]
    exact h
  -- mass bounds for the two families
  have hm2 : M2 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm := q1massPP_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [M2, C2, J, w2, wPairC] using hmm
  have hm1 : M1 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm := q1massPQ_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [M1, C2, J, w2, wPairC] using hmm
  -- assemble: |q1word| ≤ (M1+M2) + μ·C0·N̂·J
  have hc1 : 2 * |T1| + |2 * μ * T2| ≤ (M1 + M2) + μ * C0 * (N : ℝ) * J := by
    nlinarith [hpairb, hob]
  have hc2 : (M1 + M2) + μ * C0 * (N : ℝ) * J ≤
      (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 + μ * C0 * (N : ℝ)) * J := by
    nlinarith [hm1, hm2]
  -- assemble: |q1word| ≤ (M1+M2) + μ·C0·N̂·J
  have hc1 : 2 * |T1| + |2 * μ * T2| ≤ (M1 + M2) + μ * C0 * (N : ℝ) * J := by
    nlinarith [hpairb, hob]
  have hc2 : (M1 + M2) + μ * C0 * (N : ℝ) * J ≤
      (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 + μ * C0 * (N : ℝ)) * J := by
    nlinarith [hm1, hm2]
  -- expand the constants: 2·C2 = (chiSup²·π)·64·(a v), C0 = (chiSup²·π)·16·(a v)
  have hconst :
      (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 + μ * C0 * (N : ℝ)) * J =
        (a v) * (chiSup ^ 2 * π) * J *
          (64 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + 16 * μ * (N : ℝ)) := by
    dsimp [C0, C2]
    ring
  -- the linear-μ term: μ·N̂ ≤ ½·Xbig ; the N̂²-term: N̂²·(ℓ³)⁻¹ ≤ Xbig
  have hℓ3 : 0 < ℓ ^ 3 := pow_pos hℓ 3
  have hℓ3nz : ℓ ^ 3 ≠ 0 := ne_of_gt hℓ3
  have hmain : 2 * μ * (N : ℝ) * ℓ ^ 3 ≤ μ ^ 2 * ℓ ^ 6 + (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (μ * ℓ ^ 3 - (N : ℝ))]
  have h2muN : 2 * μ * (N : ℝ) ≤ μ ^ 2 * ℓ ^ 3 + (N : ℝ) ^ 2 / ℓ ^ 3 := by
    calc
      2 * μ * (N : ℝ) ≤ (μ ^ 2 * ℓ ^ 6 + (N : ℝ) ^ 2) * (ℓ ^ 3)⁻¹ := by
        calc
          2 * μ * (N : ℝ) = (2 * μ * (N : ℝ) * ℓ ^ 3) * (ℓ ^ 3)⁻¹ := by
            field_simp [hℓ3nz]
          _ ≤ (μ ^ 2 * ℓ ^ 6 + (N : ℝ) ^ 2) * (ℓ ^ 3)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hℓ3.le)
      _ = μ ^ 2 * ℓ ^ 3 + (N : ℝ) ^ 2 / ℓ ^ 3 := by
        field_simp [hℓ3nz]
  have hmuN : μ * (N : ℝ) ≤ (1 / 2) * Xbig := by
    dsimp [Xbig]
    nlinarith
  have hN2inv : (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ ≤ Xbig := by
    have hmu2 : 0 ≤ μ ^ 2 * ℓ ^ 3 := by positivity
    have h : (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ ≤ (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ + μ ^ 2 * ℓ ^ 3 := by
      linarith
    dsimp [Xbig]
    rw [div_eq_mul_inv]
    exact h
  -- G := 64·X2 + 16·μ·N̂ ≤ 72·Xbig, and the nonneg outer factor
  have hGle : 64 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + 16 * μ * (N : ℝ) ≤ 72 * Xbig := by
    have h1 : 64 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) ≤ 64 * Xbig := by
      exact mul_le_mul_of_nonneg_left hN2inv (by norm_num : (0 : ℝ) ≤ 64)
    have h2 : 16 * (μ * (N : ℝ)) ≤ 16 * ((1 / 2) * Xbig) := by
      exact mul_le_mul_of_nonneg_left hmuN (by norm_num : (0 : ℝ) ≤ 16)
    nlinarith
  have hFnn : 0 ≤ (a v) * (chiSup ^ 2 * π) * J := by
    have h1 : 0 ≤ (a v) * (chiSup ^ 2 * π) := mul_nonneg hav0 (mul_nonneg (sq_nonneg chiSup) Real.pi_nonneg)
    exact mul_nonneg h1 hJ
  have hBmid :
      (a v) * (chiSup ^ 2 * π) * J * (64 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + 16 * μ * (N : ℝ))
        ≤ (a v) * (chiSup ^ 2 * π) * J * (72 * Xbig) := by
    exact mul_le_mul_of_nonneg_left hGle hFnn
  -- final absorption: coefficient (chiSup²·π)·72·(a v) ≤ qcrossC·(a v)
  have hBtarget : (a v) * (chiSup ^ 2 * π) * J * (72 * Xbig) ≤
      qcrossC * (a v) * Xbig * J := by
    have hW : 0 ≤ chiSup ^ 2 * π * (a v) * Xbig * J := by
      have h1 : 0 ≤ chiSup ^ 2 * π := mul_nonneg (sq_nonneg chiSup) Real.pi_nonneg
      have h2 : 0 ≤ chiSup ^ 2 * π * (a v) := mul_nonneg h1 hav0
      have h3 : 0 ≤ chiSup ^ 2 * π * (a v) * Xbig := mul_nonneg h2 hX0
      exact mul_nonneg h3 hJ
    calc
      (a v) * (chiSup ^ 2 * π) * J * (72 * Xbig)
          = (72 : ℝ) * (chiSup ^ 2 * π * (a v) * Xbig * J) := by ring
      _ ≤ (1000000 * 8 : ℝ) * (chiSup ^ 2 * π * (a v) * Xbig * J) := by
        exact mul_le_mul_of_nonneg_right (by norm_num : (72 : ℝ) ≤ 1000000 * 8) hW
      _ = qcrossC * (a v) * Xbig * J := by
        dsimp [qcrossC]
        ring
  -- assemble the whole chain
  calc
    |q1word (N := N) ℓ μ w1 w2 Φ| ≤ 2 * |T1| + |2 * μ * T2| := hB1
    _ ≤ (M1 + M2) + μ * C0 * (N : ℝ) * J := hc1
    _ ≤ (2 * C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 + μ * C0 * (N : ℝ)) * J := hc2
    _ = (a v) * (chiSup ^ 2 * π) * J *
          (64 * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) + 16 * μ * (N : ℝ)) := hconst
    _ ≤ (a v) * (chiSup ^ 2 * π) * J * (72 * Xbig) := hBmid
    _ ≤ qcrossC * (a v) * Xbig * J := hBtarget
    _ = qcrossC * (a v) * (((N : ℝ) ^ 2 / ℓ ^ 3) + μ ^ 2 * ℓ ^ 3) *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
          dsimp [Xbig, J]


/-- The pair-swap `(p.1,p.2) ↦ (p.2,p.1)` is a bijection of `pairSet N`. -/
lemma sum_pairSet_swap {N : ℕ} (f : Fin N × Fin N → ℝ) :
    (∑ p ∈ pairSet N, f (p.2, p.1)) = ∑ p ∈ pairSet N, f p := by
  refine Finset.sum_bij (s := pairSet N) (t := pairSet N)
    (i := fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    simp [pairSet]
    exact Ne.symm hne
  · intro p₁ _ p₂ _ h
    cases p₁
    cases p₂
    simp at h
    exact Prod.ext h.2 h.1
  · intro b hb
    refine ⟨(b.2, b.1), ?_, ?_⟩
    · have hne : b.2 ≠ b.1 := by
        have hne' : b.1 ≠ b.2 := by simpa [pairSet] using hb
        exact Ne.symm hne'
      simp [pairSet]
      exact hne
    · rfl
  · intro p _
    rfl

/-- Sum over pairs of a function of the first coordinate equals `(N−1)·Σg`. -/
lemma sum_pairSet_first_eq (N : ℕ) (g : Fin N → ℝ) :
    (∑ p ∈ pairSet N, g p.1) = ((N : ℝ) - 1) * (∑ i : Fin N, g i) := by
  calc
    (∑ p ∈ pairSet N, g p.1) = ∑ p ∈ pairSet N, g p.2 := by
      exact sum_pairSet_swap (fun p : Fin N × Fin N => g p.2)
    _ = ((N : ℝ) - 1) * (∑ i : Fin N, g i) := sum_pairSet_second_eq N g

/-- `wPair` is monotone in its numerator at the single point `x−y`. -/
lemma wPair_mono_at {ℓ : ℝ} {a b : ℝ³ → ℝ} (x y : ℝ³)
    (hab : a (x - y) ≤ b (x - y)) : wPair ℓ a x y ≤ wPair ℓ b x y := by
  have hnnx : 0 ≤ chiScale ℓ x := chiScale_nonneg ℓ x
  have hnny : 0 ≤ chiScale ℓ y := chiScale_nonneg ℓ y
  have hc : 0 ≤ convScale ℓ (x - y) := convScale_nonneg ℓ (x - y)
  have hdiv : a (x - y) / convScale ℓ (x - y) ≤ b (x - y) / convScale ℓ (x - y) :=
    div_le_div_of_nonneg_right hab hc
  have h1 : a (x - y) / convScale ℓ (x - y) * chiScale ℓ y
      ≤ b (x - y) / convScale ℓ (x - y) * chiScale ℓ y :=
    mul_le_mul_of_nonneg_right hdiv hnny
  calc
    wPair ℓ a x y = chiScale ℓ x * (a (x - y) / convScale ℓ (x - y) * chiScale ℓ y) := by
      dsimp [wPair, wScaled]
      ring
    _ ≤ chiScale ℓ x * (b (x - y) / convScale ℓ (x - y) * chiScale ℓ y) :=
      mul_le_mul_of_nonneg_left h1 hnnx
    _ = wPair ℓ b x y := by
      dsimp [wPair, wScaled]
      ring

/-- Pointwise absolute bound of `wPair`: if `|a(x−y)| ≤ b(x−y)` then
`|wPair(ℓ,a)(x,y)| ≤ wPair(ℓ,b)(x,y)`. -/
lemma wPair_abs_le_pair {ℓ : ℝ} {a b : ℝ³ → ℝ} (x y : ℝ³)
    (hab : |a (x - y)| ≤ b (x - y)) : |wPair ℓ a x y| ≤ wPair ℓ b x y := by
  rw [wPair_abs_eq]
  exact wPair_mono_at x y hab

/-- `|g₀| ≤ v` a.e. in the chosen branch (`0 ≤ v`, `0 ≤ w₀ ≤ 1` a.e.). -/
lemma g0_abs_le_v_ae {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ᵐ z : ℝ³, |g0 v h z| ≤ v z := by
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  filter_upwards [hb.1, hb.2] with z hz0 hz1
  have h1m : 0 ≤ 1 - Classical.choose h z := by linarith
  have h1 : |1 - Classical.choose h z| ≤ 1 := by
    rw [abs_of_nonneg h1m]
    linarith
  have hvz : 0 ≤ v z := hv_nonneg z
  calc
    |g0 v h z| = |v z * (1 - Classical.choose h z)| := by rfl
    _ = |v z| * |1 - Classical.choose h z| := abs_mul _ _
    _ = v z * |1 - Classical.choose h z| := by rw [abs_of_nonneg hvz]
    _ ≤ v z * 1 := mul_le_mul_of_nonneg_left h1 hvz
    _ = v z := by ring

/-- Pointwise a.e.-comparison `|w₁| ≤ w` along a pair difference: a.e. in `x`,
`|wPair(g₀)(x_i,x_j)| ≤ wPair(v)(x_i,x_j)`. -/
lemma w1_abs_le_w_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |wPair ℓ (g0 v h) (x i) (x j)| ≤ wPair ℓ v (x i) (x j) := by
  have hg0 : ∀ᵐ z : ℝ³, |g0 v h z| ≤ v z :=
    g0_abs_le_v_ae hR hv_nonneg hvrad hv_supp h
  have hpb := ae_pair_pullback (N := N) hℓ hij hg0
  filter_upwards [hpb] with x hx
  exact wPair_abs_le_pair (a := g0 v h) (b := v) (x i) (x j) hx

/-- `|ω| = |w₀(xᵢ−xⱼ)| ≤ 1` a.e. on the box, in the chosen branch. -/
lemma w0_abs_le_one_box_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |Classical.choose h (x i - x j)| ≤ 1 := by
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  have hle : ∀ᵐ z : ℝ³, |Classical.choose h z| ≤ 1 := by
    filter_upwards [hb.1, hb.2] with z hz0 hz1
    rw [abs_of_nonneg hz0]
    exact hz1
  exact ae_pair_pullback (N := N) hℓ hij hle

/-- `v` vanishes outside `ball 0 R` (from the support hypothesis). -/
lemma v_zero_of_norm_ge {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {z : ℝ³} (hz : R ≤ ‖z‖) :
    v z = 0 := by
  by_contra h
  have hmem : z ∈ tsupport v := subset_tsupport v (by simpa using h)
  have hball : z ∈ ball (0 : ℝ³) R := hv_supp hmem
  have hlt : ‖z‖ < R := by simpa using hball
  linarith

/-- `v` is integrable on the whole space when `MemLp v 1`. -/
lemma v_integrable_whole {v : ℝ³ → ℝ} (hv : MemLp v 1) : MeasureTheory.Integrable v :=
  v_integrable hv

/-- Absolute-value fibre bound for `|wPair(g₀)|` over the centred cube
(`|w₁|-kernel`); constant `C1 := chiSup²·2·(8·π·a v)`. -/
lemma w1abs_fibre_acube_abs_le_used {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |(∫ y in acube ℓ, |wPair ℓ (g0 v h) x y|)| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  simpa [wPairC] using w1abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x



/-- Excited family with swapped slots: `Σ_p‖P_{p.2}Q_{p.1}Φ‖² ≤ N·n₊`. -/
lemma pairSum_Q_swap_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) ≤
      (N : ℝ) * cnPlus ℓ Φ := by
  have hswap : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2)
      = ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 := by
    exact sum_pairSet_swap (fun p : Fin N × Fin N =>
      ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2)
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2)
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 := hswap
    _ ≤ (N : ℝ) * cnPlus ℓ Φ := pairSum_B_le hℓ hΦc

/-- Peeled mass sum for the swapped `(P Q)`-family:
`Σ_p∫(P_{p.2}Q_{p.1}Φ)²·|wPair| ≤ C·(ℓ³)⁻¹·Σ_p∫(P_{p.2}Q_{p.1}Φ)²`. -/
lemma masssum_Qsw_abs_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 ≤ R)
    (hRℓ : R ≤ ℓ * chiR0) {h : ℝ³ → ℝ} (hh : MeasureTheory.Integrable h)
    (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (heven : ∀ z : ℝ³, h (-z) = h z)
    {C : ℝ} (hfib : ∀ x : ℝ³, |(∫ y in acube ℓ, |wPair ℓ h x y|)| ≤ C)
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
      ≤ C * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := by
  classical
  let k : ℝ³ → ℝ³ → ℝ := fun a b => |wPair ℓ h a b|
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ h (x p.1) (x p.2)|)
        ≤ ∑ p ∈ pairSet N, C * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hΨc : Continuous (aQ ℓ p.1 Φ) := aQ_continuous hℓ p.1 hΦc
          have hPic : Continuous (aP ℓ p.2 (aQ ℓ p.1 Φ)) := aP_continuous hℓ p.2 hΨc
          have hs : IntegrableOn (fun x : XN N =>
              (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ h (x p.2) (x p.1)|)
              (abox N ℓ) volume :=
            sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ
              (i := p.2) (j := p.1) (hij := Ne.symm hne) (S := aP ℓ p.2 (aQ ℓ p.1 Φ)) hPic
          have hki : IntegrableOn (fun x : XN N =>
              (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * k (x p.1) (x p.2))
              (abox N ℓ) volume := by
            refine hs.congr ?_
            filter_upwards with x
            dsimp [k]
            have hsw : wPair ℓ h (x p.2) (x p.1) = wPair ℓ h (x p.1) (x p.2) := by
              exact (wPairC_sym (h := h) heven ℓ (x p.1) (x p.2)).symm
            rw [hsw]
          have hpeel := peel_sq_kernel_le hℓ (hij := Ne.symm hne) (k := k) (C := C)
            (hkC := hfib) (Ψ := aQ ℓ p.1 Φ) hΨc hki
          simpa [k] using hpeel
    _ = C * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := by
          rw [← Finset.mul_sum]

lemma q4B_sq_w_integrable {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : XN N =>
      (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j))
      (abox N ℓ) volume := by
  classical
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  let QQ : XN N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let SS : XN N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : XN N → ℝ := fun x => Classical.choose h (x i - x j)
  let wt : XN N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let BB : XN N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  have hQQc : Continuous QQ := by
    dsimp [QQ]
    exact aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : XN N => aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have homx : AEStronglyMeasurable omx μ := by
    dsimp [omx, μ]
    simpa using (w0_diff_aem (N := N) (ℓ := ℓ) hℓ hij
      (w0 := Classical.choose h) (w0_spec h).2.lhs_integrable)
  have hvzero : ∀ z : ℝ³, R ≤ ‖z‖ → v z = 0 := fun z hz => v_zero_of_norm_ge hv_supp hz
  have hwI : Integrable wt μ := by
    have hs : IntegrableOn (fun x : XN N => wPair ℓ v (x i) (x j)) (abox N ℓ) volume := by
      simpa using (integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
        (S := fun x : XN N => (1 : ℝ))
        (by fun_prop : Continuous (fun _ : XN N => (1 : ℝ))))
    simpa [wt, μ, IntegrableOn] using hs
  have hw : AEStronglyMeasurable wt μ := hwI.aestronglyMeasurable
  have hBsm : AEStronglyMeasurable BB μ := by
    have hBQQ : BB = fun x => QQ x + omx x * SS x := by
      funext x
      dsimp [BB, QQ, SS, omx]
      rfl
    rw [hBQQ]
    exact (hQQc.aestronglyMeasurable.add (homx.mul hSc.aestronglyMeasurable))
  have hB2sm : AEStronglyMeasurable (fun x : XN N => BB x * BB x) μ := by
    convert hBsm.mul hBsm using 1
    all_goals
      ext x
      rfl
  have hQQ2w : Integrable (fun x : XN N => (QQ x) ^ 2 * wt x) μ := by
    have hs : IntegrableOn (fun x : XN N => (QQ x) ^ 2 * wPair ℓ v (x i) (x j)) (abox N ℓ) volume := by
      simpa [QQ] using (integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
        (S := fun x : XN N => (aQ ℓ j (aQ ℓ i Φ) x) ^ 2) (hQQc.pow 2))
    simpa [wt, μ, IntegrableOn] using hs
  have hS2w : Integrable (fun x : XN N => (SS x) ^ 2 * wt x) μ := by
    have hs : IntegrableOn (fun x : XN N => (SS x) ^ 2 * wPair ℓ v (x i) (x j)) (abox N ℓ) volume := by
      simpa [SS] using (integrableOn_slot_wPair hℓ (v_integrable hv_memL1) hvzero hRℓ hij
        (S := fun x : XN N => (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2))
        (hSc.pow 2))
    simpa [wt, μ, IntegrableOn] using hs
  have hdomI : Integrable (fun x : XN N => 2 * ((QQ x) ^ 2 * wt x) + 2 * ((SS x) ^ 2 * wt x)) μ :=
    (hQQ2w.const_mul 2).add (hS2w.const_mul 2)
  have hwNN : ∀ x : XN N, 0 ≤ wt x := by
    intro x
    dsimp [wt]
    exact wPairC_nonneg hv_nonneg ℓ (x i) (x j)
  have hbnd : ∀ᵐ x ∂μ, |BB x| ≤ |QQ x| + |SS x| := by
    have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
      dsimp [omx, μ]
      simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
    filter_upwards [homxb] with x hx
    have hBx : BB x = QQ x + omx x * SS x := by
      dsimp [BB, QQ, SS, omx]
      rfl
    rw [hBx]
    calc
      |QQ x + omx x * SS x| ≤ |QQ x| + |omx x * SS x| := abs_add_le _ _
      _ = |QQ x| + |omx x| * |SS x| := by rw [abs_mul]
      _ ≤ |QQ x| + 1 * |SS x| := by
        nlinarith [mul_le_mul_of_nonneg_right hx (abs_nonneg (SS x))]
      _ = |QQ x| + |SS x| := by ring
  have hbnd2 : ∀ᵐ x ∂μ, (BB x) ^ 2 ≤ 2 * (QQ x) ^ 2 + 2 * (SS x) ^ 2 := by
    filter_upwards [hbnd] with x hx
    have hnn : 0 ≤ |QQ x| + |SS x| := add_nonneg (abs_nonneg (QQ x)) (abs_nonneg (SS x))
    have hle2 : (BB x) ^ 2 ≤ (|QQ x| + |SS x|) ^ 2 := by
      calc
        (BB x) ^ 2 = |BB x| ^ 2 := by rw [← sq_abs (BB x)]
        _ ≤ (|QQ x| + |SS x|) ^ 2 := by
          apply sq_le_sq.mpr
          rw [abs_of_nonneg hnn]
          simpa using hx
    have hle : (|QQ x| + |SS x|) ^ 2 ≤ 2 * (QQ x) ^ 2 + 2 * (SS x) ^ 2 := by
      rw [← sq_abs (QQ x), ← sq_abs (SS x)]
      nlinarith [sq_nonneg (|QQ x| - |SS x|)]
    exact le_trans hle2 hle
  have hBdom : ∀ᵐ x ∂μ,
      (BB x) ^ 2 * wt x ≤ 2 * ((QQ x) ^ 2 * wt x) + 2 * ((SS x) ^ 2 * wt x) := by
    filter_upwards [hbnd2] with x hx
    have hw0 : 0 ≤ wt x := hwNN x
    calc
      (BB x) ^ 2 * wt x ≤ (2 * (QQ x) ^ 2 + 2 * (SS x) ^ 2) * wt x :=
        mul_le_mul_of_nonneg_right hx hw0
      _ = 2 * ((QQ x) ^ 2 * wt x) + 2 * ((SS x) ^ 2 * wt x) := by ring
  have hb2w : Integrable (fun x : XN N => (BB x) ^ 2 * wt x) μ := by
    refine Integrable.mono' hdomI ?_ ?_
    · have hprod : AEStronglyMeasurable (fun x : XN N => (BB x * BB x) * wt x) μ := by
        convert hB2sm.mul hw using 1
        all_goals
          ext x
          rfl
      simpa [pow_two, mul_assoc] using hprod
    · change ∀ᵐ x ∂μ, ‖(BB x) ^ 2 * wt x‖ ≤ 2 * ((QQ x) ^ 2 * wt x) + 2 * ((SS x) ^ 2 * wt x)
      filter_upwards [hBdom] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact hx
      · exact mul_nonneg (sq_nonneg (BB x)) (hwNN x)
  change Integrable (fun x : XN N =>
      (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) μ
  simpa [BB, wt, μ, IntegrableOn] using hb2w

lemma abs_mul_le_half_sq_sq (a b : ℝ) : |a| * |b| ≤ (1 / 2) * a ^ 2 + (1 / 2) * b ^ 2 := by
  have h : 2 * (|a| * |b|) ≤ a ^ 2 + b ^ 2 := by
    rw [← sq_abs a, ← sq_abs b]
    nlinarith [sq_nonneg (|a| - |b|)]
  nlinarith

lemma qcross_d2_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
      ≤ (∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ (g0 v h) (x i) (x j)|))
        + (1 / 2) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
  classical
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  let FF : XN N → ℝ := fun x => aP ℓ i (aP ℓ j Φ) x
  let QQ : XN N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let SS : XN N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : XN N → ℝ := fun x => Classical.choose h (x i - x j)
  let WW : XN N → ℝ := fun x => |wPair ℓ (g0 v h) (x i) (x j)|
  let wt : XN N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let BB : XN N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  have hFc : Continuous FF := by
    dsimp [FF]
    exact aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : XN N => aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0supp : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hF2W : Integrable (fun x : XN N => (FF x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : XN N => (FF x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := FF) hFc
    simpa [FF, WW, μ, IntegrableOn] using hs
  have hS2W : Integrable (fun x : XN N => (SS x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : XN N => (SS x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := SS) hSc
    simpa [SS, WW, μ, IntegrableOn] using hs
  have hB2wt : Integrable (fun x : XN N => (BB x) ^ 2 * wt x) μ := by
    have hs := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB, wt, μ, IntegrableOn] using hs
  have hU : Integrable (fun x : XN N =>
      (FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * wt x)) μ := by
    have h1 : Integrable (fun x : XN N => (FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hF2W.add (hS2W.const_mul (1 / 2))
    refine (h1.add (hB2wt.const_mul (1 / 2))).congr ?_
    filter_upwards with x
    rfl
  have hWnn : ∀ x : XN N, 0 ≤ WW x := by
    intro x
    dsimp [WW]
    exact abs_nonneg _
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hWlewt : ∀ᵐ x ∂μ, WW x ≤ wt x := by
    dsimp [WW, wt, μ]
    simpa using (w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hmain : ∀ᵐ x ∂μ,
      |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|
        ≤ (FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * wt x) := by
    filter_upwards [homxb, hWlewt] with x homx1 hWle
    have hQQ : QQ x = BB x - omx x * SS x := by
      dsimp [QQ, BB, SS, omx, q4B, omC]
      ring
    have hQQb : |QQ x| ≤ |BB x| + |SS x| := by
      rw [hQQ]
      calc
        |BB x - omx x * SS x| = |BB x + (-(omx x * SS x))| := by rw [sub_eq_add_neg]
        _ ≤ |BB x| + |-(omx x * SS x)| := abs_add_le _ _
        _ = |BB x| + |omx x * SS x| := by rw [abs_neg]
        _ = |BB x| + |omx x| * |SS x| := by rw [abs_mul]
        _ ≤ |BB x| + 1 * |SS x| := by
          nlinarith [mul_le_mul_of_nonneg_right homx1 (abs_nonneg (SS x))]
        _ = |BB x| + |SS x| := by ring
    have hW0 : 0 ≤ WW x := hWnn x
    have hF1 : |FF x| * |QQ x| * WW x ≤ |FF x| * (|BB x| + |SS x|) * WW x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQQb (abs_nonneg (FF x))) hW0
    have hFB1 : |FF x| * |BB x| ≤ (1 / 2) * (FF x) ^ 2 + (1 / 2) * (BB x) ^ 2 :=
      abs_mul_le_half_sq_sq (FF x) (BB x)
    have hFB2 : |FF x| * |BB x| * WW x ≤ ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (BB x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFB1 hW0
    have hFS1 : |FF x| * |SS x| ≤ (1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2 :=
      abs_mul_le_half_sq_sq (FF x) (SS x)
    have hFS2 : |FF x| * |SS x| * WW x ≤ ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFS1 hW0
    have hBW : (1 / 2) * ((BB x) ^ 2 * WW x) ≤ (1 / 2) * ((BB x) ^ 2 * wt x) := by
      have h1 : (BB x) ^ 2 * WW x ≤ (BB x) ^ 2 * wt x := by
        nlinarith [mul_le_mul_of_nonneg_left hWle (sq_nonneg (BB x))]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    calc
      |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|
          = |FF x| * |QQ x * wPair ℓ (g0 v h) (x i) (x j)| := abs_mul _ _
      _ = |FF x| * (|QQ x| * |wPair ℓ (g0 v h) (x i) (x j)|) := by rw [abs_mul]
      _ = |FF x| * (|QQ x| * WW x) := by rfl
      _ = |FF x| * |QQ x| * WW x := by ring
      _ ≤ |FF x| * (|BB x| + |SS x|) * WW x := hF1
      _ = |FF x| * |BB x| * WW x + |FF x| * |SS x| * WW x := by ring
      _ ≤ ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (BB x) ^ 2) * WW x
          + ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
          exact add_le_add hFB2 hFS2
      _ = (FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * WW x) := by ring
      _ ≤ (FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * wt x) := by
          nlinarith [hBW]
  have hL1 : |∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
      ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := by
    have hEq : (fun x : XN N =>
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j))
        =ᵐ[μ] (fun x : XN N => FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))) := by
      refine ae_of_all _ (fun x => ?_)
      dsimp [FF, QQ]
      ring
    calc
      |∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
          = |∫ x : XN N, FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j)) ∂μ| := by
            congr 1
            rw [integral_congr_ae (μ := μ) hEq]
      _ ≤ ∫ x : XN N, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| ∂μ := by
            exact abs_integral_le_integral_abs (μ := μ)
  have hL2 : (∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|)
      ≤ ∫ x in abox N ℓ,
          ((FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * wt x)) := by
    refine integral_mono_of_nonneg (μ := μ) ?_ hU ?_
    · filter_upwards with x
      exact abs_nonneg _
    · exact hmain
  have hL3 : (∫ x : XN N,
          ((FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * wt x)) ∂μ)
      = (∫ x : XN N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (BB x) ^ 2 * wt x ∂μ) := by
    have h12 : Integrable (fun x : XN N => (FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hF2W.add (hS2W.const_mul (1 / 2))
    have hT2 : Integrable (fun x : XN N => (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hS2W.const_mul (1 / 2)
    have hT3 : Integrable (fun x : XN N => (1 / 2) * ((BB x) ^ 2 * wt x)) μ :=
      hB2wt.const_mul (1 / 2)
    calc
      (∫ x, ((FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * wt x)) ∂μ)
          = (∫ x, (((FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x)) + (1 / 2) * ((BB x) ^ 2 * wt x)) ∂μ) := by
              apply integral_congr_ae
              filter_upwards with x
              ring
      _ = (∫ x, (FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) ∂μ)
          + (∫ x, (1 / 2) * ((BB x) ^ 2 * wt x) ∂μ) := integral_add h12 hT3
      _ = (∫ x, (FF x) ^ 2 * WW x ∂μ) + (∫ x, (1 / 2) * ((SS x) ^ 2 * WW x) ∂μ)
          + (∫ x, (1 / 2) * ((BB x) ^ 2 * wt x) ∂μ) := by
              rw [integral_add hF2W hT2]
      _ = (∫ x, (FF x) ^ 2 * WW x ∂μ) + (1 / 2) * (∫ x, (SS x) ^ 2 * WW x ∂μ)
          + (1 / 2) * (∫ x, (BB x) ^ 2 * wt x ∂μ) := by
              rw [integral_const_mul, integral_const_mul]
  calc
    |∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
        ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := hL1
    _ ≤ ∫ x in abox N ℓ,
        ((FF x) ^ 2 * WW x + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 2) * ((BB x) ^ 2 * wt x)) := hL2
    _ = (∫ x : XN N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (BB x) ^ 2 * wt x ∂μ) := by
          simpa [μ] using hL3
    _ = (∫ x in abox N ℓ,
          (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ (g0 v h) (x i) (x j)|))
        + (1 / 2) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
          simp [μ, FF, QQ, SS, BB, WW, wt, mul_assoc, add_assoc]

/-- Pointwise square-3 estimate against the `|wPair h|` weight: for
`(a+b+c)² ≤ 3(a²+b²+c²)` pointwise, so integrating against the nonnegative
weight `|wPair h (x_i,x_j)|` gives the same for the integrals. -/
lemma sq3_mass_pair_le {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : MeasureTheory.Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * chiR0) {a b c : XN N → ℝ}
    (hac : Continuous a) (hbc : Continuous b) (hcc : Continuous c)
    {i j : Fin N} (hij : i ≠ j) :
    (∫ x in abox N ℓ, ((a x + b x + c x) ^ 2) * |wPair ℓ h (x i) (x j)|)
      ≤ 3 * ((∫ x in abox N ℓ, (a x) ^ 2 * |wPair ℓ h (x i) (x j)|)
          + (∫ x in abox N ℓ, (b x) ^ 2 * |wPair ℓ h (x i) (x j)|)
          + (∫ x in abox N ℓ, (c x) ^ 2 * |wPair ℓ h (x i) (x j)|)) := by
  classical
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  let W : XN N → ℝ := fun x => |wPair ℓ h (x i) (x j)|
  have hWnn : ∀ x : XN N, 0 ≤ W x := by
    intro x
    dsimp [W]
    exact abs_nonneg _
  have ha2W : Integrable (fun x : XN N => (a x) ^ 2 * W x) μ := by
    have hs : IntegrableOn (fun x : XN N => (a x) ^ 2 * |wPair ℓ h (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ hij (S := a) hac
    simpa [W, μ, IntegrableOn] using hs
  have hb2W : Integrable (fun x : XN N => (b x) ^ 2 * W x) μ := by
    have hs : IntegrableOn (fun x : XN N => (b x) ^ 2 * |wPair ℓ h (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ hij (S := b) hbc
    simpa [W, μ, IntegrableOn] using hs
  have hc2W : Integrable (fun x : XN N => (c x) ^ 2 * W x) μ := by
    have hs : IntegrableOn (fun x : XN N => (c x) ^ 2 * |wPair ℓ h (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hh hsupp hRℓ hij (S := c) hcc
    simpa [W, μ, IntegrableOn] using hs
  have hsumI : Integrable (fun x : XN N => (a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x) μ := by
    have h12 : Integrable (fun x : XN N => (a x) ^ 2 * W x + (b x) ^ 2 * W x) μ := ha2W.add hb2W
    refine (h12.add hc2W).congr ?_
    filter_upwards with x
    rfl
  have hmain : ∀ᵐ x ∂μ,
      ((a x + b x + c x) ^ 2) * W x ≤ 3 * ((a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x) := by
    filter_upwards with x
    have hsq := sq_three_le (a := a x) (b := b x) (c := c x)
    have hW0 : 0 ≤ W x := hWnn x
    calc
      ((a x + b x + c x) ^ 2) * W x ≤ 3 * ((a x) ^ 2 + (b x) ^ 2 + (c x) ^ 2) * W x :=
        mul_le_mul_of_nonneg_right hsq hW0
      _ = 3 * ((a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x) := by ring
  have hsplit : (∫ x : XN N, (a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x ∂μ)
      = (∫ x : XN N, (a x) ^ 2 * W x ∂μ) + (∫ x : XN N, (b x) ^ 2 * W x ∂μ)
        + (∫ x : XN N, (c x) ^ 2 * W x ∂μ) := by
    have h12 : Integrable (fun x : XN N => (a x) ^ 2 * W x + (b x) ^ 2 * W x) μ := ha2W.add hb2W
    calc
      (∫ x, (a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x ∂μ)
          = (∫ x, (a x) ^ 2 * W x + (b x) ^ 2 * W x ∂μ) + (∫ x, (c x) ^ 2 * W x ∂μ) := by
              rw [integral_add h12 hc2W]
      _ = ((∫ x, (a x) ^ 2 * W x ∂μ) + (∫ x, (b x) ^ 2 * W x ∂μ)) + (∫ x, (c x) ^ 2 * W x ∂μ) := by
              rw [integral_add ha2W hb2W]
  have hmono1 : (∫ x : XN N, ((a x + b x + c x) ^ 2) * W x ∂μ)
      ≤ ∫ x : XN N, 3 * ((a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x) ∂μ := by
    refine integral_mono_of_nonneg (μ := μ) ?_ ?_ ?_
    · filter_upwards with x
      exact mul_nonneg (sq_nonneg _) (hWnn x)
    · simpa [mul_assoc] using hsumI.const_mul 3
    · exact hmain
  have hLμ : (∫ x : XN N, ((a x + b x + c x) ^ 2) * W x ∂μ)
      ≤ 3 * ((∫ x : XN N, (a x) ^ 2 * W x ∂μ) + (∫ x : XN N, (b x) ^ 2 * W x ∂μ)
        + (∫ x : XN N, (c x) ^ 2 * W x ∂μ)) := by
    calc
      (∫ x, ((a x + b x + c x) ^ 2) * W x ∂μ)
          ≤ ∫ x, 3 * ((a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x) ∂μ := hmono1
      _ = 3 * (∫ x, (a x) ^ 2 * W x + (b x) ^ 2 * W x + (c x) ^ 2 * W x ∂μ) := by
              rw [integral_const_mul]
      _ = 3 * ((∫ x, (a x) ^ 2 * W x ∂μ) + (∫ x, (b x) ^ 2 * W x ∂μ)
          + (∫ x, (c x) ^ 2 * W x ∂μ)) := by
              rw [hsplit]
  calc
    (∫ x in abox N ℓ, ((a x + b x + c x) ^ 2) * |wPair ℓ h (x i) (x j)|)
        = ∫ x : XN N, ((a x + b x + c x) ^ 2) * W x ∂μ := by
            simp [μ, W]
    _ ≤ 3 * ((∫ x : XN N, (a x) ^ 2 * W x ∂μ) + (∫ x : XN N, (b x) ^ 2 * W x ∂μ)
        + (∫ x : XN N, (c x) ^ 2 * W x ∂μ)) := hLμ
    _ = 3 * ((∫ x in abox N ℓ, (a x) ^ 2 * |wPair ℓ h (x i) (x j)|)
          + (∫ x in abox N ℓ, (b x) ^ 2 * |wPair ℓ h (x i) (x j)|)
          + (∫ x in abox N ℓ, (c x) ^ 2 * |wPair ℓ h (x i) (x j)|)) := by
          simp [μ, W]

theorem qcross_d2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤
      qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  classical
  let C1 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ mA + (1 / 2) * mS + (1 / 2) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_d2_pair hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = mA + (1 / 2) * mS + (1 / 2) * mQ := by
            simp [mA, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : mQ = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hD : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤ mA + (1 / 2) * mS + q4word (N := N) ℓ
          (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    calc
      |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|
          ≤ ∑ p ∈ pairSet N, |∫ x in abox N ℓ,
              (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
              simpa using (Finset.abs_sum_le_sum_abs (s := pairSet N) (f := fun p : Fin N × Fin N =>
                ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
                  wPairC ℓ (g0 v h) (x p.1) (x p.2)))
      _ ≤ mA + (1 / 2) * mS + (1 / 2) * mQ := hsum_le
      _ = mA + (1 / 2) * mS + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rw [hq4]
          ring
  have hSsplit : mS ≤ 3 * (mA + mG2 + mG3) := by
    calc
      mS = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2) *
          |wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
            rfl
      _ ≤ ∑ p ∈ pairSet N, 3 * (
            (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
          have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
          simpa [wPairC] using (sq3_mass_pair_le hℓ hg0i hg0s hRℓ
            (a := fun x => aP ℓ p.2 (aP ℓ p.1 Φ) x)
            (hac := aP_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc))
            (b := fun x => aP ℓ p.2 (aQ ℓ p.1 Φ) x)
            (hbc := aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc))
            (c := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x)
            (hcc := aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)) hne)
      _ = 3 * (mA + mG2 + mG3) := by
          have hX : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|) = mA := by
            dsimp [mA]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_comm hℓ p.1 p.2 hΦc x]
          have hc : (∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)))
              = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_add_distrib]
          rw [hc]
          rw [hX]
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC1nn : 0 ≤ C1 := by
    dsimp [C1]
    positivity
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hM : C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≥ 0 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC1nn hLinv) (sq_nonneg (N : ℝ))) hJ0
  have hmA : mA ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) :=
      masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    calc
      mA = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mA, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := hmm
      _ = C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
            rw [pairSum_A_eq]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cS1 ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (cS2_le_n_mul_cS1 hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cS1_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG2 : mG2 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
      masssum_Qsw_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    calc
      mG2 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mG2, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_Q_swap_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG3 : mG3 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
      masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    have hEq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          apply integral_congr_ae
          filter_upwards with x
          rw [aP_aQ_comm hℓ hne hΦc x]
    calc
      mG3 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mG3, wPairC]
      _ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := hEq
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hC1le : (11 / 2) * C1 ≤ qcrossC * (a v) := by
    dsimp [C1, qcrossC]
    have hpos : 0 ≤ chiSup ^ 2 * π * (a v) := by
      exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) Real.pi_nonneg) hav0
    have h88 : (88 : ℝ) ≤ (1000000 * 8 : ℝ) := by norm_num
    have hmul : (88 : ℝ) * (chiSup ^ 2 * π * (a v)) ≤ (1000000 * 8) * (chiSup ^ 2 * π * (a v)) :=
      mul_le_mul_of_nonneg_right h88 hpos
    nlinarith [hmul]
  have hX0 : 0 ≤ (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ := by positivity
  have hMainAbs : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤
      (11 / 2) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    let M : ℝ := C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
    have hD' : |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤ mA + (1 / 2) * mS + q4 := by
      simpa [q4] using hD
    calc
      |∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
            wPairC ℓ (g0 v h) (x p.1) (x p.2)| ≤ mA + (1 / 2) * mS + q4 := hD'
      _ ≤ (11 / 2) * M + q4 := by
            nlinarith [hSsplit, hmA, hmG2, hmG3]
      _ = (11 / 2) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J + q4 := by
            dsimp [M]
            ring
      _ = (11 / 2) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hAbs : (11 / 2) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≤
      qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
    have h1 : (11 / 2) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
      calc
        (11 / 2) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2
            = ((11 / 2) * C1) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by ring
        _ ≤ (qcrossC * (a v)) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by
            exact mul_le_mul_of_nonneg_right hC1le hX0
        _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
            rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 hJ0
  calc
    |∑ p ∈ pairSet N,
        ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|
        ≤ (11 / 2) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hMainAbs
    _ ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          nlinarith [hAbs]
    _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rfl


lemma qcross_d13_pair {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (hv_memL1 : MemLp v 1)
    {i j : Fin N} (hij : i ≠ j) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
      ≤ (3 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ (g0 v h) (x i) (x j)|))
        + (1 / 4) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
  classical
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  let FF : XN N → ℝ := fun x => aP ℓ i (aQ ℓ j Φ) x
  let QQ : XN N → ℝ := fun x => aQ ℓ j (aQ ℓ i Φ) x
  let SS : XN N → ℝ := fun x => (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)
  let omx : XN N → ℝ := fun x => Classical.choose h (x i - x j)
  let WW : XN N → ℝ := fun x => |wPair ℓ (g0 v h) (x i) (x j)|
  let wt : XN N → ℝ := fun x => wPair ℓ v (x i) (x j)
  let BB : XN N → ℝ := fun x => q4B ℓ (omC (Classical.choose h)) Φ (i, j) x
  have hFc : Continuous FF := by
    dsimp [FF]
    exact aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hSc : Continuous SS := by
    dsimp [SS]
    have h1 : Continuous (fun x : XN N => aP ℓ j (aP ℓ i Φ) x + (aP ℓ j (aQ ℓ i Φ) x + aQ ℓ j (aP ℓ i Φ) x)) :=
      (aP_continuous hℓ j (aP_continuous hℓ i hΦc)).add
        ((aP_continuous hℓ j (aQ_continuous hℓ i hΦc)).add
          (aQ_continuous hℓ j (aP_continuous hℓ i hΦc)))
    simpa [add_assoc] using h1
  have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0supp : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hF2W : Integrable (fun x : XN N => (FF x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : XN N => (FF x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := FF) hFc
    simpa [FF, WW, μ, IntegrableOn] using hs
  have hS2W : Integrable (fun x : XN N => (SS x) ^ 2 * WW x) μ := by
    have hs : IntegrableOn (fun x : XN N => (SS x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0supp hRℓ hij (S := SS) hSc
    simpa [SS, WW, μ, IntegrableOn] using hs
  have hB2wt : Integrable (fun x : XN N => (BB x) ^ 2 * wt x) μ := by
    have hs := q4B_sq_w_integrable hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1 hij hΦc
    simpa [BB, wt, μ, IntegrableOn] using hs
  have hU : Integrable (fun x : XN N =>
      (3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * wt x)) μ := by
    have h1 : Integrable (fun x : XN N =>
        (3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      (hF2W.const_mul (3 / 2)).add (hS2W.const_mul (1 / 2))
    refine (h1.add (hB2wt.const_mul (1 / 4))).congr ?_
    filter_upwards with x
    rfl
  have hWnn : ∀ x : XN N, 0 ≤ WW x := by
    intro x
    dsimp [WW]
    exact abs_nonneg _
  have homxb : ∀ᵐ x ∂μ, |omx x| ≤ 1 := by
    dsimp [omx, μ]
    simpa using (w0_abs_le_one_box_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hWlewt : ∀ᵐ x ∂μ, WW x ≤ wt x := by
    dsimp [WW, wt, μ]
    simpa using (w1_abs_le_w_ae (N := N) hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hmain : ∀ᵐ x ∂μ,
      |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|
        ≤ (3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * wt x) := by
    filter_upwards [homxb, hWlewt] with x homx1 hWle
    have hQQ : QQ x = BB x - omx x * SS x := by
      dsimp [QQ, BB, SS, omx, q4B, omC]
      ring
    have hQQb : |QQ x| ≤ |BB x| + |SS x| := by
      rw [hQQ]
      calc
        |BB x - omx x * SS x| = |BB x + (-(omx x * SS x))| := by rw [sub_eq_add_neg]
        _ ≤ |BB x| + |-(omx x * SS x)| := abs_add_le _ _
        _ = |BB x| + |omx x * SS x| := by rw [abs_neg]
        _ = |BB x| + |omx x| * |SS x| := by rw [abs_mul]
        _ ≤ |BB x| + 1 * |SS x| := by
          nlinarith [mul_le_mul_of_nonneg_right homx1 (abs_nonneg (SS x))]
        _ = |BB x| + |SS x| := by ring
    have hW0 : 0 ≤ WW x := hWnn x
    have hF1 : |FF x| * |QQ x| * WW x ≤ |FF x| * (|BB x| + |SS x|) * WW x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQQb (abs_nonneg (FF x))) hW0
    have hFB1 : |FF x| * |BB x| ≤ (FF x) ^ 2 + (1 / 4) * (BB x) ^ 2 := by
      rw [← sq_abs (FF x), ← sq_abs (BB x)]
      have hq : 0 ≤ (|FF x| - (1 / 2) * |BB x|) ^ 2 := sq_nonneg _
      nlinarith
    have hFB2 : |FF x| * |BB x| * WW x ≤ ((FF x) ^ 2 + (1 / 4) * (BB x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFB1 hW0
    have hFS1 : |FF x| * |SS x| ≤ (1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2 :=
      abs_mul_le_half_sq_sq (FF x) (SS x)
    have hFS2 : |FF x| * |SS x| * WW x ≤ ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
      exact mul_le_mul_of_nonneg_right hFS1 hW0
    have hBW : (1 / 4) * ((BB x) ^ 2 * WW x) ≤ (1 / 4) * ((BB x) ^ 2 * wt x) := by
      have h1 : (BB x) ^ 2 * WW x ≤ (BB x) ^ 2 * wt x := by
        nlinarith [mul_le_mul_of_nonneg_left hWle (sq_nonneg (BB x))]
      exact mul_le_mul_of_nonneg_left h1 (by norm_num)
    calc
      |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|
          = |FF x| * |QQ x * wPair ℓ (g0 v h) (x i) (x j)| := abs_mul _ _
      _ = |FF x| * (|QQ x| * |wPair ℓ (g0 v h) (x i) (x j)|) := by rw [abs_mul]
      _ = |FF x| * (|QQ x| * WW x) := by rfl
      _ = |FF x| * |QQ x| * WW x := by ring
      _ ≤ |FF x| * (|BB x| + |SS x|) * WW x := hF1
      _ = |FF x| * |BB x| * WW x + |FF x| * |SS x| * WW x := by ring
      _ ≤ ((FF x) ^ 2 + (1 / 4) * (BB x) ^ 2) * WW x
          + ((1 / 2) * (FF x) ^ 2 + (1 / 2) * (SS x) ^ 2) * WW x := by
          exact add_le_add hFB2 hFS2
      _ = (3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * WW x) := by ring
      _ ≤ (3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * wt x) := by
          nlinarith [hBW]
  have hL1 : |∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
      ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := by
    have hEq : (fun x : XN N =>
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j))
        =ᵐ[μ] (fun x : XN N => FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))) := by
      refine ae_of_all _ (fun x => ?_)
      dsimp [FF, QQ]
      ring
    calc
      |∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
          = |∫ x : XN N, FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j)) ∂μ| := by
            congr 1
            rw [integral_congr_ae (μ := μ) hEq]
      _ ≤ ∫ x : XN N, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| ∂μ := by
            exact abs_integral_le_integral_abs (μ := μ)
  have hL2 : (∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))|)
      ≤ ∫ x in abox N ℓ,
          ((3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * wt x)) := by
    refine integral_mono_of_nonneg (μ := μ) ?_ hU ?_
    · filter_upwards with x
      exact abs_nonneg _
    · exact hmain
  have hL3 : (∫ x : XN N,
          ((3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * wt x)) ∂μ)
      = (3 / 2) * (∫ x : XN N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 4) * (∫ x : XN N, (BB x) ^ 2 * wt x ∂μ) := by
    have h12 : Integrable (fun x : XN N =>
        (3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      (hF2W.const_mul (3 / 2)).add (hS2W.const_mul (1 / 2))
    have hT1 : Integrable (fun x : XN N => (3 / 2) * ((FF x) ^ 2 * WW x)) μ :=
      hF2W.const_mul (3 / 2)
    have hT2 : Integrable (fun x : XN N => (1 / 2) * ((SS x) ^ 2 * WW x)) μ :=
      hS2W.const_mul (1 / 2)
    have hT3 : Integrable (fun x : XN N => (1 / 4) * ((BB x) ^ 2 * wt x)) μ :=
      hB2wt.const_mul (1 / 4)
    calc
      (∫ x, ((3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * wt x)) ∂μ)
          = (∫ x, (((3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x)) + (1 / 4) * ((BB x) ^ 2 * wt x)) ∂μ) := by
              apply integral_congr_ae
              filter_upwards with x
              ring
      _ = (∫ x, (3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) ∂μ)
          + (∫ x, (1 / 4) * ((BB x) ^ 2 * wt x) ∂μ) := integral_add h12 hT3
      _ = (∫ x, (3 / 2) * ((FF x) ^ 2 * WW x) ∂μ) + (∫ x, (1 / 2) * ((SS x) ^ 2 * WW x) ∂μ)
          + (∫ x, (1 / 4) * ((BB x) ^ 2 * wt x) ∂μ) := by
              rw [integral_add hT1 hT2]
      _ = (3 / 2) * (∫ x, (FF x) ^ 2 * WW x ∂μ) + (1 / 2) * (∫ x, (SS x) ^ 2 * WW x ∂μ)
          + (1 / 4) * (∫ x, (BB x) ^ 2 * wt x ∂μ) := by
              rw [integral_const_mul, integral_const_mul, integral_const_mul]
  calc
    |∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * wPair ℓ (g0 v h) (x i) (x j)|
        ≤ ∫ x in abox N ℓ, |FF x * (QQ x * wPair ℓ (g0 v h) (x i) (x j))| := hL1
    _ ≤ ∫ x in abox N ℓ,
        ((3 / 2) * ((FF x) ^ 2 * WW x) + (1 / 2) * ((SS x) ^ 2 * WW x) + (1 / 4) * ((BB x) ^ 2 * wt x)) := hL2
    _ = (3 / 2) * (∫ x : XN N, (FF x) ^ 2 * WW x ∂μ)
        + (1 / 2) * (∫ x : XN N, (SS x) ^ 2 * WW x ∂μ)
        + (1 / 4) * (∫ x : XN N, (BB x) ^ 2 * wt x ∂μ) := by
          simpa [μ] using hL3
    _ = (3 / 2) * (∫ x in abox N ℓ,
          (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        + (1 / 2) * (∫ x in abox N ℓ,
            (((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) ^ 2 *
              |wPair ℓ (g0 v h) (x i) (x j)|))
        + (1 / 4) * (∫ x in abox N ℓ,
            (q4B ℓ (omC (Classical.choose h)) Φ (i, j) x) ^ 2 * wPair ℓ v (x i) (x j)) := by
          simp [μ, FF, QQ, SS, BB, WW, wt, mul_assoc, add_assoc]

theorem qcross_d13 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
      qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  classical
  let C1 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let J : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let mA : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mS : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
        |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG2 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mG3 : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  let mQ : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
  let mG : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|
  have hsum_le : (∑ p ∈ pairSet N,
      |∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
          wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
      ≤ (3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ := by
    calc
      (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          ≤ ∑ p ∈ pairSet N,
              ((3 / 2) * (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 2) * (∫ x in abox N ℓ,
                  ((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2 *
                  |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (1 / 4) * (∫ x in abox N ℓ,
                  (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            simpa [wPairC] using (qcross_d13_pair hℓ hv_nonneg hvrad hR hv_supp h hRℓ hv_memL1
              (i := p.1) (j := p.2) hne hΦc)
      _ = (3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ := by
            simp [mG, mS, mQ, Finset.sum_add_distrib, Finset.mul_sum]
  have hq4 : mQ = 2 * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    dsimp [mQ]
    unfold q4word
    ring
  have hD : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
      3 * mG + mS + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    have hq4' : (1 / 2) * mQ = q4 := by
      dsimp [q4]
      rw [hq4]
      ring
    have h1 : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 2 * ((3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ) := by
      calc
        |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ|
            = |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))| := by
                rfl
        _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|) := by
                have habs := Finset.abs_sum_le_sum_abs (s := pairSet N) (f := fun p : Fin N × Fin N =>
                  ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))
                have h2 : (0 : ℝ) ≤ 2 := by norm_num
                calc
                  |2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2))|
                      = 2 * |∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
                          rw [abs_mul, abs_of_nonneg h2]
                  _ ≤ 2 * (∑ p ∈ pairSet N, |∫ x in abox N ℓ,
                          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * wPairC ℓ (g0 v h) (x p.1) (x p.2)|) := by
                          exact mul_le_mul_of_nonneg_left habs h2
        _ ≤ 2 * ((3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ) := by
                exact mul_le_mul_of_nonneg_left hsum_le (by norm_num)
    calc
      |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 2 * ((3 / 2) * mG + (1 / 2) * mS + (1 / 4) * mQ) := h1
      _ = 3 * mG + mS + (1 / 2) * mQ := by ring
      _ = 3 * mG + mS + q4 := by
            rw [← hq4']
      _ = 3 * mG + mS + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hSsplit : mS ≤ 3 * (mA + mG2 + mG3) := by
    calc
      mS = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (((aP ℓ p.2 (aP ℓ p.1 Φ) x + aP ℓ p.2 (aQ ℓ p.1 Φ) x + aQ ℓ p.2 (aP ℓ p.1 Φ) x)) ^ 2) *
          |wPairC ℓ (g0 v h) (x p.1) (x p.2)| := by
            rfl
      _ ≤ ∑ p ∈ pairSet N, 3 * (
            (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
          + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          have hg0i : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
          have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
          simpa [wPairC] using (sq3_mass_pair_le hℓ hg0i hg0s hRℓ
            (a := fun x => aP ℓ p.2 (aP ℓ p.1 Φ) x)
            (hac := aP_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc))
            (b := fun x => aP ℓ p.2 (aQ ℓ p.1 Φ) x)
            (hbc := aP_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc))
            (c := fun x => aQ ℓ p.2 (aP ℓ p.1 Φ) x)
            (hcc := aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)) hne)
      _ = 3 * (mA + mG2 + mG3) := by
          have hX : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|) = mA := by
            dsimp [mA]
            refine Finset.sum_congr rfl (fun p hp => ?_)
            apply integral_congr_ae
            filter_upwards with x
            rw [aP_comm hℓ p.1 p.2 hΦc x]
          have hc : (∑ p ∈ pairSet N, 3 * (
                (∫ x in abox N ℓ, (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
              + (∫ x in abox N ℓ, (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)))
              = 3 * ((∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)
                + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
                    (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPairC ℓ (g0 v h) (x p.1) (x p.2)|)) := by
                rw [← Finset.mul_sum]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_add_distrib]
          rw [hc]
          rw [hX]
  have hJ0 : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC1nn : 0 ≤ C1 := by
    dsimp [C1]
    positivity
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hmA : mA ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) :=
      masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    calc
      mA = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mA, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := hmm
      _ = C1 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
            rw [pairSum_A_eq]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cS1 ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (cS2_le_n_mul_cS1 hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cS1_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG2 : mG2 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) :=
      masssum_Qsw_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    calc
      mG2 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mG2, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_Q_swap_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG3 : mG3 ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
      masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    have hEq : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
          apply integral_congr_ae
          filter_upwards with x
          rw [aP_aQ_comm hℓ hne hΦc x]
    calc
      mG3 = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aQ ℓ p.2 (aP ℓ p.1 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mG3, wPairC]
      _ = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := hEq
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hmG : mG ≤ C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by
    have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)|)
        ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
            (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
      masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ (g0_integrable hR hv_supp h)
        (fun z hz => g0_zero_of_norm_ge hv_supp hz h) (g0_even hvrad h)
        (C := C1) (fun x => w1abs_fibre_acube_abs_le_used hR hv_nonneg hvrad hv_supp h hℓ hRℓ x) hΦc
    calc
      mG = ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x p.1) (x p.2)| := by
            simp [mG, wPairC]
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) := hmm
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * cnPlus ℓ Φ) := by
            exact mul_le_mul_of_nonneg_left (pairSum_B_le hℓ hΦc) (mul_nonneg hC1nn hLinv)
      _ ≤ C1 * (ℓ ^ 3)⁻¹ * ((N : ℝ) * ((N : ℝ) * J)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC1nn hLinv)
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J := by ring
  have hC1le : (12 : ℝ) * C1 ≤ qcrossC * (a v) := by
    dsimp [C1, qcrossC]
    have hpos : 0 ≤ chiSup ^ 2 * π * (a v) := by
      exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) Real.pi_nonneg) hav0
    have h192 : (192 : ℝ) ≤ (1000000 * 8 : ℝ) := by norm_num
    have hmul : (192 : ℝ) * (chiSup ^ 2 * π * (a v)) ≤ (1000000 * 8) * (chiSup ^ 2 * π * (a v)) :=
      mul_le_mul_of_nonneg_right h192 hpos
    nlinarith [hmul]
  have hX0 : 0 ≤ (N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹ := by positivity
  have hMain : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤
      (12 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
    let q4 : ℝ := q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ
    let M : ℝ := C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
    have hD' : |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 3 * mG + mS + q4 := by
      simpa [q4] using hD
    calc
      |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ| ≤ 3 * mG + mS + q4 := hD'
      _ ≤ 12 * M + q4 := by
            nlinarith [hSsplit, hmA, hmG2, hmG3, hmG]
      _ = (12 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J + q4 := by
            dsimp [M]
            ring
      _ = (12 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
            rfl
  have hAbs : (12 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J ≤
      qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J := by
    have h1 : (12 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
      calc
        (12 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2
            = ((12 : ℝ) * C1) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by ring
        _ ≤ (qcrossC * (a v)) * ((N : ℝ) ^ 2 * (ℓ ^ 3)⁻¹) := by
            exact mul_le_mul_of_nonneg_right hC1le hX0
        _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) := by
            rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 hJ0
  calc
    |q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ|
        ≤ (12 : ℝ) * C1 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * J
          + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := hMain
    _ ≤ qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) * J
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          nlinarith [hAbs]
    _ = qcrossC * (a v) * ((N : ℝ) ^ 2 / ℓ ^ 3) *
        (∫ x in abox N ℓ, (Φ x) ^ 2)
      + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          rfl

end BoseGases
end Submission
