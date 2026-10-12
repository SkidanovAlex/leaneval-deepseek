import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.PotAppPeel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## `potapp` helper 2: the `M²`-sum bound

Auxiliary material for `potapp_M2sq_le`. -/

/-- `(a+b+c)² ≤ 3(a²+b²+c²)` pointwise. -/
lemma sq_three_le {a b c : ℝ} : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

/-- `|1 − w₀| ≤ 2` a.e. on the box along the pair difference, for the chosen
scattering solution. -/
lemma w0_one_sub_abs_le_two_ae {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |1 - Classical.choose h (x i - x j)| ≤ 2 := by
  let w0 : ℝ³ → ℝ := Classical.choose h
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  have h01 : ∀ᵐ z : ℝ³, 0 ≤ w0 z := hb.1
  have h02 : ∀ᵐ z : ℝ³, w0 z ≤ 1 := hb.2
  have habs : ∀ᵐ z : ℝ³, |1 - w0 z| ≤ 2 := by
    filter_upwards [h01, h02] with z hz0 hz1
    have h1m : 0 ≤ 1 - w0 z := by linarith
    rw [abs_of_nonneg h1m]
    linarith
  simpa [w0] using ae_pair_pullback (N := N) (ℓ := ℓ) hℓ hij habs

/-- `0 ≤ (8·π·a v)` in the chosen branch. -/
lemma av_eightpi_nonneg {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ 8 * π * a v := by
  have hb := av_bounds_weak hR hv_nonneg hvrad hv_supp h
  have hpi8 : 0 ≤ (8 * π : ℝ) := mul_nonneg (by norm_num) Real.pi_nonneg
  nlinarith [mul_nonneg hpi8 hb.1]

/-- a squared continuous slot factor times `|wPair(ℓ,h)(xᵢ,xⱼ)|` is integrable. -/
lemma sq_slot_wPair_abs_integrable {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0) (hRℓ : R ≤ ℓ * chiR0)
    {i j : Fin N} (hij : i ≠ j) {S : XN N → ℝ} (hSc : Continuous S) :
    IntegrableOn (fun x : XN N => (S x) ^ 2 * |wPair ℓ h (x i) (x j)|) (abox N ℓ) volume := by
  have hS2 : Continuous (fun x : XN N => (S x) ^ 2) := hSc.pow 2
  have hbase : IntegrableOn (fun x : XN N => (S x) ^ 2 * wPair ℓ h (x i) (x j)) (abox N ℓ) volume :=
    integrableOn_slot_wPair hℓ hh hsupp hRℓ hij hS2
  have hEq : (fun x : XN N => |(S x) ^ 2 * wPair ℓ h (x i) (x j)|) =ᵐ[volume.restrict (abox N ℓ)]
      (fun x : XN N => (S x) ^ 2 * |wPair ℓ h (x i) (x j)|) := by
    refine ae_of_all _ (fun x => ?_)
    calc
      |(S x) ^ 2 * wPair ℓ h (x i) (x j)| = |(S x) ^ 2| * |wPair ℓ h (x i) (x j)| := abs_mul _ _
      _ = (S x) ^ 2 * |wPair ℓ h (x i) (x j)| := by rw [abs_of_nonneg (sq_nonneg (S x))]
  change Integrable (fun x : XN N => (S x) ^ 2 * |wPair ℓ h (x i) (x j)|)
      (volume.restrict (abox N ℓ))
  exact (hbase.integrable.abs.congr hEq)

/-- Pair-condensate family `A`: by definition `Σ_p ∫A_p² = cS2`. -/
lemma pairSum_A_eq (N : ℕ) (ℓ : ℝ) {Φ : XN N → ℝ} :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) = cS2 ℓ Φ := by
  rfl

/-- Excited family `B := aP p.1 (aQ p.2 Φ)`: the mass sum is ≤ `N·n₊`. -/
lemma pairSum_B_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) ≤
      (N : ℝ) * cnPlus ℓ Φ := by
  have hle (p : Fin N × Fin N) (hp : p ∈ pairSet N) :
      (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) ≤
        (∫ x in abox N ℓ, (aQ ℓ p.2 Φ x) ^ 2) := by
    exact aP_sq_le hℓ p.1 (aQ_continuous hℓ p.2 hΦc)
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2)
        ≤ ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.2 Φ x) ^ 2 := by
          exact Finset.sum_le_sum (fun p hp => hle p hp)
    _ = ((N : ℝ) - 1) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
          exact sum_pairSet_second_eq N (fun i : Fin N => ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
    _ = ((N : ℝ) - 1) * cnPlus ℓ Φ := by simp [cnPlus]
    _ ≤ (N : ℝ) * cnPlus ℓ Φ := by
      have hc : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
      have h1 : (N : ℝ) - 1 ≤ (N : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right h1 hc

/-- Excited family `C := aQ p.1 (aP p.2 Φ)`: the mass sum is ≤ `N·n₊`. -/
lemma pairSum_C_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) ≤
      (N : ℝ) * cnPlus ℓ Φ := by
  have hle (p : Fin N × Fin N) (hp : p ∈ pairSet N) :
      (∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) ≤
        (∫ x in abox N ℓ, (aQ ℓ p.1 Φ x) ^ 2) := by
    have hne : p.2 ≠ p.1 := by
      have h01 : p.1 ≠ p.2 := by simpa [pairSet] using hp
      exact h01.symm
    have hc : Continuous (aQ ℓ p.1 Φ) := aQ_continuous hℓ p.1 hΦc
    calc
      (∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
          = (∫ x in abox N ℓ, (aP ℓ p.2 (aQ ℓ p.1 Φ) x) ^ 2) := by
            apply integral_congr_ae
            filter_upwards with x
            congr 1
            exact (aP_aQ_comm hℓ hne hΦc x).symm
      _ ≤ (∫ x in abox N ℓ, (aQ ℓ p.1 Φ x) ^ 2) := aP_sq_le hℓ p.2 hc
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
        ≤ ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 Φ x) ^ 2 := by
          exact Finset.sum_le_sum (fun p hp => hle p hp)
    _ = ((N : ℝ) - 1) * (∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2) := by
          have hswap : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.2 Φ x) ^ 2)
              = ∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 Φ x) ^ 2 := by
            exact pairSet_swap_sum (fun p : Fin N × Fin N => ∫ x in abox N ℓ, (aQ ℓ p.1 Φ x) ^ 2)
          rw [← hswap]
          exact sum_pairSet_second_eq N (fun i : Fin N => ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2)
    _ = ((N : ℝ) - 1) * cnPlus ℓ Φ := by simp [cnPlus]
    _ ≤ (N : ℝ) * cnPlus ℓ Φ := by
      have hc : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
      have h1 : (N : ℝ) - 1 ≤ (N : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right h1 hc

/-- peel bound for the `A`-family (`A = aP i (aP j Φ)`, kernel at `(x i, x j)`):
`∫A²·|w₁(xᵢ,xⱼ)| ≤ C₀·(ℓ³)⁻¹·∫A²`. -/
lemma peel_family_A_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    (∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      ≤ (chiSup ^ 2 * 2 * (8 * π * a v)) * (ℓ ^ 3)⁻¹ *
          (∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2) := by
  classical
  let w1 : ℝ³ → ℝ³ → ℝ := fun x y => |wPair ℓ (g0 v h) x y|
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hPic : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hPji : Continuous (aP ℓ j (aP ℓ i Φ)) := aP_continuous hℓ j hPic
  have hg0i : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hfib (x : ℝ³) : |∫ y in acube ℓ, w1 x y| ≤ C0 := by
    simpa [w1, C0] using w1abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x
  have hki : IntegrableOn (fun x : XN N => (aP ℓ j (aP ℓ i Φ) x) ^ 2 * w1 (x i) (x j))
      (abox N ℓ) volume := by
    have hs : IntegrableOn (fun x : XN N =>
        (aP ℓ j (aP ℓ i Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|) (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij hPji
    simpa [w1] using hs
  have hpeel := peel_sq_kernel_le hℓ hij.symm (k := w1) (C := C0) hfib
    (Ψ := aP ℓ i Φ) hPic hki
  -- peel conclusion: ∫ (aP j (aP i Φ))²·w1(xi,xj) ≤ C0(ℓ³)⁻¹∫(aP j(aP i Φ))²
  have hEq1 : (∫ x in abox N ℓ,
        (aP ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      = ∫ x in abox N ℓ, (aP ℓ j (aP ℓ i Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    exact aP_comm hℓ i j hΦc x
  have hEq2 : (∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2)
      = ∫ x in abox N ℓ, (aP ℓ j (aP ℓ i Φ) x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    exact aP_comm hℓ i j hΦc x
  rw [hEq1, hEq2]
  simpa [C0, w1] using hpeel

/-- peel bound for the `B`-family (`B = aP i (aQ j Φ)`, kernel at `(x i, x j)`):
`∫B²·|w₁(xᵢ,xⱼ)| ≤ C₀·(ℓ³)⁻¹·∫B²`. -/
lemma peel_family_B_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      ≤ (chiSup ^ 2 * 2 * (8 * π * a v)) * (ℓ ^ 3)⁻¹ *
          (∫ x in abox N ℓ, (aP ℓ i (aQ ℓ j Φ) x) ^ 2) := by
  classical
  let w1 : ℝ³ → ℝ³ → ℝ := fun x y => |wPair ℓ (g0 v h) x y|
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hQjc : Continuous (aQ ℓ j Φ) := aQ_continuous hℓ j hΦc
  have hBc : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i hQjc
  have hg0i : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hfib (x : ℝ³) : |∫ y in acube ℓ, w1 x y| ≤ C0 := by
    simpa [w1, C0] using w1abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x
  have hki : IntegrableOn (fun x : XN N => (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * w1 (x j) (x i))
      (abox N ℓ) volume := by
    have hs : IntegrableOn (fun x : XN N =>
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x j) (x i)|) (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij.symm (S := fun x : XN N => aP ℓ i (aQ ℓ j Φ) x) hBc
    simpa [w1] using hs
  have hpeel := peel_sq_kernel_le hℓ hij (k := w1) (C := C0) hfib
    (Ψ := aQ ℓ j Φ) hQjc hki
  -- conclusion: ∫ B²·w1(xj,xi) ≤ C0(ℓ³)⁻¹∫B² ; swap the kernel arguments
  have hswap : (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x j) (x i)|)
      = ∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    have hsw : wPair ℓ (g0 v h) (x j) (x i) = wPair ℓ (g0 v h) (x i) (x j) := by
      simpa [wPairC] using wPairC_g0_sym hvrad h ℓ (x j) (x i)
    rw [hsw]
  calc
    (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        = (∫ x in abox N ℓ,
        (aP ℓ i (aQ ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x j) (x i)|) := hswap.symm
    _ ≤ C0 * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (aP ℓ i (aQ ℓ j Φ) x) ^ 2) := by
        simpa [C0, w1] using hpeel

/-- peel bound for the `C`-family (`C = aQ i (aP j Φ)`, kernel at `(x i, x j)`):
`∫C²·|w₁(xᵢ,xⱼ)| ≤ C₀·(ℓ³)⁻¹·∫C²`. -/
lemma peel_family_C_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    (∫ x in abox N ℓ,
        (aQ ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      ≤ (chiSup ^ 2 * 2 * (8 * π * a v)) * (ℓ ^ 3)⁻¹ *
          (∫ x in abox N ℓ, (aQ ℓ i (aP ℓ j Φ) x) ^ 2) := by
  classical
  let w1 : ℝ³ → ℝ³ → ℝ := fun x y => |wPair ℓ (g0 v h) x y|
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hQic : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hPjQ : Continuous (aP ℓ j (aQ ℓ i Φ)) := aP_continuous hℓ j hQic
  have hg0i : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have hfib (x : ℝ³) : |∫ y in acube ℓ, w1 x y| ≤ C0 := by
    simpa [w1, C0] using w1abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x
  have hki : IntegrableOn (fun x : XN N => (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * w1 (x i) (x j))
      (abox N ℓ) volume := by
    have hs : IntegrableOn (fun x : XN N =>
        (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|) (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij hPjQ
    simpa [w1] using hs
  have hpeel := peel_sq_kernel_le hℓ hij.symm (k := w1) (C := C0) hfib
    (Ψ := aQ ℓ i Φ) hQic hki
  -- conclusion: ∫ (aP j(aQ iΦ))²·w1(xi,xj) ≤ C0(ℓ³)⁻¹∫(aP j(aQ iΦ))²; rewrite to C
  have hEq1 : (∫ x in abox N ℓ,
        (aQ ℓ i (aP ℓ j Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
      = ∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    exact (aP_aQ_comm hℓ hij.symm hΦc x).symm
  have hEq2 : (∫ x in abox N ℓ, (aQ ℓ i (aP ℓ j Φ) x) ^ 2)
      = ∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    exact (aP_aQ_comm hℓ hij.symm hΦc x).symm
  rw [hEq1, hEq2]
  simpa [C0, w1] using hpeel

/-- The single pair `M²`-bound (see header): the pair summand is bounded by
`6·C₀·(ℓ³)⁻¹` times the sum of the three family masses. -/
lemma m2_pair_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    (∫ x in abox N ℓ,
        (1 - Classical.choose h (x i - x j)) ^ 2 *
        (aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x) ^ 2 *
        wPairC ℓ v (x i) (x j))
      ≤ 6 * (chiSup ^ 2 * 2 * (8 * π * a v)) * (ℓ ^ 3)⁻¹ *
          ((∫ x in abox N ℓ, (aP ℓ i (aP ℓ j Φ) x) ^ 2)
            + (∫ x in abox N ℓ, (aP ℓ i (aQ ℓ j Φ) x) ^ 2)
            + (∫ x in abox N ℓ, (aQ ℓ i (aP ℓ j Φ) x) ^ 2)) := by
  classical
  let w0 : ℝ³ → ℝ := Classical.choose h
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let A : XN N → ℝ := fun x => aP ℓ i (aP ℓ j Φ) x
  let B : XN N → ℝ := fun x => aP ℓ i (aQ ℓ j Φ) x
  let C : XN N → ℝ := fun x => aQ ℓ i (aP ℓ j Φ) x
  let M : XN N → ℝ := fun x => A x + B x + C x
  let w1 : ℝ³ → ℝ³ → ℝ := fun x y => |wPair ℓ (g0 v h) x y|
  let μ : Measure (XN N) := (volume : Measure (XN N)).restrict (abox N ℓ)
  -- restate the goal in terms of A/B/C/M
  change (∫ x in abox N ℓ, (1 - w0 (x i - x j)) ^ 2 * (M x) ^ 2 * wPairC ℓ v (x i) (x j))
      ≤ 6 * C0 * (ℓ ^ 3)⁻¹ *
          ((∫ x in abox N ℓ, (A x) ^ 2) + (∫ x in abox N ℓ, (B x) ^ 2)
            + (∫ x in abox N ℓ, (C x) ^ 2))
  -- the a.e. bound on |1 − w₀(xᵢ−xⱼ)|
  have hw0b : ∀ᵐ x ∂μ, |1 - w0 (x i - x j)| ≤ 2 := by
    simpa [μ, w0] using
      (w0_one_sub_abs_le_two_ae hℓ hv_nonneg hvrad hR hv_supp h hij)
  -- continuity of the word functions
  have hAc : Continuous A := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hBc : Continuous B := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hCc : Continuous C := aQ_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hMc : Continuous M := (hAc.add hBc).add hCc
  -- g₀ integrability and support
  have hg0i : Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hg0s : ∀ z : ℝ³, R ≤ ‖z‖ → g0 v h z = 0 := fun z hz => g0_zero_of_norm_ge hv_supp hz h
  -- the family functions fA, fB, fC
  let fA : XN N → ℝ := fun x => (A x) ^ 2 * w1 (x i) (x j)
  let fB : XN N → ℝ := fun x => (B x) ^ 2 * w1 (x i) (x j)
  let fC : XN N → ℝ := fun x => (C x) ^ 2 * w1 (x i) (x j)
  -- integrability of the family functions (abs-kernel products)
  have hfA_int : IntegrableOn fA (abox N ℓ) volume := by
    have hs : IntegrableOn (fun x : XN N => (A x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij hAc
    simpa [fA, w1] using hs
  have hfB_int : IntegrableOn fB (abox N ℓ) volume := by
    have hs : IntegrableOn (fun x : XN N => (B x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij hBc
    simpa [fB, w1] using hs
  have hfC_int : IntegrableOn fC (abox N ℓ) volume := by
    have hs : IntegrableOn (fun x : XN N => (C x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)|)
        (abox N ℓ) volume :=
      sq_slot_wPair_abs_integrable hℓ hg0i hg0s hRℓ hij hCc
    simpa [fC, w1] using hs
  -- integrability of F := the original integrand (needed for the monotone-integral step)
  let F : XN N → ℝ := fun x =>
    (1 - w0 (x i - x j)) ^ 2 * (M x) ^ 2 * wPairC ℓ v (x i) (x j)
  have hF_esm : AEStronglyMeasurable F μ := by
    have hw0d : AEStronglyMeasurable (fun x : XN N => w0 (x i - x j)) μ := by
      simpa [μ, w0] using w0_diff_aem hℓ hij (w0_spec h).2.lhs_integrable
    have hw1m : AEStronglyMeasurable (fun x : XN N => 1 - w0 (x i - x j)) μ := by
      exact (aestronglyMeasurable_const.sub hw0d)
    have hw1sq : AEStronglyMeasurable (fun x : XN N => (1 - w0 (x i - x j)) ^ 2) μ := by
      have hmul : AEStronglyMeasurable
          (fun x : XN N => (1 - w0 (x i - x j)) * (1 - w0 (x i - x j))) μ :=
        hw1m.mul hw1m
      refine hmul.congr ?_
      refine ae_of_all _ (fun x => ?_)
      ring
    have hM2 : AEStronglyMeasurable (fun x : XN N => (M x) ^ 2) μ := by
      have hmul : AEStronglyMeasurable (fun x : XN N => M x * M x) μ :=
        hMc.aestronglyMeasurable.mul hMc.aestronglyMeasurable
      refine hmul.congr ?_
      refine ae_of_all _ (fun x => ?_)
      ring
    have hV : AEStronglyMeasurable (fun x : XN N => wPairC ℓ v (x i) (x j)) μ := by
      simpa [μ, wPairC] using aesm_wPair_pair hℓ (v_integrable hv_memL1) i j hij
    have hprod := ((hw1sq.mul hM2).mul hV)
    exact hprod.congr (by
      refine ae_of_all _ ?_
      intro x
      dsimp [F])
  -- pointwise identity: F = (1−w₀)·M²·w₁
  have hF_eq (x : XN N) :
      F x = (1 - w0 (x i - x j)) * (M x) ^ 2 * wPair ℓ (g0 v h) (x i) (x j) := by
    dsimp [F, w0, wPairC]
    rw [w1_eq_w_mul_one_sub h ℓ (x i) (x j)]
    ring
  -- |F| = |1−w₀|·M²·|w₁|
  have hF_abs (x : XN N) :
      |F x| = |1 - w0 (x i - x j)| * (M x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
    rw [hF_eq x]
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (M x))]
  -- M² ≤ 3(A²+B²+C²)
  have hMsq (x : XN N) : (M x) ^ 2 ≤ 3 * ((A x) ^ 2 + (B x) ^ 2 + (C x) ^ 2) := by
    simpa [M] using sq_three_le (a := A x) (b := B x) (c := C x)
  -- the pointwise (a.e.) domination |F| ≤ 6(fA + fB + fC)
  have hF_dom : ∀ᵐ x ∂μ, |F x| ≤ 6 * (fA x + fB x + fC x) := by
    filter_upwards [hw0b] with x hx
    calc
      |F x| = |1 - w0 (x i - x j)| * (M x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := hF_abs x
      _ ≤ 2 * (M x) ^ 2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
        have hh : |1 - w0 (x i - x j)| * (M x) ^ 2 ≤ 2 * (M x) ^ 2 :=
          mul_le_mul_of_nonneg_right hx (sq_nonneg (M x))
        exact mul_le_mul_of_nonneg_right hh (abs_nonneg (wPair ℓ (g0 v h) (x i) (x j)))
      _ ≤ 6 * ((A x) ^ 2 + (B x) ^ 2 + (C x) ^ 2) * |wPair ℓ (g0 v h) (x i) (x j)| := by
        have h1 : 2 * (M x) ^ 2 ≤ 6 * ((A x) ^ 2 + (B x) ^ 2 + (C x) ^ 2) := by
          have h2 : (M x) ^ 2 ≤ 3 * ((A x) ^ 2 + (B x) ^ 2 + (C x) ^ 2) := hMsq x
          nlinarith
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg (wPair ℓ (g0 v h) (x i) (x j)))
      _ = 6 * (fA x + fB x + fC x) := by
        dsimp [fA, fB, fC, w1]
        ring
  have hfAB_int : IntegrableOn (fun x : XN N => fA x + fB x) (abox N ℓ) volume := by
    change Integrable (fA + fB) (volume.restrict (abox N ℓ))
    exact hfA_int.integrable.add hfB_int.integrable
  -- integrability of the dominating function and of F
  have hT_int : Integrable (fun x : XN N => 6 * (fA x + fB x + fC x)) μ := by
    have hsum : Integrable (fun x : XN N => fA x + fB x + fC x) μ := by
      change Integrable ((fA + fB) + fC) μ
      have hA : Integrable fA μ := by simpa [μ, IntegrableOn] using hfA_int.integrable
      have hB : Integrable fB μ := by simpa [μ, IntegrableOn] using hfB_int.integrable
      have hC : Integrable fC μ := by simpa [μ, IntegrableOn] using hfC_int.integrable
      exact (hA.add hB).add hC
    simpa [μ] using hsum.const_mul 6
  have hF_int : Integrable F μ := by
    refine Integrable.mono' hT_int hF_esm ?_
    filter_upwards [hF_dom] with x hx
    rw [Real.norm_eq_abs]
    exact hx
  -- main chain: ∫F ≤ 6·(∫fA + ∫fB + ∫fC)
  have hchain1 : (∫ x in abox N ℓ, F x)
      ≤ 6 * (((∫ x in abox N ℓ, fA x) + (∫ x in abox N ℓ, fB x)) + (∫ x in abox N ℓ, fC x)) := by
    have hle : (∫ x in abox N ℓ, F x) ≤ ∫ x in abox N ℓ, 6 * (fA x + fB x + fC x) := by
      -- from integral_mono_ae (F ≤ |F| ≤ 6(sum) a.e.)
      have hF_le : ∀ᵐ x ∂μ, F x ≤ 6 * (fA x + fB x + fC x) := by
        filter_upwards [hF_dom] with x hx
        calc
          F x ≤ |F x| := le_abs_self (F x)
          _ ≤ 6 * (fA x + fB x + fC x) := hx
      simpa [μ] using (integral_mono_ae (μ := μ) hF_int hT_int hF_le)
    calc
      (∫ x in abox N ℓ, F x) ≤ ∫ x in abox N ℓ, 6 * (fA x + fB x + fC x) := hle
      _ = 6 * (∫ x in abox N ℓ, (fA x + fB x + fC x)) := by
        rw [← integral_const_mul (6 : ℝ) (fun x : XN N => fA x + fB x + fC x)]
      _ = 6 * (((∫ x in abox N ℓ, fA x) + (∫ x in abox N ℓ, fB x)) + (∫ x in abox N ℓ, fC x)) := by
        congr 1
        calc
          (∫ x in abox N ℓ, (fA x + fB x) + fC x)
              = (∫ x in abox N ℓ, fA x + fB x) + (∫ x in abox N ℓ, fC x) := by
                rw [← integral_add hfAB_int hfC_int]
          _ = ((∫ x in abox N ℓ, fA x) + (∫ x in abox N ℓ, fB x)) + (∫ x in abox N ℓ, fC x) := by
                rw [← integral_add hfA_int hfB_int]
  -- the family peel bounds (they match the `(x i, x j)`-orientation and masses)
  have hApeel := peel_family_A_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc hij
  have hBpeel := peel_family_B_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc hij
  have hCpeel := peel_family_C_le hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc hij
  -- bound the f-sums via the peels
  have hsum_le :
      (((∫ x in abox N ℓ, fA x) + (∫ x in abox N ℓ, fB x)) + (∫ x in abox N ℓ, fC x))
        ≤ C0 * (ℓ ^ 3)⁻¹ *
            (((∫ x in abox N ℓ, (A x) ^ 2) + (∫ x in abox N ℓ, (B x) ^ 2))
              + (∫ x in abox N ℓ, (C x) ^ 2)) := by
    have hA : (∫ x in abox N ℓ, fA x) ≤ C0 * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (A x) ^ 2) := by
      simpa [fA, w1, A, C0] using hApeel
    have hB : (∫ x in abox N ℓ, fB x) ≤ C0 * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (B x) ^ 2) := by
      simpa [fB, w1, B, C0] using hBpeel
    have hC : (∫ x in abox N ℓ, fC x) ≤ C0 * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (C x) ^ 2) := by
      simpa [fC, w1, C, C0] using hCpeel
    calc
      ((∫ x in abox N ℓ, fA x) + (∫ x in abox N ℓ, fB x)) + (∫ x in abox N ℓ, fC x)
          ≤ (C0 * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (A x) ^ 2)
              + C0 * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (B x) ^ 2))
              + C0 * (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ, (C x) ^ 2) := by
            exact (add_le_add (add_le_add hA hB) hC)
      _ = C0 * (ℓ ^ 3)⁻¹ *
            (((∫ x in abox N ℓ, (A x) ^ 2) + (∫ x in abox N ℓ, (B x) ^ 2))
              + (∫ x in abox N ℓ, (C x) ^ 2)) := by
            ring
  -- combine: multiply the f-sum bound by 6
  have h6 : 0 ≤ (6 : ℝ) := by norm_num
  have hchain2 :
      6 * (((∫ x in abox N ℓ, fA x) + (∫ x in abox N ℓ, fB x)) + (∫ x in abox N ℓ, fC x))
        ≤ 6 * (C0 * (ℓ ^ 3)⁻¹ *
            (((∫ x in abox N ℓ, (A x) ^ 2) + (∫ x in abox N ℓ, (B x) ^ 2))
              + (∫ x in abox N ℓ, (C x) ^ 2))) := by
    exact mul_le_mul_of_nonneg_left hsum_le h6
  -- final assembly
  calc
    (∫ x in abox N ℓ, (1 - w0 (x i - x j)) ^ 2 * (M x) ^ 2 * wPairC ℓ v (x i) (x j))
        ≤ 6 * (((∫ x in abox N ℓ, fA x) + (∫ x in abox N ℓ, fB x)) + (∫ x in abox N ℓ, fC x)) := hchain1
    _ ≤ 6 * (C0 * (ℓ ^ 3)⁻¹ *
            (((∫ x in abox N ℓ, (A x) ^ 2) + (∫ x in abox N ℓ, (B x) ^ 2))
              + (∫ x in abox N ℓ, (C x) ^ 2))) := hchain2
    _ = 6 * C0 * (ℓ ^ 3)⁻¹ *
          ((∫ x in abox N ℓ, (A x) ^ 2) + (∫ x in abox N ℓ, (B x) ^ 2)
            + (∫ x in abox N ℓ, (C x) ^ 2)) := by
          ring
  -- note: goal has `(A x)^2 + (B x)^2 + (C x)^2` (left-assoc) -- ring normalization above should match


/-- **`M²`-sum bound** for `potapp_q4`:
`Σ_p∫(1−w₀(x p.1−x p.2))²·M(p;x)²·w(x p.1,x p.2)
≤ 100·(chiSup²·2·8π·a v)·(ℓ³)⁻¹·N̂²·‖Φ‖²`. -/
lemma potapp_M2sq_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (1 - Classical.choose h (x p.1 - x p.2)) ^ 2 *
        (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x
          + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
      ≤ 100 * (chiSup ^ 2 * 2 * (8 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  classical
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  -- per-pair bound (instantiation of the abstract per-p lemma)
  have hper (p : Fin N × Fin N) (hp : p ∈ pairSet N) :
      (∫ x in abox N ℓ,
          (1 - Classical.choose h (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x
            + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        ≤ 6 * C0 * (ℓ ^ 3)⁻¹ *
            (((∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
              + (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
              + (∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)) := by
    have hne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    simpa [C0] using
      (m2_pair_bound hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hne)
  -- the nonnegativity facts used at the end
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    have ha : 0 ≤ 8 * π * a v := av_eightpi_nonneg hR hv_nonneg hvrad hv_supp h
    nlinarith [sq_nonneg chiSup]
  have hJ : 0 ≤ (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    exact integral_nonneg (μ := (volume : Measure (XN N)).restrict (abox N ℓ))
      (by intro x; exact sq_nonneg (Φ x))
  -- mass bounds for the three families
  have hA2 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) ≤
      (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    calc
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
          = cS2 ℓ Φ := pairSum_A_eq N ℓ
      _ ≤ (N : ℝ) * cS1 ℓ Φ := cS2_le_n_mul_cS1 hℓ hΦc
      _ ≤ (N : ℝ) * ((N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left (cS1_le_norm_sq hℓ hΦc) hN0
      _ = (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by ring
  have hB2 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) ≤
      (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    calc
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2)
          ≤ (N : ℝ) * cnPlus ℓ Φ := pairSum_B_le hℓ hΦc
      _ ≤ (N : ℝ) * ((N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by ring
  have hC2 : (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) ≤
      (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    calc
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
          ≤ (N : ℝ) * cnPlus ℓ Φ := pairSum_C_le hℓ hΦc
      _ ≤ (N : ℝ) * ((N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left (cnPlus_le_norm_sq hℓ hΦc) hN0
      _ = (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by ring
  -- the total mass is bounded by 3·N̂²·‖Φ‖²
  have hmass :
      (((∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
        + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2))
        ≤ 3 * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    nlinarith [hA2, hB2, hC2]
  -- sum the per-pair bounds
  have hsum2 :
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (1 - Classical.choose h (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x
            + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        ≤ 6 * C0 * (ℓ ^ 3)⁻¹ *
            (((∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
              + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
              + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)) := by
    calc
      (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (1 - Classical.choose h (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x
            + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
          ≤ ∑ p ∈ pairSet N, 6 * C0 * (ℓ ^ 3)⁻¹ *
              (((∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
                + (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
                + (∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)) := by
            exact Finset.sum_le_sum (fun p hp => hper p hp)
      _ = 6 * C0 * (ℓ ^ 3)⁻¹ *
            (∑ p ∈ pairSet N,
              (((∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
                + (∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
                + (∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2))) := by
            rw [← Finset.mul_sum]
      _ = 6 * C0 * (ℓ ^ 3)⁻¹ *
            (((∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
              + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
              + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)) := by
            congr 1
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- multiply the mass bound
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hpre : 0 ≤ 6 * C0 * (ℓ ^ 3)⁻¹ := by nlinarith
  have hBmass : 6 * C0 * (ℓ ^ 3)⁻¹ *
        (((∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
          + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2))
      ≤ 6 * C0 * (ℓ ^ 3)⁻¹ * (3 * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left hmass hpre
  -- the crude numeric absorption 6·3 = 18 ≤ 100
  have hX : 0 ≤ C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    nlinarith [mul_nonneg hC0 (mul_nonneg hLinv (mul_nonneg (sq_nonneg (N : ℝ)) hJ))]
  have hbig : 6 * C0 * (ℓ ^ 3)⁻¹ * (3 * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2))
      ≤ 100 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    calc
      6 * C0 * (ℓ ^ 3)⁻¹ * (3 * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2))
          = 18 * (C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2)) := by ring
      _ ≤ 100 * (C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2)) := by
            exact mul_le_mul_of_nonneg_right (by norm_num : (18 : ℝ) ≤ 100) hX
      _ = 100 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by ring
  -- assemble
  calc
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (1 - Classical.choose h (x p.1 - x p.2)) ^ 2 *
        (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x
          + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        ≤ 6 * C0 * (ℓ ^ 3)⁻¹ *
            (((∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)
              + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2))
              + (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2)) := hsum2
    _ ≤ 6 * C0 * (ℓ ^ 3)⁻¹ * (3 * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2)) := hBmass
    _ ≤ 100 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * (∫ x in abox N ℓ, (Φ x) ^ 2) := hbig
    _ = 100 * (chiSup ^ 2 * 2 * (8 * π * a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
          dsimp [C0]

end BoseGases

end Submission
