import ChallengeDeps
import Submission.Work.FSGroupQWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Q1 in sharp mass form (FS eq:SmallsimpleQs Q1 part, corpus per-sector)

Sub-lemma (b) of the first count-universal per-group bound: the `q1word`
(Q1 word of the potsplit at the chosen kernels `w₁ := wPairC(g₀)`,
`w₂ := wPairC(g₂)`) bounded in the sharp `n₊`/condensate mass form with
`n₀ = cS1` appearing explicitly:

    q1word = 2·T1 − 2μ·T2 ,    T1 := Σ∫(P₁Q₂Φ)(P₁P₂Φ)·w₂ ,
                               T2 := Σ∫(Q_iΦ)(P_iΦ)·(w₁-fibre)(x_i)

    |q1word| ≤ C₂·(ℓ³)⁻¹·(N̂·n₊ + cS2) + μ·C₁·(cS1 + n₊),
    C₁ := chiSup²·2·(8π·a v),  C₂ := chiSup²·2·(16π·a v)

(pair part `2·|T1| ≤ M1+M2` via the generic AM–GM
`QCrossD.q1pair_abs_le` + the two sharp `w₂`-mass atoms; one-body part
`|2μT2| ≤ μ·C₁·(cS1+n₊)` via `OneBodyBound.onebody_cross_abs_le`).
All statements per-sector over `abox N ℓ`, chosen branch, `Continuous Φ`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `w₂`-mass constant (`g₂`-fibre over the cube, times `a`). -/
noncomputable def fsqC2 (a : ℝ) : ℝ := chiSup ^ 2 * 2 * (16 * π * a)

section ChosenBranch

/-- The `|w₂|`-weighted `(P Q)`-pair mass is `n₊`-linear:
`Σ_p∫(P_{p.1}Q_{p.2}Φ)²·|wPairC(ℓ,g₂)| ≤ C₂·(ℓ³)⁻¹·N̂·n₊`. -/
lemma pq_w2_mass_le_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
  classical
  let C2 : ℝ := fsqC2 (a v)
  have hC2nn : 0 ≤ C2 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C2, fsqC2]
    positivity
  have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) ^ 2) :=
    masssum_PQ_abs_le hℓ (le_of_lt hR) hRℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) (g2_even hvrad h)
      (C := C2) (fun x => w2abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      hΦc
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hP : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
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
    _ = (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
          simp [C2]
          ring

/-- The `|w₂|`-weighted condensate-pair mass is `cS₂`-bounded:
`Σ_p∫(P_{p.1}P_{p.2}Φ)²·|wPairC(ℓ,g₂)| ≤ C₂·(ℓ³)⁻¹·cS2 ℓ Φ`. -/
lemma pp_w2_mass_le_cS2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPairC ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
  classical
  let C2 : ℝ := fsqC2 (a v)
  have hC2nn : 0 ≤ C2 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C2, fsqC2]
    positivity
  have hmm : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * |wPair ℓ (g2 v h) (x p.1) (x p.2)|)
      ≤ C2 * (ℓ ^ 3)⁻¹ * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) :=
    masssum_PP_abs_le hℓ (le_of_lt hR) hRℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) (g2_even hvrad h)
      (C := C2) (fun x => w2abs_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ x)
      hΦc
  have hLinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
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
    _ = (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
          simp [C2]

/-- **Q1 in sharp mass form** (FS eq:SmallsimpleQs Q1 part, corpus
per-sector): with `n₀ = cS1` the condensate count of the state,

    |q1word(N, ℓ, μ, wPairC(g₀), wPairC(g₂)) Φ|
      ≤ C₂·(ℓ³)⁻¹·(N̂·n₊ + cS2) + μ·C₁·(cS1 + n₊) . -/
theorem q1_sharp_mass {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ|
      ≤ (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
        + μ * (fsqC1 (a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
  classical
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g0 v h)
  let w2 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g2 v h)
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
  let C1 : ℝ := fsqC1 (a v)
  let C2 : ℝ := fsqC2 (a v)
  have hq1eq : q1word (N := N) ℓ μ w1 w2 Φ = 2 * T1 - 2 * μ * T2 := by
    dsimp [q1word, T1, T2, w1, w2]
  have hB1 : |q1word (N := N) ℓ μ w1 w2 Φ| ≤ 2 * |T1| + |2 * μ * T2| := by
    rw [hq1eq]
    calc
      |2 * T1 - 2 * μ * T2| = |2 * T1 + (-(2 * μ * T2))| := by rw [sub_eq_add_neg]
      _ ≤ |2 * T1| + |-(2 * μ * T2)| := abs_add_le (2 * T1) (-(2 * μ * T2))
      _ = |2 * T1| + |2 * μ * T2| := by rw [abs_neg]
      _ = 2 * |T1| + |2 * μ * T2| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
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
  have hM1 : M1 ≤ C2 * (ℓ ^ 3)⁻¹ * (N : ℝ) * cnPlus ℓ Φ := by
    have hmm := pq_w2_mass_le_cnPlus hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [M1, C2, w2, wPairC] using hmm
  have hM2 : M2 ≤ C2 * (ℓ ^ 3)⁻¹ * cS2 ℓ Φ := by
    have hmm := pp_w2_mass_le_cS2 hℓ hv_nonneg hvrad hR hv_supp h hRℓ hΦc
    simpa [M2, C2, w2, wPairC] using hmm
  have hTS : T2 = S := by
    dsimp [T2, S]
    apply Finset.sum_congr rfl
    intro i hi
    apply integral_congr_ae
    filter_upwards with x
    dsimp [w1]
    simp [w1Fibre, wPairC]
    ring
  have hob : |2 * μ * T2| ≤ μ * C1 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
    have hcross := onebody_cross_abs_le (N := N) hR hv_nonneg hvrad hv_supp h hℓ hRℓ μ hμ hΦc
    have hcross' : |2 * μ * S| ≤ μ * C1 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
      simpa [C1, fsqC1] using hcross
    rw [hTS]
    exact hcross'
  have hmass : M1 + M2 ≤ C2 * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ) := by
    nlinarith [hM1, hM2]
  calc
    |q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ|
        = |q1word (N := N) ℓ μ w1 w2 Φ| := by rfl
    _ ≤ 2 * |T1| + |2 * μ * T2| := hB1
    _ ≤ (M1 + M2) + μ * C1 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
          nlinarith [hpairb, hob]
    _ ≤ C2 * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
          + μ * C1 * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
          nlinarith [hmass]
    _ = (fsqC2 (a v)) * (ℓ ^ 3)⁻¹ * (((N : ℝ) * cnPlus ℓ Φ) + cS2 ℓ Φ)
          + μ * (fsqC1 (a v)) * (cS1 ℓ Φ + cnPlus ℓ Φ) := by
          simp [C1, C2]

end ChosenBranch

end BoseGases

end Submission
