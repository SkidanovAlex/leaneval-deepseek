import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.NominalPerBox
import Submission.Work.BoseB1Cube.chiFibreGood
import Submission.Work.BoseB1Cube.fibSumFibreGoodB
import Submission.Work.BoseB1Cube.fibSumIntegrableB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Classical
open Work.SmallBoxSliding
open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## placeholders for the three delegated pieces (deleted in the final file) -/

/-! ## the `m(u)`-layer thickness regime -/

theorem deltaRatio_le_eighth {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ)
    (ht : μ * A ^ 3 ≤ (1 / 8 : ℝ) ^ (969 / 148 : ℝ)) :
    μ ^ (-1 / 3 : ℝ) ≤ (1 / 8) * ((paramsAt μ A).d * sideAt μ A) := by
  have hpow : μ ^ (-1 / 3 : ℝ) = μ ^ (-(1 / 3) : ℝ) := by congr 1; norm_num
  have ht0 : (0 : ℝ) < μ * A ^ 3 := by positivity
  have hfs : Work.BoseBox.fsXp (μ * A ^ 3) (148 / 3 : ℝ) ≤ 1 / 8 := by
    have h1 : Work.BoseBox.fsXp (μ * A ^ 3) (148 / 3 : ℝ)
        = (μ * A ^ 3) ^ ((148 / 3 : ℝ) / 323) := rfl
    rw [h1]
    have h2 : ((148 / 3 : ℝ) / 323) = 148 / 969 := by norm_num
    rw [h2]
    have h3 : ((1 / 8 : ℝ) ^ (969 / 148 : ℝ)) ^ (148 / 969 : ℝ) = (1 / 8 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      norm_num
    calc (μ * A ^ 3) ^ (148 / 969 : ℝ)
        ≤ ((1 / 8 : ℝ) ^ (969 / 148 : ℝ)) ^ (148 / 969 : ℝ) :=
          Real.rpow_le_rpow ht0.le ht (by norm_num)
      _ = 1 / 8 := h3
  have hdel : (paramsAt μ A).d * sideAt μ A = A * Work.BoseBox.fsXp (μ * A ^ 3) (-157 : ℝ) :=
    Work.BoseFixB1.d_mul_sideAt_eq hA hμ
  have hmu : μ ^ (-1 / 3 : ℝ) = A * Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3) : ℝ) := by
    rw [hpow]
    exact Work.BoseFixB1.mu_inv_third_eq hA hμ
  have hmul : Work.BoseBox.fsXp (μ * A ^ 3) (-(323 / 3) : ℝ)
      = Work.BoseBox.fsXp (μ * A ^ 3) (148 / 3 : ℝ)
        * Work.BoseBox.fsXp (μ * A ^ 3) (-157 : ℝ) := by
    rw [Work.BoseBox.fsXp_mul ht0]
    norm_num
  rw [hdel, hmu, hmul]
  have hf0 : 0 ≤ Work.BoseBox.fsXp (μ * A ^ 3) (-157 : ℝ) :=
    Work.BoseBox.fsXp_nonneg ht0.le
  calc A * (Work.BoseBox.fsXp (μ * A ^ 3) (148 / 3 : ℝ)
        * Work.BoseBox.fsXp (μ * A ^ 3) (-157 : ℝ))
      = (A * Work.BoseBox.fsXp (μ * A ^ 3) (-157 : ℝ))
          * Work.BoseBox.fsXp (μ * A ^ 3) (148 / 3 : ℝ) := by ring
    _ ≤ (A * Work.BoseBox.fsXp (μ * A ^ 3) (-157 : ℝ)) * (1 / 8) :=
        mul_le_mul_of_nonneg_left hfs (by positivity)
    _ = 1 / 8 * (A * Work.BoseBox.fsXp (μ * A ^ 3) (-157 : ℝ)) := by ring

/-! ## the good set as a coordinate cube -/

theorem goodSet_eq_cube {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    goodSet ℓ d μ
      = {u : E3 | ∀ j : Fin 3, |u.ofLp j| ≤ (1 + d) / (2 * d) - μ ^ (-1 / 3 : ℝ) / (ℓ * d)} := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  ext u
  simp only [goodSet, Set.mem_setOf_eq]
  have h2 : (ℓ * d) * ((1 + d) / (2 * d) - μ ^ (-1 / 3 : ℝ) / (ℓ * d))
      = (1 / 2) * ℓ * (1 + d) - μ ^ (-1 / 3 : ℝ) := by
    have h2a : (ℓ * d) * ((1 + d) / (2 * d)) = (1 / 2) * ℓ * (1 + d) := by
      field_simp [ne_of_gt hℓ, ne_of_gt hd]
    have h2b : (ℓ * d) * (μ ^ (-1 / 3 : ℝ) / (ℓ * d)) = μ ^ (-1 / 3 : ℝ) := by
      field_simp [ne_of_gt (mul_pos hℓ hd)]
    rw [mul_sub, h2a, h2b]
  have h1 : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| = (ℓ * d) * |u.ofLp j| := by
    intro j
    rw [show ((ℓ * d) • u).ofLp j = (ℓ * d) * u.ofLp j by simp, abs_mul, abs_of_pos hc]
  constructor
  · intro hu j
    have huj := hu j
    rw [h1 j] at huj
    rw [← h2] at huj
    exact le_of_mul_le_mul_left huj hc
  · intro hu j
    have huj := hu j
    rw [h1 j, ← h2]
    exact mul_le_mul_of_nonneg_left huj hc.le

theorem interiorSet_eq_cube {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    interiorSet ℓ d μ
      = {u : E3 | ∀ j : Fin 3, |u.ofLp j| ≤ (1 + d) / (2 * d) - 2 * (μ ^ (-1 / 3 : ℝ) / (ℓ * d))} := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  ext u
  simp only [interiorSet, Set.mem_setOf_eq]
  have h2 : (ℓ * d) * ((1 + d) / (2 * d) - 2 * (μ ^ (-1 / 3 : ℝ) / (ℓ * d)))
      = (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) := by
    have h2a : (ℓ * d) * ((1 + d) / (2 * d)) = (1 / 2) * ℓ * (1 + d) := by
      field_simp [ne_of_gt hℓ, ne_of_gt hd]
    have h2b : (ℓ * d) * (2 * (μ ^ (-1 / 3 : ℝ) / (ℓ * d))) = 2 * μ ^ (-1 / 3 : ℝ) := by
      field_simp [ne_of_gt (mul_pos hℓ hd)]
    rw [mul_sub, h2a, h2b]
  have h1 : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| = (ℓ * d) * |u.ofLp j| := by
    intro j
    rw [show ((ℓ * d) • u).ofLp j = (ℓ * d) * u.ofLp j by simp, abs_mul, abs_of_pos hc]
  constructor
  · intro hu j
    have huj := hu j
    rw [h1 j] at huj
    rw [← h2] at huj
    exact le_of_mul_le_mul_left huj hc
  · intro hu j
    have huj := hu j
    rw [h1 j, ← h2]
    exact mul_le_mul_of_nonneg_left huj hc.le

/-! ## the `χ_M` fibre inequality in the interface form -/

theorem chi_fibre_goodSet {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (hδ'8 : μ ^ (-1 / 3 : ℝ) / (ℓ * d) ≤ 1 / 8)
    (z y : E3) (hz : z ∈ acube ℓ) (hy : y ∈ acube ℓ)
    (hzy : ∀ j : Fin 3, |(z - y).ofLp j| ≤ ℓ * d / 16) :
    (∫ u in (goodSet ℓ d μ)ᶜ,
        chiSmall M ((ℓ * d)⁻¹ • z - u) * chiSmall M ((ℓ * d)⁻¹ • y - u))
      ≤ 3 * (∫ u in (goodSet ℓ d μ \ interiorSet ℓ d μ),
          chiSmall M ((ℓ * d)⁻¹ • z - u) * chiSmall M ((ℓ * d)⁻¹ • y - u)) := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  obtain ⟨ν, δ', hν, hδ'⟩ : ∃ (ν δ' : ℝ), ν = (1 + d) / (2 * d)
      ∧ δ' = μ ^ (-1 / 3 : ℝ) / (ℓ * d) := ⟨_, _, rfl, rfl⟩
  have hνgt : 1 / 2 < ν := by
    rw [hν, lt_div_iff₀ (by positivity)]
    linarith
  have hδ'pos : 0 < δ' := by
    rw [hδ']
    exact div_pos (Real.rpow_pos_of_pos hμ _) hc
  have hδ'le : δ' ≤ 1 / 8 := by rw [hδ']; exact hδ'8
  have ha : ∀ j : Fin 3, |((ℓ * d)⁻¹ • z).ofLp j| ≤ ν - 1 / 2 := by
    intro j
    have h1 : |((ℓ * d)⁻¹ • z).ofLp j| = (ℓ * d)⁻¹ * |z.ofLp j| := by
      rw [show ((ℓ * d)⁻¹ • z).ofLp j = (ℓ * d)⁻¹ * z.ofLp j by simp, abs_mul,
        abs_of_pos (inv_pos.mpr hc)]
    rw [h1]
    have h2 : |z.ofLp j| ≤ ℓ / 2 := by
      have hz' := (mem_acube_iff ℓ z).mp hz j
      rw [Set.mem_Icc] at hz'
      exact abs_le.mpr ⟨by linarith [hz'.1], hz'.2⟩
    calc (ℓ * d)⁻¹ * |z.ofLp j| ≤ (ℓ * d)⁻¹ * (ℓ / 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ν - 1 / 2 := by
          rw [hν]; field_simp; ring
  have hb : ∀ j : Fin 3, |((ℓ * d)⁻¹ • y).ofLp j| ≤ ν - 1 / 2 := by
    intro j
    have h1 : |((ℓ * d)⁻¹ • y).ofLp j| = (ℓ * d)⁻¹ * |y.ofLp j| := by
      rw [show ((ℓ * d)⁻¹ • y).ofLp j = (ℓ * d)⁻¹ * y.ofLp j by simp, abs_mul,
        abs_of_pos (inv_pos.mpr hc)]
    rw [h1]
    have h2 : |y.ofLp j| ≤ ℓ / 2 := by
      have hy' := (mem_acube_iff ℓ y).mp hy j
      rw [Set.mem_Icc] at hy'
      exact abs_le.mpr ⟨by linarith [hy'.1], hy'.2⟩
    calc (ℓ * d)⁻¹ * |y.ofLp j| ≤ (ℓ * d)⁻¹ * (ℓ / 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ν - 1 / 2 := by
          rw [hν]; field_simp; ring
  have hab : ∀ j : Fin 3, |((ℓ * d)⁻¹ • z - (ℓ * d)⁻¹ • y).ofLp j| ≤ 1 / 16 := by
    intro j
    have h1 : ((ℓ * d)⁻¹ • z - (ℓ * d)⁻¹ • y).ofLp j = (ℓ * d)⁻¹ * (z - y).ofLp j := by
      rw [← smul_sub]
      simp
    rw [h1, abs_mul, abs_of_pos (inv_pos.mpr hc)]
    calc (ℓ * d)⁻¹ * |(z - y).ofLp j| ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) :=
          mul_le_mul_of_nonneg_left (hzy j) (by positivity)
      _ = 1 / 16 := by field_simp
  have hsetG : goodSet ℓ d μ = {u : E3 | ∀ j : Fin 3, |u.ofLp j| ≤ ν - δ'} := by
    rw [hν, hδ']
    exact goodSet_eq_cube hℓ hd
  have hsetI : interiorSet ℓ d μ = {u : E3 | ∀ j : Fin 3, |u.ofLp j| ≤ ν - 2 * δ'} := by
    rw [hν, hδ']
    exact interiorSet_eq_cube hℓ hd
  have hmain := chiFibreGood (M := M) hM hνgt hδ'pos hδ'le ((ℓ * d)⁻¹ • z) ((ℓ * d)⁻¹ • y)
    hab ha hb
  have hcs1 : HasCompactSupport (fun u : E3 => chiSmall M ((ℓ * d)⁻¹ • z - u)) :=
    (chiSmall_hasCompactSupport hM).comp_homeomorph (Homeomorph.subLeft ((ℓ * d)⁻¹ • z))
  have hcs2 : HasCompactSupport (fun u : E3 => chiSmall M ((ℓ * d)⁻¹ • y - u)) :=
    (chiSmall_hasCompactSupport hM).comp_homeomorph (Homeomorph.subLeft ((ℓ * d)⁻¹ • y))
  have hInt : Integrable (fun u : E3 =>
      chiSmall M ((ℓ * d)⁻¹ • z - u) * chiSmall M ((ℓ * d)⁻¹ • y - u)) := by
    have hcont : Continuous (fun u : E3 =>
        chiSmall M ((ℓ * d)⁻¹ • z - u) * chiSmall M ((ℓ * d)⁻¹ • y - u)) :=
      (((Submission.BoseGases.chiSmall_continuous hM).comp
          (continuous_const.sub continuous_id)).mul
        ((Submission.BoseGases.chiSmall_continuous hM).comp
          (continuous_const.sub continuous_id)))
    have hcs : HasCompactSupport (fun u : E3 =>
        chiSmall M ((ℓ * d)⁻¹ • z - u) * chiSmall M ((ℓ * d)⁻¹ • y - u)) :=
      hcs1.mul_right (f' := fun u : E3 => chiSmall M ((ℓ * d)⁻¹ • y - u))
    exact hcont.integrable_of_hasCompactSupport hcs
  have hadd := integral_add_compl (measurableSet_goodSet ℓ d μ) hInt
  rw [hsetG] at hadd
  rw [hsetG, hsetI]
  linarith [hmain, hadd]

/-! ## the two integral bookkeeping lemmas -/

theorem sbPot_eq_pair_sub {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {ε₀ μ : ℝ} (hAdm : Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (hR16 : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * chiR0) :
    ∀ u : E3, Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ)
      = Work.BoseFixB1.pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : X n → ℝ)
        - μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u (Φ : X n → ℝ) := by
  intro u
  have hsp := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hAdm Φ.contDiff.continuous u hR16 hRχ
  linarith [hsp]

theorem goodSet_slot_integral {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {ε₀ μ : ℝ} (hAdm : Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (hR16 : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * chiR0)
    (hIntCube : Integrable (fun u : E3 =>
      Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)))
    (hIntF : Integrable (fun u : E3 =>
      Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : X n → ℝ))) :
    (∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        sbWordSlot v h
          (if u ∈ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ then μ else 4 * μ)
          μ u (Φ : X n → ℝ))
      = (∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        - 3 * μ * (∫ u in (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
              \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ),
            Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : X n → ℝ)) := by
  classical
  have hsplit := sbPot_eq_pair_sub (v := v) h hv hv1 hvrad hR hv_supp hAdm Φ hR16 hRχ
  have hslot_mu : ∀ u : E3, sbWordSlot v h μ μ u (Φ : X n → ℝ)
      = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    intro u
    show Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
        + (Work.BoseFixB1.pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : X n → ℝ)
            - μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u (Φ : X n → ℝ))
        = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
    rw [show Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
        = Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
          + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ) from rfl, hsplit u]
  have hslot_4 : ∀ u : E3, sbWordSlot v h (4 * μ) μ u (Φ : X n → ℝ)
      = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
        - 3 * μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u (Φ : X n → ℝ) := by
    intro u
    show Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
        + (Work.BoseFixB1.pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : X n → ℝ)
            - (4 * μ) * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
                (paramsAt μ (a v)).d u (Φ : X n → ℝ))
        = Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
          - 3 * μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u (Φ : X n → ℝ)
    rw [show Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
        = Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
          + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ) from rfl, hsplit u]
    ring
  have hGmeas : MeasurableSet (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    measurableSet_goodSet _ _ _
  have hImeas : MeasurableSet (interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    measurableSet_interiorSet _ _ _
  have hdiffmeas : MeasurableSet (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
      \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) := hGmeas.diff hImeas
  have hIntInd : Integrable (fun u : E3 =>
      (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
        \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ).indicator
        (fun u => Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
          (paramsAt μ (a v)).d u (Φ : X n → ℝ)) u) :=
    hIntF.indicator hdiffmeas
  calc (∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
        sbWordSlot v h
          (if u ∈ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ then μ else 4 * μ)
          μ u (Φ : X n → ℝ))
      = ∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
          (Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
            - 3 * μ * ((goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
                \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ).indicator
                (fun u => Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u (Φ : X n → ℝ)) u)) := by
        refine setIntegral_congr_fun hGmeas ?_
        intro u hu
        simp only []
        by_cases huI : u ∈ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
        · have hnot : u ∉ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
              \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ := fun hmem => hmem.2 huI
          rw [if_pos huI, hslot_mu u, Set.indicator_of_notMem hnot]
          ring
        · have hmem : u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
              \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ := ⟨hu, huI⟩
          rw [if_neg huI, hslot_4 u, Set.indicator_of_mem hmem]
    _ = (∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          - 3 * μ * (∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
              (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
                \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ).indicator
                (fun u => Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u (Φ : X n → ℝ)) u) := by
        rw [integral_sub hIntCube.integrableOn ((hIntInd.const_mul (3 * μ)).integrableOn),
          integral_const_mul]
    _ = (∫ u in goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ,
            Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
          - 3 * μ * (∫ u in (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ
              \ interiorSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ),
            Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : X n → ℝ)) := by
        rw [setIntegral_indicator hdiffmeas, Set.inter_eq_right.mpr Set.diff_subset]

theorem goodSetCompl_cube_ge {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {ε₀ μ : ℝ} (hAdm : Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (hR16 : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * chiR0)
    (hIntCube : Integrable (fun u : E3 =>
      Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)))
    (hIntF : Integrable (fun u : E3 =>
      Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : X n → ℝ))) :
    -(μ * (∫ u in (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
        Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : X n → ℝ)))
      ≤ ∫ u in (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
          Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
  have hsplit := sbPot_eq_pair_sub (v := v) h hv hv1 hvrad hR hv_supp hAdm Φ hR16 hRχ
  have hpt : ∀ u ∈ (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
      -(μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
          (Φ : X n → ℝ))
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    intro u hu
    have hK : 0 ≤ Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ) :=
      Work.BoseFixB1C.sbKinCube_nonneg hAdm u (Φ : X n → ℝ)
    have hP : 0 ≤ Work.BoseFixB1.pairSum v (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u (Φ : X n → ℝ) :=
      Work.BoseFixB1.pairSum_nonneg hv u (Φ : X n → ℝ)
    have hsw : Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
        = Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
          + Work.BoseFixB1.pairSum v (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              (Φ : X n → ℝ)
          - μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u (Φ : X n → ℝ) := by
      rw [show Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
          = Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
            + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ) from rfl, hsplit u]
      ring
    rw [hsw]
    linarith [hK, hP]
  have hGmeas : MeasurableSet (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ) :=
    measurableSet_goodSet _ _ _
  have hIntF' : IntegrableOn (fun u : E3 =>
      -(μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
        (Φ : X n → ℝ))) ((goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ) :=
    (hIntF.const_mul μ).neg.integrableOn
  have hIntC' : IntegrableOn (fun u : E3 =>
      Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
      ((goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ) := hIntCube.integrableOn
  calc -(μ * (∫ u in (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
          Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
            (Φ : X n → ℝ)))
      = ∫ u in (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
          -(μ * Work.BoseFixB1.fibSum h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u (Φ : X n → ℝ)) := by
        rw [← integral_const_mul, ← integral_neg]
    _ ≤ ∫ u in (goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)ᶜ,
          Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
        exact setIntegral_mono_on hIntF' hIntC' hGmeas.compl (fun u hu => hpt u hu)

/-! ## the target

**FS `eq:appsliding` (`FSsrc/final_v2.tex:3639`) at the matched cube cutoff.**  The *global* matched
word dominates the localised word integrated over FS's **good set only**, with the
chemical-potential slot `m(u)μ` on the boundary layer (`m(u) = 4` on `goodSet ∖ interiorSet`) and
`μ` on `interiorSet`.

The proof (see `FINDING_slidingGoodCube.md`) is: the proved `ℝ³`-level localisation
`Work.BoseFixB1C.SlidingBCube_holds` at the slot `μ` and constant `C = 1`, plus FS's *restriction
step* — for `x, y ∈ Λ` the total `u`-integral of the two-point fibre `χ_{B(u)}(x)χ_{B(u)}(y)` is
dominated by three times its integral over the layer (`Work.BoseB1Cube.chiFibreGood`, the pure bump
lemma, lifted to `fibSum` by `Work.BoseB1Cube.fibSumFibreGoodB`), plus the pointwise slot algebra
`sbPot = pairSum − μ fibSum`:

    ∫_{goodSet} sbWordSlot(m(u)μ) = ∫_{goodSet} sbWordCube − 3μ∫_{layer} fibSum
        ≤ ∫_{ℝ³} sbWordCube      ⟸   ∫_{goodSetᶜ} fibSum ≤ 3∫_{layer} fibSum ,

the reduction using `sbKinCube ≥ 0`, `pairSum ≥ 0` (`cube ≥ −μ fibSum`) and
`fibSum ≥ 0`.  The outer band `cube ∖ goodSet` is *never* integrated over: no count window and no
band estimate enter (this is the point of the `goodSet` domain). -/

theorem slidingGoodCube {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseB1Cube.SlidingGoodCube v h := by
  classical
  obtain ⟨εK, hεK, hK⟩ := Work.BoseFixB1B.kineticHalfCube_of_oneBody (v := v) h
    (Work.BoseFixB1B.oneBodyKineticHalfCube_of_mainWord (v := v) h
      (Work.BoseFixB1C.kineticHalfCube_le_mainWord (v := v) h))
    (Work.BoseFixB1B.sbKinCube_marginal_integrable (v := v) h hv hv1 hvrad hR hv_supp hav)
  obtain ⟨εP, hεP, hP⟩ := Work.BoseFixB1.potentialHalf_holds (v := v) h hv1 hvrad hR hv_supp hav
  obtain ⟨εreg, hεreg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  set εδ : ℝ := (1 / 8 : ℝ) ^ (969 / 148 : ℝ) with hεδdef
  have hεδ : 0 < εδ := by rw [hεδdef]; positivity
  refine ⟨min (min (min εK εP) εreg) (min εδ 1), 1, le_refl 1,
    lt_min (lt_min (lt_min hεK hεP) hεreg) (lt_min hεδ one_pos), ?_⟩
  intro μ hAdm n Φ
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hdil : μ * (_root_.BoseGases.a v) ^ 3
      ≤ min (min (min εK εP) εreg) (min εδ 1) := Work.BoseFixB1.adm_dilute hAdm
  have hE1 : min (min (min εK εP) εreg) (min εδ 1) ≤ min (min εK εP) εreg := min_le_left _ _
  have hE2 : min (min εK εP) εreg ≤ min εK εP := min_le_left _ _
  have hE3 : min εK εP ≤ εK := min_le_left _ _
  have hE4 : min εK εP ≤ εP := min_le_right _ _
  have hE5 : min (min εK εP) εreg ≤ εreg := min_le_right _ _
  have hE6 : min (min (min εK εP) εreg) (min εδ 1) ≤ min εδ 1 := min_le_right _ _
  have hE7 : min εδ 1 ≤ εδ := min_le_left _ _
  have hE8 : min εδ 1 ≤ 1 := min_le_right _ _
  have hAdmK : Work.BoseBoxFix.Adm v εK μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (le_trans hE1 hE2) hE3)
  have hAdmP : Work.BoseBoxFix.Adm v εP μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (le_trans hE1 hE2) hE4)
  have hdilreg : μ * (_root_.BoseGases.a v) ^ 3 ≤ εreg := le_trans hdil (le_trans hE1 hE5)
  have hdilδ : μ * (_root_.BoseGases.a v) ^ 3 ≤ εδ := le_trans hdil (le_trans hE6 hE7)
  have hdil1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans hdil (le_trans hE6 hE8)
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hdilreg
  have hℓ : 0 < sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  obtain ⟨hIntK, hKIneq⟩ := hK μ hAdmK n Φ
  obtain ⟨hIntP, hPIneq⟩ := hP μ hAdmP n Φ
  have hIntCube : Integrable (fun u : E3 =>
      Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)) := by
    rw [show (fun u : E3 => Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        = (fun u : E3 => Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
            + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ)) from rfl]
    exact hIntK.add hIntP
  have hIntF : Integrable (fun u : E3 =>
      Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
        (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
        (Φ : X n → ℝ)) :=
    fibSumIntegrableB (v := v) (Φ := (Φ : X n → ℝ)) h hv hvrad hR hv_supp hM1 hℓ hd hR16 hRχ
      Φ.contDiff
  -- the E3-level localisation
  have hcube_split : (∫ u : E3, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
      = (∫ u : E3, Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ))
        + ∫ u : E3, Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ) := by
    rw [show (fun u : E3 => Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        = (fun u : E3 => Work.BoseFixB1B.sbKinCube v μ u (Φ : X n → ℝ)
            + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ)) from rfl]
    exact integral_add hIntK hIntP
  have hwordEq : Work.BoseBoxFix.wordB v h μ n (Φ : X n → ℝ)
      = Work.BoseKinLoc.kinFormB n (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d (paramsAt μ (_root_.BoseGases.a v)).s
          (paramsAt μ (_root_.BoseGases.a v)).eT (paramsAt μ (_root_.BoseGases.a v)).b
          (Φ : X n → ℝ)
        + ∫ x in abox n (sideAt μ (_root_.BoseGases.a v)),
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (g0 v h)
              (sideAt μ (_root_.BoseGases.a v)) μ 0 x := rfl
  have hE3 : (paramsAt μ (_root_.BoseGases.a v)).b
        / (2 * sideAt μ (_root_.BoseGases.a v) ^ 2)
        * Submission.BoseGases.cnPlus (sideAt μ (_root_.BoseGases.a v)) (Φ : X n → ℝ)
        + (∫ u : E3, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
      ≤ Work.BoseBoxFix.wordB v h μ n (Φ : X n → ℝ) := by
    rw [hwordEq, hcube_split]
    linarith [hKIneq, hPIneq]
  -- the fibre inequality
  have hδ'8 : μ ^ (-1 / 3 : ℝ) / (sideAt μ (_root_.BoseGases.a v)
      * (paramsAt μ (_root_.BoseGases.a v)).d) ≤ 1 / 8 := by
    have h := deltaRatio_le_eighth (A := _root_.BoseGases.a v) (μ := μ) hav hμ (by
      rw [hεδdef] at hdilδ
      exact hdilδ)
    have hc : 0 < sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d :=
      mul_pos hℓ hd
    rw [div_le_iff₀ hc]
    calc μ ^ (-1 / 3 : ℝ)
        ≤ (1 / 8) * ((paramsAt μ (_root_.BoseGases.a v)).d
            * sideAt μ (_root_.BoseGases.a v)) := h
      _ = 1 / 8 * (sideAt μ (_root_.BoseGases.a v)
            * (paramsAt μ (_root_.BoseGases.a v)).d) := by ring
  have hF1 : ∀ z y : E3, z ∈ acube (sideAt μ (_root_.BoseGases.a v)) →
      y ∈ acube (sideAt μ (_root_.BoseGases.a v)) →
      (∀ j : Fin 3, |(z - y).ofLp j|
        ≤ sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d / 16) →
      (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
          chiSmall (paramsAt μ (_root_.BoseGases.a v)).M
              ((sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ • z - u)
            * chiSmall (paramsAt μ (_root_.BoseGases.a v)).M
              ((sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ • y - u))
        ≤ 3 * (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ
              \ interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ),
            chiSmall (paramsAt μ (_root_.BoseGases.a v)).M
                ((sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ • z - u)
              * chiSmall (paramsAt μ (_root_.BoseGases.a v)).M
                ((sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ • y - u)) :=
    fun z y hz hy hzy => chi_fibre_goodSet (M := (paramsAt μ (_root_.BoseGases.a v)).M) hM1
      hℓ hd hμ hδ'8 z y hz hy hzy
  have hfib : (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
        Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
          (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u (Φ : X n → ℝ))
      ≤ 3 * (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ
            \ interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ),
          Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : X n → ℝ)) :=
    fibSumFibreGoodB (v := v) h hv hvrad hR hv_supp hM1 hℓ hd hR16 hRχ hμ hδ'8 hF1
      (Φ : X n → ℝ) Φ.contDiff
  have hslot := goodSet_slot_integral (v := v) h hv hv1 hvrad hR hv_supp hAdm Φ hR16 hRχ
    hIntCube hIntF
  have hcompl := goodSetCompl_cube_ge (v := v) h hv hv1 hvrad hR hv_supp hAdm Φ hR16 hRχ
    hIntCube hIntF
  have hGmeas : MeasurableSet (goodSet (sideAt μ (_root_.BoseGases.a v))
      (paramsAt μ (_root_.BoseGases.a v)).d μ) := measurableSet_goodSet _ _ _
  have hadd := integral_add_compl hGmeas hIntCube
  have hkey : (0 : ℝ)
      ≤ (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
          Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ))
        + 3 * μ * (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ
            \ interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ),
          Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : X n → ℝ)) := by
    have h1 : μ * (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
          Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : X n → ℝ))
        ≤ 3 * μ * (∫ u in (goodSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ
            \ interiorSet (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ),
          Work.BoseFixB1.fibSum h (paramsAt μ (_root_.BoseGases.a v)).M
            (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d u
            (Φ : X n → ℝ)) := by
      nlinarith [hfib, hμ]
    linarith [hcompl, h1]
  have hgoal : (∫ u in goodSet (sideAt μ (_root_.BoseGases.a v))
        (paramsAt μ (_root_.BoseGases.a v)).d μ,
        sbWordSlot v h
          (if u ∈ interiorSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ then μ else 4 * μ)
          μ u (Φ : X n → ℝ))
      ≤ ∫ u : E3, Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
    rw [hslot, ← hadd]
    linarith [hkey]
  linarith [hE3, hgoal]

end Work.BoseB1Cube
