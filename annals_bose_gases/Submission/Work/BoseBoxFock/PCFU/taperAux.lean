import Mathlib
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
import Submission.Work.BoseBoxFock.PCFU.lowSlot_L2_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.taperAux` — the auxiliary slot Lemmas of the taper estimate

These are the supporting bricks of `Work.BoseBoxFock.PCFU.taperSlot_core`
(`Submission/Work/BoseBoxFock/PCFU/chAslotTaper_le.lean`): the `ℂ`-valued Fubini peel
(`abox_integral_peelC`), the `kcInsN` bookkeeping, the constancy of `Γ` in the peeled slot,
the `Γ`-`L²` contraction and its peel, and Cauchy–Schwarz in `sqrt` form.  All `sorry`-free.

The near-complete proof of `taperSlot_core` is saved at
`Submission/Work/BoseBoxFock/PCFU/CORE_PROOF_WIP3.lean.txt`.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory Filter
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- If `Ψ` is constant in the slot `i`, then so is its `j`-slot mean (`j ≠ i`). -/
lemma aP_const_of_const_in_coord {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ∀ y z, Ψ (Function.update y i z) = Ψ y) (x : Submission.BoseGases.X n) (z : E3) :
    Submission.BoseGases.aP ℓ j Ψ (Function.update x i z) = Submission.BoseGases.aP ℓ j Ψ x := by
  simp only [Submission.BoseGases.aP]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
    (fun y _ => ?_)
  rw [Function.update_comm hij z y x]
  exact hΨ (Function.update x j y) z

/-- If `Ψ` is constant in the slot `i`, then so is its `j`-slot low-momentum lift (`j ≠ i`). -/
lemma lowSlot_const_in_coord {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    {i j : Fin n} (hij : i ≠ j) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ∀ y z, Ψ (Function.update y i z) = Ψ y) (x : Submission.BoseGases.X n) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ (Function.update x i z)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x := by
  have hkey : (fun y : E3 => Ψ (Function.update (Function.update x i z) j y))
      = fun y : E3 => Ψ (Function.update x j y) := by
    funext y
    rw [Function.update_comm hij z y x]
    exact hΨ (Function.update x j y) z
  simp only [Work.BoseBoxFix.lowSlot]
  rw [Function.update_of_ne (Ne.symm hij), hkey]

/-- **The complex twin of `Submission.BoseGases.abox_integral_peel`**: the Fubini peel of one
coordinate out of the restricted box integral, for a `ℂ`-valued integrand. -/
theorem abox_integral_peelC {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1))
    (F : Submission.BoseGases.X (n + 1) → ℂ)
    (hF : IntegrableOn F (Submission.BoseGases.abox (n + 1) ℓ) volume) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x) =
      ∫ r : Submission.BoseGases.X n,
        (∫ y : E3 in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN n i (y, r)))
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)) := by
  let μ' : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)
  let ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)
  have hmp2 : MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i)) (μ'.prod ν)
      ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E3) i))
      (Submission.BoseGases.abox_peel_mp (n := n) ℓ i)
    simpa [Submission.BoseGases.kcInsN, μ', ν] using h
  have hpeel : Integrable (fun p : E3 × Submission.BoseGases.X n =>
      F (Submission.BoseGases.kcInsN n i p)) (μ'.prod ν) :=
    (hmp2.integrable_comp (hg := hF.aestronglyMeasurable)).mpr hF
  calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x)
      = ∫ x : Submission.BoseGases.X (n + 1), F x
          ∂((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
            (Submission.BoseGases.abox (n + 1) ℓ)) := rfl
    _ = ∫ p : E3 × Submission.BoseGases.X n,
          F (Submission.BoseGases.kcInsN n i p) ∂(μ'.prod ν) := by
        simpa [μ', ν] using (hmp2.integral_comp' F).symm
    _ = ∫ r : Submission.BoseGases.X n,
          (∫ y : E3, F (Submission.BoseGases.kcInsN n i (y, r)) ∂μ') ∂ν :=
        MeasureTheory.integral_prod_symm _ hpeel
    _ = ∫ r : Submission.BoseGases.X n,
          (∫ y : E3 in Submission.BoseGases.acube ℓ,
            F (Submission.BoseGases.kcInsN n i (y, r))) ∂ν := rfl

/-! ## 2. More slot bookkeeping -/

/-- `kcInsN` inserts by a slot update. -/
lemma kcInsN_eq_update {n : ℕ} (i : Fin (n + 1)) (r : Submission.BoseGases.X n) (y : E3) :
    Submission.BoseGases.kcInsN n i (y, r)
      = Function.update (Submission.BoseGases.kcInsN n i (0, r)) i y := by
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Submission.BoseGases.kc_insN_apply_same, Function.update_self]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp only [Submission.BoseGases.kc_insN_apply_succ, Function.update_apply,
      Fin.succAbove_ne i j, if_false]

/-- A `j`-slot mean is constant in the slot `i` when its argument is (the same slot). -/
lemma aP_const_in_coord' {n : ℕ} {ℓ : ℝ} (i : Fin n) (Θ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) (z : E3) :
    Submission.BoseGases.aP ℓ i Θ (Function.update x i z) = Submission.BoseGases.aP ℓ i Θ x := by
  simp only [Submission.BoseGases.aP]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
    (fun u _ => ?_)
  rw [Function.update_idem]

/-- The `Γ` of a box-restricted state is constant in the peeled slot `i`. -/
lemma lowSlot_boxRestrict_const_in_coord {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (x : Submission.BoseGases.X (n + 1)) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ))) (Function.update x i z)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
          (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x := by
  have hP : ∀ y w, Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ)
      (Function.update y i w) = Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ) y :=
    fun y w => aP_const_in_coord' i _ y w
  have hQ : ∀ y w, Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
      (Work.BoseBoxFock.boxRestrictR ℓ Φ)) (Function.update y i w)
      = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
          (Work.BoseBoxFock.boxRestrictR ℓ Φ)) y := by
    intro y w
    have h1 := hP y w
    have h2 := aP_const_of_const_in_coord (ℓ := ℓ) (i := i) (j := j) hij hP y w
    simp only [Submission.BoseGases.aQ]
    rw [h1, h2]
  exact lowSlot_const_in_coord fc κ ℓ hij hQ x z

/-! ## 3. The `L²` bound and the peel of `Γ²` -/

/-- **The slot-`j` low-momentum lift of the pair operator `Q_jP_i` is an `L²`-contraction**:
`∫_{abox}(lowSlot_j(Q_jP_iΦ))² ≤ ∫_{abox}Φ²`. -/
lemma lowSlot_aQ_aP_sq_le_cont {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (i j : Fin n) {ℓ κ : ℝ}
    (hℓ : 0 < ℓ) (hκ : 0 < κ) {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        (Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ)) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  obtain ⟨B, hB⟩ := (Work.UBBInputs9.B.abox_isCompact n ℓ).exists_bound_of_continuousOn
    hΦc.continuousOn
  have hB0 : 0 ≤ B :=
    le_trans (norm_nonneg (Φ 0)) (hB 0 (Submission.BoseGases.zero_mem_abox (N := n) hℓ.le))
  have hΦb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ B := fun x hx => by
    have h := hB x hx
    rwa [Real.norm_eq_abs] at h
  have hPb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Submission.BoseGases.aP ℓ i Φ x| ≤ B :=
    fun x hx => Submission.BoseGases.aP_abs_le hℓ i hΦc hB0 hΦb x hx
  have hPPb : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x| ≤ B :=
    fun x hx => Submission.BoseGases.aP_abs_le hℓ j (Submission.BoseGases.aP_continuous hℓ i hΦc)
      hB0 hPb x hx
  have hQb : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x| ≤ 2 * B := by
    intro x hx
    have h1 := hPb x hx
    have h2 := hPPb x hx
    have h3 : Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
        = Submission.BoseGases.aP ℓ i Φ x
          - Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x := rfl
    rw [h3]
    calc |Submission.BoseGases.aP ℓ i Φ x
            - Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x|
        ≤ |Submission.BoseGases.aP ℓ i Φ x|
          + |Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x| := abs_sub _ _
      _ ≤ B + B := add_le_add h1 h2
      _ = 2 * B := by ring
  refine le_trans (lowSlot_L2_le (j := j) (fc := fc) (κ := κ) (ℓ := ℓ)
    (C := 2 * B) hκ hℓ (by linarith) ?_ hQb) ?_
  · exact Work.BoseBoxFock.Weak.aQ_measurable j
      (Work.BoseBoxFock.Weak.aP_measurable i hΦc.measurable)
  · exact le_trans (Submission.BoseGases.integral_aQ_sq_le hℓ j
      (Submission.BoseGases.aP_continuous hℓ i hΦc)) (Submission.BoseGases.aP_sq_le hℓ i hΦc)

/-- **The peel of the `Γ`-square**: since `Γ` is constant in the peeled slot, its square integral
over the box is `ℓ³` times the integral of its values on the peeled configurations. -/
lemma lowSlot_boxRestrict_sq_peel {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) {ℓ κ D : ℝ} (hℓ : 0 < ℓ) (hD : 0 ≤ D)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΓm : Measurable (fun x => Work.BoseBoxFix.lowSlot fc κ ℓ j
      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x))
    (hΓb : ∀ x, |Work.BoseBoxFix.lowSlot fc κ ℓ j
      (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i
        (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x| ≤ D) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
          (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x) ^ 2)
      = ℓ ^ 3 * ∫ r in Submission.BoseGases.abox n ℓ,
          (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
            (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ)))
              (Submission.BoseGases.kcInsN n i (0, r))) ^ 2 := by
  have hInt : IntegrableOn (fun x : Submission.BoseGases.X (n + 1) =>
      (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
        (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))) x) ^ 2)
      (Submission.BoseGases.abox (n + 1) ℓ) := by
    refine IntegrableOn.of_bound ((Work.UBBInputs9.B.abox_isCompact (n + 1) ℓ).measure_lt_top)
      (hΓm.pow_const 2).aestronglyMeasurable (D ^ 2) ?_
    filter_upwards with x
    have h := hΓb x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [Submission.BoseGases.abox_integral_peel i _ hInt,
    ← MeasureTheory.integral_const_mul (ℓ ^ 3)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with r
  have hconst : ∀ y : E3,
      (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
        (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ)))
          (Submission.BoseGases.kcInsN n i (y, r))) ^ 2
        = (Work.BoseBoxFix.lowSlot fc κ ℓ j (Submission.BoseGases.aQ ℓ j
          (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ)))
            (Submission.BoseGases.kcInsN n i (0, r))) ^ 2 := by
    intro y
    rw [kcInsN_eq_update,
      lowSlot_boxRestrict_const_in_coord i j hij fc κ ℓ Φ
        (Submission.BoseGases.kcInsN n i (0, r)) y]
  rw [funext hconst, MeasureTheory.integral_const, MeasureTheory.Measure.real,
    MeasureTheory.Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity)]
  simp [smul_eq_mul]


/-- The `j`-slot lift of `Q_jP_iΨ` is constant in the slot `i` (`i ≠ j`), for **any** `Ψ`. -/
lemma lowSlot_aQ_aP_const_in_coord {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j)
    (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (Ψ : Submission.BoseGases.X (n + 1) → ℝ)
    (x : Submission.BoseGases.X (n + 1)) (z : E3) :
    Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ)) (Function.update x i z)
      = Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ)) x := by
  have hP : ∀ y w, Submission.BoseGases.aP ℓ i Ψ (Function.update y i w)
      = Submission.BoseGases.aP ℓ i Ψ y := fun y w => aP_const_in_coord' i Ψ y w
  have hQ : ∀ y w, Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ)
      (Function.update y i w)
      = Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Ψ) y := by
    intro y w
    have h1 := hP y w
    have h2 := aP_const_of_const_in_coord (ℓ := ℓ) (i := i) (j := j) hij hP y w
    simp only [Submission.BoseGases.aQ]
    rw [h1, h2]
  exact lowSlot_const_in_coord fc κ ℓ hij hQ x z

/-- A `kcInsN`-image of box points is a box point. -/
lemma kcInsN_mem_abox {n : ℕ} (i : Fin (n + 1)) {ℓ : ℝ} {r : Submission.BoseGases.X n}
    (hr : r ∈ Submission.BoseGases.abox n ℓ) {y : E3} (hy : y ∈ Submission.BoseGases.acube ℓ) :
    Submission.BoseGases.kcInsN n i (y, r) ∈ Submission.BoseGases.abox (n + 1) ℓ := by
  intro k
  by_cases hk : k = i
  · subst hk
    rw [Submission.BoseGases.kc_insN_apply_same]
    exact hy
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    rw [Submission.BoseGases.kc_insN_apply_succ]
    exact hr j

/-! ## 3bis. Cauchy–Schwarz in `sqrt` form -/

/-- **Cauchy–Schwarz with a square root**: `∫ ‖f‖·√g ≤ √(∫f²)·√(∫g)` for `g ≥ 0`. -/
lemma cs_sqrt_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hg0 : 0 ≤ᵐ[μ] g) :
    (∫ a, ‖f a‖ * Real.sqrt (g a) ∂μ)
      ≤ Real.sqrt (∫ a, (f a) ^ 2 ∂μ) * Real.sqrt (∫ a, g a ∂μ) := by
  have hgaesm : AEStronglyMeasurable (fun a => Real.sqrt (g a)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hg' : MemLp (fun a => Real.sqrt (g a)) 2 μ := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq_norm hgaesm]
    exact (hg.integrable one_le_two).congr (hg0.mono (fun a ha => by
      show g a = ‖Real.sqrt (g a)‖ ^ 2
      rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha]))
  have hf2 : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg2' : MemLp (fun a => Real.sqrt (g a)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hg'
  have h := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := f)
    (g := fun a => Real.sqrt (g a)) (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) hf2 hg2'
  have e1 : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ a, (f a) ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with a
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have e2 : (∫ a, ‖Real.sqrt (g a)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      = Real.sqrt (∫ a, g a ∂μ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hg0] with a ha
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha]
  rw [e1, e2] at h
  refine le_trans (le_of_eq ?_) h
  apply MeasureTheory.integral_congr_ae
  filter_upwards with a
  rw [Real.norm_eq_abs (Real.sqrt (g a)), abs_of_nonneg (Real.sqrt_nonneg (g a))]

/-- `√(ℓ³/Λ) = ℓ³√(Λ⁻¹)/√(ℓ³)` for `ℓ, Λ > 0`. -/
lemma sqrt_div_eq_aux {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ) :
    Real.sqrt (ℓ ^ 3 / Λ) = ℓ ^ 3 * Real.sqrt (Λ⁻¹) / Real.sqrt (ℓ ^ 3) := by
  have h3 : (0:ℝ) < ℓ ^ 3 := by positivity
  rw [Real.sqrt_div (le_of_lt h3), Real.sqrt_inv]
  field_simp
  rw [Real.sq_sqrt (le_of_lt h3)]

end Work.BoseBoxFock.PCFU
