import Mathlib
import Submission.Work.HP.SlabPeel
import Submission.Work.HP.SlabDefs
import Submission.Work.HP.tau_basic

/-!
# The general "peeling" bound on the volume of a slab

This file proves `Work.HP.slab_general`: if `m` linear forms `L k` on `(ι → ℝ)` have nonzero
"diagonal" coefficients `c k` and vanishing "lower" coefficients, then the set of vectors of norm
at most `A` on which all `|L k| ≤ w k` has volume at most `∏ k, 2 * w k / |c k|` times the volume
of the box of side `2A` in the remaining `card ι - m` coordinates.

The proof peels one coordinate at a time: `peel_prod` (Fubini, in `SlabPeel.lean`) supplies the
one-dimensional slice bound, and `MeasurableEquiv.piEquivPiSubtypeProd` (together with the
`Unique`-indexed variant `peel_unique`) supplies the measure-preserving splitting of the
coefficient space into one coordinate and its complement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.HP

/-! ## Peeling one coordinate of a `Unique`-indexed coordinate space -/

theorem peel_unique {κ : Type*} [Fintype κ] [Unique κ] {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (S : Set ((κ → ℝ) × X)) (hS : MeasurableSet S)
    (B : Set X) (hB : MeasurableSet B) (hSB : ∀ p ∈ S, p.2 ∈ B)
    (c : ℝ) (hc : c ≠ 0) (g : X → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hSc : ∀ p ∈ S, |c * p.1 default + g p.2| ≤ w) :
    (volume.prod μ) S ≤ ENNReal.ofReal (2 * w / |c|) * μ B := by
  rw [Measure.prod_apply_symm hS]
  have hcyl : ∀ (J : Set ℝ), (fun f : κ → ℝ => f default) ⁻¹' J =
      Set.pi Set.univ (fun i : κ => if i = default then J else Set.univ) := by
    intro J
    ext f
    constructor
    · intro h
      simp only [Set.mem_pi, Set.mem_univ, true_implies]
      intro i
      by_cases hi : i = default
      · rw [if_pos hi, hi]; exact h
      · rw [if_neg hi]; exact Set.mem_univ _
    · intro h
      simpa using h default (Set.mem_univ default)
  have hfib : ∀ x : X, volume ((fun f : κ → ℝ => (f, x)) ⁻¹' S) ≤
      ENNReal.ofReal (2 * w / |c|) * B.indicator (1 : X → ℝ≥0∞) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      have hbound : volume ((fun f : κ → ℝ => c * f default) ⁻¹'
          Set.Icc (-w - g x) (w - g x)) ≤ ENNReal.ofReal (2 * w / |c|) := by
        have hJ : (fun f : κ → ℝ => c * f default) ⁻¹' Set.Icc (-w - g x) (w - g x) =
            (fun f : κ → ℝ => f default) ⁻¹' ((fun t : ℝ => c * t) ⁻¹'
              Set.Icc (-w - g x) (w - g x)) := rfl
        rw [hJ, hcyl, volume_pi_pi]
        rw [Finset.prod_eq_single (default : κ)]
        · rw [if_pos rfl, Real.volume_preimage_mul_left hc, Real.volume_Icc,
            ← ENNReal.ofReal_mul (abs_nonneg c⁻¹)]
          exact ENNReal.ofReal_le_ofReal (le_of_eq (by rw [abs_inv, div_eq_mul_inv]; ring))
        · intro b _ hb
          exact absurd (Unique.eq_default b) hb
        · intro h
          exact absurd (Finset.mem_univ (default : κ)) h
      refine le_trans (measure_mono ?_) hbound
      intro f hf
      simp only [Set.mem_preimage, Set.mem_Icc]
      have h := hSc (f, x) hf
      rw [abs_le] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact le_of_eq (measure_mono_null (fun f hf => absurd (hSB (f, x) hf) hx) measure_empty)
  calc ∫⁻ x, volume ((fun f : κ → ℝ => (f, x)) ⁻¹' S) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (2 * w / |c|) * B.indicator (1 : X → ℝ≥0∞) x ∂μ :=
        lintegral_mono hfib
    _ = ENNReal.ofReal (2 * w / |c|) * ∫⁻ x, B.indicator (1 : X → ℝ≥0∞) x ∂μ :=
        lintegral_const_mul _ (measurable_const.indicator hB)
    _ = ENNReal.ofReal (2 * w / |c|) * μ B := by rw [lintegral_indicator_one hB]

/-! ## The linear embedding of the complement of a coordinate -/

/-- The linear embedding of the coordinates other than `e`. -/
def embLin {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι) :
    ({i : ι // i ≠ e} → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun y i := if h : i = e then 0 else y ⟨i, h⟩
  map_add' y z := by
    ext i
    by_cases h : i = e <;> simp [h]
  map_smul' r y := by
    ext i
    by_cases h : i = e <;> simp [h]

theorem embLin_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι)
    (y : {i : ι // i ≠ e} → ℝ) (i : ι) :
    embLin e y i = if h : i = e then 0 else y ⟨i, h⟩ := rfl

theorem embLin_single {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι)
    (j : {i : ι // i ≠ e}) : embLin e (Pi.single j 1) = Pi.single j.1 1 := by
  ext i
  simp only [embLin_apply, Pi.single_apply]
  by_cases h : i = e
  · have hne : ¬(i = j.1) := fun hh => j.2 (hh ▸ h)
    rw [dif_pos h, if_neg hne]
  · rw [dif_neg h]
    by_cases hsub : (⟨i, h⟩ : {i : ι // i ≠ e}) = j
    · rw [if_pos hsub, if_pos (congrArg Subtype.val hsub)]
    · rw [if_neg hsub, if_neg (fun hh => hsub (Subtype.ext hh))]

theorem embLin_add_single {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι) (a : ι → ℝ) :
    embLin e (fun j : {i : ι // i ≠ e} => a j.1) + a e • Pi.single e 1 = a := by
  ext i
  rw [Pi.add_apply, Pi.smul_apply, embLin_apply, Pi.single_apply]
  by_cases h : i = e
  · rw [dif_pos h, if_pos h]
    simp [h]
  · rw [dif_neg h, if_neg h]
    simp

theorem rNorm_subtype_le {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι) (a : ι → ℝ) :
    rNorm (fun j : {i : ι // i ≠ e} => a j.1) ≤ rNorm a := by
  rw [rNorm, rNorm]
  apply Real.sqrt_le_sqrt
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : ι => i ≠ e) (fun i => (a i) ^ 2)
  rw [← h]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-! ## The general slab bound -/

theorem slab_general_aux : ∀ (m : ℕ) (ι : Type*) [Fintype ι] [DecidableEq ι] (em : Fin m ↪ ι)
    (L : Fin m → (ι → ℝ) →ₗ[ℝ] ℝ) (c : Fin m → ℝ),
    (∀ k, L k (Pi.single (em k) 1) = c k) → (∀ k, c k ≠ 0) →
    (∀ k l : Fin m, k < l → L l (Pi.single (em k) 1) = 0) →
    m ≤ Fintype.card ι → ∀ (w : Fin m → ℝ), (∀ k, 0 ≤ w k) → ∀ (A : ℝ), 0 ≤ A →
    volume {a : ι → ℝ | rNorm a ≤ A ∧ ∀ k, |L k a| ≤ w k} ≤
      ENNReal.ofReal ((∏ k, 2 * w k / |c k|) * (2 * A) ^ (Fintype.card ι - m)) := by
  intro m
  induction m with
  | zero =>
    intro ι _ _ em L c hc hc0 hzero hm w hw A hA
    have hsub : {a : ι → ℝ | rNorm a ≤ A ∧ ∀ k : Fin 0, |L k a| ≤ w k} ⊆
        Set.univ.pi (fun _ : ι => Set.Icc (-A) A) := by
      intro a ha i _
      exact abs_le.mp (le_trans (abs_apply_le_rNorm a i) ha.1)
    calc volume {a : ι → ℝ | rNorm a ≤ A ∧ ∀ k : Fin 0, |L k a| ≤ w k}
        ≤ volume (Set.univ.pi (fun _ : ι => Set.Icc (-A) A)) := measure_mono hsub
      _ = ∏ i : ι, volume (Set.Icc (-A) A) := volume_pi_pi _
      _ = ∏ _i : ι, ENNReal.ofReal (2 * A) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            rw [Real.volume_Icc, show A - -A = 2 * A by ring]
      _ = ENNReal.ofReal (2 * A) ^ Fintype.card ι := by
            rw [Finset.prod_const, Finset.card_univ]
      _ = ENNReal.ofReal ((∏ k : Fin 0, 2 * w k / |c k|) * (2 * A) ^ (Fintype.card ι - 0)) := by
            rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * A), Nat.sub_zero]
            simp
  | succ k ih =>
    intro ι _ _ em L c hc hc0 hzero hm w hw A hA
    haveI huniq : Unique {i : ι // i = em 0} := ⟨⟨em 0, rfl⟩, fun x => Subtype.ext x.2⟩
    letI : Fintype {i : ι // i = em 0} := Subtype.fintype (fun i : ι => i = em 0)
    have hrnorm : Continuous fun a : ι → ℝ => rNorm a := by
      simp only [rNorm]
      fun_prop
    have hrnorm' : Continuous fun y : ({i : ι // i ≠ em 0} → ℝ) => rNorm y := by
      simp only [rNorm]
      fun_prop
    have hLcont : ∀ j : Fin (k + 1), Continuous fun a : ι → ℝ => L j a :=
      fun j => (L j).continuous_of_finiteDimensional
    have hSmeas : MeasurableSet {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j} := by
      rw [show {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j} =
          {a : ι → ℝ | rNorm a ≤ A} ∩ ⋂ j : Fin (k + 1), {a : ι → ℝ | |L j a| ≤ w j} by
        ext a; simp [Set.mem_iInter]]
      refine MeasurableSet.inter (measurableSet_le hrnorm.measurable measurable_const) ?_
      exact MeasurableSet.iInter fun j =>
        measurableSet_le ((hLcont j).abs).measurable measurable_const
    set φ : (ι → ℝ) ≃ᵐ ({i : ι // i = em 0} → ℝ) × ({i : ι // i ≠ em 0} → ℝ) :=
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i : ι => i = em 0) with hφdef
    have hφmp : MeasurePreserving φ volume volume :=
      volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i : ι => i = em 0)
    have hφmap : Measure.map φ.symm (volume.prod volume) = volume :=
      (MeasurePreserving.symm φ hφmp).map_eq
    have hvol : volume {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j}
        = (volume.prod volume)
            (φ '' {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j}) := by
      rw [MeasurableEquiv.image_eq_preimage_symm,
        ← Measure.map_apply (MeasurableEquiv.measurable φ.symm) hSmeas, hφmap]
    have hS'im : MeasurableSet
        (φ '' {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j}) := by
      rw [MeasurableEquiv.image_eq_preimage_symm]
      exact hSmeas.preimage (MeasurableEquiv.measurable φ.symm)
    let B : Set ({i : ι // i ≠ em 0} → ℝ) :=
      {y | rNorm y ≤ A ∧ ∀ j : Fin k, |(L j.succ) (embLin (em 0) y)| ≤ w j.succ}
    have hBmeas : MeasurableSet B := by
      have hBeq : B = {y : {i : ι // i ≠ em 0} → ℝ | rNorm y ≤ A} ∩
          ⋂ j : Fin k, {y : {i : ι // i ≠ em 0} → ℝ | |L j.succ (embLin (em 0) y)| ≤ w j.succ} := by
        show {y : {i : ι // i ≠ em 0} → ℝ | rNorm y ≤ A ∧
              ∀ j : Fin k, |L j.succ (embLin (em 0) y)| ≤ w j.succ} = _
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      rw [hBeq]
      refine MeasurableSet.inter (measurableSet_le hrnorm'.measurable measurable_const) ?_
      exact MeasurableSet.iInter fun j =>
        measurableSet_le ((((L j.succ).comp (embLin (em 0))).continuous_of_finiteDimensional).abs).measurable
          measurable_const
    have hSB : ∀ p ∈ φ '' {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j},
        p.2 ∈ B := by
      rintro ⟨f, y⟩ ⟨a, ha, haφ⟩
      have h2 : (fun j : {i : ι // i ≠ em 0} => a j.1) = y := congrArg Prod.snd haφ
      have hrec : a = embLin (em 0) y + a (em 0) • Pi.single (em 0) 1 := by
        rw [← h2]
        exact (embLin_add_single (em 0) a).symm
      show rNorm y ≤ A ∧ ∀ j : Fin k, |L j.succ (embLin (em 0) y)| ≤ w j.succ
      constructor
      · rw [← h2]
        exact le_trans (rNorm_subtype_le (em 0) a) ha.1
      · intro j
        have hLz : L j.succ (Pi.single (em 0) 1) = 0 := hzero 0 j.succ (Fin.succ_pos j)
        have hLj : L j.succ a = L j.succ (embLin (em 0) y) := by
          rw [hrec, map_add, map_smul, hLz, smul_eq_mul, mul_zero, add_zero]
        rw [← hLj]
        exact ha.2 j.succ
    have hSc : ∀ p ∈ φ '' {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j},
        |c 0 * p.1 default + (fun y : {i : ι // i ≠ em 0} → ℝ => L 0 (embLin (em 0) y)) p.2| ≤ w 0 := by
      rintro ⟨f, y⟩ ⟨a, ha, haφ⟩
      have h2 : (fun j : {i : ι // i ≠ em 0} => a j.1) = y := congrArg Prod.snd haφ
      have h1 : (fun i : {i : ι // i = em 0} => a i.1) = f := congrArg Prod.fst haφ
      have hdef : (default : {i : ι // i = em 0}) = ⟨em 0, rfl⟩ := (huniq.uniq ⟨em 0, rfl⟩).symm
      have hfd : f default = a (em 0) := by
        rw [← h1, hdef]
      have hrec : a = embLin (em 0) y + a (em 0) • Pi.single (em 0) 1 := by
        rw [← h2]
        exact (embLin_add_single (em 0) a).symm
      have hLa : L 0 a = L 0 (embLin (em 0) y) + a (em 0) * c 0 := by
        conv_lhs => rw [hrec]
        rw [map_add, map_smul, hc 0, smul_eq_mul]
      show |c 0 * f default + L 0 (embLin (em 0) y)| ≤ w 0
      rw [hfd]
      rw [show c 0 * a (em 0) + L 0 (embLin (em 0) y) = L 0 a by rw [hLa]; ring]
      exact ha.2 0
    have hpeel := peel_unique (κ := {i : ι // i = em 0}) volume
      (φ '' {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j}) hS'im B hBmeas hSB
      (c 0) (hc0 0) (fun y : {i : ι // i ≠ em 0} → ℝ => L 0 (embLin (em 0) y)) (w 0) (hw 0) hSc
    have hem'inj : Function.Injective
        (fun j : Fin k => (⟨em j.succ, by intro h; exact Fin.succ_ne_zero j (em.injective h)⟩ :
          {i : ι // i ≠ em 0})) := by
      intro a b hab
      have h : em a.succ = em b.succ := congrArg Subtype.val hab
      exact Fin.succ_injective k (em.injective h)
    let em' : Fin k ↪ {i : ι // i ≠ em 0} :=
      ⟨fun j => ⟨em j.succ, by intro h; exact Fin.succ_ne_zero j (em.injective h)⟩, hem'inj⟩
    let Lb : Fin k → ({i : ι // i ≠ em 0} → ℝ) →ₗ[ℝ] ℝ :=
      fun j => (L j.succ).comp (embLin (em 0))
    let c' : Fin k → ℝ := fun j => c j.succ
    let w' : Fin k → ℝ := fun j => w j.succ
    have hc' : ∀ j, Lb j (Pi.single (em' j) 1) = c' j := by
      intro j
      show L j.succ (embLin (em 0) (Pi.single (em' j) 1)) = c j.succ
      rw [embLin_single]
      exact hc j.succ
    have hc0' : ∀ j, c' j ≠ 0 := fun j => hc0 j.succ
    have hzero' : ∀ i j : Fin k, i < j → Lb j (Pi.single (em' i) 1) = 0 := by
      intro i j hij
      show L j.succ (embLin (em 0) (Pi.single (em' i) 1)) = 0
      rw [embLin_single]
      have hslt : i.succ < j.succ := by
        rw [Fin.lt_def] at hij ⊢
        simp only [Fin.val_succ]
        omega
      exact hzero i.succ j.succ hslt
    have hm' : k ≤ Fintype.card {i : ι // i ≠ em 0} := by
      have h1 : Fintype.card {i : ι // i ≠ em 0}
          = Fintype.card ι - Fintype.card {i : ι // i = em 0} :=
        Fintype.card_subtype_compl (fun i : ι => i = em 0)
      have h2 : Fintype.card {i : ι // i = em 0} = 1 := Fintype.card_unique
      rw [h1, h2]
      omega
    have hBvol := ih {i : ι // i ≠ em 0} em' Lb c' hc' hc0' hzero' hm' w' (fun j => hw j.succ) A hA
    calc volume {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j}
        = (volume.prod volume)
            (φ '' {a : ι → ℝ | rNorm a ≤ A ∧ ∀ j : Fin (k + 1), |L j a| ≤ w j}) := hvol
      _ ≤ ENNReal.ofReal (2 * w 0 / |c 0|) * volume B := hpeel
      _ ≤ ENNReal.ofReal (2 * w 0 / |c 0|) *
            ENNReal.ofReal ((∏ j : Fin k, 2 * w' j / |c' j|) *
              (2 * A) ^ (Fintype.card {i : ι // i ≠ em 0} - k)) :=
          mul_le_mul_right hBvol _
      _ = ENNReal.ofReal ((∏ j : Fin (k + 1), 2 * w j / |c j|) *
            (2 * A) ^ (Fintype.card ι - (k + 1))) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (by norm_num) (hw 0)) (abs_nonneg (c 0)))]
          congr 1
          have hprod : (∏ j : Fin (k + 1), 2 * w j / |c j|) =
              (2 * w 0 / |c 0|) * ∏ j : Fin k, 2 * w' j / |c' j| := by
            rw [Fin.prod_univ_succ]
          have hcard : Fintype.card {i : ι // i ≠ em 0} - k = Fintype.card ι - (k + 1) := by
            have h1 : Fintype.card {i : ι // i ≠ em 0} = Fintype.card ι - 1 := by
              rw [Fintype.card_subtype_compl (fun i : ι => i = em 0)]
              have h2 : Fintype.card {i : ι // i = em 0} = 1 := Fintype.card_unique
              rw [h2]
            rw [h1]; omega
          rw [hprod, hcard]
          ring

theorem slab_general {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (em : Fin m ↪ ι)
    (L : Fin m → (ι → ℝ) →ₗ[ℝ] ℝ) (c : Fin m → ℝ)
    (hc : ∀ k, L k (Pi.single (em k) 1) = c k) (hc0 : ∀ k, c k ≠ 0)
    (hzero : ∀ k l : Fin m, k < l → L l (Pi.single (em k) 1) = 0)
    (hm : m ≤ Fintype.card ι) (w : Fin m → ℝ) (hw : ∀ k, 0 ≤ w k)
    (A : ℝ) (hA : 0 ≤ A) :
    volume {a : ι → ℝ | rNorm a ≤ A ∧ ∀ k, |L k a| ≤ w k} ≤
      ENNReal.ofReal ((∏ k, 2 * w k / |c k|) * (2 * A) ^ (Fintype.card ι - m)) :=
  slab_general_aux m ι em L c hc hc0 hzero hm w hw A hA

end Work.HP
