import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Periodicity and the integral over a cube

Let `f : (ι → ℝ) → ℝ` be continuous, nonnegative and `1`-periodic in every coordinate
(`Work.Diff.STE.Periodic1`).  If a measurable set `A` is contained in the box `[-N, N]^ι`, then

`∫_A f ≤ (2N+1)^(card ι) * ∫_{(0,1]^ι} f`.

The proof covers the box `[-N, N]^ι` by the `(2N+1)^(card ι)` half open unit cubes
`∏ᵢ (mᵢ − N − 1, mᵢ − N]`, `mᵢ ∈ {0, …, 2N}`, whose integrals all agree with the integral over
`(0,1]^ι` by translation invariance of Lebesgue measure together with the periodicity of `f`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.Diff.STE.B3

open Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Periodicity along integer vectors -/

omit [Fintype ι] in
/-- `1`-periodicity iterated `n` times in the coordinate `i`. -/
lemma periodic1_nat_smul {β : Type*} {f : (ι → ℝ) → β} (hf : Periodic1 f)
    (i : ι) (n : ℕ) (x : ι → ℝ) :
    f (x + (n : ℝ) • Pi.single i (1 : ℝ)) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((n + 1 : ℕ) : ℝ) • Pi.single i (1 : ℝ)
        = (n : ℝ) • Pi.single i (1 : ℝ) + Pi.single i (1 : ℝ) := by
      rw [Nat.cast_succ, add_smul, one_smul]
    rw [h1, ← add_assoc, hf i, ih]

omit [Fintype ι] in
/-- `1`-periodicity iterated an integer number of times in the coordinate `i`. -/
lemma periodic1_int_smul {β : Type*} {f : (ι → ℝ) → β} (hf : Periodic1 f)
    (i : ι) (k : ℤ) (x : ι → ℝ) :
    f (x + (k : ℝ) • Pi.single i (1 : ℝ)) = f x := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have : ((n : ℤ) : ℝ) = (n : ℝ) := by push_cast; rfl
    rw [this]
    exact periodic1_nat_smul hf i n x
  · have hneg : (0 : ℤ) ≤ -k := by omega
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hneg
    have hcast : ((-k : ℤ) : ℝ) = (n : ℝ) := by rw [hn]; push_cast; rfl
    have key := periodic1_nat_smul hf i n (x + (k : ℝ) • Pi.single i (1 : ℝ))
    have harith : (k : ℝ) • Pi.single i (1 : ℝ) + (n : ℝ) • Pi.single i (1 : ℝ) = 0 := by
      rw [← add_smul]
      have : (k : ℝ) + (n : ℝ) = 0 := by
        rw [← hcast]; simp
      rw [this, zero_smul]
    rw [add_assoc, harith, add_zero] at key
    exact key.symm

/-- A `1`-periodic function is invariant under translation by an integer vector. -/
lemma periodic1_add_iVec {β : Type*} {f : (ι → ℝ) → β} (hf : Periodic1 f)
    (x : ι → ℝ) (m : ι → ℤ) : f (x + iVec m) = f x := by
  have key : ∀ s : Finset ι, ∀ x : ι → ℝ,
      f (x + ∑ i ∈ s, (m i : ℝ) • Pi.single i (1 : ℝ)) = f x := by
    intro s
    induction s using Finset.induction with
    | empty => intro x; simp
    | insert i s hi ih =>
        intro x
        rw [Finset.sum_insert hi, ← add_assoc, ih]
        exact periodic1_int_smul hf i (m i) x
  have hsum : (∑ i ∈ Finset.univ, (m i : ℝ) • Pi.single i (1 : ℝ)) = iVec m := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hsum]
  exact key Finset.univ x

/-! ## The covering cubes -/

/-- The integer vector `(mᵢ − N − 1)ᵢ`. -/
def cellIdx (N : ℕ) (m : ι → Fin (2 * N + 1)) : ι → ℤ :=
  fun i => ((m i : ℕ) : ℤ) - (N : ℤ) - 1

/-- The translation vector `(mᵢ − N − 1)ᵢ` as a real vector. -/
def shift (N : ℕ) (m : ι → Fin (2 * N + 1)) : ι → ℝ := iVec (cellIdx N m)

/-- The half open cube `∏ᵢ (mᵢ − N − 1, mᵢ − N]` of side `1`. -/
def cell (N : ℕ) (m : ι → Fin (2 * N + 1)) : Set (ι → ℝ) :=
  Set.pi Set.univ fun i => Set.Ioc (shift N m i) (shift N m i + 1)

@[simp] lemma shift_apply (N : ℕ) (m : ι → Fin (2 * N + 1)) (i : ι) :
    shift N m i = ((m i : ℕ) : ℝ) - (N : ℝ) - 1 := by
  simp [shift, cellIdx, iVec]

lemma cell_measurable (N : ℕ) (m : ι → Fin (2 * N + 1)) : MeasurableSet (cell N m) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

lemma unitCube_measurable : MeasurableSet (unitCube : Set (ι → ℝ)) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

/-- Membership in a covering cube, translated back to the unit cube. -/
lemma add_shift_mem_cell_iff (N : ℕ) (m : ι → Fin (2 * N + 1)) (x : ι → ℝ) :
    x + shift N m ∈ cell N m ↔ x ∈ unitCube := by
  simp only [cell, unitCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc, Pi.add_apply]
  constructor
  · intro h i
    have := h i
    rw [shift_apply] at this
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    rw [shift_apply]
    constructor <;> linarith [this.1, this.2]

/-- The box `[-N, N]^ι` is covered by the `(2N+1)^(card ι)` cubes `cell N m`. -/
lemma box_subset_iUnion_cell (N : ℕ) :
    Set.pi Set.univ (fun _ : ι => Set.Icc (-(N : ℝ)) (N : ℝ))
      ⊆ ⋃ m : ι → Fin (2 * N + 1), cell N m := by
  intro x hx
  rw [Set.mem_iUnion]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hx
  refine ⟨fun i => ⟨Nat.ceil (x i + N), ?_⟩, ?_⟩
  · have h2N : x i + (N : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      push_cast
      linarith [hx i]
    have hc : Nat.ceil (x i + N) ≤ 2 * N := Nat.ceil_le.mpr h2N
    omega
  · rw [cell, Set.mem_pi]
    intro i _
    rw [shift_apply, Set.mem_Ioc]
    have hle : x i + (N : ℝ) ≤ (Nat.ceil (x i + N) : ℝ) := Nat.le_ceil _
    have h0 : (0 : ℝ) ≤ x i + N := by linarith [hx i]
    have hlt : (Nat.ceil (x i + N) : ℝ) < x i + N + 1 := Nat.ceil_lt_add_one h0
    constructor <;> linarith

/-! ## The integral over a translated cube -/

/-- The integral of `F` over a covering cube equals the integral over the unit cube of the shifted
function.  (`Measure` is translation invariant.) -/
lemma lintegral_cell_eq_shift (N : ℕ) (m : ι → Fin (2 * N + 1)) (F : (ι → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ x in cell N m, F x = ∫⁻ x in unitCube, F (x + shift N m) := by
  classical
  have hcell := cell_measurable N m
  have hu := unitCube_measurable (ι := ι)
  calc ∫⁻ x in cell N m, F x
      = ∫⁻ x, (cell N m).indicator F x := (lintegral_indicator hcell F).symm
    _ = ∫⁻ x, (cell N m).indicator F (x + shift N m) := by
        rw [← (measurePreserving_add_right volume (shift N m)).lintegral_comp (hF.indicator hcell)]
    _ = ∫⁻ x, unitCube.indicator (fun z => F (z + shift N m)) x := by
        apply lintegral_congr; intro x
        rw [Set.indicator_apply, Set.indicator_apply]
        by_cases hx : x ∈ unitCube
        · have hmem : x + shift N m ∈ cell N m := (add_shift_mem_cell_iff N m x).mpr hx
          simp [hx, hmem]
        · have hmem : x + shift N m ∉ cell N m :=
            fun h => hx ((add_shift_mem_cell_iff N m x).mp h)
          simp [hx, hmem]
    _ = ∫⁻ x in unitCube, F (x + shift N m) := lintegral_indicator hu _

/-! ## The main inequality -/

theorem periodicIntegralLeCube {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hfnn : ∀ x, 0 ≤ f x) (hfcont : Continuous f)
    (hfper : Work.Diff.STE.Periodic1 f)
    (A : Set (ι → ℝ)) (hAmeas : MeasurableSet A) (N : ℕ)
    (hA : ∀ x ∈ A, ∀ i : ι, |x i| ≤ (N : ℝ)) :
    ∫ x in A, f x ≤ (2 * (N : ℝ) + 1) ^ Fintype.card ι *
      ∫ x in Work.Diff.STE.unitCube, f x := by
  classical
  set F : (ι → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hF
  have hFmeas : Measurable F := by rw [hF]; exact hfcont.measurable.ennreal_ofReal
  -- the box containing `A`
  have hA_sub : A ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (-(N : ℝ)) (N : ℝ)) := by
    intro x hx
    rw [Set.mem_pi]
    intro i _
    rw [Set.mem_Icc, ← abs_le]
    exact hA x hx i
  -- the measure theoretic inequality
  have hle : ∫⁻ x in A, F x ≤
      (Fintype.card (ι → Fin (2 * N + 1)) : ℝ≥0∞) * ∫⁻ x in unitCube, F x := by
    calc ∫⁻ x in A, F x
        ≤ ∫⁻ x in (⋃ m : ι → Fin (2 * N + 1), cell N m), F x :=
          lintegral_mono_set (hA_sub.trans (box_subset_iUnion_cell (ι := ι) N))
      _ ≤ ∑' m : ι → Fin (2 * N + 1), ∫⁻ x in cell N m, F x :=
          lintegral_iUnion_le _ _
      _ = ∑ m : ι → Fin (2 * N + 1), ∫⁻ x in cell N m, F x := tsum_fintype _
      _ = ∑ _m : ι → Fin (2 * N + 1), ∫⁻ x in unitCube, F x := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [lintegral_cell_eq_shift N m F hFmeas]
          refine lintegral_congr fun x => ?_
          simp only [hF, shift, periodic1_add_iVec hfper x (cellIdx N m)]
      _ = (Fintype.card (ι → Fin (2 * N + 1)) : ℝ≥0∞) * ∫⁻ x in unitCube, F x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- finiteness of the integral over the unit cube
  have hI : (∫⁻ x in unitCube, F x) ≠ ⊤ := by
    have hKc : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hfcont.continuousOn
    have hunit_sub : unitCube ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
      intro x hx
      rw [unitCube] at hx
      rw [Set.mem_pi] at hx ⊢
      intro i _
      exact ⟨le_of_lt (hx i (Set.mem_univ i)).1, (hx i (Set.mem_univ i)).2⟩
    have hbd : ∀ x ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1),
        F x ≤ ENNReal.ofReal C := by
      intro x hx
      rw [hF]
      apply ENNReal.ofReal_mono
      rw [← Real.norm_of_nonneg (hfnn x)]
      exact hC x hx
    have hKmeas : MeasurableSet (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
      MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    have hfin : ∫⁻ x in unitCube, F x < ⊤ := by
      calc ∫⁻ x in unitCube, F x
          ≤ ∫⁻ x in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1), F x :=
            lintegral_mono_set hunit_sub
        _ ≤ ∫⁻ x in Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1), ENNReal.ofReal C := by
            rw [← lintegral_indicator hKmeas F,
              ← lintegral_indicator hKmeas (fun _ => ENNReal.ofReal C)]
            refine lintegral_mono fun x => ?_
            by_cases hx : x ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)
            · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
              exact hbd x hx
            · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        _ = ENNReal.ofReal C *
            volume (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) := by
            rw [lintegral_const]; simp [Measure.restrict_apply]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top
    exact hfin.ne
  -- the two conversions
  have hAconv : ∫ x in A, f x = (∫⁻ x in A, F x).toReal := by
    rw [hF]
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfnn)
      ((hfcont.aestronglyMeasurable).mono_measure Measure.restrict_le_self)
  have hcube : (∫⁻ x in unitCube, F x).toReal = ∫ x in unitCube, f x := by
    rw [hF]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hfnn)
      ((hfcont.aestronglyMeasurable).mono_measure Measure.restrict_le_self)).symm
  have hcard : (Fintype.card (ι → Fin (2 * N + 1)) : ℝ) =
      (2 * (N : ℝ) + 1) ^ Fintype.card ι := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  calc ∫ x in A, f x
      = (∫⁻ x in A, F x).toReal := hAconv
    _ ≤ ((Fintype.card (ι → Fin (2 * N + 1)) : ℝ≥0∞) * ∫⁻ x in unitCube, F x).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hI) hle
    _ = (Fintype.card (ι → Fin (2 * N + 1)) : ℝ) * (∫⁻ x in unitCube, F x).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ = (2 * (N : ℝ) + 1) ^ Fintype.card ι * ∫ x in unitCube, f x := by
        rw [hcard, hcube]

end Work.Diff.STE.B3
