import Mathlib
import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.minimax

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open LeanEval.Geometry.SphereTheorem Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length Submission.InjRadius

/-! ### Auxiliary lemmas: `Int.fract` versus the distance to `ℤ`, and the two half-periods -/

/-- The distance from `s` to the integers is `min (Int.fract s) (1 - Int.fract s)`. -/
theorem infDist_int_eq_min_fract (s : ℝ) :
    Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) = min (Int.fract s) (1 - Int.fract s) := by
  refine le_antisymm ?_ ?_
  · rw [le_min_iff]
    refine ⟨?_, ?_⟩
    · have hmem : (⌊s⌋ : ℝ) ∈ Set.range ((↑) : ℤ → ℝ) := ⟨⌊s⌋, rfl⟩
      calc Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) ≤ dist s (⌊s⌋ : ℝ) :=
            Metric.infDist_le_dist_of_mem hmem
        _ = Int.fract s := by
            rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le s))]
            linarith [Int.fract_add_floor s]
    · have hmem : ((⌊s⌋ : ℝ) + 1) ∈ Set.range ((↑) : ℤ → ℝ) := ⟨⌊s⌋ + 1, by push_cast; ring⟩
      calc Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) ≤ dist s ((⌊s⌋ : ℝ) + 1) :=
            Metric.infDist_le_dist_of_mem hmem
        _ = 1 - Int.fract s := by
            rw [Real.dist_eq,
              abs_of_nonpos (by linarith [Int.fract_add_floor s, Int.fract_lt_one s])]
            linarith [Int.fract_add_floor s, Int.fract_lt_one s]
  · rw [Metric.le_infDist (s := Set.range ((↑) : ℤ → ℝ)) (x := s) ⟨(0 : ℝ), (0 : ℤ), by norm_num⟩]
    intro y hy
    obtain ⟨m, hm⟩ := hy
    have hfr : s - Int.fract s = (⌊s⌋ : ℝ) := by linarith [Int.fract_add_floor s]
    by_cases h : ⌊s⌋ < m
    · have hcast : (⌊s⌋ : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast (show ⌊s⌋ + 1 ≤ m by omega)
      have h1 : 1 - Int.fract s ≤ dist s y := by
        rw [Real.dist_eq,
          abs_of_nonpos (by linarith [Int.lt_floor_add_one s, hcast, hm])]
        linarith [hm, hfr, hcast, Int.lt_floor_add_one s]
      exact le_trans (min_le_right _ _) h1
    · have hcast : (m : ℝ) ≤ (⌊s⌋ : ℝ) := by
        exact_mod_cast (show m ≤ ⌊s⌋ by omega)
      have h1 : Int.fract s ≤ dist s y := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [Int.floor_le s, hm, hcast])]
        linarith [hm, hfr, hcast]
      exact le_trans (min_le_left _ _) h1

theorem infDist_int_nonneg (s : ℝ) : 0 ≤ Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) :=
  Metric.infDist_nonneg

theorem infDist_int_le_half (s : ℝ) : Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) ≤ 1 / 2 := by
  rw [infDist_int_eq_min_fract]
  rcases le_total (Int.fract s) (1 / 2) with h | h
  · exact le_trans (min_le_left _ _) h
  · exact le_trans (min_le_right _ _) (by linarith)

theorem infDist_int_eq_fract_of_le_half {s : ℝ} (h : Int.fract s ≤ 1 / 2) :
    Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) = Int.fract s := by
  rw [infDist_int_eq_min_fract, min_eq_left (by linarith)]

theorem one_sub_infDist_int_eq_fract_of_half_le {s : ℝ} (h : 1 / 2 ≤ Int.fract s) :
    1 - Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) = Int.fract s := by
  rw [infDist_int_eq_min_fract, min_eq_right (by linarith)]
  ring

theorem infDist_int_add_one (s : ℝ) :
    Metric.infDist (s + 1) (Set.range ((↑) : ℤ → ℝ)) =
      Metric.infDist s (Set.range ((↑) : ℤ → ℝ)) := by
  rw [infDist_int_eq_min_fract, infDist_int_eq_min_fract, Int.fract_add_one]

theorem infDist_int_zero : Metric.infDist (0 : ℝ) (Set.range ((↑) : ℤ → ℝ)) = 0 :=
  Metric.infDist_zero_of_mem ⟨0, by norm_num⟩

theorem mem_union_Ioo_right {s : ℝ} :
    (s ∈ ⋃ n : ℤ, Ioo ((n : ℝ) + 1 / 2) ((n : ℝ) + 1)) ↔ 1 / 2 < Int.fract s := by
  rw [mem_iUnion]
  constructor
  · rintro ⟨n, hn1, hn2⟩
    have hfl : ⌊s⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨by linarith, hn2⟩
    have h2 : Int.fract s = s - (n : ℝ) := by
      have h := Int.fract_add_floor s
      rw [hfl] at h
      linarith
    linarith
  · intro hs
    refine ⟨⌊s⌋, ?_, Int.lt_floor_add_one s⟩
    have h2 : Int.fract s + (⌊s⌋ : ℝ) = s := Int.fract_add_floor s
    linarith

theorem mem_union_Ioo_left {s : ℝ} :
    (s ∈ ⋃ n : ℤ, Ioo (n : ℝ) ((n : ℝ) + 1 / 2)) ↔
      0 < Int.fract s ∧ Int.fract s < 1 / 2 := by
  rw [mem_iUnion]
  constructor
  · rintro ⟨n, hn1, hn2⟩
    have hfl : ⌊s⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨le_of_lt hn1, by linarith⟩
    have h2 : Int.fract s = s - (n : ℝ) := by
      have h := Int.fract_add_floor s
      rw [hfl] at h
      linarith
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⌊s⌋, ?_, ?_⟩
    · have h2' : Int.fract s + (⌊s⌋ : ℝ) = s := Int.fract_add_floor s
      linarith
    · have h2' : Int.fract s + (⌊s⌋ : ℝ) = s := Int.fract_add_floor s
      linarith

/-- A point outside all the open left half-periods is either an integer or lies in the closed right
half-periods. -/
theorem fract_eq_zero_or_half_of_mem {s : ℝ}
    (hB : s ∈ (⋃ n : ℤ, Ioo (n : ℝ) ((n : ℝ) + 1 / 2))ᶜ) (hA : Int.fract s ≤ 1 / 2) :
    Int.fract s = 0 ∨ Int.fract s = 1 / 2 := by
  rw [mem_compl_iff, mem_union_Ioo_left, not_and_or, not_lt, not_lt] at hB
  rcases hB with h | h
  · left
    exact le_antisymm h (Int.fract_nonneg s)
  · right
    exact le_antisymm hA h

theorem exists_based_null_homotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [SimplyConnectedSpace M]
    {p : M} {γ : ℝ → M} (hc : Continuous γ) (hper : ∀ s : ℝ, γ (s + 1) = γ s) (h0 : γ 0 = p) :
    ∃ Hm : ℝ → ℝ → M, Continuous (fun u : ℝ × ℝ => Hm u.1 u.2) ∧
      (∀ s t : ℝ, Hm (s + 1) t = Hm s t) ∧
      (∀ t : ℝ, Hm 0 t = p) ∧ (∀ s : ℝ, Hm s 0 = γ s) ∧ (∀ s : ℝ, Hm s 1 = p) := by
  -- `γ` is periodic with any integer as a period
  have hγ_per : Function.Periodic γ 1 := hper
  have hγ_one : γ 1 = p := by
    have h := hper 0
    rw [zero_add] at h
    exact h.trans h0
  have hγ_shift : ∀ (x : ℝ) (n : ℤ), γ (x + n) = γ x := by
    intro x n
    have h : Function.Periodic γ (n : ℝ) := by simpa using hγ_per.zsmul n
    exact h x
  have hγ_fract : ∀ s : ℝ, γ (Int.fract s) = γ s := by
    intro s
    have h := hγ_shift (Int.fract s) ⌊s⌋
    rw [Int.fract_add_floor] at h
    exact h.symm
  -- the closed curve as a based path, and a based null-homotopy of it
  let γ' : Path p p :=
    { toFun := fun t : unitInterval => γ (t : ℝ)
      continuous_toFun := hc.comp continuous_subtype_val
      source' := by simpa using h0
      target' := by simpa using hγ_one }
  obtain ⟨F⟩ : Path.Homotopic γ' (Path.refl p) :=
    SimplyConnectedSpace.paths_homotopic γ' (Path.refl p)
  have hF0 : ∀ x : unitInterval, F (0, x) = γ (x : ℝ) := fun x => F.map_zero_left x
  have hF1 : ∀ x : unitInterval, F (1, x) = p := fun x => F.map_one_left x
  -- `τ` clamps `ℝ` into `I`
  let τ : ℝ → unitInterval := Set.projIcc 0 1 (by norm_num)
  have hτ_cont : Continuous τ := continuous_projIcc
  have hτ_zero : τ 0 = (0 : unitInterval) := by
    apply Subtype.ext
    simp [τ]
  have hτ_one : τ 1 = (1 : unitInterval) := by
    apply Subtype.ext
    simp [τ]
  -- `w` is the distance to `ℤ`
  let w : ℝ → ℝ := fun s => Metric.infDist s (Set.range ((↑) : ℤ → ℝ))
  have hw_cont : Continuous w := Metric.continuous_infDist_pt _
  have hw_nonneg : ∀ s, 0 ≤ w s := fun s => infDist_int_nonneg s
  have hw_le_half : ∀ s, w s ≤ 1 / 2 := fun s => infDist_int_le_half s
  have hw_le_one : ∀ s, w s ≤ 1 := fun s => (hw_le_half s).trans (by norm_num)
  have hw_eq_fract : ∀ s, Int.fract s ≤ 1 / 2 → w s = Int.fract s :=
    fun s h => infDist_int_eq_fract_of_le_half h
  have hw_eq_one_sub : ∀ s, 1 / 2 ≤ Int.fract s → 1 - w s = Int.fract s :=
    fun s h => one_sub_infDist_int_eq_fract_of_half_le h
  have hw_zero : w 0 = 0 := infDist_int_zero
  have hw_add_one : ∀ s, w (s + 1) = w s := fun s => infDist_int_add_one s
  let pA : ℝ → unitInterval := fun s => ⟨w s, hw_nonneg s, hw_le_one s⟩
  let pB : ℝ → unitInterval :=
    fun s => ⟨1 - w s, by linarith [hw_le_one s], by linarith [hw_nonneg s]⟩
  have pA_apply : ∀ s, (pA s : ℝ) = w s := fun s => rfl
  have pB_apply : ∀ s, (pB s : ℝ) = 1 - w s := fun s => rfl
  have hpA_cont : Continuous pA := Continuous.subtype_mk hw_cont _
  have hpB_cont : Continuous pB := Continuous.subtype_mk (continuous_const.sub hw_cont) _
  -- the two halves of a period
  let A : Set ℝ := (⋃ n : ℤ, Ioo ((n : ℝ) + 1 / 2) ((n : ℝ) + 1))ᶜ
  let B : Set ℝ := (⋃ n : ℤ, Ioo (n : ℝ) ((n : ℝ) + 1 / 2))ᶜ
  have hA_mem : ∀ s, s ∈ A ↔ Int.fract s ≤ 1 / 2 := by
    intro s
    show s ∈ (⋃ n : ℤ, Ioo ((n : ℝ) + 1 / 2) ((n : ℝ) + 1))ᶜ ↔ Int.fract s ≤ 1 / 2
    rw [mem_compl_iff, mem_union_Ioo_right, not_lt]
  have hA_closed : IsClosed A := isClosed_compl_iff.mpr (isOpen_iUnion fun n => isOpen_Ioo)
  have hB_closed : IsClosed B := isClosed_compl_iff.mpr (isOpen_iUnion fun n => isOpen_Ioo)
  have hAB : A ∪ B = univ := by
    rw [eq_univ_iff_forall]
    intro s
    by_cases h : Int.fract s ≤ 1 / 2
    · exact Or.inl ((hA_mem s).mpr h)
    · refine Or.inr ?_
      show s ∈ (⋃ n : ℤ, Ioo (n : ℝ) ((n : ℝ) + 1 / 2))ᶜ
      rw [mem_compl_iff, mem_union_Ioo_left, not_and_or, not_lt, not_lt]
      exact Or.inr (le_of_lt (not_le.mp h))
  -- the candidate homotopy
  let Hm : ℝ → ℝ → M := fun s t =>
    if Int.fract s ≤ 1 / 2 then F (τ t, pA s) else F (τ t, pB s)
  have Hm_def : ∀ s t, Hm s t =
      if Int.fract s ≤ 1 / 2 then F (τ t, pA s) else F (τ t, pB s) := fun s t => rfl
  have hG1 : Continuous fun a : ℝ × ℝ => F (τ a.2, pA a.1) :=
    F.continuous.comp ((hτ_cont.comp continuous_snd).prodMk (hpA_cont.comp continuous_fst))
  have hG2 : Continuous fun a : ℝ × ℝ => F (τ a.2, pB a.1) :=
    F.continuous.comp ((hτ_cont.comp continuous_snd).prodMk (hpB_cont.comp continuous_fst))
  have hcontA : ContinuousOn (fun a : ℝ × ℝ => Hm a.1 a.2) (A ×ˢ (univ : Set ℝ)) := by
    refine hG1.continuousOn.congr ?_
    rintro ⟨s, t⟩ hs
    have hsA : Int.fract s ≤ 1 / 2 := (hA_mem s).mp hs.1
    dsimp only
    rw [Hm_def, if_pos hsA]
  have hcontB : ContinuousOn (fun a : ℝ × ℝ => Hm a.1 a.2) (B ×ˢ (univ : Set ℝ)) := by
    refine hG2.continuousOn.congr ?_
    rintro ⟨s, t⟩ hs
    have hsB : s ∈ (⋃ n : ℤ, Ioo (n : ℝ) ((n : ℝ) + 1 / 2))ᶜ := hs.1
    dsimp only
    rw [Hm_def]
    by_cases hle : Int.fract s ≤ 1 / 2
    · rw [if_pos hle]
      rcases fract_eq_zero_or_half_of_mem hsB hle with hz | hh
      · have hpa : pA s = (0 : unitInterval) := by
          refine Subtype.ext ?_
          simp [pA_apply, hw_eq_fract s hle, hz]
        have hpb : pB s = (1 : unitInterval) := by
          refine Subtype.ext ?_
          simp [pB_apply, hw_eq_fract s hle, hz]
        rw [hpa, hpb, F.source (τ t), F.target (τ t)]
      · have hpq : pA s = pB s := by
          refine Subtype.ext ?_
          rw [pA_apply, pB_apply, hw_eq_fract s hle, hh]
          norm_num
        rw [hpq]
    · rw [if_neg hle]
  have hAB' : (A ×ˢ (univ : Set ℝ)) ∪ (B ×ˢ (univ : Set ℝ)) = univ := by
    rw [← Set.union_prod, hAB, Set.univ_prod_univ]
  have hcont : Continuous (fun a : ℝ × ℝ => Hm a.1 a.2) :=
    continuousOn_univ.mp (hAB' ▸ ContinuousOn.union_of_isClosed hcontA hcontB
      (hA_closed.prod isClosed_univ) (hB_closed.prod isClosed_univ))
  refine ⟨Hm, hcont, ?_, ?_, ?_, ?_⟩
  · -- periodicity
    intro s t
    have hpA1 : pA (s + 1) = pA s := by
      refine Subtype.ext ?_
      simp [pA_apply, hw_add_one]
    have hpB1 : pB (s + 1) = pB s := by
      refine Subtype.ext ?_
      simp [pB_apply, hw_add_one]
    rw [Hm_def, Hm_def, Int.fract_add_one, hpA1, hpB1]
  · -- `Hm 0 t = p`
    intro t
    rw [Hm_def]
    have hcond : Int.fract (0 : ℝ) ≤ 1 / 2 := by rw [Int.fract_zero]; norm_num
    rw [if_pos hcond]
    have hpa : pA 0 = (0 : unitInterval) := by
      refine Subtype.ext ?_
      simp [pA_apply, hw_zero]
    rw [hpa]
    exact F.source (τ t)
  · -- `Hm s 0 = γ s`
    intro s
    rw [Hm_def]
    by_cases h : Int.fract s ≤ 1 / 2
    · rw [if_pos h, hτ_zero]
      have hpa : pA s = ⟨Int.fract s, Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩ := by
        refine Subtype.ext ?_
        simp [pA_apply, hw_eq_fract s h]
      rw [hpa]
      exact (hF0 _).trans (hγ_fract s)
    · rw [if_neg h, hτ_zero]
      have hpb : pB s = ⟨Int.fract s, Int.fract_nonneg s, le_of_lt (Int.fract_lt_one s)⟩ := by
        refine Subtype.ext ?_
        simp [pB_apply, hw_eq_one_sub s (le_of_lt (not_le.mp h))]
      rw [hpb]
      exact (hF0 _).trans (hγ_fract s)
  · -- `Hm s 1 = p`
    intro s
    rw [Hm_def]
    by_cases h : Int.fract s ≤ 1 / 2
    · rw [if_pos h, hτ_one]
      exact hF1 (pA s)
    · rw [if_neg h, hτ_one]
      exact hF1 (pB s)

end Work.OddBound.minimax
