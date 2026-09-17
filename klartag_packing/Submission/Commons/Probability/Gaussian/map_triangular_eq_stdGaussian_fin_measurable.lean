import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Probability.Gaussian.stdGaussian_prod_map_proj_add
import Submission.Commons.MeasureTheory.Measure.map_fin_snoc_skew
import Submission.Commons.MeasureTheory.Measure.piFinSuccAbove_last_symm

namespace Commons.Probability.Gaussian

open _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal

set_option linter.unusedSectionVars false

section aux_sec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- For a family `P` of projections depending only on the past, the projection `P ω j` is
unchanged when the last coordinate of `ω` is modified. -/
private lemma hpast_snoc_eq {m : ℕ} {P : (Fin (m + 1) → E × E) → Fin (m + 1) → E →L[ℝ] E}
    (hpast : ∀ ω ω' j, (∀ i, i < j → ω i = ω' i) → P ω j = P ω' j)
    (ω' : Fin m → E × E) (z z' : E × E) (j : Fin (m + 1)) :
    P (@Fin.snoc m (fun _ => E × E) ω' z) j = P (@Fin.snoc m (fun _ => E × E) ω' z') j := by
  refine hpast (@Fin.snoc m (fun _ => E × E) ω' z)
    (@Fin.snoc m (fun _ => E × E) ω' z') j (fun i hi => ?_)
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · simp [Fin.snoc_castSucc]
  · exact absurd hi (not_lt.mpr (Fin.le_last _))

/-- Measurability of the map `ω ↦ fun j => P ω j (ω j).1 + (1 - P ω j) (ω j).2`. -/
private lemma measurable_triMap {m : ℕ} {P : (Fin m → E × E) → Fin m → E →L[ℝ] E}
    (hmeas : ∀ j, Measurable fun p : (Fin m → E × E) × E => P p.1 j p.2) :
    Measurable fun ω : Fin m → E × E => fun j : Fin m =>
      P ω j (ω j).1 + (ContinuousLinearMap.id ℝ E - P ω j) (ω j).2 := by
  rw [measurable_pi_iff]
  intro j
  have h1 : Measurable fun ω : Fin m → E × E => P ω j (ω j).1 :=
    (hmeas j).comp (measurable_id.prodMk ((measurable_pi_apply j).fst))
  have h2 : Measurable fun ω : Fin m → E × E => P ω j (ω j).2 :=
    (hmeas j).comp (measurable_id.prodMk ((measurable_pi_apply j).snd))
  have h3 := h1.add (((measurable_pi_apply j).snd).sub h2)
  simp only [sub_apply, ContinuousLinearMap.id_apply]
  exact h3

/-- The main induction: the triangular map built from a past-dependent family of orthogonal
projections pushes the product standard Gaussian to the product standard Gaussian. -/
private theorem aux (n : ℕ) :
    ∀ (P : (Fin n → E × E) → Fin n → E →L[ℝ] E),
      (∀ ω j, (P ω j).comp (P ω j) = P ω j) →
      (∀ ω j x y, inner ℝ (P ω j x) y = inner ℝ x (P ω j y)) →
      (∀ ω ω' j, (∀ i, i < j → ω i = ω' i) → P ω j = P ω' j) →
      (∀ j, Measurable fun p : (Fin n → E × E) × E => P p.1 j p.2) →
      (Measure.pi (fun _ : Fin n =>
          (ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E))).map
        (fun ω : Fin n → E × E => fun j : Fin n =>
          P ω j (ω j).1 + (ContinuousLinearMap.id ℝ E - P ω j) (ω j).2)
        = Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian E) := by
  induction n with
  | zero =>
    intro P hproj hsym hpast hmeas
    rw [Measure.pi_of_empty (μ := fun _ : Fin 0 => ProbabilityTheory.stdGaussian E),
        Measure.pi_of_empty (μ := fun _ : Fin 0 =>
          (ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E))]
    simp only [Measure.map_dirac]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro P hproj hsym hpast hmeas
    let μ : Measure E := ProbabilityTheory.stdGaussian E
    let ν : Measure (E × E) := μ.prod μ
    let m : Measure (Fin n → E × E) := Measure.pi (fun _ : Fin n => ν)
    let P' : (Fin n → E × E) → Fin n → E →L[ℝ] E :=
      fun ω' j => P (@Fin.snoc n (fun _ => E × E) ω' (0, 0)) j.castSucc
    let q : (Fin n → E × E) → E →L[ℝ] E :=
      fun ω' => P (@Fin.snoc n (fun _ => E × E) ω' (0, 0)) (Fin.last n)
    let T' : (Fin n → E × E) → Fin n → E :=
      fun ω' j => P' ω' j (ω' j).1 + (ContinuousLinearMap.id ℝ E - P' ω' j) (ω' j).2
    let g : (Fin n → E × E) → E × E → E :=
      fun ω' z => q ω' z.1 + (ContinuousLinearMap.id ℝ E - q ω') z.2
    let T : (Fin (n + 1) → E × E) → Fin (n + 1) → E :=
      fun ω j => P ω j (ω j).1 + (ContinuousLinearMap.id ℝ E - P ω j) (ω j).2
    change (Measure.pi (fun _ : Fin (n + 1) => ν)).map T
        = Measure.pi (fun _ : Fin (n + 1) => μ)
    have hproj' : ∀ ω' j, (P' ω' j).comp (P' ω' j) = P' ω' j := fun ω' j => hproj _ _
    have hsym' : ∀ ω' j x y, inner ℝ (P' ω' j x) y = inner ℝ x (P' ω' j y) :=
      fun ω' j x y => hsym _ _ _ _
    have hpast' : ∀ ω' ω'' j, (∀ i, i < j → ω' i = ω'' i) → P' ω' j = P' ω'' j := by
      intro ω' ω'' j h
      change P (@Fin.snoc n (fun _ => E × E) ω' (0, 0)) j.castSucc
        = P (@Fin.snoc n (fun _ => E × E) ω'' (0, 0)) j.castSucc
      refine hpast _ _ j.castSucc (fun i hi => ?_)
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact h i' (by simpa using hi)
      · exact absurd hi (not_lt.mpr (Fin.le_last _))
    have hmeas' : ∀ j, Measurable fun p : (Fin n → E × E) × E => P' p.1 j p.2 := by
      intro j
      have hsnocQ : Measurable fun p : (Fin n → E × E) × E =>
          @Fin.snoc n (fun _ => E × E) p.1 (0, 0) :=
        (Commons.MeasureTheory.Measure.measurable_fin_snoc_const (α := E × E) n).comp
          (measurable_fst.prodMk
            (measurable_const : Measurable (fun _ : (Fin n → E × E) × E => (0 : E × E))))
      exact (hmeas j.castSucc).comp (hsnocQ.prodMk measurable_snd)
    have hT' : Measurable T' := measurable_triMap hmeas'
    have hg : Measurable fun p : (Fin n → E × E) × (E × E) => g p.1 p.2 := by
      have hsnocR : Measurable fun p : (Fin n → E × E) × (E × E) =>
          @Fin.snoc n (fun _ => E × E) p.1 (0, 0) :=
        (Commons.MeasureTheory.Measure.measurable_fin_snoc_const (α := E × E) n).comp
          (measurable_fst.prodMk
            (measurable_const : Measurable (fun _ : (Fin n → E × E) × (E × E) => (0 : E × E))))
      have hq1 : Measurable fun p : (Fin n → E × E) × (E × E) => q p.1 p.2.1 :=
        (hmeas (Fin.last n)).comp (hsnocR.prodMk (measurable_fst.comp measurable_snd))
      have hq2 : Measurable fun p : (Fin n → E × E) × (E × E) => q p.1 p.2.2 :=
        (hmeas (Fin.last n)).comp (hsnocR.prodMk (measurable_snd.comp measurable_snd))
      have h3 := hq1.add ((measurable_snd.comp measurable_snd).sub hq2)
      change Measurable fun p : (Fin n → E × E) × (E × E) =>
        q p.1 p.2.1 + (ContinuousLinearMap.id ℝ E - q p.1) p.2.2
      simp only [sub_apply, ContinuousLinearMap.id_apply]
      exact h3
    have hgmap : ∀ ω' : Fin n → E × E, ν.map (g ω') = μ := by
      intro ω'
      have h1 : (q ω').comp (q ω') = q ω' := hproj _ _
      have h2 : ∀ x y : E, inner ℝ (q ω' x) y = inner ℝ x (q ω' y) := fun x y => hsym _ _ _ _
      exact stdGaussian_prod_map_proj_add (q ω') h1 h2
    have ih' := ih P' hproj' hsym' hpast' hmeas'
    have hsnoc_meas : Measurable fun p : (E × E) × (Fin n → E × E) =>
        @Fin.snoc n (fun _ => E × E) p.2 p.1 :=
      (Commons.MeasureTheory.Measure.measurable_fin_snoc_const (α := E × E) n).comp measurable_swap
    have h1 : Measure.pi (fun _ : Fin (n + 1) => ν)
        = (ν.prod m).map (fun p : (E × E) × (Fin n → E × E) =>
            @Fin.snoc n (fun _ => E × E) p.2 p.1) := by
      have hcomp : (fun p : (Fin n → E × E) × (E × E) => @Fin.snoc n (fun _ => E × E) p.1 p.2)
          = (fun p : (E × E) × (Fin n → E × E) => @Fin.snoc n (fun _ => E × E) p.2 p.1)
            ∘ Prod.swap := by
        funext p; rfl
      rw [← Commons.MeasureTheory.Measure.map_fin_snoc_prod_pi ν n, hcomp,
          ← Measure.map_map hsnoc_meas measurable_swap, Measure.prod_swap]
    have hT : Measurable T := measurable_triMap hmeas
    have hTcomp : T ∘ (fun p : (E × E) × (Fin n → E × E) =>
            @Fin.snoc n (fun _ => E × E) p.2 p.1)
        = (fun p : (E × E) × (Fin n → E × E) =>
            @Fin.snoc n (fun _ => E) (T' p.2) (g p.2 p.1)) := by
      funext p
      funext j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · simp only [Function.comp_apply, T, Fin.snoc_castSucc]
        simp only [hpast_snoc_eq hpast p.2 p.1 (0, 0) i.castSucc]
        rfl
      · simp only [Function.comp_apply, T, Fin.snoc_last]
        simp only [hpast_snoc_eq hpast p.2 p.1 (0, 0) (Fin.last n)]
        rfl
    have hkey := Commons.MeasureTheory.Measure.map_fin_snoc_skew (α := E)
      (Ω := Fin n → E × E) (μ := μ) (ν := ν) (m := m) n T' g hT' hg ih' hgmap
    rw [h1, Measure.map_map hT hsnoc_meas, hTcomp]
    exact hkey

end aux_sec

theorem map_triangular_eq_stdGaussian_fin_measurable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (n : ℕ) (P : (Fin n → E × E) → Fin n → E →L[ℝ] E)
    (hproj : ∀ ω j, (P ω j).comp (P ω j) = P ω j)
    (hsym : ∀ ω j x y, inner ℝ (P ω j x) y = inner ℝ x (P ω j y))
    (hpast : ∀ ω ω' j, (∀ i, i < j → ω i = ω' i) → P ω j = P ω' j)
    (hmeas : ∀ j, Measurable fun p : (Fin n → E × E) × E => P p.1 j p.2) :
    (MeasureTheory.Measure.pi (fun _ : Fin n =>
        (ProbabilityTheory.stdGaussian E).prod (ProbabilityTheory.stdGaussian E))).map
      (fun ω : Fin n → E × E => fun j : Fin n =>
        P ω j (ω j).1 + (ContinuousLinearMap.id ℝ E - P ω j) (ω j).2)
      = MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.stdGaussian E) :=
  aux n P hproj hsym hpast hmeas

end Commons.Probability.Gaussian