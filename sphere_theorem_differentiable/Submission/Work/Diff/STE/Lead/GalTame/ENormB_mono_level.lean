import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Level

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Level-monotonicity of the energy `ENormB`

For `1 ≤ m ≤ k` the level-`m` energy `D.ENormB m h` of a section with smooth chart data `hh` is
controlled by the level-`k` energy `D.ENormB k h`, with a constant depending only on the data `D`
and on `k` (in particular *uniform* in the section `h` and in the chart data `hh`).

The proof is the iteration of the Poincaré step `ENormSq_Rper_le_succ` (proved in
`Lead/GalTame/Level.lean`), which for every level `j` supplies a single constant `C_j` with

  `ENormSq j (D.Rper i h a b) ≤ C_j * ENormSq (j+1) (D.Rper i h a b)`

simultaneously for all sections `h`, all chart data `hh` and all component indices `i a b`.  Summing
over the components gives `D.ENormB j h ≤ C_j * D.ENormB (j+1) h`, and the chain is closed by
`max C_j 1` (so that the accumulated product is monotone in the number of steps).
-/

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **One level of the Poincaré chain, summed over the components.**  The constant is independent of
the section and of its chart data (it comes from `ENormSq_Rper_le_succ`, which is uniform). -/
lemma ENormB_step (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h),
        D.ENormB j h ≤ C * D.ENormB (j + 1) h := by
  obtain ⟨C, hC, hCb⟩ := ENormSq_Rper_le_succ (I := I) (M := M) D j
  refine ⟨C, hC, ?_⟩
  intro h hh
  simp only [Work.Diff.STE.B3Data.ENormB, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
    Finset.sum_le_sum fun b _ => hCb h hh i a b

/-- The energy `D.ENormB j h` is nonnegative, for an arbitrary bilinear section. -/
lemma ENormB_nonneg_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ℕ)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) : 0 ≤ D.ENormB j h := by
  simp only [Work.Diff.STE.B3Data.ENormB]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => ENormSq_nonneg_gal j (D.Rper i h a b)

theorem ENormB_mono_level
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k),
        D.ENormB m h ≤ C * D.ENormB k h := by
  classical
  -- a single level constant `cf j` for every level `j`, uniform in the section and chart data
  let cf : ℕ → ℝ := fun j => Classical.choose (ENormB_step (I := I) (M := M) D j)
  have hcfb : ∀ j (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h),
      D.ENormB j h ≤ cf j * D.ENormB (j + 1) h := fun j h hh =>
    (Classical.choose_spec (ENormB_step (I := I) (M := M) D j)).2 h hh
  have hstep : ∀ j (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h),
      D.ENormB j h ≤ max (cf j) 1 * D.ENormB (j + 1) h := by
    intro j h hh
    exact le_trans (hcfb j h hh)
      (mul_le_mul_of_nonneg_right (le_max_left (cf j) 1) (ENormB_nonneg_gal D (j+1) h))
  have hprod1 : ∀ K : ℕ, 1 ≤ ∏ j ∈ Finset.range K, max (cf j) 1 := fun K =>
    Finset.one_le_prod₀ (s := Finset.range K) (fun j _ => le_max_right (cf j) 1)
  have hprodn : ∀ K : ℕ, 0 ≤ ∏ j ∈ Finset.range K, max (cf j) 1 := fun K =>
    Finset.prod_nonneg fun j _ => le_trans zero_le_one (le_max_right (cf j) 1)
  -- the chain: for `m ≤ K` the energy at level `m` is bounded by the accumulated product times the
  -- energy at the top level `K`
  have main : ∀ (K : ℕ) (m : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h), m ≤ K →
      D.ENormB m h ≤ (∏ j ∈ Finset.range K, max (cf j) 1) * D.ENormB K h := by
    intro K
    induction K with
    | zero =>
      intro m h hh hmK
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hmK
      subst hm0
      simp
    | succ K ih =>
      intro m h hh hmK
      rcases Nat.lt_or_ge m (K + 1) with hlt | hge
      · have hmK' : m ≤ K := Nat.lt_succ_iff.mp hlt
        have h1 := ih m h hh hmK'
        have h2 := hstep K h hh
        have h3 : D.ENormB m h
            ≤ (∏ j ∈ Finset.range K, max (cf j) 1)
              * (max (cf K) 1 * D.ENormB (K + 1) h) :=
          le_trans h1 (mul_le_mul_of_nonneg_left h2 (hprodn K))
        rw [Finset.prod_range_succ]
        calc D.ENormB m h
            ≤ (∏ j ∈ Finset.range K, max (cf j) 1)
              * (max (cf K) 1 * D.ENormB (K + 1) h) := h3
          _ = ((∏ j ∈ Finset.range K, max (cf j) 1) * max (cf K) 1) * D.ENormB (K + 1) h := by
              ring
      · have hm_eq : m = K + 1 := le_antisymm hmK hge
        subst hm_eq
        calc D.ENormB (K + 1) h ≤ 1 * D.ENormB (K + 1) h := by rw [one_mul]
          _ ≤ (∏ j ∈ Finset.range (K + 1), max (cf j) 1) * D.ENormB (K + 1) h :=
              mul_le_mul_of_nonneg_right (hprod1 (K+1)) (ENormB_nonneg_gal D (K+1) h)
  refine ⟨∏ j ∈ Finset.range k, max (cf j) 1, hprodn k, ?_⟩
  intro h hh m hm hmk
  exact main k m h hh hmk

end

end Work.Diff.STE.Lead.GalTame
