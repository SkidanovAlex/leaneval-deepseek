import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.GramInv.gram_matrix_bounds
import Submission.Work.Diff.EXT.sum_mul_inner_eq
import Submission.Work.Diff.EXT.basis_coeff_norm_equiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open Bundle ContDiff
open scoped Manifold ContDiff Bundle Topology
open Submission.Geodesic

namespace Work.Diff.EXT

/-- Uniform two-sided bounds for the Gram matrix of the coordinate frame of a chart, and for its
inverse, along a metric family `G` that is pinched between `G 0` and `G 0` up to a factor
`exp (2 n C T)` on `[0, T)`.

The proof splits the bounds into

* the compactness input `Work.Diff.GE.exists_chartGram_bounds` (the chart metric of `G 0` is
  comparable to the model norm on the compact set `pt '' K`), and
* the pointwise transfer `G 0 → G t` using the hypothesis `hmet`, with `θ = exp (2 n C T)`.

The metric comparison (at the level of quadratic forms on the tangent space) is then converted into
component bounds by the linear algebra lemmas `sum_mul_inner_eq` (the quadratic form of the Gram
matrix is the metric pairing of the expanded vector), `basis_coeff_norm_equiv` (coefficients of a
basis are comparable to the norm) and `gram_matrix_bounds` (a matrix between two quadratic forms
has bounded entries and bounded inverse entries). -/
theorem gram_data_bounds_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (x₀ : M) (K : Set E) (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target) :
    ∃ c Cl : ℝ, 0 < c ∧ 0 ≤ Cl ∧ c ≤ Cl ∧
      ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
        c ≤ Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i i ∧
        |Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i j| ≤ Cl ∧
        |Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i j| ≤ Cl := by
  classical
  by_cases hcase : K.Nonempty ∧ Nonempty (Fin (Module.finrank ℝ E))
  · obtain ⟨hKne, hnne⟩ := hcase
    have hnpos : 0 < Module.finrank ℝ E := Fin.pos_iff_nonempty.mpr hnne
    haveI hntriv : Nontrivial E := Module.finrank_pos_iff.mp hnpos
    letI hG0 : Submission.Diff.SMet I M := G 0
    letI hRB : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨hG0.toRiemannianMetric⟩
    haveI hSm : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    let Φ : E → M := fun y => (extChartAt I x₀).symm y
    have hΦcont : ContinuousOn Φ K := (continuousOn_extChartAt_symm x₀).mono hKt
    have hK'c : IsCompact (Φ '' K) := hK.image_of_continuousOn hΦcont
    have hK'ne : (Φ '' K).Nonempty := hKne.image Φ
    have hK'src : (Φ '' K) ⊆ (chartAt H x₀).source := by
      rintro p ⟨y, hy, rfl⟩
      have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
        PartialEquiv.map_target (extChartAt I x₀) (hKt hy)
      rwa [extChartAt_source (I := I) x₀] at h1
    obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ :=
      Submission.ChartBounds.exists_chartGram_bounds (I := I) x₀ hK'c hK'ne hK'src
    -- the chart bounds for `G 0`, expressed with the explicit metric pairing
    have hbnd0 : ∀ y ∈ K, ∀ a : E,
        lam * ‖a‖ ^ 2 ≤ (G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
            (frameVector (I := I) x₀ (Φ y) a) ∧
        (G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
            (frameVector (I := I) x₀ (Φ y) a) ≤ Lam * ‖a‖ ^ 2 := by
      intro y hy a
      have h := hbnd (Φ y) ⟨y, hy, rfl⟩ a
      rw [Submission.ChartConnection.chartGram_apply] at h
      exact h
    -- the pinch factor
    let θ : ℝ := Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T)
    have hθpos : 0 < θ := Real.exp_pos _
    have hθnn : 0 ≤ θ := hθpos.le
    have hnc : 0 ≤ (Module.finrank ℝ E : ℝ) * C :=
      mul_nonneg (Nat.cast_nonneg _) hC
    have hexp_le : ∀ t ∈ Set.Ico (T / 2) T,
        Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) ≤ θ := by
      intro t ht
      exact Real.exp_le_exp.mpr (by nlinarith [hnc, ht.1, ht.2, hT])
    -- transfer of the lower bound from `G 0` to `G t`, uniformly on `[T/2, T)` and on `Φ '' K`
    have hlow_gen : ∀ t ∈ Set.Ico (T / 2) T, ∀ p ∈ (Φ '' K), ∀ a : E,
        (1 / θ) * (lam * ‖a‖ ^ 2) ≤
          (G t).inner p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p a) := by
      rintro t ht p ⟨y, hy, rfl⟩ a
      have ht0 : t ∈ Set.Ico 0 T := ⟨le_trans (by linarith [hT]) ht.1, ht.2⟩
      obtain ⟨h1, h2⟩ := hmet t ht0 (Φ y) (frameVector (I := I) x₀ (Φ y) a)
      have het : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) ≤ θ := hexp_le t ht
      have hetpos : 0 < Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) := Real.exp_pos _
      have h0nn : 0 ≤ (G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
          (frameVector (I := I) x₀ (Φ y) a) := by
        by_cases hu : frameVector (I := I) x₀ (Φ y) a = 0
        · rw [hu]; simp
        · exact ((G 0).pos (Φ y) _ hu).le
      calc (1 / θ) * (lam * ‖a‖ ^ 2)
          ≤ (1 / θ) * ((G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
              (frameVector (I := I) x₀ (Φ y) a)) :=
            mul_le_mul_of_nonneg_left (hbnd0 y hy a).1 (by positivity)
        _ ≤ (1 / Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t))
              * ((G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
                 (frameVector (I := I) x₀ (Φ y) a)) := by
            apply mul_le_mul_of_nonneg_right _ h0nn
            exact one_div_le_one_div_of_le hetpos het
        _ ≤ (1 / Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t))
              * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)
                 * (G t).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
                     (frameVector (I := I) x₀ (Φ y) a)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (G t).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
              (frameVector (I := I) x₀ (Φ y) a) := by
            field_simp
    -- transfer of the upper bound
    have hup_gen : ∀ t ∈ Set.Ico (T / 2) T, ∀ p ∈ (Φ '' K), ∀ a : E,
        (G t).inner p (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p a)
          ≤ θ * (Lam * ‖a‖ ^ 2) := by
      rintro t ht p ⟨y, hy, rfl⟩ a
      have ht0 : t ∈ Set.Ico 0 T := ⟨le_trans (by linarith [hT]) ht.1, ht.2⟩
      obtain ⟨h1, h2⟩ := hmet t ht0 (Φ y) (frameVector (I := I) x₀ (Φ y) a)
      have het : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) ≤ θ := hexp_le t ht
      have h0nn : 0 ≤ (G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
          (frameVector (I := I) x₀ (Φ y) a) := by
        by_cases hu : frameVector (I := I) x₀ (Φ y) a = 0
        · rw [hu]; simp
        · exact ((G 0).pos (Φ y) _ hu).le
      calc (G t).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
              (frameVector (I := I) x₀ (Φ y) a)
          ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)
              * ((G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
                 (frameVector (I := I) x₀ (Φ y) a)) := h1
        _ ≤ θ * ((G 0).inner (Φ y) (frameVector (I := I) x₀ (Φ y) a)
                 (frameVector (I := I) x₀ (Φ y) a)) :=
            mul_le_mul_of_nonneg_right het h0nn
        _ ≤ θ * (Lam * ‖a‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hbnd0 y hy a).2 hθnn
    -- the two constants coming from the norm equivalence of the coefficients
    obtain ⟨K1, K2, hK1pos, hK2pos, hnorm⟩ :=
      basis_coeff_norm_equiv (Module.finBasis ℝ E)
    let c : ℝ := (1 / θ) * (lam / K1)
    let Cf : ℝ := θ * Lam * K2
    have hcpos : 0 < c := mul_pos (one_div_pos.mpr hθpos) (div_pos hlam hK1pos)
    have hCfnn : 0 ≤ Cf := mul_nonneg (mul_nonneg hθnn hLam.le) hK2pos.le
    refine ⟨c, max (max Cf (1 / c)) c, hcpos, ?_, le_max_right _ _, ?_⟩
    · exact le_trans (div_pos one_pos hcpos).le
        (le_trans (le_max_right _ _) (le_max_left _ _))
    · intro t ht y hy i j
      let p : M := Φ y
      let B : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ := (G t).inner p
      let σ : Fin (Module.finrank ℝ E) → TangentSpace I p :=
        fun i => frameVector (I := I) x₀ p (Module.finBasis ℝ E i)
      let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
        Work.Diff.GE.GramM G x₀ t p
      have hA : ∀ i j, A i j = B (σ i) (σ j) := fun i j => rfl
      have hsymm : ∀ i j, A i j = A j i := by
        intro i j
        rw [hA i j, hA j i]
        exact (G t).symm p (σ i) (σ j)
      -- the quadratic form of the Gram matrix is the metric pairing of the expanded vector
      have hquad : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
          ∑ i, ∑ j, v i * v j * A i j
            = (G t).inner p (frameVector (I := I) x₀ p (∑ i, v i • Module.finBasis ℝ E i))
                (frameVector (I := I) x₀ p (∑ i, v i • Module.finBasis ℝ E i)) := by
        intro v
        have h1 : ∑ i, ∑ j, v i * v j * A i j
            = ∑ i, ∑ j, v i * v j * (((G t).inner p) (σ i) (σ j)) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [hA i j]
        have h2 := sum_mul_inner_eq ((G t).inner p) σ v
        have h3 : (∑ i, v i • σ i)
            = frameVector (I := I) x₀ p (∑ i, v i • Module.finBasis ℝ E i) := by
          have h4 := frameVector_sum (I := I) Finset.univ x₀ p v
            (fun i => Module.finBasis ℝ E i)
          simpa using h4.symm
        rw [h1, h2, h3]
      -- lower bound for the quadratic form of `A`
      have hlowA : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
          c * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * A i j := by
        intro v
        have hn1 : (∑ i, (v i) ^ 2) ≤ K1 * ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2 :=
          (hnorm v).1
        have hgt := hlow_gen t ht p ⟨y, hy, rfl⟩ (∑ i, v i • Module.finBasis ℝ E i)
        have hstep : c * ∑ i, (v i) ^ 2 ≤
            (1 / θ) * (lam * ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2) := by
          have hd : (∑ i, (v i) ^ 2) / K1 ≤ ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2 := by
            rw [div_le_iff₀ hK1pos]
            exact hn1.trans (le_of_eq (mul_comm _ _))
          have h5 : lam * ((∑ i, (v i) ^ 2) / K1)
              ≤ lam * ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hd hlam.le
          have h6 : (1 / θ) * (lam * ((∑ i, (v i) ^ 2) / K1))
              ≤ (1 / θ) * (lam * ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
          calc c * ∑ i, (v i) ^ 2
              = (1 / θ) * (lam * ((∑ i, (v i) ^ 2) / K1)) := by ring
            _ ≤ (1 / θ) * (lam * ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2) := h6
        rw [hquad v]
        exact le_trans hstep hgt
      -- upper bound for the quadratic form of `A`
      have hupA : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
          ∑ i, ∑ j, v i * v j * A i j ≤ Cf * ∑ i, (v i) ^ 2 := by
        intro v
        have hn2 : ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2 ≤ (∑ i, (v i) ^ 2) * K2 :=
          ((hnorm v).2).trans (le_of_eq (mul_comm _ _))
        have hgt := hup_gen t ht p ⟨y, hy, rfl⟩ (∑ i, v i • Module.finBasis ℝ E i)
        rw [hquad v]
        calc (G t).inner p (frameVector (I := I) x₀ p (∑ i, v i • Module.finBasis ℝ E i))
                (frameVector (I := I) x₀ p (∑ i, v i • Module.finBasis ℝ E i))
            ≤ θ * (Lam * ‖∑ i, v i • Module.finBasis ℝ E i‖ ^ 2) := hgt
          _ ≤ θ * (Lam * ((∑ i, (v i) ^ 2) * K2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn2 hLam.le) hθnn
          _ = Cf * ∑ i, (v i) ^ 2 := by ring
      obtain ⟨-, hdiag, hent, hinv⟩ :=
        Work.Diff.EXT.GramInv.gram_matrix_bounds A hsymm hcpos hCfnn hlowA hupA
      refine ⟨hdiag i, ?_, ?_⟩
      · exact le_trans (hent i j) (le_trans (le_max_left _ _) (le_max_left _ _))
      · exact le_trans (hinv i j) (le_trans (le_max_right _ _) (le_max_left _ _))
  · rw [not_and_or] at hcase
    refine ⟨1, 1, one_pos, zero_le_one, le_refl 1, ?_⟩
    intro t ht y hy i j
    rcases hcase with h | h
    · exact absurd ⟨y, hy⟩ h
    · exact absurd ⟨i⟩ h

end Work.Diff.EXT
