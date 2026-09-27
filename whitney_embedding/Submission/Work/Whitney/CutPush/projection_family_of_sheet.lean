import Mathlib
import Submission.Work.Whitney.CutPush.projection_family_of_charts
import Submission.Work.Whitney.CutPush.projection_family_of_immersion
import Submission.Work.Whitney.CutPush.arc_compact_chart_cover

/-!
# The chart-cover projection family of the sheet (M1, §2.1 steps 5–6)

Steps 5 and 6 of `CutPush/NOTES_STATE_S59.md` §7.2:

* `exists_local_projections_of_sheet` — over the finite compact chart cover of the parameter interval,
  each piece carries (a) an open *correctness region* `O i`, (b) a globally smooth family `Ψ i` with
  `range (Ψ i t) = range (mfderiv F (δ t))` and `Ψ i t` injective on `O i` (this is
  `exists_local_chart_family`, steps 2–4), and (c) its orthogonal-projection family `Q i`
  (`exists_local_projection_family`), correct on `O i`;
* `exists_fixed_projection_of_sheet` — a single orthogonal projection of rank `n` (extracted from one
  `Q i` at the left endpoint), which the averaging of §7.2 step 8 uses as the "outer" piece.
-/

namespace Work.Whitney.CutPush

open scoped Manifold ContDiff
open Topology

/-- **The per-piece data of the chart-cover projection family.** -/
theorem exists_local_projections_of_sheet {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [LocallyCompactSpace M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFinj : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y))
    {δ : ℝ → M}
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ (ι : Type) (_ : Fintype ι)
      (O : ι → Set ℝ)
      (Q : ι → ℝ → EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))),
      (∀ i, IsOpen (O i)) ∧
      (Set.Icc a b) ⊆ ⋃ i, O i ∧
      (∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Q i) (O i)) ∧
      (∀ i, ∀ t ∈ O i, Q i t * Q i t = Q i t) ∧
      (∀ i, ∀ t ∈ O i, ∀ x y : EuclideanSpace ℝ (Fin (2 * n)),
        inner ℝ (Q i t x) y = inner ℝ x (Q i t y)) ∧
      (∀ i, ∀ t ∈ O i, LinearMap.range (Q i t : EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (2 * n)))
        = LinearMap.range ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ t)
            : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)) := by
  classical
  obtain ⟨ι, hιfin, x, U, K, hUo, hKc, hKU, hKeq, hch⟩ :=
    exists_compact_arc_chart_cover (n := n) δ hδ.continuous a b hab
  haveI := hιfin
  choose Ψ O hOo hKO hOU hΨc hΨinj hΨrng using fun i =>
    exists_local_chart_family F hF hFinj hδ (hUo i) (hKc i) (hKU i) (hch i)
  choose Q hQsm hQrng hQadj hQidem using fun i =>
    exists_local_projection_family (Ψ i) (hΨc i) (hOo i) (hΨinj i)
  have hcov : (Set.Icc a b) ⊆ ⋃ i, O i := by
    intro t ht
    have h1 : t ∈ ⋃ i, K i := by rw [← hKeq]; exact ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h1
    exact Set.mem_iUnion.mpr ⟨i, hKO i hi⟩
  refine ⟨ι, hιfin, O, Q, hOo, hcov, hQsm, ?_, ?_, ?_⟩
  · intro i t ht
    exact hQidem i t ht
  · intro i t ht
    exact hQadj i t ht
  · intro i t ht
    rw [hQrng i t ht, hΨrng i t ht]

/-- **The fixed "outer" projection of the average.**  A single orthogonal projection of rank `n`,
extracted from one of the local projection families at the left endpoint `a` (any point of the covered
interval would do).  The averaging of `NOTES_STATE_S59.md` §7.2 step 8 uses it outside `⋃ i, O i`,
where by construction it is the only active piece. -/
theorem exists_fixed_projection_of_sheet {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [LocallyCompactSpace M]
    (F : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hF : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFinj : ∀ y : M, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F y))
    {δ : ℝ → M}
    (hδ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) δ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ P₀ : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)),
      P₀ * P₀ = P₀ ∧
      (∀ x y : EuclideanSpace ℝ (Fin (2 * n)), inner ℝ (P₀ x) y = inner ℝ x (P₀ y)) ∧
      Module.finrank ℝ (LinearMap.range (P₀ : EuclideanSpace ℝ (Fin (2 * n)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (2 * n)))) = n := by
  classical
  obtain ⟨ι, hιfin, O, Q, hOo, hcov, hQsm, hQidem, hQadj, hQrng⟩ :=
    exists_local_projections_of_sheet F hF hFinj hδ a b hab
  haveI := hιfin
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hcov (Set.left_mem_Icc.mpr hab))
  refine ⟨Q i₀ a, hQidem i₀ a hi₀, hQadj i₀ a hi₀, ?_⟩
  rw [hQrng i₀ a hi₀]
  have hfin := LinearMap.finrank_range_of_inj
    (f := ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) F (δ a))
      : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).toLinearMap)
    (hFinj (δ a))
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  exact hfin.trans hE

end Work.Whitney.CutPush
