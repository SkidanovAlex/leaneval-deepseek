import Mathlib

/-!
# Smooth cutoff functions with prescribed support

Let `E` be a finite-dimensional real normed vector space. If `K` is compact, `W` is open and
`K ⊆ W`, then there is a smooth function `χ : E → ℝ` equal to `1` on a neighbourhood of `K`
and whose (topological) support `tsupport χ` is contained in `W`.

The proof is the standard one: around each point of `K` build a smooth bump function which is
`1` on a small ball and whose support is contained in `W`; extract a finite subcover of `K`;
then set `χ = 1 - ∏ (1 - g i)`. The pointwise construction is `exists_bump_nhds` below.
-/

namespace Work.WilE9G.Sard

open Metric Set

/-- **Pointwise bump.** If `W` is an open neighbourhood of `x` in a finite-dimensional real
normed space `E`, there is a smooth function `g : E → ℝ` which is `1` on a ball of positive
radius around `x`, and whose topological support is contained in `W`. -/
theorem exists_bump_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {W : Set E} (hW : IsOpen W) {x : E} (hx : x ∈ W) :
    ∃ (g : E → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ y ∈ ball x r, g y = 1) ∧ tsupport g ⊆ W := by
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hx)
  let c : ContDiffBump x :=
    { rIn := ε / 4, rOut := ε / 2, rIn_pos := by linarith, rIn_lt_rOut := by linarith }
  have hro : c.rOut = ε / 2 := rfl
  have hri : c.rIn = ε / 4 := rfl
  refine ⟨c, ε / 4, by linarith, c.contDiff (n := ⊤), ?_, ?_⟩
  · intro y hy
    refine ContDiffBump.one_of_mem_closedBall c ?_
    rw [hri, mem_closedBall]
    exact le_of_lt (mem_ball.mp hy)
  · rw [ContDiffBump.tsupport_eq, hro]
    intro y hy
    exact hεW (mem_ball.mpr (by have := mem_closedBall.mp hy; linarith))

theorem exists_cutoff_supp_infty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [T2Space E] [NormalSpace E] [SigmaCompactSpace E]
    {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : E → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧ tsupport χ ⊆ W := by
  -- A smooth bump around every point of `K`, supported in `W`.
  have hpoint : ∀ x : K, ∃ (g : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ (∀ y ∈ ball x.1 r, g y = 1) ∧
      tsupport g ⊆ W :=
    fun x => exists_bump_nhds hW (hKW x.2)
  choose g r hrpos hgcont hg1 hgsupp using hpoint
  -- The balls on which the bumps equal `1` cover `K`; take a finite subcover.
  have hcover : K ⊆ ⋃ i : K, ball i.1 (r i) := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hrpos _)⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover (fun i : K => ball i.1 (r i))
    (fun _ => isOpen_ball) hcover
  refine ⟨fun x => 1 - ∏ i ∈ T, (1 - g i x), ?_, ⟨⋃ i ∈ T, ball i.1 (r i), ?_, hT, ?_⟩, ?_⟩
  · -- smoothness
    exact contDiff_const.sub (contDiff_prod (fun i _ => contDiff_const.sub (hgcont i)))
  · -- openness of the region where `χ = 1`
    exact isOpen_biUnion (fun _ _ => isOpen_ball)
  · -- `χ = 1` on the union of the balls
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hz : (1 : ℝ) - g i x = 0 := by rw [hg1 i x hxi]; ring
    have hprod : ∏ i ∈ T, (1 - g i x) = 0 := Finset.prod_eq_zero hi hz
    simp [hprod]
  · -- the support of `χ` is contained in the union of the supports of the bumps
    have hsub : Function.support (fun x => 1 - ∏ i ∈ T, (1 - g i x)) ⊆
        ⋃ i ∈ T, tsupport (g i) := by
      intro x hx
      rw [Set.mem_iUnion₂]
      by_contra hcon
      simp only [not_exists] at hcon
      have hzero : ∀ i ∈ T, g i x = 0 := fun i hi =>
        Function.notMem_support.mp fun hmem => hcon i hi (subset_tsupport (g i) hmem)
      have hprod : ∏ i ∈ T, (1 - g i x) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        rw [hzero i hi, sub_zero]
      rw [Function.mem_support] at hx
      exact hx (by simp [hprod])
    refine (closure_minimal hsub ?_).trans ?_
    · exact isClosed_biUnion_finset (fun i _ => isClosed_tsupport (g i))
    · intro x hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨i, _hi, hxi⟩ := hx
      exact hgsupp i hxi

end Work.WilE9G.Sard
