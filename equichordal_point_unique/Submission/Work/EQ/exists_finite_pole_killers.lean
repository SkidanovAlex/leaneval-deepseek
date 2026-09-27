import Mathlib

/-!
# Finitely many pole-killers on a compactum

Let `f : ℂ → ℂ` be meromorphic at every point of a compact set `K : Set ℂ`.  Then the
set of points of `K` at which `f` fails to be analytic is finite: the singular set of a
meromorphic function is locally at most one point (`MeromorphicAt.eventually_analyticAt`),
hence locally finite, hence finite on a compactum.  Consequently there is a finite set
`t ⊆ K` of "candidate poles" and multiplicities `n` such that for every `y ∈ K` some
`i ∈ t` makes `z ↦ (z - i) ^ n i * f z` analytic at `y`: take `i` to be a point of the
cover of `K` by isolating balls, and if `y` happens to be a singularity then that cover
point must equal `y`, where the multiplicity supplied by meromorphy kills the pole.

The proof does not use the hypothesis `0 ∉ K`; it is kept because the statement is the
one requested downstream.
-/

open Filter Metric Set
open scoped Topology

namespace Work.EQ

theorem exists_finite_pole_killers {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∉ K)
    (hm : ∀ x ∈ K, MeromorphicAt f x) :
    ∃ (t : Finset ℂ) (n : ℂ → ℕ), (∀ x ∈ t, x ∈ K) ∧
      ∀ y ∈ K, ∃ i ∈ t, AnalyticAt ℂ (fun z => (z - i) ^ n i * f z) y := by
  classical
  -- At each point of `K` the function is meromorphic, so off that single point it is analytic
  -- on a neighbourhood; spelled out as a ball with an explicit radius.
  have key : ∀ x : K, ∃ ε : ℝ, 0 < ε ∧ ∀ y : ℂ, dist y (x : ℂ) < ε → y ≠ (x : ℂ) →
      AnalyticAt ℂ f y := by
    intro x
    have h : ∀ᶠ y in 𝓝[≠] (x : ℂ), AnalyticAt ℂ f y := (hm x x.2).eventually_analyticAt
    rw [eventually_nhdsWithin_iff] at h
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hb⟩ := h
    exact ⟨ε, hε, fun y hy hyx => hb hy hyx⟩
  choose ε hεpos hkey using key
  -- The isolating balls around the points of `K` cover `K`.
  have hcover : K ⊆ ⋃ x : K, Metric.ball (x : ℂ) (ε x) := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    rw [Metric.mem_ball, dist_self]
    exact hεpos ⟨y, hy⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball (x : ℂ) (ε x))
      (fun x => Metric.isOpen_ball) hcover
  -- The finite set of centres: it contains every singularity of `f` inside `K`.
  let tC : Finset ℂ := t.image (Subtype.val : K → ℂ)
  have memK : ∀ i ∈ tC, i ∈ K := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨x, -, rfl⟩
    exact x.2
  -- Meromorphy supplies, at each centre, a multiplicity killing the singularity there.
  have killer : ∀ i : ℂ, i ∈ tC → ∃ m : ℕ, AnalyticAt ℂ (fun z => (z - i) ^ m * f z) i := by
    intro i hi
    obtain ⟨m, hm'⟩ := hm i (memK i hi)
    exact ⟨m, by simpa only [smul_eq_mul] using hm'⟩
  let n : ℂ → ℕ := fun i => if hi : i ∈ tC then Classical.choose (killer i hi) else 0
  refine ⟨tC, n, memK, ?_⟩
  intro y hy
  -- Pick the centre of a ball of the cover containing `y`.
  have hycover : y ∈ ⋃ x ∈ t, Metric.ball (x : ℂ) (ε x) := ht hy
  rw [Set.mem_iUnion₂] at hycover
  obtain ⟨x, hx, hyball⟩ := hycover
  rw [Metric.mem_ball] at hyball
  have hxmem : (x : ℂ) ∈ tC := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  refine ⟨(x : ℂ), hxmem, ?_⟩
  have hn : n (x : ℂ) = Classical.choose (killer (x : ℂ) hxmem) := dite_eq_left hxmem
  rw [hn]
  -- If `y` is that centre we use the killing multiplicity; otherwise `f` is analytic at `y`.
  by_cases hyx : y = (x : ℂ)
  · rw [hyx]; exact Classical.choose_spec (killer (x : ℂ) hxmem)
  · have han : AnalyticAt ℂ f y := hkey x y hyball hyx
    exact (by fun_prop :
      AnalyticAt ℂ (fun z => (z - (x : ℂ)) ^ Classical.choose (killer (x : ℂ) hxmem)) y).mul han

end Work.EQ
