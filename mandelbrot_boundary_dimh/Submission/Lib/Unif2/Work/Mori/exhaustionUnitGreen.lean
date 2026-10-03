import Mathlib
import Submission.Lib.Unif2.Work.Mori.regularLevel_unitGreen
import Submission.Lib.Unif2.Work.Mori.torsionFree_abelianization_of_exhaustion
import Submission.Lib.Unif2.Work.Modulus.greenExhaustion

/-!
# The exhaustion of a Riemann surface by the superlevel sets of its Green function

`Work.Mori.isMulTorsionFree_abelianization_of_isUnitGreenFunction` is the assembly of the
*spine-free* route to the uniformization theorem: from the piece-level statement

> every superlevel set `{x | ε ≤ E x} ∪ {z₀}` of a unit-pole Green function at a *regular* level `ε`
> has torsion-free `H₁` (at every base point)

one gets `IsMulTorsionFree (H₁(X))`, and hence (with the hypothesis `H¹(X,ℝ) = 0`, through the
circle-valued character argument of
`Work.SimplyConnected.exists_diffeomorph_plane_or_upperHalfPlane_of_abelianization_torsionFree`)
the uniformization conclusion.

The pieces are `K n = {x | ε n ≤ E x} ∪ {z₀}`, where `ε n` is a strictly decreasing sequence of
regular levels of `E` tending to `0`, with `ε n < c/(n+1)` for a constant `c > 0` chosen so that the
base point `x₀` lies in every piece (`c = 1` if `x₀ = z₀`, `c = E x₀ / 2` otherwise).  Such a
sequence exists by `Work.Mori.exists_regularLevel_of_isUnitGreenFunction` (regular levels are dense
below any positive bound) by a one-step recursion, which is what makes the pieces nested and their
interiors cover `X` (the interiors contain `{x | ε n < E x}` and the pole, by the blow-up of `E` at
`z₀`, `Work.Modulus.growth_of_unitGreen`).

The membership of the pole is why the pieces are `{x | ε ≤ E x} ∪ {z₀}` and not simply the superlevel
sets: `E z₀` is an unconstrained real number, so the superlevel set alone may fail to be closed (and
the pole has to be put back for the pieces to be compact surfaces).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.Mori

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Torsion-freeness of `H₁(X)` from the piece-level statement.** -/
theorem isMulTorsionFree_abelianization_of_isUnitGreenFunction {z₀ x₀ : X} {E : X → ℝ}
    (hX : ¬ CompactSpace X) (hE : Work.UnitGreen.IsUnitGreenFunctionAt (X := X) z₀ E)
    (hpiece : ∀ ε : ℝ, 0 < ε →
      Work.CriticalSet.IsRegularValueOn E (Work.CriticalSet.punctured z₀) ε →
      ∀ p : ↥({x : X | ε ≤ E x} ∪ {z₀}),
        IsMulTorsionFree (Abelianization (FundamentalGroup ↥({x : X | ε ≤ E x} ∪ {z₀}) p))) :
    IsMulTorsionFree (Abelianization (FundamentalGroup X x₀)) := by
  classical
  have hreg := Work.Mori.exists_regularLevel_of_isUnitGreenFunction (X := X) hE hX
  -- the bound on the levels, chosen so that the base point lies in every piece
  let c : ℝ := if x₀ = z₀ then 1 else E x₀ / 2
  have hcpos : 0 < c := by
    by_cases h : x₀ = z₀
    · simp only [c, if_pos h]; norm_num
    · have h1 : 0 < E x₀ := hE.1.1 x₀ h
      simp only [c, if_neg h]; linarith
  have hminpos : ∀ (m : ℝ) (k : ℕ), 0 < m → 0 < min (m / 2) (c / ((k : ℝ) + 2)) := by
    intro m k hm
    exact lt_min (half_pos hm) (div_pos hcpos (by positivity))
  -- one step of the recursion: a regular value below a prescribed positive bound
  have hstep : ∀ m : ℝ, 0 < m → ∃ ε : ℝ, 0 < ε ∧ ε < m ∧
      Work.CriticalSet.IsRegularValueOn E (Work.CriticalSet.punctured z₀) ε := by
    intro m hm
    obtain ⟨ε, h1, h2, h3, -, -⟩ := hreg m hm
    exact ⟨ε, h1, h2, h3⟩
  -- the recursive step on the subtype of positive reals
  let stepU : {m : ℝ // 0 < m} → ℕ → {m : ℝ // 0 < m} := fun gm k =>
    ⟨Classical.choose (hstep (min ((gm : ℝ) / 2) (c / ((k : ℝ) + 2)))
        (hminpos (gm : ℝ) k gm.2)),
      (Classical.choose_spec (hstep (min ((gm : ℝ) / 2) (c / ((k : ℝ) + 2)))
        (hminpos (gm : ℝ) k gm.2))).1⟩
  let s : ℕ → {m : ℝ // 0 < m} := fun n =>
    Nat.rec ⟨Classical.choose (hstep c hcpos), (Classical.choose_spec (hstep c hcpos)).1⟩
      (fun k gk => stepU gk k) n
  let eps : ℕ → ℝ := fun n => Subtype.val (s n)
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    change 0 < Subtype.val (s n)
    exact (s n).2
  have heps_zero : eps 0 = Classical.choose (hstep c hcpos) := rfl
  have heps_succ : ∀ n, eps (n + 1) = Classical.choose (hstep (min (eps n / 2)
      (c / ((n : ℝ) + 2))) (hminpos (eps n) n (heps_pos n))) := fun n => rfl
  have heps_reg : ∀ n, Work.CriticalSet.IsRegularValueOn E
      (Work.CriticalSet.punctured z₀) (eps n) := by
    intro n
    cases n with
    | zero => exact (Classical.choose_spec (hstep c hcpos)).2.2
    | succ k =>
      rw [heps_succ k]
      exact (Classical.choose_spec (hstep (min (eps k / 2) (c / ((k : ℝ) + 2)))
        (hminpos (eps k) k (heps_pos k)))).2.2
  have heps_lt_half : ∀ n, eps (n + 1) < min (eps n / 2) (c / ((n : ℝ) + 2)) := by
    intro n
    rw [heps_succ n]
    exact (Classical.choose_spec (hstep (min (eps n / 2) (c / ((n : ℝ) + 2)))
      (hminpos (eps n) n (heps_pos n)))).2.1
  have heps_dec : ∀ n, eps (n + 1) < eps n := by
    intro n
    have h1 := heps_lt_half n
    have h2 : min (eps n / 2) (c / ((n : ℝ) + 2)) ≤ eps n / 2 := min_le_left _ _
    have h3 : eps n / 2 < eps n := by linarith [heps_pos n]
    linarith
  have heps_anti : Antitone eps := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step h ih => exact le_trans (le_of_lt (heps_dec _)) ih
  have heps_lin : ∀ n, eps n < c / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => rw [heps_zero]; simpa using (Classical.choose_spec (hstep c hcpos)).2.1
    | succ k ih =>
      have h1 := heps_lt_half k
      have h2 : min (eps k / 2) (c / ((k : ℝ) + 2)) ≤ c / ((k : ℝ) + 2) := min_le_right _ _
      have h3 : eps (k + 1) < c / ((k : ℝ) + 2) := lt_of_lt_of_le h1 h2
      have h4 : ((k : ℝ) + 2) = (((k + 1 : ℕ) : ℝ) + 1) := by push_cast; ring
      rwa [h4] at h3
  -- the exhaustion family
  let K : ℕ → Set X := fun n => {x : X | eps n ≤ E x} ∪ {z₀}
  have hKmono : Monotone K := by
    intro m n hmn x hx
    rcases hx with hx | hx
    · exact Or.inl (le_trans (heps_anti hmn) hx)
    · exact Or.inr hx
  have hKint : (⋃ n, interior (K n)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    by_cases hy : y = z₀
    · obtain ⟨C₀, V₀, hV₀, hbnd₀⟩ := hE.2
      obtain ⟨W, hW, hWgrow⟩ := Work.Modulus.growth_of_unitGreen hV₀ hbnd₀ (eps 0)
      rw [← hy] at hW
      refine Set.mem_iUnion.mpr ⟨0, ?_⟩
      refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hW ?_)
      intro x hx
      show eps 0 ≤ E x ∨ x ∈ ({z₀} : Set X)
      by_cases hxz : x = z₀
      · exact Or.inr hxz
      · exact Or.inl (le_of_lt (hWgrow x hx hxz))
    · have hyne : y ∈ (Set.univ : Set X) \ {z₀} := ⟨mem_univ y, by simpa using hy⟩
      have hcont : ContinuousAt E y :=
        Submission.HarmonicOnXAt.continuousAt (hE.1.2.1 y hyne)
      have hypos : 0 < E y := hE.1.1 y hy
      have hcEy : 0 < c / E y := div_pos hcpos hypos
      obtain ⟨N, hN⟩ := exists_nat_gt (c / E y)
      have hbound : c / ((N : ℝ) + 1) < E y := by
        have hsum : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have hlt : c < ((N : ℝ) + 1) * E y := by
          have h' := mul_lt_mul_of_pos_right hN hypos
          rw [div_mul_cancel₀ _ (ne_of_gt hypos)] at h'
          have hstep : (N : ℝ) * E y < ((N : ℝ) + 1) * E y :=
            mul_lt_mul_of_pos_right (by linarith) hypos
          linarith
        by_contra hcon
        have hle : E y ≤ c / ((N : ℝ) + 1) := not_lt.mp hcon
        have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hsum)
        rw [div_mul_cancel₀ _ (ne_of_gt hsum)] at hmul
        linarith
      obtain ⟨n, hn⟩ : ∃ n : ℕ, eps n < E y := ⟨N, lt_trans (heps_lin N) hbound⟩
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      refine mem_interior_iff_mem_nhds.mpr ?_
      have hsub : {x : X | eps n < E x} ⊆ K n := by
        intro x hx
        show eps n ≤ E x ∨ x ∈ ({z₀} : Set X)
        exact Or.inl (le_of_lt hx)
      exact Filter.mem_of_superset
        (hcont.tendsto.eventually (Ioi_mem_nhds hn)) hsub
  have hxK : ∀ n, x₀ ∈ K n := by
    intro n
    show eps n ≤ E x₀ ∨ x₀ ∈ ({z₀} : Set X)
    by_cases h : x₀ = z₀
    · exact Or.inr h
    · have hcle : c ≤ E x₀ := by
        simp only [c, if_neg h]; linarith [hE.1.1 x₀ h]
      have h2 : eps n < c := lt_of_lt_of_le (heps_lin n)
        (div_le_self hcpos.le (by have h : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith))
      exact Or.inl (le_of_lt (lt_of_lt_of_le h2 hcle))
  have htf : ∀ n, IsMulTorsionFree (Abelianization (FundamentalGroup ↥(K n) ⟨x₀, hxK n⟩)) :=
    fun n => hpiece (eps n) (heps_pos n) (heps_reg n) ⟨x₀, hxK n⟩
  exact isMulTorsionFree_abelianization_of_exhaustion x₀ K hKmono hKint hxK htf

end Work.Mori
