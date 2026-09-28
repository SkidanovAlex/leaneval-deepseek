import Mathlib
import Submission.Work.SSS.HornDefs
import Submission.Work.SSS.cubeToSimplexFun_zero_coord_iff_boundary
import Submission.Work.SSS.cubeToSimplexFun_injective_off_boundary

/-!
# The cone map `I^n × I → Δ^{n+1}` onto the simplex pair `(Δ^{n+1}, Λ[n+1,i])`

`Work.SSS.coneMapFun n i` parametrizes `Δ^{n+1}` by `I^n × I`, with the last (cone) coordinate
placed at the `i`-th vertex:

* the `i`-th coordinate is `1 - t`,
* the `(i.succAbove l)`-th coordinate is `t * θ_n(x)_l`, where `θ_n = cubeToSimplexFun n`.

This file proves `Work.SSS.coneMap_pair`: the cone map is a quotient map, its preimage of the
topological horn `Λ[n+1,i]` is the "cup" `L_n = (I^n × {0}) ∪ (∂I^n × I)` of `Work.StemsB.LSet n`,
and it is injective off that cup.  Together these say that `coneMapFun n i` exhibits the pair
`(I^n × I, L_n)` as a quotient of the pair `(Δ^{n+1}, Λ[n+1,i])`, which is what lets the relative
homotopy lifting property of a Serre fibration be transported to the horn inclusion
(`Work.SSS.relHLP_of_hasHLPRel`).

The three ingredients about `θ_n` are proved in the imported modules: surjectivity, the fact that
a coordinate of `θ_n x` vanishes exactly when `x` lies on the cube boundary, and injectivity of
`θ_n` off that boundary.
-/

open scoped Topology unitInterval

namespace Work.SSS

noncomputable section

/-- The non-`i` coordinates of a point of `Δ^{m+1}` sum to `1` minus the `i`-th coordinate. -/
theorem coneMap_pair_sum_succAbove (m : ℕ) (z : stdSimplex ℝ (Fin (m + 1)))
    (i : Fin (m + 1)) :
    (∑ l : Fin m, z (i.succAbove l)) = 1 - z i := by
  have h := Fin.sum_univ_succAbove (fun j : Fin (m + 1) => (z j : ℝ)) i
  have h2 : (∑ j : Fin (m + 1), (z j : ℝ)) = 1 := z.2.2
  linarith

/-- **Surjectivity of the cube parametrization `θ_n` of the simplex**, proved here so that this
file is independent of the separate development of that fact: for `n+1` the cone coordinate of
`z : Δ^{n+2}` is `1 - z_last`, and the remaining coordinates of `z`, rescaled by the inverse of
the cone coordinate, form a point of `Δ^{n+1}` to which the induction hypothesis applies. -/
theorem coneMap_pair_cubeToSimplex_surjective_aux :
    ∀ n : ℕ, Function.Surjective (cubeToSimplexFun n)
  | 0 => by
    intro z
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    refine stdSimplex.ext (funext fun j => ?_)
    have hz : (z : Fin (0 + 1) → ℝ) 0 = 1 := by
      simpa using z.2.2
    have hj : j = 0 := Fin.ext (by omega)
    rw [hj]
    show (1 : ℝ) = (z : Fin (0 + 1) → ℝ) 0
    rw [hz]
  | n + 1 => by
    intro z
    have hz0 : (0 : ℝ) ≤ z (Fin.last (n + 1)) := stdSimplex.zero_le z _
    have hz1 : (z (Fin.last (n + 1)) : ℝ) ≤ 1 := stdSimplex.le_one z _
    have hSnonneg : 0 ≤ 1 - (z (Fin.last (n + 1)) : ℝ) := by linarith
    by_cases hS : (1 : ℝ) - (z (Fin.last (n + 1)) : ℝ) = 0
    · -- the point is the last vertex
      refine ⟨fun _ => (0 : unitInterval), ?_⟩
      refine stdSimplex.ext (funext fun j => ?_)
      rcases Fin.eq_self_or_eq_succAbove (Fin.last (n + 1)) j with h | ⟨l, hl⟩
      · rw [h]
        simp only [cubeToSimplexFun_last]
        have hzl : z (Fin.last (n + 1)) = 1 := by linarith
        rw [hzl]
        norm_num
      · rw [hl]
        simp only [cubeToSimplexFun_succAbove]
        have hz0' : z ((Fin.last (n + 1)).succAbove l) = 0 := by
          have hsum0 : (∑ l : Fin (n + 1),
              (z ((Fin.last (n + 1)).succAbove l) : ℝ)) = 0 := by
            rw [coneMap_pair_sum_succAbove (n + 1) z (Fin.last (n + 1))]
            exact hS
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun l _ => stdSimplex.zero_le z _)).mp hsum0 l (Finset.mem_univ l)
        rw [hz0']
        simp
    · -- cone over the `n`-simplex with cone coordinate `1 - z_last`
      have hSpos : 0 < 1 - (z (Fin.last (n + 1)) : ℝ) :=
        lt_of_le_of_ne hSnonneg (Ne.symm hS)
      have hSle : 1 - (z (Fin.last (n + 1)) : ℝ) ≤ 1 := by linarith
      have hq_mem : (fun l : Fin (n + 1) =>
            (z ((Fin.last (n + 1)).succAbove l) : ℝ) / (1 - (z (Fin.last (n + 1)) : ℝ))) ∈
          stdSimplex ℝ (Fin (n + 1)) := by
        refine ⟨fun l => div_nonneg (stdSimplex.zero_le z _) (le_of_lt hSpos), ?_⟩
        rw [← Finset.sum_div, coneMap_pair_sum_succAbove (n + 1) z (Fin.last (n + 1)),
          div_self (ne_of_gt hSpos)]
      obtain ⟨y, hy⟩ := coneMap_pair_cubeToSimplex_surjective_aux n
        ⟨fun l : Fin (n + 1) =>
          (z ((Fin.last (n + 1)).succAbove l) : ℝ) / (1 - (z (Fin.last (n + 1)) : ℝ)), hq_mem⟩
      refine ⟨Fin.snoc y ⟨1 - (z (Fin.last (n + 1)) : ℝ), hSnonneg, hSle⟩, ?_⟩
      refine stdSimplex.ext (funext fun j => ?_)
      rcases Fin.eq_self_or_eq_succAbove (Fin.last (n + 1)) j with h | ⟨l, hl⟩
      · rw [h]
        simp only [cubeToSimplexFun_last, Fin.snoc_last]
        ring
      · rw [hl]
        simp only [cubeToSimplexFun_succAbove, Fin.init_snoc, Fin.snoc_last]
        have hyl : (cubeToSimplexFun n y : Fin (n + 1) → ℝ) l
            = (z ((Fin.last (n + 1)).succAbove l) : ℝ) / (1 - (z (Fin.last (n + 1)) : ℝ)) := by
          rw [hy]
          rfl
        rw [hyl, mul_div_cancel₀ _ (ne_of_gt hSpos)]

/-- Surjectivity of the cube parametrization of the simplex. -/
theorem coneMap_pair_cubeToSimplex_surjective (n : ℕ) :
    Function.Surjective (cubeToSimplexFun n) :=
  coneMap_pair_cubeToSimplex_surjective_aux n

/-- **The cone map is surjective onto the simplex.**

Given `z : Δ^{n+1}`, the cone coordinate is forced to be `t = 1 - z i`; if `t = 0` then `z` is the
`i`-th vertex, and otherwise the remaining coordinates of `z`, divided by `t`, form a point of
`Δ^n` which is hit by `θ_n`. -/
theorem coneMap_pair_surjective (n : ℕ) (i : Fin (n + 2)) :
    Function.Surjective (coneMapFun n i) := by
  intro z
  have hzi0 : (0 : ℝ) ≤ z i := stdSimplex.zero_le z i
  have hzi1 : (z i : ℝ) ≤ 1 := stdSimplex.le_one z i
  have hSnonneg : 0 ≤ 1 - (z i : ℝ) := by linarith
  by_cases hS : (1 : ℝ) - (z i : ℝ) = 0
  · -- the point is the `i`-th vertex: the cone coordinate is `0`
    refine ⟨(fun _ => (0 : unitInterval), (0 : unitInterval)), ?_⟩
    refine stdSimplex.ext (funext fun j => ?_)
    rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨l, hl⟩
    · rw [h]
      simp only [coneMapFun_self]
      have hzi : z i = 1 := by linarith
      rw [hzi]
      norm_num
    · rw [hl]
      simp only [coneMapFun_succAbove]
      have hz0 : z (i.succAbove l) = 0 := by
        have hsum0 : (∑ l : Fin (n + 1), (z (i.succAbove l) : ℝ)) = 0 := by
          rw [coneMap_pair_sum_succAbove (n + 1) z i]
          exact hS
        exact (Finset.sum_eq_zero_iff_of_nonneg
          (fun l _ => stdSimplex.zero_le z (i.succAbove l))).mp hsum0 l (Finset.mem_univ l)
      rw [hz0]
      simp
  · -- the point lies on the cone from the `i`-th vertex: rescale the other coordinates
    have hSpos : 0 < 1 - (z i : ℝ) := lt_of_le_of_ne hSnonneg (Ne.symm hS)
    have hSle : 1 - (z i : ℝ) ≤ 1 := by linarith
    have hy_mem : (fun l : Fin (n + 1) => (z (i.succAbove l) : ℝ) / (1 - (z i : ℝ))) ∈
        stdSimplex ℝ (Fin (n + 1)) := by
      refine ⟨fun l => div_nonneg (stdSimplex.zero_le z (i.succAbove l)) (le_of_lt hSpos), ?_⟩
      rw [← Finset.sum_div, coneMap_pair_sum_succAbove (n + 1) z i, div_self (ne_of_gt hSpos)]
    obtain ⟨x, hx⟩ := coneMap_pair_cubeToSimplex_surjective n
      ⟨fun l : Fin (n + 1) => (z (i.succAbove l) : ℝ) / (1 - (z i : ℝ)), hy_mem⟩
    refine ⟨(x, ⟨1 - (z i : ℝ), hSnonneg, hSle⟩), ?_⟩
    refine stdSimplex.ext (funext fun j => ?_)
    rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨l, hl⟩
    · rw [h]
      simp only [coneMapFun_self]
      ring
    · rw [hl]
      simp only [coneMapFun_succAbove]
      have hxl : (cubeToSimplexFun n x : Fin (n + 1) → ℝ) l
          = (z (i.succAbove l) : ℝ) / (1 - (z i : ℝ)) := by
        rw [hx]
        rfl
      rw [hxl, mul_div_cancel₀ _ (ne_of_gt hSpos)]

/-- **The cone map is a quotient map.**  It is a continuous surjection from a compact space onto a
Hausdorff space. -/
theorem coneMap_pair_isQuotientMap (n : ℕ) (i : Fin (n + 2)) :
    Topology.IsQuotientMap (coneMapFun n i) :=
  (Continuous.isClosedMap (continuous_coneMapFun n i)).isQuotientMap
    (continuous_coneMapFun n i) (coneMap_pair_surjective n i)

/-- **The preimage of the horn `Λ[n+1,i]` under the cone map is the cup
`L_n = (I^n × {0}) ∪ (∂I^n × I)`.** -/
theorem coneMap_pair_mem_topHorn_iff (n : ℕ) (i : Fin (n + 2))
    (w : (Fin n → unitInterval) × unitInterval) :
    coneMapFun n i w ∈ TopHorn (n + 1) i ↔ w ∈ Work.StemsB.LSet n := by
  constructor
  · rintro ⟨j, hj, hq⟩
    rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨l, hl⟩
    · exact absurd h hj
    · simp only [hl, coneMapFun_succAbove] at hq
      rcases mul_eq_zero.mp hq with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr ((cubeToSimplexFun_zero_coord_iff_boundary n w.1).mp ⟨l, h⟩)
  · intro hw
    rcases hw with h | h
    · refine ⟨i.succAbove 0, Fin.succAbove_ne i 0, ?_⟩
      simp only [coneMapFun_succAbove]
      have h0 : (w.2 : ℝ) = 0 := congrArg Subtype.val h
      rw [h0, zero_mul]
    · obtain ⟨l, hl⟩ := (cubeToSimplexFun_zero_coord_iff_boundary n w.1).mpr h
      refine ⟨i.succAbove l, Fin.succAbove_ne i l, ?_⟩
      simp only [coneMapFun_succAbove, hl, mul_zero]

/-- **The cone map is injective off the cup.**  Off the cup the cone coordinate is nonzero, so the
result is the cone over `θ_n`, and `θ_n` is injective off the boundary of the cube. -/
theorem coneMap_pair_eq_or_mem_LSet (n : ℕ) (i : Fin (n + 2))
    {w w' : (Fin n → unitInterval) × unitInterval}
    (h : coneMapFun n i w = coneMapFun n i w') :
    w = w' ∨ w ∈ Work.StemsB.LSet n := by
  by_cases hw : w ∈ Work.StemsB.LSet n
  · exact Or.inr hw
  · left
    have hw' : w' ∉ Work.StemsB.LSet n := by
      intro h'
      refine hw ((coneMap_pair_mem_topHorn_iff n i w).mp ?_)
      rw [h]
      exact (coneMap_pair_mem_topHorn_iff n i w').mpr h'
    have ht : (w.2 : ℝ) ≠ 0 := fun h0 => hw (Or.inl (Subtype.ext h0))
    have ht' : (w'.2 : ℝ) ≠ 0 := fun h0 => hw' (Or.inl (Subtype.ext h0))
    have hx : w.1 ∉ Cube.boundary (Fin n) := fun hb => hw (Or.inr hb)
    have hx' : w'.1 ∉ Cube.boundary (Fin n) := fun hb => hw' (Or.inr hb)
    have hti : (w.2 : ℝ) = (w'.2 : ℝ) := by
      have h1 := congrArg (fun q : stdSimplex ℝ (Fin (n + 2)) => (q : Fin (n + 2) → ℝ) i) h
      simp only [coneMapFun_self] at h1
      linarith
    have hθ : cubeToSimplexFun n w.1 = cubeToSimplexFun n w'.1 := by
      refine Subtype.ext (funext fun l => ?_)
      have h1 := congrArg (fun q : stdSimplex ℝ (Fin (n + 2)) =>
        (q : Fin (n + 2) → ℝ) (i.succAbove l)) h
      simp only [coneMapFun_succAbove, hti] at h1
      exact mul_left_cancel₀ ht' h1
    exact Prod.ext (cubeToSimplexFun_injective_off_boundary n hx hx' hθ) (Subtype.ext hti)

theorem coneMap_pair (n : ℕ) (i : Fin (n + 2)) :
    Topology.IsQuotientMap (Work.SSS.coneMapFun n i) ∧
    (∀ w : (Fin n → unitInterval) × unitInterval,
      Work.SSS.coneMapFun n i w ∈ Work.SSS.TopHorn (n + 1) i ↔ w ∈ Work.StemsB.LSet n) ∧
    (∀ w w' : (Fin n → unitInterval) × unitInterval,
      Work.SSS.coneMapFun n i w = Work.SSS.coneMapFun n i w' →
        w = w' ∨ w ∈ Work.StemsB.LSet n) := by
  exact ⟨coneMap_pair_isQuotientMap n i, fun w => coneMap_pair_mem_topHorn_iff n i w,
    fun w w' h => coneMap_pair_eq_or_mem_LSet n i h⟩

end

end Work.SSS
