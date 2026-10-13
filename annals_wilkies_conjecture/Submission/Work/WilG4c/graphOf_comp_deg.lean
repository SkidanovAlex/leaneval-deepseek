import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG4c.GraphOfComp

namespace Work.WilG4c

open WilkiesDesign Work.WilG0

/-- **Composition of `Ω`-definable maps, with per-coordinate format and degree.**

This is the `Fin m`-indexed refinement of `Work.WilG4c.GraphOfComp`: the coordinate graphs of
`φ` may carry individual formats `F₂ j` and degrees `D₂ j`.  The construction is the same as in
`GraphComp`: work in `ℝ^{(m+1)+m}` with layout `(x, t, w)`, pull back `graphOf g` along the
substitution `(w, t) = sigG m` and each `graphOf (φ · j)` along `(x, w_j) = sigPhi m j`, raise
everything to the single common format `F₁ + (∑ j, F₂ j) + K` (domination of a single `F₂ j` by
the sum via `Finset.single_le_sum`), intersect, and project the trailing `w`-block away.

The intersection of the `m` sets of degrees `D₂ j + 2` costs the *sum* `(∑ j, D₂ j) + 2*m`
(`SOMin.inter`), not `m * (∑ j, D₂ j)`; this is why the per-coordinate statement is genuinely
stronger than applying `GraphOfComp` with a uniform degree. -/
theorem graphOf_comp_deg (S : WilkiesDesign.SOMin) (m : ℕ) :
    ∃ (C₁ C₂ : ℕ), ∀ (F₁ D₁ : ℕ) (F₂ D₂ : Fin m → ℕ)
      (g : (Fin m → ℝ) → ℝ) (φ : (Fin m → ℝ) → (Fin m → ℝ)),
      WilkiesDesign.graphOf g ∈ S.Ω F₁ D₁ (m + 1) →
      (∀ j : Fin m, WilkiesDesign.graphOf (fun x : Fin m → ℝ => φ x j) ∈ S.Ω (F₂ j) (D₂ j) (m + 1)) →
      WilkiesDesign.graphOf (g ∘ φ) ∈
        S.Ω (F₁ + (∑ j : Fin m, F₂ j) + C₁) (D₁ + (∑ j : Fin m, D₂ j) + C₂) (m + 1) := by
  refine ⟨2 * (((m + 1) + m) + (m + 1)) + 1 + 1 + 1 + m + (m + 1), 2 + m * 2, ?_⟩
  intro F₁ D₁ F₂ D₂ g φ hg hφ
  -- The two pullbacks.  Ambients: source dimension `m + 1`, target dimension `(m+1) + m`.
  have hG : GraphComp.setG m g ∈
      S.Ω (F₁ + 2 * (((m + 1) + m) + (m + 1)) + 1) (D₁ + 2) ((m + 1) + m) :=
    GraphComp.subst_mem S (GraphComp.sigG m) hg
  have hH : ∀ j : Fin m, GraphComp.setH m φ j ∈
      S.Ω (F₂ j + 2 * (((m + 1) + m) + (m + 1)) + 1) (D₂ j + 2) ((m + 1) + m) :=
    fun j => GraphComp.subst_mem S (GraphComp.sigPhi m j) (hφ j)
  -- The common format `Fc = (F₁ + ∑ j, F₂ j) + K`, `K = 2 * (...) + 1`.
  have hG_le : F₁ + 2 * (((m + 1) + m) + (m + 1)) + 1 ≤
      (F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1) :=
    Nat.add_le_add_right (Nat.le_add_right F₁ (∑ i : Fin m, F₂ i))
      (2 * (((m + 1) + m) + (m + 1)) + 1)
  have hle_j : ∀ j : Fin m, F₂ j + 2 * (((m + 1) + m) + (m + 1)) + 1 ≤
      (F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1) := by
    intro j
    have h1 : F₂ j ≤ ∑ i : Fin m, F₂ i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (F₂ i)) (Finset.mem_univ j)
    have h2 : F₂ j ≤ F₁ + ∑ i : Fin m, F₂ i :=
      le_trans h1 (Nat.le_add_left (∑ i : Fin m, F₂ i) F₁)
    exact Nat.add_le_add_right h2 (2 * (((m + 1) + m) + (m + 1)) + 1)
  have hG' : GraphComp.setG m g ∈
      S.Ω ((F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1)) (D₁ + 2)
        ((m + 1) + m) :=
    Work.WilG1.Omega.mono hG hG_le le_rfl
  have hH' : ∀ j : Fin m, GraphComp.setH m φ j ∈
      S.Ω ((F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1)) (D₂ j + 2)
        ((m + 1) + m) :=
    fun j => Work.WilG1.Omega.mono (hH j) (hle_j j) le_rfl
  -- Intersect the `m` coordinate pullbacks: the degree is the *sum* `∑ j, (D₂ j + 2)`.
  have hA2 : (⋂ j : Fin m, GraphComp.setH m φ j) ∈
      S.Ω (((F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1)) + 1)
        ((∑ j : Fin m, D₂ j) + m * 2) ((m + 1) + m) := by
    have h := S.inter
      (F := (F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1))
      (n := (m + 1) + m) (k := m) (D := fun j : Fin m => D₂ j + 2)
      (A := fun j : Fin m => GraphComp.setH m φ j) hH'
    have hsum : (∑ j : Fin m, (D₂ j + 2)) = (∑ j : Fin m, D₂ j) + m * 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      simp
    rw [hsum] at h
    exact h
  -- Raise `setG` to the same format and intersect everything.
  have hG'' : GraphComp.setG m g ∈
      S.Ω (((F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1)) + 1) (D₁ + 2)
        ((m + 1) + m) :=
    Work.WilG1.Omega.mono hG' (Nat.le_succ _) le_rfl
  have hInt : (GraphComp.setG m g ∩ ⋂ j : Fin m, GraphComp.setH m φ j) ∈
      S.Ω ((((F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1)) + 1) + 1)
        ((D₁ + 2) + ((∑ j : Fin m, D₂ j) + m * 2)) ((m + 1) + m) :=
    Work.WilG0.Omega_inter2 hG'' hA2
  -- Project the `w`-block away.
  have hProj : projLastIter (m + 1) m (GraphComp.setG m g ∩ ⋂ j : Fin m, GraphComp.setH m φ j) ∈
      S.Ω (((((F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1)) + 1) + 1)
          + m + (m + 1))
        ((D₁ + 2) + ((∑ j : Fin m, D₂ j) + m * 2)) (m + 1) :=
    Work.WilG0.projLastIter_mem S (m + 1) m
      ((((F₁ + (∑ i : Fin m, F₂ i)) + (2 * (((m + 1) + m) + (m + 1)) + 1)) + 1) + 1)
      ((D₁ + 2) + ((∑ j : Fin m, D₂ j) + m * 2)) _ hInt
  -- The projected set is exactly the graph of the composite.
  have hset : projLastIter (m + 1) m (GraphComp.setG m g ∩ ⋂ j : Fin m, GraphComp.setH m φ j) =
      graphOf (g ∘ φ) := by
    rw [Work.WilG0.projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      rw [Set.mem_inter_iff] at hw
      obtain ⟨hGm, hHm⟩ := hw
      rw [Set.mem_iInter] at hHm
      have hlast : x (Fin.last m) = g w := (GraphComp.mem_setG g x w).mp hGm
      have hwx : w = φ (Fin.init x) := by
        funext j
        exact (GraphComp.mem_setH φ j x w).mp (hHm j)
      rw [hwx] at hlast
      simpa [graphOf, Function.comp_def] using hlast
    · intro hx
      have hx' : x (Fin.last m) = g (φ (Fin.init x)) := by
        simpa [graphOf, Function.comp_def] using hx
      refine ⟨φ (Fin.init x), ?_⟩
      rw [Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨(GraphComp.mem_setG g x (φ (Fin.init x))).mpr hx',
        fun j => (GraphComp.mem_setH φ j x (φ (Fin.init x))).mpr rfl⟩
  rw [hset] at hProj
  exact Work.WilG1.Omega.mono hProj (le_of_eq (by ring)) (le_of_eq (by ring))

end Work.WilG4c
