import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Q44Child.lam_attained

set_option autoImplicit false

noncomputable section

namespace Work.HP.Vero

/-- `eNorm` is `rNorm` after realification. -/
lemma eNorm_eq_rNorm_intCastPi {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    eNorm v = rNorm (intCastPi v) := by
  simp [eNorm, rNorm, intCastPi]

/-- Every real `r ≥ 0` that admits `i` real-independent vectors of `realify Λ` of norm `≤ r`
also admits `i` `ℤ`-independent vectors of `Λ` of norm `≤ r`.

The point is that the points of `realify Λ = Λ.map intCastPi` are exactly the realifications of
the integer points of `Λ`, and real linear independence of a realified family of integer vectors
is equivalent to `ℤ`-linear independence of the family (base change along `ℤ → ℝ`). -/
lemma realify_subset_lamSet {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℤ)) (i : ℕ) :
    {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
        (∀ j, f j ∈ realify Λ) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r}
      ⊆ {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℤ),
        (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r} := by
  intro r hr
  obtain ⟨hr0, f, hfL, hfI, hfr⟩ := hr
  have hvmem : ∀ j, ∃ v : ι → ℤ, v ∈ Λ ∧ intCastPi v = f j :=
    fun j => Submodule.mem_map.mp (hfL j)
  choose v hv using hvmem
  refine ⟨hr0, v, fun j => (hv j).1, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff] at hfI ⊢
    intro c hc
    have h1 : (∑ j, c j • intCastPi (v j)) = 0 := by
      have := congrArg intCastPi hc
      simpa only [map_sum, map_smul, map_zero] using this
    have h2 : (∑ j, c j • f j) = 0 := by
      simpa only [hv] using h1
    have h3 : (∑ j, ((c j : ℤ) : ℝ) • f j) = 0 := by
      simpa only [Int.cast_smul_eq_zsmul] using h2
    intro j
    have h4 : ((c j : ℤ) : ℝ) = 0 := hfI (fun j => ((c j : ℤ) : ℝ)) h3 j
    exact_mod_cast h4
  · intro j
    rw [eNorm_eq_rNorm_intCastPi, (hv j).2]
    exact hfr j

/-- The `i`-th successive minimum of `Λ` is at most that of its realification `realify Λ`. -/
lemma lam_le_lamR_realify {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℤ)) (i : ℕ)
    (hne : ∃ f : Fin i → (ι → ℤ), (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f) :
    lam Λ i ≤ lamR (realify Λ) i := by
  obtain ⟨g, hgL, hgI⟩ := hne
  have hsub := realify_subset_lamSet Λ i
  have hneC : {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℝ),
        (∀ j, f j ∈ realify Λ) ∧ LinearIndependent ℝ f ∧ ∀ j, rNorm (f j) ≤ r}.Nonempty := by
    refine ⟨∑ j, eNorm (g j), Finset.sum_nonneg (fun j _ => eNorm_nonneg _),
      fun j => intCastPi (g j), ?_, ?_, fun j => ?_⟩
    · intro j; exact Submodule.mem_map_of_mem (hgL j)
    · have h := linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (ι := Fin i) (ι' := ι) (v := g)
      have heq : (fun j => intCastPi (g j)) = (fun j => (algebraMap ℤ ℝ) ∘ g j) := by
        funext j i; simp [intCastPi]
      rw [heq]; exact h.mpr hgI
    · simpa [eNorm_eq_rNorm_intCastPi] using
        Finset.single_le_sum (fun k _ => eNorm_nonneg (g k)) (Finset.mem_univ j)
  have hbdd : BddBelow ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → (ι → ℤ),
        (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r} : Set ℝ) :=
    ⟨0, fun r hr => hr.1⟩
  exact csInf_le_csInf hbdd hneC hsub

/-- If `lamR (realify Λ) i ≤ B` and there are `i` `ℤ`-independent vectors of `Λ`, then there are `i`
`ℤ`-independent vectors of `Λ` of norm at most `B`.

Suggested route: the set `S = {r ≥ 0 | ∃ i independent vectors of `realify Λ` with all norms ≤ r}`
is nonempty and upward closed, so it contains `(sInf S, ∞)`, and the *minimum* of the maximal norm
over independent `i`-tuples is attained: the vectors of `Λ` inside the ball of radius `B+1` form a
finite set (bounded integer vectors), so among the finitely many `i`-tuples in that ball one has
minimal maximal norm `m`; every independent `i`-tuple has maximal norm `≥ m`, and `m = sInf S`, so
`m ≤ B` and the minimising tuple is the required witness. -/
theorem lamR_witness {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℤ)) (i : ℕ)
    (hne : ∃ f : Fin i → (ι → ℤ), (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f)
    {B : ℝ} (h : lamR (realify Λ) i ≤ B) :
    ∃ f : Fin i → (ι → ℤ), (∀ j, f j ∈ Λ) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ B := by
  classical
  obtain ⟨f0, hf0L, hf0I⟩ := hne
  -- `i` independent vectors of `Λ` bound `i` by the rank of `Λ`
  have hirank : i ≤ rk Λ := by
    have hLI : LinearIndependent ℤ (fun j : Fin i => (⟨f0 j, hf0L j⟩ : Λ)) := by
      rw [Fintype.linearIndependent_iff] at hf0I ⊢
      intro c hc
      have hc' : (∑ j, c j • f0 j) = 0 := by
        have := congrArg (Subtype.val) hc
        simpa [map_sum, map_smul] using this
      exact hf0I c hc'
    have := hLI.fintype_card_le_finrank
    simpa [rk, Fintype.card_fin] using this
  -- the successive minimum of `Λ` is at most that of its realification
  have hle : lam Λ i ≤ lamR (realify Λ) i := lam_le_lamR_realify Λ i ⟨f0, hf0L, hf0I⟩
  -- the successive minimum of `Λ` is attained
  obtain ⟨g, hgL, hgI, hgb⟩ := Work.HP.Q44Child.lamAttained_aux Λ hirank
  exact ⟨g, hgL, hgI, fun j => (hgb j).trans (hle.trans h)⟩

end Work.HP.Vero
