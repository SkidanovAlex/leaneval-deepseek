import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Basic

namespace Work.Deep.Conc.BruhnJoos

open Work.Deep.Conc

/-- **A median of a real random variable lies in its range.**

For any real-valued function `X` on a finite nonempty type `Ω` (equipped with the uniform
probability of `Work.Deep.Conc.prob`), there is a value `m` *attained by* `X` such that both
`ℙ(X ≤ m) ≥ 1/2` and `ℙ(m ≤ X) ≥ 1/2`.

The proof takes `m` to be the least attained value `x` with `ℙ(X ≤ x) ≥ 1/2` (the set of such
values is nonempty because the maximum of the range satisfies it). If `ℙ(m ≤ X) < 1/2` then
`ℙ(X < m) > 1/2`, so the largest attained value `m' < m` has `{X < m} ⊆ {X ≤ m'}`, whence
`ℙ(X ≤ m') > 1/2`; this contradicts the minimality of `m`. -/
theorem exists_median {Ω : Type*} [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    ∃ m ∈ Set.range X,
      (1 / 2 : ℝ) ≤ Work.Deep.Conc.prob {ω | X ω ≤ m} ∧
      (1 / 2 : ℝ) ≤ Work.Deep.Conc.prob {ω | m ≤ X ω} := by
  classical
  -- the range of `X`, as a finset `S` of values with `S ⊆ Set.range X`
  obtain ⟨S, hXS, hSrange, hSne⟩ :
      ∃ S : Finset ℝ, (∀ ω : Ω, X ω ∈ S) ∧ (∀ x ∈ S, x ∈ Set.range X) ∧ S.Nonempty := by
    refine ⟨Finset.image X Finset.univ,
      fun ω => Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩, ?_, ?_⟩
    · intro x hx
      obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hx
      exact ⟨ω, hω⟩
    · obtain ⟨ω⟩ : Nonempty Ω := ‹Nonempty Ω›
      exact ⟨X ω, Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩⟩
  -- `M`, the greatest value of the range: `{X ≤ M}` is all of `Ω`
  obtain ⟨M, hMS, hMle⟩ : ∃ M ∈ S, ∀ x ∈ S, x ≤ M :=
    ⟨S.max' hSne, Finset.max'_mem S hSne, fun x hx => Finset.le_max' S x hx⟩
  -- `A` = the values `x` of the range with `ℙ(X ≤ x) ≥ 1/2`; nonempty because `M ∈ A`
  obtain ⟨A, hAiff, hAne⟩ :
      ∃ A : Finset ℝ, (∀ x, x ∈ A ↔ (x ∈ S ∧ (1 / 2 : ℝ) ≤ prob {ω | X ω ≤ x})) ∧ A.Nonempty := by
    refine ⟨S.filter (fun x => (1 / 2 : ℝ) ≤ prob {ω | X ω ≤ x}), fun x => Finset.mem_filter, ?_⟩
    refine ⟨M, Finset.mem_filter.mpr ⟨hMS, ?_⟩⟩
    have hUni : {ω : Ω | X ω ≤ M} = Set.univ := by
      ext ω
      exact iff_of_true (hMle (X ω) (hXS ω)) trivial
    rw [hUni, prob_univ]
    norm_num
  -- `m` := the least element of `A`
  obtain ⟨m, hmA, hAmin⟩ : ∃ m ∈ A, ∀ x ∈ A, m ≤ x :=
    ⟨A.min' hAne, Finset.min'_mem A hAne, fun x hx => Finset.min'_le A x hx⟩
  refine ⟨m, hSrange m ((hAiff m).mp hmA).1, ((hAiff m).mp hmA).2, ?_⟩
  -- the second inequality, by contradiction
  by_contra hcontra
  simp only [not_le] at hcontra
  have hset : {ω : Ω | X ω < m} = {ω : Ω | m ≤ X ω}ᶜ := by
    ext ω
    simp [not_le]
  have hcomp : prob {ω : Ω | X ω < m} = 1 - prob {ω : Ω | m ≤ X ω} := by
    rw [hset, prob_compl]
  have hlt : (1 / 2 : ℝ) < prob {ω | X ω < m} := by
    rw [hcomp]; linarith
  rcases Set.eq_empty_or_nonempty {ω : Ω | X ω < m} with hE | ⟨ω₁, hω₁⟩
  · -- `X < m` never happens, contradicting `ℙ(X < m) > 1/2`
    rw [hE, prob_empty] at hlt
    linarith
  · -- take `m'` the greatest range value strictly below `m`
    obtain ⟨m', hm'S, hm'm, hm'max⟩ := Finset.exists_next_left (s := S) ⟨X ω₁, hXS ω₁, hω₁⟩
    have hsub : {ω : Ω | X ω < m} ⊆ {ω : Ω | X ω ≤ m'} := fun ω hω => hm'max (X ω) (hXS ω) hω
    have hge : (1 / 2 : ℝ) ≤ prob {ω | X ω ≤ m'} :=
      (le_of_lt hlt).trans (prob_mono hsub)
    have hm'A : m' ∈ A := (hAiff m').mpr ⟨hm'S, hge⟩
    -- but then `m ≤ m'`, contradicting `m' < m`
    linarith [hAmin m' hm'A]

end Work.Deep.Conc.BruhnJoos
