import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.Basic

/-!
# A median of a real-valued random variable on a finite probability space

For a finite probability space `ν` on `Ω` and any `X : Ω → ℝ`, there is a value
`m` **taken by `X`** that is a median of `X` in the sense
`P(X ≤ m) ≥ 1/2` and `P(m ≤ X) ≥ 1/2`.

The proof picks the least value `m` in the image of `X` whose lower tail has
mass at least `1/2` (the maximum of the image always works, so this set is
nonempty).  If no image value lies strictly below `m`, then `m ≤ X` holds
everywhere and there is nothing to prove.  Otherwise let `m'` be the largest
image value strictly below `m`; the set of points of `Ω` splits into
`{X ≤ m'} ∪ {m ≤ X}`, so by subadditivity of a finite measure
`1 ≤ P(X ≤ m') + P(m ≤ X)`, while `P(X ≤ m') < 1/2` by minimality of `m`.
-/

namespace Work.Deep.Nibble.BJ

theorem exists_median {Ω : Type*} [Fintype Ω]
    (ν : Work.Deep.Reed.FinProb Ω) (X : Ω → ℝ) :
    ∃ m : ℝ, m ∈ Finset.univ.image X ∧ (1 / 2 : ℝ) ≤ ν.prob {ω | X ω ≤ m} ∧
      (1 / 2 : ℝ) ≤ ν.prob {ω | m ≤ X ω} := by
  classical
  -- `Ω` is nonempty, because the weights of a probability space sum to `1`.
  have huniv : (Finset.univ : Finset Ω).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hsum := ν.wt_sum
    rw [h] at hsum
    simp at hsum
  set S : Finset ℝ := Finset.univ.image X with hSdef
  have hSne : S.Nonempty := huniv.image X
  have hmemS : ∀ ω : Ω, X ω ∈ S := fun ω => Finset.mem_image_of_mem X (Finset.mem_univ ω)
  -- the image values whose lower tail has mass at least `1/2`
  set T : Finset ℝ := S.filter (fun x => (1 / 2 : ℝ) ≤ ν.prob {ω | X ω ≤ x}) with hTdef
  -- the maximum of the image belongs to `T`
  have hmaxlower : (1 / 2 : ℝ) ≤ ν.prob {ω | X ω ≤ S.max' hSne} := by
    have hAu : {ω : Ω | X ω ≤ S.max' hSne} = Set.univ :=
      Set.eq_univ_of_forall fun ω => S.le_max' (X ω) (hmemS ω)
    rw [hAu, ν.prob_univ]
    norm_num
  have hmaxmem : S.max' hSne ∈ T := by
    rw [hTdef]
    exact Finset.mem_filter.mpr ⟨S.max'_mem hSne, hmaxlower⟩
  have hTne : T.Nonempty := ⟨S.max' hSne, hmaxmem⟩
  -- take the least such value
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = T.min' hTne := ⟨_, rfl⟩
  have hminT : T.min' hTne ∈ S.filter (fun x => (1 / 2 : ℝ) ≤ ν.prob {ω | X ω ≤ x}) :=
    T.min'_mem hTne
  have hmem : m ∈ S ∧ (1 / 2 : ℝ) ≤ ν.prob {ω | X ω ≤ m} := by
    rw [hm]
    exact Finset.mem_filter.mp hminT
  refine ⟨m, hmem.1, hmem.2, ?_⟩
  by_cases hbelow : (S.filter (fun x => x < m)).Nonempty
  · -- there is an image value strictly below `m`; let `m'` be the largest one
    obtain ⟨m', hm'⟩ : ∃ m' : ℝ, m' = (S.filter (fun x => x < m)).max' hbelow := ⟨_, rfl⟩
    have hm'mem : m' ∈ S ∧ m' < m := by
      rw [hm']
      exact Finset.mem_filter.mp ((S.filter (fun x => x < m)).max'_mem hbelow)
    -- its lower tail has mass `< 1/2`, by minimality of `m`
    have hlt : ν.prob {ω | X ω ≤ m'} < 1 / 2 := by
      by_contra h
      simp only [not_lt] at h
      have h1 : m' ∈ T := by
        rw [hTdef]
        exact Finset.mem_filter.mpr ⟨hm'mem.1, h⟩
      have h2 : m ≤ m' := by
        rw [hm]
        exact T.min'_le m' h1
      linarith
    -- every point of `Ω` lies in `{X ≤ m'}` or in `{m ≤ X}`
    have hcov : ∀ ω : Ω, X ω ≤ m' ∨ m ≤ X ω := by
      intro ω
      by_cases h1 : X ω ≤ m'
      · exact Or.inl h1
      · right
        by_contra h2
        simp only [not_le] at h1 h2
        have h3 : X ω ∈ S.filter (fun x => x < m) := Finset.mem_filter.mpr ⟨hmemS ω, h2⟩
        have h4 : X ω ≤ (S.filter (fun x => x < m)).max' hbelow :=
          (S.filter (fun x => x < m)).le_max' (X ω) h3
        rw [← hm'] at h4
        linarith
    have hcover : {ω : Ω | X ω ≤ m'} ∪ {ω : Ω | m ≤ X ω} = Set.univ :=
      Set.eq_univ_of_forall fun ω => hcov ω
    have hpu : ν.prob ({ω : Ω | X ω ≤ m'} ∪ {ω : Ω | m ≤ X ω}) = 1 := by
      rw [hcover, ν.prob_univ]
    have hsub : ν.prob ({ω : Ω | X ω ≤ m'} ∪ {ω : Ω | m ≤ X ω})
        ≤ ν.prob {ω : Ω | X ω ≤ m'} + ν.prob {ω : Ω | m ≤ X ω} :=
      ν.prob_union_le _ _
    linarith
  · -- no image value is below `m`: the upper tail is all of `Ω`
    have hall : ∀ ω : Ω, m ≤ X ω := by
      intro ω
      by_contra h
      simp only [not_le] at h
      exact hbelow ⟨X ω, Finset.mem_filter.mpr ⟨hmemS ω, h⟩⟩
    have hcover : {ω : Ω | m ≤ X ω} = Set.univ := Set.eq_univ_of_forall fun ω => hall ω
    rw [hcover, ν.prob_univ]
    norm_num

end Work.Deep.Nibble.BJ
