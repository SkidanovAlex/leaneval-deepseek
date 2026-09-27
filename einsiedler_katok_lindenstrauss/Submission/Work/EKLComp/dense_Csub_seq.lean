import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.Crat_dense

/-!
# A dense sequence in the centraliser `Csub t`

`Csub t = C_{SL₃(ℝ)}(aDiag t)` is the centraliser of `aDiag t`, i.e. the group of matrices with
zero entries at every pair `(i,j)` with `t i ≠ t j` (`mem_Csub_iff`).  The lemma
`Crat_dense` of `Submission/Work/EKLComp/Crat_dense.lean` says that the elements of `Csub t`
with rational matrix entries are dense in `Csub t`, in the metric-free sense that for every
`c ∈ Csub t` and every `ε > 0` there is such a `g` with `g⁻¹ c ∈ V ε`.

Here we turn that into an honest *sequence*: the set `CratSub t` of rational-entry elements of
`Csub t` is countable (it is contained in the preimage under `toMat` of the countable set of
matrices with rational entries, and `toMat` is injective), so it can be enumerated, and the
resulting sequence is dense in the left-`V`-sense required by the statement.
-/

namespace Work.EKLComp

open Work.EKLContract

/-- The elements of `Csub t` whose matrix entries are all rational. -/
def CratSub (t : Fin 3 → ℝ) : Set SL3 :=
  {g | g ∈ Csub t ∧ ∀ i j, ∃ q : ℚ, toMat g i j = q}

theorem dense_Csub_seq (t : Fin 3 → ℝ) : ∃ grat : ℕ → Work.EKLContract.SL3, (∀ m, grat m ∈ Work.EKLComp.Csub t) ∧ ∀ c : Work.EKLContract.SL3, c ∈ Work.EKLComp.Csub t → ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, (grat m)⁻¹ * c ∈ Work.EKLContract.V ε := by
  classical
  -- the set of matrices with rational entries
  have hQcount :
      (Set.range (fun w : Fin 3 → Fin 3 → ℚ => (Matrix.of fun i j => (w i j : ℝ)))).Countable :=
    Set.countable_range _
  -- its preimage under the injective map `toMat`
  have hpre : (toMat ⁻¹'
      (Set.range (fun w : Fin 3 → Fin 3 → ℚ => (Matrix.of fun i j => (w i j : ℝ)))) :
        Set SL3).Countable :=
    hQcount.preimage toMat_injective
  have hsub : CratSub t ⊆ (toMat ⁻¹'
      (Set.range (fun w : Fin 3 → Fin 3 → ℚ => (Matrix.of fun i j => (w i j : ℝ)))) :
        Set SL3) := by
    intro g hg
    choose w hw using hg.2
    exact ⟨w, by ext i j; exact (hw i j).symm⟩
  have hRcount : (CratSub t).Countable := hpre.mono hsub
  have hRne : (CratSub t).Nonempty := by
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro i j
    by_cases h : i = j
    · exact ⟨1, by subst h; simp⟩
    · exact ⟨0, by simp [h]⟩
  obtain ⟨f, hf⟩ := hRcount.exists_eq_range hRne
  -- patch the enumeration, replacing the (finitely many) elements outside `Csub t` by `1`
  refine ⟨fun m => if f m ∈ CratSub t then f m else 1, ?_, ?_⟩
  · intro m
    show (if f m ∈ CratSub t then f m else 1) ∈ Csub t
    by_cases h : f m ∈ CratSub t
    · rw [if_pos h]; exact h.1
    · rw [if_neg h]; exact Subgroup.one_mem _
  · intro c hc ε hε
    show ∃ m, ((fun m => if f m ∈ CratSub t then f m else 1) m)⁻¹ * c ∈ V ε
    obtain ⟨g, hgc, hgrat, hgclose⟩ := Crat_dense c hc hε
    have hgR : g ∈ CratSub t := ⟨hgc, hgrat⟩
    have hgrange : g ∈ Set.range f := by rw [← hf]; exact hgR
    obtain ⟨m, hm⟩ := hgrange
    have hfmem : f m ∈ CratSub t := by rw [hm]; exact hgR
    refine ⟨m, ?_⟩
    show (if f m ∈ CratSub t then f m else 1)⁻¹ * c ∈ V ε
    rw [if_pos hfmem, hm]
    exact hgclose

end Work.EKLComp
