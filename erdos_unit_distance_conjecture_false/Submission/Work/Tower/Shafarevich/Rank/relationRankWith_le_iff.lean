import Mathlib
import Submission.Work.Tower.Defs

namespace Work.Tower.Shafarevich.Rank

/-- If `G` admits a presentation with `d` generators and `r'` relators, and `r' ≤ r`, then it
also admits a presentation with `d` generators and `r` relators: pad the list of relators with
trivial ones (the identity element). -/
theorem pad_relators {G : Type} [Group G] {d r' r : ℕ} (hr : r' ≤ r)
    (φ : FreeGroup (Fin d) →* G) (R' : Fin r' → FreeGroup (Fin d))
    (hR' : φ.ker = Subgroup.normalClosure (Set.range R')) :
    ∃ R : Fin r → FreeGroup (Fin d), φ.ker = Subgroup.normalClosure (Set.range R) := by
  refine ⟨fun i => if h : (i : ℕ) < r' then R' ⟨i, h⟩ else 1, ?_⟩
  apply le_antisymm
  · rw [hR']
    apply Subgroup.normalClosure_mono
    rintro x ⟨j, rfl⟩
    refine ⟨⟨(j : ℕ), j.2.trans_le hr⟩, ?_⟩
    show (if h : (j : ℕ) < r' then R' ⟨(j : ℕ), h⟩ else 1) = R' j
    rw [dite_eq_left j.2]
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨i, rfl⟩
    show (if h : (i : ℕ) < r' then R' ⟨(i : ℕ), h⟩ else 1) ∈ φ.ker
    split_ifs with hi
    · rw [hR']
      exact Subgroup.subset_normalClosure ⟨⟨i, hi⟩, rfl⟩
    · exact one_mem _

theorem relationRankWith_le_iff {G : Type} [Group G] [Finite G] (d : ℕ)
    (hd : ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ) (r : ℕ) :
    Work.Tower.relationRankWith G d ≤ r ↔
      ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ ∧
        ∃ R : Fin r → FreeGroup (Fin d), φ.ker = Subgroup.normalClosure (Set.range R) := by
  classical
  refine ⟨fun h => ?_, fun h => Nat.sInf_le h⟩
  -- From any surjection `φ₀ : FreeGroup (Fin d) →* G`, the kernel is the normal closure of a
  -- finite subset of `FreeGroup (Fin d)`: its index is finite (it is `|G|`) and `FreeGroup (Fin d)`
  -- is finitely generated, so Schreier's lemma applies.
  obtain ⟨φ₀, hφ₀⟩ := hd
  have hfin : Finite (FreeGroup (Fin d) ⧸ φ₀.ker) :=
    Finite.of_surjective _ (QuotientGroup.quotientKerEquivOfSurjective φ₀ hφ₀).symm.surjective
  have : φ₀.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hFG : φ₀.ker.FG := (Group.fg_iff_subgroup_fg φ₀.ker).mp inferInstance
  obtain ⟨S, hS⟩ := hFG
  have hker : φ₀.ker = Subgroup.normalClosure (↑S : Set (FreeGroup (Fin d))) := by
    apply le_antisymm
    · rw [← hS]
      exact Subgroup.closure_le_normalClosure
    · apply Subgroup.normalClosure_le_normal
      intro x hx
      rw [← hS]
      exact Subgroup.subset_closure hx
  -- hence the set of admissible numbers of relators is nonempty
  have hne : {r : ℕ | ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ ∧
      ∃ R : Fin r → FreeGroup (Fin d),
        φ.ker = Subgroup.normalClosure (Set.range R)}.Nonempty := by
    refine ⟨S.card, φ₀, hφ₀, (fun i => (S.equivFin.symm i : FreeGroup (Fin d))), ?_⟩
    have hrange : Set.range (fun i => (S.equivFin.symm i : FreeGroup (Fin d)))
        = (↑S : Set (FreeGroup (Fin d))) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, rfl⟩ := hx
        exact Finset.mem_coe.mpr (S.equivFin.symm i).2
      · intro hx
        exact ⟨S.equivFin ⟨x, Finset.mem_coe.mp hx⟩, by simp⟩
    rw [hker, hrange]
  -- `Nat.sInf_mem` exhibits the infimum as an admissible number of relators, and we pad
  obtain ⟨φ, hφ, R, hR⟩ := Nat.sInf_mem hne
  have hle : sInf {r : ℕ | ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ ∧
      ∃ R : Fin r → FreeGroup (Fin d),
        φ.ker = Subgroup.normalClosure (Set.range R)} ≤ r := h
  exact ⟨φ, hφ, pad_relators hle φ R hR⟩

end Work.Tower.Shafarevich.Rank
