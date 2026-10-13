import Mathlib
import Submission.Work.DSCOH.Shift

/-!
Area DSCOH (curric-46) — the shifts `S(-d)` of the polynomial ring `S = A[x₀,…,x_{n-1}]` really are
direct summands, i.e. `⨁_{e ≥ 0} shift d e = Poly A n` internally.

The `e`-th piece of `shift d` is the `(e - d)`-th homogeneous piece of `S` when `e ≥ d`, and `⊥`
otherwise; it is therefore the standard grading of `S`, reindexed onto the degrees `≥ d`.  The two
ingredients are the independence of the homogeneous pieces (`iSupIndep`, transported along the
injective reindexing on the `⊥`-free part of the index set) and the fact that they span, which is
`iSup (shift d) = iSup (homogeneousSubmodule) = ⊤`.
-/

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The `e`-th piece of the shift is the `(e-d)`-th homogeneous piece of `S`; in particular the
nonzero pieces of the shift are exactly the (nonempty) homogeneous pieces. -/
lemma shift_eq_homSub_of_ne_bot {d : ℕ}
    (e : {e : ℕ // shift (A := A) (n := n) d e ≠ ⊥}) :
    shift (A := A) (n := n) d e.1 = homSub (A := A) n (e.1 - d) := by
  by_cases h : d ≤ e.1
  · exact shift_of_le h
  · exact absurd (shift_of_not_le h) e.2

theorem shift_isInternal {A : Type*} [CommRing A] {n : ℕ} (d : ℕ) :
    DirectSum.IsInternal (shift (A := A) (n := n) d) := by
  have hdec : DirectSum.Decomposition (homSub (A := A) n) :=
    MvPolynomial.decomposition (σ := Fin n) (R := A)
  have hhom : DirectSum.IsInternal (homSub (A := A) n) :=
    @DirectSum.Decomposition.isInternal ℕ (Poly A n) (Submodule A (Poly A n))
      _ _ _ _ (homSub (A := A) n) hdec
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · -- The nonzero pieces of the shift are independent: they are the homogeneous pieces,
    -- reindexed by the injective map `e ↦ e - d`.
    rw [← iSupIndep_ne_bot]
    have hind : iSupIndep (homSub (A := A) n) := hhom.submodule_iSupIndep
    have hle : ∀ e : {e : ℕ // shift (A := A) (n := n) d e ≠ ⊥}, d ≤ e.1 := by
      intro e
      by_contra h
      exact e.2 (shift_of_not_le h)
    have key : iSupIndep (fun e : {e : ℕ // shift (A := A) (n := n) d e ≠ ⊥} =>
        homSub (A := A) n (e.1 - d)) :=
      hind.comp (f := fun e : {e : ℕ // shift (A := A) (n := n) d e ≠ ⊥} => e.1 - d)
        (fun a b hab => by
          have ha := hle a; have hb := hle b
          apply Subtype.ext
          simp only at hab ⊢
          omega)
    have hfam : (fun e : {e : ℕ // shift (A := A) (n := n) d e ≠ ⊥} =>
          homSub (A := A) n (e.1 - d))
        = (fun e : {e : ℕ // shift (A := A) (n := n) d e ≠ ⊥} =>
          shift (A := A) (n := n) d e.1) := by
      funext e
      exact (shift_eq_homSub_of_ne_bot e).symm
    rw [← hfam]
    exact key
  · -- The pieces of the shift span: `⨆ e, shift d e = ⨆ k, homSub k = ⊤`.
    have htop : iSup (homSub (A := A) n) = ⊤ := hhom.submodule_iSup_eq_top
    rw [← htop]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun e => ?_
      by_cases h : d ≤ e
      · rw [shift_of_le h]; exact le_iSup (homSub (A := A) n) (e - d)
      · rw [shift_of_not_le h]; exact bot_le
    · refine iSup_le fun k => ?_
      have hk : homSub (A := A) n k = shift (A := A) (n := n) d (d + k) := by
        rw [shift_of_le (Nat.le_add_right d k), Nat.add_sub_cancel_left]
      rw [hk]
      exact le_iSup (fun e => shift (A := A) (n := n) d e) (d + k)

end Work.DSCOH
