import Mathlib
import Submission.Work.OROneRel.band_hnnConjMap_injective
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetter_generation
import Submission.Work.OROneRel.tlLowCycStep
import Submission.Work.OROneRel.tlLowCyc_cycWord_mem
import Submission.Work.OROneRel.decor_invRev_flip
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.winE_mono
import Submission.Work.OROneRel.coedgeBase
import Submission.Work.OROneRel.exists_treeGauge

namespace Work.OROneRel

/-! ## The reduced word of an all-positive word is the word itself -/

/-- A word all of whose booleans are `true` is reduced: two consecutive letters are never inverse to
each other. -/
private theorem isReduced_of_forall_true {α : Type*} {L : List (α × Bool)}
    (h : ∀ l ∈ L, l.2 = true) : FreeGroup.IsReduced L := by
  rw [FreeGroup.IsReduced]
  induction L with
  | nil => exact List.isChain_nil
  | cons x t ih =>
    cases t with
    | nil => exact List.isChain_singleton x
    | cons y t' =>
      rw [List.isChain_cons_cons]
      refine ⟨?_, ih (fun l hl => h l (List.mem_cons_of_mem _ hl))⟩
      intro _
      rw [h x (by simp), h y (by simp)]

/-- The forward cycle prefix is a word of positive letters, hence reduced. -/
private theorem cycFwdList_isReduced (p q k : ℕ) :
    FreeGroup.IsReduced (cycFwdList p q 0 k) := by
  refine isReduced_of_forall_true ?_
  intro l hl
  simp only [cycFwdList, List.mem_map] at hl
  obtain ⟨j, -, rfl⟩ := hl
  rfl

/-- The reduced word of the forward cycle prefix `cycFwdWord p q k` is the prefix list itself. -/
private theorem wordOf_cycFwdWord (p q k : ℕ) :
    wordOf (cycFwdWord p q k) = cycFwdList p q 0 k := by
  rw [cycFwdWord]
  exact wordOf_mk_of_isReduced (cycFwdList_isReduced p q k)

/-! ## The forward cycle prefix has the weight of its endpoint -/

/-- The `tlW p q`-weight of `cycFwdWord p q k` is the level `cycLevel p q k` reached by the walk:
this is `cohom_mk` on the prefix list together with the telescoping weight
`Work.OROneRel.lsig_cycFwdList`. -/
private theorem cycFwdWord_cohom (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    cohom (tlW p q) (cycFwdWord p q k) = Multiplicative.ofAdd (cycLevel p q (k : ℤ)) := by
  rw [cycFwdWord, cohom_mk, lsig_cycFwdList p q hp hq 0 k, cycLevel_zero, zero_add, sub_zero]

/-- The decorated walk of `cycFwdWord p q k` stays in the short window `[0, p+q-1]`: every decorated
letter is a cycle edge `(cycLetter p q j, cycLevel p q j)`
(`Work.OROneRel.decor_cycFwdList`), and each of these lies in the window
(`Work.OROneRel.cycLetter_level_mem_winE`). -/
private theorem cycFwdWord_walk_in_short_window (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ∀ e ∈ decor (tlW p q) 0 (wordOf (cycFwdWord p q k)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1) := by
  intro e he
  rw [wordOf_cycFwdWord] at he
  have hdec := decor_cycFwdList p q hp hq 0 k
  simp only [cycLevel_zero, zero_add] at hdec
  rw [hdec] at he
  obtain ⟨j, -, hj⟩ := List.mem_map.mp he
  rw [← hj]
  exact cycLetter_level_mem_winE p q hp hq (j : ℤ)

/-! ## The existence of an index of level one -/

/-- **The cycle reaches the level `1`.**  Since `gcd (p+q) q = gcd p q = 1`, the residue `q` is
invertible modulo `p+q`, so there is `k` with `q * k ≡ 1 (mod p+q)`; the level `cycLevel p q k` is
exactly `(k q) mod (p+q)`. -/
private theorem exists_cycLevel_eq_one (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) :
    ∃ k : ℕ, cycLevel p q (k : ℤ) = 1 := by
  have hpq : (p + q).Coprime q := (Nat.coprime_add_self_left (m := p) (n := q)).mpr hcop
  have hqp : q.Coprime (p + q) := hpq.symm
  have h1 : 1 < p + q := by omega
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hqp h1
  refine ⟨k, ?_⟩
  rw [cycLevel, tlN_cast]
  have hcast : ((q : ℤ) * (k : ℤ)) = ((q * k : ℕ) : ℤ) := by push_cast; ring
  rw [mul_comm (k : ℤ) (q : ℤ), hcast, ← Int.natCast_emod, hk]
  norm_num

/-! ## The deck identification -/

/-- **The deck identification.**  For any `k`, the product `tlLowTau p q * (cycFwdWord p q k)⁻¹` lies
in the band vertex window `tlWin p q (p*q)`: it is spelled by
`wordOf tlLowTau ++ invRev (wordOf (cycFwdWord p q k))`, whose weight vanishes and whose decorated
walk is the walk of `tlLowTau` (inside `[0,p*q]`, `Work.OROneRel.tlLowTau_walk`) followed by the walk
of the cycle prefix read back from level `1` (inside `[0,p+q-1]`, hence in `[0,p*q]`). -/
private theorem tlLowTau_mul_cycFwdWord_inv_mem_tlWin (p q k : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q)
    (hwalk : ∀ e ∈ decor (tlW p q) 0 (wordOf (cycFwdWord p q k)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) + (q : ℤ) - 1))
    (hlsigσ : lsig (tlW p q) (wordOf (cycFwdWord p q k)) = 1) :
    tlLowTau p q hp hq hcop * (cycFwdWord p q k)⁻¹ ∈ tlWin p q ((p : ℤ) * (q : ℤ)) := by
  classical
  have hlsigT : lsig (tlW p q) (wordOf (tlLowTau p q hp hq hcop)) = 1 := by
    rw [lsig_wordOf, tlLowTau_cohom]; rfl
  set L : List (Fin 2 × Bool) :=
    wordOf (tlLowTau p q hp hq hcop) ++ FreeGroup.invRev (wordOf (cycFwdWord p q k))
  have hmk : FreeGroup.mk L = tlLowTau p q hp hq hcop * (cycFwdWord p q k)⁻¹ := by
    simp only [L, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mk_wordOf]
  have hlsigL : lsig (tlW p q) L = 0 := by
    simp only [L, decor_lsig_append, lsig_invRev, hlsigT, hlsigσ]
    ring
  have hpq1 : ((p : ℤ) + (q : ℤ) - 1) ≤ (p : ℤ) * (q : ℤ) := by
    have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (p : ℤ) - 1 by linarith)
      (show (0 : ℤ) ≤ (q : ℤ) - 1 by linarith)]
  have hwalkL : ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    intro e he
    simp only [L, decor_append] at he
    rcases List.mem_append.mp he with he1 | he2
    · exact tlLowTau_walk p q hp hq hcop e he1
    · rw [hlsigT, zero_add] at he2
      rw [decor_invRev_flip (tlW p q) 1 (wordOf (cycFwdWord p q k)), hlsigσ, sub_self] at he2
      obtain ⟨p', hp', hpe⟩ := List.mem_map.mp he2
      rw [← hpe]
      exact winE_mono (tlW p q) (by norm_num) hpq1 (hwalk p' (List.mem_reverse.mp hp'))
  rw [show tlLowTau p q hp hq hcop * (cycFwdWord p q k)⁻¹ = FreeGroup.mk L from hmk.symm]
  exact Subgroup.subset_closure ⟨L, rfl, hlsigL, hwalkL⟩

/-! ## The main statement -/

/-- **A short deck element, and the deck identification.**  There is an element `σ` of `F₂` of
weight one whose walk lies in the short window `[0,p+q-1]` (the window graph `Y[0,p+q-1]` is a cycle
through every level in `[0,p+q-1]`, so a path from level `0` to level `1` inside it exists), and for
such a `σ` the product `tlLowTau p q * σ⁻¹` lies in the band vertex window `tlWin p q (p*q)`: its
walk is the walk of `tlLowTau` (which lies in `[0,p*q]` by `Work.OROneRel.tlLowTau_walk`) followed
by the inverse walk of `σ` read back down from level `1`, so it stays in `[0,p*q]`, and its weight
is `0`.

The point of the statement is that it never inspects the *value* of the opaque
`tlLowTau p q = (twoLetterLowTauBound …).choose`: only the interface lemmas
`Work.OROneRel.tlLowTau_walk`/`tlLowTau_cohom` are used. -/
theorem exists_short_deck_with_deck_mem (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hcop : Nat.Coprime p q) :
    ∃ σ : FreeGroup (Fin 2),
      Work.OROneRel.cohom (Work.OROneRel.tlW p q) σ = Multiplicative.ofAdd 1 ∧
      (∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf σ),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0
          ((p : ℤ) + (q : ℤ) - 1)) ∧
      Work.OROneRel.tlLowTau p q hp hq hcop * σ⁻¹ ∈
        Work.OROneRel.tlWin p q ((p : ℤ) * (q : ℤ)) := by
  obtain ⟨k, hk⟩ := exists_cycLevel_eq_one p q hp hq hcop
  refine ⟨cycFwdWord p q k, ?_, ?_, ?_⟩
  · rw [cycFwdWord_cohom p q k hp hq, hk]
  · exact cycFwdWord_walk_in_short_window p q k hp hq
  · refine tlLowTau_mul_cycFwdWord_inv_mem_tlWin p q k hp hq hcop
      (cycFwdWord_walk_in_short_window p q k hp hq) ?_
    rw [lsig_wordOf, cycFwdWord_cohom p q k hp hq, hk]
    rfl

end Work.OROneRel
