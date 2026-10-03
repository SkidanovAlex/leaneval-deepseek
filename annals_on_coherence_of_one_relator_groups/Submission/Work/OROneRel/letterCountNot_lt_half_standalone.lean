import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.letterCountHalfAux
import Submission.Work.OROneRel.isReduced_replicate_of_fst_eq
import Submission.Work.OROneRel.isReduced_rotate_of_isCyclicallyReduced
import Submission.Work.OROneRel.exists_complement_of_isSubwordOf_pow

namespace Work.OROneRel

universe u

variable {α : Type u}

-- The hypothesis `hpp` (the relator is not a proper power) is carried over from the original
-- statement but is not needed for this estimate.
set_option linter.unusedVariables false

/-- The product of the `ofAdd`-images of a list of integers is the `ofAdd` of the sum of those
integers. -/
lemma lhs_prod_map_ofAdd {β : Type*} (L : List β) (g : β → ℤ) :
    (L.map (fun x => Multiplicative.ofAdd (g x))).prod =
      Multiplicative.ofAdd ((L.map g).sum) := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

/-- The exponent sum of `z` in `mk L` is the letter exponent sum of the word `L`. -/
theorem lhs_expSum_mk_eq_ofAdd_ssum (z : α) (L : List (α × Bool)) :
    expSum z (FreeGroup.mk L) = Multiplicative.ofAdd (ssum z L) := by
  classical
  have h1 : expSum z (FreeGroup.mk L)
      = (L.map (fun x => Multiplicative.ofAdd (gfun z x))).prod := by
    unfold expSum
    rw [FreeGroup.lift_mk]
    congr 1
    apply List.map_congr_left
    intro x _
    obtain ⟨a, b⟩ := x
    simp only [gfun]
    by_cases h : a = z
    · subst h
      cases b <;> simp
    · cases b <;> simp [h]
  rw [h1]
  unfold ssum
  exact lhs_prod_map_ofAdd L (gfun z)

/-- The absolute value of the exponent sum of `z` in a word is bounded by the number of `z`-letters
in it. -/
theorem lhs_abs_ssum_le_tcount (z : α) (L : List (α × Bool)) :
    |ssum z L| ≤ ((tcount z L : ℕ) : ℤ) := by
  classical
  induction L with
  | nil => simp [ssum, tcount]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    have hs : ssum z ((a, b) :: L) = gfun z (a, b) + ssum z L := by
      simp [ssum, List.map_cons, List.sum_cons]
    have ht : ((tcount z ((a, b) :: L) : ℕ) : ℤ)
        = (if a = z then (1 : ℤ) else 0) + ((tcount z L : ℕ) : ℤ) := by
      have h1 : tcount z ((a, b) :: L) = (if a = z then 1 else 0) + tcount z L := by
        rw [tcount, List.countP_cons]
        by_cases h : a = z
        · simp [tcount, tp, h]
          omega
        · simp [tcount, tp, h]
      rw [h1, Nat.cast_add]
      by_cases h : a = z <;> simp [h]
    have hg : |gfun z (a, b)| ≤ (if a = z then (1 : ℤ) else 0) := by
      by_cases h : a = z
      · rw [if_pos h]
        cases b <;> simp [gfun, h]
      · rw [if_neg h]
        simp [gfun, h]
    rw [hs, ht]
    exact (abs_add_le (gfun z (a, b)) (ssum z L)).trans (add_le_add hg ih)

/-- **Arc decomposition.**  If the periodic word `(replicate k W).flatten` is written as
`L1 ++ V ++ L2` and `V` is no longer than `W`, then `V` is a prefix of the rotation of `W`
starting at the position `L1.length`, and the complementary suffix `S` has length
`W.length - V.length` and is reduced. -/
theorem lhs_rotate_subword_decomposition_list {W V L1 L2 : List (α × Bool)} {k : ℕ}
    (hcyc : FreeGroup.IsCyclicallyReduced W)
    (h : (List.replicate k W).flatten = L1 ++ V ++ L2) (hlen : V.length ≤ W.length) :
    ∃ (j : ℕ) (S : List (α × Bool)),
      V ++ S = W.rotate j ∧ S.length = W.length - V.length ∧ FreeGroup.IsReduced S := by
  have htake : V = (W.rotate L1.length).take V.length :=
    eq_rotate_take_of_flatten_replicate_eq h hlen
  refine ⟨L1.length, (W.rotate L1.length).drop V.length, ?_, ?_, ?_⟩
  · have h1 := List.take_append_drop V.length (W.rotate L1.length)
    rw [← htake] at h1
    exact h1
  · rw [List.length_drop, List.length_rotate]
  · exact (isReduced_rotate_of_isCyclicallyReduced hcyc L1.length).infix
      ⟨V, [], by
        have h1 := List.take_append_drop V.length (W.rotate L1.length)
        rw [← htake] at h1
        simpa using h1⟩

/-- A reduced word all of whose letters have generator `z` is a constant word. -/
theorem lhs_exists_replicate_of_isReduced_of_forall_fst_eq (z : α) {L : List (α × Bool)}
    (hr : FreeGroup.IsReduced L) (h : ∀ p ∈ L, p.1 = z) :
    ∃ b : Bool, L = List.replicate L.length (z, b) := by
  cases L with
  | nil => exact ⟨true, rfl⟩
  | cons p L' =>
    obtain ⟨c, hc⟩ := isReduced_replicate_of_fst_eq hr h
    have hall : ∀ x ∈ (p :: L'), x = c := List.eq_replicate_length.mp hc
    have hc1 : c.1 = z := by
      rw [← hall p (by simp)]
      exact h p (by simp)
    exact ⟨c.2, List.eq_replicate_length.mpr fun x hx => by
      obtain rfl : x = c := hall x hx
      exact Prod.ext hc1 rfl⟩

/-- **Short subwords involve strictly fewer non-`z` letters than the relator.**  A standalone
re-proof (fresh module, only buildable imports) of
`Work.OROneRel.letterCountNot_lt_of_isSubwordOf_half`, whose module
`Submission.Work.OROneRel.letterCountNot_lt_of_isSubwordOf_half` currently cannot be imported because
`Submission.Work.OROneRel.abs_ssum_le_tcount` and `Submission.Work.OROneRel.expSum_mk_eq_ofAdd_ssum`
fail to build.  Mathematically: `v` is an arc of the cyclic word of the cyclically reduced relator `r`
of length at most half the circumference, so it misses at least as much as it contains; if the
complementary arc consisted only of `z`-letters, then (as the reduced word of `r` is cyclically
reduced) that arc would be a constant run `z ^ L` or `z ^ (-L)`, whence `|σ_z v| = L = |r| - |v| ≥ |v|`
while trivially `|σ_z v| ≤` the number of `z`-letters of `v ≤ |v|`; so all of `v` and the whole of `r`
would consist of the letter `z`, contradicting `σ_z r = 0` for a nontrivial relator. -/
theorem letterCountNot_lt_half_standalone {α : Type u} (r v : FreeGroup α) (z : α) (k : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hpp : ¬ Work.OROneRel.IsProperPower r) (hz : z ∈ Work.OROneRel.relatorLetters r)
    (hσ : Work.OROneRel.expSum z r = 1)
    (hsub : Work.OROneRel.IsSubwordOf v (r ^ k))
    (hhalf : 2 * Work.OROneRel.relatorNorm v ≤ Work.OROneRel.relatorNorm r) (hv1 : v ≠ 1) :
    Work.OROneRel.letterCountNot z v < Work.OROneRel.letterCountNot z r := by
  classical
  set W : List (α × Bool) := FreeGroup.toWord r with hW
  set V : List (α × Bool) := FreeGroup.toWord v with hV
  have hWr : FreeGroup.toWord r = W := hW.symm
  have hVv : FreeGroup.toWord v = V := hV.symm
  have hrcyc : FreeGroup.IsCyclicallyReduced W := hcyc
  have hredW : FreeGroup.IsReduced W := hrcyc.1
  have hredV : FreeGroup.IsReduced V := by rw [hV]; exact FreeGroup.isReduced_toWord
  have hnormr : relatorNorm r = W.length := by
    simp only [relatorNorm, FreeGroup.norm, ← hW]
  have hnormv : relatorNorm v = V.length := by
    simp only [relatorNorm, FreeGroup.norm, ← hV]
  -- `v ≠ 1` gives `0 < V.length`
  have hVne : V ≠ [] := by
    intro h
    rw [hV] at h
    exact hv1 (FreeGroup.toWord_eq_nil_iff.mp h)
  have hV1 : 0 < V.length := List.length_pos_iff.mpr hVne
  -- `z ∈ relatorLetters r` gives `0 < W.length`
  have hW1 : 0 < W.length := by
    have hz' : ∃ b : Bool, (z, b) ∈ FreeGroup.toWord r := by
      simpa only [relatorLetters, Set.mem_ofPred_eq] using hz
    obtain ⟨b, hb⟩ := hz'
    rw [hWr] at hb
    exact List.length_pos_iff.mpr (fun h => by rw [h] at hb; simp at hb)
  have h2VW : 2 * V.length ≤ W.length := by
    have h := hhalf
    simp only [hnormv, hnormr] at h
    exact h
  have hVW : V.length ≤ W.length := by omega
  have hlen : relatorNorm v < relatorNorm r := by rw [hnormv, hnormr]; omega
  -- the arc decomposition of `v` in the cyclic word of `r`
  obtain ⟨L1, L2, hL⟩ := hsub
  have hflat : FreeGroup.toWord (r ^ k) = (List.replicate k W).flatten := by
    rw [FreeGroup.toWord_pow, ← hW]
    exact (FreeGroup.isReduced_iff_reduce_eq).mp (hrcyc.flatten_replicate k).isReduced
  have hmain : (List.replicate k W).flatten = L1 ++ V ++ L2 := by
    rw [← hflat, hL, hVv]
  obtain ⟨j, S, hVS, _, hSred⟩ :=
    lhs_rotate_subword_decomposition_list (k := k) (L1 := L1) (L2 := L2) hrcyc hmain hVW
  have hWsum : W.length = V.length + S.length := by
    have h := congrArg List.length hVS
    rw [List.length_append, List.length_rotate] at h
    omega
  -- `r` and `v` as words
  have hr_eq : r = FreeGroup.mk W := by rw [hW]; exact (FreeGroup.mk_toWord (x := r)).symm
  have hv_eq : v = FreeGroup.mk V := by rw [hV]; exact (FreeGroup.mk_toWord (x := v)).symm
  -- letter counts
  have hcntV : letterCountNot z v = V.length - tcount z V := by
    rw [hv_eq, letterCountNot_mk_of_isReduced z hredV]
  have hcntR : letterCountNot z r = W.length - tcount z W := by
    rw [hr_eq, letterCountNot_mk_of_isReduced z hredW]
  have hcountW : tcount z W = tcount z V + tcount z S := by
    have h : tcount z (V ++ S) = tcount z (W.rotate j) := by rw [hVS]
    rw [tcount_append, tcount_rotate] at h
    exact h.symm
  -- the relator is nontrivial as a `z`-word
  have hposr : 0 < letterCountNot z r := by
    by_contra hcon
    have hr0 : letterCountNot z r = 0 := Nat.eq_zero_of_not_pos hcon
    have htau : tcount z W = W.length := by
      have htW : tcount z W ≤ W.length := by
        rw [hcountW, hWsum]
        exact Nat.add_le_add (tcount_le_length z V) (tcount_le_length z S)
      have h : W.length - tcount z W = 0 := by rw [← hcntR, hr0]
      have h2 : W.length ≤ tcount z W := Nat.le_of_sub_eq_zero h
      exact le_antisymm htW h2
    have hallW : ∀ p ∈ W, p.1 = z := (tcount_eq_length_iff z W).mp htau
    obtain ⟨b, hbW⟩ := lhs_exists_replicate_of_isReduced_of_forall_fst_eq z hredW hallW
    have hssumW : ssum z W = if b then (W.length : ℤ) else -(W.length : ℤ) := by
      rw [hbW, ssum_replicate]
      cases b <;> simp
    have hexp : Multiplicative.ofAdd (ssum z W) = 1 := by
      rw [← lhs_expSum_mk_eq_ofAdd_ssum z W, ← hr_eq]
      exact hσ
    have hsum0 : ssum z W = 0 := by
      have h1 : Multiplicative.ofAdd (ssum z W) = Multiplicative.ofAdd (0 : ℤ) := by
        simpa using hexp
      exact Multiplicative.ofAdd.injective h1
    have habs : |ssum z W| = (W.length : ℤ) := by
      rw [hssumW]
      cases b <;> simp
    have hW0 : W.length = 0 := by
      have h : (W.length : ℤ) = 0 := by rw [← habs, hsum0]; simp
      exact_mod_cast h
    omega
  -- the complementary arc contains a letter different from `z`
  have hSlt : tcount z S < S.length := by
    by_contra hcon
    have hSeq : tcount z S = S.length := le_antisymm (tcount_le_length z S) (not_lt.mp hcon)
    have hallS : ∀ p ∈ S, p.1 = z := (tcount_eq_length_iff z S).mp hSeq
    obtain ⟨b, hbS⟩ := lhs_exists_replicate_of_isReduced_of_forall_fst_eq z hSred hallS
    have hssumS : ssum z S = if b then (S.length : ℤ) else -(S.length : ℤ) := by
      rw [hbS, ssum_replicate]
      cases b <;> simp
    have hexp : Multiplicative.ofAdd (ssum z (V ++ S)) = 1 := by
      rw [hVS, ssum_rotate, ← lhs_expSum_mk_eq_ofAdd_ssum z W, ← hr_eq]
      exact hσ
    have hsum0 : ssum z (V ++ S) = 0 := by
      have h1 : Multiplicative.ofAdd (ssum z (V ++ S)) = Multiplicative.ofAdd (0 : ℤ) := by
        simpa using hexp
      exact Multiplicative.ofAdd.injective h1
    rw [ssum_append, hssumS] at hsum0
    have hSV : ssum z V = -(if b then (S.length : ℤ) else -(S.length : ℤ)) := by omega
    have habs : |ssum z V| = (S.length : ℤ) := by
      rw [hSV]
      cases b <;> simp
    have hbound : (S.length : ℤ) ≤ ((tcount z V : ℕ) : ℤ) := by
      have h := lhs_abs_ssum_le_tcount z V
      rwa [habs] at h
    have hSle : S.length ≤ tcount z V := by exact_mod_cast hbound
    have hVlenS : V.length ≤ S.length := by omega
    have hVeq : tcount z V = V.length :=
      le_antisymm (tcount_le_length z V) (le_trans hVlenS hSle)
    have htau : tcount z W = W.length := by rw [hcountW, hVeq, hSeq, hWsum]
    have hr0 : letterCountNot z r = 0 := by rw [hcntR, htau]; simp
    omega
  have hVt : tcount z V ≤ V.length := tcount_le_length z V
  have hSt : tcount z S + 1 ≤ S.length := hSlt
  have hsub : V.length + S.length - (tcount z V + tcount z S)
      = (V.length - tcount z V) + (S.length - tcount z S) := by omega
  rw [hcntV, hcntR, hcountW, hWsum, hsub]
  omega

end Work.OROneRel
