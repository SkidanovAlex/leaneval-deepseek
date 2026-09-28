import Mathlib

namespace Work.HP.BoundaryMain

/-- Fibrewise counting bound: if every vertical fibre `{a | (a,b) ∈ S}` of a set
`S ⊆ α × β` has at most `K` elements, then `S` is at most `K` times as large as the
set of second coordinates it meets.  (When `S` is infinite both `ncard`s vanish;
when `β` is empty `S` is empty.) -/
theorem fiber_ncard_le {α β : Type*} (S : Set (α × β)) (K : ℝ)
    (h : ∀ b : β, (({a : α | (a, b) ∈ S} : Set α).ncard : ℝ) ≤ K) :
    (S.ncard : ℝ) ≤ K * ((S.image Prod.snd).ncard : ℝ) := by
  classical
  by_cases hβ : Nonempty β
  · obtain ⟨b0⟩ := hβ
    have hK : 0 ≤ K := (Nat.cast_nonneg _).trans (h b0)
    rcases Set.finite_or_infinite S with hfin | hinf
    · -- `S` is finite: sum the fibre sizes over the set of second coordinates.
      set T := hfin.toFinset with hTdef
      have hT : (T : Set (α × β)) = S := by rw [hTdef]; exact Set.Finite.coe_toFinset hfin
      have hcardS : S.ncard = T.card := Set.ncard_eq_toFinset_card S hfin
      set I := T.image Prod.snd with hIdef
      have hI : (I : Set β) = S.image Prod.snd := by
        rw [hIdef, Finset.coe_image, hT]
      have hcardI : (S.image Prod.snd).ncard = I.card := by
        rw [← hI, Set.ncard_coe_finset]
      rw [hcardS, hcardI]
      have hmem : Set.MapsTo Prod.snd (T : Set (α × β)) (I : Set β) := by
        intro x hx
        rw [hIdef, Finset.mem_coe, Finset.mem_image]
        exact ⟨x, hx, rfl⟩
      have hfilter : ∀ b ∈ I, ((T.filter (fun x => Prod.snd x = b)).card : ℝ) ≤ K := by
        intro b _
        have hle : (T.filter (fun x => Prod.snd x = b)).card
            ≤ ({a : α | (a, b) ∈ S} : Set α).ncard := by
          rw [← Set.ncard_coe_finset (T.filter (fun x => Prod.snd x = b))]
          refine Set.ncard_le_ncard_of_injOn (fun p : α × β => p.1) ?_ ?_ ?_
          · intro a ha
            simp only [Finset.mem_coe, Finset.mem_filter] at ha
            obtain ⟨haT, ha2⟩ := ha
            have haS : a ∈ S := by rw [← hT]; exact haT
            show (a.1, b) ∈ S
            rw [← ha2, Prod.mk.eta]
            exact haS
          · intro a ha c hc hac
            simp only [Finset.mem_coe, Finset.mem_filter] at ha hc
            exact Prod.ext hac (by rw [ha.2, hc.2])
          · exact (hfin.image Prod.fst).subset (fun i hi => ⟨(i, b), hi, rfl⟩)
        exact le_trans (by exact_mod_cast hle) (h b)
      have hsum_nat : T.card = ∑ b ∈ I, (T.filter (fun x => Prod.snd x = b)).card :=
        Finset.card_eq_sum_card_fiberwise hmem
      have hsum : (T.card : ℝ) = ∑ b ∈ I, ((T.filter (fun x => Prod.snd x = b)).card : ℝ) := by
        rw [hsum_nat]; push_cast; rfl
      calc (T.card : ℝ) = ∑ b ∈ I, ((T.filter (fun x => Prod.snd x = b)).card : ℝ) := hsum
        _ ≤ ∑ b ∈ I, K := Finset.sum_le_sum hfilter
        _ = K * (I.card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    · -- `S` is infinite: both sides are nonnegative, the left one being `0`.
      rw [hinf.ncard]
      simpa using mul_nonneg hK (Nat.cast_nonneg ((S.image Prod.snd).ncard))
  · -- `β` is empty, hence so is `S`.
    have hS : S = ∅ := by
      ext x
      exact ⟨fun hx => (hβ ⟨x.2⟩).elim, fun hx => hx.elim⟩
    rw [hS, Set.image_empty]
    simp

end Work.HP.BoundaryMain
