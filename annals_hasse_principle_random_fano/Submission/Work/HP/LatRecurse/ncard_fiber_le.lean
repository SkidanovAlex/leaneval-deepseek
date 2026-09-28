import Mathlib

namespace Work.HP.LatRecurse

/-- If every vertical fibre `{a | (a,b) ∈ S}` has at most `K` elements then
`S` is at most `K` times as large as the set of second coordinates it meets. -/
theorem ncard_fiber_le {β : Type*} (S : Set (ℤ × β)) (K : ℕ)
    (h : ∀ b : β, {a : ℤ | (a, b) ∈ S}.ncard ≤ K) :
    S.ncard ≤ K * (S.image Prod.snd).ncard := by
  classical
  rcases Set.finite_or_infinite S with hfin | hinf
  · set s := hfin.toFinset with hs_def
    have hscoe : (↑s : Set (ℤ × β)) = S := by
      rw [hs_def]; exact Set.Finite.coe_toFinset hfin
    have hSncard : S.ncard = s.card := Set.ncard_eq_toFinset_card S hfin
    have hcoe : ((Finset.image Prod.snd s : Finset β) : Set β) = S.image Prod.snd := by
      rw [Finset.coe_image, hscoe]
    have himg : (S.image Prod.snd).ncard = (Finset.image Prod.snd s).card := by
      rw [← Set.ncard_coe_finset (Finset.image Prod.snd s), hcoe]
    rw [hSncard, himg]
    apply Finset.card_le_mul_card_image
    intro b _
    have hle : (s.filter (fun a => Prod.snd a = b)).card ≤ ({a : ℤ | (a, b) ∈ S}).ncard := by
      rw [← Set.ncard_coe_finset (s.filter (fun a => Prod.snd a = b))]
      refine Set.ncard_le_ncard_of_injOn (fun p : ℤ × β => p.1) ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter] at ha
        obtain ⟨haS, hab⟩ := ha
        rw [← hab]
        exact (Set.Finite.mem_toFinset hfin).mp (by rwa [hs_def] at haS)
      · intro a ha c hc hac
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hc
        exact Prod.ext hac (by rw [ha.2, hc.2])
      · exact (hfin.image Prod.fst).subset (fun i hi => ⟨(i, b), hi, rfl⟩)
    exact le_trans hle (h b)
  · rw [hinf.ncard]
    exact Nat.zero_le _

end Work.HP.LatRecurse
