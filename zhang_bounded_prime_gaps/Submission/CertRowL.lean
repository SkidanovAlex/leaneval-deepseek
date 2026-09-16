import Submission.CertRow

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

open scoped BigOperators
open Finset

/-!
# The `x`-side row at level `k` (for the `J`-half of the certificate)

`Submission/CertRow.lean` proves, at level `50`,
`Ssum β β' 50 = mc 50 (mult β') · unpack (packedRow (mult β')) (mult β)`.  The `J`-half of the
certificate needs the *same* factorisation at level `49`.  Here we generalise the packed row to
`packedRowAt k n` (the packed word of `A^(k-|n|) · ∏_w h_w^(n_w)`) and prove

  `Ssum β β' k = mc k (mult β') · unpack (packedRowAt k (mult β')) (mult β)`

for every `k ≤ 50` (with `Σ n ≤ 12`), so that the `k = 49` table can be verified exactly as the
`k = 50` one.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The bound on the slot list at level `k ≤ 50`. -/
theorem slotList_prod_le' (k : ℕ) (hk : k ≤ 50) (n : MV) (hn : ∑ i, n i ≤ 12) :
    ((slotList k n).map cap).prod ≤ cap CertSlot.A ^ 38 * capHmax ^ 12 := by
  have hsplit : slotList k n = List.replicate (k - ∑ i, n i) CertSlot.A ++ hpartL (List.finRange 12) n := by
    rw [slotList_def, Hpart_eq_hpartL]
  rw [hsplit, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]
  have h1 : ((hpartL (List.finRange 12) n).map cap).prod ≤ capHmax ^ (∑ i, n i) := by
    have hlen : (hpartL (List.finRange 12) n).length = ∑ i, n i := by
      rw [hpartL_length, sum_map_finRange]
    calc ((hpartL (List.finRange 12) n).map cap).prod
        ≤ capHmax ^ ((hpartL (List.finRange 12) n).map cap).length :=
          List.prod_le_pow_card _ _ (fun x hx => by
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
            obtain ⟨i, rfl⟩ := mem_hpartL hs
            exact capH_le i)
      _ = capHmax ^ (∑ i, n i) := by rw [List.length_map, hlen]
  have hcapA : 1 ≤ cap CertSlot.A := by rw [cap_A]; exact Nat.le_add_right 1 _
  have h2 : cap CertSlot.A ^ (k - ∑ i, n i)
      ≤ cap CertSlot.A ^ 38 * capHmax ^ (12 - ∑ i, n i) := by
    calc cap CertSlot.A ^ (k - ∑ i, n i)
        ≤ cap CertSlot.A ^ (38 + (12 - ∑ i, n i)) :=
          Nat.pow_le_pow_right hcapA (by omega)
      _ = cap CertSlot.A ^ 38 * cap CertSlot.A ^ (12 - ∑ i, n i) := by rw [pow_add]
      _ ≤ cap CertSlot.A ^ 38 * capHmax ^ (12 - ∑ i, n i) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left capA_le_capHmax _)
  refine le_trans (Nat.mul_le_mul_left _ h1) ?_
  refine le_trans (Nat.mul_le_mul_right _ h2) ?_
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

/-- The certificate's slot lists at level `k ≤ 50` have kernel coefficients below the block
size. -/
theorem xslots_slotList_lt' (k : ℕ) (hk : k ≤ 50) (n : MV) (hn : ∑ i, n i ≤ 12) (m : MV) :
    xslots (slotList k n) m < 2 ^ BB :=
  lt_of_le_of_lt (le_trans (xslots_le_cap _ _) (slotList_prod_le' k hk n hn)) capA_capH_lt

/-- The packed word of `A^(k-|n|) · ∏_w h_w^(n_w)`. -/
def packedRowAt (k : ℕ) (n : MV) : List ℕ :=
  (List.finRange 12).foldl (fun W w => (packedMulH w)^[n w] W)
    (packedPowA (k - ∑ w : Fin 12, n w))

theorem packedRowAt_eq_pack (k : ℕ) (n : MV) :
    packedRowAt k n = pack (xslots (slotList k n)) := by
  have h1 : packedRowAt k n = (List.finRange 12).foldl (fun W w => (packedMulH w)^[n w] W)
      (pack (xslots (List.replicate (k - ∑ w : Fin 12, n w) CertSlot.A))) := by
    unfold packedRowAt
    rw [packedPowA_eq]
  rw [h1, foldl_eq]
  have hx : xslots (hpartL (List.finRange 12) n
        ++ List.replicate (k - ∑ w : Fin 12, n w) CertSlot.A)
      = xslots (slotList k n) := by
    refine xslots_perm ?_
    rw [slotList_def, Hpart_eq_hpartL]
    exact List.perm_append_comm.symm
  rw [hx]

theorem unpack_packedRowAt (k : ℕ) (hk : k ≤ 50) (n : MV) (hn : ∑ i, n i ≤ 12) (m : MV)
    (hm : m ∈ certStates) :
    unpack (packedRowAt k n) m = xslots (slotList k n) m := by
  rw [packedRowAt_eq_pack]
  exact unpack_pack (xslots (slotList k n)) (xslots_slotList_lt' k hk n hn) m hm

/-- **(F4) at level `k`.** -/
theorem Ssum_eq_packedRowAt (β β' : List ℕ) (k : ℕ) (hk : k ≤ 50)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hdeg : β.sum ≤ 24) (hdeg' : β'.sum ≤ 24) :
    Ssum β β' k = mc k (mult β') * unpack (packedRowAt k (mult β')) (mult β) := by
  have hn : ∑ i : Fin 12, mult β' i ≤ 12 := by
    rw [sum_mult_of_support β' hβ']
    exact length_le_of_support β' hβ' hdeg'
  have hm : mult β ∈ certStates :=
    mem_certStates_of_deg _ (by rw [degV_mult_of_support β hβ]; exact hdeg)
  rw [Ssum_eq_xcoe β β' k hβ hβ', xcoe_eq,
    unpack_packedRowAt k hk (mult β') hn (mult β) hm]

end Commons.NumberTheory.MaynardSieve
