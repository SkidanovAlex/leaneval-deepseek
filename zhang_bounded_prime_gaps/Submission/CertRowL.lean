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

for `k ∈ {49, 50}` (row signatures among the certificate states), so that the `k = 49` table can
be verified exactly as the `k = 50` one.
-/

namespace Commons.NumberTheory.MaynardSieve

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

theorem unpack_packedRowAt (k : ℕ) (hk : k = 49 ∨ k = 50) (n : MV) (hn : n ∈ certStates)
    (m : MV) (hm : m ∈ certStates) :
    unpack (packedRowAt k n) m = xslots (slotList k n) m := by
  rw [packedRowAt_eq_pack]
  refine unpack_pack (xslots (slotList k n)) ?_ m hm
  rcases hk with rfl | rfl
  · exact xslots_state_lt_49 n hn
  · exact xslots_state_lt_50 n hn

/-- **(F4) at level `k`.** -/
theorem Ssum_eq_packedRowAt (β β' : List ℕ) (k : ℕ) (hk : k = 49 ∨ k = 50)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hdeg : β.sum ≤ 24) (hdeg' : β'.sum ≤ 24) :
    Ssum β β' k = mc k (mult β') * unpack (packedRowAt k (mult β')) (mult β) := by
  have hn : mult β' ∈ certStates :=
    mem_certStates_of_deg _ (by rw [degV_mult_of_support β' hβ']; exact hdeg')
  have hm : mult β ∈ certStates :=
    mem_certStates_of_deg _ (by rw [degV_mult_of_support β hβ]; exact hdeg)
  rw [Ssum_eq_xcoe β β' k hβ hβ', xcoe_eq,
    unpack_packedRowAt k hk (mult β') hn (mult β) hm]

end Commons.NumberTheory.MaynardSieve
