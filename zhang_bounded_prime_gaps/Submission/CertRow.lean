import Submission.CertPackLem

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

open scoped BigOperators
open Finset

/-!
# The certificate's x-side: bounds and the packed row

`Submission/CertPackLem.lean` proves the extraction lemma (F1) and the correctness of the packed
operations (F2).  Here we
* derive the numeric bound that makes the extraction applicable to the slot lists of the
  certificate (`xslots_slotList_lt`), and
* prove (F3) `unpack (packedRow n) m = xslots (slotList 50 n) m`, hence (F4) the table
  `Ssum β β' 50 = mc 50 (mult β') · unpack (packedRow (mult β')) (mult β)`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-! ## The bound on the slot lists of the certificate -/

theorem mem_hpartL {L : List (Fin 12)} {n : MV} {s : CertSlot} (h : s ∈ hpartL L n) :
    ∃ i : Fin 12, s = CertSlot.H i := by
  induction L with
  | nil => simp [hpartL] at h
  | cons i t ih =>
      rw [hpartL_cons] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨i, (List.mem_replicate.mp h).2⟩
      · exact ih h

theorem hpartL_length (L : List (Fin 12)) (n : MV) :
    (hpartL L n).length = (L.map (fun i : Fin 12 => n i)).sum := by
  induction L with
  | nil => simp [hpartL]
  | cons i t ih =>
      rw [hpartL_cons, List.length_append, List.length_replicate, ih, List.map_cons,
        List.sum_cons]

theorem sum_map_finRange (k : ℕ) (g : Fin k → ℕ) :
    ((List.finRange k).map g).sum = ∑ i, g i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, ih, Fin.sum_univ_succ]
      simp only [Function.comp_apply]

theorem capA_le_capHmax : cap CertSlot.A ≤ capHmax := by
  rw [cap_A, capHmax]
  exact Nat.add_le_add (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero 24))
    (Finset.sum_le_sum (f := fun v : Fin 12 => Nat.factorial (2 * ((v : ℕ) + 1)))
      (g := fun v : Fin 12 => Nat.factorial (2 * ((v : ℕ) + 1) + 24))
      (fun v _ => Nat.factorial_le (by omega)))

theorem slotList_prod_le (n : MV) (hn : ∑ i, n i ≤ 12) :
    ((slotList 50 n).map cap).prod ≤ cap CertSlot.A ^ 38 * capHmax ^ 12 := by
  have hsplit : slotList 50 n
      = List.replicate (50 - ∑ i, n i) CertSlot.A ++ hpartL (List.finRange 12) n := by
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
  have h2 : cap CertSlot.A ^ (50 - ∑ i, n i)
      ≤ cap CertSlot.A ^ 38 * capHmax ^ (12 - ∑ i, n i) := by
    rw [show 50 - ∑ i, n i = 38 + (12 - ∑ i, n i) from by omega, pow_add]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left capA_le_capHmax _)
  refine le_trans (Nat.mul_le_mul_left _ h1) ?_
  refine le_trans (Nat.mul_le_mul_right _ h2) ?_
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hn]

/-- The certificate's slot lists have kernel coefficients below the block size. -/
theorem xslots_slotList_lt (n : MV) (hn : ∑ i, n i ≤ 12) (m : MV) :
    xslots (slotList 50 n) m < 2 ^ BB :=
  lt_of_le_of_lt (le_trans (xslots_le_cap _ _) (slotList_prod_le n hn)) capA_capH_lt

/-! ## The state-side facts about `mult` -/

theorem degV_eq_zero (m : MV) (h : degV m = 0) : m = 0 := by
  funext i
  have hsum : (∑ j : Fin 12, 2 * ((j : ℕ) + 1) * m j) = 0 := h
  have hterm := (Finset.sum_eq_zero_iff.mp hsum) i (Finset.mem_univ i)
  rcases Nat.mul_eq_zero.mp hterm with h1 | h1
  · omega
  · exact h1

theorem mult_cons_even (j : Fin 12) (t : List ℕ) :
    mult (2 * ((j : ℕ) + 1) :: t) = mult t + evec j := by
  funext i
  rw [mult_cons (2 * ((j : ℕ) + 1)) t i, Pi.add_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, evec, Pi.single_eq_same]
    omega
  · rw [if_neg (fun hc => hij (Fin.ext (by omega))), evec, Pi.single_eq_of_ne hij 1,
      add_zero]

theorem sum_evec (j : Fin 12) : ∑ i : Fin 12, evec j i = 1 := by
  rw [Finset.sum_eq_single j]
  · simp [evec]
  · intro b _ hb
    rw [evec, Pi.single_eq_of_ne hb 1]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem sum_mult_of_support (β : List ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    ∑ i : Fin 12, mult β i = β.length := by
  induction β with
  | nil => simp [mult]
  | cons a t ih =>
      obtain ⟨j, hj⟩ := hβ a (by simp)
      have ht : ∀ b ∈ t, ∃ i : Fin 12, b = 2 * ((i : ℕ) + 1) := fun b hb => hβ b (by simp [hb])
      rw [hj, mult_cons_even]
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, sum_evec, ih ht, List.length_cons]

theorem two_mul_length_le_sum (β : List ℕ) (hβ : ∀ a ∈ β, 2 ≤ a) : 2 * β.length ≤ β.sum := by
  induction β with
  | nil => simp
  | cons a t ih =>
      have ht : ∀ b ∈ t, 2 ≤ b := fun b hb => hβ b (by simp [hb])
      have h1 := ih ht
      have h2 := hβ a (by simp)
      rw [List.length_cons, List.sum_cons]
      omega

theorem two_le_of_support {a : ℕ} (h : ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) : 2 ≤ a := by
  obtain ⟨i, rfl⟩ := h
  omega

theorem length_le_of_support (β : List ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) (h : β.sum ≤ 24) :
    β.length ≤ 12 := by
  have h1 := two_mul_length_le_sum β (fun a ha => two_le_of_support (hβ a ha))
  omega

theorem degV_mult_of_support (β : List ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1)) :
    degV (mult β) = β.sum := by
  induction β with
  | nil => simp [mult, degV]
  | cons a t ih =>
      obtain ⟨j, hj⟩ := hβ a (by simp)
      have ht : ∀ b ∈ t, ∃ i : Fin 12, b = 2 * ((i : ℕ) + 1) := fun b hb => hβ b (by simp [hb])
      rw [hj, mult_cons_even, degV_add_single, ih ht, List.sum_cons]
      omega

/-! ## (F3) the packed row computes the slot list -/

theorem classWord_delta (i : Fin 13) :
    classWord (fun m : MV => if m = 0 then 1 else 0) (i : ℕ)
      = if (i : ℕ) = 0 then 1 else 0 := by
  rw [classWord_eq_sum]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi]
    have hset : cset (i : ℕ) = {0} := by
      ext m
      rw [mem_cset, mem_classJ_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hdeg⟩
        exact degV_eq_zero m (by rw [hdeg, hi])
      · rintro rfl
        exact ⟨mem_certStates_of_deg _ (by simp [degV]), by rw [hi]; simp [degV]⟩
    rw [hset, Finset.sum_singleton]
    simp [muVal]
  · rw [if_neg hi]
    refine Finset.sum_eq_zero (fun m hm => ?_)
    have hdeg : degV m = 2 * (i : ℕ) := (mem_classJ_iff.mp (mem_cset.mp hm)).2
    have h0 : m ≠ 0 := by
      intro h
      rw [h] at hdeg
      simp [degV] at hdeg
      omega
    rw [if_neg h0, zero_mul]

theorem W0_eq : W0 = pack (fun m : MV => if m = 0 then 1 else 0) := by
  rw [pack_eq_ofFn]
  have h : (fun i : Fin 13 => classWord (fun m : MV => if m = 0 then 1 else 0) (i : ℕ))
      = fun i : Fin 13 => if (i : ℕ) = 0 then 1 else 0 := funext (fun i => classWord_delta i)
  rw [h]
  unfold W0
  decide

theorem packedPowA_eq (k : ℕ) :
    packedPowA k = pack (xslots (List.replicate k CertSlot.A)) := by
  induction k with
  | zero =>
      have h : pack (xslots (List.replicate 0 CertSlot.A))
          = pack (fun m : MV => if m = 0 then 1 else 0) := rfl
      rw [h]
      exact W0_eq
  | succ k ih =>
      show (packedMulA^[k.succ]) W0 = pack (xslots (List.replicate (k + 1) CertSlot.A))
      rw [Function.iterate_succ_apply',
        show (packedMulA^[k]) W0 = packedPowA k from rfl, ih, packedMulA_pack,
        ← xslots_cons_A_eq, List.replicate_succ]

theorem packedMulH_iterate (w : Fin 12) (j : ℕ) (X : List CertSlot) :
    (packedMulH w)^[j] (pack (xslots X))
      = pack (xslots (List.replicate j (CertSlot.H w) ++ X)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, packedMulH_pack, ← xslots_cons_H_eq,
        List.replicate_succ, List.cons_append]

theorem foldl_eq (L : List (Fin 12)) (n : MV) (X : List CertSlot) :
    L.foldl (fun W w => (packedMulH w)^[n w] W) (pack (xslots X))
      = pack (xslots (hpartL L n ++ X)) := by
  induction L generalizing X with
  | nil => simp [hpartL]
  | cons i t ih =>
      rw [List.foldl_cons, packedMulH_iterate, ih, hpartL_cons, List.append_assoc]
      have hperm : (hpartL t n ++ (List.replicate (n i) (CertSlot.H i) ++ X)).Perm
          (List.replicate (n i) (CertSlot.H i) ++ (hpartL t n ++ X)) :=
        (List.Perm.of_eq (List.append_assoc (hpartL t n)
            (List.replicate (n i) (CertSlot.H i)) X).symm).trans
          (((List.perm_append_comm (l₁ := hpartL t n)
            (l₂ := List.replicate (n i) (CertSlot.H i))).append_right X).trans
            (List.Perm.of_eq (List.append_assoc (List.replicate (n i) (CertSlot.H i))
              (hpartL t n) X)))
      rw [show xslots (hpartL t n ++ (List.replicate (n i) (CertSlot.H i) ++ X))
          = xslots (List.replicate (n i) (CertSlot.H i) ++ (hpartL t n ++ X)) from
        xslots_perm hperm]

theorem packedRow_eq_pack (n : MV) :
    packedRow n = pack (xslots (slotList 50 n)) := by
  have h1 : packedRow n = (List.finRange 12).foldl (fun W w => (packedMulH w)^[n w] W)
      (pack (xslots (List.replicate (50 - ∑ w : Fin 12, n w) CertSlot.A))) := by
    unfold packedRow
    rw [packedPowA_eq]
  rw [h1, foldl_eq]
  have hx : xslots (hpartL (List.finRange 12) n
        ++ List.replicate (50 - ∑ w : Fin 12, n w) CertSlot.A)
      = xslots (slotList 50 n) := by
    refine xslots_perm ?_
    rw [slotList_def, Hpart_eq_hpartL]
    exact List.perm_append_comm.symm
  rw [hx]

theorem unpack_packedRow (n : MV) (hn : ∑ i, n i ≤ 12) (m : MV) (hm : m ∈ certStates) :
    unpack (packedRow n) m = xslots (slotList 50 n) m := by
  rw [packedRow_eq_pack]
  exact unpack_pack (xslots (slotList 50 n)) (xslots_slotList_lt n hn) m hm

/-! ## (F4) the `Ssum` table -/

theorem xcoe_eq (k : ℕ) (n m : MV) : xcoe k n m = mc k n * xslots (slotList k n) m := by
  rw [← slabLevel_eq_xcoe k m n, slabLevel_eq_mc k m n]
  rfl

/-- **(F4)** The factorisation of `Ssum` evaluated at `k = 50` by the packed DP. -/
theorem Ssum_50_eq (β β' : List ℕ)
    (hβ : ∀ a ∈ β, ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hβ' : ∀ a ∈ β', ∃ i : Fin 12, a = 2 * ((i : ℕ) + 1))
    (hdeg : β.sum ≤ 24) (hdeg' : β'.sum ≤ 24) :
    Ssum β β' 50 = mc 50 (mult β') * unpack (packedRow (mult β')) (mult β) := by
  have hn : ∑ i : Fin 12, mult β' i ≤ 12 := by
    rw [sum_mult_of_support β' hβ']
    exact length_le_of_support β' hβ' hdeg'
  have hm : mult β ∈ certStates :=
    mem_certStates_of_deg _ (by rw [degV_mult_of_support β hβ]; exact hdeg)
  rw [Ssum_eq_xcoe β β' 50 hβ hβ', xcoe_eq, unpack_packedRow (mult β') hn (mult β) hm]

end Commons.NumberTheory.MaynardSieve
