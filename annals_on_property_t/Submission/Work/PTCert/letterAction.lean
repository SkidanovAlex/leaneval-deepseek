import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.PTCert.letterDefs
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.RouteB.TransvectionEquiv
import Submission.Work.RouteB.FreeGroupAutDecEq
import Submission.Work.PTCert.pairOfValid
import Submission.Work.PTCert.pairOfPairIndex
import Submission.Work.PTCert.signAutConj

/-!
# Letter action of the signed permutations on `SAut(F_r)`

Proof of `Submission.PTCert.LetterAction r`.
-/

namespace Work.PTCert

open Submission.PTCert Submission.FreeGroupAut Submission.RouteB
open FreeGroup

/-! ### Bit arithmetic of `invL = (k-1) ^^^ 1 + 1` -/

lemma xor_one_div_four (m : ℕ) : (m ^^^ 1) / 4 = m / 4 := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [Nat.xor_one_of_even hm]
    obtain ⟨t, ht⟩ := hm
    omega
  · rw [Nat.xor_one_of_odd hm]
    obtain ⟨t, ht⟩ := hm
    omega

lemma xor_one_mod_four (m : ℕ) : (m ^^^ 1) % 4 = (m % 4) ^^^ 1 := by
  have heven : ∀ m, Even m → Even (m % 4) := by
    intro m hm
    rw [Nat.even_iff] at hm ⊢
    rw [Nat.mod_mod_of_dvd m (by norm_num : 2 ∣ 4)]
    exact hm
  rcases Nat.even_or_odd m with hm | hm
  · rw [Nat.xor_one_of_even hm, Nat.xor_one_of_even (heven m hm)]
    obtain ⟨t, ht⟩ := hm
    omega
  · have hodd : Odd (m % 4) := by
      rw [← Nat.not_even_iff_odd, Nat.even_iff, Nat.mod_mod_of_dvd m (by norm_num : 2 ∣ 4)]
      rw [Nat.odd_iff] at hm
      omega
    rw [Nat.xor_one_of_odd hm, Nat.xor_one_of_odd hodd]
    obtain ⟨t, ht⟩ := hm
    omega

/-! ### Conjugation by `permAut p` -/

lemma permAut_conj_kindAut {r : ℕ} (p : Equiv.Perm (Fin r)) (i j : Fin r) (hij : i ≠ j)
    (b0 b1 : ℕ) :
    Submission.RouteB.permAut p * Submission.PTCert.kindAutNat i j hij b0 b1 *
        (Submission.RouteB.permAut p)⁻¹ =
      Submission.PTCert.kindAutNat (p i) (p j) (fun h => hij (p.injective h)) b0 b1 := by
  by_cases h0 : b0 = 1
  · subst h0
    by_cases h1 : b1 = 1
    · subst h1
      rw [Submission.PTCert.kindAutNat_one_one, Submission.PTCert.kindAutNat_one_one]
      exact Submission.RouteB.permAut_conj_lamNeg p i j hij
    · have L : Submission.PTCert.kindAutNat i j hij 1 b1 = lam i j hij := by
        rw [Submission.PTCert.kindAutNat, if_pos rfl, if_neg h1]
      have R : Submission.PTCert.kindAutNat (p i) (p j) (fun h => hij (p.injective h)) 1 b1
          = lam (p i) (p j) (fun h => hij (p.injective h)) := by
        rw [Submission.PTCert.kindAutNat, if_pos rfl, if_neg h1]
      rw [L, R]; exact Submission.RouteB.permAut_conj_lam p i j hij
  · by_cases h1 : b1 = 1
    · subst h1
      have L : Submission.PTCert.kindAutNat i j hij b0 1 = rhoNeg i j hij := by
        rw [Submission.PTCert.kindAutNat, if_neg h0, if_pos rfl]
      have R : Submission.PTCert.kindAutNat (p i) (p j) (fun h => hij (p.injective h)) b0 1
          = rhoNeg (p i) (p j) (fun h => hij (p.injective h)) := by
        rw [Submission.PTCert.kindAutNat, if_neg h0, if_pos rfl]
      rw [L, R]; exact Submission.RouteB.permAut_conj_rhoNeg p i j hij
    · have L : Submission.PTCert.kindAutNat i j hij b0 b1 = rho i j hij := by
        rw [Submission.PTCert.kindAutNat, if_neg h0, if_neg h1]
      have R : Submission.PTCert.kindAutNat (p i) (p j) (fun h => hij (p.injective h)) b0 b1
          = rho (p i) (p j) (fun h => hij (p.injective h)) := by
        rw [Submission.PTCert.kindAutNat, if_neg h0, if_neg h1]
      rw [L, R]; exact Submission.RouteB.permAut_conj_rho p i j hij

lemma kindAutNat_proof_irrel {r : ℕ} (i j : Fin r) (h1 h2 : i ≠ j) (b0 b1 : ℕ) :
    Submission.PTCert.kindAutNat i j h1 b0 b1 =
      Submission.PTCert.kindAutNat i j h2 b0 b1 := by
  simp only [Submission.PTCert.kindAutNat]

/-! ### Inversion of `kindAutNat` -/

lemma kindAutNat_inv {r : ℕ} (i j : Fin r) (hij : i ≠ j) (b0 b1 : ℕ) (hb0 : b0 < 2)
    (hb1 : b1 < 2) :
    (Submission.PTCert.kindAutNat i j hij b0 b1)⁻¹ =
      Submission.PTCert.kindAutNat i j hij b0 (b1 ^^^ 1) := by
  rcases (by omega : b0 = 0 ∨ b0 = 1) with h0 | h0 <;>
    rcases (by omega : b1 = 0 ∨ b1 = 1) with h1 | h1 <;>
    subst h0 <;> subst h1
  · rw [Submission.PTCert.kindAutNat_zero_zero, Nat.zero_xor]
    exact rho_inv_eq i j hij
  · rw [Submission.PTCert.kindAutNat_zero_one, Nat.xor_self, Submission.PTCert.kindAutNat_zero_zero]
    exact rhoNeg_inv_eq i j hij
  · rw [Submission.PTCert.kindAutNat_one_zero, Nat.zero_xor, Submission.PTCert.kindAutNat_one_one]
    exact lam_inv_eq i j hij
  · rw [Submission.PTCert.kindAutNat_one_one, Nat.xor_self,
      Submission.PTCert.kindAutNat_one_zero]
    exact lamNeg_inv_eq i j hij

/-! ### Unfolding `b1` and `actL` -/

lemma b1_eq_kindAut (r q kind : ℕ) (hk : kind < 4) (i j : Fin r) (hij : i ≠ j)
    (hpair : pairOf r q = (i.val, j.val))
    (hbound : 1 + 4*q + kind < NB1 r) :
    b1 r (1 + 4*q + kind) = Submission.PTCert.kindAutNat i j hij (kind/2) (kind%2) := by
  have hk0 : ¬ (1 + 4 * q + kind = 0) := by omega
  have hsub : 1 + 4 * q + kind - 1 = 4 * q + kind := by omega
  have hq : (4*q + kind)/4 = q := by
    rw [Nat.mul_add_div (by norm_num : 0 < 4), Nat.div_eq_of_lt hk, Nat.add_zero]
  have hm : (4*q + kind)%4 = kind := by
    rw [show 4*q + kind = kind + 4*q by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  simp only [b1, hsub, hq, hm, hpair]
  rw [dif_neg hk0]
  have hcond : (↑i : ℕ) < r ∧ (↑j : ℕ) < r ∧ (↑i : ℕ) ≠ ↑j ∧ 1 + 4 * q + kind < NB1 r :=
    ⟨i.isLt, j.isLt, fun h => hij (Fin.ext h), hbound⟩
  rw [dif_pos hcond]
  interval_cases kind <;> simp only [Submission.PTCert.kindAutNat, reduceIte] <;> norm_num

lemma actL_eq (r pc sc k : ℕ) (hk0 : k ≠ 0) :
    actL r pc sc k =
      1 + 4 * pairIndex r (pdig pc ((pairOf r ((k-1)/4)).1))
        (pdig pc ((pairOf r ((k-1)/4)).2))
        + 2 * ((((k-1)%4)/2) ^^^ (sbit sc (pdig pc ((pairOf r ((k-1)/4)).1))))
        + ((((k-1)%4)%2) ^^^ (sbit sc (pdig pc ((pairOf r ((k-1)/4)).1)))
            ^^^ (sbit sc (pdig pc ((pairOf r ((k-1)/4)).2)))) := by
  rw [actL, if_neg hk0]
  simp only [pairIndex]

/-! ### Arithmetic of the letter indices -/

lemma NB1_eq (r : ℕ) : NB1 r = 1 + 4 * (r * (r - 1)) := by
  have : NB1 r = 1 + 4 * r * (r - 1) := rfl
  rw [this]; ring

lemma pairIndex_lt (r i j : ℕ) (hr : 2 ≤ r) (hi : i < r) (hj : j < r) (hij : i ≠ j) :
    pairIndex r i j < r * (r - 1) := by
  rw [pairIndex]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg (by omega : ¬ j < i)]
    have hi' : i + 1 ≤ r := by omega
    have hj' : j - 1 < r - 1 := by omega
    calc i * (r - 1) + (j - 1) < i * (r - 1) + (r - 1) := by omega
      _ = (i + 1) * (r - 1) := by ring
      _ ≤ r * (r - 1) := Nat.mul_le_mul_right (r - 1) hi'
  · exact absurd h hij
  · rw [if_pos h]
    have hi' : i ≤ r - 1 := by omega
    calc i * (r - 1) + j < i * (r - 1) + i := by omega
      _ = i * r := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ r)]
      _ ≤ (r - 1) * r := Nat.mul_le_mul_right r hi'
      _ = r * (r - 1) := by ring

lemma invL_lt (r k : ℕ) (hk : k < NB1 r) : invL k < NB1 r := by
  by_cases hk0 : k = 0
  · subst hk0; simp [invL, NB1]
  · have hkpos : 1 ≤ k := by omega
    rw [invL, if_neg hk0]
    rw [NB1_eq] at hk ⊢
    have hkm : k - 1 < 4 * (r * (r - 1)) := by omega
    have hx : (k - 1) ^^^ 1 < 4 * (r * (r - 1)) := by
      rcases Nat.even_or_odd (k - 1) with he | ho
      · rw [Nat.xor_one_of_even he]
        obtain ⟨t, ht⟩ := he
        omega
      · rw [Nat.xor_one_of_odd ho]
        obtain ⟨t, ht⟩ := ho
        omega
    omega

/-! ### Part 1: the letters invert through `invL` -/

lemma b1_inv (r : ℕ) : ∀ k < NB1 r, (b1 r k)⁻¹ = b1 r (invL k) := by
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    rw [b1, dif_pos rfl, invL, if_pos rfl]
    exact inv_one
  · have hkpos : 1 ≤ k := by omega
    have hr2 : 2 ≤ r := by
      by_contra h
      have h1 : r = 0 ∨ r = 1 := by omega
      rcases h1 with h1 | h1 <;> subst h1 <;> simp [NB1] at hk <;> omega
    have hqlt : (k - 1) / 4 < r * (r - 1) := by
      rw [NB1_eq] at hk
      apply Nat.div_lt_of_lt_mul
      omega
    obtain ⟨hi, hj, hij⟩ := pairOfValid r ((k - 1) / 4) hr2 hqlt
    let i : Fin r := ⟨(pairOf r ((k - 1) / 4)).1, hi⟩
    let j : Fin r := ⟨(pairOf r ((k - 1) / 4)).2, hj⟩
    have hij' : i ≠ j := fun h => hij (congrArg Fin.val h)
    have hpair : pairOf r ((k - 1) / 4) = (i.val, j.val) := rfl
    have hkind : (k - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hb0 : ((k - 1) % 4) / 2 < 2 := by omega
    have hb1 : ((k - 1) % 4) % 2 < 2 := by omega
    have hthis : k = 1 + 4 * ((k - 1) / 4) + (k - 1) % 4 := by
      have := Nat.div_add_mod (k - 1) 4
      omega
    have hb1k : b1 r k = Submission.PTCert.kindAutNat i j hij' (((k - 1) % 4) / 2)
        (((k - 1) % 4) % 2) := by
      conv_lhs => rw [hthis]
      exact b1_eq_kindAut r ((k - 1) / 4) ((k - 1) % 4) hkind i j hij' hpair
        (by rw [← hthis]; exact hk)
    have hinv_eq : invL k = 1 + 4 * ((k - 1) / 4) + (((k - 1) % 4) ^^^ 1) := by
      rw [invL, if_neg hk0]
      have h1 : ((k - 1) ^^^ 1) / 4 = (k - 1) / 4 := xor_one_div_four (k - 1)
      have h2 : ((k - 1) ^^^ 1) % 4 = ((k - 1) % 4) ^^^ 1 := xor_one_mod_four (k - 1)
      have := Nat.div_add_mod ((k - 1) ^^^ 1) 4
      omega
    have hk1 : (((k - 1) % 4) ^^^ 1) / 2 = ((k - 1) % 4) / 2 := by
      interval_cases (k - 1) % 4 <;> decide
    have hk2 : (((k - 1) % 4) ^^^ 1) % 2 = (((k - 1) % 4) % 2) ^^^ 1 := by
      interval_cases (k - 1) % 4 <;> decide
    have hkind1 : ((k - 1) % 4 ^^^ 1) < 4 := by
      simpa using Nat.xor_lt_two_pow (n := 2) hkind (by norm_num : (1:ℕ) < 4)
    have hb1inv : b1 r (invL k) =
        Submission.PTCert.kindAutNat i j hij' (((k - 1) % 4) / 2)
          ((((k - 1) % 4) % 2) ^^^ 1) := by
      rw [hinv_eq]
      rw [b1_eq_kindAut r ((k - 1) / 4) (((k - 1) % 4) ^^^ 1) hkind1 i j hij' hpair
        (by rw [← hinv_eq]; exact invL_lt r k hk)]
      rw [hk1, hk2]
    rw [hb1k, hb1inv]
    exact kindAutNat_inv i j hij' (((k - 1) % 4) / 2) (((k - 1) % 4) % 2) hb0 hb1

/-! ### Valid permutation codes -/

lemma validPC_pdig_lt (r pc : ℕ) (h : validPC r pc = true) :
    ∀ i, i < r → pdig pc i < r := by
  intro i hi
  rw [validPC, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 := List.all_eq_true.mp h.1.1 i (List.mem_range.mpr hi)
  simpa using h1

lemma validPC_pdig_inj (r pc : ℕ) (h : validPC r pc = true) :
    ∀ i j, i < r → j < r → pdig pc i = pdig pc j → i = j := by
  intro i j hi hj heq
  rw [validPC, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 := List.all_eq_true.mp h.1.2 i (List.mem_range.mpr hi)
  have h2 := List.all_eq_true.mp h1 j (List.mem_range.mpr hj)
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · simpa using h2
  · exact absurd heq (by simpa using h2)

/-! ### Part 2: the letter action -/

def tbit (b : Bool) : ℕ := if b then 1 else 0

lemma tbit_eq_sbit (sc i : ℕ) :
    tbit (decide (sbit sc i = 1)) = sbit sc i := by
  have h2 : sbit sc i < 2 := Nat.mod_lt _ (by norm_num)
  by_cases h : sbit sc i = 1
  · simp [tbit, h]
  · have h0 : sbit sc i = 0 := by omega
    simp [tbit, h0]

theorem letterAction (r : ℕ) : LetterAction r := by
  refine ⟨b1_inv r, ?_⟩
  intro pc sc hvalid hsc
  have hbound : ∀ i, i < r → pdig pc i < r := validPC_pdig_lt r pc hvalid
  have hinj : ∀ i j, i < r → j < r → pdig pc i = pdig pc j → i = j :=
    validPC_pdig_inj r pc hvalid
  let f : Fin r → Fin r := fun i => ⟨pdig pc i.val, hbound i.val i.isLt⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    exact hinj a.val b.val a.isLt b.isLt (congrArg Fin.val hab)
  let p : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  let s : Fin r → Bool := fun i => decide (sbit sc i.val = 1)
  have hpiv : ∀ i : Fin r, (p i).val = pdig pc i.val := fun i => rfl
  have htbit : ∀ i : Fin r, tbit (s i) = sbit sc i.val := fun i => tbit_eq_sbit sc i.val
  refine ⟨sigAut p s, ?_, ?_⟩
  · show sigAut p s ∈ Submission.PTCert.SigmaSet r
    rw [Submission.PTCert.SigmaSet]
    exact Finset.mem_image.mpr ⟨(p, s), Finset.mem_univ _, rfl⟩
  · intro k hk
    rcases eq_or_ne k 0 with hk0 | hk0
    · subst hk0
      simp [b1, actL]
    · have hkpos : 1 ≤ k := by omega
      have hr2 : 2 ≤ r := by
        by_contra h
        have h1 : r = 0 ∨ r = 1 := by omega
        rcases h1 with h1 | h1 <;> subst h1 <;> simp [NB1] at hk <;> omega
      have hqlt : (k - 1) / 4 < r * (r - 1) := by
        rw [NB1_eq] at hk
        apply Nat.div_lt_of_lt_mul
        omega
      obtain ⟨hi, hj, hij⟩ := pairOfValid r ((k - 1) / 4) hr2 hqlt
      let i : Fin r := ⟨(pairOf r ((k - 1) / 4)).1, hi⟩
      let j : Fin r := ⟨(pairOf r ((k - 1) / 4)).2, hj⟩
      have hij' : i ≠ j := fun h => hij (congrArg Fin.val h)
      have hpair : pairOf r ((k - 1) / 4) = (i.val, j.val) := rfl
      have hkind : (k - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have hthis : k = 1 + 4 * ((k - 1) / 4) + (k - 1) % 4 := by
        have := Nat.div_add_mod (k - 1) 4
        omega
      -- the letter `k`
      have hb1k : b1 r k = Submission.PTCert.kindAutNat i j hij' (((k - 1) % 4) / 2)
          (((k - 1) % 4) % 2) := by
        conv_lhs => rw [hthis]
        exact b1_eq_kindAut r ((k - 1) / 4) ((k - 1) % 4) hkind i j hij' hpair
          (by rw [← hthis]; exact hk)
      -- `p i`, `p j`
      have hpi_lt : pdig pc i.val < r := hbound i.val i.isLt
      have hpj_lt : pdig pc j.val < r := hbound j.val j.isLt
      have hpij_val : pdig pc i.val ≠ pdig pc j.val :=
        fun h => hij' (Fin.ext (hinj i.val j.val i.isLt j.isLt h))
      have hpij : p i ≠ p j := fun h => hij' (p.injective h)
      -- abbreviation for the re-encoded pair
      set P : ℕ := pairIndex r (pdig pc i.val) (pdig pc j.val) with hP
      set L : ℕ := (((k - 1) % 4) / 2) ^^^ (sbit sc (pdig pc i.val)) with hL
      set N : ℕ := (((k - 1) % 4) % 2) ^^^ (sbit sc (pdig pc i.val)) ^^^
        (sbit sc (pdig pc j.val)) with hN
      set K' : ℕ := 2 * L + N with hK'
      have hL_lt : L < 2 := by
        rw [hL]
        exact Nat.xor_lt_two_pow (n := 1) (by omega) (Nat.mod_lt _ (by norm_num))
      have hN_lt : N < 2 := by
        rw [hN]
        exact Nat.xor_lt_two_pow (n := 1)
          (Nat.xor_lt_two_pow (n := 1) (by omega) (Nat.mod_lt _ (by norm_num)))
          (Nat.mod_lt _ (by norm_num))
      have hP_lt : P < r * (r - 1) := by
        rw [hP]
        exact pairIndex_lt r (pdig pc i.val) (pdig pc j.val) hr2 hpi_lt hpj_lt hpij_val
      have hK'_lt : K' < 4 := by rw [hK']; omega
      have hbound' : 1 + 4 * P + K' < NB1 r := by
        rw [hK', NB1_eq]; omega
      -- unfolding of actL
      have hactL : actL r pc sc k = 1 + 4 * P + K' := by
        rw [actL_eq r pc sc k hk0, hpair]
        simp only [Prod.fst, Prod.snd]
        rw [← hP, ← hL, ← hN, hK']
        ring
      -- unfolding of b1 at actL
      have hpairP : pairOf r P = ((p i).val, (p j).val) := by
        rw [hP, hpiv i, hpiv j]
        exact pairOfPairIndex r (pdig pc i.val) (pdig pc j.val) hr2 hpi_lt hpj_lt hpij_val
      have hb_actL : b1 r (actL r pc sc k) =
          Submission.PTCert.kindAutNat (p i) (p j) hpij (K' / 2) (K' % 2) := by
        rw [hactL]
        exact b1_eq_kindAut r P K' hK'_lt (p i) (p j) hpij hpairP hbound'
      -- conjugation, step 1: permAut
      have hperm : Submission.RouteB.permAut p * b1 r k * (Submission.RouteB.permAut p)⁻¹ =
          Submission.PTCert.kindAutNat (p i) (p j) hpij (((k - 1) % 4) / 2)
            (((k - 1) % 4) % 2) := by
        rw [hb1k, permAut_conj_kindAut p i j hij']
      -- conjugation, step 2: signAut
      have htbit_i : tbit (s (p i)) = sbit sc (pdig pc i.val) := by
        rw [← hpiv i]; exact htbit (p i)
      have htbit_j : tbit (s (p j)) = sbit sc (pdig pc j.val) := by
        rw [← hpiv j]; exact htbit (p j)
      have hsign : signAut s * Submission.PTCert.kindAutNat (p i) (p j) hpij
            (((k - 1) % 4) / 2) (((k - 1) % 4) % 2) * (signAut s)⁻¹ =
          Submission.PTCert.kindAutNat (p i) (p j) hpij
            ((((k - 1) % 4) / 2) ^^^ tbit (s (p i)))
            ((((k - 1) % 4) % 2) ^^^ tbit (s (p i)) ^^^ tbit (s (p j))) := by
        rw [signAutConj r s (p i) (p j) hpij (((k - 1) % 4) / 2) (((k - 1) % 4) % 2)
          (by omega) (by omega)]
        rfl
      -- the two bit equalities
      have hb0eq : (((k - 1) % 4) / 2) ^^^ tbit (s (p i)) = K' / 2 := by
        rw [htbit_i, ← hL, hK']; omega
      have hb1eq : (((k - 1) % 4) % 2) ^^^ tbit (s (p i)) ^^^ tbit (s (p j)) = K' % 2 := by
        rw [htbit_i, htbit_j, ← hN, hK']; omega
      -- assemble
      rw [sigAut]
      rw [show (signAut s * Submission.RouteB.permAut p) * b1 r k *
            (signAut s * Submission.RouteB.permAut p)⁻¹
          = signAut s * (Submission.RouteB.permAut p * b1 r k *
              (Submission.RouteB.permAut p)⁻¹) * (signAut s)⁻¹ by group]
      rw [hperm, hsign, hb_actL, hb0eq, hb1eq]

end Work.PTCert
