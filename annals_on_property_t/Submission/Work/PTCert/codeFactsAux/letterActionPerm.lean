import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.letterAction
import Submission.Work.PTCert.sigmaGroupFacts

namespace Work.PTCert.codeFactsAux

open Submission.PTCert Submission.RouteB

/-- **Extraction of the letter-action computation of `Work.PTCert.letterAction`** from the
specific element `sigAut p s` built inside that proof, to an arbitrary `p : Equiv.Perm (Fin r)`
whose digits are those of `pc` (`∀ i, (p i).val = pdig pc i.val`) and the sign function
`s i = decide (sbit sc i = 1)`.  This is *literally* the second half of the proof of
`Work.PTCert.letterAction` (copy it), which uses `hvalid` only through
`validPC_pdig_lt` / `validPC_pdig_inj`, and never uses `sc < 2^r`.
Available helpers from `letterAction.lean`: `b1_eq_kindAut`, `actL_eq`, `NB1_eq`, `pairIndex_lt`,
`validPC_pdig_lt`, `validPC_pdig_inj`, `permAut_conj_kindAut`, `tbit_eq_sbit`, and from
`signAutConj.lean`: `signAutConj`; from `pairOfValid`/`pairOfPairIndex`: `pairOfValid`,
`pairOfPairIndex`. -/
theorem letterActionPerm (r pc sc : ℕ) (p : Equiv.Perm (Fin r)) (h : Submission.PTCert.validPC r pc = true)
    (hpiv : ∀ i : Fin r, (p i).val = Submission.PTCert.pdig pc i.val) :
    ∀ k < Submission.PTCert.NB1 r,
      Submission.PTCert.sigAut p (fun i => decide (Submission.PTCert.sbit sc i.val = 1)) *
        Submission.PTCert.b1 r k *
        (Submission.PTCert.sigAut p (fun i => decide (Submission.PTCert.sbit sc i.val = 1)))⁻¹ =
      Submission.PTCert.b1 r (Submission.PTCert.actL r pc sc k) := by
  have hbound : ∀ i, i < r → pdig pc i < r := validPC_pdig_lt r pc h
  have hinj : ∀ i j, i < r → j < r → pdig pc i = pdig pc j → i = j :=
    validPC_pdig_inj r pc h
  set s : Fin r → Bool := fun i => decide (sbit sc i.val = 1) with hs
  have htbit : ∀ i : Fin r, tbit (s i) = sbit sc i.val := fun i => tbit_eq_sbit sc i.val
  intro k hk
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

end Work.PTCert.codeFactsAux
