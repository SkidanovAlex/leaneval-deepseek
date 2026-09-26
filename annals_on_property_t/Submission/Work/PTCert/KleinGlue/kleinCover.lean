import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.kleinSem
import Submission.Work.PTCert.codeFactsAux.pcFacts
import Submission.Work.PTCert.codeFactsAux.letterActionPerm
import Submission.Work.PTCert.codeFactsAux.actLBound
import Submission.Work.PTCert.sigmaGroupFacts

/-!
# PTCert — Klein cover clause: every `χ_{S_k}`-admissible `N`-representative is a Klein translate
of a listed representative

This proves the *cover* hypothesis of the second Fourier level (`KleinLevel`) of the rank-5
certificate for the base characters `S_k = {0, …, k-1}`, `k ≤ 5`.

The relevant data is the family `KleinSem k` (the plain meaning of the kernel checks
`kltab_ok k`, `klcov_ok k_*`, `kldist_ok k`, `klcols_ok k`, proved in
`Submission.Work.PTCert.kleinSem`).  Its `kw`-clause says, for every `N`-representative number
`t < 611`:

* either `kw t = 0`, and then the sign code `vw t` fixes `rep t` while having character `-1`
  (a *vanishing witness*, so `rep t` is not admissible);
* or `kw t ≠ 0`, and then `rep t` is admissible and equals the `N`-representative of
  `κ_b · rep_{ks[(kw t - 1)/4]}`, where `b = (kw t - 1) % 4`.

Translating along `EI`/`repE` and the letter-table formula of `ActSetup` gives the statement.

The main auxiliary input is `tabOfKleinPermAut`: the kernel table `klT.get b` is a letter table of
the permutation automorphism `permAut (kleinPerm k b)`.
-/

namespace Work.PTCert.KleinGlue

open Submission.PTCert Submission.PTCert.G Submission.RouteB

set_option autoImplicit false

/-- `bval` is onto `{0,1,2,3}`: the Klein element `b' = zOfSc b` has `bval b' = b`. -/
private lemma bval_zOfSc (b : ℕ) (hb : b < 4) : bval (zOfSc (m := 2) b) = b := by
  have h0 : (zOfSc (m := 2) b 0).val = b % 2 := by
    show ((sbit b (0 : Fin 2).val : ℕ) : ZMod 2).val = b % 2
    rw [ZMod.val_natCast]
    simp [sbit]
  have h1 : (zOfSc (m := 2) b 1).val = (b / 2) % 2 := by
    show ((sbit b (1 : Fin 2).val : ℕ) : ZMod 2).val = (b / 2) % 2
    rw [ZMod.val_natCast]
    simp [sbit, Nat.shiftRight_eq_div_pow]
  unfold bval
  rw [h0, h1]
  omega

/-- The kernel table `klT.get b` of the base character `k` is a letter table of
`permAut (kleinPerm k b)`, with all entries `< 81`. -/
private lemma tabOfKleinPermAut (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5) (b : ℕ)
    (hb : b < 4) :
    TabOf (permAut (kleinPerm k b)) ((klTs.getD k (NT.leaf 0)).get b) ∧
    (∀ j < 81, lk ((klTs.getD k (NT.leaf 0)).get b) j < 81) := by
  have hsem := hK k hk
  unfold KleinSem at hsem
  dsimp only at hsem
  obtain ⟨h1, -⟩ := hsem
  have hlk := h1 b hb
  have hNB : NB1 5 = 81 := by norm_num [NB1]
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [hlk j hj]
    have hsig : sigAut (kleinPerm k b) (fun i : Fin 5 => decide (sbit 0 i.val = 1)) =
        permAut (kleinPerm k b) := by
      have hf : (fun i : Fin 5 => decide (sbit 0 i.val = 1)) = (fun _ : Fin 5 => false) := by
        funext i; simp [sbit]
      show signAut (fun i : Fin 5 => decide (sbit 0 i.val = 1)) * permAut (kleinPerm k b) = _
      rw [hf, Work.PTCert.SigmaFacts.signAut_one, one_mul]
    rw [← hsig]
    exact Work.PTCert.codeFactsAux.letterActionPerm 5 (pcOf (kleinPerm k b)) 0 (kleinPerm k b)
      (Work.PTCert.codeFactsAux.validPC_pcOf _)
      (fun i => (Work.PTCert.codeFactsAux.pdig_pcOf _ i).symm) j (by rw [hNB]; exact hj)
  · intro j hj
    rw [hlk j hj]
    exact Work.PTCert.codeFactsAux.actLBound (pcOf (kleinPerm k b)) 0
      (Work.PTCert.codeFactsAux.validPC_pcOf _) j hj

theorem kleinCover (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hN : NSem) (hBB : BitsBridge)
    (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5)
    (hts : ∀ i < nK k, (ksL.getD k []).getD i 0 < 611)
    (x : EI) (hrep : repE x = x)
    (hadm : ∀ a : Fin 5 → ZMod 2, actN a x = x → chiS (SkF k) a = 1) :
    ∃ (i : ℕ) (b : Fin 2 → ZMod 2), i < nK k ∧ repE (kapE k b (kE k i)) = x := by
  obtain ⟨hInj, hclosed, hconj, hcomp, hid, hbij, hactTbl, hactCd, haddN, hzeroN, hSgSign,
    hscTbl⟩ := hA
  obtain ⟨-, -, -, hrepN, hrepRE, hrepEI⟩ := hNst
  obtain ⟨hBB1, hBB2, hBB3, hBB4, hBB5, hBB6⟩ := hBB
  have hsem := hK k hk
  unfold KleinSem at hsem
  dsimp only at hsem
  obtain ⟨hklk, hcov, hdist, hylen, hcols⟩ := hsem
  -- the `N`-representative number of `x`
  set t := (em x.1 - 1) / 32 with ht
  have ht611 : t < 611 := by rw [ht]; exact (hrepRE x).1
  have hrepx : (repE x).1 = rp t := by rw [ht]; exact (hrepRE x).2
  have hx : x.1 = rp t := by rw [← hrep]; exact hrepx
  have htclause := hcov t ht611
  by_cases hc0 : cG (kwTs.getD k (NT.leaf 0)) t = 0
  · -- `t` carries a vanishing witness: `x` would not be admissible
    obtain ⟨hfix, hchi⟩ := htclause.1 hc0
    have hsc32 : rG (vwTs.getD k (NT.leaf 0)) t < 32 := by
      have h : rG (vwTs.getD k (NT.leaf 0)) t ≤ 31 := Nat.and_le_right
      omega
    have hfixN : actN (zOfSc (m := 5) (rG (vwTs.getD k (NT.leaf 0)) t)) x = x := by
      apply Subtype.ext
      rw [hscTbl (rG (vwTs.getD k (NT.leaf 0)) t) hsc32 x, hx, hfix]
    have h1 := hadm (zOfSc (m := 5) (rG (vwTs.getD k (NT.leaf 0)) t)) hfixN
    have hSk32 : Sk k < 32 := by interval_cases k <;> decide
    have h2 : chiS (SkF k) (zOfSc (m := 5) (rG (vwTs.getD k (NT.leaf 0)) t)) = -1 := by
      have hb := hBB3 (Sk k) (rG (vwTs.getD k (NT.leaf 0)) t) hSk32 hsc32
      rw [show SkF k = maskSet (m := 5) (Sk k) from rfl, hb, hchi]
      norm_num
    rw [h1] at h2
    norm_num at h2
  · -- `x` is a Klein translate of the listed representative `ks[(kw t - 1) / 4]`
    obtain ⟨hAdm, hi, hrep2⟩ := htclause.2 hc0
    have hbb : (cG (kwTs.getD k (NT.leaf 0)) t - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
    obtain ⟨bp, hbp⟩ : ∃ bp : Fin 2 → ZMod 2,
        bval bp = (cG (kwTs.getD k (NT.leaf 0)) t - 1) % 4 :=
      ⟨zOfSc (m := 2) _, bval_zOfSc _ hbb⟩
    refine ⟨(cG (kwTs.getD k (NT.leaf 0)) t - 1) / 4, bp, ?_, ?_⟩
    · exact hi
    · apply Subtype.ext
      have hke : (kE k ((cG (kwTs.getD k (NT.leaf 0)) t - 1) / 4)).1
          = rp ((ksL.getD k []).getD ((cG (kwTs.getD k (NT.leaf 0)) t - 1) / 4) 0) :=
        (hrepEI _ (hts _ hi) pt0).2
      have hTabK := tabOfKleinPermAut hK k hk ((cG (kwTs.getD k (NT.leaf 0)) t - 1) % 4) hbb
      have hkap : (kapE k bp (kE k ((cG (kwTs.getD k (NT.leaf 0)) t - 1) / 4))).1
          = actC D.cmT ((klTs.getD k (NT.leaf 0)).get ((cG (kwTs.getD k (NT.leaf 0)) t - 1) % 4))
              (rp ((ksL.getD k []).getD ((cG (kwTs.getD k (NT.leaf 0)) t - 1) / 4) 0)) := by
        show (actE (permAut (kleinPerm k (bval bp)))
            (kE k ((cG (kwTs.getD k (NT.leaf 0)) t - 1) / 4))).1 = _
        rw [hbp]
        rw [hactTbl (permAut (kleinPerm k ((cG (kwTs.getD k (NT.leaf 0)) t - 1) % 4)))
              ((klTs.getD k (NT.leaf 0)).get ((cG (kwTs.getD k (NT.leaf 0)) t - 1) % 4))
              hTabK.1 hTabK.2, hke]
      rw [(hrepRE (kapE k bp (kE k ((cG (kwTs.getD k (NT.leaf 0)) t - 1) / 4)))).2, hkap, hrep2]
      exact hx.symm

end Work.PTCert.KleinGlue
