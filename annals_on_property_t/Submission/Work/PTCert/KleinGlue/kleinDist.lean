import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.nLevel

/-!
# `Work.PTCert.KleinGlue.kleinDist`

The listed Klein representatives `ksL.getD k []` of a base character `k ≤ 5` lie in pairwise
distinct `N`-orbits *after* translation by the Klein group `(ℤ/2)²` acting through `kapE k`:

`repE (kapE k b (kE k i)) = kE k j → i = j`.

This is the "distinct Klein orbits" hypothesis of `KleinLevel` (GL5).  The proof reads the
`N`-orbit number `(em z - 1) / 32` off the two sides of the hypothesis and compares the kernel
"Klein number" `cG kwT` of the resulting representative with the data recorded in `KleinSem k`.
-/

namespace Work.PTCert.KleinGlue

open Submission.PTCert Submission.PTCert.G Submission.RouteB
open Submission.PTCert.D

set_option maxHeartbeats 800000

/-- The code `32 * pcOf p` of a coordinate permutation realises `permAut p`. -/
private lemma codeElt_pcOf (hCF : CodeFacts) (p : Equiv.Perm (Fin 5)) :
    codeElt (32 * pcOf p) = Submission.RouteB.permAut p := by
  have h2 : codeElt (32 * pcOf p + scOf (fun _ : Fin 5 => false)) =
      sigAut p (fun _ : Fin 5 => false) :=
    (hCF.2.2.1 p (fun _ : Fin 5 => false)).2.2
  have hsc : scOf (fun _ : Fin 5 => false) = 0 := by simp [scOf]
  have hsig : sigAut p (fun _ : Fin 5 => false) = Submission.RouteB.permAut p := by
    rw [sigAut, SigmaFacts.signAut_one, one_mul]
  calc codeElt (32 * pcOf p)
      = codeElt (32 * pcOf p + scOf (fun _ : Fin 5 => false)) := by rw [hsc, add_zero]
    _ = sigAut p (fun _ : Fin 5 => false) := h2
    _ = Submission.RouteB.permAut p := hsig

/-- The two Klein generators `b 0, b 1 ∈ {0, 1}` give a Klein element number `< 4`. -/
private lemma bval_lt_four (b : Fin 2 → ZMod 2) : bval b < 4 := by
  unfold bval
  have h0 : (b 0).val < 2 := ZMod.val_lt (b 0)
  have h1 : (b 1).val < 2 := ZMod.val_lt (b 1)
  omega

/-- The letter table clause of `KleinSem`. -/
private lemma kleinSem_clause1 (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5) (b : ℕ)
    (hb : b < 4) (j : ℕ) (hj : j < 81) :
    lk ((klTs.getD k (NT.leaf 0)).get b) j = actL 5 (pcOf (kleinPerm k b)) 0 j := by
  have hkm := hK k hk
  unfold KleinSem at hkm
  dsimp only at hkm
  exact hkm.1 b hb j hj

/-- The second part of the distinctness clause of `KleinSem`. -/
private lemma kleinSem_clause3 (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5) (i : ℕ)
    (hi : i < (ksL.getD k []).length) (b : ℕ) (hb : b < 4) :
    (cG (kwTs.getD k (NT.leaf 0))
      ((em (actC cmT ((klTs.getD k (NT.leaf 0)).get b) (rp ((ksL.getD k []).getD i 0)))
        - 1) / 32) - 1) / 4 = i := by
  have hkm := hK k hk
  unfold KleinSem at hkm
  dsimp only at hkm
  exact (hkm.2.2.1 i hi).2 b hb

/-- The first part of the distinctness clause of `KleinSem`. -/
private lemma kleinSem_clause3' (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5) (i : ℕ)
    (hi : i < (ksL.getD k []).length) :
    cG (kwTs.getD k (NT.leaf 0)) ((ksL.getD k []).getD i 0) = 1 + 4 * i := by
  have hkm := hK k hk
  unfold KleinSem at hkm
  dsimp only at hkm
  exact (hkm.2.2.1 i hi).1

/-- The letter table of the Klein translation `permAut (kleinPerm k b)`. -/
private lemma tabOfKleinAux (hCF : CodeFacts) (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5)
    (b : ℕ) (hb : b < 4) :
    TabOf (Submission.RouteB.permAut (kleinPerm k b)) ((klTs.getD k (NT.leaf 0)).get b) ∧
    (∀ j < 81, lk ((klTs.getD k (NT.leaf 0)).get b) j < 81) := by
  have hvalid : validPC 5 (pcOf (kleinPerm k b)) = true :=
    (hCF.2.2.1 (kleinPerm k b) (fun _ : Fin 5 => false)).1
  have hce : codeElt (32 * pcOf (kleinPerm k b)) = Submission.RouteB.permAut (kleinPerm k b) :=
    codeElt_pcOf hCF (kleinPerm k b)
  have hdiv : (32 * pcOf (kleinPerm k b)) / 32 = pcOf (kleinPerm k b) :=
    Nat.mul_div_right _ (by norm_num : 0 < 32)
  have hmod : (32 * pcOf (kleinPerm k b)) % 32 = 0 := Nat.mul_mod_right 32 _
  have hvalid' : validPC 5 ((32 * pcOf (kleinPerm k b)) / 32) = true := by rw [hdiv]; exact hvalid
  have hcf1a : ∀ j < 81, actL 5 (pcOf (kleinPerm k b)) 0 j < 81 := by
    intro j hj
    have h := (hCF.1 (32 * pcOf (kleinPerm k b)) hvalid').2 j hj
    simpa [hdiv, hmod] using h.1
  have hcf1b : ∀ j < 81, Submission.RouteB.permAut (kleinPerm k b) * b1 5 j *
      (Submission.RouteB.permAut (kleinPerm k b))⁻¹ = b1 5 (actL 5 (pcOf (kleinPerm k b)) 0 j) := by
    intro j hj
    have h := (hCF.1 (32 * pcOf (kleinPerm k b)) hvalid').2 j hj
    simpa [hdiv, hmod, hce] using h.2
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [kleinSem_clause1 hK k hk b hb j hj]
    exact hcf1b j hj
  · rw [kleinSem_clause1 hK k hk b hb j hj]
    exact hcf1a j hj

theorem kleinDist (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hN : NSem)
    (hK : ∀ k ≤ 5, KleinSem k) (k : ℕ) (hk : k ≤ 5)
    (hts : ∀ i < nK k, (ksL.getD k []).getD i 0 < 611)
    (i j : ℕ) (hi : i < nK k) (hj : j < nK k) (b : Fin 2 → ZMod 2)
    (h : repE (kapE k b (kE k i)) = kE k j) : i = j := by
  obtain ⟨-, -, -, -, -, -, hTab, -, -, -, -, -⟩ := hA
  have hti : (ksL.getD k []).getD i 0 < 611 := hts i hi
  have htj : (ksL.getD k []).getD j 0 < 611 := hts j hj
  -- the codes of the listed representatives
  have hkEi : (kE k i).1 = rp ((ksL.getD k []).getD i 0) :=
    (hNst.2.2.2.2.2 ((ksL.getD k []).getD i 0) hti pt0).2
  have hkEj : (kE k j).1 = rp ((ksL.getD k []).getD j 0) :=
    (hNst.2.2.2.2.2 ((ksL.getD k []).getD j 0) htj pt0).2
  have hrepE_val : ∀ x : EI, (repE x).1 = rp ((em x.1 - 1) / 32) :=
    fun x => (hNst.2.2.2.2.1 x).2
  have hdivlt : ∀ x : EI, (em x.1 - 1) / 32 < 611 := fun x => (hNst.2.2.2.2.1 x).1
  -- the code of the Klein translate
  have hb4 : bval b < 4 := bval_lt_four b
  have htab := tabOfKleinAux hCF hK k hk (bval b) hb4
  have hkapE : (kapE k b (kE k i)).1 =
      actC cmT ((klTs.getD k (NT.leaf 0)).get (bval b)) (rp ((ksL.getD k []).getD i 0)) := by
    show (actE (Submission.RouteB.permAut (kleinPerm k (bval b))) (kE k i)).1 = _
    rw [hTab (Submission.RouteB.permAut (kleinPerm k (bval b)))
      ((klTs.getD k (NT.leaf 0)).get (bval b)) htab.1 htab.2 (kE k i), hkEi]
  set X : ℕ := (em (actC cmT ((klTs.getD k (NT.leaf 0)).get (bval b))
    (rp ((ksL.getD k []).getD i 0))) - 1) / 32 with hX
  have hrep : (repE (kapE k b (kE k i))).1 = rp X := by
    rw [hrepE_val (kapE k b (kE k i)), hkapE]
  have hXlt : X < 611 := by
    have h' := hdivlt (kapE k b (kE k i))
    rw [hkapE] at h'
    exact h'
  -- `rp` is injective on the representatives `< 611`
  have hrp_inj : ∀ a < 611, ∀ b' < 611, rp a = rp b' → a = b' := by
    intro a ha b' hb' hab
    have h1 : em (rp a) = 32 * a + 1 := (hN.2.1 a ha).2
    have h2 : em (rp b') = 32 * b' + 1 := (hN.2.1 b' hb').2
    rw [hab] at h1
    omega
  have hs : X = (ksL.getD k []).getD j 0 := by
    apply hrp_inj X hXlt _ htj
    have h1 : (repE (kapE k b (kE k i))).1 = (kE k j).1 := by rw [h]
    rw [hrep, hkEj] at h1
    exact h1
  -- compare the kernel Klein numbers
  have hkm : i < (ksL.getD k []).length := hi
  have hci : (cG (kwTs.getD k (NT.leaf 0)) X - 1) / 4 = i :=
    kleinSem_clause3 hK k hk i hkm (bval b) hb4
  have hcj : cG (kwTs.getD k (NT.leaf 0)) ((ksL.getD k []).getD j 0) = 1 + 4 * j :=
    kleinSem_clause3' hK k hk j hj
  rw [← hci, hs, hcj]
  omega

end Work.PTCert.KleinGlue
