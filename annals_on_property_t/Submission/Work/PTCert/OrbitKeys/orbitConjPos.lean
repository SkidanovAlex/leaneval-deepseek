import Mathlib
import Submission.Work.PTCert.OrbitKeysDefs

set_option maxRecDepth 400000
set_option autoImplicit false

namespace Work.PTCert.OrbitKeys

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D

/-- `actCode` and `actC` agree when the letter table computes `actL`. -/
private lemma actCode_eq_actC (c tab z : ℕ)
    (h : ∀ k < 81, lk tab k = Submission.PTCert.actL 5 (c / 32) (c % 32) k)
    (h1 : z / 128 < 81) (h2 : z % 128 < 81) : actCode c z = actC cmT tab z := by
  unfold actCode Submission.PTCert.actC
  rw [← h (z / 128) h1, ← h (z % 128) h2]

/-- Membership of `List.getD`. -/
private lemma getD_mem' (l : List ℕ) (i : ℕ) (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem (hn := hi)]
  exact List.getElem_mem hi

theorem orbitConjPos (hCF : Submission.PTCert.CodeFacts) (hA : Submission.PTCert.G.ActSetup)
    (hE : Submission.PTCert.G.ESem) (hR : Submission.PTCert.G.RowSem)
    (hG : Submission.PTCert.G.GroupSem) {r : ℕ} (hr1 : 1 ≤ r) (hr : r < 18)
    (y : Submission.PTCert.G.EI) :
    ∃ σ ∈ Submission.PTCert.G.Sg,
      Submission.PTCert.G.actE σ (Work.PTCert.OrbitKeys.grepEI r (Submission.PTCert.G.labE r y.1)) = y ∧
      Submission.PTCert.G.actE σ (Submission.PTCert.G.x0E r Submission.PTCert.G.pt0) =
        Submission.PTCert.G.x0E r Submission.PTCert.G.pt0 := by
  have hR7 := hR.2.2.2.2.2.2.1
  have hR8 := hR.2.2.2.2.2.2.2
  have hcode := hA.2.2.2.2.2.2.2.1
  have hyEmem : y.1 ∈ eAll := List.mem_toFinset.mp y.2
  obtain ⟨hglt, i, hi, hiy⟩ := (hG.2.2 r hr hr1).1 y.1 hyEmem
  have hgmem : grepE r (labE r y.1) ∈ eAll := ((hG.2.2 r hr hr1).2.1 (labE r y.1) hglt).1
  obtain ⟨hvalidc, hlkc⟩ := hR8 r hr hr1 i hi
  have hcSg : codeElt ((stabL r).getD i 0) ∈ Sg := (hCF.1 _ hvalidc).1
  have hcmem : (stabL r).getD i 0 ∈ stabL r := getD_mem' _ i hi
  have hbounds := hE.2.2.1 (grepE r (labE r y.1)) hgmem
  refine ⟨codeElt ((stabL r).getD i 0), hcSg, ?_, ?_⟩
  · apply Subtype.ext
    show (actE (codeElt ((stabL r).getD i 0)) (grepEI r (labE r y.1))).1 = y.1
    rw [hcode _ hvalidc]
    have hval : (grepEI r (labE r y.1)).1 = grepE r (labE r y.1) :=
      grepEI_val (mem_eS_of_mem _ hgmem)
    rw [hval, actCode_eq_actC ((stabL r).getD i 0) (stabTab r i) (grepE r (labE r y.1))
      hlkc hbounds.1 hbounds.2.1, hiy]
  · apply Subtype.ext
    show (actE (codeElt ((stabL r).getD i 0)) (x0E r pt0)).1 = (x0E r pt0).1
    rw [hcode _ hvalidc, x0E_val hR hr]
    exact ((hR7 r hr hr1 ((stabL r).getD i 0) hvalidc).1).mpr hcmem

end Work.PTCert.OrbitKeys
