import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.OrbitKeysDefs

set_option maxRecDepth 10000

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G
open Work.PTCert.OrbitKeys

/-- The row representatives `x0E r pt0` (`r < 18`) lie in pairwise distinct `Sg`-orbits: the
`18` orbits of `Sg` on `E = B₂` are the rows of the certificate.

* `r = 0` is the identity: `x0E 0 pt0 = pt0` (`x0c 0 = 0` and `eltC 0 = 1`), and the identity is
  fixed by every `g ∈ Sg` (`ConjAction`, `fE` injective).
* `r ≥ 1`: a conjugate of `x0E r pt0` is `codeElt c · x0E r pt0 · (codeElt c)⁻¹` with
  `c` a valid code of `g` (`CodeFacts`); its code is `actCode c (x0c r)` (`ActSetup`), and the
  `RowSem` scan says that a code of a conjugate of `x0c r` can only be the row code `x0c r`
  itself. -/
theorem distinctOrbits (hCF : CodeFacts) (hA : ActSetup) (hR : RowSem) :
    ∀ r < 18, ∀ r' < 18, ∀ g ∈ Sg, actE g (x0E r pt0) = x0E r' pt0 → r = r' := by
  have hRs : RowSem := hR
  obtain ⟨hx00, hx0mem, _hrinfo, hlab, _hlablt, _hfilter, hrow, _hstab⟩ := hR
  obtain ⟨hInj, _hEx, hConj, _hMul, _hOne, _hBij, _hTab, hCode, _h2, _h3, _h4, _h5⟩ := hA
  intro r hr r' hr' g hg heq
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · -- ## `r = 0`: the identity row
    have hx0 : x0E 0 pt0 = pt0 := by
      apply Subtype.ext
      rw [x0E_val hRs (by norm_num), hx00]
      rfl
    have hfpt : fE pt0 = 1 := by rw [← hx0]; exact fE_x0E_zero hRs
    have hfix : actE g pt0 = pt0 := by
      apply hInj
      rw [hConj.2 g hg pt0, hfpt]
      simp
    have hx0r' : x0E r' pt0 = pt0 := by rw [← heq, hx0]; exact hfix
    have hcode0 : x0c r' = 0 := by
      have h := congrArg Subtype.val hx0r'
      rw [x0E_val hRs hr'] at h
      rwa [show (pt0 : EI).1 = 0 from rfl] at h
    have hlab0 : labE 0 0 = 0 := by
      have h := hlab 0 (by norm_num); rwa [hx00] at h
    have h2 : r' = labE 0 0 := by
      have h := hlab r' hr'
      rw [hcode0] at h
      exact h.symm
    omega
  · -- ## `r ≥ 1`: the row code determines the row
    obtain ⟨c, hcval, hcElt⟩ := hCF.2.1 g hg
    have h1 : (actE g (x0E r pt0)).1 = actCode c (x0c r) := by
      rw [← hcElt, hCode c hcval (x0E r pt0), x0E_val hRs hr]
    have h2 : actCode c (x0c r) = x0c r' := by
      have h := congrArg Subtype.val heq
      rw [h1, x0E_val hRs hr'] at h
      exact h
    exact ((hrow r hr hrpos c hcval).2 r' hr' h2).symm

end Work.PTCert
