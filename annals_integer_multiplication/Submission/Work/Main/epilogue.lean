import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs
import Submission.Work.Main.bridge
import Submission.Work.Main.finalmath
import Submission.Work.Main.crt.Pcr_lt
import Submission.Work.Main.crt.Pinv_Pcr
import Submission.Work.Main.recover.recov_eq

/-! The recovery corollary: the list produced by the algorithm carries the coefficients of the product. -/

set_option autoImplicit false

namespace Work.Main

open HvdH

/-- The values computed by the last stage (recovery + inverse reindexing) are exactly the
convolution coefficients of the chunked product. -/
theorem ys_getD_hcoeff {sp : SP} {zs : List (ℤ × ℤ)} {F G : List (ℤ × ℤ)} {ys : List ℤ}
    (hDFT : DFTMathProp)
    (hOK : ParamOK (max sp.x.size sp.y.size) sp.ts sp.ss)
    (hSp : sp.S = sp.ss.prod)
    (hFl : ∀ m < sp.ss.prod,
      F.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.x sp.b sp.N' sp.S (sp.p - sp.b) m)
    (hGl : ∀ m < sp.ss.prod,
      G.getD (HvdH.crtIdx sp.ss m) (0,0) = pchunkZ sp.y sp.b sp.N' sp.S (sp.p - sp.b) m)
    (hb : sp.b = HvdH.bpar (max sp.x.size sp.y.size))
    (hγ : 2 * HvdH.D * sp.α ^ 2 + 13 < sp.b) (hbp : sp.b ≤ sp.p) (h6 : 6 * sp.b ≤ sp.p)
    (hb12 : 12 ≤ sp.b) (hTb : sp.ts.prod * sp.b ≤ 10 * max sp.x.size sp.y.size)
    (hnb : max sp.x.size sp.y.size ≤ 2 ^ sp.b)
    (hApprox : HvdH.Approx sp.p zs
      (HvdH.convC sp.ss (HvdH.fxVec sp.p sp.ss.prod F) (HvdH.fxVec sp.p sp.ss.prod G))
      ((2 ^ (2 * HvdH.D * sp.α ^ 2 + 8) * sp.ts.prod ^ 2 * Nat.log 2 sp.ts.prod : ℕ) : ℝ))
    (hSlt : sp.S ≤ sp.ts.prod) (hN'2 : 2 * sp.N' ≤ sp.S + 1)
    (hys : ∀ m < sp.ss.prod, ys.getD m 0 = recov sp.S sp.p sp.b (zs.getD (HvdH.crtIdx sp.ss m) (0,0))) :
    ∀ m < sp.S, ys.getD m 0 = ((hcoeff sp.x sp.y sp.b sp.N' m : ℕ) : ℤ) := by
  have hcop : sp.ss.Pairwise Nat.Coprime := hOK.2.2.2.2.2.2.1
  have hodd : ∀ s ∈ sp.ss, Odd s := hOK.2.2.2.2.2.2.2
  have hpos : ∀ s ∈ sp.ss, 0 < s := fun s hs => (hodd s hs).pos
  intro m hm
  have hm' : m < sp.ss.prod := lt_of_lt_of_eq hm hSp
  have hq2 : HvdH.crtIdx sp.ss m < sp.S := by
    rw [hSp, ← Pcr_eq_crtIdx sp.ss m]
    exact (crt.Pcr_lt hpos m)
  have hrec : recov sp.S sp.p sp.b (zs.getD (HvdH.crtIdx sp.ss m) (0,0)) =
      ((hcoeff sp.x sp.y sp.b sp.N' (Pinv sp.ss (HvdH.crtIdx sp.ss m)) : ℕ) : ℤ) :=
    recover.recov_eq (by omega)
      (recov_eq_hcoeff hOK hSp hFl hGl hb hγ hbp h6 hb12 hTb hnb hApprox hSlt hN'2 hq2 hDFT)
  rw [hys m hm', hrec]
  congr 2
  rw [← Pcr_eq_crtIdx sp.ss m]
  exact crt.Pinv_Pcr hcop hpos hm'

end Work.Main
