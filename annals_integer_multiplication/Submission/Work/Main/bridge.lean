import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pcr_inj
import Submission.Work.Main.crt.Pcr_lt
import Submission.Work.Main.crt.Pcr_mod
import Submission.Work.Main.crt.Pinv_spec
import Submission.Work.Main.crt.Pinv_Pcr

/-! Bridges between the program data and the mathematical objects of the main step. -/

set_option autoImplicit false

namespace Work.Main

open HvdH

/-- `Pcr` is the interface's `crtIdx`. -/
theorem Pcr_eq_crtIdx : ∀ (ss : List ℕ) (m : ℕ), Pcr ss m = HvdH.crtIdx ss m := by
  intro ss
  induction ss with
  | nil => intro m; rfl
  | cons t ts ih => intro m; simp only [Pcr_cons, HvdH.crtIdx, ih]

/-- the `m`-th entry of the padded chunk list is the `m`-th chunk. -/
theorem pchunkN_eq (x b N' S m : ℕ) (hNS : N' ≤ S) : pchunkN x b N' S m = pchunk x b N' m := rfl

/-- the fixed point value of the scaled chunk is the chunk divided by `2^b`. -/
theorem fxC_pchunkZ (p b N' S x m : ℕ) (hb : b ≤ p) :
    HvdH.fxC p (pchunkZ x b N' S (p - b) m) = ((pchunkN x b N' S m : ℕ) : ℂ) / 2 ^ b := by
  have hp : (2 : ℂ) ^ p = (2 : ℂ) ^ (p - b) * 2 ^ b := by
    rw [← pow_add]; congr 1; omega
  have hc : ((((pchunk x b N' m : ℕ) : ℤ) * 2 ^ (p - b) : ℤ) : ℂ) =
      ((pchunk x b N' m : ℕ) : ℂ) * (2 : ℂ) ^ (p - b) := by push_cast; ring
  simp only [HvdH.fxC, pchunkZ, pchunkN, hc, hp, Int.cast_zero, zero_mul, add_zero]
  field_simp

/-- the flat-ordered chunk vector is `flatv`. -/
theorem fxVec_eq_flatv {ss : List ℕ} {N' b p x : ℕ} {F : List (ℤ × ℤ)}
    (hcop : ss.Pairwise Nat.Coprime) (hpos : ∀ s ∈ ss, 0 < s) (hb : b ≤ p)
    (hF : ∀ m < ss.prod, F.getD (HvdH.crtIdx ss m) (0,0) = pchunkZ x b N' ss.prod (p - b) m) :
    HvdH.fxVec p ss.prod F = flatv b N' ss x := by
  funext q
  have hlt : Pinv ss q.val < ss.prod := (crt.Pinv_spec hcop hpos q.isLt).1
  have hspec : Pcr ss (Pinv ss q.val) = q.val := (crt.Pinv_spec hcop hpos q.isLt).2
  have hidx : HvdH.crtIdx ss (Pinv ss q.val) = q.val := by
    rw [← Pcr_eq_crtIdx ss (Pinv ss q.val), hspec]
  have hFq : F.getD q.val (0,0) = pchunkZ x b N' ss.prod (p - b) (Pinv ss q.val) := by
    conv_lhs => rw [← hidx]
    exact hF (Pinv ss q.val) hlt
  have h1 : HvdH.fxVec p ss.prod F q =
      HvdH.fxC p (pchunkZ x b N' ss.prod (p - b) (Pinv ss q.val)) := by
    simp only [HvdH.fxVec]; exact congrArg (HvdH.fxC p) hFq
  rw [h1, fxC_pchunkZ p b N' ss.prod x (Pinv ss q.val) hb]
  simp only [flatv, pchunkN]

end Work.Main
