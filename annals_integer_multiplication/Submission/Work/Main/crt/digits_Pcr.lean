import Mathlib
import Submission.Work.Main.defs
import Submission.Work.Main.crt.Pcr_lt

namespace Work.Main.crt

open Work.Main

/-- Unfolding of `HvdH.digits` on a cons. -/
lemma digits_cons (t : ℕ) (ts : List ℕ) (m : ℕ) :
    HvdH.digits (t :: ts) m = (m / ts.prod) % t :: HvdH.digits ts (m % ts.prod) := rfl

/-- `HvdH.digits ss` is the multi-index of `m % sᵢ` recovered from the flat CRT index
`Pcr ss m = Σᵢ (m % sᵢ) · ∏_{j>i} sⱼ`. -/
theorem digits_Pcr {ss : List ℕ} (hpos : ∀ s ∈ ss, 0 < s) (m : ℕ) :
    HvdH.digits ss (Pcr ss m) = ss.map (fun s => m % s) := by
  induction ss with
  | nil => rfl
  | cons t ts ih =>
    rw [Pcr_cons, digits_cons, List.map_cons]
    have hts : ∀ s ∈ ts, 0 < s := fun s hs => hpos s (List.mem_cons_of_mem _ hs)
    have htsprod : 0 < ts.prod := List.prod_pos hts
    have hPcrlt : Pcr ts m < ts.prod := Pcr_lt hts m
    have hdiv : ((m % t) * ts.prod + Pcr ts m) / ts.prod = m % t := by
      rw [mul_comm (m % t) ts.prod, Nat.mul_add_div htsprod, Nat.div_eq_of_lt hPcrlt,
        Nat.add_zero]
    have hmod : ((m % t) * ts.prod + Pcr ts m) % ts.prod = Pcr ts m := by
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hPcrlt]
    rw [hdiv, hmod, Nat.mod_mod, ih hts]

end Work.Main.crt
