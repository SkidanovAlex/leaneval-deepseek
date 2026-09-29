import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.crt

open Work.Main

/-- The flat CRT index of a multi-index is bounded by the product of the moduli: at each step
`Pcr (t :: ts) m = (m % t) * ∏ts + Pcr ts m < t * ∏ts = ∏(t :: ts)`. -/
theorem Pcr_lt {ss : List ℕ} (hpos : ∀ s ∈ ss, 0 < s) (m : ℕ) : Pcr ss m < ss.prod := by
  induction ss generalizing m with
  | nil => simp
  | cons t ts ih =>
    rw [Pcr_cons, List.prod_cons]
    have ht : 0 < t := hpos t (List.mem_cons_self ..)
    have hts : ∀ s ∈ ts, 0 < s := fun s hs => hpos s (List.mem_cons_of_mem _ hs)
    have ih' : Pcr ts m < ts.prod := ih hts m
    have hmod : m % t < t := Nat.mod_lt _ ht
    have h1 : m % t * ts.prod + Pcr ts m < m % t * ts.prod + ts.prod :=
      Nat.add_lt_add_left ih' _
    have h2 : m % t * ts.prod + ts.prod = (m % t + 1) * ts.prod := by ring
    have h3 : (m % t + 1) * ts.prod ≤ t * ts.prod :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hmod)
    omega

end Work.Main.crt
