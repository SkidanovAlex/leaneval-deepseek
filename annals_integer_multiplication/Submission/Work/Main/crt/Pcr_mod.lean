import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.crt

open Work.Main

/-- `Pcr` is invariant under reduction of the argument modulo `ss.prod`: the flat CRT index
of `m % ∏ss` coincides with that of `m`. -/
theorem Pcr_mod (ss : List ℕ) (m : ℕ) : Pcr ss (m % ss.prod) = Pcr ss m := by
  induction ss generalizing m with
  | nil => simp
  | cons t ts ih =>
      simp only [Pcr_cons, List.prod_cons]
      have h1 : m % (t * ts.prod) % t = m % t :=
        Nat.mod_mod_of_dvd m (dvd_mul_right t ts.prod)
      have h2 : Pcr ts (m % (t * ts.prod)) = Pcr ts m :=
        calc Pcr ts (m % (t * ts.prod))
            = Pcr ts ((m % (t * ts.prod)) % ts.prod) := (ih _).symm
          _ = Pcr ts (m % ts.prod) := by
                rw [Nat.mod_mod_of_dvd m (dvd_mul_left ts.prod t)]
          _ = Pcr ts m := ih m
      rw [h1, h2]

end Work.Main.crt
