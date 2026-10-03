import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs
import Submission.Work.FIArea4.Vflip.JacobiFlip.jacobiSym_oddPart_flip
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Vflip.FlipSetup
import Submission.Work.FIArea4.PairSumCommon
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Vflip.Vfd.pairWeight_steps

namespace Work.FIArea4.Vflip.Vfd

theorem pairWeight_flip (D : ℕ) (r1 s1 r2 s2 : ℕ)
    (hodd1 : Odd r1) (hodd2 : Odd r2) (h8 : r1 % 8 = r2 % 8)
    (hs1 : Nat.Coprime s1 r1) (hs2 : Nat.Coprime s2 r2)
    (hA : 0 < Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2) :
    Work.FIArea4.Vflip.pairWeight D (r1, s1) (r2, s2)
      = (((jacobiSym (s1 : ℤ) (Work.FIArea4.Vflip.pairR r1 r2)
            * jacobiSym (s2 : ℤ) (Work.FIArea4.Vflip.pairR r2 r1) : ℤ) : ℂ)) *
        ∑ m ∈ (Work.FIArea4.Vflip.pairC r1 r2).divisors, (ArithmeticFunction.moebius m : ℂ) *
          ∑ q ∈ (Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2).divisors.filter
              (fun q => m * q ∣ Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2),
            ((bump (((Work.FIArea4.Vflip.pairAbs r1 r2 s1 s2 / q : ℕ) : ℝ) / D) : ℂ)) *
              ((jacobiSym ((Work.FIArea4.Vflip.pairR r1 r2 : ℕ) : ℤ) (Work.FIPlan.oddPart q)
                * jacobiSym ((Work.FIArea4.Vflip.pairR r2 r1 : ℕ) : ℤ)
                    (Work.FIPlan.oddPart q) : ℤ) : ℂ) := by
  change pairWeight D (r1, s1) (r2, s2) = PWrhs D r1 r2 s1 s2
  rw [pairWeight_eq_PWfull D r1 s1 r2 s2 hodd1 hodd2 hA,
      PWfull_eq_PWred D r1 r2 s1 s2 hodd1 hodd2]
  exact (PWrhsQ_eq_PWred D r1 r2 s1 s2 hodd1 hodd2 h8 hs1 hs2 hA).symm.trans
    (PWrhs_eq_PWrhsQ D r1 r2 s1 s2 hodd1 hA).symm

end Work.FIArea4.Vflip.Vfd
