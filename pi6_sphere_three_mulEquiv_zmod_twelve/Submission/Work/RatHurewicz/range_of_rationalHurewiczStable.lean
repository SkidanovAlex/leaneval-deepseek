import Mathlib
import Submission.Work.RatHurewicz.SerreHurewicz
import Submission.Work.Drive.RationalHurewicz
import Submission.Work.Stems.HurewiczNeutral

namespace Work.RatHurewicz

/-- **The drive's contract implies the map form of the rational Hurewicz statement.**  Given a
class `a : π_{n+1}(X,x₀)` of the range form, take a representative cube `Quotient.out a`; the
contract applied to it (its hypothesis is the statement that `hurewiczMapN (n+1) x₀ a =
hurewiczChain (n+1) x₀ (Quotient.out a)` is of finite order, by `Work.Stems.hurewiczMapN_out`) gives
a power of `Quotient.out a` equal to `1` in `π_{n+1}(X,x₀)`, hence a power of `a`. -/
theorem range_of_rationalHurewiczStable (h : Work.Drive.RationalHurewiczStable) :
    Work.RatHurewicz.HurewiczModTorsionRange := by
  intro k hk X _ x₀ hconn n hn a ha
  obtain ⟨N, hN, hNa⟩ := ha
  -- rewrite the Hurewicz image of the class as that of its representative cube
  have hout := Work.Stems.hurewiczMapN_out (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ a
  rw [hout] at hNa
  -- apply the contract to that cube
  obtain ⟨M, hM, hMpow⟩ :=
    h k hk X x₀ hconn n hn (Quotient.out a) ⟨N, hN, hNa⟩
  -- the class of the representative is `a` itself
  exact ⟨M, hM, by rwa [← Quotient.out_eq a]⟩

end Work.RatHurewicz
