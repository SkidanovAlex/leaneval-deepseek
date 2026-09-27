import Mathlib

namespace Work.PsiC

/-- The product of pairwise commuting idempotents in a ring is idempotent. -/
theorem IdemMul3 {R : Type} [Ring R] (a b c : R) (ha : a * a = a) (hb : b * b = b)
    (hc : c * c = c) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    (a * b * c) * (a * b * c) = a * b * c := by
  have hab' : Commute a b := hab
  have hac' : Commute a c := hac
  have hbc' : Commute b c := hbc
  have h1 : IsIdempotentElem a := ha
  have h2 : IsIdempotentElem b := hb
  have h3 : IsIdempotentElem c := hc
  exact (h1.mul_of_commute hab' h2).mul_of_commute (hac'.mul_left hbc') h3

end Work.PsiC
