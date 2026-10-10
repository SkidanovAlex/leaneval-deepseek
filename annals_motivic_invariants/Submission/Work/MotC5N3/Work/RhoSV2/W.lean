import Mathlib
import Submission.Work.MotV5.ASLocal.asRhoPoly_witPt_wv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000

/-! Atom-form copies of the witness ruling vector `asWv0 … asWv4` (products of `C a`, `C b`,
`C g` and `X`), so that `ring` sees genuine polynomial atoms. -/

namespace Work.MotV5.ASLocal

open Polynomial

noncomputable def Wa0 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  3*(C a)^(6:ℕ)*(C g)*X^(3:ℕ)+(C a)^(6:ℕ)*(C g)*X^(2:ℕ)+(C a)^(6:ℕ)*(C g)*X+4*(C a)^(6:ℕ)*(C g)+4*(C a)^(6:ℕ)*X^(6:ℕ)+(C a)^(6:ℕ)*X^(5:ℕ)+4*(C a)^(6:ℕ)*X^(3:ℕ)+(C a)^(6:ℕ)*X^(2:ℕ)+2*(C a)^(6:ℕ)*X+2*(C a)^(6:ℕ)+(C a)^(5:ℕ)*(C b)*(C g)*X^(3:ℕ)+2*(C a)^(5:ℕ)*(C b)*(C g)*X^(2:ℕ)+2*(C a)^(5:ℕ)*(C b)*(C g)+2*(C a)^(5:ℕ)*(C b)*X^(6:ℕ)+3*(C a)^(5:ℕ)*(C b)*X^(5:ℕ)+4*(C a)^(5:ℕ)*(C b)*X^(3:ℕ)+(C a)^(5:ℕ)*(C b)*X+(C a)^(5:ℕ)*(C b)+3*(C a)^(4:ℕ)*(C b)^(2:ℕ)*X^(3:ℕ)+3*(C a)^(4:ℕ)*(C b)^(2:ℕ)*X^(2:ℕ)+4*(C a)^(3:ℕ)*(C b)^(3:ℕ)*X^(3:ℕ)+2*(C a)^(3:ℕ)*(C b)^(3:ℕ)*X^(2:ℕ)+2*(C a)^(3:ℕ)*(C b)^(3:ℕ)*X+4*(C a)^(3:ℕ)*(C b)^(3:ℕ)+2*(C a)^(2:ℕ)*(C b)^(4:ℕ)*X^(3:ℕ)+2*(C a)^(2:ℕ)*(C b)^(4:ℕ)*X+4*(C a)^(2:ℕ)*(C b)^(4:ℕ)+(C a)*(C b)^(5:ℕ)*(C g)*X^(3:ℕ)+2*(C a)*(C b)^(5:ℕ)*(C g)*X^(2:ℕ)+2*(C a)*(C b)^(5:ℕ)*(C g)*X+3*(C a)*(C b)^(5:ℕ)*(C g)+3*(C a)*(C b)^(5:ℕ)*X^(6:ℕ)+2*(C a)*(C b)^(5:ℕ)*X^(5:ℕ)+4*(C a)*(C b)^(5:ℕ)*X^(3:ℕ)+4*(C a)*(C b)^(5:ℕ)*X^(2:ℕ)+3*(C a)*(C b)^(5:ℕ)*X+2*(C a)*(C b)^(5:ℕ)+2*(C b)^(6:ℕ)*(C g)*X^(3:ℕ)+4*(C b)^(6:ℕ)*(C g)*X^(2:ℕ)+4*(C b)^(6:ℕ)*(C g)+4*(C b)^(6:ℕ)*X^(6:ℕ)+(C b)^(6:ℕ)*X^(5:ℕ)+(C b)^(6:ℕ)*X^(3:ℕ)+2*(C b)^(6:ℕ)*X^(2:ℕ)+3*(C b)^(6:ℕ)*X+4*(C b)^(6:ℕ)

noncomputable def Wa1 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  (C a)^(6:ℕ)*(C g)*X^(2:ℕ)+4*(C a)^(6:ℕ)*(C g)+(C a)^(6:ℕ)*X^(6:ℕ)+3*(C a)^(6:ℕ)*X^(5:ℕ)+3*(C a)^(6:ℕ)*X^(4:ℕ)+4*(C a)^(6:ℕ)*X^(3:ℕ)+(C a)^(6:ℕ)*X^(2:ℕ)+2*(C a)^(6:ℕ)*X+2*(C a)^(6:ℕ)+2*(C a)^(5:ℕ)*(C b)*(C g)*X^(2:ℕ)+3*(C a)^(5:ℕ)*(C b)*(C g)+2*(C a)^(5:ℕ)*(C b)*X^(6:ℕ)+3*(C a)^(5:ℕ)*(C b)*X^(5:ℕ)+4*(C a)^(5:ℕ)*(C b)*X^(4:ℕ)+(C a)^(5:ℕ)*(C b)*X^(3:ℕ)+4*(C a)^(5:ℕ)*(C b)*X^(2:ℕ)+4*(C a)^(5:ℕ)*(C b)*X+3*(C a)^(4:ℕ)*(C b)^(2:ℕ)*X^(3:ℕ)+2*(C a)^(4:ℕ)*(C b)^(2:ℕ)*X^(2:ℕ)+(C a)^(4:ℕ)*(C b)^(2:ℕ)*X+4*(C a)^(4:ℕ)*(C b)^(2:ℕ)+4*(C a)^(3:ℕ)*(C b)^(3:ℕ)*X^(3:ℕ)+(C a)^(3:ℕ)*(C b)^(3:ℕ)*X^(2:ℕ)+3*(C a)^(3:ℕ)*(C b)^(3:ℕ)+2*(C a)^(2:ℕ)*(C b)^(4:ℕ)*X^(3:ℕ)+3*(C a)^(2:ℕ)*(C b)^(4:ℕ)*X^(2:ℕ)+(C a)^(2:ℕ)*(C b)^(4:ℕ)*X+2*(C a)^(2:ℕ)*(C b)^(4:ℕ)+2*(C a)*(C b)^(5:ℕ)*(C g)*X^(2:ℕ)+3*(C a)*(C b)^(5:ℕ)*(C g)+2*(C a)*(C b)^(5:ℕ)*X^(6:ℕ)+(C a)*(C b)^(5:ℕ)*X^(5:ℕ)+(C a)*(C b)^(5:ℕ)*X^(4:ℕ)+4*(C a)*(C b)^(5:ℕ)*X^(3:ℕ)+(C a)*(C b)^(5:ℕ)*X^(2:ℕ)+4*(C a)*(C b)^(5:ℕ)+4*(C b)^(6:ℕ)*(C g)*X^(2:ℕ)+(C b)^(6:ℕ)*(C g)+4*(C b)^(6:ℕ)*X^(6:ℕ)+(C b)^(6:ℕ)*X^(5:ℕ)+3*(C b)^(6:ℕ)*X^(4:ℕ)+2*(C b)^(6:ℕ)

noncomputable def Wa2 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  3*(C a)^(6:ℕ)*(C g)*X+2*(C a)^(6:ℕ)*(C g)+(C a)^(6:ℕ)*X^(6:ℕ)+3*(C a)^(6:ℕ)*X^(5:ℕ)+4*(C a)^(6:ℕ)*X^(4:ℕ)+2*(C a)^(6:ℕ)*X^(3:ℕ)+3*(C a)^(6:ℕ)*X^(2:ℕ)+2*(C a)^(6:ℕ)*X+4*(C a)^(6:ℕ)+(C a)^(5:ℕ)*(C b)*(C g)*X+4*(C a)^(5:ℕ)*(C b)*(C g)+2*(C a)^(5:ℕ)*(C b)*X^(6:ℕ)+(C a)^(5:ℕ)*(C b)*X^(5:ℕ)+2*(C a)^(5:ℕ)*(C b)*X^(4:ℕ)+(C a)^(5:ℕ)*(C b)*X^(3:ℕ)+4*(C a)^(5:ℕ)*(C b)*X^(2:ℕ)+2*(C a)^(5:ℕ)*(C b)*X+(C a)^(5:ℕ)*(C b)+3*(C a)^(4:ℕ)*(C b)^(2:ℕ)*X^(2:ℕ)+2*(C a)^(4:ℕ)*(C b)^(2:ℕ)*X+4*(C a)^(4:ℕ)*(C b)^(2:ℕ)+4*(C a)^(3:ℕ)*(C b)^(3:ℕ)*X^(2:ℕ)+(C a)^(3:ℕ)*(C b)^(3:ℕ)*X+2*(C a)^(3:ℕ)*(C b)^(3:ℕ)+2*(C a)^(2:ℕ)*(C b)^(4:ℕ)*X^(2:ℕ)+3*(C a)^(2:ℕ)*(C b)^(4:ℕ)*X+(C a)^(2:ℕ)*(C b)^(4:ℕ)+(C a)*(C b)^(5:ℕ)*(C g)*X+4*(C a)*(C b)^(5:ℕ)*(C g)+2*(C a)*(C b)^(5:ℕ)*X^(6:ℕ)+(C a)*(C b)^(5:ℕ)*X^(5:ℕ)+3*(C a)*(C b)^(5:ℕ)*X^(4:ℕ)+4*(C a)*(C b)^(5:ℕ)*X^(3:ℕ)+2*(C a)*(C b)^(5:ℕ)*X^(2:ℕ)+3*(C a)*(C b)^(5:ℕ)*X+(C a)*(C b)^(5:ℕ)+2*(C b)^(6:ℕ)*(C g)*X+3*(C b)^(6:ℕ)*(C g)+4*(C b)^(6:ℕ)*X^(6:ℕ)+2*(C b)^(6:ℕ)*X^(5:ℕ)+4*(C b)^(6:ℕ)*X^(4:ℕ)+2*(C b)^(6:ℕ)*X^(3:ℕ)+(C b)^(6:ℕ)*X^(2:ℕ)+(C b)^(6:ℕ)*X+(C b)^(6:ℕ)

noncomputable def Wa3 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  2*(C a)^(6:ℕ)*X^(5:ℕ)+3*(C a)^(6:ℕ)*X^(4:ℕ)+4*(C a)^(6:ℕ)*X^(3:ℕ)+2*(C a)^(6:ℕ)*X^(2:ℕ)+3*(C a)^(6:ℕ)*X+2*(C a)^(6:ℕ)+4*(C a)^(5:ℕ)*(C b)*X^(5:ℕ)+(C a)^(5:ℕ)*(C b)*X^(4:ℕ)+3*(C a)^(5:ℕ)*(C b)*X^(2:ℕ)+(C a)^(5:ℕ)*(C b)*X+3*(C a)^(5:ℕ)*(C b)+4*(C a)^(4:ℕ)*(C b)^(2:ℕ)*X+2*(C a)^(4:ℕ)*(C b)^(2:ℕ)+2*(C a)^(3:ℕ)*(C b)^(3:ℕ)*X+(C a)^(3:ℕ)*(C b)^(3:ℕ)+(C a)^(2:ℕ)*(C b)^(4:ℕ)*X+3*(C a)^(2:ℕ)*(C b)^(4:ℕ)+4*(C a)*(C b)^(5:ℕ)*X^(5:ℕ)+(C a)*(C b)^(5:ℕ)*X^(4:ℕ)+3*(C a)*(C b)^(5:ℕ)*X^(3:ℕ)+4*(C a)*(C b)^(5:ℕ)*X^(2:ℕ)+4*(C a)*(C b)^(5:ℕ)*X+3*(C a)*(C b)^(5:ℕ)+3*(C b)^(6:ℕ)*X^(5:ℕ)+2*(C b)^(6:ℕ)*X^(4:ℕ)+(C b)^(6:ℕ)*X^(2:ℕ)+(C b)^(6:ℕ)*X+3*(C b)^(6:ℕ)

noncomputable def Wa4 {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  0

noncomputable def WaV {K : Type} [CommRing K] (a b g : K) : Fin 5 → Polynomial K :=
  ![Wa0 a b g, Wa1 a b g, Wa2 a b g, Wa3 a b g, Wa4 a b g]

set_option maxHeartbeats 4000000 in
theorem hWa0 {K : Type} [CommRing K] (a b g : K) : asWv0 a b g = Wa0 a b g := by
  simp only [asWv0, Wa0, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast, pow_one, mul_one]
  try ring

set_option maxHeartbeats 4000000 in
theorem hWa1 {K : Type} [CommRing K] (a b g : K) : asWv1 a b g = Wa1 a b g := by
  simp only [asWv1, Wa1, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast, pow_one, mul_one]
  try ring

set_option maxHeartbeats 4000000 in
theorem hWa2 {K : Type} [CommRing K] (a b g : K) : asWv2 a b g = Wa2 a b g := by
  simp only [asWv2, Wa2, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast, pow_one, mul_one]
  try ring

set_option maxHeartbeats 4000000 in
theorem hWa3 {K : Type} [CommRing K] (a b g : K) : asWv3 a b g = Wa3 a b g := by
  simp only [asWv3, Wa3, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast, pow_one, mul_one]
  try ring

set_option maxHeartbeats 4000000 in
theorem hWa4 {K : Type} [CommRing K] (a b g : K) : asWv4 a b g = Wa4 a b g := by
  simp only [asWv4, Wa4, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast, pow_one, mul_one]
  try ring

end Work.MotV5.ASLocal
