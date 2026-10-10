import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.MotC5N3.RulingX2.GamCert

open MvPolynomial

variable {K : Type*} [Field K] [CharP K 5]

lemma five_dvd_numeral (k : ℕ) (h : 5 ∣ k) : (k : MvPolynomial (Fin 2) K) = 0 := by
  rw [← map_natCast (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K) k,
      (CharP.cast_eq_zero_iff K 5 k).mpr h, map_zero]

lemma num0 (n : ℕ) (h : 5 ∣ n) : (n : MvPolynomial (Fin 2) K) = 0 := five_dvd_numeral n h

noncomputable def E_ (a b g : K) : MvPolynomial (Fin 2) K :=
  C ((4 : K) * b ^(5:ℕ)) + C ((2 : K) * a ^(5:ℕ))

noncomputable def c1_ (a b g : K) : MvPolynomial (Fin 2) K :=
  C (b ^(5:ℕ)) + C ((4 : K) * b ^(5:ℕ) * g ^(1:ℕ)) + C ((4 : K) * a ^(1:ℕ) * b ^(4:ℕ)) + C (a ^(1:ℕ) * b ^(4:ℕ)) * X 1 + C ((3 : K) * a ^(2:ℕ) * b ^(3:ℕ)) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ)) * X 1 + C (a ^(3:ℕ) * b ^(2:ℕ)) + C ((2 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 + C ((2 : K) * a ^(4:ℕ) * b ^(1:ℕ)) + C ((2 : K) * a ^(4:ℕ) * b ^(1:ℕ)) * X 1 + C ((2 : K) * a ^(5:ℕ)) + C ((2 : K) * a ^(5:ℕ) * g ^(1:ℕ))

noncomputable def c0_ (a b g : K) : MvPolynomial (Fin 2) K :=
  C ((2 : K) * b ^(5:ℕ)) + C ((4 : K) * b ^(5:ℕ)) * X 1 + C ((4 : K) * b ^(5:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * b ^(5:ℕ) * g ^(1:ℕ)) + C ((4 : K) * b ^(5:ℕ) * g ^(1:ℕ)) * X 1 ^(2:ℕ) + C (a ^(1:ℕ) * b ^(4:ℕ)) + C ((3 : K) * a ^(1:ℕ) * b ^(4:ℕ)) * X 1 + C (a ^(1:ℕ) * b ^(4:ℕ)) * X 1 ^(2:ℕ) + C (a ^(1:ℕ) * b ^(4:ℕ) * g ^(1:ℕ)) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ)) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ)) * X 1 + C ((2 : K) * a ^(2:ℕ) * b ^(3:ℕ)) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(2:ℕ) * b ^(3:ℕ) * g ^(1:ℕ)) + C ((2 : K) * a ^(3:ℕ) * b ^(2:ℕ)) + C ((3 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 + C ((4 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(3:ℕ) * b ^(2:ℕ) * g ^(1:ℕ)) + C ((2 : K) * a ^(4:ℕ) * b ^(1:ℕ)) + C ((4 : K) * a ^(4:ℕ) * b ^(1:ℕ)) * X 1 + C ((3 : K) * a ^(4:ℕ) * b ^(1:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(4:ℕ) * b ^(1:ℕ) * g ^(1:ℕ)) + C (a ^(5:ℕ)) + C ((2 : K) * a ^(5:ℕ)) * X 1 + C ((3 : K) * a ^(5:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(5:ℕ) * g ^(1:ℕ)) + C ((2 : K) * a ^(5:ℕ) * g ^(1:ℕ)) * X 1 ^(2:ℕ)

noncomputable def Dh_ (a b g : K) : MvPolynomial (Fin 2) K :=
  C ((2 : K) * b ^(6:ℕ)) + C ((4 : K) * b ^(6:ℕ)) * X 1 + C ((4 : K) * b ^(6:ℕ) * g ^(1:ℕ)) * X 1 + C (a ^(1:ℕ) * b ^(5:ℕ)) + C ((3 : K) * a ^(1:ℕ) * b ^(5:ℕ)) * X 1 + C (a ^(1:ℕ) * b ^(5:ℕ)) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(1:ℕ) * b ^(5:ℕ) * g ^(1:ℕ)) * X 1 + C ((2 : K) * a ^(2:ℕ) * b ^(4:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(3:ℕ) * b ^(3:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(4:ℕ) * b ^(2:ℕ)) * X 1 ^(2:ℕ) + C (a ^(5:ℕ) * b ^(1:ℕ)) + C ((2 : K) * a ^(5:ℕ) * b ^(1:ℕ)) * X 1 + C (a ^(5:ℕ) * b ^(1:ℕ)) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(5:ℕ) * b ^(1:ℕ) * g ^(1:ℕ)) * X 1 + C ((3 : K) * a ^(6:ℕ)) + C ((4 : K) * a ^(6:ℕ)) * X 1 + C (a ^(6:ℕ) * g ^(1:ℕ)) * X 1

noncomputable def Rh_ (a b g : K) : MvPolynomial (Fin 2) K :=
  C (b ^(6:ℕ)) + C ((3 : K) * b ^(6:ℕ)) * X 1 + C ((2 : K) * b ^(6:ℕ) * g ^(1:ℕ)) + C ((4 : K) * b ^(6:ℕ) * g ^(1:ℕ)) * X 1 + C ((4 : K) * b ^(6:ℕ) * g ^(1:ℕ)) * X 1 ^(3:ℕ) + C ((2 : K) * a ^(1:ℕ) * b ^(5:ℕ)) + C ((3 : K) * a ^(1:ℕ) * b ^(5:ℕ)) * X 1 ^(2:ℕ) + C (a ^(1:ℕ) * b ^(5:ℕ) * g ^(1:ℕ)) + C ((3 : K) * a ^(1:ℕ) * b ^(5:ℕ) * g ^(1:ℕ)) * X 1 + C ((2 : K) * a ^(1:ℕ) * b ^(5:ℕ) * g ^(1:ℕ)) * X 1 ^(3:ℕ) + C ((2 : K) * a ^(2:ℕ) * b ^(4:ℕ)) * X 1 + C ((3 : K) * a ^(2:ℕ) * b ^(4:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(3:ℕ) * b ^(3:ℕ)) * X 1 + C ((3 : K) * a ^(4:ℕ) * b ^(2:ℕ)) * X 1 + C ((3 : K) * a ^(4:ℕ) * b ^(2:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(5:ℕ) * b ^(1:ℕ)) + C ((2 : K) * a ^(5:ℕ) * b ^(1:ℕ)) * X 1 ^(2:ℕ) + C (a ^(5:ℕ) * b ^(1:ℕ) * g ^(1:ℕ)) + C ((2 : K) * a ^(5:ℕ) * b ^(1:ℕ) * g ^(1:ℕ)) * X 1 + C ((2 : K) * a ^(5:ℕ) * b ^(1:ℕ) * g ^(1:ℕ)) * X 1 ^(3:ℕ) + C (a ^(6:ℕ)) + C ((2 : K) * a ^(6:ℕ)) * X 1 + C ((3 : K) * a ^(6:ℕ) * g ^(1:ℕ)) + C ((4 : K) * a ^(6:ℕ) * g ^(1:ℕ)) * X 1 + C (a ^(6:ℕ) * g ^(1:ℕ)) * X 1 ^(3:ℕ)

noncomputable def P_ (a b g : K) : MvPolynomial (Fin 2) K :=
  C (b ^(5:ℕ)) + C ((3 : K) * b ^(5:ℕ)) * X 1 + C ((4 : K) * b ^(5:ℕ)) * X 1 ^(2:ℕ) + C ((2 : K) * b ^(5:ℕ)) * X 1 ^(3:ℕ) + C ((3 : K) * b ^(5:ℕ) * g ^(1:ℕ)) + C ((4 : K) * b ^(5:ℕ) * g ^(1:ℕ)) * X 1 + C (b ^(5:ℕ) * g ^(1:ℕ)) * X 1 ^(3:ℕ) + C ((3 : K) * b ^(5:ℕ) * g ^(2:ℕ)) * X 1 + C ((2 : K) * b ^(5:ℕ) * g ^(2:ℕ)) * X 1 ^(5:ℕ) + C ((4 : K) * b ^(5:ℕ) * g ^(3:ℕ)) + C ((2 : K) * a ^(1:ℕ) * b ^(4:ℕ)) + C ((2 : K) * a ^(1:ℕ) * b ^(4:ℕ)) * X 1 + C ((2 : K) * a ^(1:ℕ) * b ^(4:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(1:ℕ) * b ^(4:ℕ)) * X 1 ^(3:ℕ) + C (a ^(1:ℕ) * b ^(4:ℕ)) * X 1 ^(4:ℕ) + C (a ^(1:ℕ) * b ^(4:ℕ) * g ^(1:ℕ)) * X 1 + C ((3 : K) * a ^(1:ℕ) * b ^(4:ℕ) * g ^(1:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ)) + C ((3 : K) * a ^(2:ℕ) * b ^(3:ℕ)) * X 1 + C (a ^(2:ℕ) * b ^(3:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(2:ℕ) * b ^(3:ℕ)) * X 1 ^(3:ℕ) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ)) * X 1 ^(4:ℕ) + C ((2 : K) * a ^(2:ℕ) * b ^(3:ℕ)) * X 1 ^(5:ℕ) + C ((2 : K) * a ^(2:ℕ) * b ^(3:ℕ) * g ^(1:ℕ)) * X 1 + C ((2 : K) * a ^(2:ℕ) * b ^(3:ℕ) * g ^(1:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(3:ℕ) * b ^(2:ℕ)) + C ((4 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 + C ((2 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 ^(3:ℕ) + C ((2 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 ^(4:ℕ) + C ((4 : K) * a ^(3:ℕ) * b ^(2:ℕ)) * X 1 ^(5:ℕ) + C ((4 : K) * a ^(3:ℕ) * b ^(2:ℕ) * g ^(1:ℕ)) * X 1 + C (a ^(3:ℕ) * b ^(2:ℕ) * g ^(1:ℕ)) * X 1 ^(2:ℕ) + C (a ^(4:ℕ) * b ^(1:ℕ)) + C ((4 : K) * a ^(4:ℕ) * b ^(1:ℕ)) * X 1 + C (a ^(4:ℕ) * b ^(1:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(4:ℕ) * b ^(1:ℕ)) * X 1 ^(3:ℕ) + C ((2 : K) * a ^(4:ℕ) * b ^(1:ℕ)) * X 1 ^(4:ℕ) + C ((3 : K) * a ^(4:ℕ) * b ^(1:ℕ) * g ^(1:ℕ)) * X 1 + C (a ^(4:ℕ) * b ^(1:ℕ) * g ^(1:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(5:ℕ)) * X 1 + C ((2 : K) * a ^(5:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(5:ℕ)) * X 1 ^(3:ℕ) + C ((4 : K) * a ^(5:ℕ) * g ^(1:ℕ)) + C ((3 : K) * a ^(5:ℕ) * g ^(1:ℕ)) * X 1 + C ((3 : K) * a ^(5:ℕ) * g ^(1:ℕ)) * X 1 ^(3:ℕ) + C ((4 : K) * a ^(5:ℕ) * g ^(2:ℕ)) * X 1 + C (a ^(5:ℕ) * g ^(2:ℕ)) * X 1 ^(5:ℕ) + C ((2 : K) * a ^(5:ℕ) * g ^(3:ℕ))

noncomputable def X0_ : MvPolynomial (Fin 2) K := X 0

noncomputable def P1_ (a b g : K) : MvPolynomial (Fin 2) K :=
  E_ (K := K) a b g * X0_ (K := K) ^(2:ℕ) + c1_ (K := K) a b g * X0_ (K := K) + c0_ (K := K) a b g

end Work.MotC5N3.RulingX2.GamCert
