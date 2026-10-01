/-
# `T13.Defs` — the closed form of `FT` in "atom" form, its cleared numerator, and the
interval versions used by the `table13_cert` numerical certificate.

**Generated file** (see the author's scratch generator).  Do not edit by hand.

For `π/2 < θ < π` and `λ, z` put `ζ = -λ tan θ`, `T = tan θ`, `C2 = cos²θ`,
`S2 = sin 2θ`, `CC2 = cos 2θ`, `E = exp (-(2 γ z))`, `γ = θ/ζ`.

* `FTreal θ λ z T C2 S2 CC2 E` is the right-hand side of `t13_ft_laplace` with those
  five subterms replaced by the arguments (so `FT θ λ z = FTreal θ λ z (tan θ) (cos²θ) …`).
* `Dreal λ z T = ζ · z² · (z²+ζ²)²` and `Mreal = FTreal · Dreal` is a *division-free*
  polynomial expression in the atoms; `Mreal_eq` records the identity.
* `Miv`, `Div`, `M0iv`, `D0iv` are the same expressions evaluated on interval arguments,
  and `Miv_mem`, `Div_mem`, `M0mem`, `D0mem` are their correctness lemmas.

`f0real θ λ T = λ(1+T²)(3 - θT - 3θ/T)` is the closed form of `fT θ λ 0`
(`t13_ft_zero`); `M0real/D0real` is the same quantity with the division cleared
(`D0real T = -T > 0` for `T < 0`).
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.T13.Iv
import Submission.Work.LinnikAreas.Density4.TestFun

noncomputable section

namespace Work.LinnikAreas.Density4.T13

open Work.LinnikAreas.Density4

/-- The closed form of `FT` (HB §7) as a function of `T = tan θ`, `C2 = cos²θ`,
`S2 = sin 2θ`, `CC2 = cos 2θ`, `E = exp (-(2γz))` (with `ζ = -λT`, `γ = θ/ζ`). -/
def FTreal (th lam z T C2 S2 CC2 E : ℝ) : ℝ :=
  (((lam * lam) * (((1:ℝ) + (T * T)) * ((1:ℝ) + (T * T)))) * (((((((((2:ℝ) * C2) * (th * ((1:ℝ) / ((-lam) * T)))) - (S2 * ((1:ℝ) / ((-lam) * T)))) * (((1:ℝ) - E) * ((1:ℝ) / z))) + ((-C2) * (((1:ℝ) - (E * ((1:ℝ) + (((2:ℝ) * (th * ((1:ℝ) / ((-lam) * T)))) * z)))) * ((1:ℝ) / (z * z))))) + (((th * ((1:ℝ) / ((-lam) * T))) - (S2 * ((1:ℝ) / ((2:ℝ) * ((-lam) * T))))) * (((((1:ℝ) - (E * CC2)) * z) + ((E * S2) * ((-lam) * T))) * ((1:ℝ) / ((z * z) + (((-lam) * T) * ((-lam) * T))))))) + ((-((1:ℝ)/(2:ℝ))) * (((((1:ℝ) - (E * ((CC2 * ((1:ℝ) + (((2:ℝ) * (th * ((1:ℝ) / ((-lam) * T)))) * z))) + (S2 * ((2:ℝ) * th))))) * ((z * z) - (((-lam) * T) * ((-lam) * T)))) - ((E * ((CC2 * ((2:ℝ) * th)) - (S2 * ((1:ℝ) + (((2:ℝ) * (th * ((1:ℝ) / ((-lam) * T)))) * z))))) * (((2:ℝ) * ((-lam) * T)) * z))) * ((1:ℝ) / (((z * z) + (((-lam) * T) * ((-lam) * T))) * ((z * z) + (((-lam) * T) * ((-lam) * T)))))))) + (((((1:ℝ)/(2:ℝ)) + C2) * ((1:ℝ) / ((-lam) * T))) * (((((1:ℝ) - (E * CC2)) * ((-lam) * T)) - ((E * S2) * z)) * ((1:ℝ) / ((z * z) + (((-lam) * T) * ((-lam) * T))))))))

/-- `Mreal = FTreal * Dreal`, cleared of the denominators `z`, `ζ`, `z²+ζ²`. -/
def Mreal (th lam z T C2 S2 CC2 E : ℝ) : ℝ :=
  (((lam * lam) * (((1:ℝ) + (T * T)) * ((1:ℝ) + (T * T)))) * (((((((((2:ℝ) * (th * C2)) - S2) * ((1:ℝ) - E)) * (z * (((z * z) + (((-lam) * T) * ((-lam) * T))) * ((z * z) + (((-lam) * T) * ((-lam) * T)))))) + (((-(((z * z) + (((-lam) * T) * ((-lam) * T))) * ((z * z) + (((-lam) * T) * ((-lam) * T))))) * C2) * (((-lam) * T) - (E * (((-lam) * T) + ((2:ℝ) * (th * z))))))) + (((((1:ℝ)/(2:ℝ)) * (((2:ℝ) * th) - S2)) * ((((1:ℝ) - (E * CC2)) * z) + ((E * S2) * ((-lam) * T)))) * ((z * z) * ((z * z) + (((-lam) * T) * ((-lam) * T)))))) + ((-((1:ℝ)/(2:ℝ))) * ((((((-lam) * T) - (E * ((CC2 * (((-lam) * T) + ((2:ℝ) * (th * z)))) + (((2:ℝ) * th) * (S2 * ((-lam) * T)))))) * ((z * z) - (((-lam) * T) * ((-lam) * T)))) - ((E * ((((2:ℝ) * th) * (CC2 * ((-lam) * T))) - (S2 * (((-lam) * T) + ((2:ℝ) * (th * z)))))) * ((2:ℝ) * (((-lam) * T) * z)))) * (z * z)))) + (((((1:ℝ)/(2:ℝ)) + C2) * ((((1:ℝ) - (E * CC2)) * ((-lam) * T)) - ((E * S2) * z))) * ((z * z) * ((z * z) + (((-lam) * T) * ((-lam) * T)))))))

/-- `Dreal λ z T = ζ z² (z²+ζ²)²`, `ζ = -λT`.  Positive whenever `z ≠ 0` and `T ≠ 0`. -/
def Dreal (lam z T : ℝ) : ℝ :=
  ((((-lam) * T) * (z * z)) * (((z * z) + (((-lam) * T) * ((-lam) * T))) * ((z * z) + (((-lam) * T) * ((-lam) * T)))))

/-- Interval version of `Mreal`. -/
def Miv (th lam z : ℝ) (Ti C2i S2i CC2i Ei : Iv) : Iv :=
  Iv.mul (Iv.mul (Iv.mul (Iv.ofReal lam) (Iv.ofReal lam)) (Iv.mul (Iv.add (Iv.ofReal (1:ℝ)) (Iv.mul (Ti) (Ti))) (Iv.add (Iv.ofReal (1:ℝ)) (Iv.mul (Ti) (Ti))))) (Iv.add (Iv.add (Iv.add (Iv.add (Iv.mul (Iv.mul (Iv.sub (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.mul (Iv.ofReal th) (C2i))) (S2i)) (Iv.sub (Iv.ofReal (1:ℝ)) (Ei))) (Iv.mul (Iv.ofReal z) (Iv.mul (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)))) (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti))))))) (Iv.mul (Iv.mul (Iv.neg (Iv.mul (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)))) (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)))))) (C2i)) (Iv.sub (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Ei) (Iv.add (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.mul (Iv.ofReal th) (Iv.ofReal z)))))))) (Iv.mul (Iv.mul (Iv.mul (Iv.ofReal ((1:ℝ)/(2:ℝ))) (Iv.sub (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.ofReal th)) (S2i))) (Iv.add (Iv.mul (Iv.sub (Iv.ofReal (1:ℝ)) (Iv.mul (Ei) (CC2i))) (Iv.ofReal z)) (Iv.mul (Iv.mul (Ei) (S2i)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti))))) (Iv.mul (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti))))))) (Iv.mul (Iv.neg (Iv.ofReal ((1:ℝ)/(2:ℝ)))) (Iv.mul (Iv.sub (Iv.mul (Iv.sub (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Ei) (Iv.add (Iv.mul (CC2i) (Iv.add (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.mul (Iv.ofReal th) (Iv.ofReal z))))) (Iv.mul (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.ofReal th)) (Iv.mul (S2i) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti))))))) (Iv.sub (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti))))) (Iv.mul (Iv.mul (Ei) (Iv.sub (Iv.mul (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.ofReal th)) (Iv.mul (CC2i) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)))) (Iv.mul (S2i) (Iv.add (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.mul (Iv.ofReal th) (Iv.ofReal z))))))) (Iv.mul (Iv.ofReal (2:ℝ)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.ofReal z))))) (Iv.mul (Iv.ofReal z) (Iv.ofReal z))))) (Iv.mul (Iv.mul (Iv.add (Iv.ofReal ((1:ℝ)/(2:ℝ))) (C2i)) (Iv.sub (Iv.mul (Iv.sub (Iv.ofReal (1:ℝ)) (Iv.mul (Ei) (CC2i))) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti))) (Iv.mul (Iv.mul (Ei) (S2i)) (Iv.ofReal z)))) (Iv.mul (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)))))))

/-- Interval version of `Dreal`. -/
def Divv (lam z : ℝ) (Ti : Iv) : Iv :=
  Iv.mul (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.ofReal z) (Iv.ofReal z))) (Iv.mul (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)))) (Iv.add (Iv.mul (Iv.ofReal z) (Iv.ofReal z)) (Iv.mul (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)) (Iv.mul (Iv.neg (Iv.ofReal lam)) (Ti)))))

/-- Interval version of `M0real`. -/
def M0iv (th lam : ℝ) (Ti : Iv) : Iv :=
  Iv.mul (Iv.mul (Iv.ofReal lam) (Iv.add (Iv.ofReal (1:ℝ)) (Iv.mul (Ti) (Ti)))) (Iv.mul (Iv.ofReal ((1:ℝ)/(6:ℝ))) (Iv.add (Iv.sub (Iv.mul (Iv.ofReal th) (Iv.mul (Ti) (Ti))) (Iv.mul (Iv.ofReal (3:ℝ)) (Ti))) (Iv.mul (Iv.ofReal (3:ℝ)) (Iv.ofReal th))))

/-- Interval version of `D0real`. -/
def D0iv (Ti : Iv) : Iv :=
  Iv.neg (Ti)

theorem Miv_mem (th lam z : ℝ) (Ti C2i S2i CC2i Ei : Iv) (T C2 S2 CC2 E : ℝ)
    (hT : Ti.Mem T) (hC2 : C2i.Mem C2) (hS2 : S2i.Mem S2) (hCC2 : CC2i.Mem CC2)
    (hE : Ei.Mem E) :
    (Miv th lam z Ti C2i S2i CC2i Ei).Mem (Mreal th lam z T C2 S2 CC2 E) :=
  Iv.mem_mul (Iv.mem_mul (Iv.mem_mul (Iv.mem_ofReal lam) (Iv.mem_ofReal lam)) (Iv.mem_mul (Iv.mem_add (Iv.mem_ofReal (1:ℝ)) (Iv.mem_mul (hT) (hT))) (Iv.mem_add (Iv.mem_ofReal (1:ℝ)) (Iv.mem_mul (hT) (hT))))) (Iv.mem_add (Iv.mem_add (Iv.mem_add (Iv.mem_add (Iv.mem_mul (Iv.mem_mul (Iv.mem_sub (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_mul (Iv.mem_ofReal th) (hC2))) (hS2)) (Iv.mem_sub (Iv.mem_ofReal (1:ℝ)) (hE))) (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_mul (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)))) (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT))))))) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_mul (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)))) (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)))))) (hC2)) (Iv.mem_sub (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (hE) (Iv.mem_add (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_mul (Iv.mem_ofReal th) (Iv.mem_ofReal z)))))))) (Iv.mem_mul (Iv.mem_mul (Iv.mem_mul (Iv.mem_ofReal ((1:ℝ)/(2:ℝ))) (Iv.mem_sub (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_ofReal th)) (hS2))) (Iv.mem_add (Iv.mem_mul (Iv.mem_sub (Iv.mem_ofReal (1:ℝ)) (Iv.mem_mul (hE) (hCC2))) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (hE) (hS2)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT))))) (Iv.mem_mul (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT))))))) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal ((1:ℝ)/(2:ℝ)))) (Iv.mem_mul (Iv.mem_sub (Iv.mem_mul (Iv.mem_sub (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (hE) (Iv.mem_add (Iv.mem_mul (hCC2) (Iv.mem_add (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_mul (Iv.mem_ofReal th) (Iv.mem_ofReal z))))) (Iv.mem_mul (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_ofReal th)) (Iv.mem_mul (hS2) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT))))))) (Iv.mem_sub (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT))))) (Iv.mem_mul (Iv.mem_mul (hE) (Iv.mem_sub (Iv.mem_mul (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_ofReal th)) (Iv.mem_mul (hCC2) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)))) (Iv.mem_mul (hS2) (Iv.mem_add (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_mul (Iv.mem_ofReal th) (Iv.mem_ofReal z))))))) (Iv.mem_mul (Iv.mem_ofReal (2:ℝ)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_ofReal z))))) (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z))))) (Iv.mem_mul (Iv.mem_mul (Iv.mem_add (Iv.mem_ofReal ((1:ℝ)/(2:ℝ))) (hC2)) (Iv.mem_sub (Iv.mem_mul (Iv.mem_sub (Iv.mem_ofReal (1:ℝ)) (Iv.mem_mul (hE) (hCC2))) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT))) (Iv.mem_mul (Iv.mem_mul (hE) (hS2)) (Iv.mem_ofReal z)))) (Iv.mem_mul (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)))))))

theorem Divv_mem (lam z : ℝ) (Ti : Iv) (T : ℝ) (hT : Ti.Mem T) :
    (Divv lam z Ti).Mem (Dreal lam z T) :=
  Iv.mem_mul (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z))) (Iv.mem_mul (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)))) (Iv.mem_add (Iv.mem_mul (Iv.mem_ofReal z) (Iv.mem_ofReal z)) (Iv.mem_mul (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)) (Iv.mem_mul (Iv.mem_neg (Iv.mem_ofReal lam)) (hT)))))

/-- The closed form of `fT θ λ 0` (HB Lemma 7.4). -/
def f0real (th lam T : ℝ) : ℝ := lam * (1 + T*T) * (3 - th*T - 3*th/T)

/-- `M0real = f0real / (−T)` cleared of the division. -/
def M0real (th lam T : ℝ) : ℝ :=
  ((lam * ((1:ℝ) + (T * T))) * (((1:ℝ)/(6:ℝ)) * (((th * (T * T)) - ((3:ℝ) * T)) + ((3:ℝ) * th))))

/-- `D0real T = -T > 0` for `T < 0`. -/
def D0real (T : ℝ) : ℝ :=
  (-T)

theorem M0mem (th lam : ℝ) (Ti : Iv) (T : ℝ) (hT : Ti.Mem T) :
    (M0iv th lam Ti).Mem (M0real th lam T) :=
  Iv.mem_mul (Iv.mem_mul (Iv.mem_ofReal lam) (Iv.mem_add (Iv.mem_ofReal (1:ℝ)) (Iv.mem_mul (hT) (hT)))) (Iv.mem_mul (Iv.mem_ofReal ((1:ℝ)/(6:ℝ))) (Iv.mem_add (Iv.mem_sub (Iv.mem_mul (Iv.mem_ofReal th) (Iv.mem_mul (hT) (hT))) (Iv.mem_mul (Iv.mem_ofReal (3:ℝ)) (hT))) (Iv.mem_mul (Iv.mem_ofReal (3:ℝ)) (Iv.mem_ofReal th))))

theorem D0mem (Ti : Iv) (T : ℝ) (hT : Ti.Mem T) : (D0iv Ti).Mem (D0real T) :=
  Iv.mem_neg (hT)

theorem Mreal_eq (th lam z T C2 S2 CC2 E : ℝ) (hz : z ≠ 0) (hlam : lam ≠ 0) (hT : T ≠ 0)
    (hW : z^2 + (lam*T)^2 ≠ 0) :
    Mreal th lam z T C2 S2 CC2 E = FTreal th lam z T C2 S2 CC2 E * Dreal lam z T := by
  simp only [Mreal, FTreal, Dreal]
  field_simp
  ring

theorem FTreal_eq (th lam z T C2 S2 CC2 E : ℝ) (hz : z ≠ 0) (hlam : lam ≠ 0) (hT : T ≠ 0)
    (hW : z^2 + (lam*T)^2 ≠ 0) :
    FTreal th lam z T C2 S2 CC2 E = Mreal th lam z T C2 S2 CC2 E / Dreal lam z T := by
  have hW' : z*z + ((-lam)*T)*((-lam)*T) ≠ 0 := by
    have : z*z + ((-lam)*T)*((-lam)*T) = z^2 + (lam*T)^2 := by ring
    rw [this]; exact hW
  have hD : Dreal lam z T ≠ 0 := by
    simp only [Dreal]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hlam) hT)
      (mul_self_ne_zero.mpr hz)) (mul_self_ne_zero.mpr hW')
  rw [Mreal_eq th lam z T C2 S2 CC2 E hz hlam hT hW]
  exact (mul_div_cancel_right₀ (FTreal th lam z T C2 S2 CC2 E) hD).symm

theorem M0_eq (th lam T : ℝ) (hT : T ≠ 0) :
    f0real th lam T / 6 = M0real th lam T / D0real T := by
  simp only [f0real, M0real, D0real]
  field_simp
  ring

end Work.LinnikAreas.Density4.T13
