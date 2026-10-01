import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_squarefree_r2

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.DirichletCharacter

theorem split_sum6 {p v : ℕ} [NeZero p] [NeZero v] (hcop : p.Coprime v)
    (χ : DirichletCharacter ℂ (p*v)) (a0 a1 a2 b0 b1 b2 : ℕ) :
    (∑ x : ZMod (p*v), χ ((x + (a0:ZMod (p*v))) * (x + (a1:ZMod (p*v))) * (x + (a2:ZMod (p*v))))
        * (starRingEnd ℂ) (χ ((x + (b0:ZMod (p*v))) * (x + (b1:ZMod (p*v))) * (x + (b2:ZMod (p*v))))))
    = (∑ y : ZMod p, factorLeft hcop χ ((y + (a0:ZMod p)) * (y + (a1:ZMod p)) * (y + (a2:ZMod p)))
        * (starRingEnd ℂ) (factorLeft hcop χ ((y + (b0:ZMod p)) * (y + (b1:ZMod p)) * (y + (b2:ZMod p)))))
      * (∑ z : ZMod v, factorRight hcop χ ((z + (a0:ZMod v)) * (z + (a1:ZMod v)) * (z + (a2:ZMod v)))
        * (starRingEnd ℂ) (factorRight hcop χ ((z + (b0:ZMod v)) * (z + (b1:ZMod v)) * (z + (b2:ZMod v))))) := by
  have hcastp : ∀ x : ZMod (p*v),
      (((x + (a0:ZMod (p*v))) * (x + (a1:ZMod (p*v))) * (x + (a2:ZMod (p*v)))).cast : ZMod p)
      = (x.cast + (a0:ZMod p)) * (x.cast + (a1:ZMod p)) * (x.cast + (a2:ZMod p)) := by
    intro x; simp only [ZMod.cast_mul (Nat.dvd_mul_right p v), ZMod.cast_add (Nat.dvd_mul_right p v),
      ZMod.cast_natCast (Nat.dvd_mul_right p v)]
  have hcastq : ∀ x : ZMod (p*v),
      (((x + (b0:ZMod (p*v))) * (x + (b1:ZMod (p*v))) * (x + (b2:ZMod (p*v)))).cast : ZMod p)
      = (x.cast + (b0:ZMod p)) * (x.cast + (b1:ZMod p)) * (x.cast + (b2:ZMod p)) := by
    intro x; simp only [ZMod.cast_mul (Nat.dvd_mul_right p v), ZMod.cast_add (Nat.dvd_mul_right p v),
      ZMod.cast_natCast (Nat.dvd_mul_right p v)]
  have hcastpv : ∀ x : ZMod (p*v),
      (((x + (a0:ZMod (p*v))) * (x + (a1:ZMod (p*v))) * (x + (a2:ZMod (p*v)))).cast : ZMod v)
      = (x.cast + (a0:ZMod v)) * (x.cast + (a1:ZMod v)) * (x.cast + (a2:ZMod v)) := by
    intro x; simp only [ZMod.cast_mul (Nat.dvd_mul_left v p), ZMod.cast_add (Nat.dvd_mul_left v p),
      ZMod.cast_natCast (Nat.dvd_mul_left v p)]
  have hcastqv : ∀ x : ZMod (p*v),
      (((x + (b0:ZMod (p*v))) * (x + (b1:ZMod (p*v))) * (x + (b2:ZMod (p*v)))).cast : ZMod v)
      = (x.cast + (b0:ZMod v)) * (x.cast + (b1:ZMod v)) * (x.cast + (b2:ZMod v)) := by
    intro x; simp only [ZMod.cast_mul (Nat.dvd_mul_left v p), ZMod.cast_add (Nat.dvd_mul_left v p),
      ZMod.cast_natCast (Nat.dvd_mul_left v p)]
  have hmain : (∑ x : ZMod (p*v), χ ((x + (a0:ZMod (p*v))) * (x + (a1:ZMod (p*v))) * (x + (a2:ZMod (p*v))))
        * (starRingEnd ℂ) (χ ((x + (b0:ZMod (p*v))) * (x + (b1:ZMod (p*v))) * (x + (b2:ZMod (p*v))))))
      = ∑ x : ZMod (p*v),
          (factorLeft hcop χ ((x.cast + (a0:ZMod p)) * (x.cast + (a1:ZMod p)) * (x.cast + (a2:ZMod p)))
            * (starRingEnd ℂ) (factorLeft hcop χ ((x.cast + (b0:ZMod p)) * (x.cast + (b1:ZMod p)) * (x.cast + (b2:ZMod p)))))
          * (factorRight hcop χ ((x.cast + (a0:ZMod v)) * (x.cast + (a1:ZMod v)) * (x.cast + (a2:ZMod v)))
            * (starRingEnd ℂ) (factorRight hcop χ ((x.cast + (b0:ZMod v)) * (x.cast + (b1:ZMod v)) * (x.cast + (b2:ZMod v))))) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [chi_eq_factors hcop χ ((x + (a0:ZMod (p*v))) * (x + (a1:ZMod (p*v))) * (x + (a2:ZMod (p*v)))),
        chi_eq_factors hcop χ ((x + (b0:ZMod (p*v))) * (x + (b1:ZMod (p*v))) * (x + (b2:ZMod (p*v)))),
        hcastp x, hcastq x, hcastpv x, hcastqv x, map_mul (starRingEnd ℂ), mul_mul_mul_comm]
  rw [hmain]
  have hstep := Fintype.sum_equiv (crtE hcop).toEquiv
    (fun x : ZMod (p*v) =>
          (factorLeft hcop χ ((x.cast + (a0:ZMod p)) * (x.cast + (a1:ZMod p)) * (x.cast + (a2:ZMod p)))
            * (starRingEnd ℂ) (factorLeft hcop χ ((x.cast + (b0:ZMod p)) * (x.cast + (b1:ZMod p)) * (x.cast + (b2:ZMod p)))))
          * (factorRight hcop χ ((x.cast + (a0:ZMod v)) * (x.cast + (a1:ZMod v)) * (x.cast + (a2:ZMod v)))
            * (starRingEnd ℂ) (factorRight hcop χ ((x.cast + (b0:ZMod v)) * (x.cast + (b1:ZMod v)) * (x.cast + (b2:ZMod v))))))
    (fun w : ZMod p × ZMod v =>
          (factorLeft hcop χ ((w.1 + (a0:ZMod p)) * (w.1 + (a1:ZMod p)) * (w.1 + (a2:ZMod p)))
            * (starRingEnd ℂ) (factorLeft hcop χ ((w.1 + (b0:ZMod p)) * (w.1 + (b1:ZMod p)) * (w.1 + (b2:ZMod p)))))
          * (factorRight hcop χ ((w.2 + (a0:ZMod v)) * (w.2 + (a1:ZMod v)) * (w.2 + (a2:ZMod v)))
            * (starRingEnd ℂ) (factorRight hcop χ ((w.2 + (b0:ZMod v)) * (w.2 + (b1:ZMod v)) * (w.2 + (b2:ZMod v))))))
    (fun x => by
      have h1 : ((crtE hcop).toEquiv x).1 = x.cast := crtE_fst hcop x
      have h2 : ((crtE hcop).toEquiv x).2 = x.cast := crtE_snd hcop x
      rw [h1, h2])
  rw [hstep, Fintype.sum_prod_type, ← Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
    (f := fun y : ZMod p => factorLeft hcop χ ((y + (a0:ZMod p)) * (y + (a1:ZMod p)) * (y + (a2:ZMod p)))
        * (starRingEnd ℂ) (factorLeft hcop χ ((y + (b0:ZMod p)) * (y + (b1:ZMod p)) * (y + (b2:ZMod p)))))
    (g := fun z : ZMod v => factorRight hcop χ ((z + (a0:ZMod v)) * (z + (a1:ZMod v)) * (z + (a2:ZMod v)))
        * (starRingEnd ℂ) (factorRight hcop χ ((z + (b0:ZMod v)) * (z + (b1:ZMod v)) * (z + (b2:ZMod v)))))]

end Commons.NumberTheory.DirichletCharacter
