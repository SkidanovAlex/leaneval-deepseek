import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.RiemannRoch.Aquot.rank_Aquot_place
import Submission.Work.RiemannRoch.Aquot.rank_quotient_tower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch.Aquot

open Work.CurveBasics

variable {k : Type u} [Field k]

/-- The divisor of a single place, as a local abbreviation for
`Work.CurveBasics.Curve.Div.place`. -/
noncomputable abbrev placeDiv {C : Work.CurveBasics.Curve k} (Q : C.Place) : C.Div :=
  Work.CurveBasics.Curve.Div.place Q

/-- `A(D)` is trivial modulo itself. -/
theorem rank_Aquot_self (C : Work.CurveBasics.Curve k) (D : C.Div) :
    Module.rank k (Work.RiemannRoch.Curve.Aquot C D D) = 0 := by
  rw [rank_zero_iff]
  simp only [Work.RiemannRoch.Curve.Aquot, Submodule.comap_subtype_self]
  infer_instance

/-- Adding `n` poles at a single place increases the rank of `A(D + n·[Q])/A(D)` by
`n · Q.degree`. -/
theorem rank_Aquot_nsmul_place (C : Work.CurveBasics.Curve k) (D : C.Div) (Q : C.Place)
    (n : ℕ) :
    Module.rank k (Work.RiemannRoch.Curve.Aquot C D (D + n • placeDiv Q))
      = ((n * Q.degree : ℕ) : Cardinal) := by
  induction n with
  | zero =>
      rw [zero_nsmul, add_zero, rank_Aquot_self]
      simp
  | succ n ih =>
      have h : D + (n + 1) • placeDiv Q = (D + n • placeDiv Q) + placeDiv Q := by
        rw [succ_nsmul, add_assoc]
      rw [h]
      rw [rank_quotient_tower (S := Work.RiemannRoch.Curve.A C D)
        (T := Work.RiemannRoch.Curve.A C (D + n • placeDiv Q))
        (A := Work.RiemannRoch.Curve.A C ((D + n • placeDiv Q) + placeDiv Q)) ?_ ?_]
      · rw [rank_Aquot_place, ih, ← Nat.cast_add]
        congr 1
        rw [Nat.succ_mul]
        omega
      · exact Work.RiemannRoch.Curve.A_mono C (Finsupp.le_def.mpr fun P => by
          rw [Finsupp.add_apply]
          exact le_add_of_nonneg_right (by
            rw [Finsupp.smul_apply, placeDiv, Work.CurveBasics.Curve.Div.place,
              Finsupp.single_apply]
            split <;> simp))
      · exact Work.RiemannRoch.Curve.A_mono C (Finsupp.le_def.mpr fun P => by
          rw [Finsupp.add_apply]
          exact le_add_of_nonneg_right (by
            rw [placeDiv, Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
            split <;> simp))

/-- The degree of `n • [Q]`, as a natural number. -/
theorem toNat_deg_nsmul_place (C : Work.CurveBasics.Curve k) (Q : C.Place) (n : ℕ) :
    (C.deg (n • placeDiv Q)).toNat = n * Q.degree := by
  rw [C.deg_nsmul, placeDiv, Work.CurveBasics.Curve.deg_place, nsmul_eq_mul, ← Nat.cast_mul,
    Int.toNat_natCast]

/-- Adding poles bounded by an effective divisor `F` increases the rank of the quotient
`A(D + F)/A(D)` by `deg F`. -/
theorem rank_Aquot_add (C : Work.CurveBasics.Curve k) (D : C.Div) :
    ∀ F : C.Div, F.IsEffective →
      Module.rank k (Work.RiemannRoch.Curve.Aquot C D (D + F))
        = ((C.deg F).toNat : Cardinal) := by
  intro F
  refine Finsupp.induction₂ (motive := fun F : C.Div => F.IsEffective →
    Module.rank k (Work.RiemannRoch.Curve.Aquot C D (D + F))
      = ((C.deg F).toNat : Cardinal)) F ?_ ?_
  · intro _
    rw [add_zero, rank_Aquot_self]
    simp
  · intro a b f ha hb ih hF
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have hbval : (f + Finsupp.single a b) a = b := by
      rw [Finsupp.add_apply, hfa, Finsupp.single_eq_same, zero_add]
    have hb0 : 0 ≤ b := by rw [← hbval]; exact hF a
    have hff : Work.CurveBasics.Curve.Div.IsEffective f := by
      intro P
      by_cases hP : P = a
      · subst hP; rw [hfa]
      · have h1 : (f + Finsupp.single a b) P = f P := by
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hP, add_zero]
        rw [← h1]; exact hF P
    have hsingle : Finsupp.single a b = (b.toNat : ℕ) • placeDiv a := by
      rw [placeDiv, Work.CurveBasics.Curve.Div.place, Finsupp.smul_single]
      congr 1
      rw [nsmul_eq_mul, mul_one, Int.toNat_of_nonneg hb0]
    have hFeq : f + Finsupp.single a b = f + (b.toNat : ℕ) • placeDiv a := by
      rw [hsingle]
    rw [hFeq]
    have hnn : ∀ P, 0 ≤ ((b.toNat : ℕ) • placeDiv a) P := fun P => by
      rw [Finsupp.smul_apply, placeDiv, Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]
      split <;> simp
    have hle1 : Work.RiemannRoch.Curve.A C D ≤ Work.RiemannRoch.Curve.A C (D + f) :=
      Work.RiemannRoch.Curve.A_mono C (Finsupp.le_def.mpr fun P => by
        rw [Finsupp.add_apply]
        exact le_add_of_nonneg_right (hff P))
    have hle2 : Work.RiemannRoch.Curve.A C (D + f) ≤
        Work.RiemannRoch.Curve.A C ((D + f) + (b.toNat : ℕ) • placeDiv a) :=
      Work.RiemannRoch.Curve.A_mono C (Finsupp.le_def.mpr fun P => by
        rw [Finsupp.add_apply]
        exact le_add_of_nonneg_right (hnn P))
    have hdeg : (C.deg (f + (b.toNat : ℕ) • placeDiv a)).toNat
        = (C.deg f).toNat + b.toNat * a.degree := by
      have h2 : 0 ≤ C.deg ((b.toNat : ℕ) • placeDiv a) := by
        rw [show C.deg ((b.toNat : ℕ) • placeDiv a) = ((b.toNat : ℤ) * (a.degree : ℤ)) from by
          rw [C.deg_nsmul, placeDiv, Work.CurveBasics.Curve.deg_place, nsmul_eq_mul]]
        positivity
      rw [C.deg_add, Int.toNat_add (Work.CurveBasics.Divisor.deg_nonneg hff) h2,
        toNat_deg_nsmul_place]
    rw [← add_assoc, rank_quotient_tower (S := Work.RiemannRoch.Curve.A C D)
        (T := Work.RiemannRoch.Curve.A C (D + f))
        (A := Work.RiemannRoch.Curve.A C ((D + f) + (b.toNat : ℕ) • placeDiv a)) hle1 hle2,
      rank_Aquot_nsmul_place, ih hff, hdeg, Nat.cast_add, add_comm]

/-- **Riemann's theorem** for the adelic quotient `A(E)/A(D)`: the `k`-dimension of `A(E)/A(D)`
is the degree of `E - D`, for `D ≤ E`.  This is the elementary part of Riemann–Roch
(Serre, *Algebraic Groups and Class Fields*, II §5). -/
theorem finrank_Aquot {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) :
    Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E) = (C.deg (E - D)).toNat := by
  have hF : (E - D).IsEffective :=
    Work.CurveBasics.Curve.Div.le_iff.mpr fun Q => (Finsupp.le_def.mp h) Q
  have hmain : Module.rank k (Work.RiemannRoch.Curve.Aquot C D (D + (E - D)))
      = ((C.deg (E - D)).toNat : Cardinal) := rank_Aquot_add C D (E - D) hF
  rw [add_sub_cancel D E] at hmain
  show (Module.rank k (Work.RiemannRoch.Curve.Aquot C D E)).toNat = (C.deg (E - D)).toNat
  rw [hmain, Cardinal.toNat_natCast]

end Work.RiemannRoch.Aquot
