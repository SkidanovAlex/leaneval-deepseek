import Mathlib.RingTheory.PowerSeries.Derivative

namespace Commons.RingTheory.PowerSeries

/-- Iterating the scaled-derivative endomorphism `g ↦ ψ · g'` on `f.subst b`
commutes with the substitution: `(ψ·d/dX)^[i] (f.subst b) =
((d/dX)^[i] f).subst b`, provided `ψ` is a two-sided inverse of `b'`
so that the chain rule telescopes. -/
lemma iterate_subst_deriv_scaled (R : Type*) [Field R] (f b ψ : PowerSeries R) (i : ℕ)
    (hb : PowerSeries.HasSubst b)
    (hunit : ((PowerSeries.derivative (R := R)) b) * ψ = 1) :
    ((fun g : PowerSeries R => ψ * ((PowerSeries.derivative (R := R)) g))^[i]) (f.subst b) =
      (((fun g : PowerSeries R => (PowerSeries.derivative (R := R)) g)^[i]) f).subst b := by
  induction i with
  | zero => simp
  | succ i ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih]
      let Y : PowerSeries R := ((fun g : PowerSeries R => (PowerSeries.derivative (R := R)) g)^[i]) f
      change (fun g : PowerSeries R => ψ * (PowerSeries.derivative (R := R)) g) (Y.subst b) =
        ((fun g : PowerSeries R => (PowerSeries.derivative (R := R)) g) Y).subst b
      have hchain : (PowerSeries.derivative (R := R)) (Y.subst b) =
          (((PowerSeries.derivative (R := R)) Y).subst b) * (PowerSeries.derivative (R := R)) b := by
        simpa using (PowerSeries.derivative_subst (R := R) (f := Y) (g := b) hb)
      calc
        (fun g : PowerSeries R => ψ * (PowerSeries.derivative (R := R)) g) (Y.subst b)
            = ψ * (PowerSeries.derivative (R := R)) (Y.subst b) := by rfl
        _ = ψ * ((((PowerSeries.derivative (R := R)) Y).subst b) * (PowerSeries.derivative (R := R)) b) := by
            rw [hchain]
        _ = (((PowerSeries.derivative (R := R)) Y).subst b) := by
            calc
              ψ * ((((PowerSeries.derivative (R := R)) Y).subst b) * (PowerSeries.derivative (R := R)) b)
                  = ((((PowerSeries.derivative (R := R)) Y).subst b) * (PowerSeries.derivative (R := R)) b) * ψ := by
                      rw [mul_comm]
              _ = (((PowerSeries.derivative (R := R)) Y).subst b) * ((PowerSeries.derivative (R := R)) b * ψ) := by
                      rw [mul_assoc]
              _ = (((PowerSeries.derivative (R := R)) Y).subst b) * 1 := by rw [hunit]
              _ = (((PowerSeries.derivative (R := R)) Y).subst b) := by simp
        _ = ((fun g : PowerSeries R => (PowerSeries.derivative (R := R)) g) Y).subst b := by rfl

end Commons.RingTheory.PowerSeries