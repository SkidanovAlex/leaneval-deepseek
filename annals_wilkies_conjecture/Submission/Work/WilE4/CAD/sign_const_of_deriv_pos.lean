import Mathlib
import Submission.Work.WilE4.CAD.sign_eq_of_between

namespace Work.WilE4.CAD

/-- If a polynomial `f` has strictly positive derivative on the open interval `(a, b)` and the signs
of the values at the endpoints `a`, `b` agree, then the sign of `f` is constant on `(a, b)` and
equal to the sign of `f` at `a`. -/
theorem sign_const_of_deriv_pos {f : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Set.Ioo a b, 0 < (f.derivative).eval t)
    (hs : SignType.sign (f.eval a) = SignType.sign (f.eval b)) :
    ∀ t ∈ Set.Ioo a b, SignType.sign (f.eval t) = SignType.sign (f.eval a) := by
  -- A polynomial with strictly positive derivative on `(a,b)` is strictly increasing on `[a,b]`.
  have hmono : StrictMonoOn (fun x => f.eval x) (Set.Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) f.continuous.continuousOn ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [Polynomial.deriv]
    exact h x hx
  intro t ht
  have hat : a < t := ht.1
  have htb : t < b := ht.2
  have hta : (fun x => f.eval x) a < (fun x => f.eval x) t :=
    hmono ⟨le_refl a, le_of_lt hab⟩ ⟨le_of_lt hat, le_of_lt htb⟩ hat
  have htb' : (fun x => f.eval x) t < (fun x => f.eval x) b :=
    hmono ⟨le_of_lt hat, le_of_lt htb⟩ ⟨le_of_lt hab, le_refl b⟩ htb
  exact sign_eq_of_between hta htb' hs

end Work.WilE4.CAD
