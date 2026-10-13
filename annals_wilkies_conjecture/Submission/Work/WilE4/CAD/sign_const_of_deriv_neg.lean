import Mathlib
import Submission.Work.WilE4.CAD.sign_eq_of_between

namespace Work.WilE4.CAD

theorem sign_const_of_deriv_neg {f : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Set.Ioo a b, (f.derivative).eval t < 0)
    (hs : SignType.sign (f.eval a) = SignType.sign (f.eval b)) :
    ∀ t ∈ Set.Ioo a b, SignType.sign (f.eval t) = SignType.sign (f.eval a) := by
  -- `f` is strictly antitone on `[a, b]`, so `f.eval t` is squeezed strictly
  -- between `f.eval b` and `f.eval a` for any `t ∈ (a, b)`.
  have hanti : StrictAntiOn (fun x => f.eval x) (Set.Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) (Polynomial.continuousOn f)
    intro x hx
    rw [interior_Icc] at hx
    rw [Polynomial.deriv]
    exact h x hx
  intro t ht
  have htI : t ∈ Set.Icc a b := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have haI : a ∈ Set.Icc a b := ⟨le_refl a, le_of_lt hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨le_of_lt hab, le_refl b⟩
  have hbt : f.eval b < f.eval t := hanti htI hbI ht.2
  have hta : f.eval t < f.eval a := hanti haI htI ht.1
  exact (sign_eq_of_between hbt hta hs.symm).trans hs.symm

end Work.WilE4.CAD
