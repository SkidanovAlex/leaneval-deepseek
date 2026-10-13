import Mathlib
import Submission.Work.WilE4.Poly
import Submission.Work.WilE4.CAD.realized_from_pieces
import Submission.Work.WilE4.CAD.vanish_persist_minor
import Submission.Work.WilE4.CAD.seq_closed_minor

namespace Work.WilE4.CAD

/-- **Type constancy of a family of polynomials whose projection datum is the sign pattern of all
Sylvester submatrix determinants.**

The two mathematical halves are proved separately:
* `vanish_persist_minor` — persistence of the vanishing pattern at a witness (this is the "openness"
  half; it is what the *non-maximal* Sylvester minors — the subresultant/Lazard data — are for);
* `seq_closed_minor` — sequential closedness of the realised-sign-vector set.

They are glued by `realized_const_from_pieces`: the set of parameters realising a fixed sign vector
is clopen in the preconnected `C`, hence either empty or all of `C`. -/
theorem syl_minor_type_const {m k : ℕ} (P : Fin k → MvPolynomial (Fin (m + 1)) ℝ) (D : ℕ)
    (hD : ∀ i : Fin k, (P i).degreeOf (Fin.last m) ≤ D)
    (hclosed : ∀ i : Fin k, ∃ j : Fin k, P j = MvPolynomial.pderiv (Fin.last m) (P i))
    (C : Set (Fin m → ℝ)) (hC : IsPreconnected C)
    (hcoeff : ∀ i : Fin k, ∀ j : ℕ, j ≤ D → ∀ x ∈ C, ∀ x' ∈ C,
      SignType.sign ((Work.WilE4.spec (P i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (P i) x').coeff j))
    (hmin : PscSignConst P C)
    (v : Fin k → SignType) :
    (∀ x ∈ C, ∃ t : ℝ, ∀ i, SignType.sign ((Work.WilE4.spec (P i) x).eval t) = v i) ∨
      (∀ x ∈ C, ¬ ∃ t : ℝ, ∀ i, SignType.sign ((Work.WilE4.spec (P i) x).eval t) = v i) :=
  realized_const_from_pieces P C hC
    (fun x₀ hx₀ t₀ ε hε =>
      vanish_persist_minor P D hD hclosed C hcoeff hmin hx₀ t₀ hε)
    (fun v' x hxC x₀ hx₀ hlim hv =>
      seq_closed_minor P D hD hclosed C hcoeff hmin v' x hxC hx₀ hlim hv)
    v

end Work.WilE4.CAD
