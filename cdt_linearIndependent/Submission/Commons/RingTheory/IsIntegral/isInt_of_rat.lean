import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# A rational number that is integral over `ℤ` is an integer

If `x : ℂ` is (the image of) a rational number and is integral over `ℤ`, then it
is in fact the image of an integer: rational roots of monic integer polynomials
are integers (the rational root theorem), i.e. `ℤ` is integrally closed in `ℚ`.
-/

namespace Commons.RingTheory.IsIntegral

lemma isInt_of_rat {x : ℂ} (hrat : ∃ r : ℚ, (r : ℂ) = x) (hx : IsIntegral ℤ x) :
    ∃ n : ℤ, (n : ℂ) = x := by
  rcases hrat with ⟨r, rfl⟩
  -- Descent: an element of ℚ that is integral over ℤ when viewed in ℂ is
  -- already integral over ℤ in ℚ (integrality is preserved under the
  -- injective algebra map ℚ → ℂ).
  have hℚ : IsIntegral ℤ (r : ℚ) := by
    exact (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)).mp hx
  -- ℤ is integrally closed in ℚ = FractionRing ℤ, so the integral rational
  -- `r` is an integer.
  rcases (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hℚ with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  calc
    (n : ℂ) = ((n : ℚ) : ℂ) := by norm_num
    _ = (r : ℂ) := by exact congrArg (fun z : ℚ => (z : ℂ)) hn

end Commons.RingTheory.IsIntegral