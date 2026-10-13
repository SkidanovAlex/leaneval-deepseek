import Mathlib

namespace Work.DSF1.Sheaf

open CategoryTheory Limits

universe v

set_option linter.style.haveILetI false

theorem isZero_homology_quotient_of_shortExact
    {A : Type*} [Category.{v} A] [Abelian A]
    (T : ShortComplex (CochainComplex A ℕ)) (hT : T.ShortExact)
    (h₂ : ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (T.X₂.homology n))
    (h₁ : ∀ n : ℕ, 1 < n → CategoryTheory.Limits.IsZero (T.X₁.homology n)) :
    ∀ n : ℕ, 0 < n → CategoryTheory.Limits.IsZero (T.X₃.homology n) := by
  intro n hn
  -- The connecting homomorphism of the long exact homology sequence at the adjacent
  -- degrees `n` and `n+1` (note that for cochain complexes the connecting map *raises*
  -- the degree): `δ : H^n(X₃) ⟶ H^{n+1}(X₁)`.
  have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := by
    rw [ComplexShape.up_Rel]
  -- Since `H^n(X₂) = 0`, exactness makes `δ` a monomorphism.
  haveI : Mono (hT.δ n (n + 1) hrel) := hT.mono_δ n (n + 1) hrel (h₂ n hn)
  -- Since `1 < n+1`, the target `H^{n+1}(X₁)` vanishes, hence so does `H^n(X₃)`.
  exact IsZero.of_mono (hT.δ n (n + 1) hrel) (h₁ (n + 1) (by omega))

end Work.DSF1.Sheaf
