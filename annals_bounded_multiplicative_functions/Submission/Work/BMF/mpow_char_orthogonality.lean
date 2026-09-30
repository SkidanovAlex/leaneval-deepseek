import Mathlib
import Submission.Work.BMF.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped ComplexConjugate

/-- For a complex Dirichlet character `ψ` of conductor `q`, the `m`-th power evaluates at a
unit `A` as the value of `ψ` at `A ^ m`. -/
lemma pow_apply_unit (q m : ℕ) (ψ : DirichletCharacter ℂ q) (A : (ZMod q)ˣ) :
    (ψ ^ m) (A : ZMod q) = ψ ((A ^ m : (ZMod q)ˣ) : ZMod q) := by
  rw [MulChar.pow_apply_coe, Units.val_pow_eq_pow_val]
  exact (map_pow ψ (A : ZMod q) m).symm

/-- For `A, B` units modulo `q`, orthogonality of the `m`-th powers of the characters mod `q`:
`Σ_ψ (ψ^m)(A) · star((ψ^m)(B)) = φ(q) · 1_{A^m = B^m}`.
Indeed for units `(ψ^m)(A)·star((ψ^m)(B)) = ψ((A/B)^m)` (values on units are roots of unity), and
the standard orthogonality `Σ_ψ ψ(x) = φ(q)·1_{x=1}` from Chen's `sum_char_mul_conj`
(`Σ_χ χ(a)·conj χ(b) = φ(q)·1_{a=b}`) gives the claim.  This is the correct form of the MRTTZ
character identity, whose `Σ_{χ^m = χ₀}` should be read as the `m`-th powers `Ĝ^m`. -/
theorem mpow_char_orthogonality (q m : ℕ) [NeZero q] (A B : (ZMod q)ˣ) :
    (∑ ψ : DirichletCharacter ℂ q, (ψ ^ m) (A : ZMod q) * star ((ψ ^ m) (B : ZMod q)))
      = (q.totient : ℂ) * (if A ^ m = B ^ m then 1 else 0) := by
  classical
  have hterm : ∀ ψ : DirichletCharacter ℂ q,
      (ψ ^ m) (A : ZMod q) * star ((ψ ^ m) (B : ZMod q))
        = (ψ ((A ^ m : (ZMod q)ˣ) : ZMod q)) *
            conj (ψ ((B ^ m : (ZMod q)ˣ) : ZMod q)) := by
    intro ψ
    rw [pow_apply_unit, pow_apply_unit, Complex.star_def]
  trans ∑ ψ : DirichletCharacter ℂ q,
      (ψ ((A ^ m : (ZMod q)ˣ) : ZMod q)) * conj (ψ ((B ^ m : (ZMod q)ˣ) : ZMod q))
  · exact Finset.sum_congr rfl (fun ψ _ => hterm ψ)
  · rw [Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj q ((A ^ m).isUnit)
        ((B ^ m : (ZMod q)ˣ) : ZMod q)]
    simp only [Units.val_inj]
    split_ifs <;> ring

end Work.BMF
