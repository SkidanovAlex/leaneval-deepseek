import Mathlib
import Submission.Work.FIArea2.coprime_gnorm_absDelta
import Submission.Work.FIArea2.coprime_re_absDelta
import Submission.Work.FIArea2.coprime_residue_absDelta
import Submission.Work.FIArea2.G8Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.FIArea2

/-- **Solving a linear congruence with an invertible coefficient.**  If `D ≠ 0` and
`(g,D) = 1` then for every integer `r` there is a natural number `a` with
`a·g ≡ r (mod D)`.  The solution is the canonical representative in `[0,D)` of the element
`r·g⁻¹` of `ZMod D`, where `g` is inverted using `ZMod.unitOfCoprime`. -/
lemma exists_mul_modEq (D : ℕ) (hD : D ≠ 0) (g : ℕ) (r : ℤ) (hcop : Nat.Coprime g D) :
    ∃ a : ℕ, (a : ℤ) * (g : ℤ) ≡ r [ZMOD (D : ℤ)] := by
  haveI : NeZero D := ⟨hD⟩  -- instance for `ZMod.natCast_zmod_val`
  refine ⟨((r : ZMod D) * (↑((ZMod.unitOfCoprime g hcop)⁻¹) : ZMod D)).val, ?_⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_zmod_val]
  rw [← ZMod.coe_unitOfCoprime g hcop]
  have hval : (↑((ZMod.unitOfCoprime g hcop)⁻¹) : ZMod D)
      * (↑(ZMod.unitOfCoprime g hcop) : ZMod D) = 1 := by
    rw [← Units.val_mul]; simp
  rw [mul_assoc, hval, mul_one]

/-- **The residue `a = z₂/z₁ (mod |Δ|)` of (6.6), with all its properties.**  For a coprime pair of
coprime *primitive* Gaussian integers with `Δ = Im(z̄₁z₂) ≠ 0` there is `a : ℕ` with

* `(|z₁|², |Δ|) = 1` (so that `|z₁|²` is invertible modulo `|Δ|`),
* `(Re(z̄₁z₂), |Δ|) = 1` (so that `(a,|Δ|) = 1` follows),
* `a·|z₁|² ≡ Re(z̄₁z₂) (mod |Δ|)` — i.e. `a` is the residue of `z₂/z₁ = Re(z̄₁z₂)·|z₁|²⁻¹` (6.6),
* `(a, |Δ|) = 1`.

The three coprimality statements are exactly `Work.FIArea2.coprime_gnorm_absDelta`,
`Work.FIArea2.coprime_re_absDelta` and `Work.FIArea2.coprime_residue_absDelta`; only the definition
of `a` (as the canonical representative of `Re(z̄₁z₂)·(|z₁|²)⁻¹` in `ZMod |Δ|`) and the congruence
have to be produced. -/
theorem exists_residue_data (z1 z2 : GaussianInt)
    (hcop : IsCoprime z1 z2) (hp1 : IsCoprime z1 (star z1)) (hp2 : IsCoprime z2 (star z2))
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    ∃ a : ℕ,
      Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) ∧
      Nat.Coprime ((star z1 * z2).re).natAbs (Work.FIPlan.absDelta z1 z2) ∧
      (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)] ∧
      Nat.Coprime a (Work.FIPlan.absDelta z1 z2) := by
  have hgnorm := coprime_gnorm_absDelta hcop hp1
  have hre := coprime_re_absDelta hcop hp1 hp2
  obtain ⟨a, ha⟩ := exists_mul_modEq (Work.FIPlan.absDelta z1 z2) hD
    (Work.FIPlan.gnorm z1) (star z1 * z2).re hgnorm
  exact ⟨a, hgnorm, hre, ha, coprime_residue_absDelta ha hre⟩

end Work.FIArea2
