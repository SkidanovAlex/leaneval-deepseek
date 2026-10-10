import Mathlib
import Submission.Work.MotK.TGen.ZTwistDivGeomDefs
import Submission.Work.MotK.TGen.ZpgI4NormalForm

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

/-- **The saturation of the chart ideal `zpgI4` by the denominator `zpgW4` lands in the radical.**

The five chart quadrics `zpgQ a b h k` cut out the affine chart of the `h`-twisted Klein curve
and form a Gröbner basis for the (grevlex) monomial order with leading monomials
`y₂y₃, y₂², y₁y₂, y₁², y₃²` (module `ZpgI4NormalForm`), with a `K`-linear normal form `NF` whose
kernel is `zpgI4`.  The content of the statement is that `zpgW4` is a non-zero-divisor modulo
`zpgI4`: if `zpgW4 * v ∈ zpgI4` then `NF (zpgW4 * v) = 0`, and since
`NF (zpgW4 * v) = NF (zpgW4 * NF v)` with `NF v` in the standard span, the normal form `NF v`
must vanish, whence `v ∈ zpgI4`.  The `n`-th power case follows by induction. -/
theorem ZpgI4SatW (K : Type) [Field K] (a b h : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    ∀ u : MvPolynomial (Fin 4) K,
      (∃ n : ℕ, (Work.MotK.TGen.zpgW4 a b h) ^ n * u ∈ Work.MotK.TGen.zpgI4 a b h) →
        u ∈ Ideal.radical (Work.MotK.TGen.zpgI4 a b h) := by
  intro u hu
  obtain ⟨m, NF, hunit, hd0, hd1, hd2, hd3, hd4, hsub, hkill, hsupp, hkey⟩ :=
    ZpgI4NormalForm K a b h ha hb hh
  -- `zpgW4` is a non-zero-divisor modulo `zpgI4`.
  have hW : ∀ v : MvPolynomial (Fin 4) K,
      zpgW4 a b h * v ∈ zpgI4 a b h → v ∈ zpgI4 a b h := by
    intro v hv
    have h1 : NF (zpgW4 a b h * v) = 0 := hkill _ hv
    have h2 : NF (zpgW4 a b h * v) = NF (zpgW4 a b h * NF v) := by
      have hmem : zpgW4 a b h * (v - NF v) ∈ zpgI4 a b h :=
        Ideal.mul_mem_left _ _ (hsub v)
      have hz : NF (zpgW4 a b h * (v - NF v)) = 0 := hkill _ hmem
      have hlin : NF (zpgW4 a b h * (v - NF v))
          = NF (zpgW4 a b h * v) - NF (zpgW4 a b h * NF v) := by
        rw [mul_sub, map_sub]
      rw [hlin] at hz
      exact sub_eq_zero.mp hz
    have h3 : NF (zpgW4 a b h * NF v) = 0 := by rw [← h2]; exact h1
    have h4 : NF v = 0 := by
      by_contra hne
      exact hkey (NF v) (hsupp v) hne h3
    have hv' := hsub v
    rw [h4, sub_zero] at hv'
    exact hv'
  -- descent on the exponent `n`
  have hpow : ∀ n : ℕ, (zpgW4 a b h) ^ n * u ∈ zpgI4 a b h → u ∈ zpgI4 a b h := by
    intro n
    induction n with
    | zero => intro hk; simpa using hk
    | succ k ih =>
        intro hk
        have hkk : (zpgW4 a b h) ^ k * u ∈ zpgI4 a b h := by
          apply hW
          have heq : zpgW4 a b h * ((zpgW4 a b h) ^ k * u)
              = (zpgW4 a b h) ^ (k + 1) * u := by
            rw [pow_succ]; ring
          rw [heq]; exact hk
        exact ih hkk
  obtain ⟨n0, hn0⟩ := hu
  exact Ideal.le_radical (hpow n0 hn0)

end Work.MotK.TGen
