import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.LocalAnabelian.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalAnabelian.Kummer

open IntermediateField

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']

/-- **Key computation.**  If `b = a * c ^ p` in `kˣ` then every `p`-th root of `b`
in `K'` is the image of a `p`-th root of `a` under multiplication by the image of
`c`; hence `k(b^{1/p}) ⊆ k(a^{1/p})`.

The case `p = 0` is not exceptional: then `c ^ p = 1` and the equality
`a * c ^ p = b` reads `a = b`, while the argument below still applies because
`γ ^ 0 = 1 ≠ 0` for `γ = algebraMap k K' c`. -/
private theorem kummerField_le_of_mul_pow_eq (p : ℕ) {a b c : kˣ}
    (h : a * c ^ p = b) :
    kummerField (K' := K') p b ≤ kummerField (K' := K') p a := by
  rw [NK.LocalAnabelian.kummerField_le_iff]
  intro α hα
  -- The images of `a` and `b` are related by the `p`-th power of the image of `c`.
  have hbmap : algebraMap k K' (a : k) * (algebraMap k K' (c : k)) ^ p
      = algebraMap k K' (b : k) := by
    have hval : ((a * c ^ p : kˣ) : k) = (b : k) := congrArg (fun u : kˣ => (u : k)) h
    rw [← hval]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  set γ : K' := algebraMap k K' (c : k) with hγdef
  have hγ0 : γ ≠ 0 := (map_ne_zero (algebraMap k K')).mpr (Units.ne_zero c)
  -- Dividing the given `p`-th root of `b` by `γ` produces one of `a`.
  have hβ : (α * γ⁻¹) ^ p = algebraMap k K' (a : k) := by
    rw [mul_pow, inv_pow, hα, ← hbmap, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero p hγ0), mul_one]
  have hmem : α * γ⁻¹ ∈ kummerField (K' := K') p a :=
    NK.LocalAnabelian.mem_kummerField_of_pow_eq hβ
  have hγmem : γ ∈ kummerField (K' := K') p a := by
    rw [hγdef]; exact IntermediateField.algebraMap_mem _ _
  have hthis := IntermediateField.mul_mem (kummerField (K' := K') p a) hmem hγmem
  have heq : α * γ⁻¹ * γ = α := by rw [mul_assoc, inv_mul_cancel₀ hγ0, mul_one]
  rwa [heq] at hthis

theorem kummerField_eq_of_div_mem_powSubgroup {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] (p : ℕ) {a b : kˣ}
    (h : a⁻¹ * b ∈ powSubgroup p k) :
    kummerField (K' := K') p a = kummerField (K' := K') p b := by
  obtain ⟨c, hc⟩ :=
    MonoidHom.mem_range.mp (show a⁻¹ * b ∈ (powMonoidHom p : kˣ →* kˣ).range from h)
  rw [powMonoidHom_apply] at hc
  have hba : a * c ^ p = b := by rw [hc, mul_inv_cancel_left]
  have hab : b * (c⁻¹) ^ p = a := by
    rw [← hba]; group
  exact le_antisymm
    (kummerField_le_of_mul_pow_eq p (a := b) (b := a) (c := c⁻¹) hab)
    (kummerField_le_of_mul_pow_eq p hba)

end NK.LocalAnabelian.Kummer
