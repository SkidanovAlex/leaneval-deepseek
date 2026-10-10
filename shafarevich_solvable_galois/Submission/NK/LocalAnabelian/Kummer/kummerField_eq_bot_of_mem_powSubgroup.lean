import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Submission.NK.LocalAnabelian.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalAnabelian.Kummer

open IntermediateField

/-- **Every `p`-th root of unity in `K'` lies in `k`**, when `k` contains a
primitive `p`-th root of unity `ζ`.

Indeed `μ_p(K')` is a group of exponent `p` inside the multiplicative group of
the field `K'`, so `X ^ p - 1` has at most `p` roots there; on the other hand it
contains the `p` distinct powers of the image of `ζ`. -/
theorem exists_pow_eq_algebraMap_of_pow_eq_one {k K' : Type*} [Field k] [Field K']
    [Algebra k K'] (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p) {u : K'}
    (hu : u ^ p = 1) : ∃ m : ℕ, algebraMap k K' (ζ ^ m) = u := by
  have hne : NeZero p := ⟨hp.ne_zero⟩
  have hζ' : IsPrimitiveRoot (algebraMap k K' ζ) p :=
    hζ.map_of_injective (algebraMap k K').injective
  obtain ⟨m, -, hm⟩ := hζ'.eq_pow_of_pow_eq_one hu
  exact ⟨m, by rw [map_pow, hm]⟩

theorem kummerField_eq_bot_of_mem_powSubgroup {k K' : Type*} [Field k] [Field K'] [Algebra k K']
    (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p) {a : kˣ}
    (ha : a ∈ powSubgroup p k) :
    kummerField (K' := K') p a = ⊥ := by
  -- write `a = c ^ p`
  obtain ⟨c, hc⟩ :=
    MonoidHom.mem_range.mp (show a ∈ (powMonoidHom p : kˣ →* kˣ).range from ha)
  rw [powMonoidHom_apply] at hc
  refine le_antisymm ?_ bot_le
  rw [kummerField_le_iff]
  intro α hα
  rw [IntermediateField.mem_bot]
  -- the image `γ` of `c` in `K'` is a `p`-th root of the image of `a`, and non-zero
  set γ : K' := algebraMap k K' (c : k) with hγdef
  have hγ0 : γ ≠ 0 := by
    rw [hγdef]
    exact (map_ne_zero (algebraMap k K')).mpr (Units.ne_zero c)
  have hγpow : γ ^ p = algebraMap k K' (a : k) := by
    have hval : ((c ^ p : kˣ) : k) = (a : k) := congrArg (fun u : kˣ => (u : k)) hc
    rw [hγdef, ← hval, Units.val_pow_eq_pow_val, map_pow]
  have hmem0 : algebraMap k K' (a : k) ≠ 0 := by
    rw [← hγpow]
    exact pow_ne_zero p hγ0
  -- hence `α / γ` is a `p`-th root of unity in `K'`, so a power of `ζ`
  have hroot : (α * γ⁻¹) ^ p = 1 := by
    rw [mul_pow, inv_pow, hα, hγpow, mul_inv_cancel₀ hmem0]
  obtain ⟨m, hm⟩ := exists_pow_eq_algebraMap_of_pow_eq_one p hp hζ hroot
  -- so `α = ζ ^ m * γ` lies in the image of `k`
  refine ⟨ζ ^ m * (c : k), ?_⟩
  rw [map_mul, hm, ← hγdef, mul_assoc, inv_mul_cancel₀ hγ0, mul_one]

end NK.LocalAnabelian.Kummer
