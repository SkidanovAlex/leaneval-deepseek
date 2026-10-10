import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean half of the Kummer dictionary: involutions are real places

The node's hypothesis `hyinf` and its clause (C) say that the constructed `z` vanishes at every
involution of `G_K`.  By Artin–Schreier the involutions of `G_K` are exactly the conjugations at the
*real places* of `K`, so clause (C) is the arithmetic statement "`b` is positive at every real place
of `K`" — the archimedean half of the local data, the piece of the `p = 2` story which is empty for
odd `p` (there `H¹(ℝ, M) = 0`).

This file supplies the dictionary that turns the cochain condition into that arithmetic statement:

* `kummerChar_eq_zero_iff_apply_sqrt` — the Kummer character of `a` vanishes at `σ ∈ Gal(Ω/K)`
  exactly when `σ` fixes the chosen square root of `a`;
* `kummerChar_eq_zero_iff_exists_sqrt_fixed` — equivalently, exactly when *some* square root of `a`
  in `Ω` is fixed by `σ`, i.e. when `a` is a square in the fixed field `Ω^σ`;
* `nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed` — the same in the node's vocabulary
  (`nodeKummerCochar`, a subgroup `K.fixingSubgroup`), which is the form clause (C) needs.

For `σ = c` an involution, `Ω^c` is real closed with `Ω = Ω^c(i)` (Artin–Schreier), so "`a` is a
square in `Ω^c`" is exactly "`a > 0` at the real place of `c`"; the two lemmas above are the
formalised half of that translation, the real-closed-field reading being the classical extra input.
-/

open scoped Pointwise

namespace Work.SSGRoute

section ArchKummer

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- **The archimedean Kummer dictionary.**  The Kummer character of `a ∈ Kˣ` vanishes at
`σ ∈ Gal(Ω/K)` exactly when `σ` fixes the chosen square root of `a` in `Ω`. -/
theorem kummerChar_eq_zero_iff_apply_sqrt (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (a : Kˣ)
    (σ : Ω ≃ₐ[K] Ω) :
    kummerChar ζ hζ a σ = 0 ↔
      (σ : Ω → Ω) ((kummerSqrt (Ω := Ω) a : Ωˣ) : Ω) = ((kummerSqrt (Ω := Ω) a : Ωˣ) : Ω) := by
  rw [kummerChar_apply]
  refine ⟨fun h => ?_, fun h => kummerIdx_eq_zero_of_apply_eq 2 hζ a _ _ σ h⟩
  have hspec := kummerIdx_spec 2 hζ a (kummerSqrt (Ω := Ω) a) (kummerSqrt_pow (Ω := Ω) a) σ
  rw [h] at hspec
  have h1 : Work.Kummer.kummerRatio σ (kummerSqrt (Ω := Ω) a) = 1 := by
    rw [hspec, show Multiplicative.ofAdd (0 : ZMod 2) = (1 : Multiplicative (ZMod 2)) from rfl,
      map_one]
    simp
  have h1' : ((Work.Kummer.kummerRatio σ (kummerSqrt (Ω := Ω) a) : Ωˣ) : Ω) = 1 := by
    rw [h1, Units.val_one]
  rw [Work.Kummer.kummerRatio_coe] at h1'
  have hne : ((kummerSqrt (Ω := Ω) a : Ωˣ) : Ω) ≠ 0 := Units.ne_zero _
  exact (div_eq_one_iff_eq hne).mp h1'

/-- **The archimedean Kummer dictionary, square form.**  The Kummer character of `a` vanishes at `σ`
exactly when *some* square root of `a` in `Ω` is fixed by `σ` — that is, exactly when `a` is a
square in the fixed field `Ω^σ`.  For `σ = c` an involution this says that `a` is a square in the
real closed field `Ω^c`, i.e. that `a` is positive at the corresponding real place of `K`. -/
theorem kummerChar_eq_zero_iff_exists_sqrt_fixed (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (a : Kˣ)
    (σ : Ω ≃ₐ[K] Ω) :
    kummerChar ζ hζ a σ = 0 ↔
      ∃ y : Ω, (σ : Ω → Ω) y = y ∧ y ^ 2 = algebraMap K Ω (a : K) := by
  constructor
  · intro h
    exact ⟨(kummerSqrt (Ω := Ω) a : Ωˣ), (kummerChar_eq_zero_iff_apply_sqrt ζ hζ a σ).mp h,
      kummerSqrtVal_pow (Ω := Ω) a⟩
  · rintro ⟨y, hy, hy2⟩
    have hy0 : y ≠ 0 := by
      intro h
      have h' : algebraMap K Ω (a : K) = 0 := by
        rw [← hy2, h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      exact a.ne_zero ((algebraMap K Ω).injective (by simpa using h'))
    let yv : Ωˣ := Units.mk0 y hy0
    have hyv_pow : yv ^ 2 = Units.map (algebraMap K Ω) a := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.coe_map]
      exact hy2
    rw [kummerChar_apply,
      kummerIdx_congr 2 hζ a (kummerSqrt_pow (Ω := Ω) a) hyv_pow σ]
    refine kummerIdx_eq_zero_of_apply_eq 2 hζ a yv hyv_pow σ ?_
    show (σ : Ω → Ω) ((yv : Ωˣ) : Ω) = ((yv : Ωˣ) : Ω)
    rw [Units.val_mk0]
    exact hy

end ArchKummer

section ArchKummerNode

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

set_option maxHeartbeats 4000000 in
/-- **The archimedean Kummer dictionary in the node's vocabulary.**  For `b ∈ (↥K)ˣ` and
`c ∈ K.fixingSubgroup`, the node's Kummer cochain of `b` vanishes at `c` exactly when `c` fixes a
square root of `b` in `Ω` — equivalently, when `b` is a square in the fixed field `Ω^c`.

For `c` an involution (a real place of `K`) this is the arithmetic form of the node's clause (C):
`b` is positive at that real place.  In particular clause (C) is *equivalent* to a condition on `b`
alone, so that the Kummer core can be stated as a purely arithmetic existence statement about `b`. -/
theorem nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ 2)
    (b : (↥K)ˣ) (c : Ω ≃ₐ[k] Ω) (hc : c ∈ K.fixingSubgroup) :
    nodeKummerCochar K ζ hζK hζ b c = 0 ↔
      ∃ y : Ω, ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ : Ω ≃ₐ[↥K] Ω) y = y ∧
        y ^ 2 = algebraMap ↥K Ω (b : ↥K) := by
  have hpt : nodeKummerCochar K ζ hζK hζ b c =
      kummerCochar K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b c := rfl
  have hmain := kummerChar_eq_zero_iff_exists_sqrt_fixed ⟨ζ, hζK⟩
    (isPrimitiveRoot_subtype_of_mem hζK hζ) b
    ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩)
  simpa only [hpt, kummerCochar_apply K ⟨ζ, hζK⟩ (isPrimitiveRoot_subtype_of_mem hζK hζ) b hc]
    using hmain

/-- **Clause (C) of the node, in arithmetic form.**  The Kummer cochain of `b` vanishes at every
involution of `G_K` exactly when `b` is a square in the fixed field of every involution — i.e. when
`b` is positive at every real place of `K` (Artin–Schreier: the involutions of `G_K` are the
conjugations at the real places, so this is the "totally positive" condition on `b`). -/
theorem nodeKummerCochar_eq_zero_on_involutions_iff (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζK : ζ ∈ K) (hζ : IsPrimitiveRoot ζ 2)
    (b : (↥K)ˣ) :
    (∀ c : Ω ≃ₐ[k] Ω, c ∈ K.fixingSubgroup → c ^ 2 = 1 →
        nodeKummerCochar K ζ hζK hζ b c = 0) ↔
      (∀ c : Ω ≃ₐ[k] Ω, ∀ hc : c ∈ K.fixingSubgroup, c ^ 2 = 1 →
        ∃ y : Ω, ((IntermediateField.fixingSubgroupEquiv K) ⟨c, hc⟩ : Ω ≃ₐ[↥K] Ω) y = y ∧
          y ^ 2 = algebraMap ↥K Ω (b : ↥K)) := by
  constructor
  · intro H c hc hc2
    exact (nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed K ζ hζK hζ b c hc).mp (H c hc hc2)
  · intro H c hc hc2
    exact (nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed K ζ hζK hζ b c hc).mpr (H c hc hc2)

end ArchKummerNode

end Work.SSGRoute
