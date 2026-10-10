import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.NK.UchidaKummer.Defs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.grunwald_kummer_idx
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Vocabulary for `Work.SSGRoute.grunwald_surjective_two`

The global Kummer character of a unit `a ∈ Kˣ` (relative to a square root chosen in `Ω`), as a
function on `Gal(Ω/K)`, and the local `2`-power class of `a` at a prime `𝔭` of `K`.

The main lemma `Work.SSGRoute.grunwald_surjective_two` is proved by combining

* `Work.SSGRoute.kummerChar_eq_iff_local_powClass` — the global Kummer character restricted to a
  decomposition group is the same for `a` and `b` iff `a/b` is a local square (equivalently, the
  two have the same local `2`-power class);
* `Work.SSGRoute.natCard_localChars` — the number of continuous additive characters of the
  decomposition group equals the number of local `2`-power classes;
* `NK.UchidaKummer.IsKummerSurjective` — the global Kummer local surjection.
-/

namespace Work.SSGRoute

open scoped Pointwise

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- A square root in `Ω` of `a ∈ Kˣ`. -/
theorem exists_sqrt_val (a : Kˣ) : ∃ γ : Ω, γ ^ 2 = algebraMap K Ω (a : K) := by
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) (by norm_num : 0 < 2)
  exact ⟨γ, hγ⟩

/-- A chosen square root in `Ω` of `a ∈ Kˣ`. -/
noncomputable def kummerSqrtVal (a : Kˣ) : Ω := Classical.choose (exists_sqrt_val (Ω := Ω) a)

theorem kummerSqrtVal_pow (a : Kˣ) : (kummerSqrtVal (Ω := Ω) a) ^ 2 = algebraMap K Ω (a : K) :=
  Classical.choose_spec (exists_sqrt_val (Ω := Ω) a)

theorem kummerSqrtVal_ne_zero (a : Kˣ) : kummerSqrtVal (Ω := Ω) a ≠ 0 := by
  intro h
  have h2 := kummerSqrtVal_pow (Ω := Ω) a
  rw [h, zero_pow (by norm_num : 2 ≠ 0)] at h2
  exact a.ne_zero ((algebraMap K Ω).injective (h2.symm.trans (map_zero (algebraMap K Ω)).symm))

/-- A chosen square root in `Ωˣ` of `a ∈ Kˣ`. -/
noncomputable def kummerSqrt (a : Kˣ) : Ωˣ :=
  Units.mk0 (kummerSqrtVal (Ω := Ω) a) (kummerSqrtVal_ne_zero (Ω := Ω) a)

theorem kummerSqrt_pow (a : Kˣ) : kummerSqrt (Ω := Ω) a ^ 2 =
    Units.map (algebraMap K Ω) a := by
  refine Units.ext ?_
  simp only [kummerSqrt, Units.val_mk0, Units.val_pow_eq_pow_val, Units.coe_map]
  exact kummerSqrtVal_pow (Ω := Ω) a

/-- **The global Kummer character** of `a ∈ Kˣ` at a square root of unity `ζ ∈ K` of order `2`:
the class function `σ ↦ (σ √a)/√a`, encoded through `Work.SSGRoute.kummerIdx`. -/
noncomputable def kummerChar (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (a : Kˣ) :
    (Ω ≃ₐ[K] Ω) → ZMod 2 :=
  fun σ => kummerIdx 2 hζ a (kummerSqrt (Ω := Ω) a) (kummerSqrt_pow (Ω := Ω) a) σ

@[simp] theorem kummerChar_apply (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (a : Kˣ)
    (σ : Ω ≃ₐ[K] Ω) :
    kummerChar ζ hζ a σ =
      kummerIdx 2 hζ a (kummerSqrt (Ω := Ω) a) (kummerSqrt_pow (Ω := Ω) a) σ := rfl

/-- **Additivity** of the Kummer character. -/
theorem kummerChar_mul_apply (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (a : Kˣ)
    (σ τ : Ω ≃ₐ[K] Ω) :
    kummerChar ζ hζ a (σ * τ) = kummerChar ζ hζ a σ + kummerChar ζ hζ a τ :=
  kummerIdx_mul_apply 2 hζ a _ _ σ τ

/-- The Kummer character of `a` is additive in `a`. -/
theorem kummerChar_mul (ζ : K) (hζ : IsPrimitiveRoot ζ 2) (a b : Kˣ) :
    kummerChar (Ω := Ω) ζ hζ (a * b) = kummerChar (Ω := Ω) ζ hζ a + kummerChar (Ω := Ω) ζ hζ b := by
  funext σ
  rw [Pi.add_apply, kummerChar_apply, kummerChar_apply, kummerChar_apply]
  have hcd : (kummerSqrt (Ω := Ω) a * kummerSqrt (Ω := Ω) b) ^ 2 =
      Units.map (algebraMap K Ω) (a * b) := by
    rw [mul_pow, kummerSqrt_pow (Ω := Ω) a, kummerSqrt_pow (Ω := Ω) b, map_mul]
  rw [kummerIdx_congr 2 hζ (a * b) (kummerSqrt_pow (Ω := Ω) (a * b)) hcd σ]
  exact kummerIdx_mul 2 hζ a b (kummerSqrt (Ω := Ω) a) (kummerSqrt (Ω := Ω) b)
    (kummerSqrt_pow (Ω := Ω) a) (kummerSqrt_pow (Ω := Ω) b) hcd σ

end

/-- A continuous additive character of a subgroup `H ≤ Γ` (with `Γ` a topological group): an
additive map `H → ZMod 2` that is constant on the cosets of an open subgroup. -/
def IsContAddChar {Γ : Type*} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ)
    (f : Γ → ZMod 2) : Prop :=
  (∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + f h) ∧
    (∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ ∀ g ∈ H, ∀ u ∈ U, u ∈ H → f (g * u) = f g)

end Work.SSGRoute
