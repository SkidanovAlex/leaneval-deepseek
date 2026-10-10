import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.AbsoluteKummer.Hilbert90.exists_div_of_isCrossedHom
import Submission.Work.AbsoluteKummer.Kummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Surjectivity of the Kummer map

For a field `k` with a primitive `n`-th root of unity `ζ ∈ k`, the Kummer map

`kummerMap hζ : kˣ/(kˣ)^n →* H¹(G_k, μ_n)`

is surjective: every continuous `1`-cocycle `c : G_k → μ_n(k̄)` is the Kummer cocycle of some
`x : kˣ`.

The proof is the classical one.  Since `k` contains all `n`-th roots of unity of `k̄` (they are
the powers of `ζ`), a cocycle `c` with values in `μ_n(k̄)` is a crossed homomorphism with values
in `k̄ˣ` for the ordinary Galois action, and it is locally constant; Hilbert's Theorem 90 in the
absolute form (`Work.AbsoluteKummer.Hilbert90.exists_div_of_isCrossedHom`) produces `b : k̄ˣ`
with `σ b / b = c σ` for all `σ`.  Then `b ^ n` is fixed by `G_k`, hence `b ^ n = x` for a unique
`x : kˣ`, and `b` is an `n`-th root of `x`, so `c` is the Kummer cocycle of `x`.

The main auxiliary result is `Work.AbsoluteKummer.Kummer.exists_kummerCocycle_eq`.
-/

namespace Work.AbsoluteKummer.Kummer

open scoped Classical Topology

noncomputable section

variable {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {n : ℕ} [NeZero n] {ζ : k}

/-- The underlying function `G_k → k̄ˣ → μ_n ⊂ k̄ˣ ↪ k̄ˣ` **:**

Given `c : Z¹(G_k, μ_n(k̄))`, the map `σ ↦ (c σ : k̄ˣ)` (forgetting that the values are roots
of unity) is a crossed homomorphism `G_k → k̄ˣ`.

**Every continuous `1`-cocycle of `G_k` with values in `μ_n(k̄)` is the Kummer cocycle `σ ↦ σ α / α`
of some `x : kˣ`.**  Equivalently, the map `x ↦ (σ ↦ σ α/α)` (with `α ^ n = x`) from `kˣ` to
`Z¹(G_k, μ_n(k̄))` is surjective. -/
theorem exists_kummerCocycle_eq (hζ : IsPrimitiveRoot ζ n)
    (c : Z1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) :
    ∃ x : kˣ, kummerCocycle hζ x = c := by
  classical
  let f : G k → (AlgebraicClosure k)ˣ := fun σ =>
    ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) σ) :
      rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ)
  have hf_cross : ∀ σ τ : G k, f (σ * τ) = f σ * algEquivUnitsMap k σ (f τ) := by
    intro σ τ
    have hc := isCrossedHom_of_mem_Z1 c.2 σ τ
    have h1 : Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) (σ * τ)) =
        Additive.toMul (σ • (c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) τ) *
          Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) σ) := by
      rw [hc, toMul_add]
    have h2 : ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) (σ * τ)) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ)
        = algEquivUnitsMap k σ ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) τ) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ)
          * ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) σ) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) := by
      have h2a := congrArg (fun u : rootsOfUnity n (AlgebraicClosure k) => (u : (AlgebraicClosure k)ˣ)) h1
      rw [Subgroup.coe_mul] at h2a
      rw [h2a, addRootsOfUnity_smul_toMul_val]
    have h3 : algEquivUnitsMap k σ ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) τ) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ)
        = ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) τ) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) :=
      algEquivUnitsMap_eq_self_of_mem_rootsOfUnity k hζ σ (Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) τ)).2
    show ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) (σ * τ)) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) = _
    rw [h2, h3, mul_comm]
  have hf_lc : Work.AbsoluteKummer.IsLocallyConstant f := by
    intro σ
    obtain ⟨U, hU, hσU, hcU⟩ := isLocallyConstant_of_mem_Z1 c.2 σ
    refine ⟨U, hU, hσU, fun τ hτ => ?_⟩
    show ((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) τ) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ) = _
    rw [hcU τ hτ]
  obtain ⟨b, hb⟩ := Hilbert90.exists_div_of_isCrossedHom (k := k) f hf_cross hf_lc
  have hroot : ∀ σ : G k, (f σ : AlgebraicClosure k) ^ n = 1 := by
    intro σ
    exact (mem_rootsOfUnity' n (M := AlgebraicClosure k)
      (((Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) σ)) : rootsOfUnity n (AlgebraicClosure k)) : (AlgebraicClosure k)ˣ)).mp
      (Additive.toMul ((c : G k → Additive (rootsOfUnity n (AlgebraicClosure k))) σ)).2
  have hfix : ∀ σ : G k, σ (((b ^ n : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)) =
      ((b ^ n : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by
    intro σ
    have hb' : algEquivUnitsMap k σ b = f σ * b := by
      rw [hb σ, div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]
    calc σ (((b ^ n : (AlgebraicClosure k)ˣ) : AlgebraicClosure k))
        = σ ((b : AlgebraicClosure k)) ^ n := by rw [Units.val_pow_eq_pow_val, map_pow]
      _ = ((algEquivUnitsMap k σ b : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) ^ n := by
            rw [algEquivUnitsMap_coe]
      _ = (((f σ * b : (AlgebraicClosure k)ˣ)) : AlgebraicClosure k) ^ n := by rw [hb']
      _ = ((f σ : AlgebraicClosure k) * (b : AlgebraicClosure k)) ^ n := by rw [Units.val_mul]
      _ = (f σ : AlgebraicClosure k) ^ n * (b : AlgebraicClosure k) ^ n := mul_pow _ _ n
      _ = 1 * (b : AlgebraicClosure k) ^ n := by rw [hroot σ]
      _ = ((b ^ n : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by
            rw [Units.val_pow_eq_pow_val, one_mul]
  obtain ⟨a₀, ha₀⟩ := Set.mem_range.mp ((InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k) (K := AlgebraicClosure k)
      ((b ^ n : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)).mpr hfix)
  have ha₀0 : a₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha₀
    exact (Units.ne_zero (b ^ n)) ha₀.symm
  let a : kˣ := Units.mk0 a₀ ha₀0
  have hmap : Units.map (algebraMap k (AlgebraicClosure k)) a = b ^ n := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_mk0]
    exact ha₀
  have hp1 : (b : AlgebraicClosure k) ^ n = algebraMap k (AlgebraicClosure k) (a : k) := by
    have h := congrArg (fun u : (AlgebraicClosure k)ˣ => (u : AlgebraicClosure k)) hmap
    rw [Units.coe_map, Units.val_pow_eq_pow_val] at h
    exact h.symm
  have hratio : ∀ σ : G k, Work.Kummer.kummerRatio σ (kummerRootUnit (n := n) a) = f σ := by
    intro σ
    rw [Work.Kummer.kummerRatio_congr hζ (a := a) hp1 (kummerRootUnit_pow_val (n := n) a) σ]
    exact (hb σ).symm
  refine ⟨a, ?_⟩
  refine Subtype.ext (funext fun σ => Additive.ext (Subtype.ext ?_))
  rw [kummerCocycle_coe, kummerCocycleFun_toMul, hratio σ]

theorem kummerMap_surjective {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {n : ℕ} [NeZero n] {ζ : k} (hζ : IsPrimitiveRoot ζ n) : Function.Surjective (Work.AbsoluteKummer.kummerMap hζ) := by
  classical
  intro y
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((B1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))).comap
      (Z1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))).subtype)
    (Multiplicative.toAdd y)
  obtain ⟨a, ha⟩ := exists_kummerCocycle_eq (k := k) hζ c
  refine ⟨QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup n kˣ) a, ?_⟩
  rw [kummerMap_mk]
  show Multiplicative.ofAdd (H1π (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))
      (kummerCocycle hζ a)) = y
  rw [ha]
  exact congrArg Multiplicative.ofAdd hc

end

end Work.AbsoluteKummer.Kummer
