import Mathlib
import Submission.Work.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

/-- The algebra norm of a finite Galois extension is invariant under the action of the
Galois group: `N_{L/K}(σ x) = N_{L/K}(x)` for every `σ : Gal(L/K)`.

Indeed `N_{L/K}(x)` is the product of the conjugates `τ x` over `τ : Gal(L/K)`, and right
multiplication `τ ↦ τ * σ` is a bijection of the Galois group. -/
theorem norm_algEquiv_apply {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L) (x : L) :
    Algebra.norm K (σ x) = Algebra.norm K x := by
  apply FaithfulSMul.algebraMap_injective K L
  rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms]
  refine Fintype.prod_equiv (Equiv.mulRight σ) (fun g : Gal(L/K) => g (σ x))
    (fun g : Gal(L/K) => g x) (fun g => ?_)
  change g (σ x) = (g * σ) x
  rw [AlgEquiv.mul_apply]

/-- **A Kummer-theoretic divisibility.** Let `L/K` be a finite Galois extension of degree `n`,
with `K` containing a primitive `n`-th root of unity `ζ`. Let `η : Lˣ` have norm `ζ`, let
`μ : Lˣ` and `σ : Gal(L/K)` satisfy `σ μ = η ^ n * μ`, and let `c : Lˣ` with `μ ^ d = c ^ n`.
Then `n ∣ d`.

The point is that `σ` acts on `c` by multiplication by an `n`-th root of unity: passing to the
`n`-th powers of `σ μ = η ^ n μ` and using `μ ^ d = c ^ n` gives
`(σ c) ^ n = η ^ (n * d) c ^ n`, so `θ := σ c / (c η ^ d)` satisfies `θ ^ n = 1`. Since `L`
contains the primitive `n`-th root `ζ`, `θ` is a power of `ζ`, hence fixed by `Gal(L/K)` and of
norm `1`. Taking norms in `σ c = θ η ^ d c`, and using that the norm is Galois-invariant, yields
`N(c) = ζ ^ d * N(c)`; cancelling `N(c) ≠ 0` gives `ζ ^ d = 1`, i.e. `n ∣ d`. -/
theorem dvd_of_pow_eq_nth_pow {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hn : Module.finrank K L = n)
    (η : Lˣ) (hη : Algebra.norm K (η : L) = ζ)
    {μ : Lˣ} {σ : Gal(L/K)} (hμ : (σ : L ≃ₐ[K] L) (μ : L) = (η : L) ^ n * (μ : L))
    {d : ℕ} {c : Lˣ} (hc : μ ^ d = c ^ n) : n ∣ d := by
  -- Coerce the unit equation `μ ^ d = c ^ n` to `L`.
  have hcL : (μ : L) ^ d = (c : L) ^ n := by
    have := congrArg (fun u : Lˣ => (u : L)) hc
    simpa using this
  -- Pass to `n`-th powers in `σ μ = η ^ n * μ` and use `μ ^ d = c ^ n`.
  have hstep : ((σ : L ≃ₐ[K] L) (c : L)) ^ n = (η : L) ^ (n * d) * (c : L) ^ n := by
    calc ((σ : L ≃ₐ[K] L) (c : L)) ^ n
        = (σ : L ≃ₐ[K] L) ((c : L) ^ n) := by rw [map_pow]
      _ = (σ : L ≃ₐ[K] L) ((μ : L) ^ d) := by rw [hcL]
      _ = ((σ : L ≃ₐ[K] L) (μ : L)) ^ d := by rw [map_pow]
      _ = ((η : L) ^ n * (μ : L)) ^ d := by rw [hμ]
      _ = (η : L) ^ (n * d) * (c : L) ^ n := by
            rw [mul_pow, ← pow_mul, hcL]
  -- `θ` is the ratio `σ c / (c η ^ d)`, an `n`-th root of unity.
  set θ : L := (σ : L ≃ₐ[K] L) (c : L) / ((c : L) * (η : L) ^ d) with hθdef
  have hden : (c : L) * (η : L) ^ d ≠ 0 :=
    mul_ne_zero (Units.ne_zero c) (pow_ne_zero d (Units.ne_zero η))
  have hθ : θ ^ n = 1 := by
    have key : (η : L) ^ (n * d) = (η : L) ^ (d * n) := by rw [mul_comm]
    rw [hθdef, div_pow, hstep, mul_pow, ← pow_mul]
    rw [key, mul_comm ((c : L) ^ n) ((η : L) ^ (d * n))]
    exact div_self (mul_ne_zero (pow_ne_zero _ (Units.ne_zero η))
      (pow_ne_zero _ (Units.ne_zero c)))
  -- `θ` is a power of `ζ`, hence has norm `1`.
  obtain ⟨i, hi, hθi⟩ := (hζ.map_of_injective (f := algebraMap K L)
      (FaithfulSMul.algebraMap_injective K L)).eq_pow_of_pow_eq_one hθ
  have hNθ : Algebra.norm K θ = 1 := by
    rw [← hθi, ← map_pow, Algebra.norm_algebraMap, hn, ← pow_mul, mul_comm i n, pow_mul,
      hζ.pow_eq_one, one_pow]
  -- Take norms in `σ c = θ η ^ d c`.
  have hsc : (σ : L ≃ₐ[K] L) (c : L) = θ * ((c : L) * (η : L) ^ d) := by
    rw [hθdef]
    exact (div_mul_cancel₀ _ hden).symm
  have hkey0 : Algebra.norm K ((σ : L ≃ₐ[K] L) (c : L)) =
      Algebra.norm K (c : L) * ζ ^ d := by
    rw [hsc, map_mul, map_mul, map_pow, hη, hNθ, one_mul]
  have hkey : Algebra.norm K (c : L) = Algebra.norm K (c : L) * ζ ^ d :=
    (norm_algEquiv_apply (σ : L ≃ₐ[K] L) (c : L)).symm.trans hkey0
  -- Cancel the nonzero norm of the unit `c`.
  have hNc_ne : Algebra.norm K (c : L) ≠ 0 :=
    (IsUnit.map (Algebra.norm K) (Units.isUnit c)).ne_zero
  have hζd : ζ ^ d = 1 := by
    have h : Algebra.norm K (c : L) * ζ ^ d = Algebra.norm K (c : L) * 1 := by
      rw [mul_one, ← hkey]
    exact mul_left_cancel₀ hNc_ne h
  exact hζ.dvd_of_pow_eq_one d hζd

end Work.Kummer
