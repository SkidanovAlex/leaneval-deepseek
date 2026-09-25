import Mathlib
import Submission.Commons.RingTheory.Valuation.exists_pow_eq_of_isIntegral

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

/-- If `σ` is a `K`-algebra automorphism of `L` preserving a valuation subring `A` of `L`, and
`L/K` is algebraic, then `σ` preserves the valuation attached to `A`.  Equivalently, the induced
order-preserving automorphism of the value group of `A` is trivial, because the value group is
torsion over the values coming from `K` (an algebraic extension only adds torsion to the value
group) while `σ` fixes those values. -/
theorem val_eq_of_algEquiv_of_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : Algebra.IsAlgebraic K L) (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (hσ : A.comap (σ : L →+* L) = A) : ∀ x : L, A.valuation (σ x) = A.valuation x := by
  intro x
  -- `σ` preserves `A` elementwise
  have hA : ∀ z : L, σ z ∈ A ↔ z ∈ A := by
    intro z
    have h := SetLike.ext_iff.mp hσ z
    rwa [ValuationSubring.mem_comap] at h
  -- the induced ring hom `A →+* A`, and its action on units
  let σA : A →+* A :=
    { toFun := fun a => ⟨σ (a : L), (hA (a : L)).mpr a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  by_cases hx : x = 0
  · subst hx; simp
  -- algebraic ⟹ integral, so the value of `x` is torsion over the values from `K`
  let vK : Valuation K A.ValueGroup := A.valuation.comap (algebraMap K L)
  haveI : vK.HasExtension A.valuation := ⟨Valuation.IsEquiv.refl⟩
  obtain ⟨n, hn, a, ha⟩ :=
    exists_pow_eq_of_isIntegral vK A.valuation (halg.isAlgebraic x).isIntegral hx
  -- `A.valuation (x^n) = A.valuation (algebraMap K L a)`
  have hpow : A.valuation (x ^ n) = A.valuation (algebraMap K L a) := by
    rw [map_pow]; exact ha
  -- write `x^n = u * m` with `u` a unit of `A`
  obtain ⟨u, hu⟩ := (A.valuation_eq_iff (x ^ n) (algebraMap K L a)).mp hpow
  -- `m = algebraMap K L a` is fixed by `σ`
  have hσm : σ (algebraMap K L a) = algebraMap K L a := σ.commutes a
  -- `σ u` is (the image of) a unit of `A`
  let u' : Aˣ := Units.map σA.toMonoidHom u
  have hco : (u' : L) = σ (u : L) := rfl
  have hval_u' : A.valuation (σ (u : L)) = 1 := by
    rw [← hco]; exact A.valuation_unit u'
  -- σ(x^n) = σ(u) * m
  have hσmul : σ (x ^ n) = σ (u : L) * (algebraMap K L a) := by
    rw [← hu, map_mul, hσm]
  have hxn : (σ x) ^ n = σ (u : L) * (algebraMap K L a) := by
    rw [← map_pow σ x n]; exact hσmul
  -- the `n`-th powers of the two values agree
  have h1 : A.valuation ((σ x) ^ n) = A.valuation (x ^ n) := by
    rw [hxn, map_mul, hval_u', one_mul, ← hpow]
  have h2 : A.valuation (σ x) ^ n = A.valuation x ^ n := by
    rw [← map_pow A.valuation (σ x) n, ← map_pow A.valuation x n]
    exact h1
  -- `Γ` is a linearly ordered commutative group with zero, so `·^n` is injective (`n ≠ 0`)
  exact (pow_left_inj₀ (show (0 : A.ValueGroup) ≤ A.valuation (σ x) from zero_le)
    (show (0 : A.ValueGroup) ≤ A.valuation x from zero_le) hn.ne').mp h2

end Commons.RingTheory.Valuation
