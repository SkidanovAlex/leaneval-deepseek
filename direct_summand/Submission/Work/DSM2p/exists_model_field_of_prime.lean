import Mathlib
import Submission.Work.DSM2p.CSAlgPos_mod_varpi_flat_aux

/-!
# `Work.DSM2p.exists_model_field_of_prime`

**A model field for a prime `𝔮` not containing `p`.**

Given a perfectoid ring `A` (`P : DSMap.PerfectoidData p A`), a prime ideal `𝔮 ⊆ A` with
`p ∉ 𝔮`, this file produces a field `K` which is an `A`-algebra with

* `ker (A → K) = 𝔮`,
* `P.ϖ 0` invertible in `K`, and
* for every monic polynomial `F` of positive degree over `A`, a compatible system of `p`-power
  roots `r : ℕ → K` (`r (n+1) ^ p = r n`) whose `0`-th member is a root of `F` in `K`.

The construction is the natural one: `K = AlgebraicClosure (FractionRing (A ⧸ 𝔮))` with the
`A`-algebra structure induced by `A → A ⧸ 𝔮 → Frac(A ⧸ 𝔮) → K`.  Since `K` is a field and `𝔮`
is prime, the kernel of the structure map is exactly `𝔮`; since `ϖ ^ p = p · u` with `u` a unit,
`p ∉ 𝔮` forces `ϖ ∉ 𝔮`, so the image of `ϖ` is a nonzero element of a field, hence a unit.
Finally an algebraically closed field is perfect of positive characteristic and contains a root
of every positive-degree polynomial, so the compatible root systems are produced by recursion.
-/

namespace Work.DSM2p

universe u

theorem exists_model_field_of_prime (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] (P : DSMap.PerfectoidData p A) (𝔮 : Ideal A) (h𝔮 : 𝔮.IsPrime) (hp𝔮 : (p : A) ∉ 𝔮) : ∃ (K : Type u) (_ : Field K) (_ : Algebra A K), RingHom.ker (algebraMap A K) = 𝔮 ∧ IsUnit (algebraMap A K (P.ϖ 0)) ∧ (∀ F : MonicPolysPos A, ∃ r : ℕ → K, (∀ n : ℕ, r (n + 1) ^ p = r n) ∧ Polynomial.aeval (r 0) (F.1.map (algebraMap A K)) = 0) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  -- The residue ring `A ⧸ 𝔮`, its fraction field, and an algebraic closure.
  let k := A ⧸ 𝔮
  haveI : IsDomain k := Ideal.Quotient.isDomain 𝔮
  let L := FractionRing k
  let K := AlgebraicClosure L
  -- The structure map `A → K`.
  let φ : A →+* K := (algebraMap L K).comp ((algebraMap k L).comp (Ideal.Quotient.mk 𝔮))
  have hkerφ : RingHom.ker φ = 𝔮 := by
    show RingHom.ker
        ((algebraMap L K).comp ((algebraMap k L).comp (Ideal.Quotient.mk 𝔮))) = 𝔮
    rw [RingHom.ker_comp_of_injective _ (RingHom.injective (algebraMap L K : L →+* K)),
      RingHom.ker_comp_of_injective _ (IsFractionRing.injective k L), Ideal.mk_ker]
  -- `ϖ = P.ϖ 0` is not in `𝔮`: `ϖ ^ p = p · u` with `u` a unit, and `p ∉ 𝔮`.
  have hvarpi : P.ϖ 0 ∉ 𝔮 := by
    intro hmem
    obtain ⟨v, hv⟩ := P.unit
    have hmem2 : (p : A) * (v : A) ∈ 𝔮 := by
      rw [← hv]
      exact Ideal.pow_mem_of_mem 𝔮 hmem p hp0
    rcases h𝔮.mem_or_mem hmem2 with hp_mem | hv_mem
    · exact hp𝔮 hp_mem
    · exact (Ideal.notMem_of_isUnit 𝔮 v.isUnit) hv_mem
  -- Install the `A`-algebra structure on `K`.
  letI : Algebra A K := φ.toAlgebra
  have hker : RingHom.ker (algebraMap A K) = 𝔮 := hkerφ
  have hunit : IsUnit (algebraMap A K (P.ϖ 0)) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    exact hvarpi (hker ▸ RingHom.mem_ker.mpr h0)
  -- Every element of an algebraically closed field has a `p`-th root.
  have hroot : ∀ x : K, ∃ y : K, y ^ p = x := by
    intro x
    have hdeg : (Polynomial.X ^ p - Polynomial.C x : Polynomial K).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C hp0 x]
      exact_mod_cast hp.ne_zero
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    rw [Polynomial.IsRoot.def] at hy
    refine ⟨y, ?_⟩
    have h : y ^ p - x = 0 := by simpa using hy
    exact sub_eq_zero.mp h
  have hroots : ∀ F : MonicPolysPos A, ∃ r : ℕ → K,
      (∀ n : ℕ, r (n + 1) ^ p = r n) ∧
        Polynomial.aeval (r 0) (F.1.map (algebraMap A K)) = 0 := by
    intro F
    -- the image of `F` in `K[T]` has positive degree, hence a root
    have hFdeg : (F.1.map (algebraMap A K) : Polynomial K).degree ≠ 0 := by
      have hnat : (F.1.map (algebraMap A K)).natDegree = F.1.natDegree :=
        F.2.1.natDegree_map (algebraMap A K)
      have hpos : 0 < (F.1.map (algebraMap A K)).natDegree := hnat ▸ F.2.2
      exact ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mp hpos)
    obtain ⟨root0, hroot0⟩ := IsAlgClosed.exists_root _ hFdeg
    rw [Polynomial.IsRoot.def] at hroot0
    -- choose `p`-th roots successively
    let rootPt : K → K := fun x => Classical.choose (hroot x)
    have hrootPt : ∀ x : K, (rootPt x) ^ p = x := fun x => Classical.choose_spec (hroot x)
    let r : ℕ → K := fun n => rootPt^[n] root0
    refine ⟨r, ?_, ?_⟩
    · intro n
      have hstep : r (n + 1) = rootPt (r n) := Function.iterate_succ_apply' rootPt n root0
      rw [hstep, hrootPt]
    · have h0 : r 0 = root0 := Function.iterate_zero_apply rootPt root0
      rw [h0, show Polynomial.aeval root0 (F.1.map (algebraMap A K))
            = Polynomial.eval root0 (F.1.map (algebraMap A K)) by
          simp [Polynomial.aeval_def]]
      exact hroot0
  exact ⟨K, inferInstance, φ.toAlgebra, hker, hunit, hroots⟩

end Work.DSM2p
