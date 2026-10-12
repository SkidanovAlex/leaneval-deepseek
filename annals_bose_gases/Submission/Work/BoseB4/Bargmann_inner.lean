import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.Gauss_integrable
import Submission.Work.BoseB4.Gauss_moment
import Submission.Work.BoseB4.PhiProps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Bargmann_inner` — the Bargmann isometry (resolution of the identity)

FS §8.3 resolve the identity on the condensate mode in coherent states
`|z⟩ = e^{z a₀†}Ω`:

    `1 = ∫_ℂ |z⟩⟨z| dν(z)`,   `dν(z) = e^{-|z|²} d²z/π`.

On the Fock space presented as `Fock E = ⨁_n E` (with `n` the number of condensate
quanta) and with the coherent-state transform `Phi Ψ z = ⟨z|Ψ⟩ = ∑ₙ (z̄ⁿ/√(n!)) Ψₙ`,
the resolution of the identity is the **isometry**

    `⟪Ψ, Ψ'⟫ = ∫_ℂ ⟪Phi Ψ z, Phi Ψ' z⟫ dν(z)`   (`Bargmann_inner`),

i.e. `Φ` is an isometry from the algebraic Fock core into the Bargmann space
`L²(ℂ, dν)`.

## Proof

Both sides are finite sums.  Writing `S = Ψ.support ∪ Ψ'.support`, the pointwise
expansion of the integrand is

    `⟪Phi Ψ z, Phi Ψ' z⟫ = ∑_{n ∈ S} ∑_{m ∈ S} conj(cw n z) * cw m z * ⟪Ψₙ, Ψ'ₘ⟫`,
    `cw n z = z̄ⁿ/√(n!)`,

and since `conj(cw n z) = zⁿ/√(n!)`, the Gaussian moment computation
(`Gauss_moment`) gives, term by term,

    `∫_ℂ conj(cw n z) * cw m z dν(z) = δ_{n m}`

(the `cw n` are orthonormal in `L²(ℂ, dν)`).  Hence the double sum collapses to
`∑_{n ∈ S} ⟪Ψₙ, Ψ'ₙ⟫ = ⟪Ψ, Ψ'⟫`, the last step because `Ψ, Ψ'` are finitely
supported (the `tsum` defining the core inner product is a finite sum).
-/

noncomputable section

open MeasureTheory
open scoped lp NNReal ENNReal

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

namespace BargmannInnerAux

/-- Conjugation of the coherent weight: because `cw n z = z̄ⁿ/√(n!)` with `√(n!)`
real, its conjugate is `zⁿ/√(n!)`. -/
lemma star_cohWeight (n : ℕ) (z : ℂ) :
    starRingEnd ℂ (cohWeight n z) = z ^ n / sq n.factorial := by
  rw [cohWeight, map_div₀, map_pow]
  simp [sq, Complex.conj_ofReal]

/-- The product of a conjugated coherent weight with another one, in the form
consuming `Gauss_moment`: `conj(cw n z) * cw m z = zⁿ z̄ᵐ · (√(n!)√(m!))⁻¹`. -/
lemma cohWeight_mul_eq (n m : ℕ) (z : ℂ) :
    starRingEnd ℂ (cohWeight n z) * cohWeight m z
      = (z ^ n * (starRingEnd ℂ z) ^ m) * (sq n.factorial * sq m.factorial)⁻¹ := by
  rw [star_cohWeight, cohWeight, div_eq_mul_inv, div_eq_mul_inv]
  simp only [sq]
  ring

/-- **Orthonormality of the coherent weights** in `L²(ℂ, dν)`:
`∫_ℂ conj(cw n z) * cw m z dν(z) = δ_{n m}`.  This is the Gaussian moment
`∫ zⁿ z̄ᵐ dν = δ_{nm} m!` (`Gauss_moment`) divided by `√(n!)·√(m!)`. -/
lemma integral_cohWeight_mul (n m : ℕ) :
    ∫ z : ℂ, starRingEnd ℂ (cohWeight n z) * cohWeight m z ∂gauss = if n = m then 1 else 0 := by
  have hfun : (fun z : ℂ => starRingEnd ℂ (cohWeight n z) * cohWeight m z)
      = fun z => (z ^ n * (starRingEnd ℂ z) ^ m) * (sq n.factorial * sq m.factorial)⁻¹ :=
    funext fun z => cohWeight_mul_eq n m z
  rw [hfun, integral_mul_const, Gauss_moment]
  by_cases h : n = m
  · subst h
    rw [if_pos rfl, sq_mul_sq]
    rw [mul_inv_cancel₀
      (show ((n.factorial : ℂ)) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
    rw [if_pos rfl]
  · rw [if_neg h, if_neg h, zero_mul]

/-- Integrability of the coherent-weight product against the Gaussian measure,
used to commute `∫` with the finite sums in the expansion of `⟪Phi Ψ z, Phi Ψ' z⟫`.
Reduced to `Gauss_integrable` and the rewriting `cohWeight_mul_eq`. -/
lemma integrable_cohWeight_mul (n m : ℕ) :
    Integrable (fun z : ℂ => starRingEnd ℂ (cohWeight n z) * cohWeight m z) gauss := by
  have h := (Gauss_integrable n m).mul_const ((sq n.factorial * sq m.factorial)⁻¹)
  refine h.congr ?_
  filter_upwards with z
  exact (cohWeight_mul_eq n m z).symm

end BargmannInnerAux

/-- **The Bargmann isometry** (FS §8.3, resolution of the identity): the
coherent-state transform `Φ` is an isometry from the Fock core into `L²(ℂ, dν)`. -/
theorem Bargmann_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Ψ Ψ' : Work.BoseB4.FockCore E) :
    Work.BoseB4.coreInner Ψ Ψ'
      = ∫ z : ℂ, inner ℂ (Work.BoseB4.Phi Ψ z) (Work.BoseB4.Phi Ψ' z) ∂(Work.BoseB4.gauss) := by
  set S : Finset ℕ := Ψ.support ∪ Ψ'.support with hS
  -- The core inner product is a finite sum over `S`.
  have hzero : ∀ n ∉ S, inner ℂ (Ψ n) (Ψ' n) = 0 := by
    intro n hn
    have h1 : n ∉ Ψ.support := fun h => hn (by rw [hS]; exact Finset.mem_union.mpr (Or.inl h))
    rw [Finsupp.notMem_support_iff.mp h1, inner_zero_left]
  rw [coreInner_eq_tsum, tsum_eq_sum hzero]
  -- Pointwise expansion of the integrand as a double sum over `S`.
  have hexp : (fun z : ℂ => inner ℂ (Phi Ψ z) (Phi Ψ' z))
      = fun z => ∑ n ∈ S, ∑ m ∈ S,
          (starRingEnd ℂ (cohWeight n z) * cohWeight m z) * inner ℂ (Ψ n) (Ψ' m) := by
    funext z
    have h1 : Phi Ψ z = ∑ n ∈ S, cohWeight n z • Ψ n := by
      rw [Phi_apply]
      refine Finset.sum_subset (by rw [hS]; exact Finset.subset_union_left) ?_
      intro x _ hxnot
      rw [Finsupp.notMem_support_iff.mp hxnot, smul_zero]
    have h2 : Phi Ψ' z = ∑ m ∈ S, cohWeight m z • Ψ' m := by
      rw [Phi_apply]
      refine Finset.sum_subset (by rw [hS]; exact Finset.subset_union_right) ?_
      intro x _ hxnot
      rw [Finsupp.notMem_support_iff.mp hxnot, smul_zero]
    rw [h1, h2, sum_inner]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_left, inner_smul_right]
    ring
  rw [hexp]
  -- Integrate the double sum term by term and use the Gaussian moments.
  refine (show ∫ z : ℂ, (∑ n ∈ S, ∑ m ∈ S,
      (starRingEnd ℂ (cohWeight n z) * cohWeight m z) * inner ℂ (Ψ n) (Ψ' m)) ∂gauss
      = ∑ n ∈ S, inner ℂ (Ψ n) (Ψ' n) from ?_).symm
  rw [MeasureTheory.integral_finsetSum S (f := fun n z => ∑ m ∈ S,
      (starRingEnd ℂ (cohWeight n z) * cohWeight m z) * inner ℂ (Ψ n) (Ψ' m))
      (fun n _ => MeasureTheory.integrable_finsetSum S (f := fun m z =>
        (starRingEnd ℂ (cohWeight n z) * cohWeight m z) * inner ℂ (Ψ n) (Ψ' m))
        (fun m _ => (BargmannInnerAux.integrable_cohWeight_mul n m).mul_const _))]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [MeasureTheory.integral_finsetSum S (f := fun m z =>
      (starRingEnd ℂ (cohWeight n z) * cohWeight m z) * inner ℂ (Ψ n) (Ψ' m))
      (fun m _ => (BargmannInnerAux.integrable_cohWeight_mul n m).mul_const _)]
  rw [Finset.sum_congr rfl (fun m _ => ?_), Finset.sum_ite_eq]
  · rw [if_pos hn]
  · rw [integral_mul_const, BargmannInnerAux.integral_cohWeight_mul]
    by_cases h : n = m <;> simp [h]

end Work.BoseB4
