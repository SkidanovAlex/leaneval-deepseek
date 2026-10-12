import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseB4.Kafz_monomial
import Submission.Work.BoseB4.MonoOp
import Submission.Work.BoseB4.inner_Phi_PhiB_expansion
import Submission.Work.BoseB4.integrable_conj_cohWeight_mul_cohWeight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Kafz_sum` — the `c`-number substitution for a finite sum

FS §8.3 (`thm:Kafz`) apply the substitution rule `a₀ ↦ z`, `a₀† ↦ z̄` to an
*operator that is a finite sum of anti-normal monomials*,

    `H = ∑ᵢ a₀^{pᵢ} (a₀†)^{qᵢ} (lift Bᵢ)`,

which is the form in which every operator of FS §8–§11 (`eq:HLambdaSecond`,
`eq:Kz`) appears.  Term by term the substitution is
`Work.BoseB4.Kafz_monomial`; summing over the finite index set only requires

* `Embed` (a linear map) and `inner x` (linear in its *second* argument) to
  distribute over a `Finset.sum`, and
* the integral of a finite sum to be the sum of the integrals, i.e. the
  integrability of every single summand.

The integrability is the only non-formal input: the summand
`z ↦ z^{p} z̄^{q} ⟪Φ Ψ z, B (Φ Ψ z)⟫` is a *polynomial* in `z` and `z̄` times
constants — expanding `⟪Φ Ψ z, B (Φ Ψ z)⟫` over the (finite) condensate levels of
`Ψ` (`Work.BoseB4.inner_Phi_PhiB_expansion`) makes this manifest, and polynomials
are integrable against the Gaussian measure (`Work.BoseB4.Gauss_integrable`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB4

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Integrability of a single monomial summand** of the `c`-number substitution:
for any `p q : ℕ`, any `B : E →ₗ[ℂ] E` and any core vector `Ψ`,

`z ↦ z^p z̄^q ⟪Φ Ψ z, B (Φ Ψ z)⟫`

is integrable against the Gaussian measure `dν`.  The point is that it is a
polynomial in `z, z̄` times constants: writing `S = Ψ.support` and expanding
`⟪Φ Ψ z, B (Φ Ψ z)⟫ = ∑_{n ∈ S} ∑_{m ∈ S} conj(cw n z) cw m z ⟪Ψ n, B (Ψ m)⟫`
(`inner_Phi_PhiB_expansion`), where `conj(cw n z) = z^n/√(n!)`, the summand is a
finite sum of multiples of the monomials `z^{p+n} z̄^{q+m}`, each of which is
integrable by `Gauss_integrable`. -/
lemma integrable_kafz_integrand (p q : ℕ) (B : E →ₗ[ℂ] E) (Ψ : FockCore E) :
    Integrable (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q *
      inner ℂ (Phi Ψ z) (B (Phi Ψ z))) gauss := by
  have hsum : Integrable (fun z : ℂ => ∑ n ∈ Ψ.support, ∑ m ∈ Ψ.support,
      (z ^ (p + n) * (starRingEnd ℂ z) ^ (q + m)) *
        ((sq n.factorial * sq m.factorial)⁻¹ * inner ℂ (Ψ n) (B (Ψ m)))) gauss := by
    refine integrable_finsetSum Ψ.support (fun n _ => ?_)
    refine integrable_finsetSum Ψ.support (fun m _ => ?_)
    exact (Gauss_integrable (p + n) (q + m)).mul_const _
  refine hsum.congr ?_
  filter_upwards with z
  rw [inner_Phi_PhiB_expansion B Ψ Ψ z, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [conj_cohWeight_mul_eq n m z, pow_add, pow_add]
  ring

/-- **The `c`-number substitution for a finite sum of anti-normal monomials**
(FS `thm:Kafz`, the form consumed by the box analysis): for every finite family
`(pᵢ, qᵢ, Bᵢ)ᵢ`, with `H = ∑ᵢ a₀^{pᵢ} (a₀†)^{qᵢ} (lift Bᵢ)`,

`⟪Ψ, H Ψ⟫ = ∫_ℂ ∑ᵢ z^{pᵢ} z̄^{qᵢ} ⟪Φ Ψ z, Bᵢ (Φ Ψ z)⟫ dν(z)`.

The left-hand side distributes over the finite sum (`map_sum` for the linear
`Embed`, `inner_sum` for the conjugate-linear-first, linear-second inner product),
each term is `Kafz_monomial`, and the right-hand side commutes `∫` with the finite
sum (`integral_finsetSum`), the integrability of each summand being
`integrable_kafz_integrand`. -/
theorem Kafz_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} (s : Finset ι) (p q : ι → ℕ) (B : ι → E →ₗ[ℂ] E) (Ψ : Work.BoseB4.FockCore E) :
    inner ℂ (Work.BoseB4.Embed E Ψ)
        (Work.BoseB4.Embed E (∑ i ∈ s, Work.BoseB4.monoOp (p i) (q i) (B i) Ψ))
      = ∫ z : ℂ, ∑ i ∈ s, z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
          inner ℂ (Work.BoseB4.Phi Ψ z) (B i (Work.BoseB4.Phi Ψ z)) ∂(Work.BoseB4.gauss) := by
  have hInt : ∀ i ∈ s, Integrable (fun z : ℂ => z ^ (p i) * (starRingEnd ℂ z) ^ (q i) *
      inner ℂ (Phi Ψ z) (B i (Phi Ψ z))) gauss :=
    fun i _ => integrable_kafz_integrand (p i) (q i) (B i) Ψ
  rw [map_sum, inner_sum]
  rw [integral_finsetSum s hInt]
  exact Finset.sum_congr rfl fun i _ => Kafz_monomial (p i) (q i) (B i) Ψ

end Work.BoseB4
