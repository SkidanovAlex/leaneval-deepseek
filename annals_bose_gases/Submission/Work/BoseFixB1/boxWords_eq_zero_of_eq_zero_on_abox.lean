import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PerBoxNames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxWords_eq_zero_of_eq_zero_on_abox`

A state `Φ : X N → ℝ` that vanishes on the analysis box `abox N a` has all five
box-projected words at the box `A ⊆ acube a` vanishing:

* the flat (condensate) count `boxFlatCount volA a A Φ = Σᵢ∫_{abox}(PᵢΦ)²`,
* the excited count `boxQCount volA a A Φ = Σᵢ∫_{abox}(QᵢΦ)²`,
* FS's excited count `cnPlusBoxInd a A volA Φ = Σᵢ∫_{abox}(Q_{B,i}Φ)²`
  (definitionally the same summands as `boxQCount`),
* the pairing word `boxA2 a volA A w₁ Φ`, a sum over `pairSet N` of box integrals of
  products of the *two-slot* projections `P_iP_jΦ`, `Q_jQ_iΦ`,
* the `p`-diagonal kinetic form `tBdiagFormInd a A volA χ F Φ`, a sum over `i` of
  momentum integrals of `‖tBamp χ p (Q_{B,i}Φ) i ·‖²` over the box.

The mathematics is one membership observation plus the fact that every one of the
above integrands is *pointwise* zero on `abox N a` (so its Bochner integral vanishes
by `setIntegral_eq_zero_of_forall_eq_zero`, with no measurability or integrability
input — the `integral_undef` convention is irrelevant here because the integrand is
literally `0` on the region).

The observation: `abox N ℓ = {x | ∀ i, x i ∈ acube ℓ}`, and `A ⊆ acube a`, so placing
any coordinate of a configuration of the box inside `A` keeps the configuration in the
box. Hence for `x ∈ abox N a`:

* `P_{B,i}Ψ(x) = (1/volA)·∫_{A}Ψ(x_{i←z})·1_A(x_i)` has the integral of a function that
  vanishes on the region `x_{i←z}`, `z ∈ A` — so it is `0` whenever `Ψ` itself vanishes
  on the box;
* `Q_{B,i}Ψ = 1_A(x_i)·Ψ(x) − P_{B,i}Ψ` vanishes at `x` and — because at *any* point
  `x_{i←z}` with `z ∉ A` both the indicator `1_A(z)` and the `P`-term's indicator
  `1_A(z)` are `0`, while for `z ∈ A` the point `x_{i←z}` lies in the box — also at every
  `x_{i←z}`, `z` arbitrary.  The latter is exactly what the amplitude `tBamp`, whose
  integrand is evaluated at `x_{i←z}`, needs.

The two iterated uses (`P_iP_jΦ`, `Q_jQ_iΦ`) are obtained by instantiating the helper
lemmas at `Ψ := P_{B,j}Φ` and `Ψ := Q_{B,i}Φ`.  All declarations here are `sorry`-free.
-/

namespace Work.BoseFixB1

open MeasureTheory

/-- **The box condensate projection kills a state vanishing on the box.**
If `Ψ` vanishes on `abox N a` and `A ⊆ acube a`, then `P_{B,i}Ψ` vanishes on `abox N a`:
the defining integral `∫_{A}Ψ(x_{i←z})` is taken over points that stay in the box. -/
lemma boxPInd_eq_zero_of_vanishes_on_abox {N : ℕ} {a volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : A ⊆ Submission.BoseGases.acube a)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ y, y ∈ Submission.BoseGases.abox N a → Ψ y = 0) (i : Fin N) :
    ∀ x, x ∈ Submission.BoseGases.abox N a →
      Work.UBBInputs8.boxPInd volA A i Ψ x = 0 := by
  intro x hx
  -- placing the `i`-th coordinate inside `A ⊆ acube a` keeps the configuration in the box
  have hmem : ∀ z, z ∈ A → Function.update x i z ∈ Submission.BoseGases.abox N a := by
    intro z hz j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hAc hz
    · rw [Function.update_of_ne hj]; exact hx j
  have hint : (∫ z in A, Ψ (Function.update x i z)) = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun z hz => hΨ _ (hmem z hz))
  rw [Work.UBBInputs8.boxPInd, hint]
  ring

/-- **The box mean-free projection kills a state vanishing on the box, at every
slotted point.**  If `Ψ` vanishes on `abox N a` and `A ⊆ acube a`, then
`Q_{B,i}Ψ(x_{i←z}) = 0` for every `x ∈ abox N a` and **every** `z` (not only `z ∈ A`):
for `z ∈ A` the point `x_{i←z}` is back in the box and both terms vanish, while for
`z ∉ A` both the box indicator of `Q_{B,i}` and that of `P_{B,i}` are `0`. -/
lemma boxQInd_update_eq_zero_of_vanishes_on_abox {N : ℕ} {a volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : A ⊆ Submission.BoseGases.acube a)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ y, y ∈ Submission.BoseGases.abox N a → Ψ y = 0) (i : Fin N) :
    ∀ x, x ∈ Submission.BoseGases.abox N a → ∀ z,
      Work.UBBInputs8.boxQInd volA A i Ψ (Function.update x i z) = 0 := by
  intro x hx z
  have hmem : ∀ w, w ∈ A → Function.update x i w ∈ Submission.BoseGases.abox N a := by
    intro w hw j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hAc hw
    · rw [Function.update_of_ne hj]; exact hx j
  by_cases hz : z ∈ A
  · have hy : Function.update x i z ∈ Submission.BoseGases.abox N a := hmem z hz
    rw [Work.UBBInputs8.boxQInd, hΨ _ hy,
      boxPInd_eq_zero_of_vanishes_on_abox hAc hΨ i _ hy]
    ring
  · rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Function.update_self,
      Set.indicator_of_notMem hz]
    ring

/-- **The box mean-free projection kills a state vanishing on the box.**  The pointwise
form of `boxQInd_update_eq_zero_of_vanishes_on_abox` (take `z := x i`). -/
lemma boxQInd_eq_zero_of_vanishes_on_abox {N : ℕ} {a volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : A ⊆ Submission.BoseGases.acube a)
    {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : ∀ y, y ∈ Submission.BoseGases.abox N a → Ψ y = 0) (i : Fin N) :
    ∀ x, x ∈ Submission.BoseGases.abox N a → Work.UBBInputs8.boxQInd volA A i Ψ x = 0 := by
  intro x hx
  have h := boxQInd_update_eq_zero_of_vanishes_on_abox (volA := volA) hAc hΨ i x hx (x i)
  rwa [Function.update_eq_self i x] at h

theorem boxWords_eq_zero_of_eq_zero_on_abox {N : ℕ} {a volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAc : A ⊆ Submission.BoseGases.acube a)
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (F : ℝ → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ}
    (h0 : ∀ y, y ∈ Submission.BoseGases.abox N a → Φ y = 0) :
    Work.BoseFixB1S.boxFlatCount volA a A Φ = 0
      ∧ Work.BoseFixB1S.boxQCount volA a A Φ = 0
      ∧ Work.UBBInputs8.cnPlusBoxInd a A volA Φ = 0
      ∧ Work.BoseFixB1.boxA2 a volA A w1 Φ = 0
      ∧ Work.UBBInputs8.tBdiagFormInd a A volA χ F Φ = 0 := by
  -- the projections of `Φ` vanish on the box …
  have hP : ∀ i : Fin N, ∀ x, x ∈ Submission.BoseGases.abox N a →
      Work.UBBInputs8.boxPInd volA A i Φ x = 0 :=
    fun i => boxPInd_eq_zero_of_vanishes_on_abox hAc h0 i
  have hQ : ∀ i : Fin N, ∀ x, x ∈ Submission.BoseGases.abox N a →
      Work.UBBInputs8.boxQInd volA A i Φ x = 0 :=
    fun i => boxQInd_eq_zero_of_vanishes_on_abox hAc h0 i
  -- … and so do their slotted values, which is what the amplitude `tBamp` sees
  have hQu : ∀ i : Fin N, ∀ x, x ∈ Submission.BoseGases.abox N a → ∀ z,
      Work.UBBInputs8.boxQInd volA A i Φ (Function.update x i z) = 0 :=
    fun i => boxQInd_update_eq_zero_of_vanishes_on_abox (volA := volA) hAc h0 i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the flat count: a sum of box integrals of squares of `PᵢΦ`
    rw [Work.BoseFixB1S.boxFlatCount]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
      (fun x hx => by rw [hP i x hx]; ring)
  · -- the excited count `Σᵢ∫(QᵢΦ)²`
    rw [Work.BoseFixB1S.boxQCount]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
      (fun x hx => by rw [hQ i x hx]; ring)
  · -- FS's excited count `n₊(B) = Σᵢ∫(Q_{B,i}Φ)²`, the same summands
    rw [Work.UBBInputs8.cnPlusBoxInd]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
      (fun x hx => by rw [hQ i x hx]; ring)
  · -- the pairing word: the two-slot projections `P_iP_jΦ`, `Q_jQ_iΦ` vanish on the box
    rw [Work.BoseFixB1.boxA2]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
      (fun x hx => by
        rw [boxPInd_eq_zero_of_vanishes_on_abox hAc (hP p.2) p.1 x hx,
            boxQInd_eq_zero_of_vanishes_on_abox hAc (hQ p.1) p.2 x hx]
        ring)
  · -- the kinetic form: the amplitude is an integral of `Q_{B,i}Φ` at `x_{i←z}`
    rw [Work.UBBInputs8.tBdiagFormInd]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hint : ∀ pp : EuclideanSpace ℝ (Fin 3),
        (∫ x in Submission.BoseGases.abox N a,
          ‖Work.SmallBoxTBWord.tBamp χ pp (Work.UBBInputs8.boxQInd volA A i Φ) i x‖ ^ 2) = 0 := by
      intro pp
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun x hx => ?_)
      have hb : Work.SmallBoxTBWord.tBamp χ pp
          (Work.UBBInputs8.boxQInd volA A i Φ) i x = 0 := by
        rw [Work.SmallBoxTBWord.tBamp]
        simp only [hQu i x hx]
        simp
      rw [hb]
      norm_num
    simp only [hint]
    simp

end Work.BoseFixB1
