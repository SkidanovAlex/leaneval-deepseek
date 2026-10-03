import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Sum

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped lp BigOperators ENNReal

/-- **The frequency support of a finite sum is contained in the union of the frequency supports.**
A major arc system is `f_{Σ_A} = Σ_{α ∈ Σ_A} f_α`, a finite sum of band-limited functions, so its
frequency support is contained in the union of the arcs of the summands.

Proof route: `ftLp` is linear in the sequence (the Fourier transform is the Hilbert-basis expansion
along `fourierBasis`, and `repr.symm` is additive: `map_sum`), so
`ftLp (Σ_i f i) = Σ_i ftLp (f i)` as elements of `Lp`; the coercion of an `Lp`-sum to a function is
a.e. equal to the pointwise sum (`Lp.coeFn_finsetSum`, `Finset.sum_apply`), and a pointwise finite
sum of a.e.-vanishing functions vanishes. -/
theorem hasFreqSupport_sum {ι : Type*} [Fintype ι] {f : ι → ℤ → ℂ} (hf : ∀ i, Memℓp (f i) 2)
    {E : ι → Set Circle} (hE : ∀ i, HasFreqSupport (f i) (hf i) (E i)) :
    HasFreqSupport (fun m => ∑ i, f i m) (memℓp_sum hf) (⋃ i, E i) := by
  -- Step 1: `ftLp` is additive, since it is the inverse of the linear isometry `fourierBasis.repr`
  -- applied to the (pointwise) sum in `ℓ²(ℤ, ℂ)`.
  have hsum : ftLp (fun m => ∑ i, f i m) (memℓp_sum hf) = ∑ i, ftLp (f i) (hf i) := by
    have harg : (⟨fun m => ∑ i, f i m, memℓp_sum hf⟩ : ℓ²(ℤ, ℂ)) =
        ∑ i, (⟨f i, hf i⟩ : ℓ²(ℤ, ℂ)) := by
      refine Subtype.ext ?_
      rw [lp.coeFn_sum]
      funext m
      simp [Finset.sum_apply]
    simp only [ftLp]
    rw [harg, map_sum]
  simp only [HasFreqSupport] at hE ⊢
  -- Step 2: the `Lp`-class of the sum is a.e. the pointwise sum of the classes.
  have hcoe : (ftLp (fun m => ∑ i, f i m) (memℓp_sum hf) : Circle → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := 1)] ∑ i, (ftLp (f i) (hf i) : Circle → ℂ) := by
    rw [hsum]
    simpa using Lp.coeFn_finsetSum (μ := AddCircle.haarAddCircle (T := 1)) (Finset.univ)
      (fun i => ftLp (f i) (hf i))
  -- Step 3: a.e. simultaneously, each summand vanishes outside its own arc.
  have hforall : ∀ᵐ θ ∂AddCircle.haarAddCircle (T := 1), ∀ i,
      (θ ∉ E i → (ftLp (f i) (hf i) : Circle → ℂ) θ = 0) := Filter.eventually_all.mpr hE
  filter_upwards [hcoe, hforall] with θ hθ1 hθ2
  intro hmem
  rw [hθ1, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  exact hθ2 i (fun hi => hmem (Set.mem_iUnion.mpr ⟨i, hi⟩))

end Work.BourgainPlan.IonescuWainger
