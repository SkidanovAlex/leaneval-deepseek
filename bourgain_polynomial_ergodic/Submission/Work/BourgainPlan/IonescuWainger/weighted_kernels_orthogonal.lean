import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.kernel_arcSymbol_torsion
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_mul_pow
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Ortho
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_torsionKernel
import Submission.Work.BourgainPlan.IonescuWainger.hasFreqSupport_quadratic_weight
import Submission.Work.BourgainPlan.IonescuWainger.memlp_of_mul_quadratic_weight

namespace Work.BourgainPlan.IonescuWainger

set_option maxHeartbeats 4000000

/-- **The weighted kernels of the torsion-arc symbols are pairwise `ℓ²`-orthogonal** (the last
structural step of the `p = ∞` endpoint of Tao's `ortho-apply`(ii)).  The kernel of
`Op_{φ;α+Σ_{⊆A}}` is the torsion kernel `n ↦ conj(e_n α)·Q_A·1_{Q_A ∣ n}·K n`
(`kernel_arcSymbol_torsion`); multiplying it by the polynomial weight `w n = 1 + ε² n²` does not
spread its frequency support (`hasFreqSupport_mul_pow`), which is contained in the shifted torsion
arc around `α`; if those arcs are pairwise disjoint then the weighted kernels are pairwise
orthogonal. -/
theorem weighted_kernels_orthogonal {A : Finset ℕ} {ι : Type*} [Fintype ι]
    (αs : ι → Circle) (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    {ε : ℝ} (hε : 0 ≤ ε) (hφsupp : ∀ ξ : Circle, ε < ‖ξ‖ → φ ξ = 0)
    (hdisj : ∀ i j : ι, i ≠ j →
      Disjoint (closure {ξ : Circle | ∃ β ∈ sigmaSubAFinset A,
          ξ - (β + αs i) ∈ Metric.closedBall (0 : Circle) ε})
               (closure {ξ : Circle | ∃ β ∈ sigmaSubAFinset A,
          ξ - (β + αs j) ∈ Metric.closedBall (0 : Circle) ε}))
    (hmem : ∀ i, Memℓp (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)
        * (star (fourier n (αs i)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n)) 2)
    (i j : ι) (hij : i ≠ j) :
    ∑' n : ℤ, ((1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)
        * (star (fourier n (αs i)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n))
      * star ((1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)
        * (star (fourier n (αs j)) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n)) = 0 := by
  classical
  -- The frequency support of the *weighted* torsion kernel of the shifted torsion arc around `α`.
  have key : ∀ (α : Circle) (hW : Memℓp (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)
        * (star (fourier n α) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n)) 2),
      HasFreqSupport (fun n : ℤ => (1 + (ε : ℂ) ^ 2 * (n : ℂ) ^ 2)
        * (star (fourier n α) * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n)) hW
        (closure {ξ : Circle | ∃ β ∈ sigmaSubAFinset A,
          ξ - (β + α) ∈ Metric.closedBall (0 : Circle) ε}) := by
    intro α hW
    -- the unweighted torsion kernel is square summable, being dominated by the weighted one
    have hg : Memℓp (fun n : ℤ => star (fourier n α)
        * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n) 2 :=
      memlp_of_mul_quadratic_weight
        (g := fun n : ℤ => star (fourier n α)
          * (if (QA A : ℤ) ∣ n then (QA A : ℂ) else 0) * K n) hW
    -- the unweighted torsion kernel is supported in the shifted torsion arc (`kernel_arcSymbol_torsion`)
    have hT := hasFreqSupport_torsionKernel (A := A) α φ hφ hK hφsupp (hT := hg)
    -- multiplication by the polynomial weight `1 + ε²n²` does not spread that support
    exact hasFreqSupport_quadratic_weight hε hg hT
  exact tsum_mul_conj_eq_zero_of_disjoint_freqSupport (hmem i) (hmem j)
    (key (αs i) (hmem i)) (key (αs j) (hmem j)) (hdisj i j hij)

end Work.BourgainPlan.IonescuWainger
