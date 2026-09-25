import Mathlib
import Submission.Work.BourgainPlan.Thm52.decimatedKernel_neg_coe_eq_torsionKernel
import Submission.Work.BourgainPlan.IonescuWainger.charSum_sigmaSubAFinset
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel

namespace Work.BourgainPlan.Thm52

open MeasureTheory
open scoped BigOperators

-- The final convention bridge: the torsion-arc multiplier over the whole Q_A-torsion subgroup
-- (Tao's indicator-sum Op_{phi; Sigma_{subset A}}, which is the first factor of the KMSZ (6.22)
-- factorisation when the coarse arc set is the torsion subgroup) acts on an ell-two input exactly as
-- the convolution with the decimated kernel of the *reflected* bump.
-- Route: Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel writes the left side as
-- tsum over k of h k * ((sum over beta in sigmaSubAFinset A of star (fourier (n-k) beta)) * K (n-k))
-- with K l = integral of phi * star (fourier l); Work.BourgainPlan.IonescuWainger.charSum_sigmaSubAFinset
-- evaluates the character sum as (QA A) * [QA A divides .]; the definition of
-- Work.BourgainPlan.IonescuWainger.torsionKernel and the landed
-- Work.BourgainPlan.Thm52.decimatedKernel_neg_coe_eq_torsionKernel identify the product with
-- decimatedKernel (QA A) (fun x => phi (-x)); mul_comm moves the factors (up to a `by_cases` on the
-- divisibility, since torsionKernel puts the scalar first).
theorem opArc_sigmaSubAFinset_eq_decimatedKernel {A : Finset ℕ}
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (h : ℤ → ℂ) (hh : Memℓp h 2) (n : ℤ) :
    Work.BourgainPlan.IonescuWainger.opArc φ hφ
        (Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A) h hh n
      = ∑' j : ℤ, Work.BourgainPlan.Thm52.decimatedKernel (Work.BourgainPlan.IonescuWainger.QA A)
          (fun x : ℝ => φ (-(x : Work.BourgainPlan.IonescuWainger.Circle))) (n - j) * h j := by
  -- The `Σ_{⊆ A}`-character sum times the coefficient `K (n-k)` is the torsion kernel of `A`.
  have hchar : ∀ k : ℤ,
      (∑ β ∈ Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A, star (fourier (n - k) β))
        * (∫ ξ, φ ξ * star (fourier (n - k) ξ) ∂(AddCircle.haarAddCircle (T := 1)))
      = Work.BourgainPlan.IonescuWainger.torsionKernel A
          (fun l : ℤ => ∫ ξ, φ ξ * star (fourier l ξ)
            ∂(AddCircle.haarAddCircle (T := 1))) (n - k) := by
    intro k
    rw [Work.BourgainPlan.IonescuWainger.charSum_sigmaSubAFinset,
      Work.BourgainPlan.IonescuWainger.torsionKernel]
    by_cases hd : (Work.BourgainPlan.IonescuWainger.QA A : ℤ) ∣ (n - k)
    · rw [if_pos hd, if_pos hd]
    · rw [if_neg hd, if_neg hd]
      simp
  rw [Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel φ hφ (fun m => rfl)
    (Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A) h hh n]
  -- reduce the left-hand `tsum` to the torsion kernel
  trans ∑' k : ℤ, h k * Work.BourgainPlan.IonescuWainger.torsionKernel A
      (fun l : ℤ => ∫ ξ, φ ξ * star (fourier l ξ)
        ∂(AddCircle.haarAddCircle (T := 1))) (n - k)
  · exact tsum_congr fun k => by rw [hchar k]
  · -- and compare with the right-hand `tsum`, termwise via `mul_comm`
    trans ∑' k : ℤ, Work.BourgainPlan.IonescuWainger.torsionKernel A
        (fun l : ℤ => ∫ ξ, φ ξ * star (fourier l ξ)
          ∂(AddCircle.haarAddCircle (T := 1))) (n - k) * h k
    · exact tsum_congr fun k => mul_comm _ _
    · refine (tsum_congr fun j => ?_).symm
      rw [Work.BourgainPlan.Thm52.decimatedKernel_neg_coe_eq_torsionKernel (A := A) φ hφ (n - j)]

end Work.BourgainPlan.Thm52
