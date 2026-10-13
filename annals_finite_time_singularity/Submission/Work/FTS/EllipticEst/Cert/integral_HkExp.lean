import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Cert.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

/-- Linearity of the integral over `Iθ` against a *fixed* angular profile `f`, for a finite
sum whose coefficients are independent of `θ`. -/
lemma integral_sum_mul_const (s : Finset ℕ) (c : ℕ → ℝ) (f : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, c i * f θ)
      = (∑ i ∈ s, c i) * ∫ θ in Work.Spaces.Iθ, f θ := by
  have hfun : (fun θ => ∑ i ∈ s, c i * f θ) = fun θ => (∑ i ∈ s, c i) * f θ := by
    funext θ; exact (Finset.sum_mul s c (f θ)).symm
  rw [hfun, integral_const_mul]

/-- Linearity of the integral over `Iθ` for a finite sum of `if p i then c i * f θ else 0`,
where the proposition `p i` does not depend on `θ`: the sum can be integrated termwise. -/
lemma integral_sum_ite_mul_const (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (c : ℕ → ℝ) (f : ℝ → ℝ) (hf : IntegrableOn f Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, (if p i then c i * f θ else 0))
      = ∑ i ∈ s, (if p i then c i * (∫ θ in Work.Spaces.Iθ, f θ) else 0) := by
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hp : p i
    · simp only [hp, ite_true]; rw [integral_const_mul]
    · simp only [hp]; simp
  · intro i _
    by_cases hp : p i
    · simp only [hp]; exact hf.integrable.const_mul _
    · simp only [hp]; exact integrable_zero _ _ _

/-- The two-index version of `integral_sum_ite_mul_const`: a double finite sum whose
`(i,j)`-term is `if p i j then c i j * g i θ else 0`, with the angular profile `g i`
depending only on the outer index. -/
lemma integral_sum2_ite_mul_const (s : Finset ℕ) (p : ℕ → ℕ → Prop) [DecidableRel p]
    (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ i, IntegrableOn (g i) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, ∑ j ∈ s, (if p i j then c i j * g i θ else 0))
      = ∑ i ∈ s, ∑ j ∈ s, (if p i j then c i j * (∫ θ in Work.Spaces.Iθ, g i θ) else 0) := by
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sum_ite_mul_const s (p i) (c i) (g i) (hg i)]
  · intro i _
    refine integrable_finset_sum _ fun j _ => ?_
    by_cases hp : p i j
    · simp only [hp]; exact (hg i).integrable.const_mul _
    · simp only [hp]; exact integrable_zero _ _ _

/-- The purely algebraic rearrangement used at the end of `integral_HkExp`: the explicit
`θ`-integral of the separated `ℋ^k`-integrand equals `W` times the boxed separated
expression, with the radial weight `W` pulled out of both sums and the coefficients of the
second (mixed) double sum moved next to the angular integrals. -/
lemma HkExp_algebra (S : Finset ℕ) (W Z : ℝ) (a A : ℕ → ℝ) (p : ℕ → ℕ → Prop)
    [DecidableRel p] :
    (∑ i ∈ S, a i * W) * Z + ∑ i ∈ S, ∑ j ∈ S, (if p i j then a j * W * A i else 0)
      = W * (Z * ∑ i ∈ S, a i + ∑ i ∈ S, ∑ j ∈ S, (if p i j then a j else 0) * A i) := by
  have h1 : (∑ i ∈ S, a i * W) * Z = W * (Z * ∑ i ∈ S, a i) := by
    rw [← Finset.sum_mul]; ring
  have hinner : ∀ i, (∑ j ∈ S, (if p i j then a j * W * A i else 0))
      = W * ((∑ j ∈ S, (if p i j then a j else 0)) * A i) := by
    intro i
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : p i j <;> simp [hp] <;> ring
  have h2 : (∑ i ∈ S, ∑ j ∈ S, (if p i j then a j * W * A i else 0))
      = W * (∑ i ∈ S, (∑ j ∈ S, (if p i j then a j else 0)) * A i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hinner i
  rw [h1, h2]
  simp only [Finset.sum_mul]
  ring

theorem integral_HkExp (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ)
    (hZ : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.Cert.angZ θ)
      Work.Spaces.Iθ)
    (hA : ∀ i : ℕ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Cert.angA α i θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.HkExp α k R z θ)
      = (Work.Spaces.w z) ^ 2 *
          ((∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.angZ θ)
              * (∑ i ∈ Finset.range (k + 1),
                  (Work.FTS.EllipticEst.radIter R i z) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.FTS.EllipticEst.radIter R j z) ^ 2 else 0)
                  * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.angA α i θ)) := by
  simp only [HkExp]
  have hI1 : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.FTS.EllipticEst.radIter R i z) ^ 2 * (Work.Spaces.w z) ^ 2 * angZ θ)
      (volume.restrict Work.Spaces.Iθ) := by
    refine integrable_finset_sum _ fun i _ => ?_
    exact hZ.const_mul _
  have hI2 : Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then
        (Work.FTS.EllipticEst.radIter R j z) ^ 2 * (Work.Spaces.w z) ^ 2 * angA α i θ
      else 0)
      (volume.restrict Work.Spaces.Iθ) := by
    refine integrable_finset_sum _ fun i _ => ?_
    refine integrable_finset_sum _ fun j _ => ?_
    by_cases hp : 1 ≤ i ∧ i + j ≤ k
    · simp only [hp]; exact (hA i).const_mul _
    · simp only [hp]; exact integrable_zero _ _ _
  rw [MeasureTheory.integral_add hI1 hI2]
  rw [integral_sum_mul_const]
  rw [integral_sum2_ite_mul_const _ (fun i j => 1 ≤ i ∧ i + j ≤ k) _ _ (fun i => hA i)]
  exact HkExp_algebra _ _ _ _ _ _

end Work.FTS.EllipticEst.Cert
