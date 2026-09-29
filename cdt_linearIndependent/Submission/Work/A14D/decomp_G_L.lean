import Mathlib
import Submission.Work.A14D.decomp_G
import Submission.Work.A14D.LC_setup
import Submission.Work.A14.defs
import Submission.Work.A14D.dy_step_slitIm

/-!
# A14D `decomp_G_L`: the `log`-decomposition of the jump of the fourteen functions, *lower* half

This is the lower-half-disc companion of `Work.A14D.decomp_G`.  `jumpH D = D − D∘w` is the jump of
the continued `H` across the cut `(−∞,1]`.  On the lower half-disc `halfL δ = ball (1/9) δ ∩ {Im < 0}`
the hypothesis `LogCoeff y9 δ (halfL δ) D κL` gives

  `D z = κL · y9 z · log (z − 1/9) + h z`   (`h` holomorphic on the whole disc),

while `De = D ∘ w` is holomorphic on the disc, so on `halfL δ`

  `jumpH D z = κL · y9 z · log (z − 1/9) + (h z − De z)`.

The analytic content is `dyIter_log_struct_slitIm`: the `∂_y`-iterates of a function of the shape
`A·log(·−1/9) + (holomorphic)` on an *open* set `V ⊆ ball (1/9) δ` avoiding the branch cut of the
principal logarithm again have that shape, with the "non-log part" acquiring a pole of order at most
`k` at `1/9`: for every `k` there is `Gk` holomorphic on `ball (1/9) δ` with

  `∂_y^k (jumpH D) = (∂_y^k (κL·y9)) · log (· − 1/9) + Gk/(· − 1/9)^k`   on `halfL δ`.

Multiplying by `(· − 1/9)^{k+1}` clears the pole, which is the conclusion of `decomp_G_L` with
`m := k + 1`.  (On `halfL δ` the point `z − 1/9` has negative imaginary part, hence lies in
`Complex.slitPlane`; the principal `Complex.log` is holomorphic there with derivative
`1/(· − 1/9)`, so no sign condition is needed.)
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- `∂_y`-iterates of a `log`-structured function on an open piece `V` of the disc avoiding the real
axis: if `F` agrees on `V` with `A · log (· − 1/9) + G` with `A`, `G` holomorphic on
`Metric.ball ninth δ`, then each iterate `∂_y^k F` agrees there with
`∂_y^k A · log (· − 1/9) + Gk/(· − 1/9)^k` with `Gk` holomorphic on the disc. -/
theorem dyIter_log_struct_slitIm {δ : ℝ} (hδ : δ ≤ 1 / 20) {V : Set ℂ}
    (hVopen : IsOpen V) (hVsub : V ⊆ Metric.ball ninth δ) (hVim : ∀ z ∈ V, z.im ≠ 0)
    {F A G : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (Metric.ball ninth δ))
    (hG : DifferentiableOn ℂ G (Metric.ball ninth δ))
    (h : ∀ z ∈ V, F z = A z * Complex.log (z - ninth) + G z) :
    ∀ k : ℕ, ∃ Gk : ℂ → ℂ, DifferentiableOn ℂ Gk (Metric.ball ninth δ) ∧
      ∀ z ∈ V,
        DyIter k F z = DyIter k A z * Complex.log (z - ninth) + Gk z / (z - ninth) ^ k := by
  intro k
  have hAk : ∀ j : ℕ, DifferentiableOn ℂ (DyIter j A) (Metric.ball ninth δ) :=
    dyIter_diffOn_ninth hδ hA
  induction k with
  | zero =>
      refine ⟨G, hG, ?_⟩
      intro z hz
      simpa [DyIter] using h z hz
  | succ k ih =>
      obtain ⟨Gk, hGk, hval⟩ := ih
      obtain ⟨G', hG', hval'⟩ :=
        dy_step_slitIm hδ hVopen hVsub hVim (hAk k) hGk hval
      refine ⟨G', hG', ?_⟩
      intro z hz
      rw [DyIter_succ, DyIter_succ]
      exact hval' z hz

/-! ## The target lemma -/

theorem decomp_G_L {y9 D De : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) (κL : ℂ)
    (hY : Y9 y9 δ)
    (hL : LogCoeff y9 δ (halfL δ) D κL)
    (hDe : DifferentiableOn ℂ De (Metric.ball ninth δ))
    (hDeeq : ∀ z ∈ halfL δ, De z = D (wC z))
    (k : Fin 4) :
    ∃ (m : ℕ) (B : ℂ → ℂ),
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (Metric.ball ninth δ) ∧
      ∀ z ∈ halfL δ,
        DyIter (k : ℕ) (jumpH D) z = κL * DyIter (k : ℕ) y9 z * Complex.log (z - ninth) + B z := by
  obtain ⟨h, hh, hDeq⟩ := hL
  obtain ⟨_, _, hy9d, _, _⟩ := hY
  have hs : DifferentiableOn ℂ (fun z => h z - De z) (Metric.ball ninth δ) := hh.sub hDe
  have hA : DifferentiableOn ℂ (fun z => κL * y9 z) (Metric.ball ninth δ) := hy9d.const_mul κL
  have hF : ∀ z ∈ halfL δ,
      jumpH D z = (fun z => κL * y9 z) z * Complex.log (z - ninth) + (h z - De z) := by
    intro z hz
    have h1 := hDeq z hz
    have h2 := hDeeq z hz
    simp only [jumpH]
    rw [h1, h2]
    ring
  have hVopen : IsOpen (halfL δ) := by
    rw [halfL]
    exact Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)
  have hVsub : halfL δ ⊆ Metric.ball ninth δ := fun z hz => hz.1
  have hVim : ∀ z ∈ halfL δ, z.im ≠ 0 := fun z hz => ne_of_lt hz.2
  obtain ⟨Gk, hGk, hval⟩ :=
    dyIter_log_struct_slitIm hδ20 hVopen hVsub hVim hA hs hF (k : ℕ)
  have hlin : DyIter (k : ℕ) (fun z => κL * y9 z) = fun z => κL * DyIter (k : ℕ) y9 z :=
    DyIter_const_mul κL (k : ℕ) y9
  refine ⟨(k : ℕ) + 1, fun z => Gk z / (z - ninth) ^ (k : ℕ), ?_, ?_⟩
  · have heq : (fun z : ℂ => (z - ninth) ^ ((k : ℕ) + 1) * (Gk z / (z - ninth) ^ (k : ℕ)))
        = fun z : ℂ => (z - ninth) * Gk z := by
      funext z
      by_cases hz : z = ninth
      · subst hz
        simp
      · have hz' : z - ninth ≠ 0 := sub_ne_zero.mpr hz
        rw [pow_succ]
        field_simp
    rw [heq]
    exact (differentiableOn_id.sub (differentiableOn_const ninth)).mul hGk
  · intro z hz
    have hz' := hval z hz
    rw [hlin] at hz'
    exact hz'

end

end Work.A14D
