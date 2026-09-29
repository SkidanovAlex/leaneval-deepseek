import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.dyIter_diffOn_ninth
import Submission.Work.A14D.dy_step_ninth

/-!
# A14D `decomp_G`: the `log`-decomposition of the jump of the fourteen functions

`jumpH D = D − D∘w` is the jump of the continued `H` across the cut `(−∞,1]`.  On the upper
half-disc `halfU δ = ball (1/9) δ ∩ {Im > 0}` the hypothesis `LogCoeff y9 δ (halfU δ) D κU` gives

  `D z = κU · y9 z · log (z − 1/9) + h z`   (`h` holomorphic on the whole disc),

while `De = D ∘ w` is holomorphic on the disc, so on `halfU δ`

  `jumpH D z = κU · y9 z · log (z − 1/9) + (h z − De z)`.

The main content is that the `∂_y`-iterates of a function of the shape `A·log(·−1/9) + (holomorphic)`
on the *open* set `halfU δ` again have that shape, with the "non-log part" acquiring a pole of order
at most `k` at `1/9`: for every `k` there is `Gk` holomorphic on `ball (1/9) δ` with

  `∂_y^k (jumpH D) = (∂_y^k (κU·y9)) · log (· − 1/9) + Gk/(· − 1/9)^k`   on `halfU δ`.

The derivative of the model function at a point of the open set `halfU δ` is forced by
`Filter.EventuallyEq.deriv_eq`, so no differentiability of `jumpH D` is needed.  Multiplying by
`(· − 1/9)^{k+1}` clears the pole, which is the conclusion of `decomp_G` with `m := k + 1`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## 0. Auxiliary facts about `∂_y` -/

/-- `∂_y^{k+1} f = ∂_y (∂_y^k f)`. -/
theorem DyIter_succ (k : ℕ) (f : ℂ → ℂ) : DyIter (k + 1) f = Dy (DyIter k f) := by
  simpa only [DyIter] using Function.iterate_succ_apply' Dy k f

/-- `∂_y` is `ℂ`-linear in the scalar. -/
theorem Dy_const_mul (c : ℂ) (f : ℂ → ℂ) :
    Dy (fun z => c * f z) = fun z => c * Dy f z := by
  funext z
  simp only [Dy]
  rw [deriv_const_mul_field]
  ring

/-- Hence `∂_y^k` is `ℂ`-linear in the scalar. -/
theorem DyIter_const_mul (c : ℂ) (k : ℕ) (f : ℂ → ℂ) :
    DyIter k (fun z => c * f z) = fun z => c * DyIter k f z := by
  induction k with
  | zero => simp [DyIter]
  | succ k ih =>
      rw [DyIter_succ k (fun z => c * f z), ih, DyIter_succ k f]
      exact Dy_const_mul c (DyIter k f)

/-! ## 1. The `log`-structure of the `∂_y`-iterates on `halfU δ` -/

/-- **The `log`-decomposition of the `∂_y`-iterates.**  If `F` agrees on the upper half-disc
`halfU δ` with `A · log (· − 1/9) + G`, where `A` and `G` are holomorphic on the disc, then each
iterate `∂_y^k F` agrees there with `∂_y^k A · log (· − 1/9) + Gk/(· − 1/9)^k` with `Gk` holomorphic
on the disc. -/
theorem dyIter_log_struct_halfU {δ : ℝ} (hδ : δ ≤ 1 / 20) {F A G : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (Metric.ball ninth δ))
    (hG : DifferentiableOn ℂ G (Metric.ball ninth δ))
    (h : ∀ z ∈ halfU δ, F z = A z * Complex.log (z - ninth) + G z) :
    ∀ k : ℕ, ∃ Gk : ℂ → ℂ, DifferentiableOn ℂ Gk (Metric.ball ninth δ) ∧
      ∀ z ∈ halfU δ,
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
        dy_step_ninth hδ (m := k) (F := DyIter k F) (A := DyIter k A) (G := Gk)
          (hAk k) hGk hval
      refine ⟨G', hG', ?_⟩
      intro z hz
      rw [DyIter_succ, DyIter_succ]
      exact hval' z hz

/-! ## 2. The target lemma -/

theorem decomp_G {y9 D De : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) (κU : ℂ)
    (hY : Y9 y9 δ)
    (hU : LogCoeff y9 δ (halfU δ) D κU)
    (hDe : DifferentiableOn ℂ De (Metric.ball ninth δ))
    (hDeeq : ∀ z ∈ halfU δ, De z = D (wC z))
    (k : Fin 4) :
    ∃ (m : ℕ) (B : ℂ → ℂ),
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (Metric.ball ninth δ) ∧
      ∀ z ∈ halfU δ,
        DyIter (k : ℕ) (jumpH D) z = κU * DyIter (k : ℕ) y9 z * Complex.log (z - ninth) + B z := by
  obtain ⟨h, hh, hDeq⟩ := hU
  obtain ⟨_, _, hy9d, _, _⟩ := hY
  have hs : DifferentiableOn ℂ (fun z => h z - De z) (Metric.ball ninth δ) := hh.sub hDe
  have hA : DifferentiableOn ℂ (fun z => κU * y9 z) (Metric.ball ninth δ) :=
    hy9d.const_mul κU
  have hF : ∀ z ∈ halfU δ,
      jumpH D z = (fun z => κU * y9 z) z * Complex.log (z - ninth) + (h z - De z) := by
    intro z hz
    have h1 := hDeq z hz
    have h2 := hDeeq z hz
    simp only [jumpH]
    rw [h1, h2]
    ring
  obtain ⟨Gk, hGk, hval⟩ :=
    dyIter_log_struct_halfU hδ20 hA hs hF (k : ℕ)
  have hlin : DyIter (k : ℕ) (fun z => κU * y9 z) = fun z => κU * DyIter (k : ℕ) y9 z :=
    DyIter_const_mul κU (k : ℕ) y9
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
