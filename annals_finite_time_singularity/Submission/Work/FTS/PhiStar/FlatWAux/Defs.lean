/-
# `Work.FTS.PhiStar.FlatWAux.Defs` — the angular series objects of the `FlatW_psiSeries` route

This directory proves the `R`-term flat estimate

`FlatW 7 (fun z θ => (z+1)/z · psiSeries α (RemSource α ψ) z θ / sin 2θ) (C α²)`

of the `PhiStar` chapter.  The source `RemSource α ψ = α²·phiA α·ψ` is separable, so the mode
series of the solution is an explicit `m`-series, and the estimate runs on the expansion

`radGreen α m c = Σ_{j<J} α^j (𝒜^j c)/λ_m^{j+1} + (α^J/λ_m^{J+1})·λ_m·radGreen α m (𝒜^J c)`

(`𝒜 = αz²∂² + (5+α)z∂`, `λ_m = 2m(2m+5)`), which separates the `m`-dependence as the reciprocal
power `λ_m^{-(j+1)}`.  Because `Σ_m b_m λ_m^{-(j+1)} e_m(θ)` is *not* summable termwise after
dividing by `sin 2θ` (the `1/λ_m`-gain is what makes it converge at all), the `m`-sum has to be
resummed: it is the `(j+1)`-th member of the family

`W_j(θ) = Σ_m b_m λ_m^{-j} (eFam m θ / sin 2θ)`,   `W_0 = ψ/sin 2θ`,

whose `θ`-derivatives are produced by the zero-moment inverse `Linv`:

`deriv (W_{j+1}) = Linv (sin 2θ · W_j)`   on `(0,π/2)`

(the `j = 0` instance being `deriv(ψ/sin 2θ) = Linv ψ`, i.e. `FlatW_psiDiv`'s first-order
equation).  This file fixes the objects; `FlatWAux/AngPackage.lean` proves their bounds, and
`PhiStar/FlatW_psiSeries.lean` assembles the estimate.

* `Qm m = eFam m / sin 2θ` — the divided angular mode (a smooth function on `(0,π/2)`);
* `Wt ψ j` — the resummed angular profile `W_j` (`Wt ψ 0 = ψ/sin 2θ`, and for `j ≥ 1` the
  `λ_m^{-j}`-resummed series);
* `chia ψ j = sin 2θ · Wt ψ j` — its `sin 2θ`-multiple (`chia ψ 0 = ψ` away from the endpoints),
  which is the argument of `Linv` in the differentiation identity above;
* `J` — the truncation order of the radial expansion (chosen `8`).

The hypotheses under which the bounds are produced are collected in the structure-free lemmas of
`FlatWAux/AngPackage.lean`; the only inputs about `ψ` are that it is an `AngModel`, the
coefficient decay `|b_m| ≤ C/(λ_m √(2m+1))` and the `FlatW 7 (ψ/sin 2θ) C` bound.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- The divided angular mode `Q_m = eFam m / sin 2θ` (Lean's `0/0 = 0` at the endpoints; only the
open interval is used). -/
def Qm (m : ℕ) : ℝ → ℝ := fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ / Work.Construction.s2 θ

/-- The resummed angular profile of the expansion: `Wt ψ 0 = ψ / sin 2θ` and, for `j ≥ 1`,
`Wt ψ j = Σ_m b_m λ_m^{-j} Q_m` with `b_m = bmode m ψ`. -/
def Wt (ψ : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun θ => ψ θ / Work.Construction.s2 θ
  | (j + 1) => fun θ =>
      ∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j + 1)
          * Qm m θ

/-- `chia ψ j = sin 2θ · Wt ψ j`: the function whose `Linv` gives the derivative of the next
profile.  On `(0,π/2)`, `chia ψ 0 = ψ`. -/
def chia (ψ : ℝ → ℝ) (j : ℕ) : ℝ → ℝ := fun θ => Work.Construction.s2 θ * Wt ψ j θ

/-- Truncation order of the radial expansion (`J = 8`). -/
def J : ℕ := 8

/-- `Wt ψ 0` is `ψ / sin 2θ` (definitional). -/
theorem Wt_zero (ψ : ℝ → ℝ) : Wt ψ 0 = fun θ => ψ θ / Work.Construction.s2 θ := rfl

/-- `chia ψ j = sin 2θ · Wt ψ j` (definitional). -/
theorem chia_eq (ψ : ℝ → ℝ) (j : ℕ) :
    chia ψ j = fun θ => Work.Construction.s2 θ * Wt ψ j θ := rfl

/-- For `θ ≠ 0, π/2` the `sin 2θ`-multiple of `Q_m` is `eFam m`. -/
theorem s2_mul_Qm {m : ℕ} {θ : ℝ} (h : Work.Construction.s2 θ ≠ 0) :
    Work.Construction.s2 θ * Qm m θ = Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  simp only [Qm]
  field_simp

/-- On the open interval, `chia ψ 0 = ψ`. -/
theorem chia_zero {ψ : ℝ → ℝ} {θ : ℝ}
    (hs : Work.Construction.s2 θ ≠ 0) : chia ψ 0 θ = ψ θ := by
  simp only [chia, Wt_zero]
  field_simp

/-- The series form of `chia` on the open interval: for `j ≥ 1`,
`chia ψ j = Σ_m b_m λ_m^{-j} eFam m`. -/
theorem chia_eq_tsum (ψ : ℝ → ℝ) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    chia ψ (j + 1) θ
      = ∑' m : ℕ,
          Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  have hs : Work.Construction.s2 θ ≠ 0 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
    exact mul_ne_zero (mul_ne_zero two_ne_zero
        (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))
  show Work.Construction.s2 θ * Wt ψ (j + 1) θ = _
  simp only [Wt]
  rw [← tsum_mul_left]
  refine tsum_congr (fun m => ?_)
  rw [← s2_mul_Qm (m := m) hs]
  ring

end Work.FTS.PhiStar.FlatWAux
