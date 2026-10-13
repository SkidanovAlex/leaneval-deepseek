import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.FTS.StrongEps.N0_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps

/-- The scalar expression `N α F Φ z θ`, regrouped as a function of the seven numbers
`Φ̃ z θ`, `D_zΦ̃ z θ`, `∂_θΦ̃ z θ`, `F z θ`, `D_zF z θ`, `∂_θF z θ`, `(F,K)(z)` (where
`Φ̃ = PhiTil α F Φ`).  This is the form in which the limit of `N` is computed: each of the
seven arguments is one of the quantities controlled by the hypotheses of `gRHS_tendsto`. -/
noncomputable def gRHSNEval (α θ : ℝ) (g0 g1 g2 f0 f1 p2 k : ℝ) : ℝ :=
  (((2 * ((2 * Real.sin θ * g0 + α * Real.sin θ * g1 + Real.cos θ * g2) / Real.cos θ)) * f0)
    - ((2 * ((-3) * g0 - α * g1)) * p2))
    - (((2 * α) * (g2 - Real.tan θ * g0)) * f1)
    - ((((1 / 2) * Real.sin (2 * θ)) * k) * p2)
    - ((Real.sin θ ^ 2 * k) * f0)

/-- `N`, evaluated at a point, is the scalar expression `gRHSNEval` applied to the values
and the first derivatives of `F` and of `PhiTil α F Φ`. -/
theorem N_eq_gRHSNEval {α z θ : ℝ} (f Φ : ℝ → ℝ → ℝ) :
    Work.Construction.N α f Φ z θ
      = gRHSNEval α θ (Work.Construction.PhiTil α f Φ z θ)
          (Work.Spaces.Dz (Work.Construction.PhiTil α f Φ) z θ)
          (Work.Spaces.pth (Work.Construction.PhiTil α f Φ) z θ)
          (f z θ) (Work.Spaces.Dz f z θ) (Work.Spaces.pth f z θ)
          (Work.Construction.FK f z) := by
  simp only [gRHSNEval, Work.Construction.N, Work.Construction.Rop, Work.Construction.Uop,
    Work.Construction.Vop, Work.Spaces.Dz, Work.Construction.s2]
  ring

/-- **Pointwise convergence of `N`.**  If the slots of order `≤ 1` of `F n` converge at
`(z,θ)` to those of `Flim`, the same holds for `PhiTil α (F n) (Φ n)` with limit
`PhiTil α Flim Φlim`, and `(F n, K)(z)` converges to `(Flim, K)(z)`, then
`N α (F n) (Φ n) z θ` converges to `N α Flim Φlim z θ`.

`N` depends on its third argument only through `PhiTil α F Φ`, so the hypothesis on the
slots of `PhiTil` is exactly what is needed (in particular no hypothesis on `L₁₂ (F n)` is
required, unlike in the sibling `N_tendsto`).  The only place where `θ ∈ (0, π/2)` enters
is in dividing the `D_θ`-slots by `sin(2θ)`, because `N` sees the *plain* derivative
`∂_θ`; the `D_z`-slots are used as they stand (`z ∂_z` is exactly the combination occurring
in `Uop`, `Rop`), so `z > 0` is *not* needed for this lemma. -/
theorem N_tendsto_of_PhiTil {α : ℝ} {F : ℕ → Work.FTS.Galerkin.Fn} {Fl : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → Work.FTS.Galerkin.Fn} {Φl : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (_hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Fl z θ)))
    (hTil : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.PhiTil α Fl Φl) z θ)))
    (hFK : Filter.Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Fl z))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Φ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Fl Φl z θ)) := by
  have hs2 : Real.sin (2 * θ) ≠ 0 := by
    have h2θ : 0 < 2 * θ := by linarith [hθ.1]
    have h2π : 2 * θ < Real.pi := by linarith [hθ.2]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi h2θ h2π)
  have hA0 : Filter.Tendsto (fun n : ℕ => Work.Construction.PhiTil α (F n) (Φ n) z θ)
      Filter.atTop (nhds (Work.Construction.PhiTil α Fl Φl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hTil 0 0 (by norm_num)
  have hA1 : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.Dz (Work.Construction.PhiTil α (F n) (Φ n)) z θ)
      Filter.atTop (nhds (Work.Spaces.Dz (Work.Construction.PhiTil α Fl Φl) z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hTil 1 0 (by norm_num)
  have hA2 : Filter.Tendsto
      (fun n : ℕ => Work.Spaces.Dth (Work.Construction.PhiTil α (F n) (Φ n)) z θ)
      Filter.atTop (nhds (Work.Spaces.Dth (Work.Construction.PhiTil α Fl Φl) z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using hTil 0 1 (by norm_num)
  have hF0 : Filter.Tendsto (fun n : ℕ => F n z θ) Filter.atTop (nhds (Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hF 0 0 (by norm_num)
  have hF1 : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hF 1 0 (by norm_num)
  have hF2d : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dth (F n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dth Fl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using hF 0 1 (by norm_num)
  -- `D_θ = sin(2θ)·∂_θ`, and `sin(2θ) ≠ 0` on the open quadrant, so the `∂_θ`-slots
  -- converge as well.
  have hDthPth : ∀ (G : ℕ → ℝ → ℝ → ℝ) (Gl : ℝ → ℝ → ℝ),
      Filter.Tendsto (fun n : ℕ => Work.Spaces.Dth (G n) z θ) Filter.atTop
        (nhds (Work.Spaces.Dth Gl z θ)) →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.pth (G n) z θ) Filter.atTop
        (nhds (Work.Spaces.pth Gl z θ)) := by
    intro G Gl h
    have h' := h.const_mul ((Real.sin (2 * θ))⁻¹)
    have he : ∀ Ψ : ℝ → ℝ → ℝ,
        (Real.sin (2 * θ))⁻¹ * Work.Spaces.Dth Ψ z θ = Work.Spaces.pth Ψ z θ := by
      intro Ψ
      simp only [Work.Spaces.Dth]
      exact inv_mul_cancel_left₀ hs2 _
    simpa only [he] using h'
  have hA3 := hDthPth _ _ hA2
  have hF2 := hDthPth _ _ hF2d
  -- The five summands of `gRHSNEval`, each convergent by continuity of the basic
  -- operations (and multiplication by the constants of `θ`).
  have hstep : Filter.Tendsto (fun n : ℕ => gRHSNEval α θ
        (Work.Construction.PhiTil α (F n) (Φ n) z θ)
        (Work.Spaces.Dz (Work.Construction.PhiTil α (F n) (Φ n)) z θ)
        (Work.Spaces.pth (Work.Construction.PhiTil α (F n) (Φ n)) z θ)
        (F n z θ) (Work.Spaces.Dz (F n) z θ) (Work.Spaces.pth (F n) z θ)
        (Work.Construction.FK (F n) z)) Filter.atTop
      (nhds (gRHSNEval α θ (Work.Construction.PhiTil α Fl Φl z θ)
        (Work.Spaces.Dz (Work.Construction.PhiTil α Fl Φl) z θ)
        (Work.Spaces.pth (Work.Construction.PhiTil α Fl Φl) z θ)
        (Fl z θ) (Work.Spaces.Dz Fl z θ) (Work.Spaces.pth Fl z θ)
        (Work.Construction.FK Fl z))) := by
    have hnum := ((hA0.const_mul (2 * Real.sin θ)).add
      (hA1.const_mul (α * Real.sin θ))).add (hA3.const_mul (Real.cos θ))
    have hT1 := ((hnum.div_const (Real.cos θ)).const_mul 2).mul hF0
    have hT2 := (((hA0.const_mul (-3)).sub (hA1.const_mul α)).const_mul 2).mul hF2
    have hT3 := (((hA3.sub (hA0.const_mul (Real.tan θ)))).const_mul (2 * α)).mul hF1
    have hT4 := (hFK.const_mul ((1 / 2) * Real.sin (2 * θ))).mul hF2
    have hT5 := (hFK.const_mul (Real.sin θ ^ 2)).mul hF0
    simp only [gRHSNEval]
    exact (((hT1.sub hT2).sub hT3).sub hT4).sub hT5
  rw [show (fun n : ℕ => Work.Construction.N α (F n) (Φ n) z θ) = fun n : ℕ => gRHSNEval α θ
        (Work.Construction.PhiTil α (F n) (Φ n) z θ)
        (Work.Spaces.Dz (Work.Construction.PhiTil α (F n) (Φ n)) z θ)
        (Work.Spaces.pth (Work.Construction.PhiTil α (F n) (Φ n)) z θ)
        (F n z θ) (Work.Spaces.Dz (F n) z θ) (Work.Spaces.pth (F n) z θ)
        (Work.Construction.FK (F n) z) from
      funext (fun n => N_eq_gRHSNEval (F n) (Φ n))]
  rw [show Work.Construction.N α Fl Φl z θ = gRHSNEval α θ
        (Work.Construction.PhiTil α Fl Φl z θ)
        (Work.Spaces.Dz (Work.Construction.PhiTil α Fl Φl) z θ)
        (Work.Spaces.pth (Work.Construction.PhiTil α Fl Φl) z θ)
        (Fl z θ) (Work.Spaces.Dz Fl z θ) (Work.Spaces.pth Fl z θ)
        (Work.Construction.FK Fl z) from N_eq_gRHSNEval Fl Φl]
  exact hstep

theorem gRHS_tendsto {α : ℝ} {μ : ℕ → ℝ} {μl : ℝ} {lam : ℕ → ℝ} {laml : ℝ}
    {F : ℕ → Work.FTS.Galerkin.Fn} {Fl : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → Work.FTS.Galerkin.Fn} {Φl : Work.FTS.Galerkin.Fn}
    {w : ℕ → Work.FTS.Galerkin.Fn} {wl : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hμ : Filter.Tendsto μ Filter.atTop (nhds μl))
    (hlam : Filter.Tendsto lam Filter.atTop (nhds laml))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Fl z θ)))
    (hw : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (w n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i wl z θ)))
    (hTil : ∀ j i : ℕ, j + i ≤ 1 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (F n) (Φ n)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.PhiTil α Fl Φl) z θ)))
    (hFK : Filter.Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Fl z)))
    (hlw : ∀ z' ∈ Work.Spaces.Iz, Filter.Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z')
      Filter.atTop (nhds (Work.Construction.L12 wl z')))
    (hmubar : Filter.Tendsto (fun n : ℕ => Work.Construction.mubar
      (Work.Construction.N0 α (F n) (w n)) (Work.Construction.N α (F n) (Φ n))) Filter.atTop
      (nhds (Work.Construction.mubar (Work.Construction.N0 α Fl wl)
        (Work.Construction.N α Fl Φl)))) :
    Filter.Tendsto (fun n : ℕ => Work.Construction.gRHS α (μ n) (lam n) (F n) (Φ n) (w n) z θ)
      Filter.atTop (nhds (Work.Construction.gRHS α μl laml Fl Φl wl z θ)) := by
  -- `gRHS = -μ̄·AK + N₀ + N + N_*`, and each of the four summands converges.
  have hN : Filter.Tendsto (fun n : ℕ => Work.Construction.N α (F n) (Φ n) z θ) Filter.atTop
      (nhds (Work.Construction.N α Fl Φl z θ)) :=
    N_tendsto_of_PhiTil hz hθ hF hTil hFK
  have hN0 : Filter.Tendsto (fun n : ℕ => Work.Construction.N0 α (F n) (w n) z θ) Filter.atTop
      (nhds (Work.Construction.N0 α Fl wl z θ)) :=
    N0_tendsto (show z ∈ Work.Spaces.Iz from hz.le) hF hw hlw
  have hNs : Filter.Tendsto (fun n : ℕ => Work.Construction.Nstar (μ n) (lam n) (w n) z θ)
      Filter.atTop (nhds (Work.Construction.Nstar μl laml wl z θ)) := by
    have hw0 : Filter.Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (wl z θ)) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
        using hw 0 0 (by norm_num)
    have hw1 : Filter.Tendsto (fun n : ℕ => Work.Spaces.Dz (w n) z θ) Filter.atTop
        (nhds (Work.Spaces.Dz wl z θ)) := by
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
        Work.Spaces.DthIter_zero] using hw 1 0 (by norm_num)
    have hcoef : Filter.Tendsto (fun n : ℕ => μ n + lam n + μ n * lam n) Filter.atTop
        (nhds (μl + laml + μl * laml)) := (hμ.add hlam).add (hμ.mul hlam)
    have hmain := (hμ.neg.mul hw0).sub (hcoef.mul hw1)
    rw [show (fun n : ℕ => Work.Construction.Nstar (μ n) (lam n) (w n) z θ) = fun n : ℕ =>
          (-μ n) * (w n z θ) - (μ n + lam n + μ n * lam n) * Work.Spaces.Dz (w n) z θ from
        funext (fun n => by simp only [Work.Construction.Nstar])]
    rw [show Work.Construction.Nstar μl laml wl z θ =
          (-μl) * (wl z θ) - (μl + laml + μl * laml) * Work.Spaces.Dz wl z θ from by
        simp only [Work.Construction.Nstar]]
    exact hmain
  have hAK : Filter.Tendsto (fun _ : ℕ => Work.Construction.AK α z θ) Filter.atTop
      (nhds (Work.Construction.AK α z θ)) := tendsto_const_nhds
  have hmain := (((hmubar.neg.mul hAK).add hN0).add hN).add hNs
  rw [show (fun n : ℕ => Work.Construction.gRHS α (μ n) (lam n) (F n) (Φ n) (w n) z θ)
      = fun n : ℕ =>
          ((-(Work.Construction.mubar (Work.Construction.N0 α (F n) (w n))
                (Work.Construction.N α (F n) (Φ n))) * Work.Construction.AK α z θ)
            + Work.Construction.N0 α (F n) (w n) z θ)
            + Work.Construction.N α (F n) (Φ n) z θ
            + Work.Construction.Nstar (μ n) (lam n) (w n) z θ from
      funext (fun n => by simp only [Work.Construction.gRHS])]
  rw [show Work.Construction.gRHS α μl laml Fl Φl wl z θ =
          ((-(Work.Construction.mubar (Work.Construction.N0 α Fl wl)
                (Work.Construction.N α Fl Φl)) * Work.Construction.AK α z θ)
            + Work.Construction.N0 α Fl wl z θ)
            + Work.Construction.N α Fl Φl z θ
            + Work.Construction.Nstar μl laml wl z θ from by
      simp only [Work.Construction.gRHS]]
  exact hmain

end Work.FTS.StrongEps
