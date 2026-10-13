/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsWPLim/gRHSStep.lean`

**The pointwise limit of `Construction.gRHS`** — the `gRHS_tendsto` step of the `E5`
identification, with the modulation constants `μ`, `λ` hypothesised to converge *separately*.

`gRHS α μ lam F Φ w z θ = -mubar (N0 α F w) (N α F Φ) · AK α z θ + N0 α F w z θ
+ N α F Φ z θ + Nstar μ lam w z θ`, so the four blocks are

* `mubar (N0 α (F n) (w n)) (N α (F n) (Ψ n))` — the hypothesis `hmubar`;
* `N0 α (F n) (w n) z θ` — `N0_tendsto` (slots of `F`, slots of `w`, `L₁₂(w)(z')`);
* `N α (F n) (Ψ n) z θ` — `N_tendsto_of_PhiTil` (slots of `F`, `FK F z`, slots of
  `PhiTil α F Φ`);
* `Nstar (μ n) (lam n) (w n) z θ` — bilinear in the two scalars and the two slots
  `w z θ`, `D_z w z θ` of `w`.

Note that `λ` must converge **on its own**: `lamDyn α Φ g τ = lamfun (muDyn α Φ g τ)`, and
`lamfun μ = -2μ/(1+μ)` is *not* continuous at `μ = -1` (Lean's totalised division gives
`lamfun (-1) = 0`, while `μ + lamfun μ + μ·lamfun μ = -μ` for `μ ≠ -1` and `= -1` for
`μ = -1`: the coefficient of `D_z w` in `Nstar` jumps by `2` there).  Hence the separate
hypothesis `hlam` — see the module docstring of `Submission/Work/FTS/StrongEps/epsWP_tendsto.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsWPLim.Basic
import Submission.Work.FTS.StrongEps.N0_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsWPLim

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The pointwise limit of `gRHS`.**  All the convergences required by the four blocks of
`gRHS`, with the two modulation constants converging separately. -/
theorem gRHS_tendsto {α : ℝ} {μ : ℕ → ℝ} {μl : ℝ} {lam : ℕ → ℝ} {laml : ℝ}
    {F : ℕ → Fn} {Fl : Fn} {Ψ : ℕ → Fn} {Ψl : Fn} {w : ℕ → Fn} {wl : Fn} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hμ : Tendsto μ Filter.atTop (nhds μl))
    (hlam : Tendsto lam Filter.atTop (nhds laml))
    (hF : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (F n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Fl z θ)))
    (hw : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (w n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i wl z θ)))
    (hTil : ∀ j i : ℕ, j + i ≤ 1 →
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (F n) (Ψ n)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.PhiTil α Fl Ψl) z θ)))
    (hFK : Tendsto (fun n : ℕ => Work.Construction.FK (F n) z) Filter.atTop
      (nhds (Work.Construction.FK Fl z)))
    (hlw : ∀ z' ∈ Work.Spaces.Iz, Tendsto (fun n : ℕ => Work.Construction.L12 (w n) z')
      Filter.atTop (nhds (Work.Construction.L12 wl z')))
    (hmubar : Tendsto (fun n : ℕ => Work.Construction.mubar
      (Work.Construction.N0 α (F n) (w n)) (Work.Construction.N α (F n) (Ψ n))) Filter.atTop
      (nhds (Work.Construction.mubar (Work.Construction.N0 α Fl wl)
        (Work.Construction.N α Fl Ψl)))) :
    Tendsto (fun n : ℕ => Work.Construction.gRHS α (μ n) (lam n) (F n) (Ψ n) (w n) z θ)
      Filter.atTop (nhds (Work.Construction.gRHS α μl laml Fl Ψl wl z θ)) := by
  -- the three `μ`-free blocks
  have hN0 := Work.FTS.StrongEps.N0_tendsto (α := α) (F := F) (Flim := Fl) (w := w)
    (wlim := wl) (z := z) (θ := θ) (le_of_lt hz) hF hw hlw
  have hN := N_tendsto_of_PhiTil (α := α) (F := F) (Fl := Fl) (Ψ := Ψ) (Ψl := Ψl)
    (z := z) (θ := θ) hz hθ hF hFK hTil
  have hmb : Tendsto (fun n : ℕ => -(Work.Construction.mubar
      (Work.Construction.N0 α (F n) (w n)) (Work.Construction.N α (F n) (Ψ n)))
        * Work.Construction.AK α z θ) Filter.atTop
      (nhds (-(Work.Construction.mubar (Work.Construction.N0 α Fl wl)
        (Work.Construction.N α Fl Ψl)) * Work.Construction.AK α z θ)) :=
    (hmubar.neg.mul tendsto_const_nhds)
  -- the `Nstar` block
  have hw0 : Tendsto (fun n : ℕ => w n z θ) Filter.atTop (nhds (wl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]
      using hw 0 0 (by norm_num)
  have hDz : Tendsto (fun n : ℕ => Work.Spaces.Dz (w n) z θ) Filter.atTop
      (nhds (Work.Spaces.Dz wl z θ)) := by
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero] using hw 1 0 (by norm_num)
  have hcoef : Tendsto (fun n : ℕ => μ n + lam n + μ n * lam n) Filter.atTop
      (nhds (μl + laml + μl * laml)) :=
    (hμ.add hlam).add (hμ.mul hlam)
  have hNs : Tendsto (fun n : ℕ => Work.Construction.Nstar (μ n) (lam n) (w n) z θ) Filter.atTop
      (nhds (Work.Construction.Nstar μl laml wl z θ)) := by
    have h : (fun n : ℕ => Work.Construction.Nstar (μ n) (lam n) (w n) z θ)
        = fun n : ℕ => -(μ n) * w n z θ
            - (μ n + lam n + μ n * lam n) * Work.Spaces.Dz (w n) z θ := by
      funext n
      simp only [Work.Construction.Nstar]
    rw [h]
    exact (hμ.neg.mul hw0).sub (hcoef.mul hDz)
  -- assemble
  have hfun : (fun n : ℕ => Work.Construction.gRHS α (μ n) (lam n) (F n) (Ψ n) (w n) z θ)
      = fun n : ℕ => -(Work.Construction.mubar (Work.Construction.N0 α (F n) (w n))
            (Work.Construction.N α (F n) (Ψ n))) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (F n) (w n) z θ
          + Work.Construction.N α (F n) (Ψ n) z θ
          + Work.Construction.Nstar (μ n) (lam n) (w n) z θ := by
    funext n
    simp only [Work.Construction.gRHS]
  have hlim : Work.Construction.gRHS α μl laml Fl Ψl wl z θ
      = -(Work.Construction.mubar (Work.Construction.N0 α Fl wl)
            (Work.Construction.N α Fl Ψl)) * Work.Construction.AK α z θ
          + Work.Construction.N0 α Fl wl z θ
          + Work.Construction.N α Fl Ψl z θ
          + Work.Construction.Nstar μl laml wl z θ := by
    simp only [Work.Construction.gRHS]
  rw [hfun, hlim]
  exact ((hmb.add hN0).add hN).add hNs

end Work.FTS.StrongEps.EpsWPLim
