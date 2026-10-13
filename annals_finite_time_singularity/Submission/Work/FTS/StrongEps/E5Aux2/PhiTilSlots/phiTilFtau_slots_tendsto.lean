import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E5Aux2.L12_Ftau_marginal
import Submission.Work.FTS.StrongEps.E5Aux2.l12Slice_JfamP_tendsto
import Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsConv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `phiTilFtau_slots_tendsto` — the order-`≤ 1` slots of `PhiTil α F(τ) (slice (PsiCan …) τ)`

Along the `ε`-scheme the profiles `F(τ) = F_* + slice (JfamP ρ (ε n) (G n)) s` converge to
`F = F_* + slice g s` (slot-wise, `E5Aux2.mixed_JfamP_tendsto`) and the stream functions
`slice (PsiCan Φs E (JfamP …)) s` converge to `slice (PsiCan Φs E g) s` — the `Φs`-part is
`n`-independent, and the `E`-part converges by the `EllLimOK` clause of the elliptic layer.
This module combines the two with the explicit form of `PhiTil`,

  `PhiTil α F Φ = Φ - (1/(4α)) sin(2θ) L₁₂ F`,

whose `L₁₂`-part is handled by the two marginals `L₁₂ (Ftau …) z → L₁₂ (Ftau g) z` (`hL12v`) and
`∂_z L₁₂ (Ftau …) z → ∂_z L₁₂ (Ftau g) z` (`hL12d`), together with the differentiability of
`L₁₂ (Ftau α H s) = L₁₂ (F_* + slice H s)` on `z > 0` (the `HasDerivAt` internals of
`E5Aux2.deriv_L12_Fstar_add_of_majorant`).

The statement is exactly the `hTil` hypothesis of `Work.FTS.StrongEps.epsWP_tendsto`.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2.PhiTilSlots

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Elementary calculus helpers -/

/-- `∂_θ sin (2θ) = 2 cos (2θ)`. -/
private lemma hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ (hasDerivAt_const_mul (x := θ) (2 : ℝ))
  simpa only [mul_comm] using h

/-- `mixed 0 1 = D_θ = sin(2θ) ∂_θ`. -/
private lemma mixed_0_1_eq (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 X z θ = Real.sin (2 * θ) * Work.Spaces.pth X z θ := rfl

/-- `mixed 1 0 = D_z = z ∂_z`. -/
private lemma mixed_1_0_eq (X : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 X z θ = z * Work.Spaces.pz X z θ := rfl

/-- The explicit form of `PhiTil`: `Φ - (1/(4α)) sin(2θ) L₁₂ F`. -/
private lemma PhiTil_val {α : ℝ} (F Δ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.PhiTil α F Δ z θ
      = Δ z θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z := by
  simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]

/-! ## The two partial derivatives of `PhiTil`

`PhiTil α F Δ = Δ - Θ` with `Θ z θ = (1/(4α)) sin(2θ) L₁₂ F z`, a product of a function of `θ`
and a function of `z`.  Hence `∂_θΘ = (1/(4α)) 2cos(2θ) L₁₂ F z` needs *no* differentiability of
`L₁₂ F`, while `∂_zΘ = (1/(4α)) sin(2θ) ∂_z L₁₂ F z` needs it (and `D_z = z ∂_z`). -/

/-- `∂_θ (PhiTil α F Δ) = ∂_θΔ - (1/(4α)) 2cos(2θ) L₁₂ F`. -/
private lemma pth_PhiTil_eq {α : ℝ} {F Δ : ℝ → ℝ → ℝ}
    (hΔ : ContDiffOn ℝ 1 (Function.uncurry Δ) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.pth (Work.Construction.PhiTil α F Δ) z θ
      = Work.Spaces.pth Δ z θ - (1 / (4 * α)) * (2 * Real.cos (2 * θ))
          * Work.Construction.L12 F z := by
  have hdiffΔ : DifferentiableAt ℝ (fun θ' => Δ z θ') θ :=
    Work.Spaces.differentiableAt_slice_snd
      ((hΔ.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt (by norm_num))
  have h2 : HasDerivAt (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z)
      ((1 / (4 * α)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z) θ := by
    have h0 : HasDerivAt (fun y : ℝ => ((1 / (4 * α)) * Work.Construction.L12 F z)
          * Real.sin (2 * y))
        (((1 / (4 * α)) * Work.Construction.L12 F z) * (2 * Real.cos (2 * θ))) θ :=
      (hasDerivAt_sin_two θ).const_mul ((1 / (4 * α)) * Work.Construction.L12 F z)
    have hfun : (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z)
        = fun y : ℝ => ((1 / (4 * α)) * Work.Construction.L12 F z) * Real.sin (2 * y) := by
      funext y; ring
    have hval : ((1 / (4 * α)) * Work.Construction.L12 F z) * (2 * Real.cos (2 * θ))
        = (1 / (4 * α)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by ring
    rw [hfun, ← hval]
    exact h0
  have hsub : HasDerivAt ((fun θ' => Δ z θ')
        - fun θ' => (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z)
      (deriv (fun θ' => Δ z θ') θ - (1 / (4 * α)) * (2 * Real.cos (2 * θ))
        * Work.Construction.L12 F z) θ :=
    hdiffΔ.hasDerivAt.sub h2
  have hderiv : deriv (fun θ' => Δ z θ'
        - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z) θ
      = deriv (fun θ' => Δ z θ') θ - (1 / (4 * α)) * (2 * Real.cos (2 * θ))
        * Work.Construction.L12 F z := by
    rw [show (fun θ' => Δ z θ' - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z)
        = (fun θ' => Δ z θ') - (fun θ' => (1 / (4 * α)) * Real.sin (2 * θ')
            * Work.Construction.L12 F z) from by funext θ'; rfl]
    exact hsub.deriv
  rw [Work.Spaces.pth, Work.Spaces.pth]
  have hfun : (fun θ' => Work.Construction.PhiTil α F Δ z θ')
      = fun θ' => Δ z θ' - (1 / (4 * α)) * Real.sin (2 * θ') * Work.Construction.L12 F z := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  rw [hfun]
  exact hderiv

/-- `∂_z (PhiTil α F Δ) = ∂_zΔ - (1/(4α)) sin(2θ) ∂_z L₁₂ F`. -/
private lemma pz_PhiTil_eq {α : ℝ} {F Δ : ℝ → ℝ → ℝ}
    (hΔ : ContDiffOn ℝ 1 (Function.uncurry Δ) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0)
    (hL : DifferentiableAt ℝ (fun z' => Work.Construction.L12 F z') z) :
    Work.Spaces.pz (Work.Construction.PhiTil α F Δ) z θ
      = Work.Spaces.pz Δ z θ - (1 / (4 * α)) * Real.sin (2 * θ)
          * deriv (fun z' => Work.Construction.L12 F z') z := by
  have hdiffΔ : DifferentiableAt ℝ (fun z' => Δ z' θ) z :=
    Work.Spaces.differentiableAt_slice_fst
      ((hΔ.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt (by norm_num))
  have h2 : HasDerivAt (fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z')
      ((1 / (4 * α)) * Real.sin (2 * θ) * deriv (fun z' => Work.Construction.L12 F z') z) z :=
    hL.hasDerivAt.const_mul ((1 / (4 * α)) * Real.sin (2 * θ))
  have hsub : HasDerivAt ((fun z' => Δ z' θ)
        - fun z' => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z')
      (deriv (fun z' => Δ z' θ) z - (1 / (4 * α)) * Real.sin (2 * θ)
        * deriv (fun z' => Work.Construction.L12 F z') z) z :=
    hdiffΔ.hasDerivAt.sub h2
  have hderiv : deriv (fun z' => Δ z' θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z') z
      = deriv (fun z' => Δ z' θ) z - (1 / (4 * α)) * Real.sin (2 * θ)
        * deriv (fun z' => Work.Construction.L12 F z') z := by
    rw [show (fun z' => Δ z' θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z')
        = (fun z' => Δ z' θ) - (fun z' => (1 / (4 * α)) * Real.sin (2 * θ)
            * Work.Construction.L12 F z') from by funext z'; rfl]
    exact hsub.deriv
  rw [Work.Spaces.pz, Work.Spaces.pz]
  have hfun : (fun z' => Work.Construction.PhiTil α F Δ z' θ)
      = fun z' => Δ z' θ - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 F z' := by
    funext z'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
  rw [hfun]
  exact hderiv

/-! ## Differentiability of the `L₁₂`-marginal of the full profile -/

/-- `L₁₂ (Ftau α H s) = L₁₂ (F_* + slice H s)` is differentiable at every `z > 0`, from the
pointwise `Maj`-bound on `slice H s`. -/
private lemma differentiableAt_L12_Ftau {α : ℝ} {H : Fam} {Maj : ℝ → ℝ} {s z : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) (hMaj1 : ∀ σ, Maj σ ≤ 1)
    (hh : ContinuousOn (Function.uncurry (slice H s)) Work.FTS.EllipticEst.Q0)
    (hMaj : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hbd : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |slice H s σ θ| ≤ Maj σ)
    (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Ftau α H s) z') z := by
  have hd : HasDerivAt (fun z' => Work.Construction.L12 (Work.Construction.Ftau α H s) z')
      (-(Work.FM.L12dens Work.Spaces.K
        (fun z θ => Work.Construction.Fstar α z θ + slice H s z θ) z)) z :=
    Work.FM.hasDerivAt_L12 (K := Work.Spaces.K)
      (f := fun z θ => Work.Construction.Fstar α z θ + slice H s z θ) (a := 0) (ρ := z)
      (Work.FTS.StrongEps.E5Aux2.integrableOn_L12dens_Fstar_add_of_majorant
        hα0 hα1 hh hMaj hbd)
      (Work.FTS.StrongEps.E5Aux2.continuousAt_L12dens_Fstar_add_of_majorant
        hα0 hα1 hMaj1 hh hbd hz) hz
  exact hd.differentiableAt

/-! ## The theorem -/

theorem phiTilFtau_slots_tendsto {α B Ce : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hEll : Work.FTS.StrongEps.EllLimOK α E)
    (hEllPkg : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0)
    (hsmE : ContDiffOn ℝ 1 (Function.uncurry (E (Work.FTS.Galerkin.slice g s))) Work.FTS.EllipticEst.Q0)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s) (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hXn6 : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ B)
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0) Filter.atTop (nhds 0))
    (hL12v : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun n : ℕ => Work.Construction.L12
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z) Filter.atTop
      (nhds (Work.Construction.L12 (Work.Construction.Ftau α g s) z)))
    (hL12d : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun n : ℕ => deriv (fun z' =>
        Work.Construction.L12 (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z) Filter.atTop
      (nhds (deriv (fun z' => Work.Construction.L12
        (Work.Construction.Ftau α g s) z') z))) :
    ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) z θ)) := by
  intro j i hji z θ hzθ
  -- every instance of the stream function is `Φs + E (slice … s)`
  have hslice : ∀ H : Fam, slice (Work.FTS.Nonlin.PsiCan Φs E H) s
      = fun z θ => Φs z θ + E (slice H s) z θ := fun H => rfl
  simp only [hslice]
  -- basic data at the point
  have hz : 0 < z := hzθ.1
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < Real.pi / 2 := hzθ.2.2
  have hQ0 : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ0, hθ1⟩
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hMaj1 : ∀ σ : ℝ, Maj σ ≤ 1 := fun σ => (hDec 0).2.1 σ
  -- smoothness of the slices of `G`
  have hsm' : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k
      (Function.uncurry (slice (G n) s)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n k => by simpa only [Work.FTS.StrongEps.Quad] using hsm n k
  -- the slot convergence of the projected modulation family
  have hslot : ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (slice g s) z θ)) := by
    intro j i hji z θ hzθ
    exact Work.FTS.StrongEps.mixed_JfamP_tendsto hρ hsm' hconv (fun n => (hε n).1) hε0 hl12
      (by simpa only [Work.Construction.Qd] using hzθ) hji
  -- the elliptic limit clause
  have hEll_app := hEll (fun n : ℕ => slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
    (slice g s) B (fun n => hC n) hXn6 hconv.contDiffOn hslot
  have hEslot : ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (E (slice g s)) z θ)) :=
    fun j i hji z θ hzθ => hEll_app.2 j i (by omega) z θ hzθ
  -- the pointwise `Maj`-bounds
  have hbd_n : ∀ n : ℕ, ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s σ θ| ≤ Maj σ := by
    intro n σ hσ θ hθ
    have h := (hDec n).2.2.2.1 σ hσ θ 0 0 (by norm_num)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  have hbd_f : ∀ σ ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |slice g s σ θ| ≤ Maj σ := by
    intro σ hσ θ hθ
    have hp : (σ, θ) ∈ Work.Construction.Qd := ⟨hσ, hθ⟩
    have hlim0 : Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed 0 0
        (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) σ θ) Filter.atTop
        (nhds (Work.Spaces.mixed 0 0 (slice g s) σ θ)) := hslot 0 0 (by norm_num) σ θ hp
    have h1 := le_of_tendsto_of_tendsto' hlim0.abs tendsto_const_nhds
      (fun n => by
        have h := (hDec n).2.2.2.1 σ hσ θ 0 0 (by norm_num)
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h1
  -- `C¹` on the open quadrant of the two slices `Φs + E (slice H s)`
  have hΔsm_n : ∀ n : ℕ, ContDiffOn ℝ 1 (Function.uncurry
      (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ))
      Work.FTS.EllipticEst.Q0 :=
    fun n => hsmΦ.add
      (((hEllPkg (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (hC n)).1.smooth).forall 1)
  have hΔsm_g : ContDiffOn ℝ 1 (Function.uncurry
      (fun z θ => Φs z θ + E (slice g s) z θ)) Work.FTS.EllipticEst.Q0 :=
    hsmΦ.add hsmE
  -- the elliptic solution is smooth on the open quadrant, hence its `L₁₂`-marginal is `C¹`
  have hL_n : ∀ n : ℕ, DifferentiableAt ℝ (fun z' => Work.Construction.L12
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z :=
    fun n => differentiableAt_L12_Ftau hα0 hα1 hMaj1 ((hC n).reg.continuousOn) hMajint
      (hbd_n n) hz
  have hL_g : DifferentiableAt ℝ (fun z' => Work.Construction.L12
      (Work.Construction.Ftau α g s) z') z :=
    differentiableAt_L12_Ftau hα0 hα1 hMaj1 hconv.contDiffOn.continuousOn hMajint hbd_f hz
  have hj : j = 0 ∨ j = 1 := by omega
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl
  · -- ## `(j,i) = (0,0)`: the values
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
    have hlim : Filter.Tendsto
        (fun n : ℕ => (Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
          - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12
              (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
        Filter.atTop
        (nhds ((Φs z θ + E (slice g s) z θ)
          - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12
              (Work.Construction.Ftau α g s) z)) :=
      (tendsto_const_nhds.add (hEslot 0 0 (by norm_num) z θ hzθ)).sub
        ((hL12v z hz).const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    have hfun : (fun n : ℕ => Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) z θ)
        = fun n : ℕ => (Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
          - (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12
              (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z :=
      funext fun n => PhiTil_val _ _ _ _
    rw [hfun, PhiTil_val (Work.Construction.Ftau α g s)
      (fun z θ => Φs z θ + E (slice g s) z θ) z θ]
    exact hlim
  · -- ## `(j,i) = (0,1)`: the `θ`-slot
    have h3 : ∀ n : ℕ, Work.Spaces.mixed 0 1
        (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) z θ
        = Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1
            (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ := by
      intro n
      exact Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin
        (f := Φs) (g := E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) hsmΦ
        (((hEllPkg (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (hC n)).1.smooth).forall 1)
        0 1 (by norm_num) z θ hz hθ0 hθ1
    have h3g : Work.Spaces.mixed 0 1 (fun z θ => Φs z θ + E (slice g s) z θ) z θ
        = Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1 (E (slice g s)) z θ :=
      Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin (f := Φs) (g := E (slice g s))
        hsmΦ hsmE 0 1 (by norm_num) z θ hz hθ0 hθ1
    have hlim : Filter.Tendsto
        (fun n : ℕ => (Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1
              (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ)
          - (Real.sin (2 * θ) * ((1 / (4 * α)) * (2 * Real.cos (2 * θ))))
              * Work.Construction.L12 (Work.Construction.Ftau α
                  (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
        Filter.atTop
        (nhds ((Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1 (E (slice g s)) z θ)
          - (Real.sin (2 * θ) * ((1 / (4 * α)) * (2 * Real.cos (2 * θ))))
              * Work.Construction.L12 (Work.Construction.Ftau α g s) z)) :=
      (tendsto_const_nhds.add (hEslot 0 1 (by norm_num) z θ hzθ)).sub
        ((hL12v z hz).const_mul (Real.sin (2 * θ) * ((1 / (4 * α)) * (2 * Real.cos (2 * θ)))))
    have hfun : (fun n : ℕ => Work.Spaces.mixed 0 1 (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)) z θ)
        = fun n : ℕ => (Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1
              (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ)
          - (Real.sin (2 * θ) * ((1 / (4 * α)) * (2 * Real.cos (2 * θ))))
              * Work.Construction.L12 (Work.Construction.Ftau α
                  (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z := by
      funext n
      have hpth : Real.sin (2 * θ) * Work.Spaces.pth
          (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) z θ
          = Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1
              (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ := by
        rw [← mixed_0_1_eq (fun z θ => Φs z θ
          + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) z θ]
        exact h3 n
      rw [mixed_0_1_eq, pth_PhiTil_eq (hΔ := hΔsm_n n) hQ0, mul_sub, hpth]
      ring
    have hval : Work.Spaces.mixed 0 1 (Work.Construction.PhiTil α
        (Work.Construction.Ftau α g s) (fun z θ => Φs z θ + E (slice g s) z θ)) z θ
        = (Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1 (E (slice g s)) z θ)
          - (Real.sin (2 * θ) * ((1 / (4 * α)) * (2 * Real.cos (2 * θ))))
              * Work.Construction.L12 (Work.Construction.Ftau α g s) z := by
      have hpth : Real.sin (2 * θ) * Work.Spaces.pth
          (fun z θ => Φs z θ + E (slice g s) z θ) z θ
          = Work.Spaces.mixed 0 1 Φs z θ + Work.Spaces.mixed 0 1 (E (slice g s)) z θ := by
        rw [← mixed_0_1_eq (fun z θ => Φs z θ + E (slice g s) z θ) z θ]
        exact h3g
      rw [mixed_0_1_eq, pth_PhiTil_eq (hΔ := hΔsm_g) hQ0, mul_sub, hpth]
      ring
    rw [hfun, hval]
    exact hlim
  · -- ## `(j,i) = (1,0)`: the `z`-slot
    have h3 : ∀ n : ℕ, Work.Spaces.mixed 1 0
        (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) z θ
        = Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0
            (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ := by
      intro n
      exact Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin
        (f := Φs) (g := E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) hsmΦ
        (((hEllPkg (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (hC n)).1.smooth).forall 1)
        1 0 (by norm_num) z θ hz hθ0 hθ1
    have h3g : Work.Spaces.mixed 1 0 (fun z θ => Φs z θ + E (slice g s) z θ) z θ
        = Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0 (E (slice g s)) z θ :=
      Work.FTS.EllipticEst.Cores.DiagEstEllT.mixed_add_fin (f := Φs) (g := E (slice g s))
        hsmΦ hsmE 1 0 (by norm_num) z θ hz hθ0 hθ1
    have hlim : Filter.Tendsto
        (fun n : ℕ => (Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0
              (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ)
          - (z * ((1 / (4 * α)) * Real.sin (2 * θ)))
              * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau α
                  (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z)
        Filter.atTop
        (nhds ((Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0 (E (slice g s)) z θ)
          - (z * ((1 / (4 * α)) * Real.sin (2 * θ)))
              * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau α g s) z') z)) :=
      (tendsto_const_nhds.add (hEslot 1 0 (by norm_num) z θ hzθ)).sub
        ((hL12d z hz).const_mul (z * ((1 / (4 * α)) * Real.sin (2 * θ))))
    have hfun : (fun n : ℕ => Work.Spaces.mixed 1 0 (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)) z θ)
        = fun n : ℕ => (Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0
              (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ)
          - (z * ((1 / (4 * α)) * Real.sin (2 * θ)))
              * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau α
                  (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z := by
      funext n
      have hpz : z * Work.Spaces.pz
          (fun z θ => Φs z θ + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) z θ
          = Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0
              (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ := by
        rw [← mixed_1_0_eq (fun z θ => Φs z θ
          + E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) z θ]
        exact h3 n
      rw [mixed_1_0_eq, pz_PhiTil_eq (hΔ := hΔsm_n n) hQ0 (hL_n n), mul_sub, hpz]
      ring
    have hval : Work.Spaces.mixed 1 0 (Work.Construction.PhiTil α
        (Work.Construction.Ftau α g s) (fun z θ => Φs z θ + E (slice g s) z θ)) z θ
        = (Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0 (E (slice g s)) z θ)
          - (z * ((1 / (4 * α)) * Real.sin (2 * θ)))
              * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau α g s) z') z := by
      have hpz : z * Work.Spaces.pz (fun z θ => Φs z θ + E (slice g s) z θ) z θ
          = Work.Spaces.mixed 1 0 Φs z θ + Work.Spaces.mixed 1 0 (E (slice g s)) z θ := by
        rw [← mixed_1_0_eq (fun z θ => Φs z θ + E (slice g s) z θ) z θ]
        exact h3g
      rw [mixed_1_0_eq, pz_PhiTil_eq (hΔ := hΔsm_g) hQ0 hL_g, mul_sub, hpz]
      ring
    rw [hfun, hval]
    exact hlim
  · -- ## `(j,i) = (1,1)` is excluded by `j + i ≤ 1`
    exfalso
    omega

end Work.FTS.StrongEps.E5Aux2.PhiTilSlots
