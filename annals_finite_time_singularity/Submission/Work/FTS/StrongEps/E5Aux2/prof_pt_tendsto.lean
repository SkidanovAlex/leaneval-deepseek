import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.StrongEps.E5Aux2.PT.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.PT.Slots
import Submission.Work.FTS.StrongEps.E5Aux2.PT.L12limDiff
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem prof_pt_tendsto {α B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : Work.FTS.StrongEps.EllLimOK α E)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s) (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hXn6 : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ B)
    (hslot : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → ∀ j i : ℕ, j + i ≤ 4 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) z θ)))
    (hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0)
    (hsmW : ∀ n : ℕ, ContDiffOn ℝ 1 (Function.uncurry
      (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))) Work.FTS.EllipticEst.Q0)
    (hsmE : ContDiffOn ℝ 1 (Function.uncurry (E (Work.FTS.Galerkin.slice g s))) Work.FTS.EllipticEst.Q0)
    (hL12F : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
      Filter.atTop (nhds (Work.Construction.L12 (Work.Construction.Ftau α g s) z)))
    (hL12w : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
      Filter.atTop (nhds (Work.Construction.L12 (Work.FTS.Galerkin.slice g s) z)))
    (hdrvL12 : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => deriv (fun z' => Work.Construction.L12
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z)
      Filter.atTop (nhds (deriv (fun z' => Work.Construction.L12
        (Work.Construction.Ftau α g s) z') z)))
    (hFK : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => Work.Construction.FK
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
      Filter.atTop (nhds (Work.Construction.FK (Work.Construction.Ftau α g s) z))) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → Filter.Tendsto
      (fun n : ℕ => Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
      Filter.atTop (nhds (Work.Construction.N0 α (Work.Construction.Ftau α g s)
        (Work.FTS.Galerkin.slice g s) z θ))) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → Filter.Tendsto
      (fun n : ℕ => Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ)
      Filter.atTop (nhds (Work.Construction.N α (Work.Construction.Ftau α g s)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ))) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → Filter.Tendsto
      (fun n : ℕ => Work.Coercivity.Transport
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
      Filter.atTop (nhds (Work.Coercivity.Transport (Work.FTS.Galerkin.slice g s) z θ))) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- (1) the elliptic closure of the limiting problem at the two families
  have hEllW := hEll
    (fun n : ℕ => Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
    (Work.FTS.Galerkin.slice g s) B hC hXn6 hconv.contDiffOn
    (fun j i hji z θ hzθ => hslot z θ hzθ j i hji)
  -- (2) the limit slice and the `Φ`-profiles are `C¹` on the open quadrant
  have hWD : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS.Galerkin.slice g s))
      Work.FTS.EllipticEst.Q0 := hconv.contDiffOn.of_le (by norm_num)
  have hΨn : ∀ n : ℕ, ContDiffOn ℝ 1 (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    exact hsmΦ.add (hsmW n)
  have hΨlim : ContDiffOn ℝ 1 (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.Nonlin.PsiCan Φs E g) s)) Work.FTS.EllipticEst.Q0 := by
    exact hsmΦ.add hsmE
  -- (3) the slot convergence of the `Φ`-profiles (order `≤ 1`)
  have hΨslot : ∀ (j i : ℕ), j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.FTS.Galerkin.slice
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ)) := by
    intro j i hji z θ hzθ
    have hseq : ∀ n : ℕ, Work.Spaces.mixed j i (Work.FTS.Galerkin.slice
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ
        = Work.Spaces.mixed j i Φs z θ + Work.Spaces.mixed j i
            (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) z θ := by
      intro n
      rw [show (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)
          = (fun z' θ' => Φs z' θ' + E (Work.FTS.Galerkin.slice
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z' θ') from rfl]
      exact PT.mixed_add_one hsmΦ (hsmW n) hji hzθ
    have hlim : Work.Spaces.mixed j i (Work.FTS.Galerkin.slice
        (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ
        = Work.Spaces.mixed j i Φs z θ
          + Work.Spaces.mixed j i (E (Work.FTS.Galerkin.slice g s)) z θ := by
      rw [show (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s)
          = (fun z' θ' => Φs z' θ' + E (Work.FTS.Galerkin.slice g s) z' θ') from rfl]
      exact PT.mixed_add_one hsmΦ hsmE hji hzθ
    have hc := hEllW.2 j i (by omega) z θ hzθ
    have hconst : Filter.Tendsto (fun _ : ℕ => Work.Spaces.mixed j i Φs z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i Φs z θ)) := tendsto_const_nhds
    have := hconst.add hc
    simpa only [hseq, hlim] using this
  -- (4) the slot convergence of the full profiles `F_* + slice`
  have hFslot : ∀ (j i : ℕ), j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)
        Filter.atTop (nhds (Work.Spaces.mixed j i
          (Work.Construction.Ftau α g s) z θ)) := by
    intro j i hji z θ hzθ
    have hseq : ∀ n : ℕ, Work.Spaces.mixed j i
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ
        = Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
          + Work.Spaces.mixed j i (Work.FTS.Galerkin.slice
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ := by
      intro n
      rw [show (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          = (fun z' θ' => Work.Construction.Fstar α z' θ'
              + Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s z' θ')
          from rfl]
      exact PT.mixed_Fstar_add ((hC n).reg.forall 1) hji hzθ
    have hlim : Work.Spaces.mixed j i (Work.Construction.Ftau α g s) z θ
        = Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
          + Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) z θ := by
      rw [show (Work.Construction.Ftau α g s)
          = (fun z' θ' => Work.Construction.Fstar α z' θ'
              + Work.FTS.Galerkin.slice g s z' θ') from rfl]
      exact PT.mixed_Fstar_add hWD hji hzθ
    have hc : Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g s) z θ)) :=
      hslot z θ hzθ j i (by omega)
    have hconst : Filter.Tendsto (fun _ : ℕ =>
        Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ)) := tendsto_const_nhds
    have := hconst.add hc
    simpa only [hseq, hlim] using this
  refine ⟨?_, ?_, ?_⟩
  · -- **the `N₀`-block**
    intro z θ hzθ
    refine PT.N0_tendsto_Ioi hzθ.1 (fun j i hji => hFslot j i hji z θ hzθ)
      (fun j i hji => hslot z θ hzθ j i (by omega)) ?_
    exact hL12w z hzθ.1
  · -- **the `N`-block**: the `Φ̃`-slots of the approximants and of the limit
    intro z θ hzθ
    have hz : 0 < z := hzθ.1
    have hθ : θ ∈ Set.Ioo 0 (π / 2) := hzθ.2
    have hsin : Real.sin (2 * θ) ≠ 0 := by
      refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
      · linarith [hθ.1]
      · linarith [hθ.2]
    -- the differentiability of `L₁₂` of the *limit* profile (the crux)
    have hLdiff : DifferentiableAt ℝ (fun z' => Work.Construction.L12
        (Work.Construction.Ftau α g s) z') z :=
      (PT.L12_add_lim_hasDerivAt hα hC hXn6
        (fun z θ hzθ => hslot z θ hzθ 0 0 (by norm_num)) hL12F hz).differentiableAt
    -- the differentiability of `L₁₂` of the approximants
    have hLdiffn : ∀ n : ℕ, DifferentiableAt ℝ (fun z' => Work.Construction.L12
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z := by
      intro n
      have hmem : Work.Spaces.HkMem α 4
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) :=
        Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) (hC n).reg (hC n).mem
      exact (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα0 hα1 (hC n).reg hmem).2.2 z hz
    -- the `z`- and `θ`-slots of the `Φ`-profiles
    have hpz_slot : ∀ g' : ℝ → ℝ → ℝ, Work.Spaces.pz g' z θ
        = Work.Spaces.mixed 1 0 g' z θ / z := by
      intro g'
      rw [PT.mixed_one_zero, Work.Spaces.Dz, Work.Spaces.pz]
      field_simp
    have hpth_slot : ∀ g' : ℝ → ℝ → ℝ, Work.Spaces.pth g' z θ
        = Work.Spaces.mixed 0 1 g' z θ / Real.sin (2 * θ) := by
      intro g'
      rw [PT.mixed_zero_one, Work.Spaces.Dth]
      field_simp
    -- **`pz`**
    have hpz : Filter.Tendsto (fun n : ℕ => Work.Spaces.pz (Work.Construction.PhiTil α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ) Filter.atTop
      (nhds (Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) z θ)) := by
      have hlimval := PT.pz_PhiTil_eq_of_contDiffOn_one (α := α)
        (F := Work.Construction.Ftau α g s)
        (Ψ := Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s) hΨlim hLdiff hzθ
      rw [hlimval]
      have hseq : ∀ n : ℕ, Work.Spaces.pz (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ
          = Work.Spaces.pz (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ
            - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (fun z' => Work.Construction.L12
                (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z :=
        fun n => PT.pz_PhiTil_eq_of_contDiffOn_one (hΨn n) (hLdiffn n) hzθ
      have h1 : Filter.Tendsto (fun n : ℕ => Work.Spaces.pz (Work.FTS.Galerkin.slice
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ)
          Filter.atTop (nhds (Work.Spaces.pz (Work.FTS.Galerkin.slice
            (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ)) := by
        have h := hΨslot 1 0 (by norm_num) z θ hzθ
        have h' := h.div_const z
        simpa only [hpz_slot] using h'
      have h2 : Filter.Tendsto (fun n : ℕ => deriv (fun z' => Work.Construction.L12
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') z) Filter.atTop
          (nhds (deriv (fun z' => Work.Construction.L12
            (Work.Construction.Ftau α g s) z') z)) := hdrvL12 z hz
      have hcomb := h1.sub (h2.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
      simpa only [hseq] using hcomb
    -- **`pth`**
    have hpth : Filter.Tendsto (fun n : ℕ => Work.Spaces.pth (Work.Construction.PhiTil α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ) Filter.atTop
      (nhds (Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) z θ)) := by
      have hlimval := PT.pth_PhiTil_eq_of_contDiffOn_one (α := α)
        (F := Work.Construction.Ftau α g s)
        (Ψ := Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) s) hΨlim hzθ
      rw [hlimval]
      have hseq : ∀ n : ℕ, Work.Spaces.pth (Work.Construction.PhiTil α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ
          = Work.Spaces.pth (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ
            - (1 / (4 * α)) * Work.Construction.L12
                (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z
              * (2 * Real.cos (2 * θ)) :=
        fun n => PT.pth_PhiTil_eq_of_contDiffOn_one (hΨn n) hzθ
      have h1 : Filter.Tendsto (fun n : ℕ => Work.Spaces.pth (Work.FTS.Galerkin.slice
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ)
          Filter.atTop (nhds (Work.Spaces.pth (Work.FTS.Galerkin.slice
            (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ)) := by
        have h := hΨslot 0 1 (by norm_num) z θ hzθ
        have h' := h.div_const (Real.sin (2 * θ))
        simpa only [hpth_slot] using h'
      have h2 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z) Filter.atTop
          (nhds (Work.Construction.L12 (Work.Construction.Ftau α g s) z)) := hL12F z hz
      have hcomb := h1.sub ((h2.const_mul (1 / (4 * α))).mul_const (2 * Real.cos (2 * θ)))
      simpa only [hseq] using hcomb
    exact Work.FTS.StrongEps.N_tendsto_of_pz_pth hz hθ
      (fun j i hji => hFslot j i hji z θ hzθ)
      (fun j i hji => hΨslot j i hji z θ hzθ)
      (hL12F z hz) (hdrvL12 z hz) (hFK z hz) hpz hpth
  · -- **the transport block**
    intro z θ hzθ
    exact PT.Transport_tendsto (hslot z θ hzθ 0 1 (by norm_num))

end Work.FTS.StrongEps.E5Aux2
