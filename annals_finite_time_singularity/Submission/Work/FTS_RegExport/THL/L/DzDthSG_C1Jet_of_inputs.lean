import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E5Aux2.FK_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.l12Transport_JfamP_tendsto
import Submission.Work.FTS.StrongEps.EpsE4Thr.ZeroOrder
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.N6Trans.IP4T3Honest
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.FatouG
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.weighted_system
import Submission.Work.FTS_RegExport.RXVP3.cont_open
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.Inputs.ftau_cont
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.near0Core
import Submission.Work.Spaces.one_le_mul_w
-- ===== merged: Submission.Work.FTS.StrongEps.E5Aux2.epsWP_tendsto_of_muH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The additivity of the mixed slots over `F_* + w` at order `≤ 1`

`Ftau α g s = F_* + slice g s`, and the limit slice `slice g s` is only known to be `C⁴` on the
open quadrant, so `EpsWPLim.mixed_Fstar_add` (which asks for `SmoothOpen`) does not apply to it.
At order `≤ 1` all that is needed is the differentiability of the two slices at `(z,θ) ∈ Q0`. -/
theorem mixed_Fstar_add_one {α : ℝ} {w : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hw : ContDiffOn ℝ 1 (Function.uncurry w) Work.FTS.EllipticEst.Q0) :
    ∀ j i : ℕ, j + i ≤ 1 →
      Work.Spaces.mixed j i (fun z θ => Work.Construction.Fstar α z θ + w z θ) z θ
        = Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ
          + Work.Spaces.mixed j i w z θ := by
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  have hsmF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongEps.EpsWPLim.smoothOpen_Fstar α
  have hdFz : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
    Work.FTS.GalBasis.differentiableAt_slice_z_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      (n := 1) le_rfl (hsmF.forall 1) hzθ
  have hdFθ : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
    Work.FTS.GalBasis.differentiableAt_slice_th_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      (n := 1) le_rfl (hsmF.forall 1) hzθ
  have hdwz : DifferentiableAt ℝ (fun z' => w z' θ) z :=
    Work.FTS.GalBasis.differentiableAt_slice_z_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      (n := 1) le_rfl hw hzθ
  have hdwθ : DifferentiableAt ℝ (fun θ' => w z θ') θ :=
    Work.FTS.GalBasis.differentiableAt_slice_th_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0
      (n := 1) le_rfl hw hzθ
  intro j i hji
  have key : (j = 0 ∧ i = 0) ∨ (j = 1 ∧ i = 0) ∨ (j = 0 ∧ i = 1) := by omega
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
    rw [show deriv (fun z' => Work.Construction.Fstar α z' θ + w z' θ) z
        = deriv (fun z' => Work.Construction.Fstar α z' θ) z
          + deriv (fun z' => w z' θ) z from deriv_add hdFz hdwz]
    ring
  · simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero, Work.Spaces.Dth, Work.Spaces.pth]
    rw [show deriv (fun θ' => Work.Construction.Fstar α z θ' + w z θ') θ
        = deriv (fun θ' => Work.Construction.Fstar α z θ') θ
          + deriv (fun θ' => w z θ') θ from deriv_add hdFθ hdwθ]
    ring

theorem epsWP_tendsto_of_muH {α C₀ B Ce : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam} {s : ℝ} {Maj : ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hα : α ∈ Set.Ioc 0 1)
    (hEll : Work.FTS.StrongEps.EllLimOK α E)
    (hEllPkg : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hsmΦ : ContDiffOn ℝ 1 (Function.uncurry Φs) Work.FTS.EllipticEst.Q0)
    (hsmE : ContDiffOn ℝ 1 (Function.uncurry (E (Work.FTS.Galerkin.slice g s)))
      Work.FTS.EllipticEst.Q0)
    (hε : ∀ n : ℕ, ε n ∈ Set.Ioc 0 1) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hsm : ∀ n : ℕ, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) s)) Work.FTS.StrongEps.Quad)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G n) s)
      (Work.FTS.Galerkin.slice g s))
    (hC : ∀ n : ℕ, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
    (hXn : ∀ n : ℕ, Work.FTS.Nonlin.Xn α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ C₀ * α ^ 2)
    (hXn6 : ∀ n : ℕ, Work.FTS.StrongGlobal.Xn6 α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) ≤ B)
    (hMajint : MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0))
    (hDec : ∀ n : ℕ, Work.FTS.StrongEps.EpsDecay α ρ Φs E (ε n) s (G n) Maj)
    (hl12 : Filter.Tendsto (fun n : ℕ => Work.Construction.L12
      (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.FTS.Galerkin.slice (G n) s)) 0)
      Filter.atTop (nhds 0))
    (hmu : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    (hlam : Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) Filter.atTop
      (nhds (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)))
    {p : ℝ × ℝ} (hp : p ∈ Work.FTS.EllipticEst.Q0) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s p.1 p.2)
      Filter.atTop (nhds (Work.FTS.StrongEps.rhsFun α Φs E g s p.1 p.2)) := by
  obtain ⟨hz, hθ0, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hPQd : (p.1, p.2) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ2⟩
  have hεpos : ∀ n : ℕ, 0 < ε n := fun n => (hε n).1
  -- **the uniform convergence of the mollified family**
  have hJ : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ (j i : ℕ), j + i ≤ 4 →
        TendstoUniformlyOn
          (fun n : ℕ => fun q : ℝ × ℝ => Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ (ε n) (slice (G n) s)) q.1 q.2)
          (fun q : ℝ × ℝ => Work.Spaces.mixed j i (slice g s) q.1 q.2) Filter.atTop K :=
    fun K hK hKQ j i hji =>
      Work.FTS.StrongEps.E5Aux.mixed_Jeps_tendstoUniformlyOn hρ.moll hsm hconv hεpos hε0
        hK hKQ hji
  -- **the convergence package of the projected family**
  have hconvP : Work.FTS.StrongEps.ConvLocUnifH6 α B
      (fun n => slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (slice g s) :=
    Work.FTS.StrongEps.ConvLocUnifH6_JfamP (τ := s) hρ hsm hconv hεpos hJ hl12
  -- **the slot convergence of the projected slices**
  have hslot : ∀ (j i : ℕ), j + i ≤ 4 → Filter.Tendsto
      (fun n => Work.Spaces.mixed j i
        (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2) Filter.atTop
      (nhds (Work.Spaces.mixed j i (slice g s) p.1 p.2)) := fun j i hji =>
    Work.FTS.StrongEps.mixed_JfamP_tendsto hρ hsm hconv hεpos hε0 hl12 hPQd hji
  -- **the `L₁₂`-jet of the `Ftau`-profiles**
  obtain ⟨hL12v, hL12d⟩ :=
    L12_Ftau_marginal (Φs := Φs) (E := E) hρ hα hε hε0 hsm hconv hC hMajint hDec hl12
  -- **the `PhiTil`-slots**
  have hTil : ∀ j i : ℕ, j + i ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E
              (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.PhiTil α (Work.Construction.Ftau α g s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)) z θ)) :=
    Work.FTS.StrongEps.E5Aux2.PhiTilSlots.phiTilFtau_slots_tendsto (α := α) (B := B) (Ce := Ce)
      (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε) (G := G) (s := s) (Maj := Maj)
      hρ hα hEll hEllPkg hsmΦ hsmE hε hε0 hsm hconv hC hXn6 hMajint hDec hl12 hL12v hL12d
  -- **the angular moment**
  have hFK : Filter.Tendsto (fun n => Work.Construction.FK
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1) Filter.atTop
      (nhds (Work.Construction.FK (Work.Construction.Ftau α g s) p.1)) :=
    FK_JfamP_tendsto (α := α) (B := B) (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε) (G := G)
      (s := s) (Maj := Maj) hρ hα hε hε0 hsm hconv hC hMajint hDec hl12 p.1 hz
  -- **the `L₁₂`-convergence of the raw slices**
  have hlw : ∀ z' ∈ Work.Spaces.Iz, Filter.Tendsto (fun n => Work.Construction.L12
      (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z') Filter.atTop
      (nhds (Work.Construction.L12 (slice g s) z')) := fun z' hz' =>
    l12Slice_JfamP_tendsto (α := α) (B := B) (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε)
      (G := G) (s := s) (Maj := Maj) hρ hα hε hε0 hsm hconv hC hMajint hDec hl12 z' hz'
  have hL12T : Filter.Tendsto (fun n => Work.Coercivity.L12f (Work.Coercivity.Transport
      (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0) Filter.atTop
      (nhds (Work.Coercivity.L12f (Work.Coercivity.Transport (slice g s)) 0)) :=
    l12Transport_JfamP_tendsto (α := α) (B := B) (ρ := ρ) (Φs := Φs) (E := E) (g := g)
      (ε := ε) (G := G) (s := s) (Maj := Maj) hρ hα hε hε0 hsm hconv hC hMajint hDec hl12
  -- **the `mubar`-convergence**
  have hmubar : Filter.Tendsto (fun n : ℕ => Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))
        (Work.Construction.N α (Work.Construction.Ftau α
          (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))) Filter.atTop
      (nhds (Work.Construction.mubar
        (Work.Construction.N0 α (Work.Construction.Ftau α g s) (slice g s))
        (Work.Construction.N α (Work.Construction.Ftau α g s)
          (slice (Work.FTS.Nonlin.PsiCan Φs E g) s)))) :=
    Work.FTS.StrongEps.E5Aux2.MubarJfamP.mubar_JfamP_tendsto (α := α) (ρ := ρ) (Φs := Φs)
      (E := E) (g := g) (ε := ε) (G := G) (s := s) hα hmu hL12T
  -- **the slot convergence of the full profiles `F_* + w`**
  have hF : ∀ (j i : ℕ), j + i ≤ 1 → Filter.Tendsto
      (fun n => Work.Spaces.mixed j i
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2)
      Filter.atTop
      (nhds (Work.Spaces.mixed j i (Work.Construction.Ftau α g s) p.1 p.2)) := by
    intro j i hji
    have hcongr : (fun n => Work.Spaces.mixed j i
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2)
        = fun n => Work.Spaces.mixed j i (Work.Construction.Fstar α) p.1 p.2
            + Work.Spaces.mixed j i
                (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2 := by
      funext n
      exact Work.FTS.StrongEps.EpsWPLim.mixed_Fstar_add hz ⟨hθ0, hθ2⟩ (hC n).reg j i
    have hlimF : Work.Spaces.mixed j i (Work.Construction.Ftau α g s) p.1 p.2
        = Work.Spaces.mixed j i (Work.Construction.Fstar α) p.1 p.2
            + Work.Spaces.mixed j i (slice g s) p.1 p.2 :=
      mixed_Fstar_add_one (α := α) hz ⟨hθ0, hθ2⟩ (hconvP.contDiffOn.of_le (by norm_num)) j i hji
    rw [hcongr, hlimF]
    exact tendsto_const_nhds.add (hslot j i (by omega))
  -- **the `gRHS` block**
  have hgRHS := Work.FTS.StrongEps.EpsWPLim.gRHS_tendsto (α := α)
    (μ := fun n : ℕ => Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
    (μl := Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
    (lam := fun n : ℕ => Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
    (laml := Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
    (F := fun n : ℕ => Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
    (Fl := Work.Construction.Ftau α g s)
    (Ψ := fun n : ℕ => slice (Work.FTS.Nonlin.PsiCan Φs E
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)
    (Ψl := slice (Work.FTS.Nonlin.PsiCan Φs E g) s)
    (w := fun n : ℕ => slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (wl := slice g s)
    hz ⟨hθ0, hθ2⟩ hmu hlam hF (fun j i hji => hslot j i (by omega))
    (fun j i hji => hTil j i hji p.1 p.2 hPQd) hFK hlw hmubar
  -- **the linear block**
  have hlin : Filter.Tendsto (fun n : ℕ => Work.FTS.StrongPersist.linPart α
      (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2) Filter.atTop
      (nhds (Work.FTS.StrongPersist.linPart α (slice g s) p.1 p.2)) :=
    Work.FTS.StrongEps.E5Aux2.LinPartJfamP.linPart_JfamP_tendsto (α := α) (B := B) (ρ := ρ)
      (Φs := Φs) (E := E) (g := g) (ε := ε) (G := G) (s := s) (Maj := Maj)
      hρ hα hε hε0 hsm hconv hC hMajint hDec hl12 p hp
  -- **the two sides, unfolded**
  have hterm : (fun n : ℕ => Work.FTS.StrongEps.epsWP α ρ (ε n) Φs E (G n) s p.1 p.2)
      = fun n : ℕ => Work.FTS.StrongPersist.linPart α
            (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
                (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
              (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)
              (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1 p.2 := by
    funext n
    simp only [Work.FTS.StrongEps.epsWP, Work.FTS.Galerkin.dynRHS]
    rw [congrFun (congrFun (Work.FTS.StrongPersist.dynLin_eq_linPart α
      (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) p.1) p.2]
  have hlim : Work.FTS.StrongEps.rhsFun α Φs E g s p.1 p.2
      = Work.FTS.StrongPersist.linPart α (slice g s) p.1 p.2
          + Work.Construction.gRHS α
              (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
              (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)
              (Work.Construction.Ftau α g s)
              (slice (Work.FTS.Nonlin.PsiCan Φs E g) s) (slice g s) p.1 p.2 := by
    simp only [Work.FTS.StrongEps.rhsFun, Work.FTS.Galerkin.dynRHS]
    rw [congrFun (congrFun (Work.FTS.StrongPersist.dynLin_eq_linPart α g s) p.1) p.2]
  rw [hterm, hlim]
  exact hlin.add hgRHS

end Work.FTS.StrongEps.E5Aux2
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.ProdDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp gSlice)

set_option autoImplicit false

/-! ## §1 The angular profile and the endpoint distance -/

/-- The angular weight `Γ(θ) = (sinθ cos²θ)^α` at the **profile** exponent, i.e.
`Work.Spaces.Gam (pExp α)`.  It is `Work.FTS.Regularity.Gamma α` definitionally. -/
abbrev Gmp (α : ℝ) : ℝ → ℝ := fun θ => Work.FTS.Regularity.Gamma α θ

/-- The distance to the nearer angular endpoint. -/
def dang (θ : ℝ) : ℝ := min θ (π / 2 - θ)

theorem Gmp_eq_Gam (α θ : ℝ) : Gmp α θ = Work.Spaces.Gam (pExp α) θ :=
  Work.FTS.Regularity.Gamma_eq_Gam α θ

theorem Gmp_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Gmp α θ :=
  Work.ConstructionInstance.Gamma_nonneg hθ

theorem Gmp_le_one {α θ : ℝ} (hα : 0 ≤ α) (hθ : θ ∈ Work.Spaces.Iθ) : Gmp α θ ≤ 1 :=
  Work.ConstructionInstance.Gamma_le_one hα hθ

/-! ## §2 The modulated residual, the three coefficients and the three factors -/

/-- The modulated residual `Φ̃_τ = PhiTil (pExp α) (F_τ) (slice Φ τ)`. -/
abbrev PhiT (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ

/-- The `R`-coefficient `Rop (pExp α) Φ̃_τ`. -/
abbrev CoefR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Rop (pExp α) (PhiT α Φs E g τ) z θ

/-- The `V`-coefficient `Vop Φ̃_τ`. -/
abbrev CoefV (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Vop (PhiT α Φs E g τ) z θ

/-- The `U`-coefficient `Uop (pExp α) Φ̃_τ / sin 2θ`. -/
abbrev CoefU (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Uop (pExp α) (PhiT α Φs E g τ) z θ / Real.sin (2 * θ)

/-- The full profile `F_τ = Ftau (pExp α) (gS α (tauExt g)) τ`. -/
abbrev Fp (α : ℝ) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Ftau (pExp α)
    (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ

/-- `D_θ F_τ = sin 2θ · ∂_θF_τ`. -/
abbrev FpDth (α : ℝ) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.Dth (Fp α g τ) z θ

/-- `D_z F_τ = z ∂_zF_τ`. -/
abbrev FpDz (α : ℝ) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.Dz (Fp α g τ) z θ

/-! ## §3 The three products, in the exact shape consumed by the assembly -/

/-- The first product slot `P₁ = Rop Φ̃_τ · F_τ`. -/
abbrev P1 (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => CoefR α Φs E g τ z θ * Fp α g τ z θ

/-- The second product slot `P₂ = (Uop Φ̃_τ / sin 2θ)·D_θF_τ`. -/
abbrev P2 (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => CoefU α Φs E g τ z θ * FpDth α g τ z θ

/-- The third product slot `P₃ = Vop Φ̃_τ · D_zF_τ`. -/
abbrev P3 (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => CoefV α Φs E g τ z θ * FpDz α g τ z θ

/-! ## §4 The endpoint values of the residual and of the coefficients

`Φ̃_τ(z,·,τ)` vanishes identically at the two angular endpoints **as a function of `z`** (the
`psiR`-junk value at the endpoints is `0`, and the `Theta`-part carries `sin 2θ = 0`), hence so
does `pz Φ̃_τ` there; consequently `Uop Φ̃_τ (z,0,τ) = Uop Φ̃_τ (z,π/2,τ) = 0`.  This is what
makes the two forms of the second product slot agree on the whole closed box. -/

theorem Theta_apply_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.Theta α F z 0 = 0 := by
  simp only [Work.Construction.Theta, Work.Construction.s2]
  norm_num

theorem Theta_apply_pi_div_two (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.Theta α F z (π / 2) = 0 := by
  simp only [Work.Construction.Theta, Work.Construction.s2]
  rw [show 2 * (π / 2) = π from by ring, Real.sin_pi]
  ring

theorem psiR_apply_zero (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (z τ : ℝ) :
    Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) z 0 τ = 0 := by
  by_cases hz : 0 < z
  · rw [Work.FTS.RegExportIface.psiR, if_pos hz, Work.FTS.RegExportIface.psiQ,
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < π / 2)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (π / 2 < (0 : ℝ) ∧ (0 : ℝ) < π)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (-(π / 2) < (0 : ℝ) ∧ (0 : ℝ) < 0))]
  · rw [Work.FTS.RegExportIface.psiR, if_neg hz]
    exact Theta_apply_zero _ _ _

theorem psiR_apply_pi_div_two (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (z τ : ℝ) :
    Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) z (π / 2) τ = 0 := by
  by_cases hz : 0 < z
  · rw [Work.FTS.RegExportIface.psiR, if_pos hz, Work.FTS.RegExportIface.psiQ,
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (0 < π / 2 ∧ π / 2 < π / 2)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (π / 2 < π / 2 ∧ π / 2 < π)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (-(π / 2) < π / 2 ∧ π / 2 < 0))]
  · rw [Work.FTS.RegExportIface.psiR, if_neg hz]
    exact Theta_apply_pi_div_two _ _ _

theorem PhiT_apply_zero (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    PhiT α Φs E g τ z 0 = 0 := by
  show Work.Construction.PhiTil (pExp α)
      (Work.Construction.Ftau (pExp α) (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
      (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ) z 0 = 0
  simp only [Work.Construction.PhiTil]
  rw [show Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ z 0 = 0 from
      psiR_apply_zero α Φs E g z τ,
    Theta_apply_zero]
  ring

theorem PhiT_apply_pi_div_two (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    PhiT α Φs E g τ z (π / 2) = 0 := by
  show Work.Construction.PhiTil (pExp α)
      (Work.Construction.Ftau (pExp α) (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
      (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ) z (π / 2) = 0
  simp only [Work.Construction.PhiTil]
  rw [show Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ z (π / 2) = 0 from
      psiR_apply_pi_div_two α Φs E g z τ,
    Theta_apply_pi_div_two]
  ring

theorem pz_PhiT_zero (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    Work.Spaces.pz (PhiT α Φs E g τ) z 0 = 0 := by
  have h : (fun z' => PhiT α Φs E g τ z' 0) = fun _ => (0 : ℝ) :=
    funext fun z' => PhiT_apply_zero α Φs E g τ z'
  simp only [Work.Spaces.pz, h, deriv_const]

theorem pz_PhiT_pi_div_two (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    Work.Spaces.pz (PhiT α Φs E g τ) z (π / 2) = 0 := by
  have h : (fun z' => PhiT α Φs E g τ z' (π / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => PhiT_apply_pi_div_two α Φs E g τ z'
  simp only [Work.Spaces.pz, h, deriv_const]

/-- `Uop Φ̃_τ` vanishes at both angular endpoints. -/
theorem Uop_PhiT_endpoint {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ z θ : ℝ}
    (hθ : θ = 0 ∨ θ = π / 2) :
    Work.Construction.Uop (pExp α) (PhiT α Φs E g τ) z θ = 0 := by
  rcases hθ with rfl | rfl
  · simp [Work.Construction.Uop, PhiT_apply_zero, pz_PhiT_zero]
  · simp [Work.Construction.Uop, PhiT_apply_pi_div_two, pz_PhiT_pi_div_two]

end Work.FTS_RegExport.RXR5L
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs` — B6 of the O1 plan

The producer-level wrapper of the two `C1Jet`-regularity statements of the O1 restatement

  `DzG α g z θ τ = D_z g̃(z,θ,τ)`,   `DthG α g z θ τ = D_θ g̃(z,θ,τ)`,   `g̃ = gS α (tauExt g)`

from the *input bundle* of the construction (`Sol`, `DynOK'`, the datum `hdat` and the clock bound
`hμ`), rather than from the Γ-weighted system `WSys` directly:

* `Work.FTS_RegExport.RXT.weighted_system` produces, for every `S > 0`, a constant `K` with
  `WSys α S K g` (the six Γ-weighted slots of `RXT.idx` bounded by `K·ω`,
  `ω α z θ = z²Γ(θ)/(1+z)²`);
* then the four leaves of `THL/L` close the two `C1Jet`s:

  - **B1** `DzG_theta_mod` / **B2** `DthG_theta_mod`: the `θ`-moduli, uniform in `z ≥ 0` and in
    `τ ∈ [0,S]`;
  - **B3** `DzDthG_bound_zderiv`: the uniform value bounds, the continuity at `z = 0` and the
    `z`-derivatives with their bound;
  - **B4** `DzDthG_tau_mod`: the `τ`-moduli;
  - the `z`-moduli are produced from B3 by the engine `RXR5.zhmod_of` (Lipschitz on the open
    half-line + continuity at `0` + sup bound, interpolated into an `α`-modulus);
  - the three one-variable moduli plus the sup bound are upgraded to a joint `Jet` by
    `R3d.jet_of_bounded_holder`, and the `z`-derivative half of `C1Jet` is B3.

The constant `K` of `weighted_system` need not be nonnegative, so the leaves are applied to
`max K 0` (monotonicity in the constant, `ω ≥ 0`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

open Work.FTS_RegExport.THL (WSys DzG DthG)

set_option autoImplicit false

/-! ## Elementary helper -/

/-- Monotonicity of `Jet` in its constant. -/
private theorem jet_mono {α S N M : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Work.FTS.Regularity.Jet α S N h)
    (hNM : N ≤ M) : Work.FTS.Regularity.Jet α S M h := by
  obtain ⟨h0, hsup, hhol⟩ := H
  refine ⟨le_trans h0 hNM, fun z θ τ hz hθ hτ => le_trans (hsup z θ τ hz hθ hτ) hNM, ?_⟩
  intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
  refine le_trans (hhol z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ') ?_
  exact mul_le_mul_of_nonneg_right hNM
    (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'|) α)

/-! ## The assembly (B5), from the Γ-weighted system -/

private theorem c1jet_of_wsys {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S K : ℝ} (hS : 0 < S) (hK0 : 0 ≤ K) (hw : WSys α S K g) :
    ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂ (DzG α g) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃ (DthG α g) := by
  have hα1 : α ≤ 1 := by linarith
  have hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g := hOK.1.regPkgMin
  -- the four leaves
  obtain ⟨Lz, hLz0, hLz⟩ := DzG_theta_mod (g := g) hα hα13 hmin hS hK0 hw
  obtain ⟨Lt, hLt0, hLt⟩ := DthG_theta_mod (g := g) hα hα13 hmin hS hK0 hw
  obtain ⟨N, hN0, hB3⟩ := DzDthG_bound_zderiv (g := g) hα hα13 hmin hS hK0 hw
  obtain ⟨Lτ, hLτ0, hLτ⟩ := DzDthG_tau_mod (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS
  have h2N0 : 0 ≤ max N (2 * N) := le_trans hN0 (le_max_left _ _)
  -- the two `z`-moduli, from B3 through the engine `zhmod_of`
  have hzdz : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |DzG α g z θ τ - DzG α g z' θ τ| ≤ max N (2 * N) * |z - z'| ^ α := by
    refine Work.FTS_RegExport.RXR5.zhmod_of (h := DzG α g) hα hα1 hN0 hN0 ?_ ?_ ?_ ?_
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, -⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.1
      exact hd.differentiableAt
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.1
      rw [hd.deriv]
      exact hdb
    · intro τ hτ θ hθ
      exact (hB3 τ hτ θ hθ).2.1
    · intro τ hτ θ hθ z hz
      exact ((hB3 τ hτ θ hθ).1 z hz).1
  have hzdth : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' →
      |DthG α g z θ τ - DthG α g z' θ τ| ≤ max N (2 * N) * |z - z'| ^ α := by
    refine Work.FTS_RegExport.RXR5.zhmod_of (h := DthG α g) hα hα1 hN0 hN0 ?_ ?_ ?_ ?_
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, -⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.2
      exact hd.differentiableAt
    · intro τ hτ θ hθ x hx
      obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 x hx |>.2
      rw [hd.deriv]
      exact hdb
    · intro τ hτ θ hθ
      exact (hB3 τ hτ θ hθ).2.2.1
    · intro τ hτ θ hθ z hz
      exact ((hB3 τ hτ θ hθ).1 z hz).2
  -- the joint `Jet`s
  obtain ⟨Nz, hNz⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder (h := DzG α g)
    hα hN0 h2N0 hLz0 hLτ0
    (fun τ hτ z θ hz hθ => ((hB3 τ hτ θ hθ).1 z hz).1)
    (fun τ hτ z z' hz hz' θ hθ => hzdz τ hτ θ hθ z z' hz hz')
    hLz
    (fun τ hτ τ' hτ' z hz θ hθ => (hLτ τ hτ τ' hτ' z hz θ hθ).1)
  obtain ⟨Nt, hNt⟩ := Work.FTS.RegPkgGal.R3d.jet_of_bounded_holder (h := DthG α g)
    hα hN0 h2N0 hLt0 hLτ0
    (fun τ hτ z θ hz hθ => ((hB3 τ hτ θ hθ).1 z hz).2)
    (fun τ hτ z z' hz hz' θ hθ => hzdth τ hτ θ hθ z z' hz hz')
    hLt
    (fun τ hτ τ' hτ' z hz θ hθ => (hLτ τ hτ τ' hτ' z hz θ hθ).2)
  -- the two `C1Jet`s, with the derivative half from B3
  refine ⟨max Nz N, max Nt N, le_trans hN0 (le_max_right _ _), le_trans hN0 (le_max_right _ _),
    ?_, ?_⟩
  · refine ⟨jet_mono hNz (le_max_left _ _), ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 z hz |>.1
    exact ⟨d, hd, le_trans hdb (le_max_right _ _)⟩
  · refine ⟨jet_mono hNt (le_max_left _ _), ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := (hB3 τ hτ θ hθ).2.2.2 z hz |>.2
    exact ⟨d, hd, le_trans hdb (le_max_right _ _)⟩

/-! ## The target (B6) -/

theorem DzDthSG_C1Jet_of_inputs {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∀ S > 0, ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂ (Work.FTS_RegExport.THL.DzG α g) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃ (Work.FTS_RegExport.THL.DthG α g) := by
  intro S hS
  obtain ⟨K, hK⟩ :=
    Work.FTS_RegExport.RXT.weighted_system (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar
      hSol hOK hdat hμ S hS
  refine c1jet_of_wsys (Φs := Φs) (E := E) (g := g) hα hα13 hOK hS (le_max_right K 0) ?_
  intro k τ hτ z θ hz hθ0 hθ1
  refine le_trans (hK k τ hτ z θ hz hθ0 hθ1) ?_
  exact mul_le_mul_of_nonneg_right (le_max_left K 0)
    (Work.FTS_RegExport.RXT.omega_nonneg_of α z θ hz.le ⟨hθ0.le, hθ1.le⟩)

end Work.FTS_RegExport.THL.L
end
end
