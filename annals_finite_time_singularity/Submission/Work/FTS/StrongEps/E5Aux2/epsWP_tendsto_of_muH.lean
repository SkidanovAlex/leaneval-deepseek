import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsWPLim.Main
import Submission.Work.FTS.StrongEps.EpsConv
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.E5Aux2.l12Slice_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.l12Transport_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.L12_Ftau_marginal
import Submission.Work.FTS.StrongEps.E5Aux2.FK_JfamP_tendsto
import Submission.Work.FTS.StrongEps.ConvLocUnifH6_JfamP
import Submission.Work.FTS.StrongEps.mixed_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux.mixed_Jeps_tendstoUniformlyOn
import Submission.Work.FTS.GalBasis.FamEAux.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.MubarJfamP.mubar_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.LinPartJfamP.linPart_JfamP_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.PhiTilSlots.phiTilFtau_slots_tendsto

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
