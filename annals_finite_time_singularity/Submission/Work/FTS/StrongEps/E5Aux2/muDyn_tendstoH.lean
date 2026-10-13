import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsConv
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.E5Law
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.StrongEps.E5Aux2.MuHDens
import Submission.Work.FTS.StrongEps.E5Aux2.prof_cont
import Submission.Work.FTS.StrongEps.E5Aux2.prof_pt_tendsto
import Submission.Work.FTS.StrongEps.E5Aux2.L12_Ftau_marginal

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

theorem muDyn_tendstoH {α B C₀ C1 Ce : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
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
    (hC1 : 0 < C1)
    (hdens : ∀ n : ℕ, ∀ s' ∈ Set.Ioi (0 : ℝ),
      ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) s'‖
        ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) ∧
      ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
          (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
            (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ) s'‖
        ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) ∧
      ‖Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) s'‖
        ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2)) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
      Filter.atTop (nhds (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- **The continuity of the `Φ`-slices of the approximants.**
  have hsmPsi : ∀ n : ℕ, ContDiffOn ℝ 1 (Function.uncurry
      (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    have hEW : ContDiffOn ℝ 1 (Function.uncurry
        (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))) Work.FTS.EllipticEst.Q0 :=
      ((hEllPkg (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (hC n)).1.smooth).forall 1
    have h := hsmΦ.add hEW
    rwa [show Function.uncurry
        (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s)
      = fun p : ℝ × ℝ => Function.uncurry Φs p + Function.uncurry
          (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) p from rfl]
  -- **The continuity of the three blocks on the open quadrant** (for the `n`-th family).
  have hcont1 : ∀ n : ℕ, ContinuousOn (Function.uncurry (fun z θ => Work.Construction.N0 α
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
      (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)) Work.FTS.EllipticEst.Q0 :=
    fun n => (prof_cont hα0 hα1 (hC n) (hsmPsi n)).1
  have hcont2 : ∀ n : ℕ, ContinuousOn (Function.uncurry (fun z θ => Work.Construction.N α
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
      (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ))
      Work.FTS.EllipticEst.Q0 :=
    fun n => (prof_cont hα0 hα1 (hC n) (hsmPsi n)).2.1
  have hcont3 : ∀ n : ℕ, ContinuousOn (Function.uncurry (fun z θ => Work.Coercivity.Transport
      (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ)) Work.FTS.EllipticEst.Q0 :=
    fun n => (prof_cont hα0 hα1 (hC n) (hsmPsi n)).2.2
  -- **The pointwise convergence of the three profiles.**
  have hslot : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → ∀ j i : ℕ, j + i ≤ 4 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
        (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i (slice g s) z θ)) := by
    intro z θ hzθ j i hji
    exact Work.FTS.StrongEps.mixed_JfamP_tendsto (τ := s) hρ hsm hconv
      (fun n => (hε n).1) hε0 hl12 hzθ hji
  have hL12w : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => Work.Construction.L12
        (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
      Filter.atTop (nhds (Work.Construction.L12 (slice g s) z)) := fun z hz =>
    Work.FTS.StrongEps.E5Aux2.l12Slice_JfamP_tendsto hρ hα hε hε0 hsm hconv hC hMajint hDec hl12
      z (by simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz)
  have hFKt : ∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto
      (fun n : ℕ => Work.Construction.FK
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z)
      Filter.atTop (nhds (Work.Construction.FK (Work.Construction.Ftau α g s) z)) :=
    fun z hz => Work.FTS.StrongEps.E5Aux2.FK_JfamP_tendsto hρ hα hε hε0 hsm hconv hC hMajint
      hDec hl12 z hz
  obtain ⟨hL12Ft, hdrvL12⟩ := Work.FTS.StrongEps.E5Aux2.L12_Ftau_marginal hρ hα hε hε0 hsm
    hconv hC hMajint hDec hl12
  have hsmW : ∀ n : ℕ, ContDiffOn ℝ 1 (Function.uncurry
      (E (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s))) Work.FTS.EllipticEst.Q0 :=
    fun n => ((hEllPkg (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) (hC n)).1.smooth).forall 1
  have hprof := prof_pt_tendsto (α := α) (B := B) (ρ := ρ) (Φs := Φs) (E := E) (g := g)
    (ε := ε) (G := G) (s := s) hα hEll hconv hC hXn6 hslot hsmΦ hsmW hsmE
    hL12Ft hL12w hdrvL12 hFKt
  -- **The pointwise domination constant of the three blocks.**
  obtain ⟨Cpt, hCptpos, hCpt⟩ := N0_N_Transport_pt_le
  have hCpt0 : 0 ≤ Cpt * (1 + C₀) * (1 + B) := by
    have hC₀0 : 0 ≤ C₀ := by
      have h1 : 0 ≤ Work.FTS.Nonlin.Xn α
          (slice (Work.FTS.StrongEps.JfamP ρ (ε 0) (G 0)) s) :=
        Work.Spaces.HkNorm_nonneg α 4 _
      have h2 : 0 ≤ C₀ * α ^ 2 := le_trans h1 (hXn 0)
      by_contra hlt
      push_neg at hlt
      have h3 : 0 < α ^ 2 := pow_pos hα0 2
      have h4 : C₀ * α ^ 2 < 0 := mul_neg_of_neg_of_pos hlt h3
      linarith
    have hB0 : 0 ≤ B := by
      have h1 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α
          (slice (Work.FTS.StrongEps.JfamP ρ (ε 0) (G 0)) s) :=
        Work.Spaces.HkNorm_nonneg α 6 _
      linarith [hXn6 0]
    positivity
  have hdom1 : ∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ|
        ≤ Cpt * (1 + C₀) * (1 + B) / Real.sin (2 * θ) :=
    fun k z θ hzθ => (hCpt (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε k) (τ := s)
      (C₀ := C₀) (B := B) (g := G k) (Maj := Maj) hα (hDec k) (hC k) (hXn k) (hXn6 k)).1
      z hzθ.1 θ hzθ.2
  have hdom2 : ∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε k) (G k))) s) z θ|
        ≤ Cpt * (1 + C₀) * (1 + B) / Real.sin (2 * θ) :=
    fun k z θ hzθ => (hCpt (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε k) (τ := s)
      (C₀ := C₀) (B := B) (g := G k) (Maj := Maj) hα (hDec k) (hC k) (hXn k) (hXn6 k)).2.1
      z hzθ.1 θ hzθ.2
  have hdom3 : ∀ k : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ|
        ≤ Cpt * (1 + C₀) * (1 + B) / Real.sin (2 * θ) :=
    fun k z θ hzθ => (hCpt (α := α) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε k) (τ := s)
      (C₀ := C₀) (B := B) (g := G k) (Maj := Maj) hα (hDec k) (hC k) (hXn k) (hXn6 k)).2.2
      z hzθ.1 θ hzθ.2
  -- **A.e. strong measurability of the densities and of the angular slices.**
  have hmeas1 : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (fun s' =>
      Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ) s')
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun k => aesm_L12dens_of_contOn (hcont1 k)
  have hmeas2 : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (fun s' =>
      Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε k) (G k))) s) z θ) s')
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun k => aesm_L12dens_of_contOn (hcont2 k)
  have hmeas3 : ∀ k : ℕ, MeasureTheory.AEStronglyMeasurable (fun s' =>
      Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ) s')
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun k => aesm_L12dens_of_contOn (hcont3 k)
  have hmeasS1 : ∀ k : ℕ, ∀ s' ∈ Set.Ioi (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * (fun z θ => Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ) s' θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun k s' hs' => aesm_slice_K_of_contOn (hcont1 k) hs'
  have hmeasS2 : ∀ k : ℕ, ∀ s' ∈ Set.Ioi (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * (fun z θ => Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε k) (G k))) s) z θ) s' θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun k s' hs' => aesm_slice_K_of_contOn (hcont2 k) hs'
  have hmeasS3 : ∀ k : ℕ, ∀ s' ∈ Set.Ioi (0 : ℝ), MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * (fun z θ => Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ) s' θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun k s' hs' => aesm_slice_K_of_contOn (hcont3 k) hs'
  -- **The convergence of the densities.**
  have hconvDens1 : ∀ᵐ s' ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Filter.Tendsto (fun k : ℕ => Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ) s') Filter.atTop
      (nhds (Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
        (Work.Construction.Ftau α g s) (slice g s) z θ) s')) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s' hs' => l12dens_tendsto_of_slot
        (C := Cpt * (1 + C₀) * (1 + B)) hCpt0 hmeasS1 hdom1
        (fun z θ hzθ => (hprof.1 z θ hzθ)) s' hs')
  have hconvDens2 : ∀ᵐ s' ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Filter.Tendsto (fun k : ℕ => Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε k) (G k))) s) z θ) s')
      Filter.atTop (nhds (Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
        (Work.Construction.Ftau α g s) (slice (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ) s')) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s' hs' => l12dens_tendsto_of_slot
        (C := Cpt * (1 + C₀) * (1 + B)) hCpt0 hmeasS2 hdom2
        (fun z θ hzθ => (hprof.2.1 z θ hzθ)) s' hs')
  have hconvDens3 : ∀ᵐ s' ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      Filter.Tendsto (fun k : ℕ => Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Coercivity.Transport
        (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ) s') Filter.atTop
      (nhds (Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Coercivity.Transport
        (slice g s) z θ) s')) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s' hs' => l12dens_tendsto_of_slot
        (C := Cpt * (1 + C₀) * (1 + B)) hCpt0 hmeasS3 hdom3
        (fun z θ hzθ => (hprof.2.2 z θ hzθ)) s' hs')
  -- **The domination of the densities by the majorant of `hdens`.**
  have hbdd1 : ∀ᵐ s' ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : ℕ,
      ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N0 α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ) s'‖
      ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s' hs' k => (hdens k s' hs').1)
  have hbdd2 : ∀ᵐ s' ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : ℕ,
      ‖Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.N α
        (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ (ε k) (G k))) s) z θ) s'‖
      ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s' hs' k => (hdens k s' hs').2.1)
  have hbdd3 : ∀ᵐ s' ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), ∀ k : ℕ,
      ‖Work.FM.L12dens Work.Spaces.K (Work.Coercivity.Transport
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)) s'‖
      ≤ C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun s' hs' k => (hdens k s' hs').2.2)
  have hMint : MeasureTheory.Integrable
      (fun s' : ℝ => C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := integrable_majorant hMajint
  -- **The three `L₁₂`-convergences.**
  have hL1 := L12_tendsto_of_dominated (ρ := (0 : ℝ)) (M := fun s' : ℝ =>
      C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2))
    (f := fun k z θ => Work.Construction.N0 α
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
      (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ)
    (g := fun z θ => Work.Construction.N0 α (Work.Construction.Ftau α g s) (slice g s) z θ)
    hmeas1 hconvDens1 hbdd1 hMint
  have hL2 := L12_tendsto_of_dominated (ρ := (0 : ℝ)) (M := fun s' : ℝ =>
      C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2))
    (f := fun k z θ => Work.Construction.N α
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s)
      (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε k) (G k))) s) z θ)
    (g := fun z θ => Work.Construction.N α (Work.Construction.Ftau α g s)
      (slice (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ)
    hmeas2 hconvDens2 hbdd2 hMint
  have hL3 := L12_tendsto_of_dominated (ρ := (0 : ℝ)) (M := fun s' : ℝ =>
      C1 * (1 + C₀) * (1 + B) * (Maj s' / s' + 1 / (1 + s') ^ 2))
    (f := fun k z θ => Work.Coercivity.Transport
      (slice (Work.FTS.StrongEps.JfamP ρ (ε k) (G k)) s) z θ)
    (g := fun z θ => Work.Coercivity.Transport (slice g s) z θ)
    hmeas3 hconvDens3 hbdd3 hMint
  -- **The arithmetic of `muDyn`.**
  have hfun : (fun n : ℕ => Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)))
        (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
      = fun n : ℕ => (1 / (2 * α)) * (Work.Construction.L12 (fun z θ => Work.Construction.N0 α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s) z θ) 0
          + Work.Construction.L12 (fun z θ => Work.Construction.N α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)
            (slice (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ (ε n) (G n))) s) z θ) 0)
        + (1 / (2 * α)) * Work.Construction.L12 (Work.Coercivity.Transport
            (slice (Work.FTS.StrongEps.JfamP ρ (ε n) (G n)) s)) 0 := by
    funext n
    rfl
  have hfunl : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g s
      = (1 / (2 * α)) * (Work.Construction.L12 (fun z θ => Work.Construction.N0 α
            (Work.Construction.Ftau α g s) (slice g s) z θ) 0
          + Work.Construction.L12 (fun z θ => Work.Construction.N α
            (Work.Construction.Ftau α g s) (slice (Work.FTS.Nonlin.PsiCan Φs E g) s) z θ) 0)
        + (1 / (2 * α)) * Work.Construction.L12 (Work.Coercivity.Transport (slice g s)) 0 := by
    rfl
  rw [hfun, hfunl]
  exact (((hL1.add hL2).const_mul (1 / (2 * α))).add (hL3.const_mul (1 / (2 * α))))

end Work.FTS.StrongEps.E5Aux2
