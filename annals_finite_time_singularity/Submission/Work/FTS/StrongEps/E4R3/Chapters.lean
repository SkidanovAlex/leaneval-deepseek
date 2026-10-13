import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.EpsE4RAsm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/E4R3/Chapters.lean` — the corrected E4 chapters and their assembly (PROVED)

curric-46 install 2026-10-12 (`cbc/fts_e5swap_e4chapters.md` §B, REVIEW
`cbc/fts_e5swap_e4chapters_REVIEW.md`).  `EpsDecay` was edited **in place** (`StrongEps/EpsMem.lean`:
cap `Maj ≤ 1`, the three elliptic blocks bounded by `3` on the open quadrant), so the corrected
target `EpsE4R3Stmt` of the design *is* the statement of `StrongEps.EpsE4R`, verbatim, and the
decay chapter is `EpsE4Thr.DecayChapter` itself (its `AprioriDecayB` reads the new `EpsDecay`).
Changed against `EpsE4Thr.EpsE4RAsm`:

* `LocalStepChapter3`: only `ε ∈ (0,1]`;
* `AprioriChapter3`: `M ≥ K` and `ε₂ ∈ (0,1]` chosen after `T` (at `M = K` the old chapter is
  false: `g₀ = 0`, `K = 0`, the forcing moves the solution);
* the assembly `EpsE4R3_of_chapters` takes `∃ C, ∀ C₀ ≥ C, chapter` for each chapter, and
  `C★ := max (max 2 CL) (max CP CD)`.

Everything here is `sorry`-free.  Of the three chapters, **`DecayChapter3` is proved**
(`E4R3/Decay3.lean := E4R3/Decay3_leaf.lean`, session 22); the two still open leaves are
`E4R3/LocalStep3` (needs the pinning of the elliptic image + the raw-slice traces) and
`E4R3/Apriori3` (needs the raw-slice `ℋ⁷` datum for its `ℋ⁶` half and the coercive pairing
`Nonlin.UnifIP` for its level-`4` half) — see `StrongEps/NOTES_session22.md` §3 and
`StrongEps/REQUEST_LEAD_session22.md` (3).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R3

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps

set_option autoImplicit false

/-- **Local-step chapter, corrected**: only `ε ∈ (0,1]` (every producer needs `ε ≤ 1`). -/
def LocalStepChapter3 (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ → ∀ ε ∈ Ioc (0 : ℝ) 1, LocalStepP α' ρ ε Φs E C₀

/-- **A-priori chapter, corrected**: the `ℋ⁶` bound `M ≥ K` and `ε₂ ∈ (0,1]` are chosen after `T`. -/
def AprioriChapter3 (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ →
    ∀ T : ℝ, 0 < T → ∃ M : ℝ, K ≤ M ∧ ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₂, AprioriP α' ρ ε T Φs E g₀ C₀ M

/-- **Decay chapter** (= `EpsE4Thr.DecayChapter`, now over the bounded-block `EpsDecay`). -/
def DecayChapter3 (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ α' ∈ Ioc 0 α, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    E4Data α' C₀ K Ce Cs ρ Φs E g₀ →
    ∀ T : ℝ, 0 < T → ∃ Maj : ℝ → ℝ, AprioriDecayB α' ρ T Φs E g₀ C₀ Maj

/-- Per-`α` assembly: `EpsUniformMem_of_localStep_aprioriB` with the corrected inputs. -/
theorem EpsUniformMem_of_parts3 {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn}
    (hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0)
    (hρ : IsSmoothKernel ρ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K) (h6 : Xn6 α g₀ ≤ K * α ^ 2)
    (hsmall : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioc 0 ε₁,
      Work.FTS.Nonlin.Xn α (Jeps ρ ε g₀) ≤ C₀ * α ^ 2)
    (hd : ∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀)
    (hstep : ∀ ε ∈ Ioc (0 : ℝ) 1, LocalStepP α ρ ε Φs E C₀)
    (hapr : ∀ T : ℝ, 0 < T → ∃ M : ℝ, K ≤ M ∧ ∃ ε₂ : ℝ, 0 < ε₂ ∧ ε₂ ≤ 1 ∧
      ∀ ε ∈ Ioc 0 ε₂, AprioriP α ρ ε T Φs E g₀ C₀ M)
    (hdecB : ∀ T : ℝ, 0 < T → ∃ Maj : ℝ → ℝ, AprioriDecayB α ρ T Φs E g₀ C₀ Maj) :
    EpsUniformMem α ρ Φs E g₀ C₀ K := by
  obtain ⟨ε₁, hε₁, hsmallb⟩ := hsmall
  refine ⟨hvan, l12_zero_of_epsDatum ⟨hα, hα1⟩ hρ hd, ?_⟩
  intro T hT
  obtain ⟨M, hKM, ε₂, hε₂, hε₂1, hP⟩ := hapr T hT
  obtain ⟨Maj, hMajint, hMaj⟩ := hdecB T hT
  refine ⟨M, hKM, min ε₁ ε₂, lt_min hε₁ hε₂, Maj, hMajint, ?_⟩
  intro ε hε
  have hεpos : 0 < ε := hε.1
  have hε1' : ε ≤ ε₁ := le_trans hε.2 (min_le_left _ _)
  have hε2' : ε ≤ ε₂ := le_trans hε.2 (min_le_right _ _)
  have hε1 : ε ≤ 1 := le_trans hε2' hε₂1
  have hPz : Pz (Jeps ρ ε g₀) = Jeps ρ ε g₀ :=
    Pz_self_of_l12 (Work.FTS.ClassC.ClassC.l12_zero (hd ε hεpos).2.2)
  have hsmall₀ : Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε g₀)) ≤ C₀ * α ^ 2 := by
    rw [hPz]
    exact hsmallb ε ⟨hεpos, hε1'⟩
  have hg₀M : Xn6 α g₀ ≤ M := by
    have hα2le : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
    calc Xn6 α g₀ ≤ K * α ^ 2 := h6
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hα2le hK
      _ = K := mul_one K
      _ ≤ M := hKM
  obtain ⟨g, hsol, hreg, hbnd⟩ :=
    exists_sol_of_localStep_apriori hT (le_trans hK hKM) hg₀M hsmall₀
      (EpsDatum.toDatumP (hd ε hεpos)) (hstep ε ⟨hεpos, hε1⟩) (hP ε ⟨hεpos, hε2'⟩)
  refine ⟨g, hsol, ?_⟩
  intro τ hτ
  have hdP : EpsDatumP α ρ ε (slice g τ) := hreg.2 τ hτ
  have hCmem : Work.Spaces.HkMem α 7 (slice (JfamP ρ ε g) τ) := hdP.2.2.mem
  have hCsm : Work.FTS.EllipticEst.SmoothOpen (slice (JfamP ρ ε g) τ) := hdP.2.2.reg
  have h4 : Work.Spaces.HkMem α 4 (slice (JfamP ρ ε g) τ) :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hCsm hCmem
  exact ⟨hdP.1, h4, hdP.2.1, (hbnd τ hτ).2, (hbnd τ hτ).1, by rw [slice_JfamP]; exact hdP.2.2,
    hreg.1,
    hMaj ε ⟨hεpos, hε1⟩ g hsol hreg (fun σ hσ => (hbnd σ hσ).2) τ hτ⟩

/-- **`EpsE4R` (verbatim statement) from the three corrected chapters** (PROVED). -/
theorem EpsE4R3_of_chapters {Ce Cs : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    (hL : ∃ CL : ℝ, ∀ C₀ : ℝ, CL ≤ C₀ → LocalStepChapter3 Ce Cs C₀ ρ)
    (hP : ∃ CP : ℝ, ∀ C₀ : ℝ, CP ≤ C₀ → AprioriChapter3 Ce Cs C₀ ρ)
    (hD : ∃ CD : ℝ, ∀ C₀ : ℝ, CD ≤ C₀ → DecayChapter3 Ce Cs C₀ ρ) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C₀ : ℝ, Cstar ≤ C₀ → ∃ α₄ : ℝ, 0 < α₄ ∧
    ∀ α ∈ Set.Ioc 0 α₄, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}, 0 ≤ K →
    (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs → MuLamOK α C₀ Φs E →
    (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) →
    Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 →
    Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2 →
    EpsUniformMem α ρ Φs E g₀ C₀ K := by
  obtain ⟨CL, hL⟩ := hL
  obtain ⟨CP, hP⟩ := hP
  obtain ⟨CD, hD⟩ := hD
  refine ⟨max (max 2 CL) (max CP CD),
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_trans (le_max_left 2 CL) (le_max_left _ _)), ?_⟩
  intro C₀ hC₀
  have h2 : 2 ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC₀
  have hCL : CL ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC₀
  have hCP : CP ≤ C₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC₀
  have hCD : CD ≤ C₀ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC₀
  have hC₀' : 1 < C₀ := lt_of_lt_of_le (by norm_num) h2
  obtain ⟨αL, hαL0, hαL1, hL'⟩ := hL C₀ hCL
  obtain ⟨αP, hαP0, hαP1, hP'⟩ := hP C₀ hCP
  obtain ⟨αD, hαD0, hαD1, hD'⟩ := hD C₀ hCD
  refine ⟨min (min αL αP) (min αD 1), lt_min (lt_min hαL0 hαP0) (lt_min hαD0 one_pos), ?_⟩
  intro α hα
  have hα1 : α ≤ 1 := le_trans hα.2 (le_trans (min_le_right _ _) (min_le_right _ _))
  have hαL : α ∈ Ioc 0 αL :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_left _ _))⟩
  have hαP : α ∈ Ioc 0 αP :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_left _ _) (min_le_right _ _))⟩
  have hαD : α ∈ Ioc 0 αD :=
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  intro K Φs E g₀ hK hvan hEll hstar hml hd h4 h6
  have hdata : E4Data α C₀ K Ce Cs ρ Φs E g₀ :=
    ⟨hK, hvan, hEll, hstar, hml, hd, h4, h6⟩
  exact EpsUniformMem_of_parts3 hvan hρ hα.1 hα1 hK h6
    (Jeps_smallBall_one_lt hρ hα.1 hα1 hC₀' hd h4) hd
    (fun ε hε => hL' α hαL hdata ε hε)
    (fun T hT => hP' α hαP hdata T hT)
    (fun T hT => hD' α hαD hdata T hT)

end Work.FTS.StrongEps.EpsE4Thr.E4R3
