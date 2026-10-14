import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.RawE6Aux.Main
import Submission.Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux
import Submission.Work.FTS.StrongEps.EpsRHSPBdd_unif
import Submission.Work.FTS.StrongPersist.H6Aux.Assembly
import Submission.Work.FTS.StrongPersist.H6Aux.RadialAsm
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.NsumG.nsumG1
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_LocDatum3a.Basic
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds
import Submission.Work.FTS_RegExport.RXR5L.mubarData
import Submission.Work.FTS_StreamBdry.Inputs.slice_assy

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/rawE6_ineq_proof.lean` — leaf L-A (`rawE6_ineq`)

## Verdict on the assigned statement — MIS-STATED (missing hypothesis), not provable as written

The assigned statement binds `IsEpsSolP` (the projected scheme's ODE), `EpsRegP` (per-slice
`SmoothOpen`/`HkMem α 6`, joint `C¹`) and the *ball* on the **projected mollified** slices
`Xn α (slice (JfamP ρ ε g) τ) ≤ C₀α²` — but nothing uniform in `τ` on the **raw** slice's `ℋ⁶`
size.  The design's own route for L-A (`sources/ftsV2/fts_apriori6_ruling.md` §Verdict 4) needs
`|c(J_ε g)| = |L₁₂ (J_ε g)(0)|/pzNorm ≲ ε|g|₅`, i.e. the conservation `L₁₂ (slice g τ)(0) = 0`
(leaf **F6**) plus the `ℋ⁴`-closeness of `J_ε g` to `g`; leaf F6 is itself unprovable as stated
(its prover's verdict, `Apriori4Proofs/NOTES_rawSlice_L12_zero_proof.md`): the only proved route
`E5Aux3.L12_slice_eq_zero_of_hkMem` needs a **uniform in `τ`** `ℋ⁴`-bound on `epsRHSP`, and every
producer of that bound (`EpsE4Thr.HkNorm_epsRHSP_le`, `EpsE4Thr.EpsRHSPBdd_generalRadius`,
`StrongEps.epsWP_hkMem4_bnd_unif`) needs `HkNorm α 6 (slice g s) ≤ B` uniformly — the very datum
the `ℋ⁶`-half is about to *prove* (report `REPORT_LEAD_apriori4_decisions.md`, Decision (1)).

Consequently only `|c(J_ε g)| ≤ K α² + 2Cε√e` is available, and the rank-one term
`c(J_ε g)·IP6(X, bump)` is then bounded by `Kα²·(1/ε)(1+√e)`, which no ε-free `Λ` can dominate as
`ε → 0⁺` (the factor `(1/ε)` is the ε-pricing of `|x|₇ ≤ (Cg/ε)|g|₆`).  **The repair** is to add
the uniform bound `∀ τ ∈ Icc 0 T, Xn6 α (slice g τ) ≤ B` — the same "R2" datum already prescribed
for leaf S4/S4-local and H6.  That repaired statement is `rawE6_ineq_uniform_of_leaves` below; its
estimating part is `RawE6Aux/rawE6_pair_bound` (proved, `RawE6Aux/Main.lean`), and the leaf-level
instantiation (with S1, S5 discharged) is `rawE6_ineq_uniform`.  Full mechanism and consumption
recipe: `RawE6Aux/NOTES_verdict.md`.

## The assigned statement (kept verbatim, `sorry`: see the verdict above)
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- shorthand for the route's level-six pairing. -/
abbrev IP6o := Work.FTS.StrongEps.EpsE4Thr.E4R4.IP6o

/-- shorthand for the raw level-six energy. -/
abbrev rawE6 := Work.FTS.StrongEps.EpsE4Thr.E4R4.rawE6


/-! ## Leaf L-A, repaired: the uniform-`ℋ⁶`-datum form -/

theorem rawE6_ineq_uniform_of_leaves
    (hS1 : ∀ {ρ : ℝ × ℝ → ℝ}, Work.FTS.StrongEps.IsSmoothKernel ρ →
      (∀ p : ℝ × ℝ, ρ (-p) = ρ p) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ∀ f h : Fn, Work.FTS.VocabO.HQo α 6 f → Work.FTS.VocabO.HQo α 6 h →
        |IP6o α (Work.FTS.StrongEps.Jeps ρ ε f) h - IP6o α f (Work.FTS.StrongEps.Jeps ρ ε h)|
          ≤ C * ε * Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 h)
    (hS2 : ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Ct : ℝ, 0 ≤ Ct ∧
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, Work.FTS.StrongEps.IsSmoothKernel ρ →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ),
        Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
        Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
        Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) ∧
        Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 5 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ∧
        Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 7 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
            + Ct * (1 + Work.Spaces.HkNorm α 6 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ^ 2)
    (hS5 : ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀,
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, Work.FTS.StrongEps.IsSmoothKernel ρ →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ), 0 ≤ τ →
        Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
        Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongPersist.L6Ctx (IP6o) α (C₀ * α ^ 2) Ce Cs E Φs
          (Work.FTS.StrongEps.JfamP ρ ε g)
          (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p)
    {α₂ Ce Cp : ℝ} (hpair : Work.FTS.StrongPersist.H6Pair (IP6o) α₂ Ce Cp) :
    ∀ C₀ Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Λ C₁ : ℝ, 0 ≤ Λ ∧ 0 ≤ C₁ ∧
    ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    Work.FTS.StrongEps.EpsE4Thr.E4Data α C₀ K Ce Cs ρ Φs E g₀ →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ T : ℝ, 0 < T → ∀ g : Fam,
      Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g → Work.FTS.StrongEps.EpsRegP α ρ ε T g →
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ {B : ℝ}, (∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ B) →
      ∀ τ ∈ Set.Ioo 0 T,
        2 * IP6o α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) (slice g τ)
          ≤ Λ * (1 + rawE6 α g τ) + ε * C₁ * (1 + rawE6 α g τ) ^ 2 := by
  intro C₀ Cs
  obtain ⟨Cs1, hCs1nn, hS1'⟩ := hS1 hρ hρs
  obtain ⟨CC, hCCpos, hcs⟩ :=
    Work.FTS.StrongPersist.IP6_cs_coeffs 1 1 1 1 1 1 1 1 1 1 α₂ hpair.pos.2
  obtain ⟨a2L, CL, ha2Lpos, hCLpos, hlin⟩ := Work.FTS.StrongPersist.H6Aux.H6Lin_IP6
  obtain ⟨CW, hCWpos, hCW⟩ := Work.FTS.StrongEps.HkSq_JfamP_le ρ hρ
  obtain ⟨CL2, hCL2pos, hL12sub⟩ := Work.FTS.StrongEps.L12_Jeps_sub_le ρ hρ
  obtain ⟨Bb, hBbpos, hBbb⟩ := Work.FTS.EpsEngine.exists_HkNorm_bump_le8
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  obtain ⟨Cg, hCgnn, hstep⟩ := Work.FTS.StrongEps.HkSq_Jeps_step_le ρ hρ
  obtain ⟨CLz, hCLzpos, hl12z⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨a02, ha02pos, hS2'⟩ := hS2 C₀ Ce Cs
  obtain ⟨a05, ha05pos, hS5'⟩ := hS5 C₀ Ce Cs
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  have hCWnn : 0 ≤ CW := hCWpos.le
  have hCLnn : 0 ≤ CL := hCLpos.le
  have hCL2nn : 0 ≤ CL2 := hCL2pos.le
  have hCLznn : 0 ≤ CLz := hCLzpos.le
  have hBbnn : 0 ≤ Bb := hBbpos.le
  have hCCnn : 0 ≤ CC := hCCpos.le
  have hCJnn : 0 ≤ CJ := hCJpos.le
  refine ⟨min 1 (min α₂ (min a2L (min a02 a05))), ?_, ?_⟩
  · exact lt_min one_pos (lt_min hpair.pos.2 (lt_min ha2Lpos (lt_min ha02pos ha05pos)))
  · intro α hα
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := le_trans hα.2 (min_le_left _ _)
    have hαle2 : α ≤ α₂ := le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hαleL : α ≤ a2L :=
      le_trans hα.2 (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hαle02 : α ≤ a02 := le_trans hα.2 (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
    have hαle05 : α ≤ a05 := le_trans hα.2 (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
    have hαIoc1 : α ∈ Set.Ioc 0 1 := ⟨hα0, hα1⟩
    have hαIoc2 : α ∈ Set.Ioc 0 α₂ := ⟨hα0, hαle2⟩
    obtain ⟨Ct, hCtnn, hS2''⟩ := hS2' α ⟨hα0, hαle02⟩
    set Cg' : ℝ := Real.sqrt Cg with hCg'
    have hCg'nn : 0 ≤ Cg' := by rw [hCg']; exact Real.sqrt_nonneg Cg
    set K7 : ℝ := Real.sqrt 2 * (Cg' + (CL2 / Work.FTS.StrongEps.pzNorm) * Bb) with hK7
    have hK7nn : 0 ≤ K7 := by rw [hK7]; positivity
    set A2 : ℝ := Cp * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-(10 : ℝ)) * (1 + C₀ * α ^ 2) ^ 4 with hA2def
    have hA2nn : 0 ≤ A2 := by
      rw [hA2def]
      exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hpair.pos.1) (by positivity))
        (Real.rpow_nonneg hα0.le _)) (by positivity)
    set A5 : ℝ := (CLz / Work.FTS.StrongEps.pzNorm) * Real.exp (CJ / 2) * CC * Bb * Ct
      * (1 + Real.sqrt CW) with hA5def
    have hA5nn : 0 ≤ A5 := by rw [hA5def]; positivity
    set Λ : ℝ := 2 * CL * CW + 2 * (A2 * (1 + CW))
      + 2 * (((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb + Cs1) * Ct * (1 + K7)) + 2 * A5
      with hΛ
    have hΛnn : 0 ≤ Λ := by rw [hΛ]; positivity
    set C₁ : ℝ := 2 * (((CL2 / Work.FTS.StrongEps.pzNorm) * CC * Bb + Cs1)
      * (2 * Ct * (1 + CW))) with hC₁
    have hC₁nn : 0 ≤ C₁ := by rw [hC₁]; positivity
    refine ⟨Λ, C₁, hΛnn, hC₁nn, ?_⟩
    intro K Φs E g₀ hdat hstar6 ε hε T hT g hsol hreg hball B hb6 τ hτ
    -- # unpacking
    have hτIcc : τ ∈ Set.Icc 0 T := ⟨hτ.1.le, hτ.2.le⟩
    have hEll := hdat.2.2.1
    have hML : Work.FTS.StrongEps.MuLamOK α C₀ Φs E := hdat.2.2.2.2.1
    have hd : ∀ ε' : ℝ, 0 < ε' → Work.FTS.StrongEps.EpsDatum α ρ ε' g₀ := hdat.2.2.2.2.2.1
    have hDτ : Work.FTS.StrongEps.EpsDatumP α ρ ε (slice g τ) := hreg.2 τ hτIcc
    have hCτ : Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) := hDτ.2.2
    have hballτ : Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        ≤ C₀ * α ^ 2 := hball τ hτIcc
    have hfsmo : Work.FTS.EllipticEst.SmoothOpen (slice g τ) := hDτ.1
    have hfmem6 : Work.Spaces.HkMem α 6 (slice g τ) := hDτ.2.1
    have hfQo : Work.FTS.VocabO.HQo α 6 (slice g τ) := ⟨hfsmo, hfmem6⟩
    have hfQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g τ)) Work.FTS.StrongEps.Quad :=
      fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall (slice g τ)).mp hfsmo n
    have hfloc : MeasureTheory.LocallyIntegrable (Work.FTS.StrongEps.logPull (slice g τ))
        MeasureTheory.volume :=
      Work.FTS.StrongEps.locallyIntegrable_logPull_of_forall_contDiffOn hfQuad
    -- # the leaves S5 and S2 at τ
    have hctx : Work.FTS.StrongPersist.L6Ctx (IP6o) α (C₀ * α ^ 2) Ce Cs E Φs
        (Work.FTS.StrongEps.JfamP ρ ε g)
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ :=
      hS5' α ⟨hα0, hαle05⟩ hρ hEll hstar6 hML ε hε g τ hτ.1.le hCτ hballτ
    obtain ⟨hXQo, hX4b, hX6b⟩ := hS2'' hρ hEll hstar6 hML ε hε g τ hCτ hballτ
    -- # the profiles
    set f : Fn := slice g τ with hf
    set W : Fn := slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hW
    set X : Fn := Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ with hX
    set Jf : Fn := Work.FTS.StrongEps.Jeps ρ ε f with hJf
    set JX : Fn := Work.FTS.StrongEps.Jeps ρ ε X with hJX
    set Dn : Fn := Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) τ with hDn
    set cW : ℝ := Work.Construction.L12 Jf 0 / Work.FTS.StrongEps.pzNorm with hcW
    set cX : ℝ := Work.Construction.L12 JX 0 / Work.FTS.StrongEps.pzNorm with hcX
    set err : ℝ := IP6o α JX f - IP6o α X Jf with herr
    set e : ℝ := rawE6 α g τ with he
    set Ee : ℝ := 1 + e with hEe
    set Y : ℝ := Real.sqrt Ee with hY
    have hXQo' : Work.FTS.VocabO.HQo α 6 X := by rw [hX]; exact hXQo
    have hXmem4 : Work.Spaces.HkMem α 4 X :=
      Work.FTS.OpenPkg.HkMem_mono_open hXQo'.1 4 (by norm_num) hXQo'.2
    have hXQuad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry X) Work.FTS.StrongEps.Quad :=
      fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall X).mp hXQo'.1 n
    have hX4 : Work.Spaces.HkNorm α 4 X ≤ Ct * (1 + Work.Spaces.HkNorm α 5 W) := by
      rw [hX, hW]; exact hX4b
    have hX6 : Work.Spaces.HkNorm α 6 X ≤ Ct * (1 + Work.Spaces.HkNorm α 7 W)
        + Ct * (1 + Work.Spaces.HkNorm α 6 W) ^ 2 := by
      rw [hX, hW]; exact hX6b
    have hWQo : Work.FTS.VocabO.HQo α 6 W := by rw [hW]; exact hctx.hreg.reg
    have hW7mem : Work.Spaces.HkMem α 7 W := by rw [hW]; exact hctx.h7
    have hWpz : W = Work.FTS.StrongEps.Pz Jf := by
      rw [hW, hJf]; exact Work.FTS.StrongEps.slice_JfamP ρ ε g τ
    -- # the energy scale
    have hraw : rawE6 α g τ = IP6o α (slice g τ) (slice g τ) := rfl
    have hlo : Work.Spaces.HkSq α 6 f ≤ e := by
      have hb : e = IP6o α f (slice g τ) := by rw [he, hraw, hf]
      rw [hb]
      show Work.Spaces.HkSq α 6 f ≤ Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α f f
      exact Work.FTS.StrongPersist.IP6_lo_coeffs (α₂ := α₂) hpair.pos.2 le_rfl le_rfl le_rfl
        le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl α hαIoc2 f hfQo
    have he0 : 0 ≤ e := le_trans (Work.Spaces.HkSq_nonneg α 6 f) hlo
    have hEnn : 0 ≤ Ee := by rw [hEe]; linarith
    have hE1 : 1 ≤ Ee := by rw [hEe]; linarith
    have hY1 : 1 ≤ Y := by rw [hY]; exact Real.one_le_sqrt.mpr hE1
    have hYnn : 0 ≤ Y := by rw [hY]; exact Real.sqrt_nonneg Ee
    have hf6 : Work.Spaces.HkNorm α 6 f ≤ Y := by
      calc Work.Spaces.HkNorm α 6 f = Real.sqrt (Work.Spaces.HkSq α 6 f) := rfl
        _ ≤ Real.sqrt e := Real.sqrt_le_sqrt hlo
        _ ≤ Real.sqrt Ee := Real.sqrt_le_sqrt (by rw [hEe]; linarith)
        _ = Y := by rw [hY]
    -- # the size inputs of the estimating block
    have hSqWe : Work.Spaces.HkSq α 6 W ≤ CW * e := by
      have h1 : Work.Spaces.HkSq α 6 W ≤ CW * Work.Spaces.HkSq α 6 f := by
        rw [hW, hf]
        exact hCW α hαIoc1 6 le_rfl ε hε.1 hε.2 g τ hfQuad hfloc hfmem6
      have h2 : CW * Work.Spaces.HkSq α 6 f ≤ CW * e := mul_le_mul_of_nonneg_left hlo hCWnn
      linarith [h1, h2]
    have hJfmem7 : Work.Spaces.HkMem α 7 Jf := by
      rw [hJf]
      exact (hstep α hαIoc1 7 (by norm_num) (by norm_num) ε hε f hfQuad hfmem6).1
    have hJf7 : Work.Spaces.HkNorm α 7 Jf ≤ Cg' * ε⁻¹ * Y := by
      have hstep7 := hstep α hαIoc1 7 (by norm_num) (by norm_num) ε hε f hfQuad hfmem6
      rw [hJf]
      have h1 : Work.Spaces.HkSq α 7 (Work.FTS.StrongEps.Jeps ρ ε f)
          ≤ (Cg' * ε⁻¹) ^ 2 * Work.Spaces.HkSq α 6 f := by
        have h2 : (Cg' * ε⁻¹) ^ 2 = Cg * ε⁻¹ ^ 2 := by
          rw [mul_pow, hCg', Real.sq_sqrt hCgnn.le]
        rw [h2]; exact hstep7.2
      calc Work.Spaces.HkNorm α 7 (Work.FTS.StrongEps.Jeps ρ ε f)
          = Real.sqrt (Work.Spaces.HkSq α 7 (Work.FTS.StrongEps.Jeps ρ ε f)) := rfl
        _ ≤ Real.sqrt ((Cg' * ε⁻¹) ^ 2 * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt h1
        _ = Cg' * ε⁻¹ * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hCg'nn (le_of_lt (inv_pos.mpr hε.1)))]
        _ ≤ Cg' * ε⁻¹ * Y := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCg'nn (le_of_lt (inv_pos.mpr hε.1)))
            rw [← Work.Spaces.HkNorm]
            exact hf6
    have hErr : |err| ≤ Cs1 * ε * Work.Spaces.HkNorm α 6 X * Work.Spaces.HkNorm α 6 f := by
      have h := hS1' α hαIoc1 ε hε X f hXQo' hfQo
      rw [herr, hJX, hJf]
      exact h
    have hJepsLe : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.Jeps ρ ε X)
        ≤ Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 X :=
      hCJ α hαIoc1 4 ε hε.1 hε.2 X hXQuad hXmem4
        (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαIoc1 hε.1 hXQuad hXmem4)
    have hL12sub' : |Work.Construction.L12 Jf 0 - Work.Construction.L12 f 0|
        ≤ CL2 * ε * Work.Spaces.HkNorm α 5 f := by
      rw [hJf]
      exact hL12sub α hαIoc1 f hfsmo
        (Work.FTS.OpenPkg.HkMem_mono_open hfsmo 5 (by norm_num) hfmem6) ε hε
    -- # the conservation of the zero mode (leaf F6, uniform-data form)
    have hBnn : 0 ≤ B := by
      have h := hb6 τ hτIcc
      have h0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (slice g τ) := by
        rw [Work.FTS.StrongGlobal.Xn6]; exact Work.Spaces.HkNorm_nonneg _ _ _
      linarith
    have hB0nn : 0 ≤ C₀ * α ^ 2 := by
      have h := hball 0 ⟨le_refl 0, hT.le⟩
      have h0 : 0 ≤ Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) 0) := by
        rw [Work.FTS.Nonlin.Xn]; exact Work.Spaces.HkNorm_nonneg _ _ _
      linarith
    have hml : ∀ w : Fn, Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        ‖Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => w z θ))
            (fun z θ _ => w z θ) 0‖ ≤ 1 / 2 ∧
        ‖Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => w z θ))
            (fun z θ _ => w z θ) 0‖ ≤ 1 := by
      intro w hw hb
      obtain ⟨h1, h2⟩ := hML w hw hb
      exact ⟨by rwa [Real.norm_eq_abs], by rwa [Real.norm_eq_abs]⟩
    obtain ⟨R, hRpos, hRbd⟩ := Work.FTS.StrongEps.EpsE4Thr.EpsRHSPBdd_generalRadius
      (α := α) (Ce := Ce) (Cs := Cs) (B := B) (B0 := C₀ * α ^ 2) (Mm := 1 / 2) (Ml := 1)
      (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
      hαIoc1 hρ hε.1 hε.2 hEll hstar6.toStarPkgo2 hBnn hB0nn hml
    have hRm : ∀ σ ∈ Set.Icc 0 T,
        Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) ∧
        Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) ≤ R := by
      intro σ hσ
      have hDσ : Work.FTS.StrongEps.EpsDatumP α ρ ε (slice g σ) := hreg.2 σ hσ
      have h := hRbd σ (slice g σ) hDσ.1 hDσ.2.1 (hb6 σ hσ) hDσ.2.2 (hball σ hσ)
      rw [Work.FTS.StrongEps.epsRHSP_eq_slice]
      exact ⟨Work.FTS.OpenPkg.HkMem_mono_open h.1 4 (by norm_num) h.2.1, h.2.2⟩
    have hWm : ∀ σ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g σ)) := by
      intro σ hσ
      have hDσ : Work.FTS.StrongEps.EpsDatumP α ρ ε (slice g σ) := hreg.2 σ hσ
      obtain ⟨hQo, _, _⟩ := hS2'' hρ hEll hstar6 hML ε hε g σ hDσ.2.2 (hball σ hσ)
      exact Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαIoc1 hε.1
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hQo.1)
        (Work.FTS.OpenPkg.HkMem_mono_open hQo.1 4 (by norm_num) hQo.2)
    have hL12z : Work.Construction.L12 f 0 = 0 := by
      have h := rawSlice_L12_zero_of_uniform (α := α) (ε := ε) (T := T) (B := R) (ρ := ρ)
        (Φs := Φs) (E := E) (g₀ := g₀) (g := g) hρ hαIoc1 hε.1 hT hd hsol hreg hRm hWm τ hτIcc
      rwa [← hf] at h
    -- # the H6Lin and H6Pair rows
    have hlinB : IP6o α (Work.FTS.StrongPersist.linPart α W) W
        ≤ CL * Work.Spaces.HkSq α 6 W := by
      have h := hlin α ⟨hα0, hαleL⟩ (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        hctx.hreg hctx.h7
      rw [hW]
      exact h
    have hpairB : |IP6o α Dn W| ≤ A2 * (1 + Work.Spaces.HkSq α 6 W) := by
      have h := hpair.pair α hαIoc2 (Work.FTS.StrongEps.JfamP ρ ε g)
        (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ (C₀ * α ^ 2) Cs E Φs
        hτ.1.le hctx
      rw [hDn, hW, hA2def]
      exact h
    have hsplitX : IP6o α X W = IP6o α (Work.FTS.StrongPersist.linPart α W) W + IP6o α Dn W := by
      have hfun : X = fun z θ =>
          (Work.FTS.StrongPersist.linPart α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) z θ
            + (Work.FTS.Galerkin.dynRHS α
                (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
                (Work.FTS.StrongEps.JfamP ρ ε g) τ) z θ := by
        rw [hX]
        funext z θ
        simp only [Work.FTS.StrongEps.epsWP, Work.FTS.StrongPersist.dynLin_eq_linPart,
          Pi.add_apply]
      rw [hfun, hW, hDn]
      exact hctx.hsplit
    have h12z : |Work.Construction.L12 JX 0| ≤ CLz * Work.Spaces.HkNorm α 4 JX := by
      have hJXquad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry JX) Work.FTS.StrongEps.Quad := by
        rw [hJX]
        exact Work.FTS.StrongEps.Jeps_contDiffOn ρ hρ hε.1
          (Work.FTS.StrongEps.locallyIntegrable_logPull_of_forall_contDiffOn hXQuad)
      have hJXsmo : Work.FTS.EllipticEst.SmoothOpen JX :=
        Work.FTS.EllipticEst.smoothOpen_of_forall hJXquad
      have hJXmem : Work.Spaces.HkMem α 4 JX := by
        rw [hJX]
        exact Work.FTS.StrongEps.HkMem_Jeps hρ.moll hαIoc1 hε.1 hXQuad hXmem4
      have h := hl12z α hα0 hα1 JX ⟨hJXsmo, hJXmem⟩
      simpa only [Work.FTS.Nonlin.Xn] using h
    -- # the estimate
    have hpb := RawE6Aux.rawE6_pair_bound (α := α) (ε := ε) (Cs1 := Cs1) (CL2 := CL2)
      (CLz := CLz) (CC := CC) (Bb := Bb) (CJ := CJ) (Cg' := Cg') (Ct := Ct) (K7 := K7)
      (CL := CL) (CW := CW) (A2 := A2) (Λ := Λ) (C₁ := C₁) (e := e) (Ee := Ee) (Y := Y)
      (cW := cW) (cX := cX) (err := err)
      (ρ := ρ) (Φs := Φs) (E := E) (g := g) (f := f) (W := W) (X := X) (Jf := Jf) (JX := JX)
      (D := Dn)
      hρ hαIoc1 hε.1 hε.2 hCs1nn hCL2nn hCLznn hCCnn hBbnn hCJnn hCg'nn hCtnn hK7nn hCLnn hCWnn
      hA2nn hK7 hΛ hC₁ hEe hY he0 hJf hJX hWpz hcW hcX herr hfsmo (by rw [hf]; exact hfmem6)
      hWQo hW7mem hXQo' hXmem4 hJfmem7 hSqWe hlo hX4 hX6 hJf7 (hBbb α hαIoc1 6 (by norm_num))
      (hBbb α hαIoc1 7 (by norm_num)) hJepsLe hErr hL12sub' h12z hL12z (fun u v hu hv => by
        have h := hcs α hαIoc2 u v hu hv
        simpa only [Work.FTS.StrongPersist.Xn6] using h) hlinB hsplitX hpairB
    have hkey : Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ = Work.FTS.StrongEps.Pz JX := by
      rw [hJX, hX]
      exact Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP α ρ ε Φs E g τ
    calc 2 * IP6o α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) (slice g τ)
        = 2 * IP6o α (Work.FTS.StrongEps.Pz JX) f := by rw [hkey, hf]
      _ ≤ Λ * Ee + ε * C₁ * Ee ^ 2 := hpb
      _ = Λ * (1 + rawE6 α g τ) + ε * C₁ * (1 + rawE6 α g τ) ^ 2 := by rw [hEe, he]

/-- **Leaf L-A, repaired, with S1 and S5 discharged** by the proved leaves
`RawE6Aux.Jeps_IP6_transfer_aux` (S1) and `RawE6Aux.L6Ctx_JfamP_aux` (S5); `S2`
(`epsWP_semitame`) is still an open leaf and is carried as a hypothesis. -/
theorem rawE6_ineq_uniform
    (hS2 : ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Ct : ℝ, 0 ≤ Ct ∧
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, Work.FTS.StrongEps.IsSmoothKernel ρ →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs → Work.FTS.StrongEps.MuLamOK α C₀ Φs E →
      ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ),
        Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
        Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
        Work.FTS.VocabO.HQo α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ) ∧
        Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 5 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ∧
        Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)
          ≤ Ct * (1 + Work.Spaces.HkNorm α 7 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
            + Ct * (1 + Work.Spaces.HkNorm α 6 (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) ^ 2)
    {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p)
    {α₂ Ce Cp : ℝ} (hpair : Work.FTS.StrongPersist.H6Pair (IP6o) α₂ Ce Cp) :
    ∀ C₀ Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Set.Ioc 0 α₀, ∃ Λ C₁ : ℝ, 0 ≤ Λ ∧ 0 ≤ C₁ ∧
    ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn},
    Work.FTS.StrongEps.EpsE4Thr.E4Data α C₀ K Ce Cs ρ Φs E g₀ →
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ T : ℝ, 0 < T → ∀ g : Fam,
      Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g → Work.FTS.StrongEps.EpsRegP α ρ ε T g →
      (∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2) →
      ∀ {B : ℝ}, (∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ B) →
      ∀ τ ∈ Set.Ioo 0 T,
        2 * IP6o α (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ) (slice g τ)
          ≤ Λ * (1 + rawE6 α g τ) + ε * C₁ * (1 + rawE6 α g τ) ^ 2 :=
  rawE6_ineq_uniform_of_leaves
    (fun hρ' hρs' => Work.FTS.StrongEps.E4R3.RawE6Aux.Jeps_IP6_transfer_aux hρ' hρs')
    hS2
    (fun C₀' Ce' Cs' => Work.FTS.StrongEps.E4R3.RawE6Aux.L6Ctx_JfamP_aux C₀' Ce' Cs')
    hρ hρs hpair

/-! **Leaf L-A, repaired.**  `rawE6_ineq_uniform` above is the assigned statement plus `hb6`,
with S1 and S5 discharged by their proved specialists (`E4R3/RawE6Aux/Jeps_IP6_transfer_aux`,
`E4R3/RawE6Aux/L6Ctx_JfamP_aux`) and S2 still an explicit hypothesis — the design's S2 leaf
(`Apriori4Proofs/epsWP_semitame_proof`) is currently *not* yet `sorry`-free transitively, so the
one-line unconditional form
`rawE6_ineq_uniform (fun C₀ Ce Cs => epsWP_semitame_proof C₀ Ce Cs) hρ hρs hpair`
should be added (here, as an instantiation) as soon as that module is closed. -/

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
