import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.KafzSym
import Submission.Work.BoseBoxFock.KzAll
import Submission.Work.BoseBoxFock.KzOpC_real
import Submission.Work.BoseBoxFock.bddBelow_valFS_range_rho
import Submission.Work.BoseBoxFock.bomb_KzOpFS_level0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.KzAllC` — the "All" (label-`0`) variants of the `Kz` instruments

`KzOpFSAll` (`KzAll.lean`) is FS `eq:Kz` *with* the χ-label-`0` row of `Q₂^ex`
adjoined.  This module provides the parallel equipment on the *spectator* side
(the zero-condensate slice `split f0 = single 0 v`):

* `kzEnvAt_rho_of_nonneg`, `kzEnvAt_W1omega`, `kzEnvAt_W1omega0`, `kz0Coef_eq` —
  the `ρ`-re-pointing of the environment;
* `D2FAll` — `D2F` without its label-`0` row (the row that `KzOpCAll` absorbs),
  and the identity `D2F = D2FAll + (2ℓ⁻³Ŵ₁ω(0)) • nOpC (f 0)`;
* `KzOpCAll` — `KzOpC` plus `kz0Coef E ρ • nOpC (f 0)`, its realness, and the
  transport `bomb_KzOpFSAll_level0` of `bomb_KzOpFS_level0`;
* the boundedness transfers `valFS_le_valFSAll`, `bddBelow_valFSAll_honest`,
  `bddBelow_valFSAll_range_rho`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {m : ℕ} [NeZero m]

/-! ## 0. A generic transfer of bounded-belowness -/

/-- `BddBelow` transfers upward along a pointwise `≤` relation, stated on the index type. -/
theorem bddBelow_range_of_le {ι α : Type*} [LinearOrder α] {f : ι → α} {S : Set α}
    (hS : BddBelow S) (h : ∀ i, ∃ y ∈ S, y ≤ f i) : BddBelow (Set.range f) := by
  obtain ⟨b, hb⟩ := hS
  exact ⟨b, by rintro x ⟨i, rfl⟩; obtain ⟨y, hy, hyx⟩ := h i; exact le_trans (hb hy) hyx⟩

/-! ## 1. The `ρ`-re-pointed environment -/

lemma kzEnvAt_rho_of_nonneg {E : Work.BoseB7.Q3Env Mode} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hℓ : 0 < E.ell) : (Work.BoseFixR.KzEnvAt E ρ).rho = ρ := by
  rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
  show (Real.sqrt (ρ * E.ell ^ 3)) ^ 2 / E.ell ^ 3 = ρ
  rw [Real.sq_sqrt (by positivity), mul_div_assoc, div_self (pow_ne_zero 3 (ne_of_gt hℓ)),
    mul_one]

lemma kzEnvAt_W1omega (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    (Work.BoseFixR.KzEnvAt E ρ).W1omega = E.W1omega := rfl

lemma kzEnvAt_W1omega0 (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    (Work.BoseFixR.KzEnvAt E ρ).W1omega0 = E.W1omega0 := rfl

/-- `kz0Coef E ρ = ρ (Ŵ₁ω(0) + Ŵ₁ω(0))` for `ρ ≥ 0`. -/
lemma kz0Coef_eq {E : Work.BoseB7.Q3Env Mode} {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    kz0Coef E ρ = ρ * (E.W1omega 0 + E.W1omega0) := by
  rw [kz0Coef, kzEnvAt_rho_of_nonneg (E := E) hρ hℓ,
    kzEnvAt_W1omega, kzEnvAt_W1omega0]

/-! ## 2. `D2FAll` -/

/-- `D2F` without its χ-label-`0` row (that row is what `KzOpCAll` puts back). -/
noncomputable def D2FAll (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (((-(4 * cHCF E gHat0) : ℝ)) : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))

lemma D2FAll_def (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    D2FAll f E gHat0
      = (((-(4 * cHCF E gHat0) : ℝ)) : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :=
  rfl

/-- The label-`0` row of `D2F` is exactly the row adjoined by `KzOpCAll`. -/
lemma D2F_eq_D2FAll (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    D2F f E gHat0 = D2FAll f E gHat0
      + (((2 * i3F E * E.W1omega0 : ℝ)) : ℂ) • nOpC (f 0) := rfl

/-- **The `D2FAll` row of the discrepancy**: its form is exactly `−4c_H ‖w‖²`. -/
lemma symR_row_D2FAll (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (w : cfock (Excited m)) :
    (inner ℂ w (D2FAll f E gHat0 w)).re = -(4 * cHCF E gHat0) * ‖w‖ ^ 2 := by
  rw [D2FAll_def, LinearMap.smul_apply, inner_smul_right, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Module.End.one_apply]
  exact congrArg (fun t => -(4 * cHCF E gHat0) * t) (Work.BoseB4.re_inner_self w)

/-! ## 3. The spectator operator with the label-`0` row -/

/-- FS `eq:Kz` on the zero-condensate slice **with the χ-label-`0` row of `Q₂^ex`**:
`KzOpC` plus `kz0Coef E ρ • nOpC (f 0)` — the spectator image of `KzOpFSAll`. -/
noncomputable def KzOpCAll (f g : Mode → Fin m → ℝ)
    (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  KzOpC f g BNH F E gHat0 ρ + (((kz0Coef E ρ : ℝ)) : ℂ) • nOpC (f 0)

lemma KzOpCAll_def (f g : Mode → Fin m → ℝ)
    (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    KzOpCAll f g BNH F E gHat0 ρ
      = KzOpC f g BNH F E gHat0 ρ + (((kz0Coef E ρ : ℝ)) : ℂ) • nOpC (f 0) := rfl

theorem KzOpCAll_real (f g : Mode → Fin m → ℝ)
    (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ)
    (hBNH : IsRealMap BNH) : IsRealMap (KzOpCAll f g BNH F E gHat0 ρ) := by
  rw [KzOpCAll_def]
  exact IsRealMap.add (KzOpC_real f g BNH F E gHat0 ρ hBNH)
    (IsRealMap.ofReal_smul (isRealMap_nOpC (f 0)))

/-! ## 4. The level-`0` transport -/

/-- `split (nOp 0 f0) = single 0 (nOpC (f 0) v)` on the zero-condensate slice. -/
theorem split_nOp_zero_slice {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ}
    (kmom : Mode → EuclideanSpace ℝ (Fin 3)) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (f : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (hφ : ∀ k : Mode, f k 0 = 0) (f0 : Work.BoseB4.RealFock m)
    (v : Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hsp : Work.BoseB4.split f0 = Finsupp.single 0 v) :
    Work.BoseB4.split
        ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0)
      = Finsupp.single 0 (nOpC (f 0) v) := by
  change Work.BoseB4.split
      (((Work.BoseB4.creOf m (f 0)).comp (Work.BoseB4.annOf m (f 0))) f0)
    = Finsupp.single 0 (nOpC (f 0) v)
  rw [LinearMap.comp_apply,
    split_creOf_annOf (m := m) (f 0) (f 0) (hφ 0) (hφ 0) f0, hsp,
    Work.BoseB4.lift_single]
  rfl

/-- **The level-`0` transport of `KzOpFSAll`**: on the zero-condensate slice the
`bomb`-form of `KzOpFSAll` is the spectator form of `KzOpCAll`. -/
theorem bomb_KzOpFSAll_level0 {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (T : Work.BoseB7A.TildeData (Work.BoseB4.boxFockData B kmom hkmom m f hf))
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) (hρ : 0 ≤ ρ) (hφ : ∀ k : Mode, f k 0 = 0)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hN : ∀ y : Work.BoseB4.RealFock m, Work.BoseB4.split (T.N y)
      = (Work.BoseB4.monoOp 1 1 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
          + Work.BoseB4.monoOp 0 0 ((Work.BoseBoxFock.nPlusC (m := m))
              - (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m)))) (Work.BoseB4.split y))
    (hNH : ∀ y : Work.BoseB4.RealFock m, Work.BoseB4.split (T.NH y) = Work.BoseB4.lift BNH (Work.BoseB4.split y))
    (hTa : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.ta s y) = Work.BoseB4.lift (Work.BoseBoxFock.annOfE (g s)) (Work.BoseB4.split y))
    (hTaDag : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.taDag s y) = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s)) (Work.BoseB4.split y))
    (f0 : Work.BoseB4.RealFock m) (v : Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hsp : Work.BoseB4.split f0 = Finsupp.single 0 v) :
    Work.BoseB4.bomb m f0 (Work.BoseBoxFock.KzOpFSAll (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ f0)
      = (inner ℂ v (Work.BoseBoxFock.KzOpCAll f g BNH (Work.BoseB4.boxFockData B kmom hkmom m f hf)
          E gHat0 ρ v)).re := by
  have hbase := bomb_KzOpFS_level0 B kmom hkmom f g hf T E gHat0 ρ hρ hφ BNH hN hNH hTa hTaDag
    f0 v hsp
  have hrow := split_nOp_zero_slice B kmom hkmom f hf hφ f0 v hsp
  have hrowbomb : Work.BoseB4.bomb m f0
      ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0)
      = (inner ℂ v (nOpC (f 0) v)).re := by
    have h := Work.BoseB4.Split_inner (m := m) f0
      ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0)
    have h1 : Work.BoseB4.bomb m f0
        ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0)
        = (Work.BoseB4.coreInner (Work.BoseB4.split f0)
            (Work.BoseB4.split
              ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0))).re :=
      (Complex.ofReal_re _).symm.trans (congrArg Complex.re h).symm
    rw [h1, hrow, hsp, coreInner_single_zero]
  have hKz : (Work.BoseBoxFock.KzOpFSAll (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0
      = (Work.BoseBoxFock.KzOpFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0
        + (kz0Coef E ρ) •
            ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0) := rfl
  have hstep : Work.BoseB4.bomb m f0
      ((Work.BoseBoxFock.KzOpFSAll (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
      = Work.BoseB4.bomb m f0
          ((Work.BoseBoxFock.KzOpFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
        + (kz0Coef E ρ) * Work.BoseB4.bomb m f0
            ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0) := by
    calc Work.BoseB4.bomb m f0
          ((Work.BoseBoxFock.KzOpFSAll (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
        = Work.BoseB4.bomb m f0
            ((Work.BoseBoxFock.KzOpFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0
              + (kz0Coef E ρ) •
                  ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0)) :=
          congrArg (fun z => Work.BoseB4.bomb m f0 z) hKz
      _ = Work.BoseB4.bomb m f0
            ((Work.BoseBoxFock.KzOpFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
          + Work.BoseB4.bomb m f0
              ((kz0Coef E ρ) •
                ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0)) :=
          map_add (Work.BoseB4.bomb m f0) _ _
      _ = Work.BoseB4.bomb m f0
            ((Work.BoseBoxFock.KzOpFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
          + (kz0Coef E ρ) * Work.BoseB4.bomb m f0
              ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0) :=
          congrArg (fun z => Work.BoseB4.bomb m f0
                ((Work.BoseBoxFock.KzOpFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
              + z)
            (map_smul (Work.BoseB4.bomb m f0) (kz0Coef E ρ)
              ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0))
  have hfin : (inner ℂ v (Work.BoseBoxFock.KzOpC f g BNH
          (Work.BoseB4.boxFockData B kmom hkmom m f hf) E gHat0 ρ v)).re
        + (kz0Coef E ρ) * (inner ℂ v (nOpC (f 0) v)).re
      = (inner ℂ v (Work.BoseBoxFock.KzOpCAll f g BNH
          (Work.BoseB4.boxFockData B kmom hkmom m f hf) E gHat0 ρ v)).re := by
    rw [KzOpCAll_def, LinearMap.add_apply, inner_add_right, Complex.add_re, LinearMap.smul_apply,
      inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact hstep.trans ((congrArg (fun z => z + (kz0Coef E ρ) * Work.BoseB4.bomb m f0
        ((Work.BoseB4.boxFockData B kmom hkmom m f hf).nOp (0 : Mode) f0)) hbase).trans
      ((congrArg (fun z => (inner ℂ v (Work.BoseBoxFock.KzOpC f g BNH
            (Work.BoseB4.boxFockData B kmom hkmom m f hf) E gHat0 ρ v)).re
          + (kz0Coef E ρ) * z) hrowbomb).trans hfin))

/-! ## 5. Boundedness transfers -/

/-- **`valFS ρ ≤ valFSAll ρ`** (the label-`0` row is a nonnegative form). -/
theorem valFS_le_valFSAll (D : Work.BoseFixR.KzDatum) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hℓ : 0 < D.E.ell) (hω : 0 ≤ D.E.W1omega 0 + D.E.W1omega0)
    (hbd : BddBelow (Set.range (fun g : {g : D.F.H // D.T.NWindow D.E.bigM g ∧ g ≠ 0} =>
      D.F.qw g.1 (KzOpFS D.F D.T D.E D.gHat0 ρ) / D.F.normSq g.1))) :
    D.valFS ρ ≤ D.valFSAll ρ := by
  have hcoef : 0 ≤ kz0Coef D.E ρ := by
    rw [kz0Coef_eq hρ hℓ]
    exact mul_nonneg hρ hω
  rw [Work.BoseFixR.KzDatum.valFS, Work.BoseFixR.KzDatum.valFSAll, KzValFS, KzValFSAll]
  refine ciInf_mono hbd (fun f => ?_)
  exact div_le_div_of_nonneg_right
    (KzOpFS_qw_le_KzOpFSAll D.F D.T D.E D.gHat0 ρ hcoef f.1) (D.F.normSq_nonneg f.1)

/-- **`valFSAll ρ` is below any window Rayleigh quotient of `KzOpFSAll`** (the
`All` analogue of `valFS_le_rayleigh`). -/
theorem valFSAll_le_rayleigh (D : Work.BoseFixR.KzDatum) (ρ : ℝ) (f : D.F.H)
    (hbd : BddBelow (Set.range (fun g : {g : D.F.H // D.T.NWindow D.E.bigM g ∧ g ≠ 0} =>
      D.F.qw g.1 (KzOpFSAll D.F D.T D.E D.gHat0 ρ) / D.F.normSq g.1)))
    (hwin : D.T.NWindow D.E.bigM f) (hf : f ≠ 0) :
    D.valFSAll ρ ≤ D.F.qw f (KzOpFSAll D.F D.T D.E D.gHat0 ρ) / D.F.normSq f := by
  rw [Work.BoseFixR.KzDatum.valFSAll, KzValFSAll]
  exact ciInf_le hbd ⟨f, hwin, hf⟩

/-- The `All` version of the fixed-`ρ` window boundedness. -/
theorem bddBelow_valFSAll_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ ρ : ℝ) (hρ : 0 ≤ ρ) (hℓ : 0 < (HonestBoxFam v h fc fu HM μ).E.ell)
    (hω : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega 0
      + (HonestBoxFam v h fc fu HM μ).E.W1omega0) :
    BddBelow (Set.range (fun g : {g : (HonestBoxFam v h fc fu HM μ).F.H //
        (HonestBoxFam v h fc fu HM μ).T.NWindow (HonestBoxFam v h fc fu HM μ).E.bigM g ∧ g ≠ 0} =>
      (HonestBoxFam v h fc fu HM μ).F.qw g.1
        (KzOpFSAll (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
          (HonestBoxFam v h fc fu HM μ).E (HonestBoxFam v h fc fu HM μ).gHat0 ρ)
        / (HonestBoxFam v h fc fu HM μ).F.normSq g.1)) := by
  obtain ⟨b, hb⟩ := bddBelow_valFS_honest v h fc fu HM μ ρ hρ
  have hcoef : 0 ≤ kz0Coef (HonestBoxFam v h fc fu HM μ).E ρ := by
    rw [kz0Coef_eq hρ hℓ]
    exact mul_nonneg hρ hω
  refine ⟨b, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hx
  refine le_trans (hb ⟨g, rfl⟩) ?_
  exact div_le_div_of_nonneg_right
    (KzOpFS_qw_le_KzOpFSAll (HonestBoxFam v h fc fu HM μ).F (HonestBoxFam v h fc fu HM μ).T
      (HonestBoxFam v h fc fu HM μ).E (HonestBoxFam v h fc fu HM μ).gHat0 ρ hcoef g.1)
    ((HonestBoxFam v h fc fu HM μ).F.normSq_nonneg g.1)

/-- The `All` version of the `ρ`-uniform boundedness. -/
theorem bddBelow_valFSAll_range_rho (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (μ Kw Kχ : ℝ) (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (hω0 : 0 ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
    (hωval : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega 0
      = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
    (hWω : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
      |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k| ≤ Kw)
    (hKχ : 0 ≤ Kχ)
    (hχb : (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s ^ 2) ≤ Kχ) :
    BddBelow (Set.range (fun ρ : {ρ : ℝ // 0 ≤ ρ} =>
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).valFSAll ρ.1)) := by
  have hℓ : 0 < (HonestBoxFam v h fc fu HM μ).E.ell := by
    show 0 < Work.BoseBox.sideAt μ (BoseGases.a v)
    exact Work.BoseBox.sideAt_pos hμ hav
  have hω : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega 0
      + (HonestBoxFam v h fc fu HM μ).E.W1omega0 := by
    rw [hωval]; linarith
  obtain ⟨b, hb⟩ := bddBelow_valFS_range_rho v h fc fu HM μ Kw Kχ hμ hav hω0 hWω hKχ hχb
  refine ⟨b, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hx
  refine le_trans (hb ⟨g, rfl⟩) ?_
  exact valFS_le_valFSAll (HonestBoxFam v h fc fu HM μ) g.2 hℓ hω
    (bddBelow_valFS_honest v h fc fu HM μ g.1 g.2)

end Work.BoseBoxFock
