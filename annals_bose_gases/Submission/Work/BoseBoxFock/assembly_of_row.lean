import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.boxRestrictState
import Submission.Work.BoseBoxFock.err_arith
import Submission.Work.BoseBoxFock.exists_modes_honestModes_ae_link
import Submission.Work.BoseBoxFock.spectralNPlus_boxRestrict
import Submission.Work.MB.H2ndHon_eq_H2ndF_dGamma
import Submission.Work.MB.modelAssemblyAVgen_weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.box_to_model` modulo its ONE remaining analytic input

This module isolates the analytic content of `Work.BoseBoxFock.box_to_model`: the proof reduces
the target to the single box-side row bound `Work.BoseBoxFock.RowB`, namely

    re ∫_x ⟨boxRestrict Φ, AVgen (boxSlotSum e) id f g T_NH PHs E (8π a v) (boxRestrict Φ)⟩
      ≤ (wordB/normB + errKafz v R μ C) · massR (boxRestrict Φ)

at the honest data (`e` the honest mode bundle of `Work.BoseBoxFock.exists_modes_honestModes_ae`,
`T_NH` the second quantisation of the honest `NH`, `E` the honest environment).

## Why the state is `boxRestrict Φ = Φ·1_{abox}`

`box_to_model` quantifies over `Φ : Work.BoseKinLoc.BoxState n ℓ` (smooth, permutation invariant,
nonzero, **no support hypothesis**), hence in general *unbounded* and not `L²`; the BF3c selection
chain needs a measurable, everywhere bounded state supported in the box, and it needs
`0 < massR` (the *global* `L²` mass).  The box restriction is exactly that state
(`Work.BoseBoxFock.boxRestrictState`: measurable, everywhere bounded, supported in the box,
permutation invariant, and `massR = sqNormB = normB`), and the spectral hypothesis transports
(`Work.BoseBoxFock.spectralNPlus_boxRestrict`: `n₊` is box local).  This is why the BF3c chain had
to be re-run in the weak (measurable / everywhere bounded / box supported) state class — done in
`Submission/Work/MB/` (`Work.MB.modelAssemblyAVgen_weak` is the assembly).

## The remaining input

`RowB` is the box-side row inequality of FS `prop:Hamilton2ndQuant`: the model's first-quantised
form at `boxRestrict Φ` is dominated by FS's box word `wordB` plus the error `errKafz`.  Splitting
`AVgen` into its eleven rows, all rows but the *kinetic* one are identities/bookkeeping between the
model slots and the corpus's box kernels; the kinetic row is the aliasing (sampling) comparison
lattice vs continuum of `Work.BoseBoxFock.tauPhi_row_closedBall` /
`Work.BoseBoxFock.sharpShiftRow`.  `RowB` is stated with `errKafz` on the right (rather than with
`wordB + errB·normB` and `bf3a`), so that the assembly can consume it directly at the coefficient
`wordB/normB + errKafz` of the target.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

/-- The box restriction of a box state, as a **real**-valued function: `Φ·1_{abox n ℓ}`. -/
noncomputable def boxRestrictR {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n → ℝ :=
  fun x => Φ x * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x

/-- The box restriction of a box state, as a **complex**-valued function (the form used by
`Work.BoseBoxFock.boxRestrictState`). -/
noncomputable def boxRestrictC {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Submission.BoseGases.X n → ℂ :=
  fun x => ((Φ x : ℝ) : ℂ) * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x

/-- The complex box restriction is the coercion of the real one. -/
lemma boxRestrictC_eq_ofReal {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    boxRestrictC ℓ Φ = fun x => ((boxRestrictR ℓ Φ x : ℝ) : ℂ) := by
  funext x
  simp only [boxRestrictC, boxRestrictR, Complex.ofReal_mul]

/-- The coercion of the real box restriction is the complex one. -/
lemma ofReal_boxRestrictR {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    ((boxRestrictR ℓ Φ x : ℝ) : ℂ) = boxRestrictC ℓ Φ x := by
  simp only [boxRestrictR, boxRestrictC, Complex.ofReal_mul]

/-- The complex norm of the complex box restriction is the absolute value of the real one. -/
lemma norm_boxRestrictC {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    ‖boxRestrictC ℓ Φ x‖ = |boxRestrictR ℓ Φ x| := by
  rw [← ofReal_boxRestrictR]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The real part of the complex box restriction. -/
lemma re_boxRestrictC {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    (boxRestrictC ℓ Φ x).re = boxRestrictR ℓ Φ x := by
  rw [← ofReal_boxRestrictR]
  exact Complex.ofReal_re _

/-- `ellH v μ = sideAt μ (a v)` when the box side is positive (a cone-free copy of
`Work.BoseBoxFock.ellH_eq_sideAt`, whose module is not importable together with the model
assembly). -/
lemma ellH_eq_sideAt_asm {v : ℝ³ → ℝ} {μ : ℝ}
    (h : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
  rw [ellH, if_pos h]

/-- **The honest mode bundle at `ℓ = sideAt μ (a v)`** (a cone-free copy of
`Work.MB.honest_modes_at_sideAt`): measurable, everywhere bounded, box supported, orthonormal,
integrable products, `L^∞`, and pinned to `θ_ℓ`. -/
theorem honest_modes_at_sideAt' (v : ℝ³ → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    ∃ e : Fin (HM.m) → Ω → ℂ,
      (∀ l, Measurable (e l)) ∧
      (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) ∧
      (∀ l, Function.support (e l)
        ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) ∧
      (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
        = (if l = l' then (1 : ℂ) else 0)) ∧
      (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) ∧
      (∀ l, MeasureTheory.MemLp (e l) ⊤) ∧
      (∃ c : ℂ, (starRingEnd ℂ) c * c = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
        (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure Ω),
          e 0 x = c * Work.BoseK15.corpusBox.thetaFun
            (Work.BoseBox.sideAt μ (BoseGases.a v)) x)) := by
  have h := Work.BoseBoxFock.exists_modes_honestModes_ae v μ HM
  rw [ellH_eq_sideAt_asm hℓ] at h
  simp only [starRingEnd_apply] at h
  exact h

/-- **The honest mode bundle at `ℓ = sideAt μ (a v)` *with the coordinate pairings*** — the
version consumed by the *row table* (`RowB`): the pairings against the physical modes
`qVec (kmomLab ℓ N k)` / `thetaExp (kmomLab ℓ N s)` / `thetaFun ℓ` are the honest coordinate
vectors `HM.f`, `HM.g`.  Without these the row table is FALSE (the mode family would be free
while `f` is fixed — see `Submission/Work/BoseBoxFock/FormW2B_holds.lean`). -/
theorem honest_modes_at_sideAt_link (v : ℝ³ → ℝ) (μ : ℝ) (HM : HonestModes v μ)
    (hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    ∃ e : Fin (HM.m) → Ω → ℂ,
      (∀ l, Measurable (e l)) ∧
      (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) ∧
      (∀ l, Function.support (e l)
        ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) ∧
      (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
        = (if l = l' then (1 : ℂ) else 0)) ∧
      (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) ∧
      (∀ l, MeasureTheory.MemLp (e l) ⊤) ∧
      (∃ c : ℂ, (starRingEnd ℂ) c * c = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
        e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
            (Work.BoseBox.sideAt μ (BoseGases.a v)) x) ∧
      (∀ (k : Lab (HM).N) (l : Fin (HM).m),
        (∫ z : Ω, star (e l z)
            * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM).N k) z)
          = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
              * (HM).f k l : ℝ) : ℂ)) ∧
      (∀ (s : Lab (HM).N) (l : Fin (HM).m), s ≠ 0 →
        (∫ z : Ω, star (e l z)
            * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM).N s) z)
          = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
              * (HM).g s l : ℝ) : ℂ)) ∧
      (∫ z : Ω, star (e 0 z)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
        = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  have h := Work.BoseBoxFock.exists_modes_honestModes_ae_link v μ HM
  rw [ellH_eq_sideAt_asm hℓ] at h
  simpa only [starRingEnd_apply] using h

/-- **The one remaining analytic input of `box_to_model`** (the box-side row bound at the honest
data).  See the module docstring. -/
noncomputable def RowB (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (R J : ℝ) (Nmin : ℝ → ℕ) (ε₀ C : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
        (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
        0 < Work.BoseBoxFix.normB v μ n Φ →
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
          (Φ : Submission.BoseGases.X n → ℝ) →
        ∀ (e : Fin (HM μ).m → Ω → ℂ),
          (∀ l, Measurable (e l)) →
          (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) →
          (∀ l, Function.support (e l)
            ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBox.sideAt μ (BoseGases.a v))) →
          (∀ l l', (∫ z : Ω, star (e l z) * e l' z)
            = (if l = l' then (1 : ℂ) else 0)) →
          (∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z)) →
          (∀ l, MeasureTheory.MemLp (e l) ⊤) →
          (∃ c : ℂ, (starRingEnd ℂ) c * c
              = ((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)⁻¹ ∧
            e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun
                (Work.BoseBox.sideAt μ (BoseGases.a v)) x) →
          (∀ (k : Lab (HM μ).N) (l : Fin (HM μ).m),
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.qVec (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N k) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).f k l : ℝ) : ℂ)) →
          (∀ (s : Lab (HM μ).N) (l : Fin (HM μ).m), s ≠ 0 →
            (∫ z : Ω, star (e l z)
                * Work.BoseK15.corpusBox.thetaExp (Work.BoseBox.sideAt μ (BoseGases.a v))
                    (kmomLab (Work.BoseBox.sideAt μ (BoseGases.a v)) (HM μ).N s) z)
              = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ)
                  * (HM μ).g s l : ℝ) : ℂ)) →
          (∫ z : Ω, star (e 0 z)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBox.sideAt μ (BoseGases.a v)) z)
            = (((Work.BoseBox.sideAt μ (BoseGases.a v)) ^ (3 / 2 : ℝ) : ℝ) : ℂ) →
          ∀ (T_NH : (Fin (HM μ).m → ℝ) →ₗ[ℝ] (Fin (HM μ).m → ℝ)),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
                = Work.BoseB4.dGamma (HM μ).m T_NH →
            (∫ x : Submission.BoseGases.X n,
                star (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x)
                  * Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
                      (id : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
                      (HM μ).f (HM μ).g T_NH
                      ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
                        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
                      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
                      (8 * Real.pi * BoseGases.a v)
                      (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) x).re
              ≤ (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
                  + Work.BoseFixR.errKafz v R μ C)
                * Work.BoseBoxFock.massR
                    (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)

/-- **`box_to_model` follows from `RowB`**: the whole assembly, with the single analytic input
isolated.  The `Nmin`/`ε₀`/`C` of the target are the ones of `RowB` (note `RowB` also carries the
a-priori data `J`; the target's hypotheses `n ≤ 2μℓ³`, `IsLowB` and `Nmin μ ≤ (HM μ).N` are used
only inside `RowB`). -/
theorem box_to_model_of_row (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc)
    (hRow : ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ RowB v h fc fu R J Nmin ε₀ C) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ HM : ∀ μ : ℝ, HonestModes v μ, (∀ μ, Nmin μ ≤ (HM μ).N) →
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
            (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
            0 < Work.BoseBoxFix.normB v μ n Φ →
            Work.BoseBoxFix.IsLowB v h J μ n Φ →
            Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
              (Φ : Submission.BoseGases.X n → ℝ) →
            ∃ Ψ : Work.BoseB4.RealFock (HM μ).m, Ψ ≠ 0 ∧
              ExcWindow (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
                (BoseGases.a v) μ) n Ψ ∧
              Work.BoseB4.bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ)
                ≤ (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
                    + Work.BoseFixR.errKafz v R μ C)
                    * Work.BoseB4.bomb (HM μ).m Ψ Ψ := by
  obtain ⟨Nmin, ε₀, C, hε0, hC0, hrow⟩ := hRow
  refine ⟨Nmin, ε₀, C, hε0, hC0, ?_⟩
  intro HM hNmin μ hAdm hJ n Φ hn hnorm hlow hmom
  obtain ⟨hμpos, htε, hPOK⟩ := hAdm
  have hAdm' : Work.BoseBoxFix.Adm v ε₀ μ := ⟨hμpos, htε, hPOK⟩
  have hℓ : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBox.sideAt_eq_rpow hav hμpos]; positivity
  -- ## the honest mode bundle, with the coordinate pairings
  obtain ⟨e, he1, he2, he3, he4, he5, he6, he7, hf8, hg8, hθ8⟩ :=
    honest_modes_at_sideAt_link v μ (HM μ) hℓ
  -- ## the second quantisation of the honest `NH`
  obtain ⟨T_NH, hT⟩ := Work.BoseBoxFock.NH_eq_dGamma v h fc fu HM μ
  -- ## the box restriction and its weak regularity
  obtain ⟨hΘcm, hΘcb, -, hΘcsymC, hΘcmass⟩ := Work.BoseBoxFock.boxRestrictState hℓ Φ
  have hfun : (fun x : Submission.BoseGases.X n =>
      ((boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x : ℝ) : ℂ))
      = boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ :=
    funext fun x => ofReal_boxRestrictR _ _ x
  have hΘm : Measurable (boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) := by
    have h1 : Measurable (fun x =>
        (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x).re) :=
      Complex.measurable_re.comp hΘcm
    have h2 : (fun x => (boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x).re)
        = boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ :=
      funext fun x => re_boxRestrictC _ _ x
    rwa [h2] at h1
  have hΘb : ∃ C : ℝ,
      ∀ x, |boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x| ≤ C := by
    obtain ⟨B, hB⟩ := hΘcb
    refine ⟨B, fun x => ?_⟩
    have h := hB x
    have h' : ‖boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x‖ ≤ B := h
    rwa [norm_boxRestrictC] at h'
  have hΘsupp : Function.support (boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)
      ⊆ Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v)) := by
    intro x hx
    simp only [Function.mem_support] at hx
    by_contra hxb
    simp only [boxRestrictR, Set.indicator_of_notMem hxb, mul_zero] at hx
    exact hx rfl
  have hΘsym : ∀ σ : Equiv.Perm (Fin n),
      (fun x => boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ (x ∘ σ))
        = boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ := by
    intro σ
    have h2 : ∀ x, boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ (x ∘ σ)
        = boxRestrictC (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x :=
      congrFun (hΘcsymC σ)
    funext x
    have h3 : ((boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ (x ∘ σ) : ℝ) : ℂ)
        = ((boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x : ℝ) : ℂ) := by
      simpa only [ofReal_boxRestrictR] using h2 x
    exact Complex.ofReal_injective h3
  have hmomΘ : Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
      (boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ) :=
    Work.BoseBoxFock.spectralNPlus_boxRestrict hmom
  have hmassΘC : massR (fun x => ((Φ x : ℝ) : ℂ)
      * (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (BoseGases.a v))).indicator
          (fun _ => (1 : ℝ)) x) = Work.BoseBoxFix.normB v μ n Φ := by
    rw [hΘcmass]
    rfl
  have hmassΘ : massR (fun x =>
      ((boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x : ℝ) : ℂ))
      = Work.BoseBoxFix.normB v μ n Φ := by
    rw [hfun]
    exact hmassΘC
  have hposΘ : 0 < massR (fun x =>
      ((boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ x : ℝ) : ℂ)) := by
    rw [hmassΘ]; exact hnorm
  have hM0 : 0 ≤ Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
      (BoseGases.a v) μ := by
    have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
    simp only [Work.BoseBox.bigM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
      Work.BoseBox.fsXp]
    exact le_of_lt (mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos ht _))
  -- ## the one analytic input
  have hcle := hrow HM hNmin μ hAdm' hJ n Φ hn hnorm hlow hmom e he1 he2 he3 he4 he5 he6 he7
    hf8 hg8 hθ8 T_NH hT
  -- ## the model assembly
  obtain ⟨Ψ, hne, hwin, hbound⟩ :=
    Work.MB.modelAssemblyAVgen_weak (m := (HM μ).m) (n := n)
      (ℓ := Work.BoseBox.sideAt μ (BoseGases.a v))
      (M := Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
      hℓ e he1 he2 he4 he5 he6 he3 he7
      (f := (HM μ).f) (g := (HM μ).g) (T_NH := T_NH)
      (PHs := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
      (E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
      (gHat0 := 8 * Real.pi * BoseGases.a v)
      (boxRestrictR (Work.BoseBox.sideAt μ (BoseGases.a v)) Φ)
      hΘm hΘb hΘsupp hΘsym hM0 hmomΘ
      (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
        + Work.BoseFixR.errKafz v R μ C)
      hposΘ (by simpa only [← hfun] using hcle)
  refine ⟨Ψ, hne, hwin, ?_⟩
  have hH2 : H2ndHon v h fc fu HM μ
      = Work.BoseBoxFock.H2ndF (HM μ).f (HM μ).g (Work.BoseB4.dGamma (HM μ).m T_NH)
          ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E)
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E (8 * Real.pi * BoseGases.a v) := by
    rw [H2ndHon, hT]
  rw [hH2]
  exact hbound

end Work.BoseBoxFock
