import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.chanA_canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! The slot exchange `slotExchangeG` used below is the one proved in `PCFU/chanA_canonical.lean`
(the integrability-free form of `PCFU.slotExchangeComp`). -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.chanB_canonical`, `chanC_canonical`, `chanD_canonical`

The `(b)`, `(c)`, `(d)` channels of `MiddleU` (`PCFU.ChBU`, `ChCU`, `ChDU`), brought into the
**canonical** form in which the two *particle slots* `x i, x j` carry the window `χ_Λ` and the two
frame variables carry the sharp box `θ_Λ`.  These are the exact twins of the proved
`PCFU.chanA_canonical` (`Submission/Work/BoseBoxFock/PCFU/chanA_canonical.lean`), by the same two
measure-preserving changes of variables:

* `PCFU.slotExchangeG` — the slot/momentum exchange `(x, y, u) ↦ (x[i↦y][j↦u], x i, x j)`;
* `PCFU.configSlotSwap` — the bosonic relabelling `x ↦ x ∘ (i j)`.

Both are stated **without** integrability hypotheses.

## The canonical forms (derived, and consistent with `FINDING_PotCubicFreeU_exists_session7.md` §6)

Writing `θ = thetaFun (ellH v μ)`, `χ = chiLam (ellH v μ)`, and with `q.1 = x`, `y = q.2.1`,
`u = q.2.2`, `Θ' = Θ (x[i↦y][j↦u])`:

* `(A)` `Θ' Θ θ(y)θ(u) χ(x i)χ(x j) Ksfr(u − x j) KfrU(x j − x i)`  (proved, `chanA_canonical`);
* `(B)` `Θ' Θ θ(y)θ(u)θ(x i) χ(x j) Ksfr(u − x j) KχfrU(x j)`;
* `(C)` `Θ' Θ θ(y)θ(x j)θ(u) χ(x i) ℓ⁻³ ∫_w χ(w)Ksfr(u+w)KfrU(x i+w)`;
* `(D)` `Θ' Θ θ(y)θ(x j)θ(u)θ(x i) ℓ⁻³ ∫_w χ(w)Ksfr(u+w)KχfrU(w)`.

Note the `θ(x i)` in `(B)` and `(D)` (and the `θ(y)` in `(C)`, `(D)`): every channel carries the
`pinCond` factor `θ(x i)`, so the total count of `θ`-factors is preserved by the symmetries — the
session-7 §6 *candidate* forms for `(C)`, `(D)` (which dropped `θ(y)`) are corrected here.
-/

/-- **The `(b)`-channel in canonical form** (twin of `chanA_canonical`).  The reference channel is
`ChBU` (`PCFU/UnivFrames.lean`), whose kernel is
`Ksfr(x−y)·χ(y)·θ(x)·θ(u)·KχfrU(y)`. -/
theorem chanB_canonical {n : ℕ} {i j : Fin n} (hij : i ≠ j) (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 j) : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
            * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (q.1 j) := by
  set G : Submission.BoseGases.X n → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (x i) with hGdef
  set F1 : E3 → E3 → E3 → E3 → ℂ := fun a b c d =>
    Work.BoseBoxFock.Ksfr v fc μ N (b - c)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) c : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) b
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) d
      * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N c with hF1def
  set F2 : E3 → E3 → E3 → E3 → ℂ := fun a b c d =>
    Work.BoseK15.corpusBox.thetaFun (ellH v μ) a * F1 a b c d with hF2def
  have hG' : ∀ x : Submission.BoseGases.X n,
      (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ))
          (Submission.BoseGases.actPerm n (Equiv.swap i j) x)
        = (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)) x := by
    intro x
    simp only
    rw [hΘ (Equiv.swap i j) x]
  calc
    (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ q.1 : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * ChBU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
        = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            G q.1 * F1 (q.1 i) (q.1 j) q.2.1 q.2.2
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with q
          rw [ChBU, hGdef, hF1def]
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            G (Function.update (Function.update q.1 i q.2.1) j q.2.2)
              * F1 q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ) :=
          slotExchangeG hij G Θ F1
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            ((Θ q.1 : ℝ) : ℂ)
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
              * F2 q.2.1 q.2.2 (q.1 i) (q.1 j) := by
          apply integral_congr_ae
          filter_upwards with q
          have hu : (Function.update (Function.update q.1 i q.2.1) j q.2.2) i = q.2.1 := by
            simp [Function.update_apply, hij, hij.symm]
          simp only [hGdef, hF2def, hu]
          ring
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            ((Θ q.1 : ℝ) : ℂ)
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
              * F2 q.2.1 q.2.2 (q.1 j) (q.1 i) :=
          configSlotSwap hij (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)) hG' Θ F2
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 j) : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
            * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N (q.1 j) := by
          apply integral_congr_ae
          filter_upwards with q
          simp only [hF1def, hF2def]
          ring

/-- **The `(c)`-channel in canonical form** (twin of `chanA_canonical`).  The reference channel is
`ChCU`, whose kernel is `θ(y)·θ(x)·χ(u)·ℓ⁻³∫_w χ(w)Ksfr(x+w)KfrU(u+w)`. -/
theorem chanC_canonical {n : ℕ} {i j : Fin n} (hij : i ≠ j) (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 j)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 i) : ℝ) : ℂ)
            * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 i + w) := by
  set G : Submission.BoseGases.X n → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (x i) with hGdef
  set F1 : E3 → E3 → E3 → E3 → ℂ := fun a b c d =>
    Work.BoseK15.corpusBox.thetaFun (ellH v μ) c
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) b
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) d : ℝ) : ℂ)
      * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
      * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Work.BoseBoxFock.Ksfr v fc μ N (b + w)
          * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (d + w) with hF1def
  set F2 : E3 → E3 → E3 → E3 → ℂ := fun a b c d =>
    Work.BoseK15.corpusBox.thetaFun (ellH v μ) a * F1 a b c d with hF2def
  have hG' : ∀ x : Submission.BoseGases.X n,
      (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ))
          (Submission.BoseGases.actPerm n (Equiv.swap i j) x)
        = (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)) x := by
    intro x
    simp only
    rw [hΘ (Equiv.swap i j) x]
  calc
    (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ q.1 : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * ChCU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
        = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            G q.1 * F1 (q.1 i) (q.1 j) q.2.1 q.2.2
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with q
          rw [ChCU, hGdef, hF1def]
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            G (Function.update (Function.update q.1 i q.2.1) j q.2.2)
              * F1 q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ) :=
          slotExchangeG hij G Θ F1
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            ((Θ q.1 : ℝ) : ℂ)
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
              * F2 q.2.1 q.2.2 (q.1 i) (q.1 j) := by
          apply integral_congr_ae
          filter_upwards with q
          have hu : (Function.update (Function.update q.1 i q.2.1) j q.2.2) i = q.2.1 := by
            simp [Function.update_apply, hij, hij.symm]
          simp only [hGdef, hF2def, hu]
          ring
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            ((Θ q.1 : ℝ) : ℂ)
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
              * F2 q.2.1 q.2.2 (q.1 j) (q.1 i) :=
          configSlotSwap hij (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)) hG' Θ F2
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 j)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 i) : ℝ) : ℂ)
            * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 i + w) := by
          apply integral_congr_ae
          filter_upwards with q
          simp only [hF1def, hF2def]
          ring

/-- **The `(d)`-channel in canonical form** (twin of `chanA_canonical`).  The reference channel is
`ChDU`, whose kernel is `θ(y)·θ(x)·θ(u)·ℓ⁻³∫_w χ(w)Ksfr(x+w)KχfrU(w)`. -/
theorem chanD_canonical {n : ℕ} {i j : Fin n} (hij : i ≠ j) (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 j)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
            * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w := by
  set G : Submission.BoseGases.X n → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (x i) with hGdef
  set F1 : E3 → E3 → E3 → E3 → ℂ := fun a b c d =>
    Work.BoseK15.corpusBox.thetaFun (ellH v μ) c
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) b
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) d
      * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
      * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
          * Work.BoseBoxFock.Ksfr v fc μ N (b + w)
          * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w with hF1def
  set F2 : E3 → E3 → E3 → E3 → ℂ := fun a b c d =>
    Work.BoseK15.corpusBox.thetaFun (ellH v μ) a * F1 a b c d with hF2def
  have hG' : ∀ x : Submission.BoseGases.X n,
      (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ))
          (Submission.BoseGases.actPerm n (Equiv.swap i j) x)
        = (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)) x := by
    intro x
    simp only
    rw [hΘ (Equiv.swap i j) x]
  calc
    (∫ q : Submission.BoseGases.X n × (E3 × E3),
        ((Θ q.1 : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * ChDU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
        = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            G q.1 * F1 (q.1 i) (q.1 j) q.2.1 q.2.2
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with q
          rw [ChDU, hGdef, hF1def]
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            G (Function.update (Function.update q.1 i q.2.1) j q.2.2)
              * F1 q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ) :=
          slotExchangeG hij G Θ F1
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            ((Θ q.1 : ℝ) : ℂ)
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
              * F2 q.2.1 q.2.2 (q.1 i) (q.1 j) := by
          apply integral_congr_ae
          filter_upwards with q
          have hu : (Function.update (Function.update q.1 i q.2.1) j q.2.2) i = q.2.1 := by
            simp [Function.update_apply, hij, hij.symm]
          simp only [hGdef, hF2def, hu]
          ring
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            ((Θ q.1 : ℝ) : ℂ)
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
              * F2 q.2.1 q.2.2 (q.1 j) (q.1 i) :=
          configSlotSwap hij (fun x : Submission.BoseGases.X n => ((Θ x : ℝ) : ℂ)) hG' Θ F2
    _ = ∫ q : Submission.BoseGases.X n × (E3 × E3),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 j)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
            * (((ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * ∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 + w)
                * Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w := by
          apply integral_congr_ae
          filter_upwards with q
          simp only [hF1def, hF2def]
          ring

end Work.BoseBoxFock.PCFU
