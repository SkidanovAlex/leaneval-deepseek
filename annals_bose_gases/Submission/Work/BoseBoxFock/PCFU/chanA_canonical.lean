import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
import Submission.Work.BoseBoxFock.PCFU.configSlotSwap
import Submission.Work.BoseBoxFock.PCFU.slotExchange
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.chanA_canonical` — the canonical form of the `(a)`-channel

Thematic statement: the `(a)`-channel of `MiddleU` (`PCFU.ChAU`, an integral over the two
"momentum-slot" variables `y, u` against the `s`-frame `Ksfr` and the `k`-frame `KfrU`) can be
brought into the **canonical** form in which the two *particle slots* `x i, x j` carry the window
`χ_Λ` and the two frame variables carry the sharp box `θ_Λ`.  This is a two-step change of
variables on `X n × (E³ × E³)`:

* `slotExchangeG` — the slot/momentum exchange
  `(x, y, u) ↦ (x[i↦y][j↦u], (x i, x j))` (measure preserving, `PCFU.slotExchange`), which moves the
  two slots and the two momenta into each other's positions;
* `PCFU.configSlotSwap` — the bosonic relabelling `x ↦ x ∘ (i j)` of the particle configuration,
  which exchanges the roles of the two slots `i, j` (used because `Θ` is permutation invariant).

Both are stated **without** any integrability hypothesis: the change of variables is along a
measurable equivalence, so it holds unconditionally for the Bochner integral.
-/

/-- The slot/momentum exchange with an extra configuration factor `G`, **without** an integrability
hypothesis on the pairing.  This is `PCFU.slotExchangeComp` with its (unused) integrability
hypothesis removed. -/
theorem slotExchangeG {n : ℕ} {i j : Fin n} (hij : i ≠ j) (G : Submission.BoseGases.X n → ℂ)
    (Θ : Submission.BoseGases.X n → ℝ) (F : E3 → E3 → E3 → E3 → ℂ) :
    (∫ q : Submission.BoseGases.X n × (E3 × E3),
        G q.1 * F (q.1 i) (q.1 j) q.2.1 q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
        G (Function.update (Function.update q.1 i q.2.1) j q.2.2)
          * F q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ) := by
  have hmp := pairSlotRollEquiv_measurePreserving i j
  set ψ : Submission.BoseGases.X n × (E3 × E3) → ℂ := fun q =>
    G q.1 * F (q.1 i) (q.1 j) q.2.1 q.2.2
      * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ) with hψ
  have hpt : ∀ q : Submission.BoseGases.X n × (E3 × E3),
      ψ (pairSlotRoll i j q)
        = G (Function.update (Function.update q.1 i q.2.1) j q.2.2)
          * F q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ) := by
    intro q
    have hi : (Function.update (Function.update q.1 i q.2.1) j q.2.2) i = q.2.1 := by
      simp [Function.update_apply, hij, hij.symm]
    have hj : (Function.update (Function.update q.1 i q.2.1) j q.2.2) j = q.2.2 := by
      simp [Function.update_apply, hij, hij.symm]
    have hundo : Function.update (Function.update
        (Function.update (Function.update q.1 i q.2.1) j q.2.2) i (q.1 i)) j (q.1 j) = q.1 := by
      funext k
      by_cases hki : k = i
      · subst hki
        simp [Function.update_apply, hij, hij.symm]
      · by_cases hkj : k = j
        · subst hkj
          simp [Function.update_apply, hki, hij, hij.symm]
        · simp [Function.update_apply, hki, hkj]
    rw [hψ]
    simp only [pairSlotRoll]
    rw [hi, hj, hundo]
  have h1 : (∫ q : Submission.BoseGases.X n × (E3 × E3),
      G q.1 * F (q.1 i) (q.1 j) q.2.1 q.2.2
        * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)) = ∫ q, ψ q := rfl
  have key : (∫ q, ψ q) = ∫ q, ψ (pairSlotRollEquiv i j q) := (hmp.integral_comp' ψ).symm
  have h2 : (∫ q, ψ (pairSlotRollEquiv i j q))
      = ∫ q : Submission.BoseGases.X n × (E3 × E3),
        G (Function.update (Function.update q.1 i q.2.1) j q.2.2)
          * F q.2.1 q.2.2 (q.1 i) (q.1 j) * ((Θ q.1 : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with q
    rw [pairSlotRollEquiv_apply hij q]
    exact hpt q
  exact h1.trans (key.trans h2)

theorem chanA_canonical {n : ℕ} {i j : Fin n} (hij : i ≠ j) (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ)
    (Θ : Submission.BoseGases.X n → ℝ) (hΘ : Submission.BoseGases.PermInvariant n Θ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) :
    (∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
        ((Θ q.1 : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (q.1 i)
          * Work.BoseBoxFock.PCFU.ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
      = ∫ q : Submission.BoseGases.X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
          ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ)
            * ((Θ q.1 : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.1
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) q.2.2
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 i) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 j) : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 j - q.1 i) := by
  set G : Submission.BoseGases.X n → ℂ := fun x =>
    ((Θ x : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun (ellH v μ) (x i) with hGdef
  set F1 : E3 → E3 → E3 → E3 → ℂ := fun a b c d =>
    Work.BoseBoxFock.Ksfr v fc μ N (b - c)
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) c : ℝ) : ℂ)
      * Work.BoseK15.corpusBox.thetaFun (ellH v μ) b
      * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) d : ℝ) : ℂ)
      * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (c - d) with hF1def
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
          * ChAU v h fc fu μ N q.2.1 (q.1 j) q.2.2
          * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ))
        = ∫ q : Submission.BoseGases.X n × (E3 × E3),
            G q.1 * F1 (q.1 i) (q.1 j) q.2.1 q.2.2
              * ((Θ (Function.update (Function.update q.1 i q.2.1) j q.2.2) : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with q
          rw [ChAU, hGdef, hF1def]
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
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 i) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.chiLam (ellH v μ) (q.1 j) : ℝ) : ℂ)
            * Work.BoseBoxFock.Ksfr v fc μ N (q.2.2 - q.1 j)
            * Work.BoseBoxFock.PCFU.KfrU v h μ fu N (q.1 j - q.1 i) := by
          apply integral_congr_ae
          filter_upwards with q
          simp only [hF1def, hF2def]
          ring

end Work.BoseBoxFock.PCFU
