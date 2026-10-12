import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sharpAlias
import Submission.Work.BoseBoxFock.tauSplitBricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.ledgerParen` — the **canonical `(★)` ledger identity**, correctly parenthesised

This module proves the identity that `Submission/Work/BoseBoxFock/ledger_eq_deficitForm.lean`
*intends* to state (and whose text, as elaborated by Lean, is a different — false — statement,
because the trailing `- (5/4 + tauC0phi) * c^2 * (...)` is absorbed into the integrand of the
preceding `∫`; see the docstring of that file, and
`Work.BoseBoxFock.ledger_eq_deficitForm_forces_mass_zero` there for a machine-checked proof that
the statement as written forces `(2π)⁻³∫_p ‖ĝ(p)‖² = 0`).

The statement proved here is, verbatim with parentheses added around the first integral,

    latDeficit ℓ c g + lowGain ℓ c g - 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g)
      = c * (3 * tauLatPow ℓ 1 g - 2 * tauContPow 1 g)
        + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
            * ‖kinFT g (kmomInt ℓ n)‖ ^ 2)
        - ((2 * Real.pi) ^ 3)⁻¹ * (∫ p, tauTheta c ‖p‖ * ‖kinFT g p‖ ^ 2)
        - (5 / 4 + tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖kinFT g p‖ ^ 2) ,

i.e. the `(★)` identity recorded in `FINDING_pipeline_status.md` §5:
`LHS = c(3S₁ − 2R₁) + L(Ψ_c) − C(Θ_c) − (5/4+c₀)c²R₀`.

## The proof (three ingredients)

1. **Pointwise algebra.** `tauPsi_eq_deficit_add_thetaSym` :
   `Ψ_c(r) = δ_c(r) + Θ_c(r) − c·r + (5/4+c₀)c²`, where `δ_c` is `deficit` (`= F_c − τ_c`,
   `deficit_eq_tauSharp_sub_phi`) and `Θ_c = thetaSym c` (`= tauTheta c`,
   `thetaSym_eq_tauTheta`).  It is `tauPsi_eq_sharp_split` (`tauSplitBricks`) reread in the
   `deficit`/`thetaSym` vocabulary of `sharpAlias`.

2. **Linearity of the lattice sum** (`tsum_ledger_linear`): with the three lattice summabilities
   (`summable_latDeficit`, `summable_latThetaSym`, `tauPsiLatticeSummable`) and the two moment
   summabilities (`summable_lattice_kinFT_weight` at `j = 0, 1`), the pointwise identity sums to

       latDeficit ℓ c g + L(Θ_c) = L(Ψ_c) + c·S₁ − (5/4+c₀)c²·L(1) ,     (★₀)

   using only `tsum_add`, `tsum_sub` and `tsum_mul_left` (the `δ_c ≤ c‖p‖` bound
   `deficit_le_mul_norm` and `Θ_c ≤ c²` bound `thetaSym_le_sq` supply the summabilities).

3. **The frame identity** `L(1) = R₀` (`deficit_inputs`'s first conjunct, from
   `frame_lattice_ball`), which turns `L(1)` in (★₀) into `(2π)⁻³∫_p ‖ĝ(p)‖²`.

Substituting (★₀) into the left-hand side and `lowGain = L(Θ_c) − C(Θ_c)` gives the identity:
the `c·S₁` slot cancels the first-moment combination `−2c(R₁−S₁)` against `3cS₁ − 2cR₁`, and
`C(Θ_c)` appears on both sides.  No second-moment identity is needed.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `thetaSym c` and `tauTheta c` are the same symbol (`max` commuted).  `lowGain` is stated with
the former, the target statement with the latter. -/
lemma thetaSym_eq_tauTheta (c r : ℝ) : thetaSym c r = tauTheta c r := by
  rw [thetaSym, tauTheta, max_comm]

/-- The `sharpAlias` deficit `δ_c = (r−c)₊² − τ_c(r)` is `tauSharp c r − c²·tauPhi (r/c)`. -/
lemma deficit_eq_tauSharp_sub_phi (c r : ℝ) :
    deficit c r = tauSharp c r - c ^ 2 * tauPhi (r / c) := by
  rw [deficit, tauSharp, max_comm (r - c) 0]

/-- **The pointwise brick of the ledger identity**, in the `sharpAlias` vocabulary:
`Ψ_c(r) = δ_c(r) + Θ_c(r) − c·r + (5/4+c₀)c²`.  This is `tauPsi_eq_sharp_split` rewritten. -/
lemma tauPsi_eq_deficit_add_thetaSym (c r : ℝ) :
    tauPsi c r = deficit c r + thetaSym c r - c * r + (5 / 4 + tauC0phi) * c ^ 2 := by
  rw [tauPsi_eq_sharp_split, ← deficit_eq_tauSharp_sub_phi, ← thetaSym_eq_tauTheta]

/-- `δ_c(r) ≤ c·r` for `c > 0`, `r ≥ 0`: the deficit grows at most linearly in the frequency
(it is `0` below `c`, at most `(r−c)² ≤ c·r` on `[c,2c]`, and exactly `c·r − (5/4+c₀)c²` above
`2c`).  This is what makes the lattice sum of the deficit summable. -/
lemma deficit_le_mul_norm {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : deficit c r ≤ c * r := by
  rcases le_or_gt r c with h | h
  · rw [deficit_eq_zero_of_le hc h]; positivity
  · rcases le_or_gt r (2 * c) with h2 | h2
    · rw [deficit]
      rw [max_eq_left (by linarith : (0:ℝ) ≤ r - c)]
      have hz : 0 ≤ c ^ 2 * tauPhi (r / c) := mul_nonneg (sq_nonneg c) (tauPhi_nonneg _)
      have hprod : 0 ≤ (r - c) * (2 * c - r) := mul_nonneg (by linarith) (by linarith)
      nlinarith [hprod, hz, h, h2]
    · rw [deficit_eq_tail hc h2.le]
      nlinarith [tauPhiC0_nonneg, sq_nonneg c]

/-- `Θ_c(r) ≤ c²`: the low-frequency cap is bounded (so its lattice sum is summable). -/
lemma thetaSym_le_sq {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : thetaSym c r ≤ c ^ 2 := by
  rw [thetaSym]
  have h1 : max (c - r) 0 ≤ c := max_le (by linarith) hc.le
  have h2 : 0 ≤ max (c - r) 0 := le_max_right _ _
  exact pow_le_pow_left₀ h2 h1 2

/-- The lattice form of the deficit is summable (`δ_c ≤ c‖·‖` against the weight `j = 1`). -/
lemma summable_latDeficit {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
  have hs : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    simpa using summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 1
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hs.mul_left c)
  · exact mul_nonneg (mul_nonneg (by positivity) (deficit_nonneg hc (norm_nonneg _))) (sq_nonneg _)
  · have hδ : deficit c ‖kmomInt ℓ n‖ ≤ c * ‖kmomInt ℓ n‖ := deficit_le_mul_norm hc (norm_nonneg _)
    have hℓ3 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    have hW : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
    calc (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ ((ℓ ^ 3)⁻¹ * (c * ‖kmomInt ℓ n‖)) * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ hℓ3) hW
      _ = c * ((ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
          ring

/-- The lattice form of the cap `Θ_c` is summable (`Θ_c ≤ c²` against the weight `j = 0`). -/
lemma summable_latThetaSym {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) :
    Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * thetaSym c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
  have hm : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    simpa using summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 0
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hm.mul_left (c ^ 2))
  · rw [thetaSym]
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (sq_nonneg _)
  · have hΘ : thetaSym c ‖kmomInt ℓ n‖ ≤ c ^ 2 := thetaSym_le_sq hc (norm_nonneg _)
    have hℓ3 : (0:ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
    have hW : (0:ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
    calc (ℓ ^ 3)⁻¹ * thetaSym c ‖kmomInt ℓ n‖ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        ≤ ((ℓ ^ 3)⁻¹ * c ^ 2) * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΘ hℓ3) hW
      _ = c ^ 2 * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by ring

/-- **Linearity of the lattice sum** (the only "infinite sum" ingredient): if `f + h` agrees
pointwise with `p + (c·s − A·m)` and all five families are summable, then the sums add up. -/
lemma tsum_ledger_linear {ι : Type*} {c A : ℝ} {f h p s m : ι → ℝ} (hf : Summable f)
    (hh : Summable h) (hp : Summable p) (hs : Summable s) (hm : Summable m)
    (hpt : ∀ n, f n + h n = p n + (c * s n - A * m n)) :
    (∑' n, f n) + (∑' n, h n) = (∑' n, p n) + c * (∑' n, s n) - A * (∑' n, m n) := by
  have hcs : Summable fun n => c * s n := hs.mul_left c
  have hAm : Summable fun n => A * m n := hm.mul_left A
  calc (∑' n, f n) + (∑' n, h n)
      = ∑' n, (f n + h n) := (hf.tsum_add hh).symm
    _ = ∑' n, (p n + (c * s n - A * m n)) := tsum_congr hpt
    _ = (∑' n, p n) + ∑' n, (c * s n - A * m n) := hp.tsum_add (hcs.sub hAm)
    _ = (∑' n, p n) + ((∑' n, c * s n) - (∑' n, A * m n)) := by rw [hcs.tsum_sub hAm]
    _ = (∑' n, p n) + (c * (∑' n, s n) - A * (∑' n, m n)) := by rw [tsum_mul_left, tsum_mul_left]
    _ = (∑' n, p n) + c * (∑' n, s n) - A * (∑' n, m n) := by ring

/-- **(★₀)**: the sum of the deficit and the cap equals the convexity defect plus `c·S₁` minus
`(5/4+c₀)c²·L(1)`. -/
lemma latDeficit_add_latTheta {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    latDeficit ℓ c g
      + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * thetaSym c ‖kmomInt ℓ n‖
          * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      = (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
          * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        + c * tauLatPow ℓ 1 g
        - (5 / 4 + tauC0phi) * c ^ 2
            * (((2 * Real.pi) ^ 3)⁻¹
              * ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hsd := summable_latDeficit hℓ hc hg hgc
  have hst := summable_latThetaSym hℓ hc hg hgc
  have hsp : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := tauPsiLatticeSummable hℓ hc hg hgc
  have hss : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    simpa using summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 1
  have hsm : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2) := by
    simpa using summable_lattice_kinFT_weight (ℓ := ℓ) hℓ hg hgc 0
  have hkey := tsum_ledger_linear (c := c) (A := (5 / 4 + tauC0phi) * c ^ 2)
    (f := fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
    (h := fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * thetaSym c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
    (p := fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
    (s := fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
    (m := fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
    hsd hst hsp hss hsm (by intro n; rw [tauPsi_eq_deficit_add_thetaSym]; ring)
  have hS1 : tauLatPow ℓ 1 g = ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := by
    rw [tauLatPow]
    exact tsum_congr (fun n => by rw [pow_one])
  have hframe : (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2 :=
    (deficit_inputs hℓ hc hg hgc hgsupp).1
  rw [hframe] at hkey
  rw [latDeficit, hS1]
  exact hkey

/-- **The canonical ledger identity `(★)`, correctly parenthesised**:

    latDeficit + lowGain − 2c(R₁ − S₁) = c(3S₁ − 2R₁) + L(Ψ_c) − C(Θ_c) − (5/4+c₀)c²R₀ .

This is the statement of `Work.BoseBoxFock.ledger_eq_deficitForm` with the *first* integral of the
right-hand side parenthesised (the unparenthesised text parses with the trailing
`- (5/4+c₀)c²R₀` inside the integrand, which makes it false — see the module docstring of
`Submission/Work/BoseBoxFock/ledger_eq_deficitForm.lean`). -/
theorem ledger_eq_deficitForm_paren {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    latDeficit ℓ c g + lowGain ℓ c g - 2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g)
      = c * (3 * tauLatPow ℓ 1 g - 2 * tauContPow 1 g)
        + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
            * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        - ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
        - (5 / 4 + tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : E3, ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hcore := latDeficit_add_latTheta hℓ hc hg hgc (hgsupp.trans Metric.ball_subset_closedBall)
  have hΘ : (∫ p : E3, tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      = ∫ p : E3, thetaSym c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with p
    rw [thetaSym_eq_tauTheta]
  rw [hΘ, lowGain]
  linear_combination hcore

end Work.BoseBoxFock
