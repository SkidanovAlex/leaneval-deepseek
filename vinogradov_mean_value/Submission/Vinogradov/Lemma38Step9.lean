/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.UniformConst
import Submission.Vinogradov.Lemma38Step7
import Submission.Vinogradov.Lemma38Split

/-!
# GLYZ Lemma 3.8, steps 1-5: the fused bound

The first half of the assembly of `AsymDecFine` (GLYZ (3.10) / Lemma 3.8).  Starting from the
moving-ball form of `asymLHS` (`Lemma38Step1.asymLHS_eq_movingBall`), the chain is

1. the sup comparison on the `H`-ball (`Lemma38Step2.asymLHS_le_supMoving`);
2. the convolution swap (`Lemma38Step3.asymC1_movingBall_swap`), which lifts the ball average onto
   the plate bump `Φ_I` and produces the ball average `AV (z − t)`;
3. the localised decoupling on each translate (`exists_AV_bound`, which is lane 4
   `UniformConst.asymAV_le_proj_explicit` with the level-gap split against the trivial bound
   `Lemma38Split.asymAV_le_trivial`);
4. the fusion of the `(z,t)` double integral into the weight `W t = ∫⁻ z, C2 z · Φ_I (z − t)`
   (`AsymFineProof.lintegral_swap_refl`).

The result is **`asymLHS_le_fused`**: `asymLHS ≤ C · ∫⁻ t, W t · S t`, where `S` is the `ℓ²`-sum of
the ball-tent norms of the level-`M` sub-block sums.  The remaining work (weighted Minkowski plus
the per-sub-block bound `Lemma38Step7.lintegral_W_mul_tentNorm_le`) turns this into `AsymDecFine`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- **The `H`-ball average of the coarse block sum is bounded by the `ℓ²`-sum of the ball-tent
norms of its sub-block sums** (lane 4 with the level-gap split handled). -/
theorem exists_AV_bound {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ Cloc : ℝ≥0∞, ∀ u : E k,
      (∫⁻ w in Metric.ball (0 : E l) (hBallR k l m'),
          (‖∑ i ∈ blkFin N m q,
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
        ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) (hBallR k l m'))).toReal)
          * Cloc ^ (plExp l)
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 (hBallR k l m') (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
  have hA0 : (0 : ℝ) ≤ A := by
    have h1 : (0 : ℝ) ≤ gaugeExp k + (l : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k,
      (gaugeExp_gt hk : (k : ℝ) < gaugeExp k), Nat.cast_nonneg (α := ℝ) l]
    linarith [hAge]
  by_cases hgap : laneK k l hk hl hlk ≤ M - m
  · have hlam2 : 2 * laneLam k l hk hl hlk ≤ (2 : ℝ) ^ (M - m) :=
      laneK_spec k l hk hl hlk hgap
    exact asymAV_le_proj_explicit hk hl hlk h2m hmM hMN hξ' q hsepI hsep hM h4 hlam2
      ha1 hεm hA0 hm hf le_rfl hmMod
  · refine ⟨(((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2), fun u => ?_⟩
    have h := asymAV_le_trivial (m' := m') (ξ' := ξ') (u := u) (r := hBallR k l m') (A := A)
      hl hlk hmM hMN q hA0 hr0 hfm
    refine h.trans ?_
    have hp : ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) ^ (plExp l)
        = ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞)) ^ (plExp l / 2) := by
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have hcard' : ((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2)
        ≤ ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) ^ (plExp l) := by
      rw [hp]
      exact ENNReal.rpow_le_rpow (by exact_mod_cast card_subBlkLvl_le m M hmM q)
        (by have := plExp_pos hl; linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard' bot_le) bot_le

/-- **Measurability of the `ℓ²`-sum of ball-tent norms** in the translate variable. -/
lemma measurable_asymS {k l : ℕ} (hk : 1 ≤ k) (hlk : l ≤ k) {N m M : ℕ}
    (q : Fin (2 ^ m)) {ξ' A r : ℝ} {f : Fin (2 ^ N) → E k → ℂ}
    (hfm : ∀ i, Measurable (f i)) :
    Measurable (fun u : E k => (∑ J ∈ subBlkLvl m M q,
        (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
          f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
      ^ (plExp l / 2)) := by
  have hTN : ∀ J : Fin (2 ^ M), Measurable (fun u : E k => tentNorm l A 0 r
      (fun y : E l => ∑ i ∈ blkFin N M J,
        f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) := by
    intro J
    unfold tentNorm
    refine Measurable.lintegral_prod_right ?_
    have h1 : Measurable (fun p : E k × E l =>
        ((‖∑ i ∈ blkFin N M J,
          f i (p.1 + projEmbedLin k l (torsionVec k l hlk ξ') p.2)‖₊ : ℝ≥0∞))) := by
      refine Measurable.coe_nnreal_ennreal ?_
      refine Measurable.nnnorm ?_
      exact Finset.measurable_sum _ fun i _ => (hfm i).comp (by fun_prop)
    exact h1.pow_const _ |>.mul (measurable_ballTent l A 0 r |>.comp measurable_snd)
  exact (Finset.measurable_sum _ fun J _ => (hTN J).pow_const _).pow_const _

theorem asymLHS_le_fused {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
    (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, asymLHS k hk l N m m' q q' f ≤ C * ∫⁻ t : E k,
        (∫⁻ z : E k, asymC2 k hk l N m' q' f z
            * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t))
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 (hBallR k l m') (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
  have hA0 : (0 : ℝ) ≤ A := by
    have h1 : (0 : ℝ) ≤ gaugeExp k + (l : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k,
      (gaugeExp_gt hk : (k : ℝ) < gaugeExp k), Nat.cast_nonneg (α := ℝ) l]
    linarith [hAge]
  obtain ⟨Cloc, hAV⟩ := exists_AV_bound hk hl hlk h2m hmM hMN hM h4 hm hξ' q hsepI hsep
    ha1 hεm hAge hf hmMod
  obtain ⟨Csup, hCsup0, hsup⟩ := asymLHS_le_supMoving (hk := hk) (hl := hl) (hlk := hlk)
    q q' hξ' hr0 le_rfl hsep' hfm
  set S : E k → ℝ≥0∞ := (fun u : E k => (∑ J ∈ subBlkLvl m M q,
      (tentNorm l A 0 (hBallR k l m') (fun y : E l => ∑ i ∈ blkFin N M J,
        f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
    ^ (plExp l / 2)) with hS
  set AV : E k → ℝ≥0∞ := (fun u : E k => ∫⁻ w in Metric.ball (0 : E l) (hBallR k l m'),
      (‖∑ i ∈ blkFin N m q,
        f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l)) with hAVdef
  set Bv : ℝ≥0∞ := ENNReal.ofReal ((volume (Metric.ball (0 : E l) (hBallR k l m'))).toReal)
    with hBv
  have hSm : Measurable S := by
    rw [hS]
    exact measurable_asymS hk hlk q (ξ' := ξ') (A := A) (r := hBallR k l m') hfm
  have hΦIm : Measurable (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) :=
    (continuous_platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)).measurable
  have hC2m : Measurable (asymC2 k hk l N m' q' f) := measurable_asymC2 k hk l N m' q' hfm
  have hBv0 : Bv ≠ 0 := by
    rw [hBv, ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) 0 hr0).ne'
      (measure_ball_lt_top (μ := volume)).ne
  have hBvtop : Bv ≠ ⊤ := by rw [hBv]; exact ENNReal.ofReal_ne_top
  have hXmeas : Measurable (fun z : E k => ∫⁻ t : E k,
      platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t)) := by
    refine Measurable.lintegral_prod_right ?_
    exact (hΦIm.comp measurable_snd).mul (hSm.comp (measurable_fst.sub measurable_snd))
  -- (a) pull the constants out of the `t`-integral
  have hA1 : ∀ z : E k, (∫⁻ t : E k,
        platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
          * (Bv * Cloc ^ (plExp l) * S (z - t)))
      = Bv * Cloc ^ (plExp l) * ∫⁻ t : E k,
          platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t) := by
    intro z
    rw [show (fun t : E k => platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
          * (Bv * Cloc ^ (plExp l) * S (z - t)))
        = fun t : E k => (Bv * Cloc ^ (plExp l))
          * (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t)) from by
      funext t; ring]
    exact lintegral_const_mul _ (hΦIm.mul (hSm.comp (measurable_const.sub measurable_id)))
  -- the algebra + fusion
  have hkey : (∫⁻ z : E k, Bv⁻¹ * (∫⁻ t : E k,
        platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
          * (Bv * Cloc ^ (plExp l) * S (z - t))) * asymC2 k hk l N m' q' f z)
      = Cloc ^ (plExp l) * ∫⁻ t : E k, (∫⁻ z : E k,
          asymC2 k hk l N m' q' f z
            * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t)) * S t := by
    have h1 : (∫⁻ z : E k, Bv⁻¹ * (∫⁻ t : E k,
          platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
            * (Bv * Cloc ^ (plExp l) * S (z - t))) * asymC2 k hk l N m' q' f z)
        = ∫⁻ z : E k, Cloc ^ (plExp l)
            * ((∫⁻ t : E k, platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
                * S (z - t)) * asymC2 k hk l N m' q' f z) := by
      refine lintegral_congr fun z => ?_
      rw [hA1 z]
      rw [show Bv⁻¹ * (Bv * Cloc ^ (plExp l) * (∫⁻ t : E k,
            platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t)))
            * asymC2 k hk l N m' q' f z
          = (Bv⁻¹ * Bv) * (Cloc ^ (plExp l) * ((∫⁻ t : E k,
              platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t))
              * asymC2 k hk l N m' q' f z)) from by ring]
      rw [ENNReal.inv_mul_cancel hBv0 hBvtop, one_mul]
    have h2 : (∫⁻ z : E k, Cloc ^ (plExp l)
          * ((∫⁻ t : E k, platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
              * S (z - t)) * asymC2 k hk l N m' q' f z))
        = Cloc ^ (plExp l) * ∫⁻ z : E k,
            (∫⁻ t : E k, platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t))
              * asymC2 k hk l N m' q' f z :=
      lintegral_const_mul _ (hXmeas.mul hC2m)
    have h3 : (∫⁻ z : E k,
            (∫⁻ t : E k, platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t))
              * asymC2 k hk l N m' q' f z)
        = ∫⁻ t : E k, (∫⁻ z : E k, asymC2 k hk l N m' q' f z
            * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t)) * S t := by
      rw [show (fun z : E k => (∫⁻ t : E k,
            platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * S (z - t))
            * asymC2 k hk l N m' q' f z)
          = fun z : E k => asymC2 k hk l N m' q' f z
            * (∫⁻ t : E k, platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
                * S (z - t)) from by funext z; ring]
      exact lintegral_swap_refl hC2m hΦIm hSm
    exact h1.trans (h2.trans (congrArg (fun w => Cloc ^ (plExp l) * w) h3))
  -- the chain
  have hstep2 : (∫⁻ z : E k, Bv⁻¹ * (∫⁻ w in Metric.ball (0 : E l) (hBallR k l m'),
        asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
        * asymC2 k hk l N m' q' f z)
      = ∫⁻ z : E k, Bv⁻¹ * (∫⁻ t : E k,
          platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * AV (z - t))
        * asymC2 k hk l N m' q' f z := by
    refine lintegral_congr fun z => ?_
    rw [asymC1_movingBall_swap (hk := hk) (hlk := hlk) (q := q) (r := hBallR k l m')
      (ξ' := ξ') hr0 z hfm]
  have hstep3 : (∫⁻ z : E k, Bv⁻¹ * (∫⁻ t : E k,
        platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t * AV (z - t))
        * asymC2 k hk l N m' q' f z)
      ≤ ∫⁻ z : E k, Bv⁻¹ * (∫⁻ t : E k,
          platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) t
            * (Bv * Cloc ^ (plExp l) * S (z - t)))
        * asymC2 k hk l N m' q' f z := by
    refine lintegral_mono fun z => ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ bot_le) bot_le
    exact lintegral_mono fun t => mul_le_mul' le_rfl (hAV (z - t))
  refine ⟨ENNReal.ofReal Csup * Cloc ^ (plExp l), ?_⟩
  refine hsup.trans ?_
  refine (mul_le_mul_of_nonneg_left ?_ bot_le).trans (le_of_eq (mul_assoc _ _ _).symm)
  exact (le_of_eq hstep2).trans (hstep3.trans (le_of_eq hkey))

end Submission.Vinogradov
