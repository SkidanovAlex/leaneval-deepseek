/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymFineProof
import Submission.Vinogradov.Lemma38Step4
import Submission.Vinogradov.UncertaintyBlock

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ Lemma 3.8, steps 7 and 8: the removal of the `H`-ball average and the tent comparison

Lanes 7 and 8 of the §3.4 chain, combined into the **per-sub-block bound**.  For every level-`M`
sub-block `J` of the coarse block `q`, the `(z,t)`-fused weight

  `W t = ∫⁻ z, C2 z · Φ_I (z − t)`  (`C2 = asymC2`, `Φ_I` the level-`m` plate bump)

against the ball-tent norm of the sub-block sum `G_J = ∑_{i ∈ blkFin N M J} f_i` is bounded by the
bilinear expression at level `M`:

  `∫⁻ t, W t · tentNorm l A 0 r (fun y => G_J (t + Ψ y))
     ≤ C · asymLHS k hk l N M m' J q' f`.

Two ingredients:

* `asymC2_shift_le` — the `I'`-factor is comparable under the shifts `z ↦ z − Ψ w` with the
  *isotropic polynomial* growth `(1 + C₀‖w‖/r)^{gaugeExp k}` (from the isotropy of the plate gauge,
  `AsymFine.gauge_plateGaugeLin_projEmbed_le_norm`, fed into the abstract
  `convPow_platePhi_shift_ge`);
* `AsymFineProof.lintegral_ballTent_shift_le'` — with that growth bound the `H`-ball average can be
  removed at the price of the weighted mass of the tent (finite exactly because the tent exponent
  `A` exceeds `gaugeExp k + l`); then `AsymFineProof.lintegral_W_mul_eq` identifies the result with
  `∫⁻ z, C2 z · (|G_J|^{p_l} ∗ Φ_I)(z)`, and **Lemma A.1** (`TentCompare.convPow_platePhi_le_of_plate`)
  replaces `Φ_I` by `Φ_J`.
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

/-- **The reverse shift comparison inside a `convPow`.**  If the gauge of `h` in the plate
coordinates is at most `ρ`, then convolving with the plate bump at `x` costs at most
`(1+ρ)^{gaugeExp k}` compared with the bump at `x + h`. -/
lemma convPow_platePhi_shift_ge {k : ℕ} (hk : 1 ≤ k) (δ c : ℝ) (s : ℝ) (F : E k → ℂ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {x h : E k}
    (hh : gauge k hk (plateGaugeLin k δ c h) ≤ ρ) :
    convPow k s F (platePhi k hk δ c) x
      ≤ ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
          * convPow k s F (platePhi k hk δ c) (x + h) := by
  have h0 : (0 : ℝ) ≤ (1 + ρ) ^ gaugeExp k := Real.rpow_nonneg (by linarith) _
  rw [convPow_eq_lintegral_sub, convPow_eq_lintegral_sub]
  have hshift : ∀ t : E k, platePhi k hk δ c (x - t)
      ≤ ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk δ c ((x + h) - t) := by
    intro t
    have h1 := platePhi_shift_ge_of_gauge hk δ c hρ hh (x := x - t) (h := h)
    rwa [show (x - t) + h = (x + h) - t from by abel] at h1
  have hcongr : (∫⁻ t : E k, ((‖F t‖₊ : ℝ≥0∞) ^ s)
        * (ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk δ c ((x + h) - t)))
      = ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
        * ∫⁻ t : E k, ((‖F t‖₊ : ℝ≥0∞) ^ s) * platePhi k hk δ c ((x + h) - t) := by
    rw [show (fun t : E k => ((‖F t‖₊ : ℝ≥0∞) ^ s)
          * (ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk δ c ((x + h) - t)))
        = fun t : E k => ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
          * (((‖F t‖₊ : ℝ≥0∞) ^ s) * platePhi k hk δ c ((x + h) - t)) from by
      funext t; ring]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine (lintegral_mono fun t => mul_le_mul' le_rfl (hshift t)).trans (le_of_eq hcongr)

/-- **The `I'`-factor is polynomially comparable on the `H`-ball, with the isotropic growth
`(1 + C₀‖w‖/r)^A`.**  This is the form of the sup comparison that the removal of the `H`-ball
average needs (the ball tent decays faster than this polynomial grows). -/
theorem asymC2_shift_le {k l N m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q' : Fin (2 ^ m'))
    (hsep : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    {r : ℝ} (hr : 0 < r) (hrh : r ≤ hBallR k l m')
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (z : E k) (w : E l),
      asymC2 k hk l N m' q' f (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ gaugeExp k)
            * asymC2 k hk l N m' q' f z := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := gauge_plateGaugeLin_projEmbed_le_norm hk hlk hξ'
  refine ⟨C₀, hC₀0, ?_⟩
  intro z w
  have hpc : pieceCenter (2 ^ m') q' ∈ Set.Icc (0 : ℝ) 1 :=
    pieceCenter_mem_Icc (2 ^ m') Nat.one_le_two_pow q'
  have hδ0 : 0 < plateHalf m' := plateHalf_pos m'
  have hδr : (plateHalf m') ^ (k - l + 1) * hBallR k l m' = 1 := by
    rw [hBallR, inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hδ0))
  have hρw : gauge k hk (plateGaugeLin k (plateHalf m') (pieceCenter (2 ^ m') q')
      (projEmbedLin k l (torsionVec k l hlk ξ') w)) ≤ C₀ * ‖w‖ / r := by
    refine (hC₀ m' _ hpc hsep w).trans ?_
    have hinv : (hBallR k l m')⁻¹ = (plateHalf m') ^ (k - l + 1) :=
      inv_eq_of_mul_eq_one_left hδr
    have h1 : C₀ * (plateHalf m') ^ (k - l + 1) * ‖w‖ = C₀ * ‖w‖ / hBallR k l m' := by
      rw [div_eq_mul_inv, hinv]; ring
    rw [h1]
    exact div_le_div_of_nonneg_left (by positivity) hr hrh
  have hρ0 : 0 ≤ C₀ * ‖w‖ / r := by positivity
  have h := convPow_platePhi_shift_ge hk (plateHalf m') (pieceCenter (2 ^ m') q')
    (pkExp k - plExp l) (fun x : E k => ∑ i ∈ blkFin N m' q', f i x) hρ0 hρw
    (x := z - projEmbedLin k l (torsionVec k l hlk ξ') w)
    (h := projEmbedLin k l (torsionVec k l hlk ξ') w)
  rwa [sub_add_cancel] at h

/-- **The per-`J` bound of GLYZ Lemma 3.8.**  For every level-`M` sub-block `J` of the coarse block
`q`, the `(z,t)`-fused weight of step 5 against the ball-tent norm of the sub-block sum is bounded
by the bilinear expression at level `M` — the removal of the `H`-ball average (step 7) and the tent
comparison (step 8, Lemma A.1) combined. -/
theorem lintegral_W_mul_tentNorm_le {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (hmM : m ≤ M) (hMN : M ≤ N) (h2M : 2 ≤ M)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
    (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    {J : Fin (2 ^ M)} (hJ : J ∈ subBlkLvl m M q)
    {A : ℝ} (hA : gaugeExp k + (l : ℝ) < A)
    {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∫⁻ t : E k, (∫⁻ z : E k, asymC2 k hk l N m' q' f z
          * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t))
        * tentNorm l A 0 (hBallR k l m') (fun y : E l =>
            ∑ i ∈ blkFin N M J,
              f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y)))
      ≤ ENNReal.ofReal C * asymLHS k hk l N M m' J q' f := by
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
  set C2 : E k → ℝ≥0∞ := asymC2 k hk l N m' q' f with hC2def
  set ΦI : E k → ℝ≥0∞ := platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) with hΦIdef
  set G : E k → ℂ := fun y : E k => ∑ i ∈ blkFin N M J, f i y with hGdef
  set H : E k → ℝ≥0∞ := (fun y : E k => ((‖∑ i ∈ blkFin N M J, f i y‖₊ : ℝ≥0∞)) ^ (plExp l))
    with hHdef
  have hC2m : Measurable C2 := measurable_asymC2 k hk l N m' q' hfm
  have hΦIm : Measurable ΦI :=
    (continuous_platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)).measurable
  have hGm : Measurable G := Finset.measurable_sum _ fun i _ => hfm i
  have hHm : Measurable H := (hGm.nnnorm.coe_nnreal_ennreal).pow_const _
  -- (1) the shift bound of the `I'`-factor
  obtain ⟨C₀, hC₀0, hC₀⟩ := asymC2_shift_le hk hl hlk hξ' q' hsep' hr0 le_rfl hfm
  -- (2) the removal of the `H`-ball average
  have hge0 : (0 : ℝ) < gaugeExp k := lt_of_le_of_lt (Nat.cast_nonneg k) (gaugeExp_gt hk)
  obtain ⟨Cr, hCr0, hCr⟩ := lintegral_ballTent_shift_le' (k := k) (l := l) hk hl hlk hξ'
    (A := gaugeExp k) (A' := A) (C₀ := C₀) hge0 hC₀0 hA
  have hstep : (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t))
        * (∫⁻ w : E l, ballTent l A 0 (hBallR k l m') w * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w)))
      ≤ ENNReal.ofReal Cr * ∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t :=
    hCr C2 ΦI H hC2m hΦIm hHm (hBallR k l m') hr0 hC₀
  -- (3) the ball-tent norm is that inner integral
  have hTN : ∀ t : E k, tentNorm l A 0 (hBallR k l m') (fun y : E l =>
        ∑ i ∈ blkFin N M J, f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y))
      = ∫⁻ w : E l, ballTent l A 0 (hBallR k l m') w
          * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w) := by
    intro t
    rw [tentNorm, hHdef]
    exact lintegral_congr fun w => mul_comm _ _
  -- (4) the `L^{p_l}` identification
  have hWu : (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t)
      = ∫⁻ z : E k, C2 z * convPow k (plExp l) G ΦI z := by
    rw [hHdef, hGdef, hC2def, hΦIdef]
    exact lintegral_W_mul_eq (asymC2 k hk l N m' q' f)
      (fun y : E k => ∑ i ∈ blkFin N M J, f i y)
      (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) hC2m hGm hΦIm (plExp l)
  -- (5) the tent comparison (Lemma A.1)
  have hr1 : (1 : ℝ) ≤ plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    nlinarith
  have hδJI : plateHalf M ≤ plateHalf m := by
    rw [plateHalf, plateHalf]
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : m + 1 ≤ M + 1))
  have hδI1 : plateHalf m ≤ 1 := plateHalf_le_one m
  have hcI : pieceCenter (2 ^ m) q ∈ Set.Icc (0 : ℝ) 1 :=
    pieceCenter_mem_Icc (2 ^ m) Nat.one_le_two_pow q
  have hcJ : pieceCenter (2 ^ M) J ∈ Set.Icc (0 : ℝ) 1 :=
    pieceCenter_mem_Icc (2 ^ M) Nat.one_le_two_pow J
  have hcc : |pieceCenter (2 ^ M) J - pieceCenter (2 ^ m) q| ≤ plateHalf m := by
    refine (abs_pieceCenter_subBlkLvl_sub_le (m'' := M) hmM hJ).trans ?_
    have := plateHalf_pos M
    linarith
  have hGcls : IsFourierRep k (plate k (8 * plateHalf M) (pieceCenter (2 ^ M) J)) G := by
    rw [hGdef]
    exact isFourierRep_sum_blkFin hk h2M hMN J f hf
  obtain ⟨CA1, hCA10, hCA1⟩ :=
    convPow_platePhi_le_of_plate hk hr1 (plateHalf_pos M) hδJI hδI1 hcI hcJ hcc hGcls
  -- (6) the two `convPow` factors
  have hfinal : (∫⁻ z : E k, C2 z * convPow k (plExp l) G ΦI z)
      ≤ ENNReal.ofReal CA1 * asymLHS k hk l N M m' J q' f := by
    have hpoint : ∀ x : E k, convPow k (plExp l) G ΦI x
        ≤ ENNReal.ofReal CA1 * convPow k (plExp l) G
            (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) J)) x :=
      fun x => hCA1 x
    calc (∫⁻ z : E k, C2 z * convPow k (plExp l) G ΦI z)
        ≤ ∫⁻ z : E k, C2 z * (ENNReal.ofReal CA1 * convPow k (plExp l) G
            (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) J)) z) :=
          lintegral_mono fun z => mul_le_mul' le_rfl (hpoint z)
      _ = ENNReal.ofReal CA1 * ∫⁻ z : E k, C2 z * convPow k (plExp l) G
            (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) J)) z := by
          rw [show (fun z : E k => C2 z * (ENNReal.ofReal CA1 * convPow k (plExp l) G
                (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) J)) z))
              = fun z : E k => ENNReal.ofReal CA1 * (C2 z * convPow k (plExp l) G
                (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) J)) z) from by
            funext z; ring]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal CA1 * asymLHS k hk l N M m' J q' f := by
          rw [asymLHS_eq_integral]
          congr 1
          refine lintegral_congr fun z => ?_
          rw [hC2def]
          exact mul_comm _ _
  have hA1 : (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t)
      ≤ ENNReal.ofReal CA1 * asymLHS k hk l N M m' J q' f :=
    (le_of_eq hWu).trans hfinal
  refine ⟨Cr * CA1, mul_nonneg hCr0 hCA10, ?_⟩
  refine (le_of_eq (lintegral_congr fun t => by rw [hTN t])).trans ?_
  refine hstep.trans ?_
  refine (mul_le_mul' le_rfl hA1).trans (le_of_eq ?_)
  rw [show ENNReal.ofReal (Cr * CA1) = ENNReal.ofReal Cr * ENNReal.ofReal CA1 from
    ENNReal.ofReal_mul hCr0, mul_assoc]


end Submission.Vinogradov
