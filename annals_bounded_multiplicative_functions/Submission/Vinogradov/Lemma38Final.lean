/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Step9


/-!
# GLYZ Lemma 3.8: the uniform chain (`∀ f`-uniform constants) and `AsymDecFine`

`AsymDecFine` (GLYZ (3.10)) demands a **single** constant for all tuples `f` with
`f i ∈ 𝒞(piecePlate i)`.  The lemmas of the chain are proved *per tuple* (`∃ C, …(f)…`), and a
witness chosen after `f` may depend on `f`; the fix is to prove the chain with the quantifier over
`f` (and over the sub-block index `J`) *inside* the existential.  This module contains those
uniform versions:

* `convPow_platePhi_le_of_plate_uni` — Lemma A.1 in `convPow` form, uniform in the function;
* `asymC2_shift_le_uni` — the polynomial growth bound of the `I'`-factor, uniform in `f`;
* `lintegral_W_mul_tentNorm_le_uni` — steps 7+8 per sub-block, uniform in `J` and `f`;
* `asymAV_le_proj_explicit_uni`, `exists_AV_bound_uni` — lane 4 with the level-gap split, uniform
  in `f`;
* `asymLHS_le_supMoving_uni`, `asymLHS_le_fused_uni` — steps 1–5, uniform in `f`;
* `lintegral_ell2_minkowski_rpow_weighted_finset` — weighted Minkowski in `Finset` form;
* `asymDecFine_pt_uni` — the per-(q,q') `AsymDecFine` step, uniform in `f`;
* **`asymDecFine_of_model`** — the assembly of `AsymDecFine` (a single constant for all `(q,q')`
  and all `f`), using `Finset.sup` over the finite set of block pairs.
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

/-- **GLYZ Lemma A.1 in the `convPow` form, uniformly in the function.** -/
theorem convPow_platePhi_le_of_plate_uni {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ_I δ_J c_I c_J : ℝ) (G : E k → ℂ),
      0 < δ_J → δ_J ≤ δ_I → δ_I ≤ 1 → c_I ∈ Set.Icc (0 : ℝ) 1 →
      c_J ∈ Set.Icc (0 : ℝ) 1 → |c_J - c_I| ≤ δ_I →
      IsFourierRep k (plate k (8 * δ_J) c_J) G →
      ∀ x : E k,
        convPow k r G (platePhi k hk δ_I c_I) x
          ≤ ENNReal.ofReal C * convPow k r G (platePhi k hk δ_J c_J) x := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hrpow0 : 0 ≤ r - 1 := by linarith
  set K : ℝ := (gaugeAmp k hk * ∫ z, (max 1 (gauge k hk z)) ^ (-(gaugeExp k))) ^ (r - 1)
    with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact Real.rpow_nonneg (mul_nonneg (gaugeAmp_pos k hk).le
      (integral_nonneg fun z => Real.rpow_nonneg
        (le_trans zero_le_one (le_max_left (1:ℝ) _)) _)) _
  have hKunc : (uncConst k hk) ^ (r - 1) = ENNReal.ofReal K := by
    rw [hKdef]
    have hI : (0:ℝ) ≤ ∫ z, (max 1 (gauge k hk z)) ^ (-(gaugeExp k)) :=
      integral_nonneg fun z => Real.rpow_nonneg
        (le_trans zero_le_one (le_max_left (1:ℝ) _)) _
    rw [uncConst, ← ENNReal.ofReal_mul (gaugeAmp_pos k hk).le]
    exact ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (gaugeAmp_pos k hk).le hI) hrpow0
  obtain ⟨CA, hCA0, hCA⟩ := platePhi_conv_le k hk
  refine ⟨K * (8 : ℝ) ^ (k * (k + 1) / 2) * CA, by positivity, ?_⟩
  intro δ_I δ_J c_I c_J G hδJ hJI hI1 hcI hcJ hcc hG x
  have hδP0 : 0 < 8 * δ_J := by linarith
  have hP : ∀ z : E k, ((‖G z‖₊ : NNReal) : ℝ≥0∞) ^ r
      ≤ ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
        * convPow k r G (platePhi k hk δ_J c_J) z := by
    intro z
    refine (norm_rpow_le_convPow_of_isFourierRep hk hδJ hG hr z).trans (le_of_eq ?_)
    rw [hKunc, ← ENNReal.ofReal_mul hK0]
  have hH : Measurable (fun z : E k => ((‖G z‖₊ : NNReal) : ℝ≥0∞) ^ r) :=
    (((hG.continuous.nnnorm).measurable).coe_nnreal_ennreal).pow_const r
  have hmono : convPow k r G (platePhi k hk δ_I c_I) x
      ≤ ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
        * ∫⁻ u : E k, convPow k r G (platePhi k hk δ_J c_J) (x - u)
            * platePhi k hk δ_I c_I u := by
    rw [convPow]
    have hcongr : (∫⁻ u : E k, (ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * convPow k r G (platePhi k hk δ_J c_J) (x - u)) * platePhi k hk δ_I c_I u)
        = ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * ∫⁻ u : E k, convPow k r G (platePhi k hk δ_J c_J) (x - u)
              * platePhi k hk δ_I c_I u := by
      rw [show (fun u : E k => (ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
            * convPow k r G (platePhi k hk δ_J c_J) (x - u)) * platePhi k hk δ_I c_I u)
          = fun u : E k => ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
            * (convPow k r G (platePhi k hk δ_J c_J) (x - u)
                * platePhi k hk δ_I c_I u) from by funext u; ring]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    exact (lintegral_mono fun u => mul_le_mul' (hP (x - u)) le_rfl).trans (le_of_eq hcongr)
  refine hmono.trans ?_
  have hL := lintegral_convPow_le_of_conv_le (k := k)
    (hΦ₁ := (continuous_platePhi k hk δ_I c_I).measurable)
    (hΦ₂ := (continuous_platePhi k hk δ_J c_J).measurable)
    (C := CA) (hC := fun y => hCA δ_I δ_J c_I c_J y hδJ hJI hI1 hcI hcJ hcc)
    (H := fun z => ((‖G z‖₊ : NNReal) : ℝ≥0∞) ^ r) hH x
  rw [show (∫⁻ w : E k, ((‖G (x - w)‖₊ : NNReal) : ℝ≥0∞) ^ r
        * platePhi k hk δ_J c_J w) = convPow k r G (platePhi k hk δ_J c_J) x from rfl] at hL
  have hconst : ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
        * (ENNReal.ofReal CA * convPow k r G (platePhi k hk δ_J c_J) x)
      = ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2) * CA)
        * convPow k r G (platePhi k hk δ_J c_J) x := by
    rw [show ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * (ENNReal.ofReal CA * convPow k r G (platePhi k hk δ_J c_J) x)
        = (ENNReal.ofReal (K * (8 : ℝ) ^ (k * (k + 1) / 2))
          * ENNReal.ofReal CA) * convPow k r G (platePhi k hk δ_J c_J) x from by ring]
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ K * (8 : ℝ) ^ (k * (k + 1) / 2))]
  exact (mul_le_mul' le_rfl hL).trans (le_of_eq hconst)


/-- **The polynomial growth bound of the `I'`-factor, uniformly in the function.** -/
theorem asymC2_shift_le_uni {k l N m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q' : Fin (2 ^ m'))
    (hsep : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    {r : ℝ} (hr : 0 < r) (hrh : r ≤ hBallR k l m') :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (f : Fin (2 ^ N) → E k → ℂ) (z : E k) (w : E l),
      asymC2 k hk l N m' q' f (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ gaugeExp k)
            * asymC2 k hk l N m' q' f z := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := gauge_plateGaugeLin_projEmbed_le_norm hk hlk hξ'
  refine ⟨C₀, hC₀0, ?_⟩
  intro f z w
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

theorem lintegral_W_mul_tentNorm_le_uni {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (hmM : m ≤ M) (hMN : M ≤ N) (h2M : 2 ≤ M)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
    (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    {A : ℝ} (hA : gaugeExp k + (l : ℝ) < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Fin (2 ^ M)), J ∈ subBlkLvl m M q →
      ∀ (f : Fin (2 ^ N) → E k → ℂ), (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      (∫⁻ t : E k, (∫⁻ z : E k, asymC2 k hk l N m' q' f z
          * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t))
        * tentNorm l A 0 (hBallR k l m') (fun y : E l =>
            ∑ i ∈ blkFin N M J,
              f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y)))
      ≤ ENNReal.ofReal C * asymLHS k hk l N M m' J q' f := by
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
  have hr1 : (1 : ℝ) ≤ plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    nlinarith
  obtain ⟨CA1, hCA10, hCA1⟩ := convPow_platePhi_le_of_plate_uni (k := k) hk hr1
  obtain ⟨C₀, hC₀0, hC₀⟩ := asymC2_shift_le_uni hk hl hlk hξ' q' hsep' hr0 le_rfl
  have hge0 : (0 : ℝ) < gaugeExp k := lt_of_le_of_lt (Nat.cast_nonneg k) (gaugeExp_gt hk)
  obtain ⟨Cr, hCr0, hCr⟩ := lintegral_ballTent_shift_le' (k := k) (l := l) hk hl hlk hξ'
    (A := gaugeExp k) (A' := A) (C₀ := C₀) hge0 hC₀0 hA
  refine ⟨Cr * CA1, mul_nonneg hCr0 hCA10, fun J hJ f hf => ?_⟩
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
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
  have hC₀' : ∀ (z : E k) (w : E l),
      C2 (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / hBallR k l m') ^ gaugeExp k) * C2 z :=
    fun z w => hC₀ f z w
  have hstep : (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t))
        * (∫⁻ w : E l, ballTent l A 0 (hBallR k l m') w * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w)))
      ≤ ENNReal.ofReal Cr * ∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t :=
    hCr C2 ΦI H hC2m hΦIm hHm (hBallR k l m') hr0 hC₀'
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
  -- (6) the two `convPow` factors
  have hfinal : (∫⁻ z : E k, C2 z * convPow k (plExp l) G ΦI z)
      ≤ ENNReal.ofReal CA1 * asymLHS k hk l N M m' J q' f := by
    have hpoint : ∀ x : E k, convPow k (plExp l) G ΦI x
        ≤ ENNReal.ofReal CA1 * convPow k (plExp l) G
            (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) J)) x :=
      fun x => hCA1 (plateHalf m) (plateHalf M) (pieceCenter (2 ^ m) q)
        (pieceCenter (2 ^ M) J) G (plateHalf_pos M) hδJI hδI1 hcI hcJ hcc hGcls x
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
  refine (le_of_eq (lintegral_congr fun t => by rw [hTN t])).trans ?_
  refine hstep.trans ?_
  refine (mul_le_mul_of_nonneg_left hA1
    (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal Cr)).trans ?_
  rw [show ENNReal.ofReal (Cr * CA1) = ENNReal.ofReal Cr * ENNReal.ofReal CA1 from
    ENNReal.ofReal_mul hCr0, mul_assoc]


/-- **Lane 4 at the fixed enlargement `laneLam`, uniformly in the tuple.** -/
theorem asymAV_le_proj_explicit_uni {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m))
    (hlam2 : 2 * laneLam k l hk hl hlk ≤ (2 : ℝ) ^ (M - m))
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hA : 0 ≤ A)
    (hm : 1 ≤ m)
    {r : ℝ} (hrR : hBallR k l m' ≤ r)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, ∀ (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) → ∀ u : E k,
      (∫⁻ w in Metric.ball (0 : E l) r,
          (‖∑ i ∈ blkFin N m q,
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
        ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * C ^ (plExp l)
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  have hcL : 0 < projCL k l hl hlk := projCL_pos k l hl hlk
  have hR : 0 < projRR k l hl hlk := projRR_pos k l hl hlk
  have hplate := (projConstants_spec k l hl hlk ξ' hξ').1
  have htay := (projConstants_spec k l hl hlk ξ' hξ').2
  have hcast : (((2 ^ (M - m) : ℕ)) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
  have hρ : (2 : ℝ) ^ (l + 2) ≤ projCL k l hl hlk * (1 / (2 : ℝ) ^ m) ^ l
      * (hBallR k l m' / (((2 ^ (M - m) : ℕ)) : ℝ) ^ l) * (laneLam k l hk hl hlk) ^ l := by
    rw [hcast]
    exact hρlR_mono hl hlk hcL hmM hM (lamProj_le_laneLam k l hk hl hlk)
  have hge : (((2 ^ (M - m) : ℕ)) : ℝ) ^ l ≤ hBallR k l m' := hBallR_ge_pow (l := l) hM
  have hmMod' : ∀ M' : ℕ, 1 ≤ M' →
      DecLinScale l M' (towerEnlP l (projCL k l hl hlk) (projRR k l hl hlk)
        (2 * laneLam k l hk hl hlk)) (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm)) := hmMod
  obtain ⟨C, hdec⟩ := curveDecLocR_intervalCurve_proj hl hlk hξ' hcL hR hplate htay
    ha1 hεm (one_le_laneLam k l hk hl hlk) hm hmM h4 q hsepI hlam2 hge hρ hA hmMod'
  refine ⟨C, fun f hf u => ?_⟩
  have hclass := classCB_spec k l hk hl hlk ξ' hξ' h2m hmM hMN q hsep
    (classCB_le_laneLam k l hk hl hlk) u f hf
  exact asymAV_le_curveDecLocR hl hlk hmM hMN q (u := u) hA hrR hdec hclass

/-- **The `H`-ball average bound with the level-gap split, uniformly in the tuple.** -/
theorem exists_AV_bound_uni {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ Cloc : ℝ≥0∞, ∀ (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) → ∀ u : E k,
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
  have hA0 : (0 : ℝ) ≤ A := by
    have h1 : (0 : ℝ) ≤ gaugeExp k + (l : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k,
      (gaugeExp_gt hk : (k : ℝ) < gaugeExp k), Nat.cast_nonneg (α := ℝ) l]
    linarith [hAge]
  by_cases hgap : laneK k l hk hl hlk ≤ M - m
  · have hlam2 : 2 * laneLam k l hk hl hlk ≤ (2 : ℝ) ^ (M - m) :=
      laneK_spec k l hk hl hlk hgap
    exact asymAV_le_proj_explicit_uni hk hl hlk h2m hmM hMN hξ' q hsepI hsep hM h4 hlam2
      ha1 hεm hA0 hm le_rfl hmMod
  · refine ⟨(((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2), fun f hf u => ?_⟩
    have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
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

/-- **Step 2 of Lemma 3.8, uniformly in the tuple.** -/
theorem asymLHS_le_supMoving_uni {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) {ξ' r : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
    (hr : 0 < r) (hrh : r ≤ hBallR k l m')
    (hsep : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fin (2 ^ N) → E k → ℂ), (∀ i, Measurable (f i)) →
      asymLHS k hk l N m m' q q' f
        ≤ ENNReal.ofReal C * ∫⁻ z : E k,
            (ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal))⁻¹ *
            (∫⁻ w in Metric.ball (0 : E l) r,
              asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
            * asymC2 k hk l N m' q' f z := by
  obtain ⟨Csup, hCsup0, hCsup⟩ :=
    convPow_platePhi_shift_le (k := k) (l := l) hk hl hlk hξ' (pkExp k - plExp l)
  have hpc : pieceCenter (2 ^ m') q' ∈ Set.Icc (0 : ℝ) 1 :=
    pieceCenter_mem_Icc (2 ^ m') Nat.one_le_two_pow q'
  refine ⟨Csup, hCsup0, fun f hf => ?_⟩
  have hC : ∀ z w, w ∈ Metric.ball (0 : E l) r →
      asymC2 k hk l N m' q' f (z + projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal Csup * asymC2 k hk l N m' q' f z := by
    intro z w hw
    have hw' : ‖w‖ ≤ hBallR k l m' := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      linarith
    exact hCsup m' (pieceCenter (2 ^ m') q') hpc hsep
      (fun x : E k => ∑ i ∈ blkFin N m' q', f i x) z w hw'
  have hcore := Commons.Measure.Integral.lintegral_mul_le_moving_ball k l
    (projEmbedLin k l (torsionVec k l hlk ξ'))
    (norm_projEmbedLin_eq (orthonormal_torsionVec k l hlk ξ')) hr
    (asymC1 k hk l N m q f) (asymC2 k hk l N m' q' f)
    (measurable_asymC1 k hk l N m q hf).aemeasurable
    (measurable_asymC2 k hk l N m' q' hf).aemeasurable hC
  rw [asymLHS_eq_integral]
  exact hcore

/-! ## Weighted Minkowski in the `Finset` form -/

/-- **Minkowski's `L^pℓ² ≤ ℓ²L^p` inequality with a weight, `Finset`-indexed.**  This is
`AsymFineProof.lintegral_ell2_minkowski_rpow_weighted` with the index set replaced by a `Finset`,
obtained by applying the unweighted `Finset` version to `μ.withDensity W`. -/
theorem lintegral_ell2_minkowski_rpow_weighted_finset {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {W : α → ℝ≥0∞} (hW : AEMeasurable W μ)
    {ι : Type*} (s : Finset ι) {p : ℝ} (hp : 2 ≤ p) (f : ι → α → ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) μ) :
    (∫⁻ x, W x * (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ) ^ (1 / p)
      ≤ (∑ i ∈ s, (∫⁻ x, W x * (f i x) ^ p ∂μ) ^ (2 / p)) ^ ((1 : ℝ) / 2) := by
  have hcore := Commons.Measure.Integral.lintegral_ell2_minkowski_rpow_finset
    (μ.withDensity W) s hp f (fun i => by
      obtain ⟨g, hg, hfg⟩ := hf i
      exact ⟨g, hg, (withDensity_absolutelyContinuous μ W).ae_eq hfg⟩)
  have hm : AEMeasurable (fun x => (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (p / 2)) μ := by
    have h1 : AEMeasurable (fun x => ∑ i ∈ s, (f i x) ^ (2 : ℝ)) μ := by
      have h := Finset.aemeasurable_sum s (fun i _ => (hf i).pow_const (2 : ℝ))
      rwa [Finset.sum_fn] at h
    exact h1.pow_const _
  have h1 : (∫⁻ x, (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂(μ.withDensity W))
      = ∫⁻ x, W x * (∑ i ∈ s, (f i x) ^ (2 : ℝ)) ^ (p / 2) ∂μ :=
    lintegral_withDensity_eq_lintegral_mul₀ hW hm
  have h2 : ∀ i, (∫⁻ x, (f i x) ^ p ∂(μ.withDensity W)) = ∫⁻ x, W x * (f i x) ^ p ∂μ :=
    fun i => lintegral_withDensity_eq_lintegral_mul₀ hW ((hf i).pow_const p)
  rw [h1, Finset.sum_congr rfl (fun i _ => by rw [h2 i])] at hcore
  exact hcore

theorem asymLHS_le_fused_uni {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
    (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, ∀ (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      asymLHS k hk l N m m' q q' f ≤ C * ∫⁻ t : E k,
        (∫⁻ z : E k, asymC2 k hk l N m' q' f z
            * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t))
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 (hBallR k l m') (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
  have hA0 : (0 : ℝ) ≤ A := by
    have h1 : (0 : ℝ) ≤ gaugeExp k + (l : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k,
      (gaugeExp_gt hk : (k : ℝ) < gaugeExp k), Nat.cast_nonneg (α := ℝ) l]
    linarith [hAge]
  obtain ⟨Cloc, hAV⟩ := exists_AV_bound_uni hk hl hlk h2m hmM hMN hM h4 hm hξ' q hsepI hsep
    ha1 hεm hAge hmMod
  obtain ⟨Csup, hCsup0, hsup⟩ := asymLHS_le_supMoving_uni (hk := hk) (hl := hl) (hlk := hlk)
    q q' hξ' hr0 le_rfl hsep'
  refine ⟨ENNReal.ofReal Csup * Cloc ^ (plExp l), fun f hf => ?_⟩
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
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
  have hAV' : ∀ u : E k, AV u ≤ Bv * Cloc ^ (plExp l) * S u := fun u => hAV f hf u
  have hsup' : asymLHS k hk l N m m' q q' f ≤ ENNReal.ofReal Csup * ∫⁻ z : E k,
      (ENNReal.ofReal ((volume (Metric.ball (0 : E l) (hBallR k l m'))).toReal))⁻¹ *
      (∫⁻ w in Metric.ball (0 : E l) (hBallR k l m'),
        asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
      * asymC2 k hk l N m' q' f z := hsup f hfm
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
    exact lintegral_mono fun t => mul_le_mul' le_rfl (hAV' (z - t))
  refine hsup'.trans ?_
  refine (mul_le_mul_of_nonneg_left ?_ bot_le).trans (le_of_eq (mul_assoc _ _ _).symm)
  exact (le_of_eq hstep2).trans (hstep3.trans (le_of_eq hkey))

/-! ## The per-(q,q') step and the assembly of `AsymDecFine` -/

/-- **The per-(q,q') step of Lemma 3.8, uniformly in the tuple.** -/
theorem asymDecFine_pt_uni {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
    (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, ∀ (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      asymLHS k hk l N m m' q q' f ≤ C ^ (plExp l)
        * (∑ q'' ∈ subBlkLvl m M q,
            (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2) := by
  have hp0 : (0 : ℝ) < plExp l := plExp_pos hl
  have hp2 : (2 : ℝ) ≤ plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    nlinarith
  obtain ⟨C1, h1⟩ := asymLHS_le_fused_uni hk hl hlk h2m hmM hMN hM h4 hm hξ' q q' hsep'
    hsepI hsep ha1 hεm hAge hmMod
  obtain ⟨CJ, hCJ0, hCJ⟩ := lintegral_W_mul_tentNorm_le_uni (k := k) (l := l) hk hl hlk
    hmM hMN (le_trans h2m hmM) hξ' q q' hsep' hAge
  refine ⟨(C1 * ENNReal.ofReal CJ) ^ ((1 : ℝ) / plExp l), fun f hf => ?_⟩
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
  set W : E k → ℝ≥0∞ := fun t => ∫⁻ z : E k, asymC2 k hk l N m' q' f z
    * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t) with hW
  set TN : Fin (2 ^ M) → E k → ℝ≥0∞ := fun J u => tentNorm l A 0 (hBallR k l m')
    (fun y : E l => ∑ i ∈ blkFin N M J,
      f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y)) with hTN
  have hWm : Measurable W := by
    simp only [hW]
    refine Measurable.lintegral_prod_right ?_
    exact (measurable_asymC2 k hk l N m' q' hfm).comp measurable_snd |>.mul
      (((continuous_platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)).measurable).comp
        (measurable_snd.sub measurable_fst))
  have hTNm : ∀ J : Fin (2 ^ M), Measurable (TN J) := by
    intro J
    simp only [hTN]
    unfold tentNorm
    refine Measurable.lintegral_prod_right ?_
    refine Measurable.mul ?_ ((measurable_ballTent l A 0 (hBallR k l m')).comp measurable_snd)
    have h1 : Measurable (fun p : E k × E l =>
        ((‖∑ i ∈ blkFin N M J,
          f i (p.1 + projEmbedLin k l (torsionVec k l hlk ξ') p.2)‖₊ : ℝ≥0∞))) := by
      refine Measurable.coe_nnreal_ennreal ?_
      refine Measurable.nnnorm ?_
      exact Finset.measurable_sum _ fun i _ => (hfm i).comp
        (measurable_fst.add
          ((LinearMap.continuous_of_finiteDimensional _).measurable.comp measurable_snd))
    exact h1.pow_const _
  have hTNN : ∀ J : Fin (2 ^ M), AEMeasurable
      (fun x : E k => (TN J x) ^ ((1 : ℝ) / plExp l)) volume :=
    fun J => (hTNm J).aemeasurable.pow_const _
  have hmink := lintegral_ell2_minkowski_rpow_weighted_finset (μ := volume) (W := W)
    hWm.aemeasurable (subBlkLvl m M q) hp2 (fun J x => (TN J x) ^ ((1 : ℝ) / plExp l)) hTNN
  have hsq : ∀ (J : Fin (2 ^ M)) (x : E k),
      ((TN J x) ^ ((1 : ℝ) / plExp l)) ^ (2 : ℝ) = (TN J x) ^ (2 / plExp l) := by
    intro J x
    rw [← ENNReal.rpow_mul]
    congr 1
    ring
  have hpp : ∀ (J : Fin (2 ^ M)) (x : E k),
      ((TN J x) ^ ((1 : ℝ) / plExp l)) ^ (plExp l) = TN J x := by
    intro J x
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hp0), ENNReal.rpow_one]
  have hL : (∫⁻ x : E k, W x * (∑ i ∈ subBlkLvl m M q,
        ((TN i x) ^ ((1 : ℝ) / plExp l)) ^ (2 : ℝ)) ^ (plExp l / 2))
      = (∫⁻ x : E k, W x * (∑ J ∈ subBlkLvl m M q,
          (TN J x) ^ (2 / plExp l)) ^ (plExp l / 2)) := by
    refine lintegral_congr fun x => ?_
    rw [Finset.sum_congr rfl fun J (_ : J ∈ subBlkLvl m M q) => hsq J x]
  have hR : (∑ i ∈ subBlkLvl m M q,
        (∫⁻ x : E k, W x * ((TN i x) ^ ((1 : ℝ) / plExp l)) ^ (plExp l)) ^ (2 / plExp l))
      = (∑ J ∈ subBlkLvl m M q, (∫⁻ x : E k, W x * TN J x) ^ (2 / plExp l)) := by
    refine Finset.sum_congr rfl fun J _ => ?_
    congr 1
    exact lintegral_congr fun x => by rw [hpp J x]
  rw [hL, hR] at hmink
  have hZ : (∫⁻ t : E k, W t * (∑ J ∈ subBlkLvl m M q, (TN J t) ^ (2 / plExp l))
        ^ (plExp l / 2))
      ≤ (∑ J ∈ subBlkLvl m M q, (∫⁻ t : E k, W t * TN J t) ^ (2 / plExp l))
          ^ (plExp l / 2) := by
    calc (∫⁻ t : E k, W t * (∑ J ∈ subBlkLvl m M q, (TN J t) ^ (2 / plExp l))
          ^ (plExp l / 2))
        = ((∫⁻ t : E k, W t * (∑ J ∈ subBlkLvl m M q, (TN J t) ^ (2 / plExp l))
              ^ (plExp l / 2)) ^ ((1 : ℝ) / plExp l)) ^ (plExp l) := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hp0), ENNReal.rpow_one]
      _ ≤ ((∑ J ∈ subBlkLvl m M q, (∫⁻ t : E k, W t * TN J t) ^ (2 / plExp l))
              ^ ((1 : ℝ) / 2)) ^ (plExp l) :=
          ENNReal.rpow_le_rpow hmink hp0.le
      _ = (∑ J ∈ subBlkLvl m M q, (∫⁻ t : E k, W t * TN J t) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
  have hJsum : (∑ J ∈ subBlkLvl m M q, (∫⁻ t : E k, W t * TN J t) ^ (2 / plExp l))
      ≤ (ENNReal.ofReal CJ) ^ (2 / plExp l)
        * (∑ J ∈ subBlkLvl m M q, (asymLHS k hk l N M m' J q' f) ^ (2 / plExp l)) := by
    calc (∑ J ∈ subBlkLvl m M q, (∫⁻ t : E k, W t * TN J t) ^ (2 / plExp l))
        ≤ ∑ J ∈ subBlkLvl m M q,
            (ENNReal.ofReal CJ * asymLHS k hk l N M m' J q' f) ^ (2 / plExp l) :=
          Finset.sum_le_sum fun J hJ =>
            ENNReal.rpow_le_rpow (by simp only [hW, hTN]; exact hCJ J hJ f hf) (by positivity)
      _ = (ENNReal.ofReal CJ) ^ (2 / plExp l)
            * ∑ J ∈ subBlkLvl m M q, (asymLHS k hk l N M m' J q' f) ^ (2 / plExp l) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun J _ => by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  have hY : (∑ J ∈ subBlkLvl m M q, (∫⁻ t : E k, W t * TN J t) ^ (2 / plExp l))
        ^ (plExp l / 2)
      ≤ ENNReal.ofReal CJ * (∑ q'' ∈ subBlkLvl m M q,
          (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2) := by
    calc (∑ J ∈ subBlkLvl m M q, (∫⁻ t : E k, W t * TN J t) ^ (2 / plExp l))
          ^ (plExp l / 2)
        ≤ ((ENNReal.ofReal CJ) ^ (2 / plExp l) * (∑ q'' ∈ subBlkLvl m M q,
            (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l))) ^ (plExp l / 2) :=
          ENNReal.rpow_le_rpow hJsum (by positivity)
      _ = ((ENNReal.ofReal CJ) ^ (2 / plExp l)) ^ (plExp l / 2)
            * (∑ q'' ∈ subBlkLvl m M q,
                (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      _ = ENNReal.ofReal CJ * (∑ q'' ∈ subBlkLvl m M q,
            (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2) := by
          rw [show ((ENNReal.ofReal CJ) ^ (2 / plExp l)) ^ (plExp l / 2)
              = ENNReal.ofReal CJ from by
            rw [← ENNReal.rpow_mul,
              show (2 / plExp l) * (plExp l / 2) = 1 by field_simp, ENNReal.rpow_one]]
  have hfin : asymLHS k hk l N m m' q q' f ≤ (C1 * ENNReal.ofReal CJ)
      * (∑ q'' ∈ subBlkLvl m M q,
          (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2) := by
    refine h1 f hf |>.trans ?_
    refine (mul_le_mul_of_nonneg_left (hZ.trans hY) bot_le).trans (le_of_eq ?_)
    ring
  refine hfin.trans (le_of_eq ?_)
  rw [show ((C1 * ENNReal.ofReal CJ) ^ ((1 : ℝ) / plExp l)) ^ (plExp l)
      = C1 * ENNReal.ofReal CJ from by
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hp0), ENNReal.rpow_one]]

/-- **The separation of a coarse block from the level-`m'` centre** implies the pointwise
separation hypothesis of the lane. -/
lemma sepLevel_hsepI {m m' : ℕ} (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
    (hsep : sepLevel m m' q q') :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t
        - pieceCenter (2 ^ m') q'| := by
  intro t ht
  have h1 : 1 / 4 + plateHalf m + plateHalf m'
      ≤ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'| := by
    unfold sepLevel at hsep
    have h1' : 1 / 4 + 1 / (2 : ℝ) ^ (m + 1) + 1 / (2 : ℝ) ^ (m' + 1)
        ≤ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'| := by linarith
    rwa [plateHalf, plateHalf]
  have h2 : |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t
      - pieceCenter (2 ^ m) q| ≤ plateHalf m := by
    have hhalf : (1 : ℝ) / (2 : ℝ) ^ m = 2 * plateHalf m := by
      rw [plateHalf, pow_succ]; ring
    have ht1 : (1 / (2 : ℝ) ^ m) * t ≤ 2 * plateHalf m := by
      rw [hhalf]
      nlinarith [ht.1, ht.2, plateHalf_pos m]
    have ht0 : 0 ≤ (1 / (2 : ℝ) ^ m) * t := mul_nonneg (by positivity) ht.1
    have hsub : ((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - pieceCenter (2 ^ m) q
        = (1 / (2 : ℝ) ^ m) * t - plateHalf m := by
      have h := pieceCenter_sub_plateHalf m q
      linarith
    rw [hsub, abs_le]
    constructor <;> linarith
  have h5 := abs_sub_le (pieceCenter (2 ^ m) q)
    (((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t) (pieceCenter (2 ^ m') q')
  have h6 : |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - pieceCenter (2 ^ m') q'|
      ≥ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'|
        - |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - pieceCenter (2 ^ m) q| := by
    rw [abs_sub_comm (pieceCenter (2 ^ m) q)
      (((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t)] at h5
    linarith
  linarith [(plateHalf_pos m').le]

/-- **The separation is inherited by the refined sub-blocks.** -/
lemma sepLevel_hsep {m M m' : ℕ} (hmM : m ≤ M) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
    (hsep : sepLevel m m' q q') :
    ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - pieceCenter (2 ^ m') q'| := by
  intro j
  have h1 : 1 / 4 + plateHalf m + plateHalf m'
      ≤ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'| := by
    unfold sepLevel at hsep
    have h1' : 1 / 4 + 1 / (2 : ℝ) ^ (m + 1) + 1 / (2 : ℝ) ^ (m' + 1)
        ≤ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'| := by linarith
    rwa [plateHalf, plateHalf]
  have h2 : |pieceCenter (2 ^ M) (subIdx m M hmM q j) - pieceCenter (2 ^ m) q| ≤ plateHalf m := by
    refine (abs_pieceCenter_subBlkLvl_sub_le (m'' := M) hmM
      (mem_subBlkLvl.mpr (subIdx_div m M hmM q j))).trans ?_
    have := plateHalf_pos M
    linarith
  have h5 := abs_sub_le (pieceCenter (2 ^ m) q)
    (pieceCenter (2 ^ M) (subIdx m M hmM q j)) (pieceCenter (2 ^ m') q')
  have h6 : |pieceCenter (2 ^ M) (subIdx m M hmM q j) - pieceCenter (2 ^ m') q'|
      ≥ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'|
        - |pieceCenter (2 ^ M) (subIdx m M hmM q j) - pieceCenter (2 ^ m) q| := by
    rw [abs_sub_comm (pieceCenter (2 ^ m) q) (pieceCenter (2 ^ M) (subIdx m M hmM q j))] at h5
    linarith
  linarith [(plateHalf_pos m').le]

/-- **The assembly of `AsymDecFine`** (GLYZ (3.10) / Lemma 3.8) from the degree-`l` model theorem at
the fixed enlargement `laneEnl`.  The constant is obtained by taking the supremum of the per-(q,q')
constants over the *finite* set of block pairs, which is legitimate because the per-(q,q') step
`asymDecFine_pt_uni` is uniform in the tuple `f`. -/
theorem asymDecFine_of_model {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ refLvl l k m') (hMN : refLvl l k m' ≤ N)
    (h4 : 4 ≤ 2 ^ (refLvl l k m' - m)) (hm : 1 ≤ m)
    {a₀ εm : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, AsymDecFine k hk l N m m' C := by
  have hAge : gaugeExp k + (l : ℝ) < gaugeExp k + (l : ℝ) + 1 := by linarith
  have hper : ∀ p : Fin (2 ^ m) × Fin (2 ^ m'), ∃ C : ℝ≥0∞,
      sepLevel m m' p.1 p.2 → ∀ (f : Fin (2 ^ N) → E k → ℂ),
        (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
        asymLHS k hk l N m m' p.1 p.2 f ≤ C ^ (plExp l)
          * (∑ q'' ∈ subBlkLvl m (refLvl l k m') p.1,
              (asymLHS k hk l N (refLvl l k m') m' q'' p.2 f) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
    intro p
    by_cases hs : sepLevel m m' p.1 p.2
    · obtain ⟨C, hC⟩ := asymDecFine_pt_uni (M := refLvl l k m') hk hl hlk h2m hmM hMN rfl h4 hm
        (pieceCenter_mem_Icc (2 ^ m') Nat.one_le_two_pow p.2) p.1 p.2
        (by rw [sub_self, abs_zero]; exact (plateHalf_pos m').le) (sepLevel_hsepI p.1 p.2 hs)
        (sepLevel_hsep hmM p.1 p.2 hs) ha1 hεm hAge hmMod
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose Cp hCp using hper
  refine ⟨(Finset.univ : Finset (Fin (2 ^ m) × Fin (2 ^ m'))).sup Cp, ?_⟩
  intro q q' hsep f hf
  refine (hCp (q, q') hsep f hf).trans ?_
  refine mul_le_mul_of_nonneg_right
    (ENNReal.rpow_le_rpow (Finset.le_sup (Finset.mem_univ (q, q'))) (le_of_lt (plExp_pos hl)))
    bot_le

/-- **GLYZ Lemma 3.9, assembled**: the asymmetric bilinear decoupling at the coarse level follows
from the refined level at the price of the constant of Lemma 3.8 raised to `p_l/p_k`. -/
theorem asymDec_of_model {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (hlk1 : l ≤ k - 1)
    (h2m : 2 ≤ m) (hmM : m ≤ refLvl l k m') (hMN : refLvl l k m' ≤ N)
    (h4 : 4 ≤ 2 ^ (refLvl l k m' - m)) (hm : 1 ≤ m)
    {a₀ εm : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, ∀ C₁ : ℝ≥0∞, AsymDec k hk l N (refLvl l k m') m' C₁ →
      AsymDec k hk l N m m' (C₁ * C ^ (plExp l / pkExp k)) := by
  obtain ⟨C₂, hfine⟩ := asymDecFine_of_model hk hl hlk h2m hmM hMN h4 hm ha1 hεm hmMod
  exact ⟨C₂, fun C₁ hbig => asymDec_of_fine hk hl hlk1 hmM hMN hbig hfine⟩

end Submission.Vinogradov
