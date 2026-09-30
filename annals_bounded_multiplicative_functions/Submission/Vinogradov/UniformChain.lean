/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Final
import Submission.Vinogradov.Tower
import Submission.Vinogradov.UniformConst
import Submission.Vinogradov.CurveDecProj


/-!
# The uniform (parameter-free) constants of the §3.4 lane

The §4 recursion (GLYZ (4.4)) needs the first-slot coarsening of GLYZ Lemma 3.9 with a constant
whose `N`-dependence is controlled.  The existing chain (`Lemma38Final.asymDec_of_model`) chooses its
constant by `Classical.choose`/`Finset.sup` *after* the parameters `(N, m, m', ξ', q, q')`, so the
dependence is formally invisible.  Here we re-state the chain with those parameters universally
quantified **inside** the existential over the constant, so that the constant is a function of
`(k, l, a₀, εm)` alone.  Each proof is the proof of the corresponding non-uniform statement with the
`intro`s moved past the point where the constant is fixed.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000

namespace Submission.Vinogradov

theorem norm_projMapLin_gammaDeriv_le_uniform {k l : ℕ} (hlk : l ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ (m : ℕ), 1 ≤ m → m ≤ k - l →
      ∀ c ∈ Set.Icc (0 : ℝ) 1,
      ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c)‖
        ≤ C * |c - ξ'| ^ (k - l + 1 - m) := by
  refine ⟨((k : ℝ) + 1) * (Real.sqrt k * (k.factorial : ℝ)) + 1, by positivity, ?_⟩
  intro ξ' hξ' m hm1 hmkl c hc
  have hc1 : |c| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hc.1], hc.2⟩
  have hξ'1 : |ξ'| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hξ'.1], hξ'.2⟩
  have hint : |c - ξ'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, hξ'.1, hξ'.2]
  -- expand the derivative vector around `ξ'`
  have hexp : gammaDeriv k m c
      = ∑ e ∈ Finset.range (k + 1),
          ((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ' := by
    have h : c = ξ' + (c - ξ') := by ring
    rw [h, gammaDeriv_eq_lpSymm_gam, Commons.Analysis.MomentCurve.gam_add]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [gammaDeriv_eq_lpSymm_gam]
    norm_num
  rw [hexp, map_sum]
  -- the surviving index set
  set S : Finset ℕ := (Finset.range (k + 1)).filter (fun e => k - l - m < e) with hS
  have hsplit : ∑ e ∈ Finset.range (k + 1),
        projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')
      = ∑ e ∈ S, projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ') := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro e he hes
    have hes2 : e ≤ k - l - m := by
      by_contra hcon
      exact hes (Finset.mem_filter.mpr ⟨he, Nat.lt_of_not_le hcon⟩)
    have hme : m + e ≤ k - l := by
      have h1 : m + e ≤ m + (k - l - m) := Nat.add_le_add_left hes2 m
      have h2 : m + (k - l - m) = k - l := Nat.add_sub_of_le hmkl
      omega
    rw [map_smul, projMapLin_gammaDeriv_eq_zero hlk (by omega) hme, smul_zero]
  rw [hsplit]
  -- bound each surviving term
  have hterm : ∀ e ∈ S,
      ‖projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')‖
        ≤ |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) := by
    intro e he
    rw [hS, Finset.mem_filter, Finset.mem_range] at he
    obtain ⟨hek, hlt⟩ := he
    rw [map_smul, norm_smul]
    have hpow : |c - ξ'| ^ e ≤ |c - ξ'| ^ (k - l + 1 - m) :=
      pow_le_pow_of_le_one (abs_nonneg _) hint (by omega)
    have hfac : (1 : ℝ) ≤ (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
    have hfac0 : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
    have hc0 : (0 : ℝ) ≤ |c - ξ'| ^ e := pow_nonneg (abs_nonneg _) e
    have hcoeff : ‖(((c - ξ') ^ e / ((e.factorial : ℝ))) : ℝ)‖
        ≤ |c - ξ'| ^ (k - l + 1 - m) := by
      rw [Real.norm_eq_abs]
      have hfacabs : |(((e.factorial : ℕ) : ℝ))| = (e.factorial : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [abs_div, abs_pow, hfacabs]
      rw [div_le_iff₀ hfac0]
      calc |c - ξ'| ^ e ≤ |c - ξ'| ^ (k - l + 1 - m) := hpow
        _ = |c - ξ'| ^ (k - l + 1 - m) * 1 := by ring
        _ ≤ |c - ξ'| ^ (k - l + 1 - m) * (e.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left hfac (pow_nonneg (abs_nonneg _) _)
    calc ‖(((c - ξ') ^ e / ((e.factorial : ℝ))) : ℝ)‖
          * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (m + e) ξ')‖
        ≤ |c - ξ'| ^ (k - l + 1 - m)
            * (Real.sqrt k * (k.factorial : ℝ)) := by
          refine mul_le_mul hcoeff ?_ (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
          exact le_trans (norm_projMapLin_le k l
            (orthonormal_torsionVec k l hlk ξ') _) (norm_gammaDeriv_le k hξ'1 (m + e))
    _ = |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) := rfl
  calc ‖∑ e ∈ S, projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')‖
      ≤ ∑ e ∈ S, ‖projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ S, |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (|c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((k : ℝ) + 1) * (Real.sqrt k * (k.factorial : ℝ)) + 1)
          * |c - ξ'| ^ (k - l + 1 - m) := by
        have hcard : (S.card : ℝ) ≤ (k : ℝ) + 1 := by
          have h1 : S.card ≤ (Finset.range (k + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
          have h2 : (Finset.range (k + 1)).card = k + 1 := Finset.card_range _
          rw [h2] at h1
          exact_mod_cast h1
        have hnn : (0 : ℝ) ≤ |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) :=
          mul_nonneg (pow_nonneg (abs_nonneg _) _) (by positivity)
        calc (S.card : ℝ) * (|c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)))
            ≤ ((k : ℝ) + 1) * (|c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ))) :=
              mul_le_mul_of_nonneg_right hcard hnn
          _ ≤ (((k : ℝ) + 1) * (Real.sqrt k * (k.factorial : ℝ)) + 1)
                * |c - ξ'| ^ (k - l + 1 - m) := by
              nlinarith [pow_nonneg (abs_nonneg (c - ξ')) (k - l + 1 - m),
                Real.sqrt_nonneg k, Nat.cast_nonneg (α := ℝ) k.factorial]

/-! ## 4. The `H`-ball sits inside a fixed multiple of the polar plate -/



theorem gauge_plateGaugeLin_projEmbed_le_norm_uniform {k l : ℕ} (hk : 1 ≤ k) (hlk : l ≤ k) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ ξ' ∈ Set.Icc (0 : ℝ) 1, ∀ (m' : ℕ) (c' : ℝ), c' ∈ Set.Icc (0 : ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ w : E l,
      gauge k hk (plateGaugeLin k (plateHalf m') c'
        (projEmbedLin k l (torsionVec k l hlk ξ') w))
        ≤ C₀ * (plateHalf m') ^ (k - l + 1) * ‖w‖ := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := norm_projMapLin_gammaDeriv_le_uniform hlk
  refine ⟨max C₁ (Real.sqrt k * (k.factorial : ℝ)), le_trans hC₁pos.le (le_max_left _ _), ?_⟩
  intro ξ' hξ' m' c' hc' hsep w
  have hδ0 : 0 < plateHalf m' := plateHalf_pos m'
  have hδ1 : plateHalf m' ≤ 1 := plateHalf_le_one m'
  rw [gauge]
  refine Finset.sup'_le _ _ fun i _ => ?_
  rw [plateGaugeLin_apply]
  have hinner : ⟪projEmbedLin k l (torsionVec k l hlk ξ') w, gammaDeriv k (i.val + 1) c'⟫
      = ⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')⟫ :=
    inner_projEmbed_projMap k l (torsionVec k l hlk ξ') w _
  rw [hinner, abs_mul, abs_of_nonneg (pow_nonneg hδ0.le _)]
  have hstep : (plateHalf m') ^ (i.val + 1)
        * |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')⟫|
      ≤ (plateHalf m') ^ (i.val + 1)
        * (‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ')
            (gammaDeriv k (i.val + 1) c')‖) :=
    mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (pow_nonneg hδ0.le _)
  have hkey : (plateHalf m') ^ (i.val + 1)
        * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
      ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) := by
    by_cases hcase : i.val + 1 ≤ k - l
    · have hb := hC₁ ξ' hξ' (i.val + 1) (by omega) hcase c' hc'
      have hdK : |c' - ξ'| ^ (k - l + 1 - (i.val + 1))
          ≤ (plateHalf m') ^ (k - l + 1 - (i.val + 1)) :=
        pow_le_pow_left₀ (abs_nonneg _) hsep _
      have hval : (i.val + 1) + (k - l + 1 - (i.val + 1)) = k - l + 1 := by omega
      have hpow : (plateHalf m') ^ (i.val + 1) * (plateHalf m') ^ (k - l + 1 - (i.val + 1))
          = (plateHalf m') ^ (k - l + 1) := by rw [← pow_add, hval]
      calc (plateHalf m') ^ (i.val + 1)
            * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
          ≤ (plateHalf m') ^ (i.val + 1)
            * (C₁ * |c' - ξ'| ^ (k - l + 1 - (i.val + 1))) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hδ0.le _)
        _ ≤ (plateHalf m') ^ (i.val + 1)
            * (C₁ * (plateHalf m') ^ (k - l + 1 - (i.val + 1))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdK hC₁pos.le)
                (pow_nonneg hδ0.le _)
        _ = C₁ * (plateHalf m') ^ (k - l + 1) := by rw [← hpow]; ring
        _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hδ0.le _)
    · have hb : ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
          ≤ Real.sqrt k * (k.factorial : ℝ) :=
        le_trans (norm_projMapLin_le k l (orthonormal_torsionVec k l hlk ξ') _)
          (norm_gammaDeriv_le k (by rw [abs_le]; exact ⟨by linarith [hc'.1], hc'.2⟩) (i.val + 1))
      have hexp : k - l + 1 ≤ i.val + 1 := by omega
      have hpow : (plateHalf m') ^ (i.val + 1) ≤ (plateHalf m') ^ (k - l + 1) :=
        pow_le_pow_of_le_one hδ0.le hδ1 hexp
      calc (plateHalf m') ^ (i.val + 1)
            * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖
          ≤ (plateHalf m') ^ (k - l + 1) * (Real.sqrt k * (k.factorial : ℝ)) :=
            mul_le_mul hpow hb (norm_nonneg _) (pow_nonneg hδ0.le _)
        _ = (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) := by ring
        _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hδ0.le _)
  calc (plateHalf m') ^ (i.val + 1)
        * |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')⟫|
      ≤ (plateHalf m') ^ (i.val + 1)
        * (‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖) := hstep
    _ = ((plateHalf m') ^ (i.val + 1)
        * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (i.val + 1) c')‖) * ‖w‖ := by ring
    _ ≤ (max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1)) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
    _ = max C₁ (Real.sqrt k * (k.factorial : ℝ)) * (plateHalf m') ^ (k - l + 1) * ‖w‖ := by ring


/-! ## 4. The moving-ball (Fubini) identity for the translate `H + z` -/


theorem asymC2_shift_le_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {N m' : ℕ} {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
      (q' : Fin (2 ^ m')) (hsep : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
      {r : ℝ} (hr : 0 < r) (hrh : r ≤ hBallR k l m')
      (f : Fin (2 ^ N) → E k → ℂ) (z : E k) (w : E l),
      asymC2 k hk l N m' q' f (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ gaugeExp k)
            * asymC2 k hk l N m' q' f z := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := gauge_plateGaugeLin_projEmbed_le_norm_uniform hk hlk
  refine ⟨C₀, hC₀0, ?_⟩
  intro N m' ξ' hξ' q' hsep r hr hrh f z w
  have hpc : pieceCenter (2 ^ m') q' ∈ Set.Icc (0 : ℝ) 1 :=
    pieceCenter_mem_Icc (2 ^ m') Nat.one_le_two_pow q'
  have hδ0 : 0 < plateHalf m' := plateHalf_pos m'
  have hδr : (plateHalf m') ^ (k - l + 1) * hBallR k l m' = 1 := by
    rw [hBallR, inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt hδ0))
  have hρw : gauge k hk (plateGaugeLin k (plateHalf m') (pieceCenter (2 ^ m') q')
      (projEmbedLin k l (torsionVec k l hlk ξ') w)) ≤ C₀ * ‖w‖ / r := by
    refine (hC₀ ξ' hξ' m' _ hpc hsep w).trans ?_
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

theorem lintegral_ballTent_shift_le_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {A A' C₀ Cg : ℝ} (hA : 0 < A)
    (hC₀ : 0 ≤ C₀) (hCg : 0 ≤ Cg)
    (hgrowth : ∀ r : ℝ, 0 < r →
      (∫⁻ w : E l, ballTent l A' 0 r w * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A))
        ≤ ENNReal.ofReal Cg) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ξ' : ℝ}, ξ' ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (C2 ΦI H : E k → ℝ≥0∞), Measurable C2 → Measurable ΦI →
      Measurable H → ∀ (r : ℝ), 0 < r →
      (∀ (z : E k) (w : E l), C2 (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
          ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) →
      (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t))
          * (∫⁻ w : E l, ballTent l A' 0 r w
              * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w)))
        ≤ ENNReal.ofReal C * ∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t := by
  refine ⟨Cg, hCg, ?_⟩
  intro ξ' hξ' C2 ΦI H hC2 hΦI hH r hr hshift
  set P : E l →ₗ[ℝ] E k := projEmbedLin k l (torsionVec k l hlk ξ') with hP
  set W : E k → ℝ≥0∞ := fun t => ∫⁻ z : E k, C2 z * ΦI (z - t) with hW
  have hWmeas : Measurable W := by
    rw [hW]
    refine Measurable.lintegral_prod_right (ν := (volume : Measure (E k))) ?_
    show Measurable (fun p : E k × E k => C2 p.2 * ΦI (p.2 - p.1))
    exact (hC2.comp measurable_snd).mul (hΦI.comp (measurable_snd.sub measurable_fst))
  have hPmeas : Measurable P := P.continuous_of_finiteDimensional.measurable
  -- (1) the weighted shift bound on `W`
  have hWshift : ∀ (t : E k) (w : E l),
      W (t - P w) ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t := by
    intro t w
    have key : W (t - P w) = ∫⁻ z : E k, C2 (z - P w) * ΦI (z - t) := by
      rw [hW]
      have h2 : (∫⁻ z : E k, (fun z : E k => C2 (z - P w) * ΦI (z - t)) (z + P w))
          = ∫⁻ z : E k, (fun z : E k => C2 (z - P w) * ΦI (z - t)) z :=
        lintegral_add_right_eq_self (fun z : E k => C2 (z - P w) * ΦI (z - t)) (P w)
      rw [← h2]
      refine lintegral_congr fun z => ?_
      show C2 z * ΦI (z - (t - P w)) = C2 (z + P w - P w) * ΦI (z + P w - t)
      rw [show z + P w - P w = z from by abel,
        show z + P w - t = z - (t - P w) from by abel]
    calc W (t - P w) = ∫⁻ z : E k, C2 (z - P w) * ΦI (z - t) := key
      _ ≤ ∫⁻ z : E k, (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) * ΦI (z - t) :=
          lintegral_mono fun z => mul_le_mul' (hshift z w) le_rfl
      _ = ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t := by
          rw [hW]
          rw [show (fun z : E k => (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) * ΦI (z - t))
              = fun z : E k => ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)
                * (C2 z * ΦI (z - t)) from by funext z; ring]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- (2) pull `W t` inside, Tonelli, substitute `t ↦ t - Ψw`
  have hstep1 : (∫⁻ t : E k, W t * (∫⁻ w : E l, ballTent l A' 0 r w * H (t + P w)))
      = ∫⁻ t : E k, ∫⁻ w : E l, W t * ballTent l A' 0 r w * H (t + P w) := by
    refine lintegral_congr fun t => ?_
    rw [show (fun w : E l => W t * ballTent l A' 0 r w * H (t + P w))
        = fun w : E l => W t * (ballTent l A' 0 r w * H (t + P w)) from by funext w; ring]
    exact (lintegral_const_mul (W t) ((measurable_ballTent l A' 0 r).mul
      (hH.comp (measurable_const.add (hPmeas.comp measurable_id))))).symm
  have hstep2 : (∫⁻ t : E k, ∫⁻ w : E l, W t * ballTent l A' 0 r w * H (t + P w))
      = ∫⁻ w : E l, ∫⁻ t : E k, W t * ballTent l A' 0 r w * H (t + P w) := by
    refine lintegral_lintegral_swap ?_
    have h1 : Measurable (fun p : E k × E l =>
        W p.1 * ballTent l A' 0 r p.2 * H (p.1 + P p.2)) :=
      ((hWmeas.comp measurable_fst).mul ((measurable_ballTent l A' 0 r).comp measurable_snd)).mul
        (hH.comp (measurable_fst.add (hPmeas.comp measurable_snd)))
    exact h1.aemeasurable
  have hstep3 : ∀ w : E l,
      (∫⁻ t : E k, W t * ballTent l A' 0 r w * H (t + P w))
        = ballTent l A' 0 r w * ∫⁻ t : E k, W (t - P w) * H t := by
    intro w
    have h1 : (∫⁻ t : E k, W t * ballTent l A' 0 r w * H (t + P w))
        = ∫⁻ t : E k, ballTent l A' 0 r w * (W t * H (t + P w)) := by
      refine lintegral_congr fun t => ?_
      rw [show W t * ballTent l A' 0 r w * H (t + P w)
          = ballTent l A' 0 r w * (W t * H (t + P w)) from by ring]
    have hmeas : Measurable (fun a : E k => W a * H (a + P w)) :=
      hWmeas.mul (hH.comp (measurable_id.add measurable_const))
    have h2 : (∫⁻ t : E k, ballTent l A' 0 r w * (W t * H (t + P w)))
        = ballTent l A' 0 r w * ∫⁻ t : E k, W t * H (t + P w) :=
      lintegral_const_mul (ballTent l A' 0 r w) hmeas
    rw [h1, h2]
    congr 1
    have h3 : (∫⁻ t : E k, (fun t : E k => W (t - P w) * H t) (t + P w))
        = ∫⁻ t : E k, (fun t : E k => W (t - P w) * H t) t :=
      lintegral_add_right_eq_self (fun t : E k => W (t - P w) * H t) (P w)
    rw [← h3]
    refine lintegral_congr fun t => ?_
    show W t * H (t + P w) = W (t + P w - P w) * H (t + P w)
    rw [add_sub_cancel_right]
  -- (3) the weighted shift bound plus the growth hypothesis
  have hstep4 : (∫⁻ w : E l, ballTent l A' 0 r w * ∫⁻ t : E k, W (t - P w) * H t)
      ≤ ∫⁻ w : E l, ballTent l A' 0 r w
          * (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t) := by
    refine lintegral_mono fun w => mul_le_mul' le_rfl ?_
    have h2 : (∫⁻ t : E k, W (t - P w) * H t)
        ≤ ∫⁻ t : E k, (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t) * H t :=
      lintegral_mono fun t => mul_le_mul' (hWshift t w) le_rfl
    have h3 : (∫⁻ t : E k, (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t) * H t)
        = ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t := by
      rw [show (fun t : E k => (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * W t) * H t)
          = fun t : E k => ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * (W t * H t) from by
        funext t; ring]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    exact h2.trans (le_of_eq h3)
  have hstep5 : (∫⁻ w : E l, ballTent l A' 0 r w
        * (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t))
      ≤ ENNReal.ofReal Cg * ∫⁻ t : E k, W t * H t := by
    rw [show (fun w : E l => ballTent l A' 0 r w
          * (ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * ∫⁻ t : E k, W t * H t))
        = fun w : E l => (ballTent l A' 0 r w
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) * ∫⁻ t : E k, W t * H t from by
      funext w; ring]
    have hmeas : Measurable (fun w : E l => ballTent l A' 0 r w
        * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) :=
      (measurable_ballTent l A' 0 r).mul (by measurability)
    have h2 : (∫⁻ w : E l, (ballTent l A' 0 r w
          * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) * ∫⁻ t : E k, W t * H t)
        = (∫⁻ w : E l, ballTent l A' 0 r w
            * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A)) * ∫⁻ t : E k, W t * H t :=
      lintegral_mul_const _ hmeas
    rw [h2]
    exact mul_le_mul' (hgrowth r hr) le_rfl
  rw [hstep1, hstep2]
  refine le_trans (le_of_eq (lintegral_congr fun w => hstep3 w)) ?_
  exact le_trans hstep4 hstep5

/-- **The `H`-ball average can be removed (uniform in `ξ'`).**  The constant is the one supplied by
`Commons.Measure.Integral.ballTent_growth_lintegral_le_C0`, hence independent of `ξ'`, of the
dimension and of the data. -/
theorem lintegral_ballTent_shift_le'_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {A A' C₀ : ℝ} (hA : 0 < A) (hC₀ : 0 ≤ C₀)
    (hA' : A + (l : ℝ) < A') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ξ' : ℝ}, ξ' ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (C2 ΦI H : E k → ℝ≥0∞), Measurable C2 → Measurable ΦI →
      Measurable H → ∀ (r : ℝ), 0 < r →
      (∀ (z : E k) (w : E l), C2 (z - projEmbedLin k l (torsionVec k l hlk ξ') w)
          ≤ ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) * C2 z) →
      (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t))
          * (∫⁻ w : E l, ballTent l A' 0 r w
              * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w)))
        ≤ ENNReal.ofReal C * ∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t := by
  obtain ⟨Cg, hCg0, hCg⟩ := Commons.Measure.Integral.ballTent_growth_lintegral_le_C0
    (n := l) (A := A') (B := A) hA.le hA' C₀ hC₀
  obtain ⟨C', hC'0, hC'⟩ := lintegral_ballTent_shift_le_uniform hk hl hlk hA hC₀ hCg0
    (fun r hr => by
      have h1 : (∫⁻ w : E l, ballTent l A' 0 r w * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A))
          = ∫⁻ w : E l, (ENNReal.ofReal (volume (Metric.ball (0 : E l) r)).toReal)⁻¹
              * ENNReal.ofReal ((1 + Metric.infDist w (Metric.ball (0 : E l) r) / r) ^ (-A'))
              * ENNReal.ofReal ((1 + C₀ * ‖w‖ / r) ^ A) := by
        refine lintegral_congr fun w => ?_
        rw [ballTent_apply]
      rw [h1]
      exact hCg r hr)
  refine ⟨C', hC'0, ?_⟩
  intro ξ' hξ' C2 ΦI H hC2 hΦI hH r hr hshift
  exact hC' (ξ' := ξ') hξ' C2 ΦI H hC2 hΦI hH r hr hshift

theorem lintegral_W_mul_tentNorm_le_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {A : ℝ} (hA : gaugeExp k + (l : ℝ) < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N m M m' : ℕ} (hmM : m ≤ M) (hMN : M ≤ N) (h2M : 2 ≤ M)
      {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
      (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
      (J : Fin (2 ^ M)), J ∈ subBlkLvl m M q →
      ∀ (f : Fin (2 ^ N) → E k → ℂ), (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      (∫⁻ t : E k, (∫⁻ z : E k, asymC2 k hk l N m' q' f z
          * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t))
        * tentNorm l A 0 (hBallR k l m') (fun y : E l =>
            ∑ i ∈ blkFin N M J,
              f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y)))
      ≤ ENNReal.ofReal C * asymLHS k hk l N M m' J q' f := by
  have hr1 : (1 : ℝ) ≤ plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    nlinarith
  obtain ⟨CA1, hCA10, hCA1⟩ := convPow_platePhi_le_of_plate_uni (k := k) hk hr1
  have hge0 : (0 : ℝ) < gaugeExp k := lt_of_le_of_lt (Nat.cast_nonneg k) (gaugeExp_gt hk)
  obtain ⟨C₀, hC₀0, hC₀⟩ := asymC2_shift_le_uniform hk hl hlk
  obtain ⟨Cr, hCr0, hCr⟩ := lintegral_ballTent_shift_le'_uniform (k := k) (l := l) hk hl hlk
    (A := gaugeExp k) (A' := A) (C₀ := C₀) hge0 hC₀0 hA
  refine ⟨Cr * CA1, mul_nonneg hCr0 hCA10, ?_⟩
  intro N m M m' hmM hMN h2M ξ' hξ' q q' hsep' J hJ f hf
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
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
    fun z w => hC₀ (ξ' := ξ') hξ' q' hsep' hr0 le_rfl f z w
  have hstep : (∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t))
        * (∫⁻ w : E l, ballTent l A 0 (hBallR k l m') w * H (t + projEmbedLin k l (torsionVec k l hlk ξ') w)))
      ≤ ENNReal.ofReal Cr * ∫⁻ t : E k, (∫⁻ z : E k, C2 z * ΦI (z - t)) * H t :=
    hCr (ξ' := ξ') hξ' C2 ΦI H hC2m hΦIm hHm (hBallR k l m') hr0 hC₀'
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

theorem curveDec_tower_uniform {l : ℕ} (hl : 1 ≤ l)
    {a : ℝ} (ha1 : 1 ≤ a) {εm : ℝ} (hεm : 0 < εm) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ → ℝ → E l)
      {A cT R : ℝ} (hbd : CurveBounded l D A) (hA : 1 ≤ A) (htor : CurveTorsion l D cT)
      (hcT : 0 < cT) (htay : CurveTaylor l D R) (hR : 0 ≤ R)
      {Λ : ℝ} (hΛ : 1 ≤ Λ)
      {εt Λ₁ : ℝ} (hεt : 0 < εt) (hΛ₁ : Λ * (1 + εt) * Ctube l ≤ Λ₁)
      (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ εt * tubeCG l A cT)
      (hmod : ∀ M : ℕ, 1 ≤ M → DecLinScale l M Λ₁ (ENNReal.ofReal (a * (M : ℝ) ^ εm)))
      {m : ℕ} (hm : 4 ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
      (hδΛ : δ ≤ Λ / (2 * (m : ℝ)))
      {f : Fin m → E l → ℂ}
      (hf : ∀ i, IsFourierRep l (curvePlate l D δ (pieceCenter m i)) (f i)),
      lpNorm l (pE l) (fun x => ∑ i, f i x)
        ≤ ENNReal.ofReal C * (m : ℝ≥0∞) ^ (2 * εm) * l2Norm (fun i => lpNorm l (pE l) (f i)) := by
  classical
  obtain ⟨Cabs, hCabs, habs⟩ := Commons.Analysis.Asymptotics.pow_const_le_mul_rpow
    (a := max 1 a) (b := εm) (le_max_left 1 a) hεm (L := 2 * (l : ℝ) + 1) (by positivity)
  refine ⟨3 * Cabs, by positivity, ?_⟩
  intro D A cT R hbd hA htor hcT htay hR Λ hΛ εt Λ₁ hεt hΛ₁ ha hmod m hm δ hδ0 hδ1 hδΛ f hf
  have hm0 : 0 < m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  -- the curve constants
  have hCt2 : (2 : ℝ) ≤ Ctube l := by
    rw [Ctube]
    have h3 : (1 : ℝ) ≤ (l : ℝ) * (l.factorial : ℝ) := by
      have h4 : (1 : ℕ) ≤ l * l.factorial := by
        have h5 : 1 ≤ l := hl
        have h6 : 1 ≤ l.factorial := Nat.factorial_pos l
        nlinarith
      exact_mod_cast h4
    linarith
  -- the tower reaches the fine level
  have h0 : 2 ≤ towerN l m 1 := by
    rw [towerN_succ, towerN_zero, towerNext]
    rw [if_pos (by omega)]
    by_cases h2 : 1 * lvlStep l 1 ≤ m
    · rw [if_pos h2]
      simpa using lvlStep_two_le l 1
    · rw [if_neg h2]
      omega
  obtain ⟨K, hK, hmK⟩ := Commons.Combinatorics.LevelBlocks.pow_step_reaches_half (l := l) hl hm
    (n := fun j => towerN l m (j + 1)) h0 (fun j hj => towerN_growth hl hm (j + 1) hj)
  -- the per-step bound
  have hbound : ∀ j : ℕ, lvl2 l m (towerN l m j) f
      ≤ ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm)
        * lvl2 l m (towerN l m (j + 1)) f := by
    intro j
    set M : ℕ := towerN l m (j + 1) / towerN l m j with hM
    have hn1 : 1 ≤ towerN l m j := one_le_towerN l m j
    have hMpos : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h0M | h0M
      · exfalso
        have h1 := towerN_mul_div l m j
        rw [← hM, h0M, mul_zero] at h1
        have := one_le_towerN l m (j + 1)
        omega
      · exact h0M
    have hMtower : towerN l m j * M = towerN l m (j + 1) := by
      rw [hM]
      exact towerN_mul_div l m j
    have hδ1' : δ ≤ Λ / (2 * ((towerN l m j * M : ℕ) : ℝ)) := by
      rw [hMtower]
      have ht : (0 : ℝ) < (towerN l m (j + 1) : ℕ) := by
        exact_mod_cast one_le_towerN l m (j + 1)
      have hle : Λ / (2 * (m : ℝ)) ≤ Λ / (2 * ((towerN l m (j + 1) : ℕ) : ℝ)) := by
        apply div_le_div_of_nonneg_left (le_trans zero_le_one hΛ)
        · positivity
        · have h2 : (towerN l m (j + 1) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast towerN_le l m (j + 1) hm1
          linarith
      exact le_trans hδΛ hle
    have hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * ((towerN l m j : ℕ) : ℝ) := by
      have hMle : M ≤ max 1 (lvlStep l (towerN l m j)) := by
        rw [hM]
        exact towerN_div_le l m j
      rcases lt_or_ge 1 M with hM2 | hM1
      · have hMle' : M ≤ lvlStep l (towerN l m j) := by
          rcases le_max_iff.mp hMle with h | h
          · omega
          · exact h
        have hlvl : (lvlStep l (towerN l m j)) ^ l ≤ 2 ^ l * towerN l m j :=
          lvlStep_pow_le hl hn1
        have hreal : (M : ℝ) ^ l ≤ (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by
          have h1 : (M : ℝ) ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) := by exact_mod_cast hMle'
          have h2 : (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l :=
            pow_le_pow_left₀ (by positivity) h1 l
          have h3 : (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ)
              ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := by exact_mod_cast hlvl
          calc (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l := h2
            _ = (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := h3
            _ = (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by push_cast; ring
        exact hreal.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) hCt2 l) (by positivity))
      · have h1 : M = 1 := le_antisymm hM1 hMpos
        rw [h1, Nat.cast_one, one_pow]
        have hn1' : (1 : ℝ) ≤ (towerN l m j : ℕ) := by exact_mod_cast hn1
        have hCt1 : (1 : ℝ) ≤ (Ctube l) ^ l := one_le_pow₀ (le_trans (by norm_num) hCt2)
        nlinarith
    have hstep := lvl2_step (l := l) hl D hbd hA htor hcT htay hR hm0 hn1 hMpos
      hΛ hεt hΛ₁ (hmod M hMpos) hδ0 hδ1 hδ1' ha hb (fun i => hf i)
    rwa [hMtower] at hstep
  -- the telescoping of the product of constants
  have hprod : ∀ J : ℕ, (∏ j ∈ Finset.range J,
        ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
      = ENNReal.ofReal (a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm) := by
    intro J
    induction J with
    | zero =>
        rw [Finset.prod_range_zero, towerN_zero]
        simp
    | succ J ih =>
        have hnn : (0 : ℝ) ≤ a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm :=
          mul_nonneg (pow_nonneg (by linarith [ha1]) J) (Real.rpow_nonneg (by positivity) εm)
        rw [Finset.prod_range_succ, ih, ← ENNReal.ofReal_mul hnn]
        congr 1
        have hM := towerN_mul_div l m J
        have hcast : ((towerN l m (J + 1) : ℕ) : ℝ)
            = (towerN l m J : ℝ) * ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, towerN_mul_div]
        have htJ : (0 : ℝ) < (towerN l m J : ℕ) := by
          exact_mod_cast one_le_towerN l m J
        have htm : (0 : ℝ) < ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (towerN l m (J + 1) / towerN l m J) with h0M | h0M
          · exfalso
            have h1 : towerN l m J * (towerN l m (J + 1) / towerN l m J) = towerN l m (J + 1) :=
              towerN_mul_div l m J
            rw [h0M, mul_zero] at h1
            have h2 := one_le_towerN l m (J + 1)
            omega
          · exact_mod_cast h0M
        rw [hcast, Real.mul_rpow htJ.le htm.le, pow_succ']
        ring
  -- the chain
  have hchain := lvl2_chain (l := l) (m := m) f (n := fun j => towerN l m j)
    (C := fun j => ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
    (towerN_zero l m) hbound (K + 1)
  rw [hprod (K + 1)] at hchain
  -- the product bound
  have hpb : ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
      ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) := by
    apply ENNReal.ofReal_le_ofReal
    have hlog1 : (1 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) + 1 := by
      have h4 : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
      have h5 : (1 : ℝ) ≤ Real.log (m : ℝ) + 2 := by linarith
      have h6 : (0 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) := Real.log_nonneg h5
      linarith
    have hK' : ((K + 1 : ℕ) : ℝ)
        ≤ 2 + (2 * (l : ℝ) + 1) * (Real.log (Real.log (m : ℝ) + 2) + 1) := by
      have h1 : ((K : ℕ) : ℝ) ≤ 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) := hK
      have hL0 : (0 : ℝ) ≤ 2 * (l : ℝ) := by positivity
      push_cast
      nlinarith [h1, hL0, hlog1]
    have h1 : a ^ (K + 1) ≤ Cabs * (m : ℝ) ^ εm := by
      calc a ^ (K + 1) ≤ (max 1 a) ^ (K + 1) :=
            pow_le_pow_left₀ (by positivity) (le_max_right 1 a) _
        _ ≤ Cabs * (m : ℝ) ^ εm := habs (K + 1) m (by omega) hK'
    have h2 : ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm ≤ (m : ℝ) ^ εm := by
      refine Real.rpow_le_rpow (by positivity) ?_ hεm.le
      exact_mod_cast towerN_le l m (K + 1) hm1
    have h3 : (m : ℝ) ^ εm * (m : ℝ) ^ εm = (m : ℝ) ^ (2 * εm) := by
      rw [← Real.rpow_add (by exact_mod_cast hm0)]
      ring_nf
    calc a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm
        ≤ (Cabs * (m : ℝ) ^ εm) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Cabs * (m : ℝ) ^ εm) * (m : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cabs * (m : ℝ) ^ (2 * εm) := by rw [← h3]; ring
  -- the final comparison
  have hfin : lvl2 l m (towerN l m (K + 1)) f
      ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f :=
    lvl2_le_self (l := l) hl hm0 (one_le_towerN l m (K + 1)) hmK
      (fun i => (hf i).aestronglyMeasurable)
  have hcomb : lvl2 l m 1 f
      ≤ (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f := by
    calc lvl2 l m 1 f
        ≤ ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
            * lvl2 l m (towerN l m (K + 1)) f := hchain
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * lvl2 l m (towerN l m (K + 1)) f :=
          mul_le_mul_of_nonneg_right hpb (by simp)
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm))
            * ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f) :=
          mul_le_mul_of_nonneg_left hfin (by simp)
      _ = (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * lvl2 l m m f := by ring
  rw [lvl2_one] at hcomb
  refine hcomb.trans ?_
  have hob : (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
    have h3 : (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (3 : ℝ≥0∞) := by
      calc (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt 3) := by
            rw [Real.sqrt_eq_rpow, show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by simp,
              ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (3 : ℝ) := ENNReal.ofReal_le_ofReal (by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3])
        _ = (3 : ℝ≥0∞) := by simp
    calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        = (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
          norm_num
      _ ≤ (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * 3 :=
          mul_le_mul_of_nonneg_left h3 (by simp)
      _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
          have h3e : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by simp
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), h3e]
          ring
  calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f
      ≤ (ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)) * lvl2 l m m f :=
        mul_le_mul_of_nonneg_right hob (by simp)
    _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)
          * l2Norm (fun i => lpNorm l (pE l) (f i)) := by rw [lvl2_self]

theorem curveDec_towerM_uniform {l : ℕ} (hl : 1 ≤ l)
    {a : ℝ} (ha1 : 1 ≤ a) {εm : ℝ} (hεm : 0 < εm) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ → ℝ → E l)
      {ct R : ℝ} (hct : 0 < ct) (hlow : PlateLower l D ct)
      (htay : CurveTaylorTop l D R) (hR : 0 ≤ R)
      {Λ : ℝ} (hΛ : 1 ≤ Λ)
      {εt Λ₁ : ℝ} (hεt : 0 < εt) (hΛ₁ : Λ * (1 + εt) * Ctube l ≤ Λ₁)
      (ha : 2 * (2 ^ (l + 1) * R * ((l : ℝ) + 1) * Λ ^ (l + 1)) ≤ εt * tubeCGP l ct)
      (hmod : ∀ M : ℕ, 1 ≤ M → DecLinScale l M Λ₁ (ENNReal.ofReal (a * (M : ℝ) ^ εm)))
      {m : ℕ} (hm : 4 ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
      (hδΛ : δ ≤ Λ / (2 * (m : ℝ))) {f : Fin m → E l → ℂ}
      (hf : ∀ i, IsFourierRep l (curvePlate l D δ (pieceCenter m i)) (f i)),
      lpNorm l (pE l) (fun x => ∑ i, f i x)
        ≤ ENNReal.ofReal C * (m : ℝ≥0∞) ^ (2 * εm) * l2Norm (fun i => lpNorm l (pE l) (f i)) := by
  classical
  obtain ⟨Cabs, hCabs, habs⟩ := Commons.Analysis.Asymptotics.pow_const_le_mul_rpow
    (a := max 1 a) (b := εm) (le_max_left 1 a) hεm (L := 2 * (l : ℝ) + 1) (by positivity)
  refine ⟨3 * Cabs, by positivity, ?_⟩
  intro D ct R hct hlow htay hR Λ hΛ εt Λ₁ hεt hΛ₁ ha hmod m hm δ hδ0 hδ1 hδΛ f hf
  have hm0 : 0 < m := by omega
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  -- the curve constants
  have hCt2 : (2 : ℝ) ≤ Ctube l := by
    rw [Ctube]
    have h3 : (1 : ℝ) ≤ (l : ℝ) * (l.factorial : ℝ) := by
      have h4 : (1 : ℕ) ≤ l * l.factorial := by
        have h5 : 1 ≤ l := hl
        have h6 : 1 ≤ l.factorial := Nat.factorial_pos l
        nlinarith
      exact_mod_cast h4
    linarith
  -- the tower reaches the fine level
  have h0 : 2 ≤ towerN l m 1 := by
    rw [towerN_succ, towerN_zero, towerNext]
    rw [if_pos (by omega)]
    by_cases h2 : 1 * lvlStep l 1 ≤ m
    · rw [if_pos h2]
      simpa using lvlStep_two_le l 1
    · rw [if_neg h2]
      omega
  obtain ⟨K, hK, hmK⟩ := Commons.Combinatorics.LevelBlocks.pow_step_reaches_half (l := l) hl hm
    (n := fun j => towerN l m (j + 1)) h0 (fun j hj => towerN_growth hl hm (j + 1) hj)
  -- the per-step bound
  have hbound : ∀ j : ℕ, lvl2 l m (towerN l m j) f
      ≤ ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm)
        * lvl2 l m (towerN l m (j + 1)) f := by
    intro j
    set M : ℕ := towerN l m (j + 1) / towerN l m j with hM
    have hn1 : 1 ≤ towerN l m j := one_le_towerN l m j
    have hMpos : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h0M | h0M
      · exfalso
        have h1 := towerN_mul_div l m j
        rw [← hM, h0M, mul_zero] at h1
        have := one_le_towerN l m (j + 1)
        omega
      · exact h0M
    have hMtower : towerN l m j * M = towerN l m (j + 1) := by
      rw [hM]
      exact towerN_mul_div l m j
    have hδ1' : δ ≤ Λ / (2 * ((towerN l m j * M : ℕ) : ℝ)) := by
      rw [hMtower]
      have ht : (0 : ℝ) < (towerN l m (j + 1) : ℕ) := by
        exact_mod_cast one_le_towerN l m (j + 1)
      have hle : Λ / (2 * (m : ℝ)) ≤ Λ / (2 * ((towerN l m (j + 1) : ℕ) : ℝ)) := by
        apply div_le_div_of_nonneg_left (le_trans zero_le_one hΛ)
        · positivity
        · have h2 : (towerN l m (j + 1) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast towerN_le l m (j + 1) hm1
          linarith
      exact le_trans hδΛ hle
    have hb : (M : ℝ) ^ l ≤ (Ctube l) ^ l * ((towerN l m j : ℕ) : ℝ) := by
      have hMle : M ≤ max 1 (lvlStep l (towerN l m j)) := by
        rw [hM]
        exact towerN_div_le l m j
      rcases lt_or_ge 1 M with hM2 | hM1
      · have hMle' : M ≤ lvlStep l (towerN l m j) := by
          rcases le_max_iff.mp hMle with h | h
          · omega
          · exact h
        have hlvl : (lvlStep l (towerN l m j)) ^ l ≤ 2 ^ l * towerN l m j :=
          lvlStep_pow_le hl hn1
        have hreal : (M : ℝ) ^ l ≤ (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by
          have h1 : (M : ℝ) ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) := by exact_mod_cast hMle'
          have h2 : (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l :=
            pow_le_pow_left₀ (by positivity) h1 l
          have h3 : (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ)
              ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := by exact_mod_cast hlvl
          calc (M : ℝ) ^ l ≤ ((lvlStep l (towerN l m j) : ℕ) : ℝ) ^ l := h2
            _ = (((lvlStep l (towerN l m j)) ^ l : ℕ) : ℝ) := by push_cast; ring
            _ ≤ ((2 ^ l * towerN l m j : ℕ) : ℝ) := h3
            _ = (2 : ℝ) ^ l * ((towerN l m j : ℕ) : ℝ) := by push_cast; ring
        exact hreal.trans (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by norm_num) hCt2 l) (by positivity))
      · have h1 : M = 1 := le_antisymm hM1 hMpos
        rw [h1, Nat.cast_one, one_pow]
        have hn1' : (1 : ℝ) ≤ (towerN l m j : ℕ) := by exact_mod_cast hn1
        have hCt1 : (1 : ℝ) ≤ (Ctube l) ^ l := one_le_pow₀ (le_trans (by norm_num) hCt2)
        nlinarith
    have hstep := lvl2_stepM (l := l) hl D hct hlow htay hR hm0 hn1 hMpos
      hΛ hεt hΛ₁ (hmod M hMpos) hδ0 hδ1 hδ1' ha hb (fun i => hf i)
    rwa [hMtower] at hstep
  -- the telescoping of the product of constants
  have hprod : ∀ J : ℕ, (∏ j ∈ Finset.range J,
        ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
      = ENNReal.ofReal (a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm) := by
    intro J
    induction J with
    | zero =>
        rw [Finset.prod_range_zero, towerN_zero]
        simp
    | succ J ih =>
        have hnn : (0 : ℝ) ≤ a ^ J * ((towerN l m J : ℕ) : ℝ) ^ εm :=
          mul_nonneg (pow_nonneg (by linarith [ha1]) J) (Real.rpow_nonneg (by positivity) εm)
        rw [Finset.prod_range_succ, ih, ← ENNReal.ofReal_mul hnn]
        congr 1
        have hM := towerN_mul_div l m J
        have hcast : ((towerN l m (J + 1) : ℕ) : ℝ)
            = (towerN l m J : ℝ) * ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rw [← Nat.cast_mul, towerN_mul_div]
        have htJ : (0 : ℝ) < (towerN l m J : ℕ) := by
          exact_mod_cast one_le_towerN l m J
        have htm : (0 : ℝ) < ((towerN l m (J + 1) / towerN l m J : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (towerN l m (J + 1) / towerN l m J) with h0M | h0M
          · exfalso
            have h1 : towerN l m J * (towerN l m (J + 1) / towerN l m J) = towerN l m (J + 1) :=
              towerN_mul_div l m J
            rw [h0M, mul_zero] at h1
            have h2 := one_le_towerN l m (J + 1)
            omega
          · exact_mod_cast h0M
        rw [hcast, Real.mul_rpow htJ.le htm.le, pow_succ']
        ring
  -- the chain
  have hchain := lvl2_chain (l := l) (m := m) f (n := fun j => towerN l m j)
    (C := fun j => ENNReal.ofReal (a * ((towerN l m (j + 1) / towerN l m j : ℕ) : ℝ) ^ εm))
    (towerN_zero l m) hbound (K + 1)
  rw [hprod (K + 1)] at hchain
  -- the product bound
  have hpb : ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
      ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) := by
    apply ENNReal.ofReal_le_ofReal
    have hlog1 : (1 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) + 1 := by
      have h4 : (0 : ℝ) ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
      have h5 : (1 : ℝ) ≤ Real.log (m : ℝ) + 2 := by linarith
      have h6 : (0 : ℝ) ≤ Real.log (Real.log (m : ℝ) + 2) := Real.log_nonneg h5
      linarith
    have hK' : ((K + 1 : ℕ) : ℝ)
        ≤ 2 + (2 * (l : ℝ) + 1) * (Real.log (Real.log (m : ℝ) + 2) + 1) := by
      have h1 : ((K : ℕ) : ℝ) ≤ 2 + 2 * (l : ℝ) * (Real.log (Real.log (m : ℝ) + 2) + 1) := hK
      have hL0 : (0 : ℝ) ≤ 2 * (l : ℝ) := by positivity
      push_cast
      nlinarith [h1, hL0, hlog1]
    have h1 : a ^ (K + 1) ≤ Cabs * (m : ℝ) ^ εm := by
      calc a ^ (K + 1) ≤ (max 1 a) ^ (K + 1) :=
            pow_le_pow_left₀ (by positivity) (le_max_right 1 a) _
        _ ≤ Cabs * (m : ℝ) ^ εm := habs (K + 1) m (by omega) hK'
    have h2 : ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm ≤ (m : ℝ) ^ εm := by
      refine Real.rpow_le_rpow (by positivity) ?_ hεm.le
      exact_mod_cast towerN_le l m (K + 1) hm1
    have h3 : (m : ℝ) ^ εm * (m : ℝ) ^ εm = (m : ℝ) ^ (2 * εm) := by
      rw [← Real.rpow_add (by exact_mod_cast hm0)]
      ring_nf
    calc a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm
        ≤ (Cabs * (m : ℝ) ^ εm) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (Cabs * (m : ℝ) ^ εm) * (m : ℝ) ^ εm :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cabs * (m : ℝ) ^ (2 * εm) := by rw [← h3]; ring
  -- the final comparison
  have hfin : lvl2 l m (towerN l m (K + 1)) f
      ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f :=
    lvl2_le_self (l := l) hl hm0 (one_le_towerN l m (K + 1)) hmK
      (fun i => (hf i).aestronglyMeasurable)
  have hcomb : lvl2 l m 1 f
      ≤ (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f := by
    calc lvl2 l m 1 f
        ≤ ENNReal.ofReal (a ^ (K + 1) * ((towerN l m (K + 1) : ℕ) : ℝ) ^ εm)
            * lvl2 l m (towerN l m (K + 1)) f := hchain
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * lvl2 l m (towerN l m (K + 1)) f :=
          mul_le_mul_of_nonneg_right hpb (by simp)
      _ ≤ ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm))
            * ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * lvl2 l m m f) :=
          mul_le_mul_of_nonneg_left hfin (by simp)
      _ = (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * lvl2 l m m f := by ring
  rw [lvl2_one] at hcomb
  refine hcomb.trans ?_
  have hob : (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
    have h3 : (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤ (3 : ℝ≥0∞) := by
      calc (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt 3) := by
            rw [Real.sqrt_eq_rpow, show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by simp,
              ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
        _ ≤ ENNReal.ofReal (3 : ℝ) := ENNReal.ofReal_le_ofReal (by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3])
        _ = (3 : ℝ≥0∞) := by simp
    calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        = (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
          norm_num
      _ ≤ (ENNReal.ofReal Cabs * (m : ℝ≥0∞) ^ (2 * εm)) * 3 :=
          mul_le_mul_of_nonneg_left h3 (by simp)
      _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm) := by
          have h3e : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by simp
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), h3e]
          ring
  calc (ENNReal.ofReal (Cabs * (m : ℝ) ^ (2 * εm)) * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ))
        * lvl2 l m m f
      ≤ (ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)) * lvl2 l m m f :=
        mul_le_mul_of_nonneg_right hob (by simp)
    _ = ENNReal.ofReal (3 * Cabs) * (m : ℝ≥0∞) ^ (2 * εm)
          * l2Norm (fun i => lpNorm l (pE l) (f i)) := by rw [lvl2_self]

theorem curveDec_intervalCurve_proj_uniform {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k)
    {a₀ εm : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
      {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
      (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
        PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
      (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
      {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) (h4 : 4 ≤ 2 ^ (M - m))
      (q : Fin (2 ^ m))
      (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
      {lam' : ℝ} (hlam'1 : 1 ≤ lam') (hlam'2 : lam' ≤ (2 : ℝ) ^ (M - m))
      (hmMod : ∀ M' : ℕ, 1 ≤ M' →
        DecLinScale l M' (towerEnlP l cL R lam')
          (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))),
      CurveDec l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ')))
        (2 ^ (M - m)) lam' (K * (((2 ^ (M - m) : ℕ) : ℝ≥0∞)) ^ (2 * εm)) := by
  obtain ⟨C₀, hC₀⟩ := curveDec_towerM_uniform (l := l) hl ha1 hεm
  refine ⟨ENNReal.ofReal C₀, ENNReal.ofReal_ne_top, ?_⟩
  intro ξ' hξ' cL R hcL hR hplate htay m M hm hmM h4 q hsepI lam' hlam'1 hlam'2 hmMod
  set cc : ℝ := 1 / (2 : ℝ) ^ m with hcc
  set aa : ℝ := ((q : ℕ) : ℝ) / (2 : ℝ) ^ m with haa
  set Dp : ℕ → ℝ → E l := projCurveDeriv k l (torsionVec k l hlk ξ') with hDp
  set DI : ℕ → ℝ → E l := intervalCurve l aa cc Dp with hDI
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc ≤ 1 := by
    rw [hcc, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have haa0 : 0 ≤ aa := by rw [haa]; positivity
  have hac : aa + cc ≤ 1 := by
    rw [haa, hcc, ← add_div, div_le_one (by positivity)]
    have hq : (q : ℕ) + 1 ≤ 2 ^ m := q.isLt
    have hcast : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hq
    rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring] at hcast
    linarith
  have hmtR : ((2 ^ (M - m) : ℕ) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
  -- the anisotropic torsion of `D_I`
  have hplow : PlateLower l DI (cL * cc ^ l) := by
    refine plateLower_intervalCurve hcL hcc0 hcc1 (fun σ hσ => ?_)
    exact hplate _ ⟨by nlinarith [hσ.1, haa0, hcc0.le], by nlinarith [hσ.2, hcc0.le, hac]⟩
      (hsepI σ hσ)
  -- the sharp Taylor bound of `D_I`
  have htayI : CurveTaylorTop l DI (R * cc ^ (l + 1)) :=
    curveTaylorTop_intervalCurve_sharp htay hR.le hcc0.le hcc1 haa0 hac
  have htubeCP : 0 < tubeCBP l := tubeCBP_pos hl
  have hden : 0 < tubeCBP l * cL := mul_pos htubeCP hcL
  have heps_pos : 0 < tubeGainP l cL R lam' := by
    rw [tubeGainP]
    refine div_pos ?_ hden
    exact mul_pos (mul_pos (mul_pos (mul_pos (by positivity) hR) (by positivity))
      (pow_pos (lt_of_lt_of_le zero_lt_one hlam'1) _)) (by positivity)
  -- `ha` of the tower is automatic for this gain
  have ha : 2 * (2 ^ (l + 1) * (R * cc ^ (l + 1)) * ((l : ℝ) + 1) * lam' ^ (l + 1))
      ≤ tubeGainP l cL R lam' * tubeCGP l (cL * cc ^ l) := by
    have hne : tubeCBP l * cL ≠ 0 := ne_of_gt hden
    have heq : tubeGainP l cL R lam' * tubeCGP l (cL * cc ^ l)
        = 2 ^ (l + 2) * R * ((l : ℝ) + 1) * lam' ^ (l + 1) * cc ^ l := by
      rw [tubeGainP, tubeCGP]
      field_simp
    rw [heq]
    have h2 : 2 * (2 ^ (l + 1) * (R * cc ^ (l + 1)) * ((l : ℝ) + 1) * lam' ^ (l + 1))
        = 2 ^ (l + 2) * R * ((l : ℝ) + 1) * lam' ^ (l + 1) * cc ^ (l + 1) := by ring
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc cc ^ (l + 1) = cc ^ l * cc := by rw [pow_succ]
      _ ≤ cc ^ l * 1 := mul_le_mul_of_nonneg_left hcc1 (pow_pos hcc0 l).le
      _ = cc ^ l := mul_one _
  -- the tower
  set mt : ℕ := 2 ^ (M - m) with hmt
  have hmt4 : 4 ≤ mt := by rw [hmt]; exact h4
  have hmtR' : (mt : ℝ) = (2 : ℝ) ^ (M - m) := by rw [hmt]; exact hmtR
  have hδ0 : 0 < lam' / (2 * (mt : ℝ)) := by
    have : (0 : ℝ) < (mt : ℝ) := by rw [hmtR']; positivity
    positivity
  have hδ1 : lam' / (2 * (mt : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h3 : lam' ≤ (mt : ℝ) := by rw [hmtR']; exact hlam'2
    linarith
  have hdec : ∀ {f : Fin (2 ^ (M - m)) → E l → ℂ},
      (∀ i, IsFourierRep l (curvePlate l DI (lam' / (2 * ((2 ^ (M - m) : ℕ) : ℝ)))
        (pieceCenter (2 ^ (M - m)) i)) (f i)) →
      lpNorm l (pE l) (fun x => ∑ i, f i x)
        ≤ ENNReal.ofReal C₀ * (((2 ^ (M - m) : ℕ) : ℝ≥0∞)) ^ (2 * εm)
          * l2Norm (fun i => lpNorm l (pE l) (f i)) :=
    hC₀.2 DI (ct := cL * cc ^ l) (R := R * cc ^ (l + 1)) (mul_pos hcL (pow_pos hcc0 l)) hplow htayI
      (mul_nonneg hR.le (pow_nonneg hcc0.le _))
      (Λ := lam') hlam'1 (εt := tubeGainP l cL R lam') (Λ₁ := towerEnlP l cL R lam')
      heps_pos (le_of_eq rfl) ha hmMod
      (m := 2 ^ (M - m)) hmt4 (δ := lam' / (2 * (((2 ^ (M - m) : ℕ) : ℝ)))) hδ0 hδ1 le_rfl
  exact fun f hf => hdec hf

theorem curveDecLocR_of_curveDec_uniform {l : ℕ} (hl : 1 ≤ l) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (D : ℕ → ℝ → E l) {m : ℕ} (hm : 1 ≤ m)
      {lam lam' ρ : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ) {R₀ : ℝ} (hR0 : (m : ℝ) ^ l ≤ R₀)
      (hρlR : (2 : ℝ) ^ (l + 2) ≤ ρ * (R₀ / (m : ℝ) ^ l) * lam ^ l)
      (hrad : ∀ j : Fin m, Metric.ball (D 0 (pieceCenter m j)) (ρ * (lam / (2 * m)) ^ l)
                ⊆ curvePlate l D (lam / (2 * m)) (pieceCenter m j))
      {C : ℝ≥0∞} (hdec : CurveDec l D m lam' C) (hlam' : 2 * lam ≤ lam'),
      CurveDecLocR l D m lam A R₀ (C * K) := by
  have hp : 0 < plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hpnn : 0 ≤ plExp l := hp.le
  have hpA : 0 ≤ A / plExp l := div_nonneg hA hpnn
  obtain ⟨Cb, hCb, hbump0⟩ :=
    Commons.Analysis.Fourier.exists_ball_bump_uniform l hl (A / plExp l) hpA
  refine ⟨ENNReal.ofReal (2 * Cb), ENNReal.ofReal_ne_top, ?_⟩
  intro D m hm lam lam' ρ hlam hρ R₀ hR0 hρlR hrad C hdec hlam'
  intro f hf c R hR
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_trans (one_le_pow₀ hm1) hR0) hR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  obtain ⟨σ, ψ₀, Φ, hσpos, hσR, hΦmeas, hΦint, hΦsupp, hrep, hlow, hdecay⟩ := hbump0 R hR1
  obtain ⟨ψ, hψclass, hψlow, hψdec⟩ :=
    ball_bump_translate (c := c) hR1 hpA hCb.le hσpos hΦmeas hΦint hΦsupp hrep hlow hdecay
  set g : E l → ℂ := fun x => ∑ j, f j x with hg
  set h : E l → ℂ := fun x => ∑ j, f j x * ψ x with hh
  have hgh : ∀ x, h x = g x * ψ x := by
    intro x
    simp only [hh, hg, Finset.sum_mul]
  -- classes of the multiplied pieces
  have hclass : ∀ j : Fin m, IsFourierRep l (curvePlate l D (lam' / (2 * m)) (pieceCenter m j))
      (fun x => f j x * ψ x) := fun j =>
    isFourierRep_mul_ball_bumpR hl D hm hlam hρ hρlR hrad hlam' (j := j)
      (σ := σ) (R₀ := R₀)
      (le_trans (mul_le_mul_of_nonneg_left hR hσpos.le) hσR) hR0 hψclass (hf j)
  -- the decoupling inequality
  have hdec' : lpNorm l (pE l) h
      ≤ C * l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x)) := by
    have h1 := hdec (fun j => fun x => f j x * ψ x) hclass
    simpa only [hh] using h1
  have hdec2 : (lpNorm l (pE l) h) ^ (plExp l)
      ≤ C ^ (plExp l)
        * (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l) := by
    refine (ENNReal.rpow_le_rpow hdec' hpnn).trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpnn]
  -- the localising step
  have hpoint : ∀ x ∈ Metric.ball c R,
      (‖g x‖₊ : ℝ≥0∞) ^ (plExp l) ≤ 2 ^ (plExp l) * (‖h x‖₊ : ℝ≥0∞) ^ (plExp l) := by
    intro x hx
    have hx' : ‖x - c‖ ≤ R := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      exact hx.le
    have hψ1 : (1 / 2 : ℝ) ≤ ‖ψ x‖ := hψlow x hx'
    have h1 : ‖g x‖ ≤ 2 * ‖h x‖ := by
      have h2 : ‖h x‖ = ‖g x‖ * ‖ψ x‖ := by rw [hgh x, norm_mul]
      have h3 : ‖g x‖ * (1 / 2 : ℝ) ≤ ‖g x‖ * ‖ψ x‖ :=
        mul_le_mul_of_nonneg_left hψ1 (norm_nonneg _)
      nlinarith [norm_nonneg (g x), norm_nonneg (h x)]
    have h2 : (‖g x‖₊ : ℝ≥0∞) ≤ 2 * (‖h x‖₊ : ℝ≥0∞) := by
      have h3 : (‖g x‖₊ : NNReal) ≤ (2 : NNReal) * ‖h x‖₊ := by
        exact_mod_cast h1
      calc (‖g x‖₊ : ℝ≥0∞) = ((‖g x‖₊ : NNReal) : ℝ≥0∞) := rfl
        _ ≤ (((2 : NNReal) * ‖h x‖₊ : NNReal) : ℝ≥0∞) := by exact_mod_cast h3
        _ = 2 * (‖h x‖₊ : ℝ≥0∞) := by rw [ENNReal.coe_mul]; norm_num
    calc (‖g x‖₊ : ℝ≥0∞) ^ (plExp l) ≤ (2 * (‖h x‖₊ : ℝ≥0∞)) ^ (plExp l) :=
          ENNReal.rpow_le_rpow h2 hpnn
      _ = 2 ^ (plExp l) * (‖h x‖₊ : ℝ≥0∞) ^ (plExp l) :=
          ENNReal.mul_rpow_of_nonneg _ _ hpnn
  have hlocal := ballAvg_le_of_two_mul (p := plExp l) hpoint
  have hlp := lintegral_nnnorm_rpow_eq_lpNorm_pow l hl h
    (Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hclass j).aestronglyMeasurable)
  -- the per-piece bound
  have hj : ∀ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (plExp l)
      ≤ ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          * tentNorm l A c R (f j) := fun j =>
    lpNorm_mul_le_of_decay hl hCb hRpos (fun x => hψdec x) (f := f j)
      (hclass j).aestronglyMeasurable
  -- assembling
  have hsum2 : (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
      ≤ (((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
          ^ (2 / plExp l)) * ∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ)
        = ((lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (plExp l)) ^ (2 / plExp l) := by
          rw [← ENNReal.rpow_mul]
          congr 1
          field_simp
      _ ≤ (((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
            * tentNorm l A c R (f j)) ^ (2 / plExp l) :=
          ENNReal.rpow_le_rpow (hj j) (by positivity)
      _ = ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
            ^ (2 / plExp l) * (tentNorm l A c R (f j)) ^ (2 / plExp l) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
  have hl2 : (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l)
      = (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
          ^ (plExp l / 2) := by
    rw [l2Norm, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hKpow : (((ENNReal.ofReal Cb) ^ (plExp l)
        * ENNReal.ofReal (volume (Metric.ball c R)).toReal) ^ (2 / plExp l))
      ^ (plExp l / 2)
      = (ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal := by
    rw [← ENNReal.rpow_mul]
    rw [show (2 / plExp l) * (plExp l / 2) = 1 by field_simp]
    rw [ENNReal.rpow_one]
  have hBpos : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) c hRpos).ne'
      measure_ball_lt_top.ne
  have hBtop : ENNReal.ofReal (volume (Metric.ball c R)).toReal ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcancel : (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
        * ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal)
      = (ENNReal.ofReal Cb) ^ (plExp l) := by
    rw [mul_comm ((ENNReal.ofReal Cb) ^ (plExp l))
      (ENNReal.ofReal (volume (Metric.ball c R)).toReal),
      ← mul_assoc, ENNReal.inv_mul_cancel hBpos hBtop, one_mul]
  have hconst : 2 ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l) * C ^ (plExp l))
      ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l) := by
    have h1 : (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
        = C ^ (plExp l) * (ENNReal.ofReal (2 * Cb)) ^ (plExp l) :=
      ENNReal.mul_rpow_of_nonneg _ _ hpnn
    have h2 : (ENNReal.ofReal (2 * Cb)) ^ (plExp l)
        = (ENNReal.ofReal 2) ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.mul_rpow_of_nonneg _ _ hpnn]
    have h3 : (ENNReal.ofReal 2 : ℝ≥0∞) = 2 := by norm_num
    rw [h1, h2, h3]
    exact le_of_eq (by ac_rfl)
  calc ballAvg (plExp l) c R g
      ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * ∫⁻ x, (‖h x‖₊ : ℝ≥0∞) ^ (plExp l)) := hlocal
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (lpNorm l (pE l) h) ^ (plExp l)) := by rw [hlp]
    _ ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * (l2Norm (fun j => lpNorm l (pE l) (fun x => f j x * ψ x))) ^ (plExp l))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hdec2)
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * (∑ j : Fin m, (lpNorm l (pE l) (fun x => f j x * ψ x)) ^ (2 : ℝ))
              ^ (plExp l / 2))) := by rw [hl2]
    _ ≤ (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * ((((ENNReal.ofReal Cb) ^ (plExp l)
                * ENNReal.ofReal (volume (Metric.ball c R)).toReal) ^ (2 / plExp l)
                * ∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (ENNReal.rpow_le_rpow hsum2 (by positivity))))
    _ = (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
          * (2 ^ (plExp l) * (C ^ (plExp l)
            * ((ENNReal.ofReal Cb) ^ (plExp l) * ENNReal.ofReal (volume (Metric.ball c R)).toReal
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)))) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hKpow]
    _ = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
          * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)) := by
        have hc := hcancel
        calc (ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
              * (2 ^ (plExp l) * (C ^ (plExp l)
                * ((ENNReal.ofReal Cb) ^ (plExp l)
                  * ENNReal.ofReal (volume (Metric.ball c R)).toReal
                  * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))))
            = 2 ^ (plExp l) * (C ^ (plExp l)
                * (((ENNReal.ofReal (volume (Metric.ball c R)).toReal)⁻¹
                    * ((ENNReal.ofReal Cb) ^ (plExp l)
                      * ENNReal.ofReal (volume (Metric.ball c R)).toReal))
                  * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))) := by
                ring
          _ = 2 ^ (plExp l) * (C ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l)
                * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))) := by
                rw [hc]
          _ = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
                * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2)) := by
                ring
    _ ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
          * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) := by
        have h1 : 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l))
            ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l) := by
          have := hconst
          rwa [show 2 ^ (plExp l) * ((ENNReal.ofReal Cb) ^ (plExp l) * C ^ (plExp l))
              = 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)) from by ring] at this
        calc 2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2))
            = (2 ^ (plExp l) * (C ^ (plExp l) * (ENNReal.ofReal Cb) ^ (plExp l)))
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) := by ring
          _ ≤ (C * ENNReal.ofReal (2 * Cb)) ^ (plExp l)
              * (∑ j : Fin m, (tentNorm l A c R (f j)) ^ (2 / plExp l)) ^ (plExp l / 2) :=
              mul_le_mul' h1 le_rfl

theorem curveDecLocR_intervalCurve_proj_uniform {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k)
    {a₀ εm : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
      {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
      (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
        PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
      (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
      {lam : ℝ} (hlam1 : 1 ≤ lam)
      {m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) (h4 : 4 ≤ 2 ^ (M - m))
      (q : Fin (2 ^ m))
      (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
      (hlam2 : 2 * lam ≤ (2 : ℝ) ^ (M - m))
      {R₀ : ℝ} (hR0 : (((2 ^ (M - m) : ℕ) : ℝ)) ^ l ≤ R₀)
      (hρlR : (2 : ℝ) ^ (l + 2)
        ≤ (cL * (1 / (2 : ℝ) ^ m) ^ l) * (R₀ / (((2 ^ (M - m) : ℕ) : ℝ)) ^ l) * lam ^ l)
      (hmMod : ∀ M' : ℕ, 1 ≤ M' →
        DecLinScale l M' (towerEnlP l cL R (2 * lam))
          (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))),
      CurveDecLocR l
        (intervalCurve l (((q : ℕ) : ℝ) / (2 : ℝ) ^ m) (1 / (2 : ℝ) ^ m)
          (projCurveDeriv k l (torsionVec k l hlk ξ')))
        (2 ^ (M - m)) lam A R₀ (K * (((2 ^ (M - m) : ℕ) : ℝ≥0∞)) ^ (2 * εm)) := by
  obtain ⟨K₀, hK₀top, hK₀⟩ := curveDec_intervalCurve_proj_uniform (k := k) (l := l) hl hlk ha1 hεm
  obtain ⟨K₁, hK₁top, hK₁⟩ := curveDecLocR_of_curveDec_uniform (l := l) hl hA
  refine ⟨K₀ * K₁, ENNReal.mul_ne_top hK₀top hK₁top, ?_⟩
  intro ξ' hξ' cL R hcL hR hplate htay lam hlam1 m M hm hmM h4 q hsepI hlam2 R₀ hR0 hρlR hmMod
  set cc : ℝ := 1 / (2 : ℝ) ^ m with hcc
  set aa : ℝ := ((q : ℕ) : ℝ) / (2 : ℝ) ^ m with haa
  set Dp : ℕ → ℝ → E l := projCurveDeriv k l (torsionVec k l hlk ξ') with hDp
  set DI : ℕ → ℝ → E l := intervalCurve l aa cc Dp with hDI
  set mt : ℕ := 2 ^ (M - m) with hmt
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc ≤ 1 := by
    rw [hcc, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have haa0 : 0 ≤ aa := by rw [haa]; positivity
  have hac : aa + cc ≤ 1 := by
    rw [haa, hcc, ← add_div, div_le_one (by positivity)]
    have hq : (q : ℕ) + 1 ≤ 2 ^ m := q.isLt
    have hcast : ((q : ℕ) : ℝ) + 1 ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hq
    rw [show ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m from by push_cast; ring] at hcast
    linarith
  have hmt4 : 4 ≤ mt := by rw [hmt]; exact h4
  have hmtR : (mt : ℝ) = (2 : ℝ) ^ (M - m) := by rw [hmt]; push_cast; ring
  have hmtpos : (0 : ℝ) < (mt : ℝ) := by rw [hmtR]; positivity
  have hct : 0 < cL * cc ^ l := mul_pos hcL (pow_pos hcc0 l)
  -- the anisotropic torsion of `D_I`
  have hplow : PlateLower l DI (cL * cc ^ l) := by
    refine plateLower_intervalCurve hcL hcc0 hcc1 (fun σ hσ => ?_)
    exact hplate _ ⟨by nlinarith [hσ.1, haa0, hcc0.le], by nlinarith [hσ.2, hcc0.le, hac]⟩
      (hsepI σ hσ)
  -- the global decoupling at the doubled enlargement
  have hC₁ : CurveDec l DI mt (2 * lam) (K₀ * ((mt : ℕ) : ℝ≥0∞) ^ (2 * εm)) := by
    refine hK₀ hξ' hcL hR hplate htay hm hmM h4 q hsepI ?_ hlam2 hmMod
    have h2 : (1 : ℝ) ≤ 2 * lam := by linarith
    exact h2
  -- the ball inside the plate
  have hmtR2 : ((mt : ℕ) : ℝ) ^ l = (((2 ^ (M - m) : ℕ) : ℝ)) ^ l := by rw [hmt]
  have hlamle : lam ≤ (mt : ℝ) := by
    rw [hmtR]; linarith
  have hrad : ∀ j : Fin mt, Metric.ball (DI 0 (pieceCenter mt j))
        ((cL * cc ^ l) * (lam / (2 * mt)) ^ l)
      ⊆ curvePlate l DI (lam / (2 * mt)) (pieceCenter mt j) := by
    intro j
    have hpj : pieceCenter mt j ∈ Set.Icc (0 : ℝ) 1 := pieceCenter_mem_Icc mt (by omega) j
    have hδ0 : 0 < lam / (2 * mt) := by positivity
    have hδ1 : lam / (2 * mt) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    refine ball_subset_curvePlate_of_lower_at (D := DI) (t := pieceCenter mt j) hct
      (fun δ hδ0' hδ1' w => ?_) (lam / (2 * mt)) hδ0 hδ1
    have hw : ‖w‖ ≤ ‖coordVec l w‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      simpa only [coordVec_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (coordVec l w) i
    have h1 : (cL * cc ^ l) * δ ^ l * ‖w‖ ≤ (cL * cc ^ l) * δ ^ l * ‖coordVec l w‖ :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h2 := curvePlateLin_lower_of_plateLowerAt hct (hplow _ hpj) hδ0' hδ1' (coordVec l w)
    rw [curvePlateLin_apply] at h2
    refine h1.trans ?_
    refine h2.trans (le_of_eq ?_)
    have hsum : (∑ i : Fin l, coordVec l w i • (δ ^ (i.val + 1) • DI (i.val + 1) (pieceCenter mt j)))
        = ∑ i : Fin l, w i • (δ ^ (i.val + 1) • DI (i.val + 1) (pieceCenter mt j)) :=
      Finset.sum_congr rfl fun i _ => by rw [coordVec_apply]
    rw [hsum]
  -- Corollary 3.7
  have hK : CurveDecLocR l DI mt lam A R₀
      ((K₀ * ((mt : ℕ) : ℝ≥0∞) ^ (2 * εm)) * K₁) :=
    hK₁ DI (m := mt) (Nat.one_le_iff_ne_zero.mpr (by omega)) (lam := lam) (lam' := 2 * lam)
      (ρ := cL * cc ^ l) (R₀ := R₀)
      hlam1 hct (by rw [hmtR2]; exact hR0) hρlR hrad hC₁ (le_refl (2 * lam))
  intro f hf c R hR
  have h := hK f hf c R hR
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- **Lane 4 at the fixed enlargement `laneLam`, uniform in the tuple and the levels.** -/
theorem asymAV_le_proj_explicit_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hA : 0 ≤ A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {N m M m' : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
      {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
      (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m))
      (hlam2 : 2 * laneLam k l hk hl hlk ≤ (2 : ℝ) ^ (M - m))
      (hm : 1 ≤ m) {r : ℝ} (hrR : hBallR k l m' ≤ r)
      (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) → ∀ u : E k,
      (∫⁻ w in Metric.ball (0 : E l) r,
          (‖∑ i ∈ blkFin N m q,
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
        ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal)
          * (C * (((2 ^ (M - m) : ℕ) : ℝ≥0∞)) ^ (2 * εm)) ^ (plExp l)
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  obtain ⟨C, hCtop, hdec⟩ :=
    curveDecLocR_intervalCurve_proj_uniform (k := k) (l := l) hl hlk ha1 hεm hA
  have hcL : 0 < projCL k l hl hlk := projCL_pos k l hl hlk
  have hR : 0 < projRR k l hl hlk := projRR_pos k l hl hlk
  refine ⟨C, hCtop, ?_⟩
  intro N m M m' h2m hmM hMN ξ' hξ' q hsepI hsep hM h4 hlam2 hm r hrR f hf u
  have hplate := (projConstants_spec k l hl hlk ξ' hξ').1
  have htay := (projConstants_spec k l hl hlk ξ' hξ').2
  have hcast : (((2 ^ (M - m) : ℕ)) : ℝ) = (2 : ℝ) ^ (M - m) := by push_cast; ring
  have hρ : (2 : ℝ) ^ (l + 2) ≤ projCL k l hl hlk * (1 / (2 : ℝ) ^ m) ^ l
      * (hBallR k l m' / (((2 ^ (M - m) : ℕ)) : ℝ) ^ l) * (laneLam k l hk hl hlk) ^ l := by
    rw [hcast]
    exact hρlR_mono hl hlk hcL hmM hM (lamProj_le_laneLam k l hk hl hlk)
  have hge : (((2 ^ (M - m) : ℕ)) : ℝ) ^ l ≤ hBallR k l m' := hBallR_ge_pow (l := l) hM
  have hdec' := hdec (ξ' := ξ') hξ' hcL hR hplate htay (one_le_laneLam k l hk hl hlk)
    hm hmM h4 q hsepI hlam2 hge hρ hmMod
  have hclass := classCB_spec k l hk hl hlk ξ' hξ' h2m hmM hMN q hsep
    (classCB_le_laneLam k l hk hl hlk) u f hf
  exact asymAV_le_curveDecLocR hl hlk hmM hMN q (u := u) hA hrR hdec' hclass

/-- **The `H`-ball average bound with the level-gap split, uniform in the tuple and the levels.** -/
theorem exists_AV_bound_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {N m M m' : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
      (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
      {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
      (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) → ∀ u : E k,
      (∫⁻ w in Metric.ball (0 : E l) (hBallR k l m'),
          (‖∑ i ∈ blkFin N m q,
            f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
        ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) (hBallR k l m'))).toReal)
          * (K * (((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) ^ (plExp l)
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 (hBallR k l m') (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  classical
  have hA0 : (0 : ℝ) ≤ A := by
    have h1 : (0 : ℝ) ≤ gaugeExp k + (l : ℝ) := by
      linarith [Nat.cast_nonneg (α := ℝ) k, (gaugeExp_gt hk : (k : ℝ) < gaugeExp k),
        Nat.cast_nonneg (α := ℝ) l]
    linarith [hAge]
  obtain ⟨C, hCtop, hC⟩ := asymAV_le_proj_explicit_uniform hk hl hlk ha1 hεm hA0 hmMod
  refine ⟨(C + 1) * (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ),
    ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hCtop, ENNReal.one_ne_top⟩)
      (ENNReal.rpow_ne_top_of_nonneg (Nat.cast_nonneg (laneK k l hk hl hlk))
        (by norm_num)), ?_⟩
  intro N m M m' h2m hmM hMN hM h4 hm ξ' hξ' q hsepI hsep f hf u
  have hpl : (0 : ℝ) < plExp l := plExp_pos hl
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
  have hmt1 : (1 : ℝ≥0∞) ≤ (((2 ^ (M - m) : ℕ)) : ℝ≥0∞) := by
    rw [← Nat.cast_one]
    exact_mod_cast Nat.one_le_two_pow
  have hloss1 : (1 : ℝ≥0∞) ≤ (((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm) :=
    ENNReal.one_le_rpow hmt1 (by linarith)
  have hpow1 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ) := by
    rw [ENNReal.rpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hK1 : C ≤ (C + 1) * (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ) := by
    calc C ≤ C + 1 := le_add_right le_rfl
      _ = (C + 1) * 1 := (mul_one _).symm
      _ ≤ (C + 1) * (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hpow1 bot_le
  by_cases hgap : laneK k l hk hl hlk ≤ M - m
  · have hlam2 : 2 * laneLam k l hk hl hlk ≤ (2 : ℝ) ^ (M - m) := laneK_spec k l hk hl hlk hgap
    have h := hC h2m hmM hMN hξ' q hsepI hsep hM h4 hlam2 hm le_rfl f hf u
    refine h.trans ?_
    have hconst : (C * (((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm))
        ≤ ((C + 1) * (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ))
            * (((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm) :=
      mul_le_mul_of_nonneg_right hK1 bot_le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hconst hpl.le) bot_le) bot_le
  · have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
    have hKk : M - m ≤ laneK k l hk hl hlk := le_of_lt (not_le.mp hgap)
    have h := asymAV_le_trivial (m' := m') (ξ' := ξ') (u := u) (r := hBallR k l m') (A := A)
      hl hlk hmM hMN q hA0 hr0 hfm
    refine h.trans ?_
    have hcardnat : ((subBlkLvl m M q).card : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ (laneK k l hk hl hlk) := by
      have h1 : (subBlkLvl m M q).card ≤ 2 ^ (laneK k l hk hl hlk) :=
        (card_subBlkLvl_le m M hmM q).trans (Nat.pow_le_pow_right (by norm_num) hKk)
      exact_mod_cast h1
    have hcard2 : ((subBlkLvl m M q).card : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ) := by
      rw [ENNReal.rpow_natCast]
      exact hcardnat
    have h2L : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ) := by
      rw [ENNReal.rpow_natCast]
      exact one_le_pow₀ (by norm_num)
    have hcardp : ((((subBlkLvl m M q).card : ℝ≥0∞)) ^ (plExp l / 2))
        = ((((subBlkLvl m M q).card : ℝ≥0∞)) ^ ((1 : ℝ) / 2)) ^ (plExp l) := by
      rw [← ENNReal.rpow_mul]
      ring_nf
    have hstep : ((((subBlkLvl m M q).card : ℝ≥0∞)) ^ (plExp l / 2))
        ≤ (((C + 1) * (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ))
            * (((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) ^ (plExp l) := by
      calc ((((subBlkLvl m M q).card : ℝ≥0∞)) ^ (plExp l / 2))
          = ((((subBlkLvl m M q).card : ℝ≥0∞)) ^ ((1 : ℝ) / 2)) ^ (plExp l) := hcardp
        _ ≤ ((2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ)) ^ (plExp l) := by
            refine ENNReal.rpow_le_rpow ?_ hpl.le
            exact (ENNReal.rpow_le_rpow hcard2 (by norm_num)).trans
              ((ENNReal.rpow_le_rpow_of_exponent_le h2L (by norm_num)).trans
                (le_of_eq (ENNReal.rpow_one _)))
        _ ≤ ((C + 1) * (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ)) ^ (plExp l) :=
            ENNReal.rpow_le_rpow
              (le_mul_of_one_le_left' (le_add_left le_rfl : (1 : ℝ≥0∞) ≤ C + 1)) hpl.le
        _ ≤ (((C + 1) * (2 : ℝ≥0∞) ^ ((laneK k l hk hl hlk : ℕ) : ℝ))
              * (((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) ^ (plExp l) :=
            ENNReal.rpow_le_rpow (le_mul_of_one_le_right' hloss1) hpl.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep bot_le) bot_le

theorem gauge_plateGaugeLin_projEmbed_le_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hlk : l ≤ k) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ {ξ' : ℝ}, ξ' ∈ Set.Icc (0 : ℝ) 1 → ∀ (m' : ℕ) (c' : ℝ),
      c' ∈ Set.Icc (0 : ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ w : E l, ‖w‖ ≤ hBallR k l m' →
        gauge k hk (plateGaugeLin k (plateHalf m') c'
          (projEmbedLin k l (torsionVec k l hlk ξ') w)) ≤ ρ := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := norm_projMapLin_gammaDeriv_le_uniform hlk
  refine ⟨max C₁ (Real.sqrt k * (k.factorial : ℝ)), by positivity, ?_⟩
  intro ξ' hξ' m' c' hc' hsep w hw
  have hd0 : 0 < plateHalf m' := plateHalf_pos m'
  have hdle : plateHalf m' ≤ 1 := plateHalf_le_one m'
  have hc'1 : |c'| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hc'.1], hc'.2⟩
  refine gauge_plateGaugeLin_le hk hd0 (ρ := max C₁ (Real.sqrt k * (k.factorial : ℝ)))
    (fun i => ?_)
  set m : ℕ := i.val + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmk : m ≤ k := by have := i.isLt; omega
  have hinner : ⟪projEmbedLin k l (torsionVec k l hlk ξ') w, gammaDeriv k m c'⟫
      = ⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')⟫ :=
    inner_projEmbed_projMap k l (torsionVec k l hlk ξ') w _
  rw [hinner]
  rcases le_or_gt m (k - l) with hmle | hmgt
  · -- vanishing order case
    have hmul : (plateHalf m') ^ (k - l + 1 - m) * ((plateHalf m')⁻¹) ^ (k - l + 1)
        = ((plateHalf m') ^ m)⁻¹ := by
      rw [inv_pow]
      have hpow : (plateHalf m') ^ (k - l + 1)
          = (plateHalf m') ^ (k - l + 1 - m) * (plateHalf m') ^ m := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt (plateHalf_pos m'))), one_mul]
    have hbound := hC₁ ξ' hξ' m hm1 hmle c' hc'
    have hdK : |c' - ξ'| ^ (k - l + 1 - m) ≤ (plateHalf m') ^ (k - l + 1 - m) :=
      pow_le_pow_left₀ (abs_nonneg _) hsep _
    calc |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')⟫|
        ≤ ‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ hBallR k l m' * (C₁ * |c' - ξ'| ^ (k - l + 1 - m)) :=
          mul_le_mul hw hbound (norm_nonneg _) (hBallR_pos k l m').le
      _ = C₁ * (|c' - ξ'| ^ (k - l + 1 - m) * hBallR k l m') := by ring
      _ ≤ C₁ * ((plateHalf m') ^ (k - l + 1 - m) * ((plateHalf m')⁻¹) ^ (k - l + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdK (hBallR_pos k l m').le) hC₁pos.le
      _ = C₁ * ((plateHalf m') ^ m)⁻¹ := by rw [hmul]
      _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m') ^ m)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- bounded case
    have hbound : ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')‖
        ≤ Real.sqrt k * (k.factorial : ℝ) :=
      le_trans (norm_projMapLin_le k l (orthonormal_torsionVec k l hlk ξ') _)
        (norm_gammaDeriv_le k hc'1 m)
    have hone : (1 : ℝ) ≤ (plateHalf m')⁻¹ := one_le_inv_plateHalf m'
    have hpow : ((plateHalf m')⁻¹) ^ (k - l + 1) ≤ ((plateHalf m')⁻¹) ^ m :=
      pow_le_pow_right₀ hone (by omega)
    have hinv : ((plateHalf m')⁻¹) ^ m = ((plateHalf m') ^ m)⁻¹ := inv_pow _ _
    calc |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')⟫|
        ≤ ‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ hBallR k l m' * (Real.sqrt k * (k.factorial : ℝ)) :=
          mul_le_mul hw hbound (norm_nonneg _) (hBallR_pos k l m').le
      _ = (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m')⁻¹) ^ (k - l + 1) := by
          rw [hBallR]; ring
      _ ≤ (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m')⁻¹) ^ m :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m') ^ m)⁻¹ := by rw [hinv]
      _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m') ^ m)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem convPow_platePhi_shift_le_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (m' : ℕ) (c' : ℝ),
      c' ∈ Set.Icc (0 : ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ (F : E k → ℂ) (z : E k) (w : E l),
      ‖w‖ ≤ hBallR k l m' →
      convPow k s F (platePhi k hk (plateHalf m') c')
          (z + projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal C * convPow k s F (platePhi k hk (plateHalf m') c') z := by
  obtain ⟨ρ, hρ0, hρ⟩ := gauge_plateGaugeLin_projEmbed_le_uniform hk hl hlk
  refine ⟨(1 + ρ) ^ gaugeExp k, Real.rpow_nonneg (by linarith) _, ?_⟩
  intro ξ' hξ' m' c' hc' hsep F z w hw
  have hshift : ∀ t : E k, platePhi k hk (plateHalf m') c'
      ((z - t) + projEmbedLin k l (torsionVec k l hlk ξ') w)
      ≤ ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk (plateHalf m') c' (z - t) :=
    fun t => platePhi_shift_le_of_gauge hk (plateHalf m') c' hρ0 (hρ hξ' m' c' hc' hsep w hw)
  rw [convPow_eq_lintegral_sub, convPow_eq_lintegral_sub]
  have hcongr : (∫⁻ t : E k, ((‖F t‖₊ : ℝ≥0∞) ^ s)
        * (ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk (plateHalf m') c' (z - t)))
      = ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
        * ∫⁻ t : E k, ((‖F t‖₊ : ℝ≥0∞) ^ s) * platePhi k hk (plateHalf m') c' (z - t) := by
    rw [show (fun t : E k => ((‖F t‖₊ : ℝ≥0∞) ^ s)
          * (ENNReal.ofReal ((1 + ρ) ^ gaugeExp k) * platePhi k hk (plateHalf m') c' (z - t)))
        = fun t : E k => ENNReal.ofReal ((1 + ρ) ^ gaugeExp k)
          * (((‖F t‖₊ : ℝ≥0∞) ^ s) * platePhi k hk (plateHalf m') c' (z - t)) from by
      funext t; ring]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine (lintegral_mono fun t => ?_).trans (le_of_eq hcongr)
  have : z + projEmbedLin k l (torsionVec k l hlk ξ') w - t
      = (z - t) + projEmbedLin k l (torsionVec k l hlk ξ') w := by abel
  rw [this]
  exact mul_le_mul' le_rfl (hshift t)

/-- **Step 2 of Lemma 3.8, uniform in the tuple and the levels.**  The constant is
`(1+ρ)^{gaugeExp k}` with `ρ` the polar-plate constant, hence a function of `(k,l)` only. -/
theorem asymLHS_le_supMoving_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N m m' : ℕ} (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) {ξ' r : ℝ}
      (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1)
      (hr : 0 < r) (hrh : r ≤ hBallR k l m')
      (hsep : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m'),
      ∀ (f : Fin (2 ^ N) → E k → ℂ), (∀ i, Measurable (f i)) →
      asymLHS k hk l N m m' q q' f
        ≤ ENNReal.ofReal C * ∫⁻ z : E k,
            (ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal))⁻¹ *
            (∫⁻ w in Metric.ball (0 : E l) r,
              asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
            * asymC2 k hk l N m' q' f z := by
  obtain ⟨Csup, hCsup0, hCsup⟩ :=
    convPow_platePhi_shift_le_uniform (k := k) (l := l) hk hl hlk (pkExp k - plExp l)
  refine ⟨Csup, hCsup0, ?_⟩
  intro N m m' q q' ξ' r hξ' hr hrh hsep f hf
  have hpc : pieceCenter (2 ^ m') q' ∈ Set.Icc (0 : ℝ) 1 :=
    pieceCenter_mem_Icc (2 ^ m') Nat.one_le_two_pow q'
  have hC : ∀ z w, w ∈ Metric.ball (0 : E l) r →
      asymC2 k hk l N m' q' f (z + projEmbedLin k l (torsionVec k l hlk ξ') w)
        ≤ ENNReal.ofReal Csup * asymC2 k hk l N m' q' f z := by
    intro z w hw
    have hw' : ‖w‖ ≤ hBallR k l m' := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      linarith
    exact hCsup hξ' m' (pieceCenter (2 ^ m') q') hpc hsep
      (fun x : E k => ∑ i ∈ blkFin N m' q', f i x) z w hw'
  have hcore := Commons.Measure.Integral.lintegral_mul_le_moving_ball k l
    (projEmbedLin k l (torsionVec k l hlk ξ'))
    (norm_projEmbedLin_eq (orthonormal_torsionVec k l hlk ξ')) hr
    (asymC1 k hk l N m q f) (asymC2 k hk l N m' q' f)
    (measurable_asymC1 k hk l N m q hf).aemeasurable
    (measurable_asymC2 k hk l N m' q' hf).aemeasurable hC
  rw [asymLHS_eq_integral]
  exact hcore

/-- **The fused form of the `av` bound, uniform in the tuple and the levels.**  The constant is
`K · ((2^{M−m})^{2εm})^{p_l}` with `K = ofReal Csup · K_AV^{p_l}` a function of `(k,l,a₀,εm,A)`
only: the lane's explicit scale loss is factored out, as the §4 exponent bookkeeping requires. -/
theorem asymLHS_le_fused_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ {N m M m' : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
      (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
      {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
      (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
      (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      asymLHS k hk l N m m' q q' f
        ≤ K * ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) ^ (plExp l)
          * ∫⁻ t : E k,
        (∫⁻ z : E k, asymC2 k hk l N m' q' f z
            * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t))
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 (hBallR k l m') (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
  have hA0 : (0 : ℝ) ≤ A := by
    have h1 : (0 : ℝ) ≤ gaugeExp k + (l : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k,
      (gaugeExp_gt hk : (k : ℝ) < gaugeExp k), Nat.cast_nonneg (α := ℝ) l]
    linarith [hAge]
  obtain ⟨KAV, hKAVtop, hAV⟩ := exists_AV_bound_uniform hk hl hlk ha1 hεm hAge hmMod
  obtain ⟨Csup, hCsup0, hsup⟩ := asymLHS_le_supMoving_uniform (k := k) (l := l) hk hl hlk
  refine ⟨ENNReal.ofReal Csup * KAV ^ (plExp l),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (plExp_nonneg l) hKAVtop), ?_⟩
  intro N m M m' h2m hmM hMN hM h4 hm ξ' hξ' q q' hsep' hsepI hsep f hf
  have hr0 : 0 < hBallR k l m' := hBallR_pos k l m'
  set Cloc : ℝ≥0∞ := KAV * ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) with hCloc
  have hCe : (ENNReal.ofReal Csup * KAV ^ (plExp l))
        * ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) ^ (plExp l)
      = ENNReal.ofReal Csup * Cloc ^ (plExp l) := by
    rw [hCloc, ENNReal.mul_rpow_of_nonneg _ _ (plExp_pos hl).le]
    ring
  rw [hCe]
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
  have hAV' : ∀ u : E k, AV u ≤ Bv * Cloc ^ (plExp l) * S u :=
    fun u => hAV h2m hmM hMN hM h4 hm hξ' q hsepI hsep f hf u
  have hsup' : asymLHS k hk l N m m' q q' f ≤ ENNReal.ofReal Csup * ∫⁻ z : E k,
      (ENNReal.ofReal ((volume (Metric.ball (0 : E l) (hBallR k l m'))).toReal))⁻¹ *
      (∫⁻ w in Metric.ball (0 : E l) (hBallR k l m'),
        asymC1 k hk l N m q f (z + projEmbedLin k l (torsionVec k l hlk ξ') w))
      * asymC2 k hk l N m' q' f z := hsup q q' hξ' hr0 le_rfl hsep' f hfm
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

/-- **The per-`(q,q')` step of Lemma 3.8, uniform in the tuple and the levels.**  The constant is
`((K·ofReal CJ)^{1/p_l}·(2^{M−m})^{2εm})^{p_l}`: uniform, with the lane's scale loss factored out. -/
theorem asymDecFine_pt_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hAge : gaugeExp k + (l : ℝ) < A)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {N m M m' : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
      (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m)) (hm : 1 ≤ m)
      {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m'))
      (hsep' : |pieceCenter (2 ^ m') q' - ξ'| ≤ plateHalf m')
      (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
      (hsep : ∀ j : Fin (2 ^ (M - m)),
        1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
      (f : Fin (2 ^ N) → E k → ℂ),
      (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
      asymLHS k hk l N m m' q q' f
        ≤ (C * ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm))) ^ (plExp l)
          * (∑ q'' ∈ subBlkLvl m M q,
              (asymLHS k hk l N M m' q'' q' f) ^ (2 / plExp l)) ^ (plExp l / 2) := by
  have hp0 : (0 : ℝ) < plExp l := plExp_pos hl
  obtain ⟨K, hKtop, hK⟩ := asymLHS_le_fused_uniform hk hl hlk ha1 hεm hAge hmMod
  obtain ⟨CJ, hCJ0, hCJ⟩ := lintegral_W_mul_tentNorm_le_uniform (k := k) (l := l) hk hl hlk
    (A := A) hAge
  refine ⟨(K * ENNReal.ofReal CJ) ^ ((1 : ℝ) / plExp l),
    ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one (le_of_lt hp0))
      (ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top), ?_⟩
  intro N m M m' h2m hmM hMN hM h4 hm ξ' hξ' q q' hsep' hsepI hsep f hf
  have hp2 : (2 : ℝ) ≤ plExp l := by
    rw [plExp]
    have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    nlinarith
  set C1 : ℝ≥0∞ := K * ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) ^ (plExp l) with hC1
  have h1 : asymLHS k hk l N m m' q q' f
      ≤ C1 * ∫⁻ t : E k,
        (∫⁻ z : E k, asymC2 k hk l N m' q' f z
            * platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) (z - t))
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 (hBallR k l m') (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (t + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
    refine (hK h2m hmM hMN hM h4 hm hξ' q q' hsep' hsepI hsep f hf).trans (le_of_eq ?_)
    rw [hC1]
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
            ENNReal.rpow_le_rpow (by simp only [hW, hTN]; exact hCJ hmM hMN (le_trans h2m hmM) hξ' q q' hsep' J hJ f hf) (by positivity)
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
    refine h1.trans ?_
    refine (mul_le_mul_of_nonneg_left (hZ.trans hY) bot_le).trans (le_of_eq ?_)
    ring
  have hgoal : (C1 * ENNReal.ofReal CJ)
      = ((K * ENNReal.ofReal CJ) ^ ((1 : ℝ) / plExp l)
          * ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm))) ^ (plExp l) := by
    rw [hC1, ENNReal.mul_rpow_of_nonneg _ _ (plExp_pos hl).le,
      show ((K * ENNReal.ofReal CJ) ^ ((1 : ℝ) / plExp l)) ^ (plExp l)
        = K * ENNReal.ofReal CJ from by
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hp0), ENNReal.rpow_one]]
    ring
  exact hfin.trans (le_of_eq (by rw [hgoal]))

/-- **The assembly of `AsymDecFine` from the uniform per-`(q,q')` step.**  With the per-step
constant uniform the `Finset.sup` over the pairs disappears; the constant carries the lane's
explicit scale loss `(2^{refLvl l k m' − m})^{2εm}`. -/
theorem asymDecFine_of_model_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {a₀ εm : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {N m m' : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ refLvl l k m')
      (hMN : refLvl l k m' ≤ N) (h4 : 4 ≤ 2 ^ (refLvl l k m' - m)) (hm : 1 ≤ m),
      AsymDecFine k hk l N m m'
        (C * (((2 ^ (refLvl l k m' - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) := by
  have hAge : gaugeExp k + (l : ℝ) < gaugeExp k + (l : ℝ) + 1 := by linarith
  obtain ⟨C, hCtop, hC⟩ := asymDecFine_pt_uniform hk hl hlk ha1 hεm hAge hmMod
  refine ⟨C, hCtop, ?_⟩
  intro N m m' h2m hmM hMN h4 hm q q' hsep f hf
  exact hC h2m hmM hMN rfl h4 hm (pieceCenter_mem_Icc (2 ^ m') Nat.one_le_two_pow q')
    q q' (by rw [sub_self, abs_zero]; exact (plateHalf_pos m').le) (sepLevel_hsepI q q' hsep)
    (sepLevel_hsep hmM q q' hsep) f hf

/-- **GLYZ Lemma 3.9, in uniform form.**  The first-slot coarsening of the asymmetric bilinear
statement, with a constant `C` depending only on `(k,l,a₀,εm)`, times the explicit scale loss
`(2^{refLvl l k m' − m})^{2εm·p_l/p_k}`.  This is the form the §4 recursion consumes: the loss is
`O(b·εm)` in the exponent bookkeeping and vanishes as `εm → 0`. -/
theorem asymDec_of_model_uniform {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (hlk1 : l ≤ k - 1) {a₀ εm : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm)
    (hmMod : ∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (laneEnl k l hk hl hlk)
      (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ {N m m' : ℕ} (h2m : 2 ≤ m) (hmM : m ≤ refLvl l k m')
      (hMN : refLvl l k m' ≤ N) (h4 : 4 ≤ 2 ^ (refLvl l k m' - m)) (hm : 1 ≤ m),
      ∀ C₁ : ℝ≥0∞, AsymDec k hk l N (refLvl l k m') m' C₁ →
        AsymDec k hk l N m m'
          (C₁ * (C * (((2 ^ (refLvl l k m' - m) : ℕ)) : ℝ≥0∞) ^ (2 * εm)) ^ (plExp l / pkExp k)) := by
  obtain ⟨C₂, hC₂top, hfine⟩ := asymDecFine_of_model_uniform hk hl hlk ha1 hεm hmMod
  refine ⟨C₂, hC₂top, ?_⟩
  intro N m m' h2m hmM hMN h4 hm C₁ hbig
  exact asymDec_of_fine hk hl hlk1 hmM hMN hbig (hfine h2m hmM hMN h4 hm)

end Submission.Vinogradov
