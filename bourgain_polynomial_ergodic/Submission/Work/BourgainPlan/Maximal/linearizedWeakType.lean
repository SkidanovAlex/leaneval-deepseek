import Mathlib
import Submission.Work.BourgainPlan.Maximal.lwtCZDefs
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.dyCZ
import Submission.Work.BourgainPlan.Maximal.lintegral_ell2Max_le_uniform
import Submission.Work.BourgainPlan.Maximal.ae_le_dyMax
import Submission.Work.BourgainPlan.Maximal.lwtNorm_lwtCellAvg_le
import Submission.Work.BourgainPlan.Maximal.lintegral_lwtGood_eq

/-!
# The linearised weak-`(1,1)` bound for the `ℓ²`-valued dyadic maximal operator

Main theorem: `linearizedWeakType`, the weak-`(1,1)` estimate for the linearised operator
`linOp g m e`, with a constant uniform in the number of components.

The proof is the classical Calderón--Zygmund argument.  Write `σ = ell2Sigma g`,
`c = ofReal (λ/2)`, let `Ω = lwtOm σ c` be the CZ set (the union of the maximal dyadic cells whose
`σ`-average exceeds `c`) and let `Ω* = lwtOmStar σ c` be its one-step enlargement.  Split
`g = G + B` into the CZ good part `G = lwtG g σ c` and the bad part `B`, so that:
* `B` has mean zero on every maximal cell, hence `linOp g = linOp G` off `Ω*` (the kernel of
  `linOp` is an average over the dyadic cell of the point, and `Ω*` is exactly the set on which that
  cell can be contained in a maximal cell);
* on each maximal cell the `ℓ²`-norm of the averages of the components is at most `λ`, and off `Ω`
  the `ℓ²`-norm of `G` is that of `g`, which is at most `λ/2` a.e.; hence
  `∫⁻ ell2Sq G ≤ λ²|Ω| + (λ/2)∫⁻σ`;
* the `L²(ℓ²)` bound `lintegral_ell2Max_le_uniform` then bounds the level set of `ell2F G` by
  Chebyshev's inequality;
* `|Ω*| ≤ 2c⁻¹ ∫⁻σ = (4/λ)∫⁻σ`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Work.BourgainPlan.Maximal

variable {n : ℕ}

/-- The square of the real `ℓ²`-norm, as a real sum of squares. -/
noncomputable def lwtSq (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ := ∑ t, (f t x) ^ 2

lemma lwtSq_nonneg (f : Fin n → ℝ → ℝ) (x : ℝ) : 0 ≤ lwtSq f x :=
  Finset.sum_nonneg fun t _ => sq_nonneg _

lemma lwtNorm_sq_eq_lwtSq (g : Fin n → ℝ → ℝ) (x : ℝ) : lwtNorm g x ^ 2 = lwtSq g x :=
  lwtNorm_sq g x

lemma ell2Sq_eq_ofReal_lwtSq {f : Fin n → ℝ → ℝ} (hf : ∀ t x, 0 ≤ f t x) (x : ℝ) :
    ell2Sq f x = ENNReal.ofReal (lwtSq f x) := by
  unfold ell2Sq lwtSq
  rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Real.enorm_eq_ofReal (hf t x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (hf t x) 2]

/-- `lwtNorm` is unchanged by replacing each member of the family by its absolute value. -/
lemma lwtNorm_abs_eq (g : Fin n → ℝ → ℝ) : lwtNorm (fun t y => |g t y|) = lwtNorm g := by
  funext x
  unfold lwtNorm
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [sq_abs]

lemma abs_le_lwtNorm (g : Fin n → ℝ → ℝ) (t : Fin n) (y : ℝ) : |g t y| ≤ lwtNorm g y := by
  have h2 : (g t y) ^ 2 ≤ ∑ s, (g s y) ^ 2 :=
    Finset.single_le_sum (f := fun s => (g s y) ^ 2) (fun s _ => sq_nonneg _) (Finset.mem_univ t)
  calc |g t y| = Real.sqrt ((g t y) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ s, (g s y) ^ 2) := Real.sqrt_le_sqrt h2
    _ = lwtNorm g y := rfl

/-- The Calderón--Zygmund good part of the family `g` at level `c` (for `σ = ell2Sigma g`). -/
noncomputable def lwtG (g : Fin n → ℝ → ℝ) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) : Fin n → ℝ → ℝ :=
  fun t => lwtGood (fun y => |g t y|) σ c

lemma lwtG_measurable {g : Fin n → ℝ → ℝ} (hg : ∀ t, Measurable (g t)) (σ : ℝ → ℝ≥0∞)
    (c : ℝ≥0∞) (t : Fin n) : Measurable (lwtG g σ c t) :=
  lwtGood_measurable (hg t).abs σ c

lemma lwtG_nonneg (g : Fin n → ℝ → ℝ) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (t : Fin n) (y : ℝ) :
    0 ≤ lwtG g σ c t y :=
  lwtGood_nonneg (fun y => abs_nonneg _) σ c y

lemma lwtG_of_notMem {g : Fin n → ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {t : Fin n} {y : ℝ}
    (hy : y ∉ lwtOm σ c) : lwtG g σ c t y = |g t y| :=
  lwtGood_of_notMem hy

lemma lwtG_of_mem {g : Fin n → ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {t : Fin n} {y : ℝ}
    {p : ℤ × ℤ} (hp : p ∈ czMax σ c) (hy : y ∈ dyCell p.1 p.2) :
    lwtG g σ c t y = lwtCellAvg (fun y => |g t y|) p :=
  lwtGood_eq_lwtCellAvg (fun y => abs_nonneg _) hp hy

/-- On the CZ set, the `ℓ²`-norm of the good part is at most the level. -/
lemma lwtSq_lwtG_le {g : Fin n → ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {lam : ℝ}
    (hlam : 0 ≤ lam) (hint : ∀ t, Integrable (fun y => |g t y|))
    (hintN : Integrable (lwtNorm g))
    (havg : ∀ p : ℤ × ℤ, p ∈ czMax σ c → lwtCellAvg (lwtNorm g) p ≤ lam)
    {y : ℝ} (hy : y ∈ lwtOm σ c) : lwtSq (lwtG g σ c) y ≤ lam ^ 2 := by
  rw [lwtOm, mem_iUnion₂] at hy
  obtain ⟨p, hp, hyp⟩ := hy
  have hJ : (∑ t, (lwtCellAvg (fun y => |g t y|) p) ^ 2) ^ ((1 : ℝ) / 2)
      ≤ lwtCellAvg (lwtNorm g) p := by
    have h := lwtNorm_lwtCellAvg_le (A := fun t => fun y => |g t y|) (fun t y => abs_nonneg _)
      hint (by rwa [lwtNorm_abs_eq g]) p
    rwa [lwtNorm_abs_eq g] at h
  have hsum : lwtSq (lwtG g σ c) y = ∑ t, (lwtCellAvg (fun y => |g t y|) p) ^ 2 := by
    unfold lwtSq
    exact Finset.sum_congr rfl fun t _ => by rw [lwtG_of_mem hp hyp]
  have hnn : 0 ≤ ∑ t, (lwtCellAvg (fun y => |g t y|) p) ^ 2 :=
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have hsqt : ((∑ t, (lwtCellAvg (fun y => |g t y|) p) ^ 2) ^ ((1 : ℝ) / 2)) ^ 2
      = ∑ t, (lwtCellAvg (fun y => |g t y|) p) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  rw [hsum, ← hsqt]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hnn _) (hJ.trans (havg p hp)) 2


/-- The `L²`-mass of the good part.  On the CZ set the `ℓ²`-norm of the good part is at most `λ`;
off it, it is that of `g`, which is at most `λ/2` a.e. -/
lemma lintegral_ell2Sq_lwtG_le {g : Fin n → ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {lam : ℝ}
    (hg : ∀ t, Measurable (g t)) (hσm : Measurable σ) (hlam : 0 < lam) (hσ : ∀ y, σ y = ENNReal.ofReal (lwtNorm g y))
    (hs_int : Integrable (lwtNorm g)) (hint_abs : ∀ t, Integrable (fun y => |g t y|))
    (havg : ∀ p : ℤ × ℤ, p ∈ czMax σ c → lwtCellAvg (lwtNorm g) p ≤ lam)
    (hae : ∀ᵐ y ∂volume, y ∉ lwtOm σ c → lwtNorm g y ≤ lam / 2) :
    ∫⁻ y, ell2Sq (lwtG g σ c) y
      ≤ ENNReal.ofReal (lam ^ 2) * volume (lwtOm σ c) + ENNReal.ofReal (lam / 2) * ∫⁻ y, σ y := by
  have hΩ : MeasurableSet (lwtOm σ c) := measurableSet_lwtOm σ c
  rw [← lintegral_add_compl (fun y => ell2Sq (lwtG g σ c) y) hΩ]
  refine add_le_add ?_ ?_
  · calc ∫⁻ y in lwtOm σ c, ell2Sq (lwtG g σ c) y
        ≤ ∫⁻ y in lwtOm σ c, ENNReal.ofReal (lam ^ 2) := by
          refine setLIntegral_mono measurable_const fun y hy => ?_
          rw [ell2Sq_eq_ofReal_lwtSq (fun t x => lwtG_nonneg g σ c t x) y]
          exact ENNReal.ofReal_le_ofReal (lwtSq_lwtG_le hlam.le hint_abs hs_int havg hy)
      _ = ENNReal.ofReal (lam ^ 2) * volume (lwtOm σ c) := setLIntegral_const _ _
  · calc ∫⁻ y in (lwtOm σ c)ᶜ, ell2Sq (lwtG g σ c) y
        ≤ ∫⁻ y in (lwtOm σ c)ᶜ, ENNReal.ofReal ((lam / 2) * lwtNorm g y) := by
          refine setLIntegral_mono_ae ?_ ?_
          · exact (ENNReal.measurable_ofReal.comp
              (measurable_const.mul (lwtNorm_measurable (g := g) hg))).aemeasurable
          · filter_upwards [hae] with y hy hyc
            rw [ell2Sq_eq_ofReal_lwtSq (fun t x => lwtG_nonneg g σ c t x) y]
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : lwtSq (lwtG g σ c) y = lwtSq g y := by
              unfold lwtSq
              exact Finset.sum_congr rfl fun t _ => by rw [lwtG_of_notMem hyc, sq_abs]
            have hsq : lwtSq g y = lwtNorm g y * lwtNorm g y := by
              rw [← lwtNorm_sq_eq_lwtSq, pow_two]
            rw [h1, hsq]
            exact mul_le_mul_of_nonneg_right (hy hyc) (lwtNorm_nonneg g y)
      _ = ENNReal.ofReal (lam / 2) * ∫⁻ y in (lwtOm σ c)ᶜ, σ y := by
          rw [← lintegral_const_mul (ENNReal.ofReal (lam / 2)) hσm]
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ lam / 2), ← hσ y]
      _ ≤ ENNReal.ofReal (lam / 2) * ∫⁻ y, σ y :=
          mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- Off `Ω*`, the dyadic average of `‖g t ·‖ₑ` agrees with that of the good part: the bad part has
mean zero on every maximal CZ cell, and every maximal cell meeting the cell of `x` is contained in
it. -/
lemma lwtG_dyAvg_eq {g : Fin n → ℝ → ℝ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hg : ∀ t, Measurable (g t))
    (t : Fin n) (n : ℤ) (x : ℝ) (hx : x ∉ lwtOmStar σ c)
    (hψint : Integrable (fun y => |g t y|)) :
    dyAvg (fun y => ‖g t y‖ₑ) n x = dyAvg (fun y => ‖lwtG g σ c t y‖ₑ) n x := by
  have hcell : ∀ p : ℤ × ℤ, p ∈ czMax σ c → ¬ dyCell n (dyIdx n x) ⊆ dyCell p.1 p.2 := by
    intro p hp hsub
    refine hx ?_
    rw [lwtOmStar, mem_iUnion₂]
    exact ⟨p, hp, dyCell_subset_succ p.1 p.2 (hsub (dyIdx_mem n x))⟩
  have hT := lintegral_lwtGood_eq (σ := σ) (c := c) (ψ := fun y => |g t y|)
    (fun y => abs_nonneg _) (hg t).abs hψint hcell
  have h1 : ∫⁻ y in dyCell n (dyIdx n x), ‖lwtG g σ c t y‖ₑ
      = ∫⁻ y in dyCell n (dyIdx n x),
          ENNReal.ofReal (lwtGood (fun y => |g t y|) σ c y) := by
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (lwtG_nonneg g σ c t y)]
    rfl
  have h2 : ∫⁻ y in dyCell n (dyIdx n x), ENNReal.ofReal (|g t y|)
      = ∫⁻ y in dyCell n (dyIdx n x), ‖g t y‖ₑ := by
    refine lintegral_congr fun y => ?_
    exact (Real.enorm_eq_ofReal_abs (g t y)).symm
  rw [dyAvg, dyAvg]
  congr 1
  rw [← h2, h1, ← hT]


theorem linearizedWeakType :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : Fin n → ℝ → ℝ), (∀ t, Measurable (g t)) →
      ∀ (m : Fin n → ℝ → ℤ), (∀ t, Measurable (m t)) →
      ∀ (e : Fin n → ℝ → ℝ), (∀ t, Measurable (e t)) → (∀ t x, 0 ≤ e t x) →
      (∀ x, ∑ t, (e t x) ^ 2 ≤ 1) → ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {x : ℝ | ENNReal.ofReal (lam / 2) <
          Work.BourgainPlan.Maximal.linOp g m e x}
        ≤ ENNReal.ofReal (C / lam) * ∫⁻ x, Work.BourgainPlan.Maximal.ell2Sigma g x := by
  obtain ⟨C₀, hC₀, hL2⟩ := lintegral_ell2Max_le_uniform
  refine ⟨4 + 10 * C₀ ^ (2 : ℝ), ?_, ?_⟩
  · have h : (0:ℝ) ≤ C₀ ^ (2 : ℝ) := Real.rpow_nonneg hC₀.le 2
    linarith
  intro n g hg m hm e he he0 he1 lam hlam
  set σ : ℝ → ℝ≥0∞ := ell2Sigma g with hσdef
  set s : ℝ → ℝ := lwtNorm g with hsdef
  have hσ : ∀ x, σ x = ENNReal.ofReal (s x) := fun x => ell2Sigma_eq_ofReal g x
  have hs_meas : Measurable s := lwtNorm_measurable hg
  have hσ_meas : Measurable σ := by rw [hσdef]; exact ell2Sigma_measurable hg
  have hcong : (∫⁻ x, ENNReal.ofReal (s x)) = ∫⁻ x, σ x := lintegral_congr fun x => (hσ x).symm
  by_cases htop : ∫⁻ x, σ x = ∞
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact le_top
  · have hint : ∫⁻ x, σ x < ∞ := lt_top_iff_ne_top.mpr htop
    have hs_int : Integrable s volume := by
      refine (lintegral_ofReal_ne_top_iff_integrable hs_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => lwtNorm_nonneg g x)).mp ?_
      rw [hcong]; exact hint.ne
    have hae_le : ∀ᵐ x ∂volume, σ x ≤ dyMax σ x := by
      have heq : (fun y => ENNReal.ofReal (s y)) = σ := funext fun y => (hσ y).symm
      have h := ae_le_dyMax s hs_int.locallyIntegrable (fun x => lwtNorm_nonneg g x)
      filter_upwards [h] with x hx
      rw [heq] at hx
      rwa [hσ x]
    set a : ℝ≥0∞ := ENNReal.ofReal (lam / 2) with hadef
    have ha_pos : 0 < a := ENNReal.ofReal_pos.mpr (by linarith)
    have ha_ne_top : a ≠ ⊤ := ENNReal.ofReal_ne_top
    have hae_off : ∀ᵐ x ∂volume, x ∉ lwtOm σ a → s x ≤ lam / 2 := by
      filter_upwards [hae_le] with x hx hxnot
      have h1 : dyMax σ x ≤ a := by
        by_contra hcon
        rw [not_le] at hcon
        exact hxnot (by rw [lwtOm_eq_levelSet ha_pos hint]; exact hcon)
      have h2' : σ x ≤ a := hx.trans h1
      rw [hσ x, hadef] at h2'
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith : (0:ℝ) ≤ lam / 2)).mp h2'
    have havg : ∀ p : ℤ × ℤ, p ∈ czMax σ a → lwtCellAvg s p ≤ lam := by
      intro p hp
      have h1 := czMax_avg_le ha_pos hint hp
      have h2 := ofReal_lwtCellAvg (A := s) (σ := σ) (p := p)
        (fun y => lwtNorm_nonneg g y) hσ (hs_int.integrableOn)
      rw [h2] at h1
      have h3 : 2 * a = ENNReal.ofReal lam := by
        rw [hadef, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [h3] at h1
      rwa [ENNReal.ofReal_le_ofReal_iff hlam.le] at h1
    have hint_abs : ∀ t, Integrable (fun y => |g t y|) := fun t =>
      hs_int.mono' (hg t).abs.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by simpa using abs_le_lwtNorm g t y)
    have ha_inv : a⁻¹ = ENNReal.ofReal (2 / lam) := by
      rw [hadef, ← ENNReal.ofReal_inv_of_pos (by linarith : (0:ℝ) < lam / 2)]
      congr 1
      field_simp
    have hvol_Om : volume (lwtOm σ a) ≤ ENNReal.ofReal (2 / lam) * ∫⁻ x, σ x :=
      (volume_lwtOm_le ha_pos ha_ne_top).trans (by rw [ha_inv])
    have hvol_star : volume (lwtOmStar σ a) ≤ ENNReal.ofReal (4 / lam) * ∫⁻ x, σ x := by
      refine (volume_lwtOmStar_le ha_pos ha_ne_top).trans ?_
      rw [ha_inv]
      have h2 : 2 * ENNReal.ofReal (2 / lam) = ENNReal.ofReal (4 / lam) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [← h2, mul_assoc]
    have hI_sq : ∫⁻ y, ell2Sq (lwtG g σ a) y
        ≤ ENNReal.ofReal (lam ^ 2) * volume (lwtOm σ a) + ENNReal.ofReal (lam / 2) * ∫⁻ y, σ y :=
      lintegral_ell2Sq_lwtG_le hg hσ_meas hlam hσ hs_int hint_abs havg hae_off
    have hI_sq2 : ∫⁻ y, ell2Sq (lwtG g σ a) y ≤ ENNReal.ofReal ((5 / 2) * lam) * ∫⁻ x, σ x := by
      refine hI_sq.trans ?_
      have hconst : ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (2 / lam) = ENNReal.ofReal (2 * lam) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ lam ^ 2)]
        congr 1
        field_simp
      calc ENNReal.ofReal (lam ^ 2) * volume (lwtOm σ a) + ENNReal.ofReal (lam / 2) * ∫⁻ x, σ x
          ≤ ENNReal.ofReal (lam ^ 2) * (ENNReal.ofReal (2 / lam) * ∫⁻ x, σ x)
              + ENNReal.ofReal (lam / 2) * ∫⁻ x, σ x :=
            add_le_add (mul_le_mul_of_nonneg_left hvol_Om bot_le) le_rfl
        _ = (ENNReal.ofReal (lam ^ 2) * ENNReal.ofReal (2 / lam) + ENNReal.ofReal (lam / 2))
              * ∫⁻ x, σ x := by rw [add_mul]; ac_rfl
        _ = (ENNReal.ofReal (2 * lam) + ENNReal.ofReal (lam / 2)) * ∫⁻ x, σ x := by rw [hconst]
        _ = ENNReal.ofReal ((5 / 2) * lam) * ∫⁻ x, σ x := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring_nf
    have hI_max : ∫⁻ y, ell2Max (lwtG g σ a) y
        ≤ ENNReal.ofReal (C₀ ^ (2 : ℝ)) * ∫⁻ y, ell2Sq (lwtG g σ a) y :=
      hL2 n (lwtG g σ a) fun t => lwtG_measurable hg σ a t
    have hI_max2 : ∫⁻ y, ell2Max (lwtG g σ a) y
        ≤ ENNReal.ofReal (C₀ ^ (2 : ℝ)) * (ENNReal.ofReal ((5 / 2) * lam) * ∫⁻ x, σ x) :=
      hI_max.trans (mul_le_mul_of_nonneg_left hI_sq2 bot_le)
    have ha2 : a ^ 2 = ENNReal.ofReal (lam ^ 2 / 4) := by
      rw [hadef, ← ENNReal.ofReal_pow (by linarith : (0:ℝ) ≤ lam / 2) 2]
      congr 1
      ring
    have ha2_inv : (a ^ 2)⁻¹ = ENNReal.ofReal (4 / lam ^ 2) := by
      rw [ha2, ← ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < lam ^ 2 / 4)]
      congr 1
      field_simp
    have ha2_ne_zero : a ^ 2 ≠ 0 := by
      rw [ha2]; exact (ENNReal.ofReal_pos.mpr (by positivity : (0:ℝ) < lam ^ 2 / 4)).ne'
    have ha2_ne_top : a ^ 2 ≠ ⊤ := by
      rw [ha2]; exact ENNReal.ofReal_ne_top
    have hmarkov := mul_meas_ge_le_lintegral (μ := volume) (ell2Max_measurable (lwtG g σ a)) (a ^ 2)
    have hZ : volume {x : ℝ | a ^ 2 ≤ ell2Max (lwtG g σ a) x}
        ≤ ENNReal.ofReal (10 * C₀ ^ (2 : ℝ) / lam) * ∫⁻ x, σ x := by
      have hconst : (a ^ 2)⁻¹ * ENNReal.ofReal (C₀ ^ (2 : ℝ)) * ENNReal.ofReal ((5 / 2) * lam)
          = ENNReal.ofReal (10 * C₀ ^ (2 : ℝ) / lam) := by
        rw [ha2_inv, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 / lam ^ 2),
          ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 / lam ^ 2 * C₀ ^ (2 : ℝ))]
        congr 1
        field_simp
        ring_nf
      calc volume {x : ℝ | a ^ 2 ≤ ell2Max (lwtG g σ a) x}
          = (a ^ 2)⁻¹ * (a ^ 2 * volume {x : ℝ | a ^ 2 ≤ ell2Max (lwtG g σ a) x}) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel ha2_ne_zero ha2_ne_top, one_mul]
        _ ≤ (a ^ 2)⁻¹
              * (ENNReal.ofReal (C₀ ^ (2 : ℝ)) * (ENNReal.ofReal ((5 / 2) * lam) * ∫⁻ x, σ x)) :=
            mul_le_mul_of_nonneg_left (hmarkov.trans hI_max2) bot_le
        _ = ENNReal.ofReal (10 * C₀ ^ (2 : ℝ) / lam) * ∫⁻ x, σ x := by
            rw [show (a ^ 2)⁻¹ * (ENNReal.ofReal (C₀ ^ (2 : ℝ))
                  * (ENNReal.ofReal ((5 / 2) * lam) * ∫⁻ x, σ x))
                = ((a ^ 2)⁻¹ * ENNReal.ofReal (C₀ ^ (2 : ℝ)) * ENNReal.ofReal ((5 / 2) * lam))
                  * ∫⁻ x, σ x from by ac_rfl,
              hconst]
    have hsubset : {x : ℝ | a < ell2F (lwtG g σ a) x}
        ⊆ {x : ℝ | a ^ 2 ≤ ell2Max (lwtG g σ a) x} := by
      intro x hx
      have hx' : a < (ell2Max (lwtG g σ a) x) ^ ((1 : ℝ) / 2) := hx
      have h2 : a ^ (2 : ℝ) < ((ell2Max (lwtG g σ a) x) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) :=
        ENNReal.rpow_lt_rpow hx' (by norm_num)
      rw [← ENNReal.rpow_mul, show (1 : ℝ) / 2 * 2 = 1 by norm_num,
        ENNReal.rpow_one] at h2
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast] at h2
      exact h2.le
    have hvol_level : volume {x : ℝ | a < ell2F (lwtG g σ a) x}
        ≤ ENNReal.ofReal (10 * C₀ ^ (2 : ℝ) / lam) * ∫⁻ x, σ x :=
      (measure_mono hsubset).trans hZ
    have hlin_eq : ∀ x, x ∉ lwtOmStar σ a → linOp g m e x = linOp (lwtG g σ a) m e x := by
      intro x hx
      unfold linOp
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [lwtG_dyAvg_eq hg t (m t x) x hx (hint_abs t)]
    have hlevel : volume {x : ℝ | a < linOp g m e x}
        ≤ volume (lwtOmStar σ a) + volume {x : ℝ | a < ell2F (lwtG g σ a) x} := by
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro x hx
      by_cases hxstar : x ∈ lwtOmStar σ a
      · exact Or.inl hxstar
      · refine Or.inr ?_
        have hx' : a < linOp g m e x := hx
        rw [hlin_eq x hxstar] at hx'
        exact lt_of_lt_of_le hx' (linOp_le_ell2F (lwtG g σ a) m e he0 he1 x)
    have hfinal : ENNReal.ofReal (4 / lam) * (∫⁻ x, σ x)
          + ENNReal.ofReal (10 * C₀ ^ (2 : ℝ) / lam) * (∫⁻ x, σ x)
        = ENNReal.ofReal ((4 + 10 * C₀ ^ (2 : ℝ)) / lam) * (∫⁻ x, σ x) := by
      rw [show (4 + 10 * C₀ ^ (2 : ℝ)) / lam = 4 / lam + 10 * C₀ ^ (2 : ℝ) / lam by ring,
        ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    exact (hlevel.trans (add_le_add hvol_star hvol_level)).trans hfinal.le

end Work.BourgainPlan.Maximal
