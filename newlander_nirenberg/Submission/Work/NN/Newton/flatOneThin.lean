import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.Polydisc.isClosedForm_dbarCoord
import Submission.Work.CR.Flat.Cauchy.dbar_interior_oneshot_C0
import Submission.Work.CR.Flat.Holder.holderNorm_comp_add
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.NN.Final.iterDerivNorm_comp_smul
import Submission.Work.NN.Ratio.Setup
import Submission.Work.NN.Ratio.recU_solves_local
import Submission.Work.NN.Ratio.recU_estimate_nc
import Submission.Work.NN.Ratio.contDiff_recU
import Submission.Work.NN.Ratio.contDiffOn_recU
import Submission.Work.NN.Newton.ThinProfile.thinProfile
import Submission.Work.NN.Newton.ThinSup.recU_norm_le
import Submission.Work.NN.Newton.ThinLocal.localGain
import Submission.Work.NN.Newton.ThinCover.holderNorm_two_le_of_local

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

/-! ## helper lemmas -/

lemma flatOneThin_dbarCoord_congr {n : ℕ} {f g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (h : f =ᶠ[nhds z] g) (j : Fin n) :
    Work.CR.Flat.dbarCoord j f z = Work.CR.Flat.dbarCoord j g z := by
  unfold Work.CR.Flat.dbarCoord
  rw [h.fderiv_eq]

/-- Membership in a polydisc centred at the origin. -/
lemma flatOneThin_mem_pd0 {n : ℕ} {r : Fin n → ℝ} {z : Fin n → ℂ} :
    z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) r ↔ ∀ j, ‖z j‖ < r j := by
  rw [Work.CR.Flat.mem_polydisc]
  simp

/-! ## the arithmetic bound -/

lemma flatOneThin_arith {r δ KL Cu : ℝ} {s : ℝ} {n : ℕ}
    (hr1 : 1 / 2 ≤ r) (hr4 : r ≤ 4) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hs : s = r * δ / 64) (hKL0 : 0 < KL) (hCu0 : 0 ≤ Cu) :
    (6 + 6 / s) * (KL / s ^ 3) * (s + Cu / δ ^ n)
      ≤ (792 * KL * 128 ^ 3 * (1 + Cu)) / δ ^ (n + 4) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hδ1 : δ ≤ 1 := by linarith
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hs1' : s ≤ 1 := by rw [hs]; nlinarith
  -- (1)
  have h1 : 6 + 6 / s ≤ 792 / δ := by
    have hs' : 6 / s = 384 / (r * δ) := by rw [hs]; field_simp; norm_num
    rw [hs', le_div_iff₀ hδ0]
    have h : 384 / (r * δ) * δ = 384 / r := by field_simp
    rw [add_mul, h]
    have h1a : 6 * δ ≤ 6 * (1 / 4) := by linarith
    have h1b : 384 / r ≤ 384 / (1 / 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hr1
    norm_num at h1b
    linarith
  -- (2)
  have h2 : KL / s ^ 3 ≤ KL * 128 ^ 3 / δ ^ 3 := by
    rw [hs]
    field_simp
    have hr3 : (1 / 8 : ℝ) ≤ r ^ 3 := by
      have h3 : (1 / 2 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr1 3
      norm_num at h3 ⊢
      linarith
    nlinarith [hr3]
  -- (3)
  have h3 : s + Cu / δ ^ n ≤ (1 + Cu) / δ ^ n := by
    have hδn : δ ^ n ≤ 1 := pow_le_one₀ hδ0.le hδ1
    have hδnp : (0 : ℝ) < δ ^ n := pow_pos hδ0 n
    have h1' : (1 : ℝ) ≤ 1 / δ ^ n := by rw [le_div_iff₀ hδnp]; simpa using hδn
    have hsle : s ≤ 1 / δ ^ n := le_trans hs1' h1'
    rw [add_div]
    linarith
  -- assemble
  have h4 : (792 * KL * 128 ^ 3 * (1 + Cu)) / δ ^ (n + 4)
      = (792 / δ) * (KL * 128 ^ 3 / δ ^ 3) * ((1 + Cu) / δ ^ n) := by
    rw [pow_add]
    field_simp
  rw [h4]
  have hb : (0 : ℝ) ≤ (792 / δ) * (KL * 128 ^ 3 / δ ^ 3) := by positivity
  have hc : (0 : ℝ) ≤ s + Cu / δ ^ n := by
    have h1 : (0 : ℝ) ≤ Cu / δ ^ n := by
      have : (0 : ℝ) < δ ^ n := pow_pos hδ0 n
      positivity
    linarith
  have hd : (0 : ℝ) ≤ (1 + Cu) / δ ^ n := by positivity
  have hspos : 0 < s := by rw [hs]; positivity
  have he : (0 : ℝ) ≤ KL / s ^ 3 := div_nonneg hKL0.le (pow_nonneg hspos.le 3)
  have hf : (0 : ℝ) ≤ 792 / δ := by positivity
  exact mul_le_mul (mul_le_mul h1 h2 he hf) h3 hc hb


/-! ## the main theorem -/

set_option maxHeartbeats 4000000 in
theorem flatOneThin {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ r δ : ℝ, 1 / 2 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 4 →
      ∀ f : Fin n → Work.NN.Core.Cn n → ℂ,
        (∀ j, ∀ m : ℕ, ContDiffOn ℝ m (f j)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        ∃ u : Work.NN.Core.Cn n → ℂ,
          (∀ m : ℕ, ContDiffOn ℝ m u
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))) ∧
          (∀ j z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) →
            Work.CR.Flat.dbarCoord j u z = f j z) ∧
          Work.CR.Flat.holderNorm 2 α u
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (C / δ ^ N) *
              ∑ j, Work.CR.Flat.holderNorm 1 α (f j)
                (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r)) := by

  classical
  obtain ⟨Kp, hKp0, hKpspec⟩ := Work.NN.Newton.ThinProfile.thinProfile
  obtain ⟨KL, hKL0, hKLspec⟩ := Work.NN.Newton.ThinLocal.localGain (n := n) hn hα0 hα1
  set M : ℝ := max 1 (128 * Kp) with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  set Cu : ℝ := (n : ℝ) * 16 * M ^ n with hCudef
  have hCu0 : (0 : ℝ) ≤ Cu := by rw [hCudef]; positivity
  refine ⟨792 * KL * 128 ^ 3 * (1 + Cu), by positivity, n + 4, ?_⟩
  intro r δ hr1 hr4 hδ0 hδ4 f hf hfcl
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  set s : ℝ := r * δ / 64 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hs1 : s ≤ 1 := by rw [hsdef]; nlinarith
  set a : ℝ := r * (1 - 3 * δ / 4) with hadef
  set b : ℝ := r * (1 - δ / 2) with hbdef
  set e : ℝ := r * (1 - 7 * δ / 8) with hedef
  set Ag : ℝ := r * (1 - 3 * δ / 8) with hAgdef
  set Bg : ℝ := r * (1 - δ / 8) with hBgdef
  -- basic order relations
  have ha_pos : 0 < a := by rw [hadef]; exact mul_pos hr0 (by linarith)
  have hab : a < b := by rw [hadef, hbdef]; nlinarith [mul_pos hr0 hδ0]
  have hbT : b < r := by rw [hbdef]; nlinarith [mul_pos hr0 hδ0]
  have hea : e < a := by rw [hedef, hadef]; nlinarith [mul_pos hr0 hδ0]
  have hr2b : 2 * b ≤ 8 := by rw [hbdef]; nlinarith [hr4, hδ0]
  have ha14 : 1 / 4 ≤ a := by rw [hadef]; nlinarith [hr1, hδ4]
  have hb8 : b ≤ 8 := by rw [hbdef]; nlinarith [hr4, hδ0]
  have hba : b - a = r * δ / 4 := by rw [hbdef, hadef]; ring
  have hAg0 : 0 ≤ Ag := by rw [hAgdef]; nlinarith [hr1, hδ4]
  have hAgBg : Ag < Bg := by rw [hAgdef, hBgdef]; nlinarith [mul_pos hr0 hδ0]
  have hBgr : Bg < r := by rw [hBgdef]; nlinarith [mul_pos hr0 hδ0]
  have hAgr : Ag < r := lt_trans hAgBg hBgr
  have heAg : e < Ag := by rw [hedef, hAgdef]; nlinarith [mul_pos hr0 hδ0]
  -- the profile of the telescoping construction
  obtain ⟨χG, hχG_sm, hχG_one, hχG_zero, hχG_le, hχG_bar_in, hχG_bar_out, hχG_cχ,
    hχG_cχ', hχG_L⟩ := hKpspec a b ha14 hab hb8
  -- the geometric data of the recursion
  let G : Work.NN.Ratio.Geom n :=
    { a := a, b := b, T := r, r := 8, e := e,
      ha := ha_pos, hab := hab, hbT := hbT, hea := hea, hr := hr2b, hr0 := by norm_num,
      χ := χG, hχ_smooth := hχG_sm, hχ_one := hχG_one, hχ_zero := hχG_zero,
      hχ_le := hχG_le, hχbar_in := hχG_bar_in, hχbar_out := hχG_bar_out,
      cχ := Kp / (b - a), hcχ0 := by positivity, hcχ := hχG_cχ,
      cχ' := Kp / (b - a) ^ 2, hcχ'0 := by positivity, hcχ' := hχG_cχ',
      L := Kp / (b - a), hL0 := by positivity, hL := hχG_L }
  -- the global cutoff on the polydisc
  let χg : (Fin n → ℂ) → ℂ := Work.NN.Ratio.polydiscCut (fun _ => Ag) (fun _ => Bg)
  have hχg_sm : ContDiff ℝ ∞ χg := Work.NN.Ratio.contDiff_polydiscCut _ _
  have hχg_one : ∀ z : Fin n → ℂ, (∀ j, ‖z j‖ ≤ Ag) → χg z = 1 := fun z hz =>
    Work.NN.Ratio.polydiscCut_eq_one (fun _ => hAg0) (fun _ => hAgBg) hz
  have hχg_zero : ∀ z : Fin n → ℂ, (∃ j, Bg ≤ ‖z j‖) → χg z = 0 := fun z hz =>
    Work.NN.Ratio.polydiscCut_eq_zero (fun _ => hAg0) (fun _ => hAgBg) hz
  have hχg_le : ∀ z : Fin n → ℂ, ‖χg z‖ ≤ 1 :=
    Work.NN.Ratio.norm_polydiscCut_le_one _ _
  have hχg_tsupp : tsupport χg ⊆ {z : Fin n → ℂ | ∀ j, ‖z j‖ ≤ Bg} :=
    Work.NN.Ratio.tsupport_polydiscCut_subset (fun _ => hAg0) (fun _ => hAgBg)
  -- globalisation of the datum
  let F : Fin n → (Fin n → ℂ) → ℂ := fun j z => χg z * f j z
  have hPr_open : IsOpen (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r)) :=
    Work.CR.Flat.isOpen_polydisc _ _
  have hF_sm : ∀ (j : Fin n) (m : ℕ), ContDiff ℝ m (F j) := by
    intro j m
    have := Work.NN.Ratio.contDiff_mul_of_tsupport_subset hχg_sm hPr_open
      (fun z hz => flatOneThin_mem_pd0.mpr (fun l => lt_of_le_of_lt (hχg_tsupp hz l) hBgr)) (hf j m)
    simpa only [F] using this
  have hF_closed : ∀ (j l : Fin n) (z : Fin n → ℂ), (∀ m, ‖z m‖ < Ag) →
      Work.CR.Flat.dbarCoord l (F j) z = Work.CR.Flat.dbarCoord j (F l) z := by
    intro j l z hz
    have hzAg : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => Ag) := flatOneThin_mem_pd0.mpr hz
    have hmem : Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => Ag) ∈ nhds z :=
      (Work.CR.Flat.isOpen_polydisc _ _).mem_nhds hzAg
    have hev1 : F j =ᶠ[nhds z] f j := by
      filter_upwards [hmem] with w hw
      show χg w * f j w = f j w
      rw [hχg_one w (fun m => le_of_lt ((flatOneThin_mem_pd0.mp hw) m)), one_mul]
    have hev2 : F l =ᶠ[nhds z] f l := by
      filter_upwards [hmem] with w hw
      show χg w * f l w = f l w
      rw [hχg_one w (fun m => le_of_lt ((flatOneThin_mem_pd0.mp hw) m)), one_mul]
    rw [flatOneThin_dbarCoord_congr hev1 l, flatOneThin_dbarCoord_congr hev2 j]
    exact (hfcl j l z (flatOneThin_mem_pd0.mpr (fun m => lt_trans (hz m) hAgr))).symm
  have hF_eq : ∀ (j : Fin n) (z : Fin n → ℂ), (∀ l, ‖z l‖ < e) → F j z = f j z := by
    intro j z hz
    show χg z * f j z = f j z
    rw [hχg_one z (fun l => le_of_lt (lt_trans (hz l) heAg)), one_mul]
  -- the solution
  have hAg_b : b < Ag := by rw [hbdef, hAgdef]; nlinarith [mul_pos hr0 hδ0]
  have hsolve_e : ∀ (i : Fin n) (z : Fin n → ℂ), (∀ l, ‖z l‖ < e) →
      Work.CR.Flat.dbarCoord i (fun z => G.recU F z) z = f i z := by
    intro i z hze
    rw [Work.NN.Ratio.recU_solves_local G hAg_b (fun j => (hF_sm j 1)) hF_closed i z hze]
    exact hF_eq i z hze
  have hsm_all : ∀ m : ℕ, ContDiff ℝ m (fun z => G.recU F z) := by
    intro m
    cases m with
    | zero => exact (Work.NN.Ratio.contDiff_recU G (fun j => hF_sm j 1)).of_le (by simp)
    | succ k => exact Work.NN.Ratio.contDiff_recU G (fun j => hF_sm j (k + 1))
  have hsolve : ∀ (i : Fin n) (z : Fin n → ℂ),
      z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r * (1 - δ)) →
      Work.CR.Flat.dbarCoord i (fun z => G.recU F z) z = f i z := by
    intro i z hz
    refine hsolve_e i z fun l => ?_
    have h1 := (flatOneThin_mem_pd0.mp hz) l
    rw [hedef]
    nlinarith [h1, mul_pos hr0 hδ0]
  have hsm_final : ∀ m : ℕ, ContDiffOn ℝ m (fun z => G.recU F z)
      (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r * (1 - δ))) :=
    fun m => (hsm_all m).contDiffOn
  have hbound : Work.CR.Flat.holderNorm 2 α (fun z => G.recU F z)
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r * (1 - δ)))
      ≤ ENNReal.ofReal (792 * KL * 128 ^ 3 * (1 + Cu) / δ ^ (n + 4)) * ∑ j,
        Work.CR.Flat.holderNorm 1 α (f j)
          (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r)) := by
      set S : ℝ≥0∞ := ∑ j, Work.CR.Flat.holderNorm 1 α (f j)
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r)) with hSdef
      by_cases hStop : S = ⊤
      · rw [hStop, ENNReal.mul_top (by positivity)]
        exact le_top
      · set S0 : ℝ := S.toReal with hS0def
        have hSne : S ≠ ⊤ := hStop
        have hS0nn : 0 ≤ S0 := ENNReal.toReal_nonneg
        have hS_eq : S = ENNReal.ofReal S0 := (ENNReal.ofReal_toReal hSne).symm
        have hf_le : ∀ (j : Fin n) (z : Fin n → ℂ),
            z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r) → ‖f j z‖ ≤ S0 := by
          intro j z hz
          have h1 : ENNReal.ofReal ‖f j z‖ ≤ Work.CR.Flat.holderNorm 1 α (f j)
              (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r)) :=
            Work.CR.Flat.norm_apply_le_holderNorm 1 α (f j) _ hz
          have h2 : Work.CR.Flat.holderNorm 1 α (f j)
              (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r)) ≤ S := by
            rw [hSdef]
            exact Finset.single_le_sum (f := fun i => Work.CR.Flat.holderNorm 1 α (f i)
              (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r))) (fun _ _ => bot_le)
              (Finset.mem_univ j)
          rw [hS0def]
          exact (ENNReal.ofReal_le_iff_le_toReal hSne).mp (le_trans h1 h2)
        have hFs : ∀ (j : Fin n) (z : Fin n → ℂ), ‖F j z‖ ≤ S0 := by
          intro j z
          by_cases hχ : χg z = 0
          · have h0 : F j z = 0 := by
              show χg z * f j z = 0
              rw [hχ, zero_mul]
            rw [h0, norm_zero]
            exact hS0nn
          · have hzB : ∀ m, ‖z m‖ < Bg := by
              by_contra hcon
              push Not at hcon
              obtain ⟨m, hm⟩ := hcon
              exact hχ (hχg_zero z ⟨m, hm⟩)
            have hzr : z ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r) :=
              flatOneThin_mem_pd0.mpr (fun m => lt_trans (hzB m) hBgr)
            calc ‖F j z‖ = ‖χg z‖ * ‖f j z‖ := by
                  show ‖χg z * f j z‖ = ‖χg z‖ * ‖f j z‖
                  rw [norm_mul]
              _ ≤ 1 * ‖f j z‖ := mul_le_mul_of_nonneg_right (hχg_le z) (norm_nonneg _)
              _ = ‖f j z‖ := one_mul _
              _ ≤ S0 := hf_le j z hzr
        have h2r : G.r = 8 := rfl
        have hcχG : max 1 (2 * G.r * G.cχ) ≤ M / δ := by
          show max 1 (2 * 8 * (Kp / (b - a))) ≤ M / δ
          rw [hba]
          have h1 : 16 * (Kp / (r * δ / 4)) ≤ 128 * Kp / δ := by
            rw [le_div_iff₀ hδ0]
            have he : 16 * (Kp / (r * δ / 4)) * δ = 64 * Kp / r := by field_simp; ring
            rw [he, div_le_iff₀ hr0]
            nlinarith [hKp0, hr1]
          have h2 : 128 * Kp / δ ≤ M / δ := by
            have hMle : 128 * Kp ≤ M := by rw [hMdef]; exact le_max_right _ _
            exact div_le_div_of_nonneg_right hMle (le_of_lt hδ0)
          refine max_le ?_ ?_
          · rw [le_div_iff₀ hδ0]
            nlinarith [hM1, hδ4]
          · linarith
        have hu_sup : ∀ z : Fin n → ℂ, ‖G.recU F z‖ ≤ Cu / δ ^ n * S0 := by
          intro z
          have hrec := Work.NN.Newton.ThinSup.recU_norm_le G (A := S0) hS0nn (fun j y => hFs j y) z
          have hpow : (max 1 (2 * G.r * G.cχ)) ^ n ≤ (M / δ) ^ n :=
            pow_le_pow_left₀ (by positivity) hcχG n
          calc ‖G.recU F z‖
              ≤ (n : ℝ) * (2 * G.r) * (max 1 (2 * G.r * G.cχ)) ^ n * S0 := hrec
            _ ≤ (n : ℝ) * (2 * G.r) * (M / δ) ^ n * S0 := by
                have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
                have hr8 : (0 : ℝ) ≤ 2 * G.r := by rw [h2r]; norm_num
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hpow (mul_nonneg hn0 hr8)) hS0nn
            _ = Cu / δ ^ n * S0 := by
                rw [hCudef, h2r, div_pow]
                ring
        set L : ℝ≥0∞ := ENNReal.ofReal (KL / s ^ 3) *
          (ENNReal.ofReal s * S + ENNReal.ofReal (Cu / δ ^ n * S0)) with hLdef
        have hloc : ∀ c : Fin n → ℂ,
            c ∈ Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r * (1 - δ)) →
            Work.CR.Flat.holderNorm 2 α (fun z => G.recU F z)
              (Work.CR.Flat.polydisc c (fun _ => 2 * s)) ≤ L := by
          intro c hc
          have hc' : ∀ i, ‖c i‖ < r * (1 - δ) := flatOneThin_mem_pd0.mp hc
          have heq : ∀ (j : Fin n) (z : Fin n → ℂ), (∀ i, ‖z i - c i‖ < 4 * s) →
              Work.CR.Flat.dbarCoord j (fun z => G.recU F z) z = f j z := by
            intro j z hz
            have hze : ∀ i, ‖z i‖ < e := fun i => by
              have h1 : ‖z i‖ ≤ ‖c i‖ + ‖z i - c i‖ := by
                  calc ‖z i‖ = ‖(z i - c i) + c i‖ := by rw [sub_add_cancel]
                  _ ≤ ‖z i - c i‖ + ‖c i‖ := norm_add_le _ _
                  _ = ‖c i‖ + ‖z i - c i‖ := by ring
              have h2 : r * (1 - δ) + 4 * s < e := by
                rw [hsdef, hedef]; nlinarith [mul_pos hr0 hδ0]
              linarith [hc' i, hz i, h1, h2]
            exact hsolve_e j z hze
          have hloc' := hKLspec (fun z => G.recU F z) f c s (Cu / δ ^ n * S0) hs0 hs1 hsm_all heq hu_sup
          rw [hLdef]
          refine le_trans hloc' ?_
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          refine add_le_add ?_ le_rfl
          have hsum : (∑ j, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
              (Work.CR.Flat.polydisc c (fun _ => 4 * s)))
              ≤ ∑ j, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
                (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r)) := by
            refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ bot_le
            refine Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc _ _)
              (Work.CR.Flat.isOpen_polydisc _ _) ?_ 1 α (f j)
            intro z hz
            have hz' : ∀ i, ‖z i - c i‖ < 4 * s := hz
            refine flatOneThin_mem_pd0.mpr fun i => ?_
            have h1 : ‖z i‖ ≤ ‖c i‖ + ‖z i - c i‖ := by
              calc ‖z i‖ = ‖(z i - c i) + c i‖ := by rw [sub_add_cancel]
                _ ≤ ‖z i - c i‖ + ‖c i‖ := norm_add_le _ _
                _ = ‖c i‖ + ‖z i - c i‖ := by ring
            have h2 : r * (1 - δ) + 4 * s < r := by
              rw [hsdef]; nlinarith [mul_pos hr0 hδ0]
            linarith [hc' i, hz' i, h1, h2]
          calc (∑ j, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
                (Work.CR.Flat.polydisc c (fun _ => 4 * s)))
              ≤ ∑ j, ENNReal.ofReal s * Work.CR.Flat.holderNorm 1 α (f j)
                (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r)) := hsum
            _ = ENNReal.ofReal s * S := by
                rw [hSdef, Finset.mul_sum]
        have hcover := Work.NN.Newton.ThinCover.holderNorm_two_le_of_local hα0 hα1
          (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) (fun _ => r * (1 - δ))) hs0 hs1 hloc
        have hpos_ref : (0 : ℝ) ≤ Cu / δ ^ n * S0 := by
          have : (0 : ℝ) < δ ^ n := pow_pos hδ0 n
          positivity
        have hCuδ : (0 : ℝ) ≤ Cu / δ ^ n := by
          have : (0 : ℝ) < δ ^ n := pow_pos hδ0 n
          positivity
        have hA0 : (0 : ℝ) ≤ (s + Cu / δ ^ n) * S0 := mul_nonneg (by linarith [hs0]) hS0nn
        have hL_eq : L = ENNReal.ofReal ((KL / s ^ 3) * (s + Cu / δ ^ n) * S0) := by
          have hsum : ENNReal.ofReal (Cu / δ ^ n * S0) =
              ENNReal.ofReal (Cu / δ ^ n) * ENNReal.ofReal S0 := ENNReal.ofReal_mul hCuδ
          rw [hLdef, hsum, hS_eq]
          have hinner : ENNReal.ofReal s * ENNReal.ofReal S0 +
              ENNReal.ofReal (Cu / δ ^ n) * ENNReal.ofReal S0
              = ENNReal.ofReal ((s + Cu / δ ^ n) * S0) := by
            rw [← ENNReal.ofReal_mul hs0.le, ← ENNReal.ofReal_mul hCuδ,
              ← ENNReal.ofReal_add (mul_nonneg hs0.le hS0nn) (mul_nonneg hCuδ hS0nn)]
            congr 1
            ring
          rw [hinner, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
        have h60 : (0 : ℝ) ≤ 6 + 6 / s := by positivity
        have hB0 : (0 : ℝ) ≤ 792 * KL * 128 ^ 3 * (1 + Cu) / δ ^ (n + 4) := by
          have : (0 : ℝ) < δ ^ (n + 4) := pow_pos hδ0 _
          positivity
        have hmain : ENNReal.ofReal (6 + 6 / s) * L ≤
            ENNReal.ofReal (792 * KL * 128 ^ 3 * (1 + Cu) / δ ^ (n + 4)) * S := by
          have harith := flatOneThin_arith (r := r) (δ := δ) (KL := KL) (Cu := Cu) (s := s) (n := n)
            hr1 hr4 hδ0 hδ4 rfl hKL0 hCu0
          calc ENNReal.ofReal (6 + 6 / s) * L
              = ENNReal.ofReal (6 + 6 / s) *
                ENNReal.ofReal ((KL / s ^ 3) * (s + Cu / δ ^ n) * S0) := by rw [hL_eq]
            _ = ENNReal.ofReal ((6 + 6 / s) * ((KL / s ^ 3) * (s + Cu / δ ^ n) * S0)) :=
                (ENNReal.ofReal_mul h60).symm
            _ ≤ ENNReal.ofReal ((792 * KL * 128 ^ 3 * (1 + Cu) / δ ^ (n + 4)) * S0) := by
                apply ENNReal.ofReal_le_ofReal
                have h := mul_le_mul_of_nonneg_right harith hS0nn
                linarith [h]
            _ = ENNReal.ofReal (792 * KL * 128 ^ 3 * (1 + Cu) / δ ^ (n + 4)) *
                ENNReal.ofReal S0 := ENNReal.ofReal_mul hB0
            _ = ENNReal.ofReal (792 * KL * 128 ^ 3 * (1 + Cu) / δ ^ (n + 4)) * S := by
                rw [hS_eq]
        calc Work.CR.Flat.holderNorm 2 α (fun z => G.recU F z)
              (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (6 + 6 / s) * L := hcover
          _ ≤ ENNReal.ofReal (792 * KL * 128 ^ 3 * (1 + Cu) / δ ^ (n + 4)) * S := hmain
  exact ⟨fun z => G.recU F z, hsm_final, hsolve, hbound⟩

end Work.NN.Newton
