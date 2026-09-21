import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.Window.KvecDefs
import Submission.Work.OddVolterra.Window.KvecJet_data
import Submission.Work.OddVolterra.Window.TWU_zrad_jet_lipschitz
import Submission.Work.OddExistence.Manifest.aw_toolkit
import Submission.Work.OddVolterra.Window.Kvec_deriv_close
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.Existence.krad_pos_state_region

/-!
# Auxiliary uniform estimates for the truncated odd `Θ`-datum `TW`

This file collects the uniform (in the perturbation `h`) estimates on the Abelian data of the
odd transition window which feed the final Lipschitz statement `TW_lipschitz_unif`.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## `krad` is uniformly Lipschitz in `t` (also for the `a`-derivative) -/

/-- `hquot h · σ` is `C^∞`. -/
lemma hquot_slice_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) :=
  (Work.OddVolterra.Existence.hquot_contDiff hh).comp (contDiff_id.prodMk contDiff_const)

/-- Explicit form of the `a`-derivative of `krad`. -/
lemma deriv_krad_eq {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t a : ℝ) :
    deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a
      = t ^ 2 + t * (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
            + deriv h a + Work.OddVolterra.hquot h a σ)
        + (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (h σ + h a)
            + Work.OddVolterra.hquot h a σ * deriv h a) := by
  have hhc : ContDiff ℝ (⊤ : ℕ∞) (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) :=
    hquot_slice_contDiff hh σ
  have hH : HasDerivAt (fun a' : ℝ => Work.OddVolterra.hquot h a' σ)
      (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a) a :=
    (hhc.differentiable (by simp) a).hasDerivAt
  have hl : HasDerivAt (fun a' : ℝ => Work.OddVolterra.line h a' t) (t + deriv h a) a := by
    have h1 : HasDerivAt (fun a' : ℝ => a' * t) (1 * t) a := (hasDerivAt_id a).mul_const t
    have h2 : HasDerivAt h (deriv h a) a := (hh.differentiable (by simp) a).hasDerivAt
    have h3 : HasDerivAt (fun a' : ℝ => a' * t + h a') (1 * t + deriv h a) a := h1.add h2
    rw [show (1 : ℝ) * t = t by ring] at h3
    simpa [Work.OddVolterra.line] using h3
  have hk : (fun a' : ℝ => Work.OddVolterra.krad h σ t a')
      = (fun a' : ℝ => t + Work.OddVolterra.hquot h a' σ) *
          (fun a' : ℝ => Work.OddVolterra.line h σ t + Work.OddVolterra.line h a' t) := by
    funext a'; rw [Work.OddVolterra.krad_apply]; rfl
  have hprod := (HasDerivAt.const_add t hH).mul
    (HasDerivAt.const_add (Work.OddVolterra.line h σ t) hl)
  rw [hk, hprod.deriv]
  simp only [Work.OddVolterra.line, Pi.mul_apply]
  ring

theorem TWU_krad_lipschitz_local (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ σ ∈ Set.Icc (9 / 20 : ℝ) 1, ∀ a ∈ Set.Icc (9 / 20 : ℝ) 1,
      ∀ t ∈ Set.Icc (-2 : ℝ) 2, ∀ t' ∈ Set.Icc (-2 : ℝ) 2,
        |Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad h σ t' a| ≤ K * |t - t'| ∧
        |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a -
         deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t' a') a| ≤ K * |t - t'| := by
  refine ⟨10, by norm_num, ?_⟩
  intro h hh hjet σ hσ a ha t ht t' ht'
  have hh0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hjet 0 (by omega) x
  have hh1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := fun x => by
    simpa [iteratedDeriv_one] using hjet 1 (by omega) x
  have hh2 : ∀ x : ℝ, |iteratedDeriv 2 h x| ≤ 1 / 100 := fun x => hjet 2 (by omega) x
  have hq : |Work.OddVolterra.hquot h a σ| ≤ 1 / 100 :=
    Work.OddExistence.Manifest.AW.abs_hquot_le_state hh1
  have hqd : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a| ≤ 1 / 100 :=
    (Work.OddExistence.Manifest.AW.hquot_deriv_bound hh (by norm_num) hh1 hh2 a σ).2
  have haabs : |a| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], ha.2⟩
  have hσabs : |σ| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
  have hSabs : |σ + a| ≤ 2 := by
    rw [abs_le] at haabs hσabs ⊢
    constructor <;> linarith [haabs.1, haabs.2, hσabs.1, hσabs.2]
  have htabs : |t| ≤ 2 := abs_le.mpr ⟨ht.1, ht.2⟩
  have ht'abs : |t'| ≤ 2 := abs_le.mpr ⟨ht'.1, ht'.2⟩
  have htt : |t + t'| ≤ 4 := by
    rw [abs_le] at htabs ht'abs ⊢
    constructor <;> linarith [htabs.1, htabs.2, ht'abs.1, ht'abs.2]
  -- first conjunct
  constructor
  · have hkey : Work.OddVolterra.krad h σ t a - Work.OddVolterra.krad h σ t' a
        = (t - t') * ((σ + a) * (t + t') + (h σ + h a)
            + Work.OddVolterra.hquot h a σ * (σ + a)) := by
      simp only [Work.OddVolterra.krad_apply, Work.OddVolterra.line]
      ring
    rw [hkey, abs_mul]
    have hb : |(σ + a) * (t + t') + (h σ + h a) + Work.OddVolterra.hquot h a σ * (σ + a)| ≤ 10 := by
      have h1 : |(σ + a) * (t + t')| ≤ 8 := by
        rw [abs_mul]
        calc |σ + a| * |t + t'| ≤ 2 * 4 := by
              exact mul_le_mul hSabs htt (abs_nonneg _) (by norm_num)
          _ = 8 := by norm_num
      have h2 : |h σ + h a| ≤ 1 / 50 := by
        calc |h σ + h a| ≤ |h σ| + |h a| := abs_add_le _ _
          _ ≤ 1 / 100 + 1 / 100 := add_le_add (hh0 σ) (hh0 a)
          _ = 1 / 50 := by norm_num
      have h3 : |Work.OddVolterra.hquot h a σ * (σ + a)| ≤ 1 / 50 := by
        rw [abs_mul]
        calc |Work.OddVolterra.hquot h a σ| * |σ + a| ≤ (1 / 100) * 2 :=
              mul_le_mul hq hSabs (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 50 := by norm_num
      calc |(σ + a) * (t + t') + (h σ + h a) + Work.OddVolterra.hquot h a σ * (σ + a)|
          ≤ |(σ + a) * (t + t') + (h σ + h a)|
            + |Work.OddVolterra.hquot h a σ * (σ + a)| := abs_add_le _ _
        _ ≤ |(σ + a) * (t + t')| + |h σ + h a| + |Work.OddVolterra.hquot h a σ * (σ + a)| := by
              linarith [abs_add_le ((σ + a) * (t + t')) (h σ + h a)]
        _ ≤ 8 + 1 / 50 + 1 / 50 := by linarith
        _ ≤ 10 := by norm_num
    calc |t - t'| * |(σ + a) * (t + t') + (h σ + h a)
            + Work.OddVolterra.hquot h a σ * (σ + a)|
        ≤ |t - t'| * 10 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = 10 * |t - t'| := by ring
  · -- second conjunct
    have hd1 := deriv_krad_eq hh σ t a
    have hd2 := deriv_krad_eq hh σ t' a
    rw [hd1, hd2]
    have hB : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
        + deriv h a + Work.OddVolterra.hquot h a σ| ≤ 5 := by
      have h1 : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)| ≤ 1 / 50 := by
        rw [abs_mul]
        calc |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a| * |σ + a|
            ≤ (1 / 100) * 2 := mul_le_mul hqd hSabs (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 50 := by norm_num
      calc |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
            + deriv h a + Work.OddVolterra.hquot h a σ|
          ≤ |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)| + |deriv h a|
            + |Work.OddVolterra.hquot h a σ| := by
            linarith [abs_add_le (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
              + deriv h a) (Work.OddVolterra.hquot h a σ),
              abs_add_le (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a))
                (deriv h a)]
        _ ≤ 1 / 50 + 1 / 100 + 1 / 100 := by linarith [hh1 a, hq]
        _ ≤ 5 := by norm_num
    have hA : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (h σ + h a)
        + Work.OddVolterra.hquot h a σ * deriv h a| ≤ 1 := by
      have h1 : |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (h σ + h a)| ≤ 1 / 500 := by
        rw [abs_mul]
        calc |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a| * |h σ + h a|
            ≤ (1 / 100) * (1 / 50) := mul_le_mul hqd (by
              calc |h σ + h a| ≤ |h σ| + |h a| := abs_add_le _ _
                _ ≤ 1 / 100 + 1 / 100 := add_le_add (hh0 σ) (hh0 a)
                _ = 1 / 50 := by norm_num) (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 500 := by norm_num
      have h2 : |Work.OddVolterra.hquot h a σ * deriv h a| ≤ 1 / 500 := by
        rw [abs_mul]
        calc |Work.OddVolterra.hquot h a σ| * |deriv h a| ≤ (1 / 100) * (1 / 100) :=
              mul_le_mul hq (hh1 a) (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 500 := by norm_num
      linarith [abs_add_le (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (h σ + h a))
        (Work.OddVolterra.hquot h a σ * deriv h a)]
    have hkey : t ^ 2 + t * (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
            + deriv h a + Work.OddVolterra.hquot h a σ)
        + (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (h σ + h a)
            + Work.OddVolterra.hquot h a σ * deriv h a)
        - (t' ^ 2 + t' * (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
            + deriv h a + Work.OddVolterra.hquot h a σ)
        + (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (h σ + h a)
            + Work.OddVolterra.hquot h a σ * deriv h a))
        = (t - t') * (t + t' + (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
            + deriv h a + Work.OddVolterra.hquot h a σ)) := by
      ring
    rw [hkey, abs_mul]
    have hb : |t + t' + (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
          + deriv h a + Work.OddVolterra.hquot h a σ)| ≤ 10 := by
      calc |t + t' + (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
            + deriv h a + Work.OddVolterra.hquot h a σ)|
          ≤ |t + t'| + |deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
              + deriv h a + Work.OddVolterra.hquot h a σ| := abs_add_le _ _
        _ ≤ 4 + 5 := add_le_add htt hB
        _ ≤ 10 := by norm_num
    calc |t - t'| * |t + t' + (deriv (fun a' : ℝ => Work.OddVolterra.hquot h a' σ) a * (σ + a)
            + deriv h a + Work.OddVolterra.hquot h a σ)|
        ≤ |t - t'| * 10 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = 10 * |t - t'| := by ring

/-- The jet curve `u ↦ KJet n h σ z u` is `C^∞` when `h` is. -/
lemma contDiff_KJet_local (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ)
    (z : St) : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) := by
  rw [contDiff_pi]
  intro i
  cases i
  case aa => exact contDiff_id
  case sg => exact contDiff_const
  case t1 => exact contDiff_const
  case t2 => exact contDiff_const
  case kd1 => exact Work.OddVolterra.contDiff_krad hh σ (-(z 0))
  case kd2 => exact Work.OddVolterra.contDiff_krad hh σ (z 1)
  case c2 => exact contDiff_const
  case c3 => exact contDiff_const
  case Z1 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * Work.OddVolterra.krad h σ (-(z 0)) v) :=
      (contDiff_const.sub contDiff_id).mul (Work.OddVolterra.contDiff_krad hh σ (-(z 0)))
    simpa [Work.OddVolterra.kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  case Z2 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * Work.OddVolterra.krad h σ (z 1) v) :=
      (contDiff_const.sub contDiff_id).mul (Work.OddVolterra.contDiff_krad hh σ (z 1))
    simpa [Work.OddVolterra.kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  case w j =>
    simpa [iteratedDeriv_eq_iterate] using hh.iterate_deriv (j.1 + 1)

theorem TWU_kjet_state_lipschitz_local (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ u ∈ Set.Icc (9 / 20 : ℝ) σ,
      ∀ Z Z' : Work.OddVolterra.St,
        (1 / 5 ≤ Z 0) → (1 / 5 ≤ Z 1) → (∀ i : Fin 4, |Z i| ≤ 2) →
        (1 / 5 ≤ Z' 0) → (1 / 5 ≤ Z' 1) → (∀ i : Fin 4, |Z' i| ≤ 2) →
        ‖KJet n h σ Z u - KJet n h σ Z' u‖ ≤ K * ‖Z - Z'‖ ∧
        ‖deriv (fun u' : ℝ => KJet n h σ Z u') u -
         deriv (fun u' : ℝ => KJet n h σ Z' u') u‖ ≤ K * ‖Z - Z'‖ := by
  obtain ⟨K1, hK1nn, hK1⟩ := TWU_zrad_jet_lipschitz n
  obtain ⟨K2, hK2nn, hK2⟩ := TWU_krad_lipschitz_local n
  refine ⟨K1 + K2 + 1, by positivity, ?_⟩
  intro h hh hjet σ hσ u hu Z Z' hZ0 hZ1 hZ hZ'0 hZ'1 hZ'
  have hh1 : ContDiff ℝ (1 : ℕ∞) h := hh.of_le (by norm_num)
  set C : ℝ := K1 + K2 + 1 with hC
  have hCnn : 0 ≤ C := by rw [hC]; linarith
  have hC1K1 : K1 ≤ C := by rw [hC]; linarith
  have hC1K2 : K2 ≤ C := by rw [hC]; linarith
  set r : ℝ := ‖Z - Z'‖ with hr
  have hrnn : 0 ≤ r := by rw [hr]; exact norm_nonneg _
  have hCr : r ≤ C * r := by nlinarith [hrnn, hCnn, hC1K1]
  have hle1 : K1 * r ≤ C * r := mul_le_mul_of_nonneg_right hC1K1 hrnn
  have hle2 : K2 * r ≤ C * r := mul_le_mul_of_nonneg_right hC1K2 hrnn
  have hσ9 : σ ∈ Set.Icc (9 / 20 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  have hu9 : u ∈ Set.Icc (9 / 20 : ℝ) 1 := ⟨hu.1, le_trans hu.2 hσ.2⟩
  have hcoord : ∀ i : Fin 4, |Z i - Z' i| ≤ r := by
    intro i
    have h := norm_le_pi_norm (Z - Z') i
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact h
  have ht1 : |-(Z 0)| ≤ 2 := by rw [abs_neg]; exact hZ 0
  have ht2 : |Z 1| ≤ 2 := hZ 1
  have ht1' : |-(Z' 0)| ≤ 2 := by rw [abs_neg]; exact hZ' 0
  have ht2' : |Z' 1| ≤ 2 := hZ' 1
  have hdt1 : |(-(Z 0)) - (-(Z' 0))| ≤ r := by
    have h := hcoord 0
    rwa [show -(Z 0) - (-(Z' 0)) = -(Z 0 - Z' 0) by ring, abs_neg]
  have hdt2 : |Z 1 - Z' 1| ≤ r := hcoord 1
  have hval : ∀ i : KJIx n, |KJet n h σ Z u i - KJet n h σ Z' u i| ≤ C * r := by
    intro i
    cases i with
    | aa => simp only [KJet_aa, sub_self, abs_zero]; exact mul_nonneg hCnn hrnn
    | sg => simp only [KJet_sg, sub_self, abs_zero]; exact mul_nonneg hCnn hrnn
    | t1 =>
        simp only [KJet_t1]
        rw [show -(Z 0) - (-(Z' 0)) = -(Z 0 - Z' 0) by ring, abs_neg]
        exact le_trans (hcoord 0) hCr
    | t2 => simp only [KJet_t2]; exact le_trans (hcoord 1) hCr
    | kd1 =>
        simp only [KJet_kd1]
        have h := (hK2 h hh hjet σ hσ9 u hu9 (-(Z 0)) (abs_le.mp ht1)
          (-(Z' 0)) (abs_le.mp ht1')).1
        exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt1 hK2nn)) hle2
    | kd2 =>
        simp only [KJet_kd2]
        have h := (hK2 h hh hjet σ hσ9 u hu9 (Z 1) (abs_le.mp ht2)
          (Z' 1) (abs_le.mp ht2')).1
        exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt2 hK2nn)) hle2
    | c2 => simp only [KJet_c2]; exact le_trans (hcoord 2) hCr
    | c3 => simp only [KJet_c3]; exact le_trans (hcoord 3) hCr
    | Z1 k =>
        simp only [KJet_Z1]
        rw [Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (-(Z 0)) u k.1,
          Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (-(Z' 0)) u k.1]
        have hk : k.1 ≤ n + 2 := by omega
        have h := hK1 h hh hjet σ hσ9 u hu9 k.1 hk (-(Z 0)) (abs_le.mp ht1)
          (-(Z' 0)) (abs_le.mp ht1')
        exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt1 hK1nn)) hle1
    | Z2 k =>
        simp only [KJet_Z2]
        rw [Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (Z 1) u k.1,
          Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (Z' 1) u k.1]
        have hk : k.1 ≤ n + 2 := by omega
        have h := hK1 h hh hjet σ hσ9 u hu9 k.1 hk (Z 1) (abs_le.mp ht2)
          (Z' 1) (abs_le.mp ht2')
        exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt2 hK1nn)) hle1
    | w j => simp only [KJet_w, sub_self, abs_zero]; exact mul_nonneg hCnn hrnn
  constructor
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg hCnn hrnn)]
    intro i
    rw [Real.norm_eq_abs]
    exact hval i
  · have hder : ∀ i : KJIx n,
        |deriv (fun u' : ℝ => KJet n h σ Z u' i) u -
         deriv (fun u' : ℝ => KJet n h σ Z' u' i) u| ≤ C * r := by
      intro i
      cases i with
      | aa =>
          simp only [KJet_aa, sub_self, abs_zero]
          exact mul_nonneg hCnn hrnn
      | sg => simp only [KJet_sg, deriv_const, sub_self, abs_zero]
              exact mul_nonneg hCnn hrnn
      | t1 => simp only [KJet_t1, deriv_const, sub_self, abs_zero]
              exact mul_nonneg hCnn hrnn
      | t2 => simp only [KJet_t2, deriv_const, sub_self, abs_zero]
              exact mul_nonneg hCnn hrnn
      | kd1 =>
          simp only [KJet_kd1]
          have h := (hK2 h hh hjet σ hσ9 u hu9 (-(Z 0)) (abs_le.mp ht1)
            (-(Z' 0)) (abs_le.mp ht1')).2
          exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt1 hK2nn)) hle2
      | kd2 =>
          simp only [KJet_kd2]
          have h := (hK2 h hh hjet σ hσ9 u hu9 (Z 1) (abs_le.mp ht2)
            (Z' 1) (abs_le.mp ht2')).2
          exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt2 hK2nn)) hle2
      | c2 => simp only [KJet_c2, deriv_const, sub_self, abs_zero]
              exact mul_nonneg hCnn hrnn
      | c3 => simp only [KJet_c3, deriv_const, sub_self, abs_zero]
              exact mul_nonneg hCnn hrnn
      | Z1 k =>
          simp only [KJet_Z1]
          rw [← Work.OddVolterra.kjet_succ h σ (-(Z 0)) u k.1,
            ← Work.OddVolterra.kjet_succ h σ (-(Z' 0)) u k.1]
          rw [Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (-(Z 0)) u (k.1 + 1),
            Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (-(Z' 0)) u (k.1 + 1)]
          have hk : k.1 + 1 ≤ n + 2 := by omega
          have h := hK1 h hh hjet σ hσ9 u hu9 (k.1 + 1) hk (-(Z 0)) (abs_le.mp ht1)
            (-(Z' 0)) (abs_le.mp ht1')
          exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt1 hK1nn)) hle1
      | Z2 k =>
          simp only [KJet_Z2]
          rw [← Work.OddVolterra.kjet_succ h σ (Z 1) u k.1,
            ← Work.OddVolterra.kjet_succ h σ (Z' 1) u k.1]
          rw [Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (Z 1) u (k.1 + 1),
            Work.OddVolterra.Window.kjet_eq_Zrad hh1 σ (Z' 1) u (k.1 + 1)]
          have hk : k.1 + 1 ≤ n + 2 := by omega
          have h := hK1 h hh hjet σ hσ9 u hu9 (k.1 + 1) hk (Z 1) (abs_le.mp ht2)
            (Z' 1) (abs_le.mp ht2')
          exact le_trans (le_trans h (mul_le_mul_of_nonneg_left hdt2 hK1nn)) hle1
      | w j =>
          simp only [KJet_w, sub_self, abs_zero]
          exact mul_nonneg hCnn hrnn
    have hdZ : DifferentiableAt ℝ (fun u' : ℝ => KJet n h σ Z u') u :=
      ((contDiff_KJet_local n hh σ Z).differentiable (by simp)).differentiableAt
    have hdZ' : DifferentiableAt ℝ (fun u' : ℝ => KJet n h σ Z' u') u :=
      ((contDiff_KJet_local n hh σ Z').differentiable (by simp)).differentiableAt
    have hpiZ : deriv (fun u' : ℝ => KJet n h σ Z u') u
        = fun i => deriv (fun u' : ℝ => KJet n h σ Z u' i) u :=
      deriv_pi (𝕜 := ℝ) (x := u) (φ := fun u' : ℝ => KJet n h σ Z u')
        (fun i => (differentiableAt_pi.mp hdZ) i)
    have hpiZ' : deriv (fun u' : ℝ => KJet n h σ Z' u') u
        = fun i => deriv (fun u' : ℝ => KJet n h σ Z' u' i) u :=
      deriv_pi (𝕜 := ℝ) (x := u) (φ := fun u' : ℝ => KJet n h σ Z' u')
        (fun i => (differentiableAt_pi.mp hdZ') i)
    rw [hpiZ, hpiZ']
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hCnn hrnn)]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact hder i

/-- Bounds and Lipschitz constants of a `C^∞` function on a compact convex box. -/
lemma box_data {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → ℝ) {U : Set E} (hU : IsOpen U) {Kc : Set E} (hcvx : Convex ℝ Kc)
    (hcpt : IsCompact Kc) (hKU : Kc ⊆ U) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) :
    ∃ A L M Lf : ℝ, 0 ≤ A ∧ 0 ≤ L ∧ 0 ≤ M ∧ 0 ≤ Lf ∧
      (∀ x ∈ Kc, |G x| ≤ A) ∧
      (∀ x ∈ Kc, ∀ y ∈ Kc, |G x - G y| ≤ L * ‖x - y‖) ∧
      (∀ x ∈ Kc, ‖fderiv ℝ G x‖ ≤ M) ∧
      (∀ x ∈ Kc, ∀ y ∈ Kc, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ Lf * ‖x - y‖) := by
  have hGc : ContinuousOn G Kc := (hG.mono hKU).continuousOn
  obtain ⟨A₀, hA₀⟩ := hcpt.exists_bound_of_continuousOn hGc
  obtain ⟨L₀, hL₀⟩ := (hG.mono hKU).exists_lipschitzOnWith (n := (⊤ : ℕ∞)) (by simp) hcvx hcpt
  have hfderiv_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ G) Kc := fun x hx =>
    ((hG.contDiffAt (hU.mem_nhds (hKU hx))).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).contDiffWithinAt
  obtain ⟨M₀, hM₀⟩ := hcpt.exists_bound_of_continuousOn
    ((hG.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU)
  obtain ⟨Lf₀, hLf₀⟩ := hfderiv_cd.exists_lipschitzOnWith (n := (⊤ : ℕ∞)) (by simp) hcvx hcpt
  exact ⟨max A₀ 0, (L₀ : ℝ), max M₀ 0, (Lf₀ : ℝ), le_max_right _ _, L₀.coe_nonneg,
    le_max_right _ _, Lf₀.coe_nonneg,
    fun x hx => le_trans (hA₀ x hx) (le_max_left _ _),
    fun x hx y hy => hL₀.norm_sub_le hx hy,
    fun x hx => le_trans (hM₀ x hx) (le_max_left _ _),
    fun x hx y hy => hLf₀.norm_sub_le hx hy⟩

/-- Positivity of the Abel radicand on the box `[9/20,1]^2`, for `|t| ≥ 1/5`. -/
lemma krad_pos_box_local {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ a t : ℝ} (ha : a ∈ Set.Icc (9 / 20 : ℝ) 1) (hσ1 : σ ≤ 1) (haσ : a ≤ σ)
    (ht : 1 / 5 ≤ |t|) : 0 < Work.OddVolterra.krad h σ t a :=
  Work.OddVolterra.Existence.krad_pos_state_region hsupp hsmall
    (by norm_num : (0:ℝ) < 9 / 20) ha.1 haσ hσ1 ht

/-- The chain rule for the jet curve. -/
lemma deriv_comp_KJet {n : ℕ} {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {σ : ℝ} (Z : St)
    (a : ℝ) {G : (KJIx n → ℝ) → ℝ} (hG : DifferentiableAt ℝ G (KJet n h σ Z a)) :
    deriv (fun a' : ℝ => G (KJet n h σ Z a')) a
      = fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a) := by
  have hK : HasDerivAt (fun u : ℝ => KJet n h σ Z u)
      (deriv (fun u : ℝ => KJet n h σ Z u) a) a :=
    (((contDiff_KJet_local n hh σ Z).differentiable (by simp)).differentiableAt).hasDerivAt
  exact (hG.hasFDerivAt.comp_hasDerivAt a hK).deriv

/-- The uniform componentwise bounds for `KvecM` in the state, on the region `a < σ`. -/
private lemma kvecm_component_bound (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) 1) {a : ℝ} (ha : a ∈ Set.Ico (9 / 20 : ℝ) σ)
    {Z Z' : St} (hZ0 : 1 / 5 ≤ Z 0) (hZ1 : 1 / 5 ≤ Z 1) (hZ : ∀ i : Fin 4, |Z i| ≤ 2)
    (hZ'0 : 1 / 5 ≤ Z' 0) (hZ'1 : 1 / 5 ≤ Z' 1) (hZ' : ∀ i : Fin 4, |Z' i| ≤ 2)
    {j : Fin 2} {G : (KJIx n → ℝ) → ℝ} {A L M Lf Kj Kj' : ℝ}
    (hAnn : 0 ≤ A) (hLnn : 0 ≤ L) (hMnn : 0 ≤ M) (hLfnn : 0 ≤ Lf)
    (hKjnn : 0 ≤ Kj) (hKj'nn : 0 ≤ Kj')
    (hAb : ∀ v ∈ KJbox n (KJbz n), |G v| ≤ A)
    (hLb : ∀ v ∈ KJbox n (KJbz n), ∀ w ∈ KJbox n (KJbz n), |G v - G w| ≤ L * ‖v - w‖)
    (hMb : ∀ v ∈ KJbox n (KJbz n), ‖fderiv ℝ G v‖ ≤ M)
    (hLfb : ∀ v ∈ KJbox n (KJbz n), ∀ w ∈ KJbox n (KJbz n),
      ‖fderiv ℝ G v - fderiv ℝ G w‖ ≤ Lf * ‖v - w‖)
    (hGcd : ∀ v ∈ KJbox n (KJbz n), DifferentiableAt ℝ G v)
    (hid : ∀ a' σ' Z'', a' < σ' → 0 < Work.OddVolterra.krad h σ' (-(Z'' 0)) a' →
      0 < Work.OddVolterra.krad h σ' (Z'' 1) a' →
      Work.OddVolterra.KernelExt.KvecM n h a' σ' (Z'' 0) (Z'' 1) (Z'' 2) (Z'' 3) j
        = G (KJet n h σ' Z'' a'))
    (hKjb : ‖KJet n h σ Z a - KJet n h σ Z' a‖ ≤ Kj * ‖Z - Z'‖)
    (hKj'b : ‖deriv (fun u : ℝ => KJet n h σ Z u) a
        - deriv (fun u : ℝ => KJet n h σ Z' u) a‖ ≤ Kj' * ‖Z - Z'‖) :
    |Work.OddVolterra.KernelExt.KvecM n h a σ (Z 0) (Z 1) (Z 2) (Z 3) j| ≤ max A (M * KJbz n) ∧
    |deriv (fun a' : ℝ =>
        Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j) a|
      ≤ max A (M * KJbz n) ∧
    |Work.OddVolterra.KernelExt.KvecM n h a σ (Z 0) (Z 1) (Z 2) (Z 3) j
      - Work.OddVolterra.KernelExt.KvecM n h a σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j|
        ≤ max (L * Kj) (M * Kj' + Lf * KJbz n * Kj) * ‖Z - Z'‖ ∧
    |deriv (fun a' : ℝ =>
        Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j) a
      - deriv (fun a' : ℝ =>
        Work.OddVolterra.KernelExt.KvecM n h a' σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j) a|
        ≤ max (L * Kj) (M * Kj' + Lf * KJbz n * Kj) * ‖Z - Z'‖ := by
  have hBz0 : 0 ≤ KJbz n := KJbz_nonneg n
  have hBz1 : 1 ≤ KJbz n := one_le_KJbz n
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hjet k (by omega) s
  have hσ9 : σ ∈ Set.Icc (9 / 20 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2⟩
  have ha9 : (9 / 20 : ℝ) ≤ a := ha.1
  have haσ : a < σ := ha.2
  have haI : a ∈ Set.Icc (9 / 20 : ℝ) 1 := ⟨ha.1, le_trans ha.2.le hσ.2⟩
  have ht1 : (1 / 5 : ℝ) ≤ |-(Z 0)| := by rw [abs_neg]; exact le_trans hZ0 (le_abs_self _)
  have ht2 : (1 / 5 : ℝ) ≤ |Z 1| := le_trans hZ1 (le_abs_self _)
  have hkpos1 : 0 < Work.OddVolterra.krad h σ (-(Z 0)) a :=
    krad_pos_box_local hsupp hsmall1 haI hσ.2 ha.2.le ht1
  have hkpos2 : 0 < Work.OddVolterra.krad h σ (Z 1) a :=
    krad_pos_box_local hsupp hsmall1 haI hσ.2 ha.2.le ht2
  -- the jet data
  obtain ⟨hmem1, hcd1, -, hder1, -, -, -⟩ :=
    KvecJet_data n hn hh (δ := 1 / 100) (σ := σ) (z := Z) (by norm_num) le_rfl hsupp
      (fun k hk s => hjet k hk s) hσ hZ0 hZ1 hZ a ⟨ha.1, ha.2.le⟩
  obtain ⟨hmem2, hcd2, -, hder2, -, -, -⟩ :=
    KvecJet_data n hn hh (δ := 1 / 100) (σ := σ) (z := Z') (by norm_num) le_rfl hsupp
      (fun k hk s => hjet k hk s) hσ hZ'0 hZ'1 hZ' a ⟨ha.1, ha.2.le⟩
  -- the eventual identity
  have hev : (fun a' : ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j)
      =ᶠ[𝓝 a] (fun a' : ℝ => G (KJet n h σ Z a')) := by
    have h1 : ∀ᶠ a' in 𝓝 a, a' < σ := isOpen_Iio.mem_nhds haσ
    have h2 : ∀ᶠ a' in 𝓝 a, 0 < Work.OddVolterra.krad h σ (-(Z 0)) a' :=
      (Work.OddVolterra.continuous_krad hh σ (-(Z 0))).continuousAt.eventually
        (isOpen_Ioi.mem_nhds hkpos1)
    have h3 : ∀ᶠ a' in 𝓝 a, 0 < Work.OddVolterra.krad h σ (Z 1) a' :=
      (Work.OddVolterra.continuous_krad hh σ (Z 1)).continuousAt.eventually
        (isOpen_Ioi.mem_nhds hkpos2)
    filter_upwards [h1, h2, h3] with a' h1' h2' h3'
    exact hid a' σ Z h1' h2' h3'
  have hev' : (fun a' : ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h a' σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j)
      =ᶠ[𝓝 a] (fun a' : ℝ => G (KJet n h σ Z' a')) := by
    have h1 : ∀ᶠ a' in 𝓝 a, a' < σ := isOpen_Iio.mem_nhds haσ
    have h2 : ∀ᶠ a' in 𝓝 a, 0 < Work.OddVolterra.krad h σ (-(Z' 0)) a' := by
      have hp : 0 < Work.OddVolterra.krad h σ (-(Z' 0)) a :=
        krad_pos_box_local hsupp hsmall1 haI hσ.2 ha.2.le (by rw [abs_neg]; exact le_trans hZ'0 (le_abs_self _))
      exact (Work.OddVolterra.continuous_krad hh σ (-(Z' 0))).continuousAt.eventually
        (isOpen_Ioi.mem_nhds hp)
    have h3 : ∀ᶠ a' in 𝓝 a, 0 < Work.OddVolterra.krad h σ (Z' 1) a' := by
      have hp : 0 < Work.OddVolterra.krad h σ (Z' 1) a :=
        krad_pos_box_local hsupp hsmall1 haI hσ.2 ha.2.le (le_trans hZ'1 (le_abs_self _))
      exact (Work.OddVolterra.continuous_krad hh σ (Z' 1)).continuousAt.eventually
        (isOpen_Ioi.mem_nhds hp)
    filter_upwards [h1, h2, h3] with a' h1' h2' h3'
    exact hid a' σ Z' h1' h2' h3'
  -- value bound
  have hval : |Work.OddVolterra.KernelExt.KvecM n h a σ (Z 0) (Z 1) (Z 2) (Z 3) j|
      ≤ max A (M * KJbz n) := by
    rw [hid a σ Z haσ hkpos1 hkpos2]
    exact le_trans (hAb _ hmem1) (le_max_left _ _)
  -- derivative: chain rule
  have hchain : deriv (fun a' : ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j) a
      = fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a) := by
    rw [hev.deriv_eq]
    exact deriv_comp_KJet hh Z a (hGcd _ hmem1)
  have hchain' : deriv (fun a' : ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h a' σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j) a
      = fderiv ℝ G (KJet n h σ Z' a) (deriv (fun u : ℝ => KJet n h σ Z' u) a) := by
    rw [hev'.deriv_eq]
    exact deriv_comp_KJet hh Z' a (hGcd _ hmem2)
  have hder : |deriv (fun a' : ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j) a|
      ≤ max A (M * KJbz n) := by
    rw [hchain]
    calc |fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a)|
        = ‖fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ G (KJet n h σ Z a)‖ * ‖deriv (fun u : ℝ => KJet n h σ Z u) a‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * KJbz n := mul_le_mul (hMb _ hmem1) hder1 (norm_nonneg _) hMnn
      _ ≤ max A (M * KJbz n) := le_max_right _ _
  -- Lipschitz in the state
  have hlip : |Work.OddVolterra.KernelExt.KvecM n h a σ (Z 0) (Z 1) (Z 2) (Z 3) j
      - Work.OddVolterra.KernelExt.KvecM n h a σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j|
      ≤ max (L * Kj) (M * Kj' + Lf * KJbz n * Kj) * ‖Z - Z'‖ := by
    rw [hid a σ Z haσ hkpos1 hkpos2,
      hid a σ Z' haσ
        (krad_pos_box_local hsupp hsmall1 haI hσ.2 ha.2.le
          (by rw [abs_neg]; exact le_trans hZ'0 (le_abs_self _)))
        (krad_pos_box_local hsupp hsmall1 haI hσ.2 ha.2.le (le_trans hZ'1 (le_abs_self _)))]
    calc |G (KJet n h σ Z a) - G (KJet n h σ Z' a)|
        ≤ L * ‖KJet n h σ Z a - KJet n h σ Z' a‖ := hLb _ hmem1 _ hmem2
      _ ≤ L * (Kj * ‖Z - Z'‖) := mul_le_mul_of_nonneg_left hKjb hLnn
      _ = (L * Kj) * ‖Z - Z'‖ := by ring
      _ ≤ max (L * Kj) (M * Kj' + Lf * KJbz n * Kj) * ‖Z - Z'‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hlider : |deriv (fun a' : ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j) a
      - deriv (fun a' : ℝ =>
      Work.OddVolterra.KernelExt.KvecM n h a' σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j) a|
      ≤ max (L * Kj) (M * Kj' + Lf * KJbz n * Kj) * ‖Z - Z'‖ := by
    rw [hchain, hchain']
    have hsplit : fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a)
        - fderiv ℝ G (KJet n h σ Z' a) (deriv (fun u : ℝ => KJet n h σ Z' u) a)
        = fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a
            - deriv (fun u : ℝ => KJet n h σ Z' u) a)
          + (fderiv ℝ G (KJet n h σ Z a) - fderiv ℝ G (KJet n h σ Z' a))
            (deriv (fun u : ℝ => KJet n h σ Z' u) a) := by
      rw [map_sub, sub_apply]; abel
    rw [hsplit]
    calc |fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a
            - deriv (fun u : ℝ => KJet n h σ Z' u) a)
          + (fderiv ℝ G (KJet n h σ Z a) - fderiv ℝ G (KJet n h σ Z' a))
            (deriv (fun u : ℝ => KJet n h σ Z' u) a)|
        = ‖fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a
            - deriv (fun u : ℝ => KJet n h σ Z' u) a)
          + (fderiv ℝ G (KJet n h σ Z a) - fderiv ℝ G (KJet n h σ Z' a))
            (deriv (fun u : ℝ => KJet n h σ Z' u) a)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ G (KJet n h σ Z a) (deriv (fun u : ℝ => KJet n h σ Z u) a
            - deriv (fun u : ℝ => KJet n h σ Z' u) a)‖
          + ‖(fderiv ℝ G (KJet n h σ Z a) - fderiv ℝ G (KJet n h σ Z' a))
            (deriv (fun u : ℝ => KJet n h σ Z' u) a)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ G (KJet n h σ Z a)‖ *
            ‖deriv (fun u : ℝ => KJet n h σ Z u) a
              - deriv (fun u : ℝ => KJet n h σ Z' u) a‖
          + ‖fderiv ℝ G (KJet n h σ Z a) - fderiv ℝ G (KJet n h σ Z' a)‖ *
            ‖deriv (fun u : ℝ => KJet n h σ Z' u) a‖ :=
          add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      _ ≤ M * (Kj' * ‖Z - Z'‖) + (Lf * ‖KJet n h σ Z a - KJet n h σ Z' a‖) * KJbz n :=
          add_le_add
            (mul_le_mul (hMb _ hmem1) hKj'b (norm_nonneg _) hMnn)
            (mul_le_mul (hLfb _ hmem1 _ hmem2) hder2 (norm_nonneg _)
              (mul_nonneg hLfnn (norm_nonneg _)))
      _ ≤ M * (Kj' * ‖Z - Z'‖) + (Lf * (Kj * ‖Z - Z'‖)) * KJbz n := by
          have h1 : Lf * ‖KJet n h σ Z a - KJet n h σ Z' a‖ ≤ Lf * (Kj * ‖Z - Z'‖) :=
            mul_le_mul_of_nonneg_left hKjb hLfnn
          nlinarith [h1, hBz0, hder2, hLfnn]
      _ = (M * Kj' + Lf * KJbz n * Kj) * ‖Z - Z'‖ := by ring
      _ ≤ max (L * Kj) (M * Kj' + Lf * KJbz n * Kj) * ‖Z - Z'‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  exact ⟨hval, hder, hlip, hlider⟩

/-- **Uniform componentwise bounds for `KvecM` and its first-slot derivative on the region
`a < σ`, together with their Lipschitz dependence on the state.** -/
theorem TWU_kvecm_state_lipschitz_local (n : ℕ) (hn : 1 ≤ n) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ a ∈ Set.Ico (9 / 20 : ℝ) σ,
      ∀ Z Z' : St,
        (1 / 5 ≤ Z 0) → (1 / 5 ≤ Z 1) → (∀ i : Fin 4, |Z i| ≤ 2) →
        (1 / 5 ≤ Z' 0) → (1 / 5 ≤ Z' 1) → (∀ i : Fin 4, |Z' i| ≤ 2) →
        (∀ j : Fin 2, |Work.OddVolterra.KernelExt.KvecM n h a σ (Z 0) (Z 1) (Z 2) (Z 3) j| ≤ C) ∧
        (∀ j : Fin 2, |deriv (fun a' : ℝ =>
          Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j) a| ≤ C) ∧
        (∀ j : Fin 2, |Work.OddVolterra.KernelExt.KvecM n h a σ (Z 0) (Z 1) (Z 2) (Z 3) j
          - Work.OddVolterra.KernelExt.KvecM n h a σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j|
            ≤ K * ‖Z - Z'‖) ∧
        (∀ j : Fin 2, |deriv (fun a' : ℝ =>
            Work.OddVolterra.KernelExt.KvecM n h a' σ (Z 0) (Z 1) (Z 2) (Z 3) j) a
          - deriv (fun a' : ℝ =>
            Work.OddVolterra.KernelExt.KvecM n h a' σ (Z' 0) (Z' 1) (Z' 2) (Z' 3) j) a|
            ≤ K * ‖Z - Z'‖) := by
  obtain ⟨A1, L1, M1, Lf1, hA1nn, hL1nn, hM1nn, hLf1nn, hA1, hL1, hM1, hLf1⟩ :=
    box_data (KF1 n) (isOpen_KJopen n) (convex_KJbox n (KJbz n)) (isCompact_KJbox n (KJbz n))
      (KJbox_subset_KJopen n (KJbz n)) (KvecJet_smooth n).1
  obtain ⟨A2, L2, M2, Lf2, hA2nn, hL2nn, hM2nn, hLf2nn, hA2, hL2, hM2, hLf2⟩ :=
    box_data (KF2 n) (isOpen_KJopen n) (convex_KJbox n (KJbz n)) (isCompact_KJbox n (KJbz n))
      (KJbox_subset_KJopen n (KJbz n)) (KvecJet_smooth n).2
  obtain ⟨Kj, hKjnn, hKj⟩ := TWU_kjet_state_lipschitz_local n
  have hCnn : 0 ≤ max (max A1 (M1 * KJbz n)) (max A2 (M2 * KJbz n)) :=
    le_trans hA1nn (le_trans (le_max_left A1 (M1 * KJbz n))
      (le_max_left (max A1 (M1 * KJbz n)) (max A2 (M2 * KJbz n))))
  have hKnn : 0 ≤ max (max (L1 * Kj) (M1 * Kj + Lf1 * KJbz n * Kj))
      (max (L2 * Kj) (M2 * Kj + Lf2 * KJbz n * Kj)) :=
    le_trans (mul_nonneg hL1nn hKjnn)
      (le_trans (le_max_left (L1 * Kj) (M1 * Kj + Lf1 * KJbz n * Kj))
        (le_max_left _ _))
  refine ⟨max (max A1 (M1 * KJbz n)) (max A2 (M2 * KJbz n)),
    max (max (L1 * Kj) (M1 * Kj + Lf1 * KJbz n * Kj))
      (max (L2 * Kj) (M2 * Kj + Lf2 * KJbz n * Kj)), hCnn, hKnn, ?_⟩
  intro h hh hsupp hjet σ hσ a ha Z Z' hZ0 hZ1 hZ hZ'0 hZ'1 hZ'
  have hkJ := hKj h hh hjet σ hσ a ⟨ha.1, ha.2.le⟩ Z Z' hZ0 hZ1 hZ hZ'0 hZ'1 hZ'
  have hgcd1 : ∀ v ∈ KJbox n (KJbz n), DifferentiableAt ℝ (KF1 n) v := fun v hv =>
    ((KvecJet_smooth n).1.contDiffAt ((isOpen_KJopen n).mem_nhds
      (KJbox_subset_KJopen n (KJbz n) hv))).differentiableAt (by simp)
  have hgcd2 : ∀ v ∈ KJbox n (KJbz n), DifferentiableAt ℝ (KF2 n) v := fun v hv =>
    ((KvecJet_smooth n).2.contDiffAt ((isOpen_KJopen n).mem_nhds
      (KJbox_subset_KJopen n (KJbz n) hv))).differentiableAt (by simp)
  have hid1 : ∀ a' σ' Z'', a' < σ' → 0 < Work.OddVolterra.krad h σ' (-(Z'' 0)) a' →
      0 < Work.OddVolterra.krad h σ' (Z'' 1) a' →
      Work.OddVolterra.KernelExt.KvecM n h a' σ' (Z'' 0) (Z'' 1) (Z'' 2) (Z'' 3) 0
        = KF1 n (KJet n h σ' Z'' a') := by
    intro a' σ' Z'' hlt hp1 hp2
    rw [KvecM_eq_Kvec' n hn hh hlt.le (Z'' 0) (Z'' 1) (Z'' 2) (Z'' 3) hp2 hp1]
    exact Kvec_zero_eq_KF1 hh hlt hp1 hp2
  have hid2 : ∀ a' σ' Z'', a' < σ' → 0 < Work.OddVolterra.krad h σ' (-(Z'' 0)) a' →
      0 < Work.OddVolterra.krad h σ' (Z'' 1) a' →
      Work.OddVolterra.KernelExt.KvecM n h a' σ' (Z'' 0) (Z'' 1) (Z'' 2) (Z'' 3) 1
        = KF2 n (KJet n h σ' Z'' a') := by
    intro a' σ' Z'' hlt hp1 hp2
    rw [KvecM_eq_Kvec' n hn hh hlt.le (Z'' 0) (Z'' 1) (Z'' 2) (Z'' 3) hp2 hp1]
    exact Kvec_one_eq_KF2 hh hn hlt hp1 hp2
  have h0 := kvecm_component_bound n hn hh hsupp hjet hσ ha hZ0 hZ1 hZ hZ'0 hZ'1 hZ'
    (j := 0) (G := KF1 n) (A := A1) (L := L1) (M := M1) (Lf := Lf1) (Kj := Kj) (Kj' := Kj)
    hA1nn hL1nn hM1nn hLf1nn hKjnn hKjnn hA1 hL1 hM1 hLf1 hgcd1 hid1 hkJ.1 hkJ.2
  have h1 := kvecm_component_bound n hn hh hsupp hjet hσ ha hZ0 hZ1 hZ hZ'0 hZ'1 hZ'
    (j := 1) (G := KF2 n) (A := A2) (L := L2) (M := M2) (Lf := Lf2) (Kj := Kj) (Kj' := Kj)
    hA2nn hL2nn hM2nn hLf2nn hKjnn hKjnn hA2 hL2 hM2 hLf2 hgcd2 hid2 hkJ.1 hkJ.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j
    · exact le_trans h0.1 (le_max_left (max A1 (M1 * KJbz n)) (max A2 (M2 * KJbz n)))
    · exact le_trans h1.1 (le_max_right (max A1 (M1 * KJbz n)) (max A2 (M2 * KJbz n)))
  · intro j; fin_cases j
    · exact le_trans h0.2.1 (le_max_left (max A1 (M1 * KJbz n)) (max A2 (M2 * KJbz n)))
    · exact le_trans h1.2.1 (le_max_right (max A1 (M1 * KJbz n)) (max A2 (M2 * KJbz n)))
  · intro j; fin_cases j
    · refine le_trans h0.2.2.1 ?_
      exact mul_le_mul_of_nonneg_right
        (le_max_left (max (L1 * Kj) (M1 * Kj + Lf1 * KJbz n * Kj))
          (max (L2 * Kj) (M2 * Kj + Lf2 * KJbz n * Kj))) (norm_nonneg _)
    · refine le_trans h1.2.2.1 ?_
      exact mul_le_mul_of_nonneg_right
        (le_max_right (max (L1 * Kj) (M1 * Kj + Lf1 * KJbz n * Kj))
          (max (L2 * Kj) (M2 * Kj + Lf2 * KJbz n * Kj))) (norm_nonneg _)
  · intro j; fin_cases j
    · refine le_trans h0.2.2.2 ?_
      exact mul_le_mul_of_nonneg_right
        (le_max_left (max (L1 * Kj) (M1 * Kj + Lf1 * KJbz n * Kj))
          (max (L2 * Kj) (M2 * Kj + Lf2 * KJbz n * Kj))) (norm_nonneg _)
    · refine le_trans h1.2.2.2 ?_
      exact mul_le_mul_of_nonneg_right
        (le_max_right (max (L1 * Kj) (M1 * Kj + Lf1 * KJbz n * Kj))
          (max (L2 * Kj) (M2 * Kj + Lf2 * KJbz n * Kj))) (norm_nonneg _)

end

end Work.OddVolterra.Window
