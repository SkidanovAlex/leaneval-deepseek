import Mathlib
import Submission.Work.OddVolterra.Window.KvecDefs
import Submission.Work.OddVolterra.Window.TWU_aux
import Submission.Work.OddVolterra.Window.TWU_zrad_jet_lipschitz

namespace Work.OddVolterra.Window

/-- State-Lipschitz of the jet curve `KJet` at `u ∈ [9/20, 1]`, i.e. without the restriction
`u ≤ σ`: this is `TWU_kjet_state_lipschitz_local` in `Submission/Work/OddVolterra/Window/TWU_aux.lean`
with the single hypothesis `u ∈ Icc (9/20) σ` weakened to `u ∈ Icc (9/20) 1` (that proof uses
`u ≤ σ` only to obtain `u ∈ Icc (9/20) 1`).  Copy that proof with `hu9 := hu`. -/
theorem KJet_state_lipschitz_window (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) →
      ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ u ∈ Set.Icc (9 / 20 : ℝ) 1,
      ∀ Z Z' : Work.OddVolterra.St,
        (1 / 5 ≤ Z 0) → (1 / 5 ≤ Z 1) → (∀ i : Fin 4, |Z i| ≤ 2) →
        (1 / 5 ≤ Z' 0) → (1 / 5 ≤ Z' 1) → (∀ i : Fin 4, |Z' i| ≤ 2) →
        ‖Work.OddVolterra.Window.KJet n h σ Z u - Work.OddVolterra.Window.KJet n h σ Z' u‖ ≤ K * ‖Z - Z'‖ ∧
        ‖deriv (fun u' : ℝ => Work.OddVolterra.Window.KJet n h σ Z u') u -
         deriv (fun u' : ℝ => Work.OddVolterra.Window.KJet n h σ Z' u') u‖ ≤ K * ‖Z - Z'‖ := by
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
  have hu9 : u ∈ Set.Icc (9 / 20 : ℝ) 1 := hu
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
end Work.OddVolterra.Window
