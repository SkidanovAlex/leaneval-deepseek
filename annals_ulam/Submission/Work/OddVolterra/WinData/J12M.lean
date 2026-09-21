import Mathlib
import Submission.Work.OddExistence.Manifest
import Submission.Work.OddExistence.Manifest.aw_toolkit
import Submission.Work.OddExistence.Manifest.zrad_sharp
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.Rnu_spec
import Submission.Work.OddVolterra.KernelExt.Rnu_contDiff
import Submission.Work.OddVolterra.KernelExt.fderiv_fst_eq_deriv
import Submission.Work.OddVolterra.WinData.Basic

/-!
# Jet bounds for the manifest numerators `J1M`, `J2M` on a general slope box

Copied (with the namespace changed) from `Submission/Work/OddExistence/Manifest/thetaM_close.lean`,
where the same statement is proved; the proof only uses the stable modules `Manifest.aw_toolkit`
(`rnu_jet_bound`, `jetC`) and `Manifest.zrad_sharp` (`Zrad_jet_bounds_sharp`).
-/

namespace Work.OddVolterra.WinData

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddExistence.Manifest
open Work.OddVolterra
open Work.OddVolterra.KernelExt

noncomputable section

theorem J12M_jet_bound_box (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ x ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 2 →
      ((|J1M n h x σ t - J1M n 0 x σ t| ≤ C * δ ∧
        |deriv (fun y : ℝ => J1M n h y σ t) x -
         deriv (fun y : ℝ => J1M n 0 y σ t) x| ≤ C * δ ∧
        |J1M n 0 x σ t| ≤ C ∧
        |deriv (fun y : ℝ => J1M n 0 y σ t) x| ≤ C) ∧
       (|J2M n h x σ t - J2M n 0 x σ t| ≤ C * δ ∧
        |deriv (fun y : ℝ => J2M n h y σ t) x -
         deriv (fun y : ℝ => J2M n 0 y σ t) x| ≤ C * δ ∧
        |J2M n 0 x σ t| ≤ C ∧
        |deriv (fun y : ℝ => J2M n 0 y σ t) x| ≤ C)) := by
  obtain ⟨CZ, hCZ0, hZsharp⟩ := ZS.Zrad_jet_bounds_sharp n
  set MZ : ℕ → ℝ := fun _ => CZ with hMZ
  set KZ : ℕ → ℝ := fun _ => 3 * CZ with hKZ
  have hMZn : ∀ i, 0 ≤ MZ i := fun i => by rw [hMZ]; exact hCZ0
  have hKZn : ∀ i, 0 ≤ KZ i := fun i => by rw [hKZ]; positivity
  set C1 : ℝ := AW.jetC ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) (n+1) 0 with hC1
  set C2 : ℝ := AW.jetC ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) (n+1) 1 with hC2
  set C3 : ℝ := AW.jetC ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) n 0 with hC3
  set C4 : ℝ := AW.jetC ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) n 1 with hC4
  have hC1n : 0 ≤ C1 := by
    rw [hC1]
    exact AW.jetC_nonneg ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) hMZn hKZn (fun _ => le_refl 0) (fun _ => zero_le_one) (n+1) 0
  have hC2n : 0 ≤ C2 := by
    rw [hC2]
    exact AW.jetC_nonneg ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) hMZn hKZn (fun _ => le_refl 0) (fun _ => zero_le_one) (n+1) 1
  have hC3n : 0 ≤ C3 := by
    rw [hC3]
    exact AW.jetC_nonneg ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) hMZn hKZn (fun _ => zero_le_one) (fun _ => by norm_num) n 0
  have hC4n : 0 ≤ C4 := by
    rw [hC4]
    exact AW.jetC_nonneg ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) hMZn hKZn (fun _ => zero_le_one) (fun _ => by norm_num) n 1
  refine ⟨max (max C1 C2) (max C3 C4) + 1, by
    have : (0:ℝ) ≤ max (max C1 C2) (max C3 C4) :=
      le_trans hC1n (le_max_of_le_left (le_max_left _ _))
    linarith, ?_⟩
  have hC1le : C1 ≤ max (max C1 C2) (max C3 C4) + 1 := by
    have h : C1 ≤ max (max C1 C2) (max C3 C4) :=
      le_trans (le_max_left C1 C2) (le_max_left (max C1 C2) (max C3 C4))
    linarith
  have hC2le : C2 ≤ max (max C1 C2) (max C3 C4) + 1 := by
    have h : C2 ≤ max (max C1 C2) (max C3 C4) :=
      le_trans (le_max_right C1 C2) (le_max_left (max C1 C2) (max C3 C4))
    linarith
  have hC3le : C3 ≤ max (max C1 C2) (max C3 C4) + 1 := by
    have h : C3 ≤ max (max C1 C2) (max C3 C4) :=
      le_trans (le_max_left C3 C4) (le_max_right (max C1 C2) (max C3 C4))
    linarith
  have hC4le : C4 ≤ max (max C1 C2) (max C3 C4) + 1 := by
    have h : C4 ≤ max (max C1 C2) (max C3 C4) :=
      le_trans (le_max_right C3 C4) (le_max_right (max C1 C2) (max C3 C4))
    linarith
  intro h δ hh hδ hδ1 hjet x hx σ hσ t ht5 ht2
  have hδ0 : 0 ≤ δ := hδ.le
  have hδ1' : δ ≤ 1 := le_trans hδ1 (by norm_num)
  have hσ01 : σ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt (lt_of_lt_of_le ha hσ.1), le_trans hσ.2 hb⟩
  have ht2' : -2 ≤ t := (abs_le.mp ht2).1
  have ht2'' : t ≤ 2 := (abs_le.mp ht2).2
  -- Zrad jet hypotheses on the box, for all indices ≤ n+2
  have hZh : ∀ i, i ≤ n + 2 → ∀ a' ∈ Set.Icc a b,
      |iteratedDeriv i (fun v : ℝ => Zrad h (v, σ, t)) a'| ≤ MZ i + 2 * KZ i := by
    intro i hi a' ha'
    have ha'01 : a' ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_of_lt (lt_of_lt_of_le ha ha'.1), le_trans ha'.2 hb⟩
    have h1 := (hZsharp h δ hh hδ0 hδ1' hjet σ hσ01 t ht2 a' ha'01).1 i hi
    have h2 : MZ i + 2 * KZ i = 7 * CZ := by rw [hMZ, hKZ]; dsimp only; ring
    rw [h2]
    linarith [h1, hCZ0]
  have hZd : ∀ i, i ≤ n + 2 → ∀ a' ∈ Set.Icc a b,
      |iteratedDeriv i (fun v : ℝ => Zrad h (v, σ, t)) a' -
       iteratedDeriv i (fun v : ℝ => Zrad 0 (v, σ, t)) a'| ≤ KZ i * δ := by
    intro i hi a' ha'
    have ha'01 : a' ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_of_lt (lt_of_lt_of_le ha ha'.1), le_trans ha'.2 hb⟩
    have h1 := (hZsharp h δ hh hδ0 hδ1' hjet σ hσ01 t ht2 a' ha'01).2 i hi
    rw [hKZ]
    simp only
    have h2 : |t| + δ ≤ 3 := by linarith [ht2, hδ1']
    calc |iteratedDeriv i (fun v : ℝ => Zrad h (v, σ, t)) a' -
          iteratedDeriv i (fun v : ℝ => Zrad 0 (v, σ, t)) a'|
        ≤ CZ * δ * (|t| + δ) := h1
      _ ≤ CZ * δ * 3 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * CZ * δ := by ring
  have hjet0 : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k (0:ℝ → ℝ) s| ≤ δ := by
    intro k hk s
    rw [show (0:ℝ → ℝ) = fun _ : ℝ => (0:ℝ) from rfl, iteratedDeriv_const]
    split_ifs <;> simpa using hδ0
  have hZ0 : ∀ i, i ≤ n + 2 → ∀ a' ∈ Set.Icc a b,
      |iteratedDeriv i (fun v : ℝ => Zrad 0 (v, σ, t)) a'| ≤ MZ i := by
    intro i hi a' ha'
    have ha'01 : a' ∈ Set.Icc (0:ℝ) 1 :=
      ⟨le_of_lt (lt_of_lt_of_le ha ha'.1), le_trans ha'.2 hb⟩
    have h1 := (hZsharp (fun _ : ℝ => 0) δ contDiff_const hδ0 hδ1' hjet0 σ hσ01 t ht2
      a' ha'01).1 i hi
    rw [hMZ]
    exact h1
  -- the constant initial datum `1`
  have hI1d : ∀ j, j ≤ n + 2 → ∀ a' ∈ Set.Icc a b,
      |iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1:ℝ)) (a, σ, t)) a' -
       iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1:ℝ)) (a, σ, t)) a'|
        ≤ (0:ℝ) * δ := by
    intro j hj a' ha'; simp
  have hI10 : ∀ j, j ≤ n + 2 → ∀ a' ∈ Set.Icc a b,
      |iteratedDeriv j (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1:ℝ)) (a, σ, t)) a'| ≤ (1:ℝ) := by
    intro j hj a' ha'
    rw [show (fun a : ℝ => (fun _ : ℝ × ℝ × ℝ => (1:ℝ)) (a, σ, t)) = fun _ : ℝ => (1:ℝ)
      from rfl, iteratedDeriv_const]
    split_ifs <;> norm_num
  -- the initial datum `∂_s L = t + h'`
  have hlin1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) := by
    unfold lineSlope; fun_prop
  have hlin0 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℝ => lineSlope (0:ℝ → ℝ) p.1 p.2.2) := by
    have hzero : (fun p : ℝ × ℝ × ℝ => lineSlope (0:ℝ → ℝ) p.1 p.2.2) = fun p => p.2.2 := by
      funext p; simp [lineSlope]
    rw [hzero]; fun_prop
  have hI2d : ∀ j, j ≤ n + 1 → ∀ a' ∈ Set.Icc a b,
      |iteratedDeriv j (fun a : ℝ => lineSlope h a t) a' -
       iteratedDeriv j (fun a : ℝ => lineSlope (0:ℝ → ℝ) a t) a'| ≤ (1:ℝ) * δ := by
    intro j hj a' ha'
    have he : (fun a : ℝ => lineSlope h a t) - (fun a : ℝ => lineSlope (0:ℝ → ℝ) a t)
        = fun a : ℝ => deriv h a := by
      funext a; simp [lineSlope]
    have hlin1a : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => lineSlope h a t) := by
      unfold lineSlope; fun_prop
    have hlin0a : ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => lineSlope (0:ℝ → ℝ) a t) := by
      have hzero : (fun a : ℝ => lineSlope (0:ℝ → ℝ) a t) = fun _ : ℝ => t := by
        funext a; simp [lineSlope]
      rw [hzero]; fun_prop
    rw [← iteratedDeriv_sub (hlin1a.contDiffAt.of_le (AW.natCast_le_top_enat j))
      (hlin0a.contDiffAt.of_le (AW.natCast_le_top_enat j)), he]
    have hs : iteratedDeriv j (fun a : ℝ => deriv h a) a' = iteratedDeriv (j + 1) h a' := by
      rw [iteratedDeriv_succ' (f := h) (n := j)]
    rw [hs]
    simpa using hjet (j + 1) (by omega) a'
  have hI20 : ∀ j, j ≤ n + 1 → ∀ a' ∈ Set.Icc a b,
      |iteratedDeriv j (fun a : ℝ => lineSlope (0:ℝ → ℝ) a t) a'| ≤ (2:ℝ) := by
    intro j hj a' ha'
    have heq : (fun a : ℝ => lineSlope (0:ℝ → ℝ) a t) = fun _ : ℝ => t := by
      funext a; simp [lineSlope]
    rw [heq, iteratedDeriv_const]
    split_ifs with hj0
    · rw [abs_le]; exact ⟨ht2', ht2''⟩
    · norm_num
  -- the four applications of the abstract recursion bound
  have hJ1_0 := (AW.rnu_jet_bound ((n:ℝ)+1/2) (n+1) a b KZ MZ (fun _ => 0) (fun _ => 1)
      hKZn hMZn (fun _ => le_refl 0) (fun _ => zero_le_one)
      h (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) hh contDiff_const contDiff_const
      σ t δ hδ0 hδ1' hZh hZd hZ0 hI1d hI10 (n+1) 0 (by omega) x hx)
  have hJ1_1 := (AW.rnu_jet_bound ((n:ℝ)+1/2) (n+1) a b KZ MZ (fun _ => 0) (fun _ => 1)
      hKZn hMZn (fun _ => le_refl 0) (fun _ => zero_le_one)
      h (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) hh contDiff_const contDiff_const
      σ t δ hδ0 hδ1' hZh hZd hZ0 hI1d hI10 (n+1) 1 (by omega) x hx)
  have hJ2_0 := (AW.rnu_jet_bound ((n:ℝ)-1/2) n a b KZ MZ (fun _ => 1) (fun _ => 2)
      hKZn hMZn (fun _ => zero_le_one) (fun _ => by norm_num)
      h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => lineSlope (0:ℝ → ℝ) p.1 p.2.2) hh hlin1 hlin0
      σ t δ hδ0 hδ1'
      (fun i hi a' ha' => hZh i (by omega) a' ha') (fun i hi a' ha' => hZd i (by omega) a' ha')
      (fun i hi a' ha' => hZ0 i (by omega) a' ha')
      (fun j hj a' ha' => hI2d j (by omega) a' ha') (fun j hj a' ha' => hI20 j (by omega) a' ha')
      n 0 (by omega) x hx)
  have hJ2_1 := (AW.rnu_jet_bound ((n:ℝ)-1/2) n a b KZ MZ (fun _ => 1) (fun _ => 2)
      hKZn hMZn (fun _ => zero_le_one) (fun _ => by norm_num)
      h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2)
      (fun p : ℝ × ℝ × ℝ => lineSlope (0:ℝ → ℝ) p.1 p.2.2) hh hlin1 hlin0
      σ t δ hδ0 hδ1'
      (fun i hi a' ha' => hZh i (by omega) a' ha') (fun i hi a' ha' => hZd i (by omega) a' ha')
      (fun i hi a' ha' => hZ0 i (by omega) a' ha')
      (fun j hj a' ha' => hI2d j (by omega) a' ha') (fun j hj a' ha' => hI20 j (by omega) a' ha')
      n 1 (by omega) x hx)
  have hJ1M_h (y : ℝ) : J1M n h y σ t = iteratedDeriv 0
      (fun a : ℝ => Rnu ((n:ℝ)+1/2) h (fun _ => (1:ℝ)) (n+1) (a, σ, t)) y := rfl
  have hJ1M_0 (y : ℝ) : J1M n 0 y σ t = iteratedDeriv 0
      (fun a : ℝ => Rnu ((n:ℝ)+1/2) 0 (fun _ => (1:ℝ)) (n+1) (a, σ, t)) y := rfl
  have hJ2M_h (y : ℝ) : J2M n h y σ t = iteratedDeriv 0
      (fun a : ℝ => Rnu ((n:ℝ)-1/2) h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) n
        (a, σ, t)) y := rfl
  have hJ2M_0 (y : ℝ) : J2M n 0 y σ t = iteratedDeriv 0
      (fun a : ℝ => Rnu ((n:ℝ)-1/2) 0 (fun p : ℝ × ℝ × ℝ => lineSlope (0:ℝ → ℝ) p.1 p.2.2) n
        (a, σ, t)) y := rfl
  have hd1 : deriv (fun y : ℝ => J1M n h y σ t) x = iteratedDeriv 1
      (fun a : ℝ => Rnu ((n:ℝ)+1/2) h (fun _ => (1:ℝ)) (n+1) (a, σ, t)) x := by
    rw [iteratedDeriv_one]; simp only [J1M]
  have hd2 : deriv (fun y : ℝ => J1M n 0 y σ t) x = iteratedDeriv 1
      (fun a : ℝ => Rnu ((n:ℝ)+1/2) 0 (fun _ => (1:ℝ)) (n+1) (a, σ, t)) x := by
    rw [iteratedDeriv_one]; simp only [J1M]
  have hd3 : deriv (fun y : ℝ => J2M n h y σ t) x = iteratedDeriv 1
      (fun a : ℝ => Rnu ((n:ℝ)-1/2) h (fun p : ℝ × ℝ × ℝ => lineSlope h p.1 p.2.2) n
        (a, σ, t)) x := by
    rw [iteratedDeriv_one]; simp only [J2M]
  have hd4 : deriv (fun y : ℝ => J2M n 0 y σ t) x = iteratedDeriv 1
      (fun a : ℝ => Rnu ((n:ℝ)-1/2) 0 (fun p : ℝ × ℝ × ℝ => lineSlope (0:ℝ → ℝ) p.1 p.2.2) n
        (a, σ, t)) x := by
    rw [iteratedDeriv_one]; simp only [J2M]
  have hb1 : AW.jetC ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) (n+1) 0 * δ
      ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
    rw [← hC1]; exact mul_le_mul_of_nonneg_right hC1le hδ0
  have hb2 : AW.jetC ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) (n+1) 1 * δ
      ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
    rw [← hC2]; exact mul_le_mul_of_nonneg_right hC2le hδ0
  have hb3 : AW.jetC ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) n 0 * δ
      ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
    rw [← hC3]; exact mul_le_mul_of_nonneg_right hC3le hδ0
  have hb4 : AW.jetC ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) n 1 * δ
      ≤ (max (max C1 C2) (max C3 C4) + 1) * δ := by
    rw [← hC4]; exact mul_le_mul_of_nonneg_right hC4le hδ0
  have hv1 : AW.jetC ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) (n+1) 0
      ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC1]; exact hC1le
  have hv2 : AW.jetC ((n:ℝ)+1/2) MZ KZ (fun _ => 0) (fun _ => 1) (n+1) 1
      ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC2]; exact hC2le
  have hv3 : AW.jetC ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) n 0
      ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC3]; exact hC3le
  have hv4 : AW.jetC ((n:ℝ)-1/2) MZ KZ (fun _ => 1) (fun _ => 2) n 1
      ≤ max (max C1 C2) (max C3 C4) + 1 := by rw [← hC4]; exact hC4le
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hJ1M_h x, hJ1M_0 x]; exact le_trans hJ1_0.1 hb1
  · rw [hd1, hd2]; exact le_trans hJ1_1.1 hb2
  · rw [hJ1M_0 x]; exact le_trans hJ1_0.2 hv1
  · rw [hd2]; exact le_trans hJ1_1.2 hv2
  · rw [hJ2M_h x, hJ2M_0 x]; exact le_trans hJ2_0.1 hb3
  · rw [hd3, hd4]; exact le_trans hJ2_1.1 hb4
  · rw [hJ2M_0 x]; exact le_trans hJ2_0.2 hv3
  · rw [hd4]; exact le_trans hJ2_1.2 hv4

end

end Work.OddVolterra.WinData
