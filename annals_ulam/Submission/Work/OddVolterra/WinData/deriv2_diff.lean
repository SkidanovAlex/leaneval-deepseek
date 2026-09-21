import Mathlib
import Submission.Work.OddVolterra.WinData.deriv2_core
import Submission.Work.OddVolterra.Window.KvecJet_data
import Submission.Work.OddVolterra.Window.TW2_kvecM_state_unif

/-!
# Smoothness of the jet curve and of the manifest Abel kernel in the first slot

The manifest kernel `KvecM n h · σ z` is the composite `Phi_j ∘ KJet n h σ z` of a fixed smooth
function of the finite jet with the jet curve (`KvecM_row0`, `KvecM_row1`).  This file records the
two consequences used by the estimate files: the jet curve is `C^∞` (for every `h`), and a
component of `KvecM` is `C^∞` in the first slot at every point where the two radicands are
positive.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

open Work.OddVolterra Work.OddVolterra.Window Work.OddVolterra.KernelExt

/-- **The jet curve is `C^∞`.** -/
lemma contDiff_KJet (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ : ℝ) (z : St) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) := by
  rw [contDiff_pi]
  intro i
  cases i with
  | aa => exact contDiff_id
  | sg => exact contDiff_const
  | t1 => exact contDiff_const
  | t2 => exact contDiff_const
  | kd1 => simpa using contDiff_krad hh σ (-(z 0))
  | kd2 => simpa using contDiff_krad hh σ (z 1)
  | c2 => exact contDiff_const
  | c3 => exact contDiff_const
  | Z1 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ (-(z 0)) v) :=
      (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ (-(z 0)))
    simpa [kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  | Z2 k =>
    have hF : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => (σ - v) * krad h σ (z 1) v) :=
      (contDiff_const.sub contDiff_id).mul (contDiff_krad hh σ (z 1))
    simpa [kjet, iteratedDeriv_eq_iterate] using hF.iterate_deriv k.1
  | w j => simpa [iteratedDeriv_eq_iterate] using hh.iterate_deriv (j.1 + 1)

/-- **A component of `KvecM` is `C^∞` in the first slot** wherever the two radicands are positive. -/
lemma contDiffAt_KvecM_comp (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ x : ℝ} (hσ : 1 / 4 ≤ σ) (hx : 3 / 16 ≤ x)
    {z : St} (hz0 : 1 / 5 ≤ z 0) (hz1 : 1 / 5 ≤ z 1) (j : Fin 2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => (KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) x := by
  have hA : (0 : ℝ) < 3 / 16 := by norm_num
  have hz0pos : (0 : ℝ) ≤ z 0 := by linarith
  have hz1pos : (0 : ℝ) ≤ z 1 := by linarith
  have ht1 : (1 / 5 : ℝ) ≤ |-(z 0)| := by rw [abs_neg, abs_of_nonneg hz0pos]; exact hz0
  have ht2 : (1 / 5 : ℝ) ≤ |z 1| := by rw [abs_of_nonneg hz1pos]; exact hz1
  have hpos1 : 0 < krad h σ (-(z 0)) x :=
    krad_pos_of_pos hsupp hsmall hA (by linarith) (by linarith) ht1
  have hpos2 : 0 < krad h σ (z 1) x :=
    krad_pos_of_pos hsupp hsmall hA (by linarith) (by linarith) ht2
  have hmem : KJet n h σ z x ∈ KJopen n := by
    constructor
    · simpa using hpos1
    · simpa using hpos2
  have hJ : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n h σ z u) x :=
    (contDiff_KJet n hh σ z).contDiffAt
  rcases fin2_cases j with h | h
  · subst h
    have hPhi : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => KF1 n v) (KJet n h σ z x) :=
      (KvecJet_smooth n).1.contDiffAt ((isOpen_KJopen n).mem_nhds hmem)
    have hcomp := hPhi.comp x hJ
    have hid : (fun u : ℝ => (KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 0)
        = fun u : ℝ => KF1 n (KJet n h σ z u) := funext fun u => KvecM_row0 n hh u σ z
    rw [hid]
    change ContDiffAt ℝ (⊤ : ℕ∞) ((fun v : KJIx n → ℝ => KF1 n v) ∘ KJet n h σ z) x
    exact hcomp
  · subst h
    have hPhi : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : KJIx n → ℝ => Phi2 n v) (KJet n h σ z x) :=
      (contDiffOn_Phi2 n).contDiffAt ((isOpen_KJopen n).mem_nhds hmem)
    have hcomp := hPhi.comp x hJ
    have hid : (fun u : ℝ => (KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) 1)
        = fun u : ℝ => Phi2 n (KJet n h σ z u) := funext fun u => KvecM_row1 n hh u σ z
    rw [hid]
    change ContDiffAt ℝ (⊤ : ℕ∞) ((fun v : KJIx n → ℝ => Phi2 n v) ∘ KJet n h σ z) x
    exact hcomp

/-- **Differentiability of a component of `KvecM` and of its first-slot derivative.** -/
lemma differentiableAt_KvecM_comp_and_deriv (n : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ x : ℝ} (hσ : 1 / 4 ≤ σ) (hx : 3 / 16 ≤ x)
    {z : St} (hz0 : 1 / 5 ≤ z 0) (hz1 : 1 / 5 ≤ z 1) (j : Fin 2) :
    DifferentiableAt ℝ (fun u : ℝ => (KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j) x ∧
    DifferentiableAt ℝ (deriv (fun u : ℝ => (KvecM n h u σ (z 0) (z 1) (z 2) (z 3)) j)) x := by
  have hcd := contDiffAt_KvecM_comp n hh hsupp hsmall hσ hx hz0 hz1 j
  refine ⟨hcd.differentiableAt (by simp), ?_⟩
  exact (ContDiffAt.derivWithin hcd (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)

end

end Work.OddVolterra.WinData
