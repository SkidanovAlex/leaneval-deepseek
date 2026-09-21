import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.JM_diag
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.Kernel.Diag

/-!
# The manifest data agrees with the paper's data on the region of use

The long-interval fixed point engine is applied to the *manifest* data
(`Work.OddVolterra.KernelExt.GoddM`, `ThetaM`), whose kernel entries are polynomials in the jet of
the radicand (hence smooth wherever the radicand is positive), and the resulting solution is
converted back into a solution of the system of `Work.OddVolterra.Defs` (with `Godd`, `Theta`,
`Xi`).  This file records the conversion facts:

* `KvecM_diag`, and hence `GoddM_eq_Godd`: on the diagonal the manifest and the paper's kernel
  agree (`JM_diag`), so `GoddM = Godd` *everywhere*, with no positivity hypothesis;
* `G2M_eq_G2`: on the triangle `s ≤ σ`, when the radicands are positive along the whole segment,
  the two `τ`-averages agree;
* `ThetaM_eq_Theta`: for `s < σ`, with the radicands positive on a left neighbourhood of `s`, the
  two `s`-derivatives agree, so the two `Θ`'s agree.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

lemma JM_diag_fun (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s : ℝ) :
    (fun t : ℝ => Work.OddVolterra.KernelExt.J1M n h s s t) = Work.OddVolterra.J1 n h s s ∧
    (fun t : ℝ => Work.OddVolterra.KernelExt.J2M n h s s t) = Work.OddVolterra.J2 n h s s :=
  ⟨funext (fun t => (Work.OddVolterra.KernelExt.JM_diag n hh s t).1),
   funext (fun t => (Work.OddVolterra.KernelExt.JM_diag n hh s t).2)⟩

/-- On the diagonal the manifest and the paper's kernels agree (no positivity hypothesis). -/
lemma KvecM_diag (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s : ℝ)
    (x y x' y' : ℝ) :
    Work.OddVolterra.KernelExt.KvecM n h s s x y x' y' =
      Work.OddVolterra.Kvec n h s s x y x' y' := by
  obtain ⟨hj1, hj2⟩ := JM_diag_fun n hh s
  have hK1 : ∀ t : ℝ,
      Work.OddVolterra.KernelExt.K1M n h s s t = Work.OddVolterra.K1 n h s s t := by
    intro t
    simp only [Work.OddVolterra.KernelExt.K1M, Work.OddVolterra.K1]
    rw [show Work.OddVolterra.KernelExt.J1M n h s s t = Work.OddVolterra.J1 n h s s t from
      congrFun hj1 t]
  have hK2 : ∀ t : ℝ,
      Work.OddVolterra.KernelExt.K2M n h s s t = Work.OddVolterra.K2 n h s s t := by
    intro t
    simp only [Work.OddVolterra.KernelExt.K2M, Work.OddVolterra.K2]
    rw [show Work.OddVolterra.KernelExt.J2M n h s s t = Work.OddVolterra.J2 n h s s t from
      congrFun hj2 t]
  funext i
  fin_cases i <;>
    simp only [Work.OddVolterra.KernelExt.KvecM, Work.OddVolterra.Kvec, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, hK1, hK2]

/-- **`GoddM` is `Godd`** for every state and every slope. -/
theorem GoddM_eq_Godd (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (s : ℝ)
    (z : Work.OddVolterra.St) :
    Work.OddVolterra.KernelExt.GoddM n h s z = Work.OddVolterra.Godd n h s z := by
  have hG2 : Work.OddVolterra.KernelExt.G2M n h s s (z 0) (z 1) (z 2) (z 3)
      = Work.OddVolterra.G2 n h s s (z 0) (z 1) (z 2) (z 3) := by
    funext i
    simp only [Work.OddVolterra.KernelExt.G2M, Work.OddVolterra.G2]
    apply intervalIntegral.integral_congr
    intro τ _
    simp only [show ∀ x : ℝ, s + x * (s - s) = s from fun x => by ring]
    rw [KvecM_diag n hh s]
  funext i
  fin_cases i <;> simp [Work.OddVolterra.KernelExt.GoddM, Work.OddVolterra.Godd, hG2]

/-- `KvecM_eq_Kvec` in the shape needed below: positivity of the radicands is stated through
`krad`. -/
lemma KvecM_eq_Kvec' (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {a σ : ℝ} (haσ : a ≤ σ) (x y x' y' : ℝ)
    (h1 : 0 < Work.OddVolterra.krad h σ y a) (h2 : 0 < Work.OddVolterra.krad h σ (-x) a) :
    Work.OddVolterra.KernelExt.KvecM n h a σ x y x' y' =
      Work.OddVolterra.Kvec n h a σ x y x' y' := by
  refine Work.OddVolterra.KernelExt.KvecM_eq_Kvec n hn hh haσ x y x' y' ?_ ?_
  · simpa only [Work.OddVolterra.krad] using h1
  · simpa only [Work.OddVolterra.krad] using h2

/-- **`G2M = G2` on the triangle**, when the radicands stay positive along the segment. -/
theorem G2M_eq_G2 (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ : ℝ} (hsσ : s ≤ σ) (x y x' y' : ℝ)
    (h1 : ∀ a ∈ Set.Icc s σ, 0 < Work.OddVolterra.krad h σ (-x) a)
    (h2 : ∀ a ∈ Set.Icc s σ, 0 < Work.OddVolterra.krad h σ y a) :
    Work.OddVolterra.KernelExt.G2M n h s σ x y x' y' =
      Work.OddVolterra.G2 n h s σ x y x' y' := by
  funext i
  simp only [Work.OddVolterra.KernelExt.G2M, Work.OddVolterra.G2]
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hτ
  have ha : s + τ * (σ - s) ∈ Set.Icc s σ := by
    constructor
    · nlinarith [hτ.1, hsσ, hτ.1]
    · nlinarith [hτ.2, hsσ]
  have hK := KvecM_eq_Kvec' n hn hh ha.2 x y x' y' (h2 _ ha) (h1 _ ha)
  exact congrArg (fun v : Fin 2 → ℝ => v i / Real.sqrt (τ * (1 - τ))) hK

/-- **`ThetaM = Theta`** for `s < σ`, when the radicands are positive on a left neighbourhood of
`s` (the region on which both are given by the derivative of their respective `τ`-averages). -/
theorem ThetaM_eq_Theta (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {s σ δ : ℝ} (hsσ : s < σ) (hδ : 0 < δ) (z : Work.OddVolterra.St)
    (h1 : ∀ a ∈ Set.Icc (s - δ) σ, 0 < Work.OddVolterra.krad h σ (-(z 0)) a)
    (h2 : ∀ a ∈ Set.Icc (s - δ) σ, 0 < Work.OddVolterra.krad h σ (z 1) a) :
    Work.OddVolterra.KernelExt.ThetaM n h s σ z = Work.OddVolterra.Theta n h s σ z := by
  have hsδ : s - δ < s := by linarith
  have hsσ' : s < (s + σ) / 2 := by linarith
  have hmid : (s + σ) / 2 < σ := by linarith
  have hev : (fun u : ℝ => Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3))
      =ᶠ[𝓝 s] (fun u : ℝ => Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo (show s ∈ Set.Ioo (s - δ) ((s + σ) / 2) from
      ⟨hsδ, hsσ'⟩)] with u hu
    refine G2M_eq_G2 n hn hh (le_of_lt (lt_trans hu.2 hmid)) _ _ _ _ ?_ ?_
    · intro a ha
      exact h1 a ⟨le_of_lt (lt_of_lt_of_le hu.1 ha.1), ha.2⟩
    · intro a ha
      exact h2 a ⟨le_of_lt (lt_of_lt_of_le hu.1 ha.1), ha.2⟩
  have hder : ∀ i : Fin 2,
      deriv (fun u : ℝ =>
        (Work.OddVolterra.KernelExt.G2M n h u σ (z 0) (z 1) (z 2) (z 3)) i) s =
      deriv (fun u : ℝ =>
        (Work.OddVolterra.G2 n h u σ (z 0) (z 1) (z 2) (z 3)) i) s := by
    intro i
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hev] with u hu
    exact congrFun hu i
  funext i
  fin_cases i <;>
    simp [Work.OddVolterra.KernelExt.ThetaM, Work.OddVolterra.Theta, hder]

end

end Work.OddVolterra.Window
