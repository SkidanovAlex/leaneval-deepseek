import Mathlib
import Submission.Work.L61.Basic

/-!
# `gdom` is open and contains a ball around `0`  (Lemma 6.1 auxiliary)

`gdom d hd = {0} ∪ π(B^u ∪ B^ℓ)`.  Here `π = piExp w = exp(2πi w)`, `B^u` is an open set
containing the half plane `{η < im w}` (`HornData.upper`), and `B^ℓ` is open as well
(`HornData.Bu_open`, `HornData.Bl_open`).

Hence:
* `π(B^u ∪ B^ℓ)` is open, because `π` is an open map (it is `exp` composed with the
  homeomorphism `w ↦ 2πi w`; `Complex.isOpenMap_exp`) and `B^u ∪ B^ℓ` is open;
* the image of the half plane `{η < im w}` is exactly the punctured disc
  `{z | 0 < ‖z‖ < exp(-2πη)}`, so `{0} ∪ π(B^u ∪ B^ℓ)` contains `ball 0 (exp(-2πη))`.

Together these give openness of `{0} ∪ π(B^u ∪ B^ℓ)`.
-/

namespace Work.L61.Push

open MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- `π = piExp` is an open map (composition of `exp` with the homeomorphism `w ↦ 2πi w`). -/
lemma piExp_isOpenMap : IsOpenMap (piExp : ℂ → ℂ) := by
  have hL : IsOpenMap (fun x : ℂ => (2 * (Real.pi : ℂ) * I) * x) := by
    simpa [Homeomorph.coe_mulLeft₀] using
      (Homeomorph.mulLeft₀ (2 * (Real.pi : ℂ) * I) Complex.two_pi_I_ne_zero).isOpenMap
  have h : IsOpenMap (Complex.exp ∘ (fun x : ℂ => (2 * (Real.pi : ℂ) * I) * x)) :=
    Complex.isOpenMap_exp.comp hL
  rwa [show Complex.exp ∘ (fun x : ℂ => (2 * (Real.pi : ℂ) * I) * x) = piExp from rfl] at h

/-- `‖π w‖ = exp(-2π · im w)`: the modulus of `π w` only depends on the imaginary part of `w`. -/
lemma norm_piExp (w : ℂ) : ‖piExp w‖ = Real.exp (-(2 * Real.pi) * w.im) := by
  rw [piExp, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem gdom_open_ball {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀} (hd : MandelDim.HornData d) :
    IsOpen (Work.L61.gdom d hd) ∧ ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball 0 ρ ⊆ Work.L61.gdom d hd := by
  set ρ : ℝ := Real.exp (-(2 * Real.pi * hd.η)) with hρ
  have hρpos : 0 < ρ := Real.exp_pos _
  -- the image `π(B^u ∪ B^ℓ)` is open
  have hSopen : IsOpen (piExp '' (hd.Bu ∪ hd.Bl)) :=
    piExp_isOpenMap (hd.Bu ∪ hd.Bl) (hd.Bu_open.union hd.Bl_open)
  -- and `{0} ∪ π(B^u ∪ B^ℓ)` contains the ball of radius `ρ` around `0`
  have hball : Metric.ball (0 : ℂ) ρ ⊆ insert (0 : ℂ) (piExp '' (hd.Bu ∪ hd.Bl)) := by
    intro z hz
    have hznorm : ‖z‖ < ρ := by simpa [Metric.mem_ball] using hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact mem_insert_iff.mpr (Or.inl rfl)
    · set w : ℂ := Complex.log z / (2 * Real.pi * I) with hw
      have hpiw : piExp w = z := by rw [hw]; exact piExp_log_div z hz0
      have him : hd.η < w.im := by
        have hexp : Real.exp (-(2 * Real.pi) * w.im) < Real.exp (-(2 * Real.pi * hd.η)) := by
          rw [← norm_piExp w, hpiw]
          simpa [hρ] using hznorm
        have hlt' : -(2 * Real.pi) * w.im < -(2 * Real.pi * hd.η) := Real.exp_lt_exp.mp hexp
        nlinarith [Real.pi_pos]
      exact mem_insert_iff.mpr (Or.inr ⟨w, Or.inl (hd.upper him), hpiw⟩)
  -- `{0} ∪ π(B^u ∪ B^ℓ)` is exactly `π(B^u ∪ B^ℓ) ∪ ball 0 ρ`, a union of open sets
  have hEq : insert (0 : ℂ) (piExp '' (hd.Bu ∪ hd.Bl))
      = (piExp '' (hd.Bu ∪ hd.Bl)) ∪ Metric.ball (0 : ℂ) ρ := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with rfl | hx
      · exact Or.inr (by simp [Metric.mem_ball, hρpos])
      · exact Or.inl hx
    · rintro x (hx | hx)
      · exact mem_insert_of_mem 0 hx
      · exact hball hx
  constructor
  · unfold Work.L61.gdom
    rw [hEq]
    exact hSopen.union Metric.isOpen_ball
  · exact ⟨ρ, hρpos, hball⟩

end

end Work.L61.Push
