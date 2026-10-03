import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# `Work.FatouCH.FC.abelPair`

Given an admissible pair of vertices `c₁ c₂` and a near-translation `F` on `MandelDim.Qreg c₁ c₂`
(`‖F z - (z+1)‖ ≤ 1/32`), there is a point `z` of `Qreg` whose image is again in `Qreg`.

The region is

`Qreg b₁ b₂ = {z | ∀ a ∈ b₁, -|(z-a).im| < (z-a).re} ∩ {z | ∀ b ∈ b₂, (z-b).re < |(z-b).im|}`,

i.e. the complement of the leftward cones at the vertices of `b₁` and of the rightward cones at the
vertices of `b₂`.  Both cones open up as `|Im z| → ∞` while their "width" at a point grows linearly
in `|Im z|`, so for `z = iY` with `Y` large the points `z` and `z + 1` both lie *deep* inside `Qreg`
(margin `≥ 1/2` for the two quantities

`lp z a = (z-a).re + |(z-a).im|`,   `rp z b = |(z-b).im| - (z-b).re`).

Since a point of `Qreg` and `F z` differ by `‖F z - z‖ ≤ ‖F z - (z+1)‖ + 1 ≤ 33/32`, the Lipschitz
estimate `|lp u a - lp v a| ≤ 2‖u-v‖` (and the same for `rp`) shows that `F z` still has positive
margin, i.e. lies in `Qreg`.
-/

namespace Work.FatouCH.FC

open Complex

/-- The "leftward cone" margin at `z` for the vertex `a`: positive exactly when
`-|(z-a).im| < (z-a).re`. -/
def lp (z a : ℂ) : ℝ := (z - a).re + |(z - a).im|

/-- The "rightward cone" margin at `z` for the vertex `b`: positive exactly when
`(z-b).re < |(z-b).im|`. -/
def rp (z b : ℂ) : ℝ := |(z - b).im| - (z - b).re

/-- Membership in `some x` of an `Option` determines the value. -/
lemma eq_of_mem_some {α : Type*} {x y : α} (h : y ∈ (some x : Option α)) : y = x :=
  (Option.some.inj (Option.mem_def.mp h)).symm

/-- `lp` is `2`-Lipschitz in `z`. -/
lemma lp_lipschitz (u v a : ℂ) : |lp u a - lp v a| ≤ 2 * ‖u - v‖ := by
  have hA : |(u - a).re - (v - a).re| ≤ ‖u - v‖ := by
    rw [show (u - a).re - (v - a).re = (u - v).re by simp [Complex.sub_re]]
    exact Complex.abs_re_le_norm _
  have hB : abs (|(u - a).im| - |(v - a).im|) ≤ ‖u - v‖ := by
    calc abs (|(u - a).im| - |(v - a).im|) ≤ |(u - a).im - (v - a).im| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |(u - v).im| := by simp [Complex.sub_im]
      _ ≤ ‖u - v‖ := Complex.abs_im_le_norm _
  calc |lp u a - lp v a|
        = |((u - a).re - (v - a).re) + (|(u - a).im| - |(v - a).im|)| := by
          congr 1; simp only [lp]; ring
    _ ≤ |(u - a).re - (v - a).re| + abs (|(u - a).im| - |(v - a).im|) := abs_add_le _ _
    _ ≤ ‖u - v‖ + ‖u - v‖ := add_le_add hA hB
    _ = 2 * ‖u - v‖ := by ring

/-- `rp` is `2`-Lipschitz in `z`. -/
lemma rp_lipschitz (u v b : ℂ) : |rp u b - rp v b| ≤ 2 * ‖u - v‖ := by
  have hC : abs (|(u - b).im| - |(v - b).im|) ≤ ‖u - v‖ := by
    calc abs (|(u - b).im| - |(v - b).im|) ≤ |(u - b).im - (v - b).im| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |(u - v).im| := by simp [Complex.sub_im]
      _ ≤ ‖u - v‖ := Complex.abs_im_le_norm _
  have hD : |(v - b).re - (u - b).re| ≤ ‖u - v‖ := by
    rw [show (v - b).re - (u - b).re = (v - u).re by simp [Complex.sub_re]]
    rw [show ‖u - v‖ = ‖v - u‖ by rw [norm_sub_rev]]
    exact Complex.abs_re_le_norm _
  calc |rp u b - rp v b|
        = |(|(u - b).im| - |(v - b).im|) + ((v - b).re - (u - b).re)| := by
          congr 1; simp only [rp]; ring
    _ ≤ abs (|(u - b).im| - |(v - b).im|) + |(v - b).re - (u - b).re| := abs_add_le _ _
    _ ≤ ‖u - v‖ + ‖u - v‖ := add_le_add hC hD
    _ = 2 * ‖u - v‖ := by ring

/-- Value of `lp` at the explicit point `⟨x, Y⟩`. -/
lemma lp_pt (x Y : ℝ) (a : ℂ) : lp (⟨x, Y⟩ : ℂ) a = x - a.re + |Y - a.im| := by
  simp [lp, Complex.sub_re, Complex.sub_im]

/-- Value of `rp` at the explicit point `⟨x, Y⟩`. -/
lemma rp_pt (x Y : ℝ) (b : ℂ) : rp (⟨x, Y⟩ : ℂ) b = |Y - b.im| - (x - b.re) := by
  simp [rp, Complex.sub_re, Complex.sub_im]

/-- At `⟨x, Y⟩` with `0 ≤ x` and `Y` past the vertex the leftward margin is at least `1/2`. -/
lemma lp_pt_ge {x Y : ℝ} {a : ℂ} (hx : 0 ≤ x) (hY : a.im + |a.re| + 5 ≤ Y) :
    (1 / 2 : ℝ) ≤ lp (⟨x, Y⟩ : ℂ) a := by
  rw [lp_pt]
  have h1 : 0 ≤ Y - a.im := by have h := abs_nonneg a.re; linarith
  rw [abs_of_nonneg h1]
  have h2 : a.re ≤ |a.re| := le_abs_self _
  linarith

/-- At `⟨x, Y⟩` with `x ≤ 1` and `Y` past the vertex the rightward margin is at least `1/2`. -/
lemma rp_pt_ge {x Y : ℝ} {b : ℂ} (hx : x ≤ 1) (hY : b.im + |b.re| + 5 ≤ Y) :
    (1 / 2 : ℝ) ≤ rp (⟨x, Y⟩ : ℂ) b := by
  rw [rp_pt]
  have h1 : 0 ≤ Y - b.im := by have h := abs_nonneg b.re; linarith
  rw [abs_of_nonneg h1]
  have h2 : b.re ≤ |b.re| := le_abs_self _
  have h3 : -|b.re| ≤ b.re := neg_abs_le _
  linarith

/-- A point within `1/32` of a point with margins `≥ 1/2` still lies in `Qreg`. -/
lemma mem_Qreg_of_close {b₁ b₂ : Option ℂ} {w u : ℂ}
    (h₁ : ∀ a ∈ b₁, (1 / 2 : ℝ) ≤ lp w a)
    (h₂ : ∀ b ∈ b₂, (1 / 2 : ℝ) ≤ rp w b)
    (hc : ‖u - w‖ ≤ 1 / 32) : u ∈ MandelDim.Qreg b₁ b₂ := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hb' : |lp u a - lp w a| ≤ 2 * ‖u - w‖ := lp_lipschitz u w a
    have hle : 2 * ‖u - w‖ ≤ 2 * (1 / 32 : ℝ) := by linarith
    have hx := (abs_le.mp (le_trans hb' hle)).1
    have h1 := h₁ a ha
    have hpos : 0 < lp u a := by linarith
    simp only [lp] at hpos
    linarith
  · have hb' : |rp u b - rp w b| ≤ 2 * ‖u - w‖ := rp_lipschitz u w b
    have hle : 2 * ‖u - w‖ ≤ 2 * (1 / 32 : ℝ) := by linarith
    have hx := (abs_le.mp (le_trans hb' hle)).1
    have h1 := h₂ b hb
    have hpos : 0 < rp u b := by linarith
    simp only [rp] at hpos
    linarith

/-- The explicit point `⟨x, Y⟩` lies in `Qreg` as soon as `Y` dominates all the vertices
(respectively `0 ≤ x` and `x ≤ 1`). -/
lemma Qreg_mem_pt {b₁ b₂ : Option ℂ} {x Y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hY₁ : ∀ a ∈ b₁, a.im + |a.re| + 5 ≤ Y) (hY₂ : ∀ b ∈ b₂, b.im + |b.re| + 5 ≤ Y) :
    (⟨x, Y⟩ : ℂ) ∈ MandelDim.Qreg b₁ b₂ := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h := lp_pt_ge (x := x) (Y := Y) hx0 (hY₁ a ha)
    have h2 : 0 < lp (⟨x, Y⟩ : ℂ) a := by linarith
    simp only [lp] at h2
    linarith
  · have h := rp_pt_ge (x := x) (Y := Y) hx1 (hY₂ b hb)
    have h2 : 0 < rp (⟨x, Y⟩ : ℂ) b := by linarith
    simp only [rp] at h2
    linarith

/-- Same as `Qreg_mem_pt` for a point `u` only known to be within `1/32` of `⟨x, Y⟩`. -/
lemma Qreg_mem_close_of_pt {b₁ b₂ : Option ℂ} {x Y : ℝ} {u : ℂ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hY₁ : ∀ a ∈ b₁, a.im + |a.re| + 5 ≤ Y) (hY₂ : ∀ b ∈ b₂, b.im + |b.re| + 5 ≤ Y)
    (hc : ‖u - (⟨x, Y⟩ : ℂ)‖ ≤ 1 / 32) : u ∈ MandelDim.Qreg b₁ b₂ :=
  mem_Qreg_of_close (fun a ha => lp_pt_ge hx0 (hY₁ a ha)) (fun b hb => rp_pt_ge hx1 (hY₂ b hb)) hc

/-- `⟨1, Y⟩ = ⟨0, Y⟩ + 1`. -/
lemma pt_one (Y : ℝ) : (⟨1, Y⟩ : ℂ) = (⟨0, Y⟩ : ℂ) + 1 := by
  apply Complex.ext <;> simp

theorem abelPair {c₁ c₂ : Option ℂ} {F : ℂ → ℂ} (hAdm : MandelDim.QAdm c₁ c₂)
    (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg c₁ c₂)) :
    ∃ z ∈ MandelDim.Qreg c₁ c₂, F z ∈ MandelDim.Qreg c₁ c₂ := by
  rcases c₁ with _ | a <;> rcases c₂ with _ | b
  · -- `c₁ = none`, `c₂ = none`
    have hY₁ : ∀ a' ∈ (none : Option ℂ), a'.im + |a'.re| + 5 ≤ (0 : ℝ) := by simp
    have hY₂ : ∀ b' ∈ (none : Option ℂ), b'.im + |b'.re| + 5 ≤ (0 : ℝ) := by simp
    have hz : (⟨0, (0 : ℝ)⟩ : ℂ) ∈ MandelDim.Qreg (none : Option ℂ) none :=
      Qreg_mem_pt (x := 0) (Y := 0) le_rfl (by norm_num) hY₁ hY₂
    refine ⟨⟨0, 0⟩, hz, ?_⟩
    have hc : ‖F (⟨0, (0 : ℝ)⟩ : ℂ) - (⟨1, (0 : ℝ)⟩ : ℂ)‖ ≤ 1 / 32 := by
      have h := (hNT.2 (⟨0, (0 : ℝ)⟩ : ℂ) hz).1
      rw [pt_one 0]; exact h
    exact Qreg_mem_close_of_pt (x := 1) (Y := 0) zero_le_one le_rfl hY₁ hY₂ hc
  · -- `c₁ = none`, `c₂ = some b`
    set Y : ℝ := b.im + |b.re| + 5 with hYdef
    have hY₁ : ∀ a' ∈ (none : Option ℂ), a'.im + |a'.re| + 5 ≤ Y := by simp
    have hY₂ : ∀ b' ∈ (some b : Option ℂ), b'.im + |b'.re| + 5 ≤ Y := by
      intro b' hb'
      rw [eq_of_mem_some hb', hYdef]
    have hz : (⟨0, Y⟩ : ℂ) ∈ MandelDim.Qreg (none : Option ℂ) (some b) :=
      Qreg_mem_pt (x := 0) (Y := Y) le_rfl (by norm_num) hY₁ hY₂
    refine ⟨⟨0, Y⟩, hz, ?_⟩
    have hc : ‖F (⟨0, Y⟩ : ℂ) - (⟨1, Y⟩ : ℂ)‖ ≤ 1 / 32 := by
      have h := (hNT.2 (⟨0, Y⟩ : ℂ) hz).1
      rw [pt_one Y]; exact h
    exact Qreg_mem_close_of_pt (x := 1) (Y := Y) zero_le_one le_rfl hY₁ hY₂ hc
  · -- `c₁ = some a`, `c₂ = none`
    set Y : ℝ := a.im + |a.re| + 5 with hYdef
    have hY₁ : ∀ a' ∈ (some a : Option ℂ), a'.im + |a'.re| + 5 ≤ Y := by
      intro a' ha'
      rw [eq_of_mem_some ha', hYdef]
    have hY₂ : ∀ b' ∈ (none : Option ℂ), b'.im + |b'.re| + 5 ≤ Y := by simp
    have hz : (⟨0, Y⟩ : ℂ) ∈ MandelDim.Qreg (some a) (none : Option ℂ) :=
      Qreg_mem_pt (x := 0) (Y := Y) le_rfl (by norm_num) hY₁ hY₂
    refine ⟨⟨0, Y⟩, hz, ?_⟩
    have hc : ‖F (⟨0, Y⟩ : ℂ) - (⟨1, Y⟩ : ℂ)‖ ≤ 1 / 32 := by
      have h := (hNT.2 (⟨0, Y⟩ : ℂ) hz).1
      rw [pt_one Y]; exact h
    exact Qreg_mem_close_of_pt (x := 1) (Y := Y) zero_le_one le_rfl hY₁ hY₂ hc
  · -- `c₁ = some a`, `c₂ = some b`
    set Y : ℝ := max (a.im + |a.re| + 5) (b.im + |b.re| + 5) with hYdef
    have hY₁ : ∀ a' ∈ (some a : Option ℂ), a'.im + |a'.re| + 5 ≤ Y := by
      intro a' ha'
      rw [eq_of_mem_some ha', hYdef]
      exact le_max_left _ _
    have hY₂ : ∀ b' ∈ (some b : Option ℂ), b'.im + |b'.re| + 5 ≤ Y := by
      intro b' hb'
      rw [eq_of_mem_some hb', hYdef]
      exact le_max_right _ _
    have hz : (⟨0, Y⟩ : ℂ) ∈ MandelDim.Qreg (some a) (some b) :=
      Qreg_mem_pt (x := 0) (Y := Y) le_rfl (by norm_num) hY₁ hY₂
    refine ⟨⟨0, Y⟩, hz, ?_⟩
    have hc : ‖F (⟨0, Y⟩ : ℂ) - (⟨1, Y⟩ : ℂ)‖ ≤ 1 / 32 := by
      have h := (hNT.2 (⟨0, Y⟩ : ℂ) hz).1
      rw [pt_one Y]; exact h
    exact Qreg_mem_close_of_pt (x := 1) (Y := Y) zero_le_one le_rfl hY₁ hY₂ hc

end Work.FatouCH.FC
