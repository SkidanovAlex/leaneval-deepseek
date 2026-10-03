import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# FATOU (uniformization route): setup

Definitions for the construction of the perturbed Fatou coordinate of a near-translation `F`
on Shishikura's region `Qreg b₁ b₂` (interface `MandelDim`).

* `eps F z = F z - (z+1)` is the error term; `|eps F z| , |deriv (eps F) z| ≤ 1/32` on `Q`.
* `xOf b₁ b₂` is the reference abscissa `x₀`, chosen so that the vertical strip
  `x₀ ± 3/16` is contained in `Q` and satisfies the hypotheses of `FatouFundamental`.
* `smoothstep` is a `C¹` cut-off `0 → 1` on `[1/8,7/8]`, equal to `1` on `[7/8,9/8]` and
  `1 → 0` on `[9/8,15/8]`, with `|smoothstep'| ≤ 2`.
* `devH x₀ F ζ = x₀ + ζ + χ(Re ζ)·eps F (x₀+ζ-1)` is the interpolation between the identity
  and `F`: it is a *globally* expanding homeomorphism of `ℂ` with `devH (ζ+1) = F (devH ζ)` on
  the central strip `|Re ζ| < 1/8`.  It is the basic chart of the Riemann surface `XF`.

Everything here is `sorry`-free; the analytic properties of `smoothstep` and `devH` are proved
in the sibling files.
-/

namespace Work.Fatou

open MandelDim

noncomputable section

/-- The error term of a near-translation: `eps F z = F z - (z + 1)`. -/
def eps (F : ℂ → ℂ) (z : ℂ) : ℂ := F z - (z + 1)

@[simp]
theorem eps_apply (F : ℂ → ℂ) (z : ℂ) : eps F z = F z - (z + 1) := rfl

/-- The reference abscissa.  It is chosen so that the hypotheses of `FatouFundamental` hold
(`Re b₁ + 1 < x₀` and `x₀ + 3 < Re b₂`) and so that the vertical strip of half-width `1`
around `x₀` is contained in `Qreg b₁ b₂`. -/
def xOf : Option ℂ → Option ℂ → ℝ
  | none, none => 0
  | none, some b => b.re - 4
  | some a, none => a.re + 2
  | some a, some b => (a.re + b.re) / 2 - 1

@[simp] theorem xOf_some_some (a b : ℂ) : xOf (some a) (some b) = (a.re + b.re) / 2 - 1 := rfl
@[simp] theorem xOf_some_none (a : ℂ) : xOf (some a) none = a.re + 2 := rfl
@[simp] theorem xOf_none_some (b : ℂ) : xOf none (some b) = b.re - 4 := rfl
@[simp] theorem xOf_none_none : xOf none none = 0 := rfl

/-- `xOf` lies to the right of `b₁` (given admissibility). -/
theorem xOf_gt_left {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) : ∀ a ∈ b₁, a.re + 1 < xOf b₁ b₂ := by
  intro a ha
  match b₁, b₂ with
  | none, _ => exact (by simp at ha)
  | some a', some b =>
      have ha' : a = a' := by simpa [eq_comm] using ha
      have hh : a'.re + 4 < b.re := by simpa [QAdm] using h
      subst ha'; simp only [xOf_some_some]; linarith
  | some a', none =>
      have ha' : a = a' := by simpa [eq_comm] using ha
      subst ha'; simp only [xOf_some_none]; linarith

/-- The strip of half-width `7/8` around `xOf` stays to the right of `b₁`. -/
theorem xOf_sub_left {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) : ∀ a ∈ b₁, a.re + 7 / 8 < xOf b₁ b₂ := by
  intro a ha
  match b₁, b₂ with
  | none, _ => exact (by simp at ha)
  | some a', some b =>
      have ha' : a = a' := by simpa [eq_comm] using ha
      have hh : a'.re + 4 < b.re := by simpa [QAdm] using h
      subst ha'; simp only [xOf_some_some]; linarith
  | some a', none =>
      have ha' : a = a' := by simpa [eq_comm] using ha
      subst ha'; simp only [xOf_some_none]; linarith

/-- `xOf + 3` lies to the left of `b₂` (given admissibility). -/
theorem xOf_lt_right {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) : ∀ b ∈ b₂, xOf b₁ b₂ + 3 < b.re := by
  intro b hb
  match b₁, b₂ with
  | _, none => exact (by simp at hb)
  | none, some b' =>
      have hb' : b = b' := by simpa [eq_comm] using hb
      subst hb'; simp only [xOf_none_some]; linarith
  | some a, some b' =>
      have hb' : b = b' := by simpa [eq_comm] using hb
      have hh : a.re + 4 < b'.re := by simpa [QAdm] using h
      subst hb'; simp only [xOf_some_some]; linarith

/-- The strip of half-width `7/8` around `xOf` stays to the left of `b₂` (given admissibility). -/
theorem xOf_add_right {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) : ∀ b ∈ b₂, xOf b₁ b₂ + 7 / 8 < b.re := by
  intro b hb
  match b₁, b₂ with
  | _, none => exact (by simp at hb)
  | none, some b' =>
      have hb' : b = b' := by simpa [eq_comm] using hb
      subst hb'; simp only [xOf_none_some]; linarith
  | some a, some b' =>
      have hb' : b = b' := by simpa [eq_comm] using hb
      have hh : a.re + 4 < b'.re := by simpa [QAdm] using h
      subst hb'; simp only [xOf_some_some]; linarith

/-- `xOf - 3/16` lies to the right of `b₁`. -/
theorem xOf_sub_16 {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) : ∀ a ∈ b₁, a.re + 3 / 16 < xOf b₁ b₂ := by
  intro a ha
  have := xOf_gt_left h a ha
  linarith

theorem xOf_add_16 {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) : ∀ b ∈ b₂, xOf b₁ b₂ + 3 / 16 < b.re := by
  intro b hb
  have := xOf_lt_right h b hb
  linarith

/-- The vertical strip `{Re b₁ < Re z < Re b₂}` is contained in `Qreg b₁ b₂`. -/
theorem vertStrip_subset_Qreg (b₁ b₂ : Option ℂ) :
    {z : ℂ | (∀ a ∈ b₁, a.re < z.re) ∧ (∀ b ∈ b₂, z.re < b.re)} ⊆ Qreg b₁ b₂ := by
  intro z hz
  rcases hz with ⟨h₁, h₂⟩
  constructor
  · intro a ha
    have := h₁ a ha
    have hle : -|(z - a).im| ≤ 0 := neg_nonpos.2 (abs_nonneg _)
    have : 0 < (z - a).re := by simp [Complex.sub_re]; linarith
    linarith
  · intro b hb
    have := h₂ b hb
    have hle : 0 ≤ |(z - b).im| := abs_nonneg _
    have : (z - b).re < 0 := by simp [Complex.sub_re]; linarith
    linarith

/-- The vertical strip `x₀ ± 3/16` around `xOf` is contained in `Qreg b₁ b₂`. -/
theorem strip_xOf_subset_Qreg {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) :
    {z : ℂ | xOf b₁ b₂ - 3 / 16 ≤ z.re ∧ z.re ≤ xOf b₁ b₂ + 3 / 16} ⊆ Qreg b₁ b₂ := by
  apply subset_trans _ (vertStrip_subset_Qreg b₁ b₂)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have := xOf_sub_16 h a ha; linarith
  · have := xOf_add_16 h b hb; linarith

/-- The vertical strip `x₀ ± 1/8` around `xOf` is contained in `Qreg b₁ b₂`. -/
theorem strip_eighth_subset_Qreg {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) :
    {z : ℂ | xOf b₁ b₂ - 1 / 8 ≤ z.re ∧ z.re ≤ xOf b₁ b₂ + 1 / 8} ⊆ Qreg b₁ b₂ := by
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  exact strip_xOf_subset_Qreg h ⟨by linarith, by linarith⟩

/-- The vertical strip `x₀ ± 7/8` around `xOf` is contained in `Qreg b₁ b₂`. -/
theorem strip_seven_subset_Qreg {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) :
    {z : ℂ | xOf b₁ b₂ - 7 / 8 ≤ z.re ∧ z.re ≤ xOf b₁ b₂ + 7 / 8} ⊆ Qreg b₁ b₂ := by
  apply subset_trans _ (vertStrip_subset_Qreg b₁ b₂)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have := xOf_sub_left h a ha; linarith
  · have := xOf_add_right h b hb; linarith

/-- `x₀ + ζ - 1 ∈ Qreg` whenever `1/8 ≤ Re ζ ≤ 15/8`. -/
theorem xOf_add_mem_Qreg {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) {ζ : ℂ}
    (h₁ : (1 / 8 : ℝ) ≤ ζ.re) (h₂ : ζ.re ≤ 15 / 8) :
    (xOf b₁ b₂ : ℂ) + ζ - 1 ∈ Qreg b₁ b₂ := by
  apply strip_seven_subset_Qreg h
  simp only [Set.mem_ofPred_eq]
  have : ((xOf b₁ b₂ : ℂ) + ζ - 1).re = xOf b₁ b₂ + ζ.re - 1 := by simp
  rw [this]; constructor <;> linarith

/-- `x₀ + ζ ∈ Qreg` whenever `-1/8 ≤ Re ζ ≤ 1/8`. -/
theorem xOf_add_shift_mem_Qreg {b₁ b₂ : Option ℂ} (h : QAdm b₁ b₂) {ζ : ℂ}
    (h₁ : -(1 / 8 : ℝ) ≤ ζ.re) (h₂ : ζ.re ≤ 1 / 8) :
    (xOf b₁ b₂ : ℂ) + ζ ∈ Qreg b₁ b₂ := by
  apply strip_eighth_subset_Qreg h
  simp only [Set.mem_ofPred_eq]
  have : ((xOf b₁ b₂ : ℂ) + ζ).re = xOf b₁ b₂ + ζ.re := by simp
  rw [this]; constructor <;> linarith

/-- The smoothstep `χ : 0 → 1` on `[1/8,7/8]`, `= 1` on `[7/8,9/8]`, `1 → 0` on `[9/8,15/8]`,
`= 0` outside `[1/8,15/8]`.  It is `C¹` with `|χ'| ≤ 2` and values in `[0,1]`. -/
def smoothstep (t : ℝ) : ℝ :=
  if t ≤ 1 / 8 then 0
  else if t < 7 / 8 then
    let u := (t - 1 / 8) / (3 / 4)
    3 * u ^ 2 - 2 * u ^ 3
  else if t ≤ 9 / 8 then 1
  else if t < 15 / 8 then
    let u := (15 / 8 - t) / (3 / 4)
    3 * u ^ 2 - 2 * u ^ 3
  else 0

/-- The interpolated map `devH`.  It equals `x₀ + ζ` for `Re ζ ≤ 1/8`, equals
`F (x₀ + ζ - 1)` for `7/8 ≤ Re ζ ≤ 9/8`, and equals `x₀ + ζ` again for `Re ζ ≥ 15/8`;
on the whole plane it is `C¹` with `‖D devH - I‖ ≤ 3/32`, hence a globally expanding
homeomorphism. -/
def devH (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  (x₀ : ℂ) + ζ + (smoothstep ζ.re : ℂ) * eps F ((x₀ : ℂ) + ζ - 1)

@[simp]
theorem devH_apply (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) :
    devH x₀ F ζ = (x₀ : ℂ) + ζ + (smoothstep ζ.re : ℂ) * eps F ((x₀ : ℂ) + ζ - 1) := rfl

/-- The basic chart domain: the `ζ`-strip on which `devH` interpolates. -/
def Sigma : Set ℂ := {ζ : ℂ | -(1 / 8) < ζ.re ∧ ζ.re < 9 / 8}

theorem mem_Sigma {ζ : ℂ} : ζ ∈ Sigma ↔ -(1 / 8) < ζ.re ∧ ζ.re < 9 / 8 := Iff.rfl

/-- The strip shifted by `n`. -/
def SigmaAt (n : ℤ) : Set ℂ := {ζ : ℂ | (n : ℂ).re - 1 / 8 < ζ.re ∧ ζ.re < (n : ℂ).re + 9 / 8}

theorem isOpen_Sigma : IsOpen (Sigma : Set ℂ) := by
  have h1 : IsOpen {ζ : ℂ | -(1 / 8 : ℝ) < ζ.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {ζ : ℂ | ζ.re < (9 / 8 : ℝ)} :=
    isOpen_lt Complex.continuous_re continuous_const
  exact h1.inter h2

/-- A point of `Qreg` satisfies the "left" cone condition. -/
theorem Qreg.left {b₁ b₂ : Option ℂ} {z : ℂ} (hz : z ∈ Qreg b₁ b₂) :
    ∀ a ∈ b₁, -|(z - a).im| < (z - a).re := hz.1

/-- A point of `Qreg` satisfies the "right" cone condition. -/
theorem Qreg.right {b₁ b₂ : Option ℂ} {z : ℂ} (hz : z ∈ Qreg b₁ b₂) :
    ∀ b ∈ b₂, (z - b).re < |(z - b).im| := hz.2

end

end Work.Fatou
