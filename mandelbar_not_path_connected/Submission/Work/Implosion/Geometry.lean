/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# Fundamental domains of the implosion: the cut `ℓ` and its image `f(ℓ)`

Hubbard–Schleicher, Prop. 4.1–4.2.  The local normal form
`f(ζ) = ζ + (ζ²−a²)h(ζ)` with `‖h−1‖ < ε` has two simple fixed points `±a`; the
straight segment

  `ℓ = [−a, a]`

separates the *incoming* from the *outgoing* petal, and the image `f(ℓ)` is an arc
joining `a` to `−a`.  The region between `ℓ` and `f(ℓ)` is the **fundamental domain
of the implosion**: every finite orbit of `f` in the union of the two petals meets
it essentially once (there is a unique integer "transit phase"), and the two
boundary arcs are glued by `f`.  This is the "egg-beater" of HS §4.

For `a = iλ` the cut is the imaginary axis and the two petals are the two open
half-planes `Re ζ > 0` and `Re ζ < 0`; the exact formula

  `Re f(t·a) = λ²(1−t²)·Re h(t·a)`

shows that `f(ℓ)` meets `ℓ` only in the two fixed points `±a`, and leaves into the
open petal.
-/
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

open Complex

/-! ## The two petals -/

/-- The open half-plane on the `s`-side of the line `iℝ·a` through the two fixed
points: the two components of its complement are the incoming and outgoing petals.
`s = 1` is the petal into which `f(ℓ)` moves for `a = iλ`. -/
def petal (a : ℂ) (s : ℝ) : Set ℂ := {ζ : ℂ | 0 < s * (ζ / a).im}

/-- The `(+)` petal (contains `f(ℓ)` for `a = iλ`). -/
def petalPos (a : ℂ) : Set ℂ := petal a 1

/-- The `(−)` petal. -/
def petalNeg (a : ℂ) : Set ℂ := petal a (-1)

theorem mem_petalPos_iff (a ζ : ℂ) : ζ ∈ petalPos a ↔ 0 < (ζ / a).im := by
  simp [petalPos, petal]

theorem mem_petalNeg_iff (a ζ : ℂ) : ζ ∈ petalNeg a ↔ (ζ / a).im < 0 := by
  simp [petalNeg, petal]

/-- The cut lies on the boundary of both petals. -/
theorem cutPt_not_mem_petal (a : ℂ) (ha : a ≠ 0) (t : ℝ) :
    cutPt a t ∉ petalPos a ∧ cutPt a t ∉ petalNeg a := by
  have h : ((cutPt a t) / a).im = 0 := by
    rw [cutPt, mul_div_cancel_right₀ _ ha]
    simp
  constructor
  · rw [mem_petalPos_iff, h]; exact lt_irrefl 0
  · rw [mem_petalNeg_iff, h]; exact lt_irrefl 0

/-! ## The fundamental domain between `ℓ` and `f(ℓ)` -/

/-- The **fundamental domain of the implosion**: the union of the straight chords
joining `t·a ∈ ℓ` to `f(t·a) ∈ f(ℓ)`, for `−1 < t < 1`.  This is the region
between the cut and its image (HS Prop. 4.1–4.2, Figure 4). -/
noncomputable def fundamentalDomain (a : ℂ) (h : ℂ → ℂ) : Set ℂ :=
  {ζ : ℂ | ∃ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 ∧ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
    ζ = ((1 - s : ℝ) : ℂ) * cutPt a t + (s : ℂ) * normalForm a h (cutPt a t)}

theorem mem_fundamentalDomain_iff (a : ℂ) (h : ℂ → ℂ) (ζ : ℂ) :
    ζ ∈ fundamentalDomain a h ↔
      ∃ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 ∧ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
        ζ = ((1 - s : ℝ) : ℂ) * cutPt a t + (s : ℂ) * normalForm a h (cutPt a t) :=
  Iff.rfl

/-- The cut part of the fundamental domain: the chord at parameter `s = 0`. -/
theorem cutPt_mem_fundamentalDomain (a : ℂ) (h : ℂ → ℂ) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : cutPt a t ∈ fundamentalDomain a h :=
  ⟨t, ht, 0, Set.left_mem_Icc.mpr zero_le_one, by simp⟩

/-- The **critical point** `0` of the normal form lies on the cut `ℓ`; hence `f` is
conformal on the *interior* of the fundamental domain, which is why the identification
`A^{out}/f` of HS Prop. 4.2 is by a conformal map. -/
theorem zero_mem_cut (a : ℂ) : (0 : ℂ) ∈ cut a := ⟨0, by norm_num, by simp [cutPt]⟩

theorem zero_mem_fundamentalDomain (a : ℂ) (h : ℂ → ℂ) :
    (0 : ℂ) ∈ fundamentalDomain a h := by
  simpa using cutPt_mem_fundamentalDomain a h 0 ⟨by norm_num, by norm_num⟩

/-- The image-arc part of the fundamental domain: the chord at parameter `s = 1`. -/
theorem normalForm_mem_fundamentalDomain (a : ℂ) (h : ℂ → ℂ) (t : ℝ)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    normalForm a h (cutPt a t) ∈ fundamentalDomain a h :=
  ⟨t, ht, 1, Set.right_mem_Icc.mpr zero_le_one, by simp⟩

/-- The fundamental domain is contained in the closed half-plane bounded by the
line through `±a` on the side of the image arc — for `a = iλ` it lies in the
closed right half-plane. -/
theorem fundamentalDomain_convexComb (a : ℂ) (h : ℂ → ℂ) {ζ : ℂ}
    (hζ : ζ ∈ fundamentalDomain a h) :
    ∃ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 ∧ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
      ζ = ((1 - s : ℝ) : ℂ) * cutPt a t + (s : ℂ) * normalForm a h (cutPt a t) := hζ

end Work.Implosion
