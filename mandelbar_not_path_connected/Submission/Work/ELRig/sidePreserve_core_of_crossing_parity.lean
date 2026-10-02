import Mathlib
import Submission.Work.ELRig.side_flip_at_crossing
import Submission.Work.ELRig.side_flip_at_crossing_gamma2
import Submission.Work.ELRig.even_sign_changes
import Submission.Work.ELRig.same_side_of_even_flips
import Submission.Work.ELRig.range_lift_closed
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.Sides
import Submission.Work.ELRig.level_window_shift_bij
import Submission.Work.ELRig.cyl_horizontal_isolated

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-! ## The parameters at which the lifts cross the horizontal line through `u`

Let `u` be a point of the far-left half plane and `c₀ = Im u`, `a = Re u`.  Along the horizontal
line `Im = c₀` the point `u + t` lies on the first lift `range γ₁` exactly at the *crossing times*
`t`:  if `s` is a parameter of the lift with `(γ₁ s).im = c₀` then the points `γ₁ (s + k)`
(`k ∈ ℤ`) of its `ℤ`-orbit (under `w ↦ w + 1`) sit at the levels `(γ₁ s).re + k`, and since
`γ₁` is injective there is at most one of them with level in `[a, a+1)`.  This file builds the two
finite sets

* `sdT L u h₁ h₂` — the set of *crossing times*, i.e. of those `t` with `u + t ∈ range γ₁ ∪
  range γ₂`, and
* `sdF L u h₁ h₂ ⊆ sdT` — the subset of *transversal* crossings (those at which the height
  function `s ↦ (γᵢ s).im` changes sign),

and the main theorem `sidePreserve_core_of_crossing_parity` concludes by the walking lemma
`Work.ELRig.same_side_of_even_flips`, using `Work.ELRig.even_sign_changes` (the transversal
crossings of the level `c₀` in one period are even) and the flip criterion
`Work.ELRig.side_flip_at_crossing` (a transversal crossing of the lift is exactly a change of
side). -/

/-- The parameter shift of `γ₁` which moves the point `γ₁ s` into the window
`[Re u, Re u + 1)` of the horizontal line through `u`. -/
def sdWin₁ (L : RayCylLift d fl) (u : ℂ) (s : ℝ) : ℝ := ceilShift L.γ₁ u.re s

/-- The *crossing time* of the horizontal line through `u` at which the lift point
`γ₁ (sdWin₁ L u s)` sits: `γ₁ (sdWin₁ L u s) = u + sdTime₁ L u s`. -/
def sdTime₁ (L : RayCylLift d fl) (u : ℂ) (s : ℝ) : ℝ := (L.γ₁ (sdWin₁ L u s)).re - u.re

/-- The parameter shift of `γ₂` into the window `[Re u, Re u + 1)`. -/
def sdWin₂ (L : RayCylLift d fl) (u : ℂ) (s : ℝ) : ℝ := ceilShift L.γ₂ u.re s

/-- The crossing time of `γ₂`. -/
def sdTime₂ (L : RayCylLift d fl) (u : ℂ) (s : ℝ) : ℝ := (L.γ₂ (sdWin₂ L u s)).re - u.re

/-- The level set of `Im γ₁ = Im u` inside the fundamental domain, as a finite set. -/
def sdLev₁ (L : RayCylLift d fl) (u : ℂ)
    (h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}) : Finset ℝ :=
  h₁.toFinset

/-- The level set of `Im γ₂ = Im u` inside the fundamental domain, as a finite set. -/
def sdLev₂ (L : RayCylLift d fl) (u : ℂ)
    (h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}) : Finset ℝ :=
  h₂.toFinset

/-- The set of **crossing times** of the horizontal line through `u` with the two lifts. -/
def sdT (L : RayCylLift d fl) (u : ℂ)
    (h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im})
    (h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}) : Finset ℝ :=
  (h₁.toFinset.image (sdTime₁ L u)) ∪ (h₂.toFinset.image (sdTime₂ L u))

/-- The set of **transversal crossing times** of the horizontal line through `u` with the two
lifts: those crossing times whose parameter is a sign change of the height `s ↦ (γᵢ s).im`. -/
def sdF (L : RayCylLift d fl) (u : ℂ)
    (h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im})
    (h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}) : Finset ℝ :=
  ((h₁.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₁ t).im) u.im (sdWin₁ L u s))).image
      (sdTime₁ L u)) ∪
  ((h₂.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₂ t).im) u.im (sdWin₂ L u s))).image
      (sdTime₂ L u))

/-! ## Elementary facts about the window shift -/

theorem sdWin₁_def (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    sdWin₁ L u s = s + (⌈u.re - (L.γ₁ s).re⌉ : ℤ) := rfl

theorem sdWin₁_spec (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    L.γ₁ (sdWin₁ L u s) = L.γ₁ s + ((⌈u.re - (L.γ₁ s).re⌉ : ℤ) : ℂ) := by
  rw [sdWin₁_def]
  exact gamma_shift_int L.per₁ _ s

theorem sdWin₁_im (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    (L.γ₁ (sdWin₁ L u s)).im = (L.γ₁ s).im := ceilShift_im L.per₁ s

theorem sdWin₁_re (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    (L.γ₁ (sdWin₁ L u s)).re = (L.γ₁ s).re + (⌈u.re - (L.γ₁ s).re⌉ : ℝ) :=
  ceilShift_re L.per₁ s

theorem sdTime₁_mem_Icc (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    0 ≤ sdTime₁ L u s ∧ sdTime₁ L u s < 1 := by
  obtain ⟨h1, h2⟩ := ceilShift_mem (a := u.re) L.per₁ s
  simp only [sdTime₁, sdWin₁]
  exact ⟨by linarith, by linarith⟩

theorem sdWin₂_spec (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    L.γ₂ (sdWin₂ L u s) = L.γ₂ s + ((⌈u.re - (L.γ₂ s).re⌉ : ℤ) : ℂ) := by
  rw [sdWin₂, ceilShift]
  exact gamma_shift_int L.per₂ _ s

theorem sdWin₂_im (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    (L.γ₂ (sdWin₂ L u s)).im = (L.γ₂ s).im := ceilShift_im L.per₂ s

theorem sdWin₂_re (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    (L.γ₂ (sdWin₂ L u s)).re = (L.γ₂ s).re + (⌈u.re - (L.γ₂ s).re⌉ : ℝ) :=
  ceilShift_re L.per₂ s

theorem sdTime₂_mem_Icc (L : RayCylLift d fl) (u : ℂ) (s : ℝ) :
    0 ≤ sdTime₂ L u s ∧ sdTime₂ L u s < 1 := by
  obtain ⟨h1, h2⟩ := ceilShift_mem (a := u.re) L.per₂ s
  simp only [sdTime₂, sdWin₂]
  exact ⟨by linarith, by linarith⟩

/-- The crossing point of `γ₁` at the parameter `s` of the level `Im = Im u` sits at the crossing
time `sdTime₁ L u s`. -/
theorem sdTime₁_spec (L : RayCylLift d fl) (u : ℂ) {s : ℝ} (hs : (L.γ₁ s).im = u.im) :
    L.γ₁ (sdWin₁ L u s) = u + (sdTime₁ L u s : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, sdTime₁]
    ring
  · rw [Complex.add_im, Complex.ofReal_im, add_zero, sdWin₁_im, hs]

theorem sdTime₂_spec (L : RayCylLift d fl) (u : ℂ) {s : ℝ} (hs : (L.γ₂ s).im = u.im) :
    L.γ₂ (sdWin₂ L u s) = u + (sdTime₂ L u s : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, sdTime₂]
    ring
  · rw [Complex.add_im, Complex.ofReal_im, add_zero, sdWin₂_im, hs]

/-- Two points of the fundamental domain which differ by an integer coincide. -/
theorem eq_of_sub_eq_intCast {s s' : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (hs' : s' ∈ Set.Ico (0 : ℝ) 1)
    (m : ℤ) (hm : s - s' = (m : ℝ)) : s = s' := by
  have h1 : (-1 : ℤ) < m := by
    have : (-1 : ℝ) < (m : ℝ) := by linarith [hs.1, hs'.2, hm]
    exact_mod_cast this
  have h2 : m < 1 := by
    have : (m : ℝ) < 1 := by linarith [hs.2, hs'.1, hm]
    exact_mod_cast this
  have hm0 : m = 0 := by omega
  have : s - s' = 0 := by rw [hm, hm0]; simp
  linarith

/-- The second lift is injective, by the anti-symmetry `γ₂ s = star (γ₁ s) + 1/2`. -/
theorem cyl_injective₂ (L : RayCylLift d fl) : ∀ s s' : ℝ, L.γ₂ s = L.γ₂ s' → s = s' := by
  intro s s' h
  have h1 : star (L.γ₁ s) = star (L.γ₁ s') := by
    rw [L.anti s, L.anti s'] at h
    exact add_right_cancel h
  have h2 : L.γ₁ s = L.γ₁ s' := by
    have := congrArg star h1
    simpa using this
  exact injective₁ L s s' h2

/-- If `u` is off both lifts, the crossing time of a point of the level set is strictly positive:
otherwise the crossing point is `u` itself. -/
theorem sdTime₁_pos (L : RayCylLift d fl) (u : ℂ)
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) {s : ℝ} (hs : (L.γ₁ s).im = u.im) :
    0 < sdTime₁ L u s := by
  rcases lt_or_eq_of_le (sdTime₁_mem_Icc L u s).1 with h | h
  · exact h
  · exfalso
    have hspec : L.γ₁ (sdWin₁ L u s) = u := by
      rw [sdTime₁_spec L u hs, ← h, Complex.ofReal_zero, add_zero]
    exact huΛ (Or.inl ⟨sdWin₁ L u s, hspec⟩)

theorem sdTime₂_pos (L : RayCylLift d fl) (u : ℂ)
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) {s : ℝ} (hs : (L.γ₂ s).im = u.im) :
    0 < sdTime₂ L u s := by
  rcases lt_or_eq_of_le (sdTime₂_mem_Icc L u s).1 with h | h
  · exact h
  · exfalso
    have hspec : L.γ₂ (sdWin₂ L u s) = u := by
      rw [sdTime₂_spec L u hs, ← h, Complex.ofReal_zero, add_zero]
    exact huΛ (Or.inr ⟨sdWin₂ L u s, hspec⟩)

/-- A point of the `γ₁`-level set is determined by its crossing time. -/
theorem sdTime₁_injOn (L : RayCylLift d fl) (u : ℂ) :
    Set.InjOn (sdTime₁ L u) {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im} := by
  intro s hs s' hs' hτ
  have h1 : L.γ₁ (sdWin₁ L u s) = L.γ₁ (sdWin₁ L u s') := by
    rw [sdTime₁_spec L u hs.2, sdTime₁_spec L u hs'.2, hτ]
  have h2 := injective₁ L (sdWin₁ L u s) (sdWin₁ L u s') h1
  rw [sdWin₁_def, sdWin₁_def] at h2
  obtain ⟨m, hm⟩ : ∃ m : ℤ, s - s' = (m : ℝ) :=
    ⟨⌈u.re - (L.γ₁ s').re⌉ - ⌈u.re - (L.γ₁ s).re⌉, by push_cast; linarith⟩
  exact eq_of_sub_eq_intCast hs.1 hs'.1 m hm

theorem sdTime₂_injOn (L : RayCylLift d fl) (u : ℂ) :
    Set.InjOn (sdTime₂ L u) {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im} := by
  intro s hs s' hs' hτ
  have h1 : L.γ₂ (sdWin₂ L u s) = L.γ₂ (sdWin₂ L u s') := by
    rw [sdTime₂_spec L u hs.2, sdTime₂_spec L u hs'.2, hτ]
  have h2 : sdWin₂ L u s = sdWin₂ L u s' := cyl_injective₂ L _ _ h1
  rw [sdWin₂, ceilShift, sdWin₂, ceilShift] at h2
  obtain ⟨m, hm⟩ : ∃ m : ℤ, s - s' = (m : ℝ) :=
    ⟨⌈u.re - (L.γ₂ s').re⌉ - ⌈u.re - (L.γ₂ s).re⌉, by push_cast; linarith⟩
  exact eq_of_sub_eq_intCast hs.1 hs'.1 m hm

/-! ## The two lifts have disjoint ranges

The `Ψ`-image of a point of `range γ₁` lies on the parameter ray `R(α₁)`, and the `Ψ`-image of a
point of `range γ₂` on `R(α₂)`; since `α₁ ≠ α₂` and the external angle of a ray point is the angle
of the ray, the two ranges cannot meet. -/

theorem cyl_range_disjoint (L : RayCylLift d fl) : ∀ s s' : ℝ, L.γ₁ s ≠ L.γ₂ s' := by
  intro s s' h
  have hα₁₀ : 0 ≤ Work.EL.alpha1 := by rw [Work.EL.alpha1]; norm_num
  have hα₁₁ : Work.EL.alpha1 < 1 := by rw [Work.EL.alpha1]; norm_num
  have hα₂₀ : 0 ≤ Work.EL.alpha2 := by rw [Work.EL.alpha2]; norm_num
  have hα₂₁ : Work.EL.alpha2 < 1 := by rw [Work.EL.alpha2]; norm_num
  have heq : fl.Ψ (L.γ₂ s') = fl.Ψ (L.γ₁ s) := by rw [h]
  have e1 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s)) = Work.EL.alpha1 :=
    Work.Top.extAngle_of_mem_paramRay d.hN hα₁₀ hα₁₁ (L.img₁ s)
  have e2 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ (L.γ₁ s)) = Work.EL.alpha2 := by
    rw [← heq]
    exact Work.Top.extAngle_of_mem_paramRay d.hN hα₂₀ hα₂₁ (L.img₂ s')
  have := e1.symm.trans e2
  norm_num [Work.EL.alpha1, Work.EL.alpha2] at this

/-! ## `⌈x - τ⌉ = x` for an integer `x` and `0 ≤ τ < 1` -/

theorem ceil_intCast_sub {k : ℤ} {τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1) :
    ⌈(k : ℝ) - τ⌉ = k := by
  rw [Int.ceil_eq_iff]
  constructor <;> linarith

/-! ## The crossing times of one lift -/

theorem sdLev₁_mem (L : RayCylLift d fl) (u : ℂ) {h₁ : Set.Finite _} {s : ℝ} :
    s ∈ sdLev₁ L u h₁ ↔ s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im :=
  Set.Finite.mem_toFinset h₁

theorem sdLev₂_mem (L : RayCylLift d fl) (u : ℂ) {h₂ : Set.Finite _} {s : ℝ} :
    s ∈ sdLev₂ L u h₂ ↔ s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im :=
  Set.Finite.mem_toFinset h₂

/-- **The crossing-time correspondence, first lift.**  For a parameter `s` of the level
`Im γ₁ = Im u`, the point `γ₁ (sdWin₁ L u s)` of the lift sits on the horizontal line through `u`
at the crossing time `sdTime₁ L u s ∈ [0,1)`. -/
theorem sdWin₁_of_mem (L : RayCylLift d fl) (u : ℂ) {σ τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hσ : L.γ₁ σ = u + (τ : ℂ)) :
    sdWin₁ L u (σ - ⌊σ⌋) = σ ∧ L.γ₁ (σ - ⌊σ⌋) = u + (τ : ℂ) - ((⌊σ⌋ : ℤ) : ℂ) := by
  set s : ℝ := σ - ⌊σ⌋ with hsdef
  have hfloor : s + ((⌊σ⌋ : ℤ) : ℝ) = σ := by
    rw [hsdef]; push_cast; ring
  have hshift : L.γ₁ σ = L.γ₁ s + ((⌊σ⌋ : ℤ) : ℂ) := by
    have := gamma_shift_int (γ := L.γ₁) L.per₁ ⌊σ⌋ s
    rwa [hfloor] at this
  have hval : L.γ₁ s = u + (τ : ℂ) - ((⌊σ⌋ : ℤ) : ℂ) := by
    rw [hshift] at hσ
    exact eq_sub_of_add_eq hσ
  have hre : (L.γ₁ s).re = u.re + τ - (⌊σ⌋ : ℝ) := by
    rw [hval]; simp
  have hceil : ⌈u.re - (L.γ₁ s).re⌉ = ⌊σ⌋ := by
    rw [hre]
    have : u.re - (u.re + τ - (⌊σ⌋ : ℝ)) = (⌊σ⌋ : ℝ) - τ := by ring
    rw [this]
    exact ceil_intCast_sub hτ₀ hτ₁
  constructor
  · rw [sdWin₁_def, hceil]
    exact hfloor
  · exact hval

theorem sdTime_of_mem₁ (L : RayCylLift d fl) (u : ℂ) {σ τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hσ : L.γ₁ σ = u + (τ : ℂ)) :
    sdTime₁ L u (σ - ⌊σ⌋) = τ := by
  obtain ⟨hwin, -⟩ := sdWin₁_of_mem L u hτ₀ hτ₁ hσ
  have hσ' : L.γ₁ (sdWin₁ L u (σ - ⌊σ⌋)) = u + (τ : ℂ) := by rw [hwin]; exact hσ
  simp only [sdTime₁, hσ', Complex.add_re, Complex.ofReal_re]
  ring

theorem sdWin₂_of_mem (L : RayCylLift d fl) (u : ℂ) {σ τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hσ : L.γ₂ σ = u + (τ : ℂ)) :
    sdWin₂ L u (σ - ⌊σ⌋) = σ ∧ L.γ₂ (σ - ⌊σ⌋) = u + (τ : ℂ) - ((⌊σ⌋ : ℤ) : ℂ) := by
  set s : ℝ := σ - ⌊σ⌋ with hsdef
  have hfloor : s + ((⌊σ⌋ : ℤ) : ℝ) = σ := by
    rw [hsdef]; push_cast; ring
  have hshift : L.γ₂ σ = L.γ₂ s + ((⌊σ⌋ : ℤ) : ℂ) := by
    have := gamma_shift_int (γ := L.γ₂) L.per₂ ⌊σ⌋ s
    rwa [hfloor] at this
  have hval : L.γ₂ s = u + (τ : ℂ) - ((⌊σ⌋ : ℤ) : ℂ) := by
    rw [hshift] at hσ
    exact eq_sub_of_add_eq hσ
  have hre : (L.γ₂ s).re = u.re + τ - (⌊σ⌋ : ℝ) := by
    rw [hval]; simp
  have hceil : ⌈u.re - (L.γ₂ s).re⌉ = ⌊σ⌋ := by
    rw [hre]
    have : u.re - (u.re + τ - (⌊σ⌋ : ℝ)) = (⌊σ⌋ : ℝ) - τ := by ring
    rw [this]
    exact ceil_intCast_sub hτ₀ hτ₁
  constructor
  · rw [sdWin₂, ceilShift, hceil]
    exact hfloor
  · exact hval

theorem sdTime_of_mem₂ (L : RayCylLift d fl) (u : ℂ) {σ τ : ℝ} (hτ₀ : 0 ≤ τ) (hτ₁ : τ < 1)
    (hσ : L.γ₂ σ = u + (τ : ℂ)) :
    sdTime₂ L u (σ - ⌊σ⌋) = τ := by
  obtain ⟨hwin, -⟩ := sdWin₂_of_mem L u hτ₀ hτ₁ hσ
  have hσ' : L.γ₂ (sdWin₂ L u (σ - ⌊σ⌋)) = u + (τ : ℂ) := by rw [hwin]; exact hσ
  simp only [sdTime₂, hσ', Complex.add_re, Complex.ofReal_re]
  ring

/-- **The crossing times are exactly the points of `u + [0,1]` lying on the two lifts.** -/
theorem mem_sdT_iff (L : RayCylLift d fl) (u : ℂ)
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    {h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}}
    {h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}}
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (u + (τ : ℂ) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂) ↔ τ ∈ sdT L u h₁ h₂ := by
  constructor
  · rintro (⟨σ, hσ⟩ | ⟨σ, hσ⟩)
    · have hτ₁ : τ < 1 := by
        rcases lt_or_eq_of_le hτ.2 with h | h
        · exact h
        · exfalso
          have h1 : u + 1 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
            refine Or.inl ⟨σ, ?_⟩
            rw [h] at hσ
            simpa using hσ
          have h2 : u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
            have := (g2_range_sub_one L (u + 1)).mp h1
            simpa using this
          exact huΛ h2
      have hsIco : σ - ⌊σ⌋ ∈ Set.Ico (0 : ℝ) 1 := floor_sub_floor_mem σ
      have him : (L.γ₁ (σ - ⌊σ⌋)).im = u.im := by
        rw [(sdWin₁_of_mem L u hτ.1 hτ₁ hσ).2]
        simp
      have hslev : σ - ⌊σ⌋ ∈ h₁.toFinset :=
        (Set.Finite.mem_toFinset h₁).mpr ⟨hsIco, him⟩
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨σ - ⌊σ⌋, hslev, sdTime_of_mem₁ L u hτ.1 hτ₁ hσ⟩))
    · have hτ₁ : τ < 1 := by
        rcases lt_or_eq_of_le hτ.2 with h | h
        · exact h
        · exfalso
          have h1 : u + 1 ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
            refine Or.inr ⟨σ, ?_⟩
            rw [h] at hσ
            simpa using hσ
          have h2 : u ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
            have := (g2_range_sub_one L (u + 1)).mp h1
            simpa using this
          exact huΛ h2
      have hsIco : σ - ⌊σ⌋ ∈ Set.Ico (0 : ℝ) 1 := floor_sub_floor_mem σ
      have him : (L.γ₂ (σ - ⌊σ⌋)).im = u.im := by
        rw [(sdWin₂_of_mem L u hτ.1 hτ₁ hσ).2]
        simp
      have hslev : σ - ⌊σ⌋ ∈ h₂.toFinset :=
        (Set.Finite.mem_toFinset h₂).mpr ⟨hsIco, him⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨σ - ⌊σ⌋, hslev, sdTime_of_mem₂ L u hτ.1 hτ₁ hσ⟩))
  · intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
      obtain ⟨hsIco, hsim⟩ := (Set.Finite.mem_toFinset h₁).mp hs
      rw [← hst, ← sdTime₁_spec L u hsim]
      exact Or.inl ⟨sdWin₁ L u s, rfl⟩
    · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
      obtain ⟨hsIco, hsim⟩ := (Set.Finite.mem_toFinset h₂).mp hs
      rw [← hst, ← sdTime₂_spec L u hsim]
      exact Or.inr ⟨sdWin₂ L u s, rfl⟩

/-- All crossing times lie in `(0,1)`. -/
theorem sdT_pos (L : RayCylLift d fl) (u : ℂ)
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) {h₁ h₂} {t : ℝ}
    (ht : t ∈ sdT L u h₁ h₂) : 0 < t := by
  rcases Finset.mem_union.mp ht with h | h
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
    rw [← hst]
    exact sdTime₁_pos L u huΛ ((Set.Finite.mem_toFinset h₁).mp hs).2
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
    rw [← hst]
    exact sdTime₂_pos L u huΛ ((Set.Finite.mem_toFinset h₂).mp hs).2

theorem sdT_lt_one (L : RayCylLift d fl) (u : ℂ) {h₁ h₂} {t : ℝ}
    (ht : t ∈ sdT L u h₁ h₂) : t < 1 := by
  rcases Finset.mem_union.mp ht with h | h
  · obtain ⟨s, -, hst⟩ := Finset.mem_image.mp h
    rw [← hst]; exact (sdTime₁_mem_Icc L u s).2
  · obtain ⟨s, -, hst⟩ := Finset.mem_image.mp h
    rw [← hst]; exact (sdTime₂_mem_Icc L u s).2

theorem sdF_subset_sdT (L : RayCylLift d fl) (u : ℂ) {h₁ h₂} :
    sdF L u h₁ h₂ ⊆ sdT L u h₁ h₂ := by
  intro t ht
  rcases Finset.mem_union.mp ht with h | h
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
      ⟨s, (Finset.mem_filter.mp hs).1, hst⟩))
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp h
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
      ⟨s, (Finset.mem_filter.mp hs).1, hst⟩))

/-- The two families of crossing times are disjoint, by `cyl_range_disjoint`. -/
theorem sdF_disjoint (L : RayCylLift d fl) (u : ℂ)
    {h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}}
    {h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}} :
    Disjoint ((h₁.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₁ t).im) u.im (sdWin₁ L u s))).image
        (sdTime₁ L u))
      ((h₂.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₂ t).im) u.im (sdWin₂ L u s))).image
        (sdTime₂ L u)) := by
  rw [Finset.disjoint_left]
  intro t ht₁ ht₂
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp ht₁
  obtain ⟨s', hs', hs't⟩ := Finset.mem_image.mp ht₂
  have him₁ : (L.γ₁ s).im = u.im := ((Set.Finite.mem_toFinset h₁).mp (Finset.mem_filter.mp hs).1).2
  have him₂ : (L.γ₂ s').im = u.im := ((Set.Finite.mem_toFinset h₂).mp (Finset.mem_filter.mp hs').1).2
  have h1 : L.γ₁ (sdWin₁ L u s) = u + (sdTime₁ L u s : ℂ) := sdTime₁_spec L u him₁
  have h2 : L.γ₂ (sdWin₂ L u s') = u + (sdTime₂ L u s' : ℂ) := sdTime₂_spec L u him₂
  exact cyl_range_disjoint L _ _ (by rw [h1, h2, hst, hs't])

/-! ## The number of transversal crossings is even -/

/-- The two normal forms of `Cross`: the one which puts a single radius for both one-sided
conditions.  (`Work.ELRig.Cross` has the `∃` inside the conjunction, the form used by the flip
criterion `Work.ELRig.side_flip_at_crossing` has it outside.) -/
theorem cross_iff_single {h : ℝ → ℝ} {c s : ℝ} :
    Cross h c s ↔
      ((∃ ε > 0, (∀ t ∈ Set.Ioo (s - ε) s, c < h t) ∧ (∀ t ∈ Set.Ioo s (s + ε), h t < c)) ∨
       (∃ ε > 0, (∀ t ∈ Set.Ioo (s - ε) s, h t < c) ∧ (∀ t ∈ Set.Ioo s (s + ε), c < h t))) := by
  simp only [Cross, LPos, LNeg, RPos, RNeg]
  constructor
  · rintro (⟨⟨ε₁, hε₁, h₁⟩, ⟨ε₂, hε₂, h₂⟩⟩ | ⟨⟨ε₁, hε₁, h₁⟩, ⟨ε₂, hε₂, h₂⟩⟩)
    · refine Or.inl ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
      · intro t ht
        exact h₁ t ⟨by linarith [ht.1, min_le_left ε₁ ε₂], ht.2⟩
      · intro t ht
        exact h₂ t ⟨ht.1, by linarith [ht.2, min_le_right ε₁ ε₂]⟩
    · refine Or.inr ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩
      · intro t ht
        exact h₁ t ⟨by linarith [ht.1, min_le_left ε₁ ε₂], ht.2⟩
      · intro t ht
        exact h₂ t ⟨ht.1, by linarith [ht.2, min_le_right ε₁ ε₂]⟩
  · rintro (⟨ε, hε, h₁, h₂⟩ | ⟨ε, hε, h₁, h₂⟩)
    · exact Or.inl ⟨⟨ε, hε, h₁⟩, ⟨ε, hε, h₂⟩⟩
    · exact Or.inr ⟨⟨ε, hε, h₁⟩, ⟨ε, hε, h₂⟩⟩

/-- The same normal form with the two alternatives exchanged, matching the sign convention of
`Work.ELRig.side_flip_at_crossing`. -/
theorem cross_iff_single' {h : ℝ → ℝ} {c s : ℝ} :
    Cross h c s ↔
      ((∃ ε > 0, (∀ t ∈ Set.Ioo (s - ε) s, h t < c) ∧ (∀ t ∈ Set.Ioo s (s + ε), c < h t)) ∨
       (∃ ε > 0, (∀ t ∈ Set.Ioo (s - ε) s, c < h t) ∧ (∀ t ∈ Set.Ioo s (s + ε), h t < c))) := by
  rw [cross_iff_single]
  exact or_comm

theorem sdCross₁_even (L : RayCylLift d fl) (u : ℂ)
    (h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}) :
    Even (h₁.toFinset.filter
        (fun s => Cross (fun t : ℝ => (L.γ₁ t).im) u.im (sdWin₁ L u s))).card := by
  have hper : ∀ s : ℝ, (fun t : ℝ => (L.γ₁ t).im) (s + 1) = (fun t : ℝ => (L.γ₁ t).im) s := by
    intro s
    simp only
    rw [L.per₁ s]
    simp
  have hfin : ({s : ℝ | (L.γ₁ s).im = u.im} ∩ Set.Ico (0 : ℝ) 1).Finite :=
    h₁.subset (fun s hs => ⟨hs.2, hs.1⟩)
  have hES := even_sign_changes (fun s : ℝ => (L.γ₁ s).im)
    (Complex.continuous_im.comp L.cont₁) hper u.im hfin
  have hAfin : ({s : ℝ | (L.γ₁ s).im = u.im ∧
      Cross (fun t : ℝ => (L.γ₁ t).im) u.im s} ∩ Set.Ico (0 : ℝ) 1).Finite :=
    h₁.subset (fun s hs => ⟨hs.2, hs.1.1⟩)
  have hwin₁ : (h₁.toFinset.filter
        (fun s => Cross (fun t : ℝ => (L.γ₁ t).im) u.im (sdWin₁ L u s)))
      = (h₁.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₁ t).im) u.im s)) := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hc⟩
      exact ⟨hs, (Cross_shift_int (h := fun t : ℝ => (L.γ₁ t).im) (c := u.im) hper
        ⌈u.re - (L.γ₁ s).re⌉ s).mp hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨hs, (Cross_shift_int (h := fun t : ℝ => (L.γ₁ t).im) (c := u.im) hper
        ⌈u.re - (L.γ₁ s).re⌉ s).mpr hc⟩
  have hfeq : (h₁.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₁ t).im) u.im s))
      = hAfin.toFinset := by
    ext s
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [hwin₁, hfeq, ← Set.ncard_eq_toFinset_card _ hAfin]
  simpa only [Cross, LPos, LNeg, RPos, RNeg] using hES

theorem sdCross₂_even (L : RayCylLift d fl) (u : ℂ)
    (h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}) :
    Even (h₂.toFinset.filter
        (fun s => Cross (fun t : ℝ => (L.γ₂ t).im) u.im (sdWin₂ L u s))).card := by
  have hper : ∀ s : ℝ, (fun t : ℝ => (L.γ₂ t).im) (s + 1) = (fun t : ℝ => (L.γ₂ t).im) s := by
    intro s
    simp only
    rw [L.per₂ s]
    simp
  have hfin : ({s : ℝ | (L.γ₂ s).im = u.im} ∩ Set.Ico (0 : ℝ) 1).Finite :=
    h₂.subset (fun s hs => ⟨hs.2, hs.1⟩)
  have hES := even_sign_changes (fun s : ℝ => (L.γ₂ s).im)
    (Complex.continuous_im.comp L.cont₂) hper u.im hfin
  have hAfin : ({s : ℝ | (L.γ₂ s).im = u.im ∧
      Cross (fun t : ℝ => (L.γ₂ t).im) u.im s} ∩ Set.Ico (0 : ℝ) 1).Finite :=
    h₂.subset (fun s hs => ⟨hs.2, hs.1.1⟩)
  have hwin₂ : (h₂.toFinset.filter
        (fun s => Cross (fun t : ℝ => (L.γ₂ t).im) u.im (sdWin₂ L u s)))
      = (h₂.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₂ t).im) u.im s)) := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hc⟩
      exact ⟨hs, (Cross_shift_int (h := fun t : ℝ => (L.γ₂ t).im) (c := u.im) hper
        ⌈u.re - (L.γ₂ s).re⌉ s).mp hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨hs, (Cross_shift_int (h := fun t : ℝ => (L.γ₂ t).im) (c := u.im) hper
        ⌈u.re - (L.γ₂ s).re⌉ s).mpr hc⟩
  have hfeq : (h₂.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₂ t).im) u.im s))
      = hAfin.toFinset := by
    ext s
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  rw [hwin₂, hfeq, ← Set.ncard_eq_toFinset_card _ hAfin]
  simpa only [Cross, LPos, LNeg, RPos, RNeg] using hES

/-- **The number of transversal crossings of the segment is even.** -/
theorem sdF_card_even (L : RayCylLift d fl) (u : ℂ)
    {h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}}
    {h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}} :
    Even (sdF L u h₁ h₂).card := by
  have hdisj := sdF_disjoint L u (h₁ := h₁) (h₂ := h₂)
  have hinj₁ : Set.InjOn (sdTime₁ L u)
      ↑(h₁.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₁ t).im) u.im (sdWin₁ L u s))) :=
    (sdTime₁_injOn L u).mono
      (fun s hs => (Set.Finite.mem_toFinset h₁).mp (Finset.mem_filter.mp hs).1)
  have hinj₂ : Set.InjOn (sdTime₂ L u)
      ↑(h₂.toFinset.filter (fun s => Cross (fun t : ℝ => (L.γ₂ t).im) u.im (sdWin₂ L u s))) :=
    (sdTime₂_injOn L u).mono
      (fun s hs => (Set.Finite.mem_toFinset h₂).mp (Finset.mem_filter.mp hs).1)
  rw [sdF, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj₁,
    Finset.card_image_of_injOn hinj₂]
  exact Even.add (sdCross₁_even L u h₁) (sdCross₂_even L u h₂)

/-! ## The flip and non-flip alternatives at a crossing time -/

/-- The **flip alternative** at the crossing time `t` of the segment `[u, u+1]`: the two points
`u + t ± δ` of the segment near `t` (for all small `δ` which stay off the crossing set) are sent by
`Ψ` to the two *opposite* sides of the pair `P`. -/
def sdFlipAt (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN) (u : ℂ)
    (h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im})
    (h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im})
    (t : ℝ) : Prop :=
  ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → t + δ ∈ Set.Icc (0 : ℝ) 1 →
    t - δ ∈ Set.Icc (0 : ℝ) 1 → t + δ ∉ sdT L u h₁ h₂ → t - δ ∉ sdT L u h₁ h₂ →
    (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ∧
        fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P) ∨
      (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P ∧
        fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P)

/-- The **non-flip alternative** at the crossing time `t`. -/
def sdNonFlipAt (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN) (u : ℂ)
    (h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im})
    (h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im})
    (t : ℝ) : Prop :=
  ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → t + δ ∈ Set.Icc (0 : ℝ) 1 →
    t - δ ∈ Set.Icc (0 : ℝ) 1 → t + δ ∉ sdT L u h₁ h₂ → t - δ ∉ sdT L u h₁ h₂ →
    (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ∧
        fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) ∨
      (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P ∧
        fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P)

/-- The `Ψ`-image of a point of the segment `[u, u+1]` off the crossing set lies in one of the two
sides of the pair. -/
theorem sd_side_or {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) {u : ℂ}
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) (hu1 : u.re + 1 < -L.R)
    {h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}}
    {h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}}
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hτT : τ ∉ sdT L u h₁ h₂) :
    fl.Ψ (u + (τ : ℂ)) ∈ Work.EL.pairSide P ∨
      fl.Ψ (u + (τ : ℂ)) ∈ Work.EL.pairSideNear P := by
  have hτΛ : u + (τ : ℂ) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
    fun h => hτT ((mem_sdT_iff L u huΛ hτ).mp h)
  have hre : (u + (τ : ℂ)).re < -L.R := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hτ.2]
  exact hside.mem_or_mem (fun hcurve =>
    hτΛ ((RayCylLift.preimage_pairCurve L P hPa hPb hPy _ hre).mp hcurve))

/-- The `Ψ`-image of a point of the segment off the crossing set is in *exactly* one of the two
sides. -/
theorem sd_side_excl {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    {L : RayCylLift d fl} {P : Work.EL.CoPair d.hN} (hside : Work.EL.PairSides d.hN P)
    {A B : Set ℂ} (hA : A = Work.EL.pairSide P) (hB : B = Work.EL.pairSideNear P) {z : ℂ}
    (hz : z ∈ Work.EL.pairSide P ∨ z ∈ Work.EL.pairSideNear P) :
    ¬ (z ∈ A ∧ z ∈ B) := by
  rintro ⟨h1, h2⟩
  rw [hA] at h1
  rw [hB] at h2
  exact (Set.disjoint_left.mp hside.disjoint h1) h2

/-! ## The flip criterion at a crossing time -/

/-- From an opposite-side alternative and the side data, the two points lie on opposite sides. -/
theorem sd_disjunction_of_iff {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    {P : Work.EL.CoPair d.hN} (hside : Work.EL.PairSides d.hN P) {x y : ℂ}
    (hx : fl.Ψ x ∈ Work.EL.pairSide P ∨ fl.Ψ x ∈ Work.EL.pairSideNear P)
    (hy : fl.Ψ y ∈ Work.EL.pairSide P ∨ fl.Ψ y ∈ Work.EL.pairSideNear P)
    (hiff : (fl.Ψ x ∈ Work.EL.pairSide P ↔ ¬ (fl.Ψ y ∈ Work.EL.pairSide P))) :
    (fl.Ψ x ∈ Work.EL.pairSide P ∧ fl.Ψ y ∈ Work.EL.pairSideNear P) ∨
      (fl.Ψ x ∈ Work.EL.pairSideNear P ∧ fl.Ψ y ∈ Work.EL.pairSide P) := by
  rcases hx with h | h
  · rcases hy with h2 | h2
    · exact absurd h2 (hiff.mp h)
    · exact Or.inl ⟨h, h2⟩
  · rcases hy with h2 | h2
    · exact Or.inr ⟨h, h2⟩
    · exfalso
      exact Set.disjoint_left.mp hside.disjoint
        (hiff.mpr (fun hf => Set.disjoint_left.mp hside.disjoint hf h2)) h

/-- From an equality of the far-side memberships and the side data, both points lie on the same
side. -/
theorem sd_same_of_iff {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    {P : Work.EL.CoPair d.hN} (hside : Work.EL.PairSides d.hN P) {x y : ℂ}
    (hx : fl.Ψ x ∈ Work.EL.pairSide P ∨ fl.Ψ x ∈ Work.EL.pairSideNear P)
    (hy : fl.Ψ y ∈ Work.EL.pairSide P ∨ fl.Ψ y ∈ Work.EL.pairSideNear P)
    (hiff : (fl.Ψ x ∈ Work.EL.pairSide P ↔ (fl.Ψ y ∈ Work.EL.pairSide P))) :
    (fl.Ψ x ∈ Work.EL.pairSide P ∧ fl.Ψ y ∈ Work.EL.pairSide P) ∨
      (fl.Ψ x ∈ Work.EL.pairSideNear P ∧ fl.Ψ y ∈ Work.EL.pairSideNear P) := by
  rcases hx with h | h
  · exact Or.inl ⟨h, hiff.mp h⟩
  · rcases hy with h2 | h2
    · exfalso
      exact Set.disjoint_left.mp hside.disjoint (hiff.mpr h2) h
    · exact Or.inr ⟨h, h2⟩

/-- **A transversal crossing flips the side.**  At a crossing time `t` of the transversal set
`sdF` with parameter `s` (so that `s₀ = sdWinᵢ L u s` is the parameter of the crossing point
`u + t = γᵢ s₀` of the lift), the two points `u + t ± δ` of the segment — for every sufficiently
small `δ` which stays off the crossing set — are sent by `Ψ` to opposite sides of the pair. -/
theorem sdFlip_of_mem_sdF {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) {u : ℂ}
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) (hu1 : u.re + 1 < -L.R)
    (hiso : ∀ w : ℂ, w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ → w.im = u.im → u.re ≤ w.re →
      w.re ≤ u.re + 1 → ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
        w + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
        w - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    {h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}}
    {h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}}
    {t : ℝ} (ht : t ∈ sdF L u h₁ h₂) : sdFlipAt L P u h₁ h₂ t := by
  rcases Finset.mem_union.mp ht with hmem | hmem
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hmem
    obtain ⟨hslev, hcross⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsIco, him⟩ := (Set.Finite.mem_toFinset h₁).mp hslev
    have ht1 : t < 1 := by rw [← hst]; exact (sdTime₁_mem_Icc L u s).2
    have hw : L.γ₁ (sdWin₁ L u s) = u + (t : ℂ) := by rw [← hst, sdTime₁_spec L u him]
    have hwim : (L.γ₁ (sdWin₁ L u s)).im = u.im := by rw [sdWin₁_im, him]
    have hw₀ : u.re ≤ (L.γ₁ (sdWin₁ L u s)).re := by
      have := (sdTime₁_mem_Icc L u s).1
      simp only [sdTime₁] at this
      linarith
    have hw₁ : (L.γ₁ (sdWin₁ L u s)).re ≤ u.re + 1 := by
      have := (sdTime₁_mem_Icc L u s).2
      simp only [sdTime₁] at this
      linarith
    obtain ⟨δs, hδspos, hδsspec⟩ := hiso _ (Or.inl ⟨sdWin₁ L u s, rfl⟩) hwim hw₀ hw₁
    have hre : (L.γ₁ (sdWin₁ L u s)).re < -L.R := by
      have h1 := (sdTime₁_mem_Icc L u s).2
      rw [hw]
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hflip := (side_flip_at_crossing d fl L P hPa hPb hPy hside hre ⟨δs, hδspos, hδsspec⟩).mp
      (by simpa only [sdWin₁_im, him] using (cross_iff_single'.mp hcross))
    obtain ⟨δc, hδcpos, hδc⟩ := hflip
    refine ⟨min δc δs, lt_min hδcpos hδspos, fun δ hδpos hδlt hIcc₁ hIcc₂ hT₁ hT₂ => ?_⟩
    have hδδc : δ < δc := lt_of_lt_of_le hδlt (min_le_left _ _)
    have heq₁ : L.γ₁ (sdWin₁ L u s) + (δ : ℂ) = u + ((t + δ : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    have heq₂ : L.γ₁ (sdWin₁ L u s) - (δ : ℂ) = u + ((t - δ : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    have hiff : (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        ¬ (fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P)) := by
      have h := hδc δ ⟨hδpos, hδδc⟩
      rwa [heq₁, heq₂] at h
    exact sd_disjunction_of_iff hside
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hIcc₁ hT₁)
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hIcc₂ hT₂) hiff
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hmem
    obtain ⟨hslev, hcross⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsIco, him⟩ := (Set.Finite.mem_toFinset h₂).mp hslev
    have ht1 : t < 1 := by rw [← hst]; exact (sdTime₂_mem_Icc L u s).2
    have hw : L.γ₂ (sdWin₂ L u s) = u + (t : ℂ) := by rw [← hst, sdTime₂_spec L u him]
    have hwim : (L.γ₂ (sdWin₂ L u s)).im = u.im := by rw [sdWin₂_im, him]
    have hw₀ : u.re ≤ (L.γ₂ (sdWin₂ L u s)).re := by
      have := (sdTime₂_mem_Icc L u s).1
      simp only [sdTime₂] at this
      linarith
    have hw₁ : (L.γ₂ (sdWin₂ L u s)).re ≤ u.re + 1 := by
      have := (sdTime₂_mem_Icc L u s).2
      simp only [sdTime₂] at this
      linarith
    obtain ⟨δs, hδspos, hδsspec⟩ := hiso _ (Or.inr ⟨sdWin₂ L u s, rfl⟩) hwim hw₀ hw₁
    have hre : (L.γ₂ (sdWin₂ L u s)).re < -L.R := by
      have h1 := (sdTime₂_mem_Icc L u s).2
      rw [hw]
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hflip := (side_flip_at_crossing_gamma2 d fl L P hPa hPb hPy hside hre
      ⟨δs, hδspos, hδsspec⟩).mp
      (by simpa only [sdWin₂_im, him] using (cross_iff_single'.mp hcross))
    obtain ⟨δc, hδcpos, hδc⟩ := hflip
    refine ⟨min δc δs, lt_min hδcpos hδspos, fun δ hδpos hδlt hIcc₁ hIcc₂ hT₁ hT₂ => ?_⟩
    have hδδc : δ < δc := lt_of_lt_of_le hδlt (min_le_left _ _)
    have heq₁ : L.γ₂ (sdWin₂ L u s) + (δ : ℂ) = u + ((t + δ : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    have heq₂ : L.γ₂ (sdWin₂ L u s) - (δ : ℂ) = u + ((t - δ : ℝ) : ℂ) := by
      rw [hw]; push_cast; ring
    have hiff : (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        ¬ (fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P)) := by
      have h := hδc δ ⟨hδpos, hδδc⟩
      rwa [heq₁, heq₂] at h
    exact sd_disjunction_of_iff hside
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hIcc₁ hT₁)
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hIcc₂ hT₂) hiff

/-- **A non-transversal crossing does not flip the side.**  If the parameter `s` of the crossing
time `t` is not a sign change of the height `s ↦ (γᵢ s).im`, then the two points `u + t ± δ` of the
segment (for all small `δ` which stay off the crossing set) are sent by `Ψ` to the *same* side of
the pair. -/
theorem sdNonFlip_of_mem_sdT_not_mem_sdF {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (L : RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P) {u : ℂ}
    (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) (hu1 : u.re + 1 < -L.R)
    (hiso : ∀ w : ℂ, w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ → w.im = u.im → u.re ≤ w.re →
      w.re ≤ u.re + 1 → ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
        w + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
        w - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂)
    {h₁ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}}
    {h₂ : Set.Finite {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}}
    {t : ℝ} (ht : t ∈ sdT L u h₁ h₂) (htF : t ∉ sdF L u h₁ h₂) :
    sdNonFlipAt L P u h₁ h₂ t := by
  have ht0 : 0 < t := sdT_pos L u huΛ ht
  have ht1 : t < 1 := sdT_lt_one L u ht
  have hoff : ∀ τ ∈ Set.Icc (0 : ℝ) 1, τ ∉ sdT L u h₁ h₂ →
      fl.Ψ (u + (τ : ℂ)) ∈ Work.EL.pairSide P ∪ Work.EL.pairSideNear P :=
    fun τ hτ hτT => by
      rw [Set.mem_union]
      exact sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hτ hτT
  have hseg : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → a ≤ b →
      (∀ τ ∈ Set.Icc a b, τ ∉ sdT L u h₁ h₂) →
      (fl.Ψ (u + (a : ℂ)) ∈ Work.EL.pairSide P ↔
        fl.Ψ (u + (b : ℂ)) ∈ Work.EL.pairSide P) := by
    intro a b ha hb hab havoid
    exact side_iff_of_Icc (A := Work.EL.pairSide P) (B := Work.EL.pairSideNear P)
      (σ := fun τ : ℝ => fl.Ψ (u + (τ : ℂ))) (b := 1) (T := sdT L u h₁ h₂)
      hside.isOpen_far hside.isOpen_near hside.disjoint
      (fl.Ψ_diff.continuous.comp (continuous_const.add Complex.continuous_ofReal))
      hoff ha hb hab havoid
  rcases Finset.mem_union.mp ht with hmem | hmem
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hmem
    obtain ⟨hsIco, him⟩ := (Set.Finite.mem_toFinset h₁).mp hs
    have hncross : ¬ Cross (fun τ : ℝ => (L.γ₁ τ).im) u.im (sdWin₁ L u s) := by
      intro hc
      refine htF ?_
      have hmem' : sdTime₁ L u s ∈ sdF L u h₁ h₂ :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
          ⟨s, Finset.mem_filter.mpr ⟨hs, hc⟩, rfl⟩))
      simpa [hst] using hmem'
    have hw : L.γ₁ (sdWin₁ L u s) = u + (t : ℂ) := by rw [← hst, sdTime₁_spec L u him]
    have hwim : (L.γ₁ (sdWin₁ L u s)).im = u.im := by rw [sdWin₁_im, him]
    have hw₀ : u.re ≤ (L.γ₁ (sdWin₁ L u s)).re := by
      have := (sdTime₁_mem_Icc L u s).1
      simp only [sdTime₁] at this
      linarith
    have hw₁ : (L.γ₁ (sdWin₁ L u s)).re ≤ u.re + 1 := by
      have := (sdTime₁_mem_Icc L u s).2
      simp only [sdTime₁] at this
      linarith
    obtain ⟨δ₁, hδ₁pos, hδ₁spec⟩ := hiso _ (Or.inl ⟨sdWin₁ L u s, rfl⟩) hwim hw₀ hw₁
    have hre : (L.γ₁ (sdWin₁ L u s)).re < -L.R := by
      have h1 := (sdTime₁_mem_Icc L u s).2
      rw [hw]
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hp₁ : ∀ τ : ℝ, t < τ → τ < t + δ₁ → τ ≤ 1 → τ ∉ sdT L u h₁ h₂ := by
      intro τ h1 h2 h3 hτT
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h3⟩
      have hmem' : u + (τ : ℂ) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
        (mem_sdT_iff L u huΛ hτIcc).mpr hτT
      have hoff₁ := (hδ₁spec (τ - t) ⟨by linarith, by linarith⟩).1
      have heq : u + (τ : ℂ) = L.γ₁ (sdWin₁ L u s) + ((τ - t : ℝ) : ℂ) := by
        rw [hw]; push_cast; ring
      rw [heq] at hmem'
      exact hoff₁ hmem'
    have hm₁ : ∀ τ : ℝ, t - δ₁ < τ → τ < t → 0 ≤ τ → τ ∉ sdT L u h₁ h₂ := by
      intro τ h1 h2 h3 hτT
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨h3, by linarith⟩
      have hmem' : u + (τ : ℂ) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
        (mem_sdT_iff L u huΛ hτIcc).mpr hτT
      have hoff₁ := (hδ₁spec (t - τ) ⟨by linarith, by linarith⟩).2
      have heq : u + (τ : ℂ) = L.γ₁ (sdWin₁ L u s) - ((t - τ : ℝ) : ℂ) := by
        rw [hw]; push_cast; ring
      rw [heq] at hmem'
      exact hoff₁ hmem'
    set δ₀ : ℝ := min (δ₁ / 2) (min (t / 2) ((1 - t) / 2)) with hδ₀def
    have hδ₀pos : 0 < δ₀ := by
      rw [hδ₀def]
      exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hδ₀δ₁ : δ₀ < δ₁ := by
      rw [hδ₀def]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ₀t : δ₀ ≤ t / 2 := by
      rw [hδ₀def]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ₀t' : δ₀ ≤ (1 - t) / 2 := by
      rw [hδ₀def]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have htδ₀ : t + δ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have htδ₀' : t - δ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hKey : (fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
      by_contra hne
      have hRef : (fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P)) := by
        by_cases hA : fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P
        · refine ⟨fun _ hB => hne ⟨fun _ => hB, fun _ => hA⟩, fun _ => hA⟩
        · refine ⟨fun h hB => absurd h hA,
            fun h => False.elim (absurd ⟨fun h' => absurd h' hA, fun h' => absurd h' h⟩ hne)⟩
      have hsideR : (∃ ε > 0, ∀ u' ∈ Set.Ioo (0 : ℝ) ε,
          fl.Ψ (L.γ₁ (sdWin₁ L u s) + (u' : ℂ)) ∈ Work.EL.pairSide P ↔
            ¬ (fl.Ψ (L.γ₁ (sdWin₁ L u s) - (u' : ℂ)) ∈ Work.EL.pairSide P)) := by
        refine ⟨δ₀, hδ₀pos, fun u' hu' => ?_⟩
        have hR : (fl.Ψ (u + ((t + u' : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
            fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) :=
          hseg (t + u') (t + δ₀) ⟨by linarith [hu'.1, hu'.2], by linarith [hu'.1, hu'.2]⟩ htδ₀
            (by linarith [hu'.1, hu'.2])
            (fun τ hτ => hp₁ τ (by linarith [hτ.1, hu'.1]) (by linarith [hτ.2, hδ₀δ₁])
              (by linarith [hτ.2, hδ₀t']))
        have hL : (fl.Ψ (u + ((t - u' : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
            fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
          have h := hseg (t - δ₀) (t - u') ⟨by linarith, by linarith [hu'.1, hu'.2]⟩
            ⟨by linarith [hu'.1, hu'.2], by linarith [hu'.1, hu'.2]⟩
            (by linarith [hu'.1, hu'.2])
            (fun τ hτ => hm₁ τ (by linarith [hτ.1, hδ₀δ₁]) (by linarith [hτ.2, hu'.1])
              (by linarith [hτ.1, hδ₀t]))
          exact h.symm
        have heqR : L.γ₁ (sdWin₁ L u s) + ((u' : ℝ) : ℂ) = u + ((t + u' : ℝ) : ℂ) := by
          rw [hw]; push_cast; ring
        have heqL : L.γ₁ (sdWin₁ L u s) - ((u' : ℝ) : ℂ) = u + ((t - u' : ℝ) : ℂ) := by
          rw [hw]; push_cast; ring
        rw [heqR, heqL, hR, hL]
        exact hRef
      have hwin : Cross (fun τ : ℝ => (L.γ₁ τ).im) u.im (sdWin₁ L u s) :=
        cross_iff_single'.mpr (by
          have hfx := (side_flip_at_crossing d fl L P hPa hPb hPy hside hre
            ⟨δ₁, hδ₁pos, hδ₁spec⟩).mpr hsideR
          simpa only [sdWin₁_im, him] using hfx)
      exact hncross hwin
    refine ⟨δ₀, hδ₀pos, fun δ hδpos hδlt hI₁ hI₂ hT₁ hT₂ => ?_⟩
    have hR : (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) :=
      hseg (t + δ) (t + δ₀) ⟨by linarith [hI₁.1], by linarith [hI₁.2]⟩ htδ₀
        (by linarith [hδlt])
        (fun τ hτ => hp₁ τ (by linarith [hτ.1, hδpos]) (by linarith [hτ.2, hδ₀δ₁])
            (by linarith [hτ.2, hδ₀t']))
    have hL : (fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
      have h := hseg (t - δ₀) (t - δ) ⟨by linarith [hδ₀t], by linarith [hδpos]⟩
        ⟨by linarith [hI₂.1], by linarith [hI₂.2]⟩ (by linarith [hδlt])
        (fun τ hτ => hm₁ τ (by linarith [hτ.1, hδ₀δ₁]) (by linarith [hτ.2, hδpos])
            (by linarith [hτ.1, hδ₀t]))
      exact h.symm
    exact sd_same_of_iff hside
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hI₁ hT₁)
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hI₂ hT₂)
      (hR.trans (hKey.trans hL.symm))
  · obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp hmem
    obtain ⟨hsIco, him⟩ := (Set.Finite.mem_toFinset h₂).mp hs
    have hncross : ¬ Cross (fun τ : ℝ => (L.γ₂ τ).im) u.im (sdWin₂ L u s) := by
      intro hc
      refine htF ?_
      have hmem' : sdTime₂ L u s ∈ sdF L u h₁ h₂ :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨s, Finset.mem_filter.mpr ⟨hs, hc⟩, rfl⟩))
      simpa [hst] using hmem'
    have hw : L.γ₂ (sdWin₂ L u s) = u + (t : ℂ) := by rw [← hst, sdTime₂_spec L u him]
    have hwim : (L.γ₂ (sdWin₂ L u s)).im = u.im := by rw [sdWin₂_im, him]
    have hw₀ : u.re ≤ (L.γ₂ (sdWin₂ L u s)).re := by
      have := (sdTime₂_mem_Icc L u s).1
      simp only [sdTime₂] at this
      linarith
    have hw₁ : (L.γ₂ (sdWin₂ L u s)).re ≤ u.re + 1 := by
      have := (sdTime₂_mem_Icc L u s).2
      simp only [sdTime₂] at this
      linarith
    obtain ⟨δ₁, hδ₁pos, hδ₁spec⟩ := hiso _ (Or.inr ⟨sdWin₂ L u s, rfl⟩) hwim hw₀ hw₁
    have hre : (L.γ₂ (sdWin₂ L u s)).re < -L.R := by
      have h1 := (sdTime₂_mem_Icc L u s).2
      rw [hw]
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    have hp₁ : ∀ τ : ℝ, t < τ → τ < t + δ₁ → τ ≤ 1 → τ ∉ sdT L u h₁ h₂ := by
      intro τ h1 h2 h3 hτT
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, h3⟩
      have hmem' : u + (τ : ℂ) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
        (mem_sdT_iff L u huΛ hτIcc).mpr hτT
      have hoff₁ := (hδ₁spec (τ - t) ⟨by linarith, by linarith⟩).1
      have heq : u + (τ : ℂ) = L.γ₂ (sdWin₂ L u s) + ((τ - t : ℝ) : ℂ) := by
        rw [hw]; push_cast; ring
      rw [heq] at hmem'
      exact hoff₁ hmem'
    have hm₁ : ∀ τ : ℝ, t - δ₁ < τ → τ < t → 0 ≤ τ → τ ∉ sdT L u h₁ h₂ := by
      intro τ h1 h2 h3 hτT
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨h3, by linarith⟩
      have hmem' : u + (τ : ℂ) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
        (mem_sdT_iff L u huΛ hτIcc).mpr hτT
      have hoff₁ := (hδ₁spec (t - τ) ⟨by linarith, by linarith⟩).2
      have heq : u + (τ : ℂ) = L.γ₂ (sdWin₂ L u s) - ((t - τ : ℝ) : ℂ) := by
        rw [hw]; push_cast; ring
      rw [heq] at hmem'
      exact hoff₁ hmem'
    set δ₀ : ℝ := min (δ₁ / 2) (min (t / 2) ((1 - t) / 2)) with hδ₀def
    have hδ₀pos : 0 < δ₀ := by
      rw [hδ₀def]
      exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hδ₀δ₁ : δ₀ < δ₁ := by
      rw [hδ₀def]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδ₀t : δ₀ ≤ t / 2 := by
      rw [hδ₀def]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ₀t' : δ₀ ≤ (1 - t) / 2 := by
      rw [hδ₀def]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have htδ₀ : t + δ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have htδ₀' : t - δ₀ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hKey : (fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
      by_contra hne
      have hRef : (fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
          ¬ (fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P)) := by
        by_cases hA : fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P
        · refine ⟨fun _ hB => hne ⟨fun _ => hB, fun _ => hA⟩, fun _ => hA⟩
        · refine ⟨fun h hB => absurd h hA,
            fun h => False.elim (absurd ⟨fun h' => absurd h' hA, fun h' => absurd h' h⟩ hne)⟩
      have hsideR : (∃ ε > 0, ∀ u' ∈ Set.Ioo (0 : ℝ) ε,
          fl.Ψ (L.γ₂ (sdWin₂ L u s) + (u' : ℂ)) ∈ Work.EL.pairSide P ↔
            ¬ (fl.Ψ (L.γ₂ (sdWin₂ L u s) - (u' : ℂ)) ∈ Work.EL.pairSide P)) := by
        refine ⟨δ₀, hδ₀pos, fun u' hu' => ?_⟩
        have hR : (fl.Ψ (u + ((t + u' : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
            fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) :=
          hseg (t + u') (t + δ₀) ⟨by linarith [hu'.1, hu'.2], by linarith [hu'.1, hu'.2]⟩ htδ₀
            (by linarith [hu'.1, hu'.2])
            (fun τ hτ => hp₁ τ (by linarith [hτ.1, hu'.1]) (by linarith [hτ.2, hδ₀δ₁])
              (by linarith [hτ.2, hδ₀t']))
        have hL : (fl.Ψ (u + ((t - u' : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
            fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
          have h := hseg (t - δ₀) (t - u') ⟨by linarith, by linarith [hu'.1, hu'.2]⟩
            ⟨by linarith [hu'.1, hu'.2], by linarith [hu'.1, hu'.2]⟩
            (by linarith [hu'.1, hu'.2])
            (fun τ hτ => hm₁ τ (by linarith [hτ.1, hδ₀δ₁]) (by linarith [hτ.2, hu'.1])
              (by linarith [hτ.1, hδ₀t]))
          exact h.symm
        have heqR : L.γ₂ (sdWin₂ L u s) + ((u' : ℝ) : ℂ) = u + ((t + u' : ℝ) : ℂ) := by
          rw [hw]; push_cast; ring
        have heqL : L.γ₂ (sdWin₂ L u s) - ((u' : ℝ) : ℂ) = u + ((t - u' : ℝ) : ℂ) := by
          rw [hw]; push_cast; ring
        rw [heqR, heqL, hR, hL]
        exact hRef
      have hwin : Cross (fun τ : ℝ => (L.γ₂ τ).im) u.im (sdWin₂ L u s) :=
        cross_iff_single'.mpr (by
          have hfx := (side_flip_at_crossing_gamma2 d fl L P hPa hPb hPy hside hre
            ⟨δ₁, hδ₁pos, hδ₁spec⟩).mpr hsideR
          simpa only [sdWin₂_im, him] using hfx)
      exact hncross hwin
    refine ⟨δ₀, hδ₀pos, fun δ hδpos hδlt hI₁ hI₂ hT₁ hT₂ => ?_⟩
    have hR : (fl.Ψ (u + ((t + δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        fl.Ψ (u + ((t + δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) :=
      hseg (t + δ) (t + δ₀) ⟨by linarith [hI₁.1], by linarith [hI₁.2]⟩ htδ₀
        (by linarith [hδlt])
        (fun τ hτ => hp₁ τ (by linarith [hτ.1, hδpos]) (by linarith [hτ.2, hδ₀δ₁])
            (by linarith [hτ.2, hδ₀t']))
    have hL : (fl.Ψ (u + ((t - δ : ℝ) : ℂ)) ∈ Work.EL.pairSide P ↔
        fl.Ψ (u + ((t - δ₀ : ℝ) : ℂ)) ∈ Work.EL.pairSide P) := by
      have h := hseg (t - δ₀) (t - δ) ⟨by linarith [hδ₀t], by linarith [hδpos]⟩
        ⟨by linarith [hI₂.1], by linarith [hI₂.2]⟩ (by linarith [hδlt])
        (fun τ hτ => hm₁ τ (by linarith [hτ.1, hδ₀δ₁]) (by linarith [hτ.2, hδpos])
            (by linarith [hτ.1, hδ₀t]))
      exact h.symm
    exact sd_same_of_iff hside
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hI₁ hT₁)
      (sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hI₂ hT₂)
      (hR.trans (hKey.trans hL.symm))

/-! ## The main theorem -/

theorem sidePreserve_core_of_crossing_parity {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {u : ℂ} (huΛ : u ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) (hu : u.re < -L.R) (hu1 : u.re + 1 < -L.R)
    (hfin₁ : ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₁ s).im = u.im}).Finite)
    (hfin₂ : ({s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ (L.γ₂ s).im = u.im}).Finite) :
    (fl.Ψ u ∈ Work.EL.pairSide P ↔ fl.Ψ (u + 1) ∈ Work.EL.pairSide P) := by
  -- the isolation of the crossing points of the horizontal line
  have hiso : ∀ w : ℂ, w ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ → w.im = u.im → u.re ≤ w.re →
      w.re ≤ u.re + 1 → ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
        w + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
        w - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ :=
    fun w h1 h2 h3 h4 => cyl_horizontal_isolated L hfin₁ hfin₂ h1 h2 h3 h4
  -- `u + 1` is off the two lifts as well
  have hu1Λ : u + 1 ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ := by
    intro h
    refine huΛ ?_
    have := (g2_range_sub_one L (u + 1)).mp h
    simpa using this
  have hnotcurve1 : fl.Ψ (u + 1) ∉ Work.EL.pairCurve P := by
    intro hcurve
    refine hu1Λ ((RayCylLift.preimage_pairCurve L P hPa hPb hPy (u + 1) (by simpa using hu1)).mp hcurve)
  -- the datum of the walking lemma
  have hoff : ∀ τ ∈ Set.Icc (0 : ℝ) 1, τ ∉ sdT L u hfin₁ hfin₂ →
      fl.Ψ (u + (τ : ℂ)) ∈ Work.EL.pairSide P ∪ Work.EL.pairSideNear P :=
    fun τ hτ hτT => by
      rw [Set.mem_union]
      exact sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hτ hτT
  have hoff' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, τ ∉ sdT L u hfin₁ hfin₂ →
      fl.Ψ (u + (τ : ℂ)) ∈ Work.EL.pairSideNear P ∪ Work.EL.pairSide P :=
    fun τ hτ hτT => by
      rw [Set.mem_union]
      rcases sd_side_or d fl L P hPa hPb hPy hside huΛ hu1 hτ hτT with h | h
      · exact Or.inr h
      · exact Or.inl h
  have heven : Even (sdF L u hfin₁ hfin₂).card := sdF_card_even L u
  have hFflip : ∀ t ∈ sdF L u hfin₁ hfin₂, sdFlipAt L P u hfin₁ hfin₂ t :=
    fun t ht => sdFlip_of_mem_sdF d fl L P hPa hPb hPy hside huΛ hu1 hiso ht
  have hTnotF : ∀ t ∈ sdT L u hfin₁ hfin₂, t ∉ sdF L u hfin₁ hfin₂ →
      sdNonFlipAt L P u hfin₁ hfin₂ t :=
    fun t ht htF => sdNonFlip_of_mem_sdT_not_mem_sdF d fl L P hPa hPb hPy hside huΛ hu1 hiso ht htF
  -- the walk from `u + 1` to `u`
  have hstep1 : fl.Ψ (u + ((1 : ℝ) : ℂ)) ∈ Work.EL.pairSide P →
      fl.Ψ (u + ((0 : ℝ) : ℂ)) ∈ Work.EL.pairSide P := by
    intro htop
    refine same_side_of_even_flips (A := Work.EL.pairSide P) (B := Work.EL.pairSideNear P)
      (σ := fun τ : ℝ => fl.Ψ (u + (τ : ℂ))) (b := 1) (T := sdT L u hfin₁ hfin₂)
      (F := sdF L u hfin₁ hfin₂) hside.isOpen_far hside.isOpen_near hside.disjoint ?_ one_pos
      ?_ ?_ ?_ ?_ ?_ hoff heven htop
    · exact fl.Ψ_diff.continuous.comp (continuous_const.add Complex.continuous_ofReal)
    · intro t ht; exact sdT_pos L u huΛ ht
    · intro t ht; exact sdT_lt_one L u ht
    · intro t ht; exact sdF_subset_sdT L u ht
    · intro t ht
      obtain ⟨ε, hε, hspec⟩ := hFflip t ht
      exact ⟨ε, hε, fun δ hδ hδε hI₁ hI₂ hT₁ hT₂ => hspec δ hδ hδε hI₁ hI₂ hT₁ hT₂⟩
    · intro t ht htF
      obtain ⟨ε, hε, hspec⟩ := hTnotF t ht htF
      exact ⟨ε, hε, fun δ hδ hδε hI₁ hI₂ hT₁ hT₂ => hspec δ hδ hδε hI₁ hI₂ hT₁ hT₂⟩
  -- the walk from `u` to `u + 1`, with the two sides exchanged
  have hstep2 : fl.Ψ (u + ((1 : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P →
      fl.Ψ (u + ((0 : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P := by
    intro htop
    refine same_side_of_even_flips (A := Work.EL.pairSideNear P) (B := Work.EL.pairSide P)
      (σ := fun τ : ℝ => fl.Ψ (u + (τ : ℂ))) (b := 1) (T := sdT L u hfin₁ hfin₂)
      (F := sdF L u hfin₁ hfin₂) hside.isOpen_near hside.isOpen_far hside.disjoint.symm ?_
      one_pos ?_ ?_ ?_ ?_ ?_ hoff' heven htop
    · exact fl.Ψ_diff.continuous.comp (continuous_const.add Complex.continuous_ofReal)
    · intro t ht; exact sdT_pos L u huΛ ht
    · intro t ht; exact sdT_lt_one L u ht
    · intro t ht; exact sdF_subset_sdT L u ht
    · intro t ht
      obtain ⟨ε, hε, hspec⟩ := hFflip t ht
      exact ⟨ε, hε, fun δ hδ hδε hI₁ hI₂ hT₁ hT₂ =>
        (hspec δ hδ hδε hI₁ hI₂ hT₁ hT₂).elim (fun h => Or.inr h) (fun h => Or.inl h)⟩
    · intro t ht htF
      obtain ⟨ε, hε, hspec⟩ := hTnotF t ht htF
      exact ⟨ε, hε, fun δ hδ hδε hI₁ hI₂ hT₁ hT₂ =>
        (hspec δ hδ hδε hI₁ hI₂ hT₁ hT₂).elim (fun h => Or.inr h) (fun h => Or.inl h)⟩
  refine ⟨?_, ?_⟩
  · intro h
    by_contra hc
    have hnear1 : fl.Ψ (u + 1) ∈ Work.EL.pairSideNear P := by
      rcases hside.mem_or_mem hnotcurve1 with hf | hn
      · exact absurd hf hc
      · exact hn
    have hnear0 : fl.Ψ (u + ((0 : ℝ) : ℂ)) ∈ Work.EL.pairSideNear P :=
      hstep2 (by simpa using hnear1)
    exact (Set.disjoint_left.mp hside.disjoint h) (by simpa using hnear0)
  · intro h
    have := hstep1 (by simpa using h)
    simpa using this

end Work.ELRig
