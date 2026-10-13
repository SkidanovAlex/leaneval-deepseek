/-
# `FTS/GalFields/Tail/SlotAdjoints` — the formal adjoints of `D_z` and `D_θ`

The slot pairing `Work.FTS.TransportS.slotPairing ρ p q U V` pairs the *derivatives*
`D_z^q D_θ^p U` of the first argument against `ρ·D_z^q D_θ^p V`.  When `V` (and hence `ρ·D_z^qD_θ^pV`)
vanishes off a compact box inside the open quadrant, all the derivatives can be moved off `U` onto
that compactly supported factor, by the two one-variable integration-by-parts identities

  `∫_z (z ∂_z u) · v = ∫_z u · (adjZ v)`,    `adjZ v = -(v + z ∂_z v)`,
  `∫_θ (sin 2θ ∂_θ u) · v = ∫_θ u · (adjTh v)`, `adjTh v = -(sin 2θ ∂_θ v + 2 cos 2θ · v)`,

whose boundary terms vanish because `adjZ`/`adjTh` preserve the support box.

This module fixes the notation `adjZ`, `adjTh`, `adjZIter`, `adjThIter` and provides the
smoothness of the iterates on the open quadrant, together with the elementary fact that the
adjoints preserve the property of vanishing off a box (given the corresponding property for
`pz` and `pth`, which is supplied by the consumer).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `SmoothOpen` closure (local copies of the elementary facts) -/

theorem SmoothOpen.add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.add hg

theorem SmoothOpen.neg {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) := by
  have h : Function.uncurry (fun z θ => -f z θ)
      = fun p : ℝ × ℝ => -Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.neg

theorem SmoothOpen.mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have h : Function.uncurry (fun z θ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact hf.mul hg

theorem SmoothOpen.const (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ _ : ℝ => c) := by
  have h : Function.uncurry (fun _ _ : ℝ => c) = fun _ : ℝ × ℝ => c := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact contDiffOn_const

theorem SmoothOpen.const_mul {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (c : ℝ) : Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  have h : Function.uncurry (fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact contDiffOn_const.mul hf

/-- `θ ↦ 2 cos(2θ)`, as a function on the quadrant, is `C^∞` on the open quadrant. -/
theorem SmoothOpen.cos2 :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => 2 * Real.cos (2 * θ)) := by
  have h : Function.uncurry (fun _ θ : ℝ => 2 * Real.cos (2 * θ))
      = fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact (show ContDiff ℝ ⊤ (fun p : ℝ × ℝ => 2 * Real.cos (2 * p.2)) from by
    fun_prop).contDiffOn.of_le le_top

/-! ## The adjoints -/

/-- The formal adjoint of `D_z = z ∂_z`: `adjZ G = -(G + z ∂_z G)`.  It satisfies
`∫_z (D_z u) · v = ∫_z u · (adjZ v)` whenever the boundary term `z u v` vanishes. -/
def adjZ (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => -(G z θ + Work.Spaces.Dz G z θ)

/-- The formal adjoint of `D_θ = sin(2θ) ∂_θ`:
`adjTh G = -(sin(2θ)·∂_θ G + 2 cos(2θ)·G)`.  It satisfies
`∫_θ (D_θ u) · v = ∫_θ u · (adjTh v)` whenever the boundary term `sin(2θ) u v` vanishes. -/
def adjTh (G : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(Work.Spaces.Dth G z θ + 2 * Real.cos (2 * θ) * G z θ)

/-- The `n`-fold iterate of `adjZ`. -/
def adjZIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, G => G
  | n + 1, G => adjZ (adjZIter n G)

/-- The `n`-fold iterate of `adjTh`. -/
def adjThIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, G => G
  | n + 1, G => adjTh (adjThIter n G)

@[simp] theorem adjZIter_zero (G : ℝ → ℝ → ℝ) : adjZIter 0 G = G := rfl
@[simp] theorem adjZIter_succ (n : ℕ) (G : ℝ → ℝ → ℝ) :
    adjZIter (n + 1) G = adjZ (adjZIter n G) := rfl
@[simp] theorem adjThIter_zero (G : ℝ → ℝ → ℝ) : adjThIter 0 G = G := rfl
@[simp] theorem adjThIter_succ (n : ℕ) (G : ℝ → ℝ → ℝ) :
    adjThIter (n + 1) G = adjTh (adjThIter n G) := rfl

theorem adjZIter_comp (n : ℕ) (G : ℝ → ℝ → ℝ) : adjZIter n (adjZ G) = adjZIter (n + 1) G := by
  induction n with
  | zero => rfl
  | succ n ih => rw [adjZIter_succ, adjZIter_succ, ih]

theorem adjThIter_comp (n : ℕ) (G : ℝ → ℝ → ℝ) :
    adjThIter n (adjTh G) = adjThIter (n + 1) G := by
  induction n with
  | zero => rfl
  | succ n ih => rw [adjThIter_succ, adjThIter_succ, ih]

/-- Unfolding of `adjZ` through the `z`-slice derivative. -/
theorem adjZ_eq (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    adjZ G z θ = -(G z θ + z * deriv (fun y : ℝ => G y θ) z) := rfl

/-- Unfolding of `adjTh` through the `θ`-slice derivative. -/
theorem adjTh_eq (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    adjTh G z θ
      = -(Real.sin (2 * θ) * deriv (fun y : ℝ => G z y) θ
          + 2 * Real.cos (2 * θ) * G z θ) := rfl

/-! ## Smoothness of the adjoint iterates on the open quadrant -/

theorem smoothOpen_adjZ {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (adjZ G) := by
  have h : Function.uncurry (adjZ G)
      = fun p : ℝ × ℝ => -(Function.uncurry G p + Function.uncurry (Work.Spaces.Dz G) p) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact (hG.add hG.Dz).neg

theorem smoothOpen_adjTh {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (adjTh G) := by
  have h : Function.uncurry (adjTh G)
      = fun p : ℝ × ℝ => -(Function.uncurry (Work.Spaces.Dth G) p
          + Function.uncurry (fun z θ => 2 * Real.cos (2 * θ) * G z θ) p) := rfl
  rw [Work.FTS.EllipticEst.SmoothOpen, h]
  exact (hG.Dth.add (SmoothOpen.cos2.mul hG)).neg

theorem smoothOpen_adjZIter {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (n : ℕ) : Work.FTS.EllipticEst.SmoothOpen (adjZIter n G) := by
  induction n with
  | zero => simpa using hG
  | succ n ih => rw [adjZIter_succ]; exact smoothOpen_adjZ ih

theorem smoothOpen_adjThIter {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G)
    (n : ℕ) : Work.FTS.EllipticEst.SmoothOpen (adjThIter n G) := by
  induction n with
  | zero => simpa using hG
  | succ n ih => rw [adjThIter_succ]; exact smoothOpen_adjTh ih

/-! ## The adjoints preserve vanishing off a box -/

/-- If `G` vanishes off the box `[a,b] × [δ,π/2-δ]`, then so do its plain partial derivatives
`pz G` and `pth G`.  (No smoothness is needed: off the box the relevant slice is either
identically zero, or zero on a neighbourhood of the point.) -/
theorem pz_pth_eq_zero_of_vanish {a b δ : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : ∀ z θ : ℝ,
      (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → G z θ = 0) :
    (∀ z θ : ℝ,
        (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → Work.Spaces.pz G z θ = 0) ∧
      (∀ z θ : ℝ,
        (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → Work.Spaces.pth G z θ = 0) := by
  have hzc : ∀ z ∉ Set.Icc a b, ∀ᶠ y in 𝓝 z, y ∉ Set.Icc a b := fun z hz =>
    (isClosed_Icc.isOpen_compl).mem_nhds hz
  have htc : ∀ θ ∉ Set.Icc δ (Real.pi / 2 - δ), ∀ᶠ x in 𝓝 θ,
      x ∉ Set.Icc δ (Real.pi / 2 - δ) := fun θ hθ => (isClosed_Icc.isOpen_compl).mem_nhds hθ
  constructor
  · intro z θ h
    rw [Work.Spaces.pz]
    rcases h with hz | hθ
    · have hev : (fun y : ℝ => G y θ) =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
        hzc z hz |>.mono fun y hy => hG y θ (Or.inl hy)
      rw [hev.deriv_eq, deriv_const]
    · have hzero : (fun y : ℝ => G y θ) = fun _ => (0 : ℝ) :=
        funext fun y => hG y θ (Or.inr hθ)
      rw [hzero, deriv_const]
  · intro z θ h
    rw [Work.Spaces.pth]
    rcases h with hz | hθ
    · have hzero : (fun x : ℝ => G z x) = fun _ => (0 : ℝ) :=
        funext fun x => hG z x (Or.inl hz)
      rw [hzero, deriv_const]
    · have hev : (fun x : ℝ => G z x) =ᶠ[𝓝 θ] fun _ => (0 : ℝ) :=
        htc θ hθ |>.mono fun x hx => hG z x (Or.inr hx)
      rw [hev.deriv_eq, deriv_const]

/-- If `G` vanishes off the box `[a,b] × [δ,π/2-δ]`, then so do all the iterated operators
`DzIter j G`, `DthIter i G` and the mixed derivatives `mixed j i G`. -/
theorem iter_eq_zero_of_vanish {a b δ : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : ∀ z θ : ℝ,
      (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → G z θ = 0) :
    (∀ j : ℕ, ∀ z θ : ℝ,
        (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → Work.Spaces.DzIter j G z θ = 0) ∧
      (∀ i : ℕ, ∀ z θ : ℝ,
        (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → Work.Spaces.DthIter i G z θ = 0) ∧
      (∀ j i : ℕ, ∀ z θ : ℝ,
        (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) →
          Work.Spaces.mixed j i G z θ = 0) := by
  have hDz : ∀ (H : ℝ → ℝ → ℝ),
      (∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → H z θ = 0) →
      ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) →
        Work.Spaces.Dz H z θ = 0 := by
    intro H hH z θ h
    rw [Work.Spaces.Dz, (pz_pth_eq_zero_of_vanish hH).1 z θ h]
    ring
  have hDth : ∀ (H : ℝ → ℝ → ℝ),
      (∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → H z θ = 0) →
      ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) →
        Work.Spaces.Dth H z θ = 0 := by
    intro H hH z θ h
    rw [Work.Spaces.Dth, (pz_pth_eq_zero_of_vanish hH).2 z θ h]
    ring
  have hDzIter : ∀ (H : ℝ → ℝ → ℝ),
      (∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → H z θ = 0) →
      ∀ j : ℕ, ∀ z θ : ℝ,
        (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) →
          Work.Spaces.DzIter j H z θ = 0 := by
    intro H hH j
    induction j with
    | zero => exact hH
    | succ j ih => rw [Work.Spaces.DzIter_succ]; exact hDz (Work.Spaces.DzIter j H) ih
  have hDthIter : ∀ (H : ℝ → ℝ → ℝ),
      (∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → H z θ = 0) →
      ∀ i : ℕ, ∀ z θ : ℝ,
        (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) →
          Work.Spaces.DthIter i H z θ = 0 := by
    intro H hH i
    induction i with
    | zero => exact hH
    | succ i ih => rw [Work.Spaces.DthIter_succ]; exact hDth (Work.Spaces.DthIter i H) ih
  refine ⟨hDzIter G hG, hDthIter G hG, fun j i z θ h => ?_⟩
  rw [Work.Spaces.mixed]
  exact hDzIter (Work.Spaces.DthIter i G) (hDthIter G hG i) j z θ h

/-- If `G` vanishes off the box `[a,b] × [δ,π/2-δ]` and the same holds for `pz G` and `pth G`,
then `adjZ G` and `adjTh G` vanish off `s ×ˢ t` as well. -/
theorem adj_eq_zero_off {G : ℝ → ℝ → ℝ} {s t : Set ℝ}
    (hG : ∀ z θ : ℝ, (z ∉ s ∨ θ ∉ t) → G z θ = 0)
    (hpz : ∀ z θ : ℝ, (z ∉ s ∨ θ ∉ t) → Work.Spaces.pz G z θ = 0)
    (hpth : ∀ z θ : ℝ, (z ∉ s ∨ θ ∉ t) → Work.Spaces.pth G z θ = 0) :
    (∀ z θ : ℝ, (z ∉ s ∨ θ ∉ t) → adjZ G z θ = 0) ∧
      (∀ z θ : ℝ, (z ∉ s ∨ θ ∉ t) → adjTh G z θ = 0) := by
  constructor
  · intro z θ h
    rw [adjZ, Work.Spaces.Dz, hG z θ h, hpz z θ h]
    ring
  · intro z θ h
    rw [adjTh, Work.Spaces.Dth, hG z θ h, hpth z θ h]
    ring

/-- The `n`-fold adjoint iterates of a function vanishing off the box also vanish off the box. -/
theorem adjZIter_eq_zero_off {G : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hG : ∀ z θ : ℝ,
      (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → G z θ = 0) (n : ℕ) :
    ∀ z θ : ℝ,
      (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → adjZIter n G z θ = 0 := by
  induction n with
  | zero => exact hG
  | succ n ih =>
    rw [adjZIter_succ]
    exact (adj_eq_zero_off ih (pz_pth_eq_zero_of_vanish ih).1
      (pz_pth_eq_zero_of_vanish ih).2).1

/-- The `n`-fold angular adjoint iterates of a function vanishing off the box also vanish off
the box. -/
theorem adjThIter_eq_zero_off {G : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hG : ∀ z θ : ℝ,
      (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → G z θ = 0) (n : ℕ) :
    ∀ z θ : ℝ,
      (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (Real.pi / 2 - δ)) → adjThIter n G z θ = 0 := by
  induction n with
  | zero => exact hG
  | succ n ih =>
    rw [adjThIter_succ]
    exact (adj_eq_zero_off ih (pz_pth_eq_zero_of_vanish ih).1
      (pz_pth_eq_zero_of_vanish ih).2).2

end Work.FTS.GalFields.Tail
