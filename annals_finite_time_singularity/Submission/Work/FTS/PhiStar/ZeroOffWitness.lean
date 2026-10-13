import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Assemble
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.ZeroOffWitness` — the zero-extension normal form of `Φ_*`

`StarCore.zeroOff` demands that `PhiTs α Φs = Φs − Θ` vanish *off* the open quadrant.
This is free: given any honest solution `Φ` of the profile equation one replaces it by

`ZeroOffW α Φ z θ = if (z,θ) ∈ Q0 then Φ z θ else Θ α (F_*)(z,θ)`,

which agrees with `Φ` on the open quadrant (an open set) and equals the singular part `Θ` outside
it.  Since `Θ(z,0) = Θ(z,π/2) = 0` (the factor `sin 2θ`) and `bslOp` is built from `deriv`, which
only sees the germ, the replacement preserves `IsBslSol`, `SmoothOpen` and every bound that is
stated on `Q0` only (`FlatW`, `Ycheck`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Classical

namespace Work.FTS.PhiStar

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The **zero-extension normal form**: equal to `Φ` on the open quadrant, and equal to the
singular part `Θ α (F_*)` off it (in particular on the lines `θ = 0`, `θ = π/2` and the axis
`z = 0`). -/
def ZeroOffW (α : ℝ) (Φ : Fn) : Fn :=
  fun z θ => if (z, θ) ∈ Work.FTS.EllipticEst.Q0 then Φ z θ
    else Work.Construction.Theta α (Work.Construction.Fstar α) z θ

/-- `ZeroOffW α Φ` agrees with `Φ` on the open quadrant. -/
theorem zeroOffW_eqOn (α : ℝ) (Φ : Fn) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → ZeroOffW α Φ z θ = Φ z θ := by
  intro z θ h
  unfold ZeroOffW
  rw [if_pos h]

/-- The singular part vanishes on the two boundary lines. -/
theorem Theta_zero (α : ℝ) (z : ℝ) :
    Work.Construction.Theta α (Work.Construction.Fstar α) z 0 = 0 ∧
      Work.Construction.Theta α (Work.Construction.Fstar α) z (π / 2) = 0 := by
  have h0 : Work.Construction.s2 0 = 0 := by simp [Work.Construction.s2]
  have h1 : Work.Construction.s2 (π / 2) = 0 := by
    simp only [Work.Construction.s2]
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
  constructor
  · simp only [Work.Construction.Theta, h0, mul_zero, zero_mul]
  · simp only [Work.Construction.Theta, h1, mul_zero, zero_mul]

/-- `PhiTs` of the zero-extension agrees with `PhiTs` of `Φ` on the open quadrant. -/
theorem PhiTs_zeroOffW_eqOn (α : ℝ) (Φ : Fn) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Construction.PhiTil α (Work.Construction.Fstar α) (ZeroOffW α Φ) z θ
        = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φ z θ := by
  intro z θ h
  simp only [Work.Construction.PhiTil, zeroOffW_eqOn α Φ z θ h]

/-- **`zeroOff`**: `PhiTs` of the zero-extension vanishes off the open quadrant. -/
theorem PhiTs_zeroOffW_off (α : ℝ) (Φ : Fn) :
    ∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 →
      Work.Construction.PhiTil α (Work.Construction.Fstar α) (ZeroOffW α Φ) z θ = 0 := by
  intro z θ h
  simp only [Work.Construction.PhiTil, ZeroOffW, if_neg h, sub_self]

/-! ## `pthIter` as an iterated one-variable derivative -/

/-- `pthIter k` is the `k`-th derivative of the `θ`-slice. -/
theorem pthIter_eq_iteratedDeriv (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter k f z θ = iteratedDeriv k (fun θ' => f z θ') θ := by
  induction k generalizing θ with
  | zero => simp [Work.Spaces.pthIter]
  | succ k ih =>
    rw [Work.Spaces.pthIter_succ, Work.Spaces.pth]
    have hfun : (fun θ' : ℝ => Work.Spaces.pthIter k f z θ')
        = fun θ' : ℝ => iteratedDeriv k (fun θ'' : ℝ => f z θ'') θ' := by
      funext θ'
      exact ih θ'
    rw [hfun, iteratedDeriv_succ]

/-! ## Locality of `Lzero` and `bslOp` on the open quadrant -/

/-- `Lzero` is local: two functions agreeing on `Q0` have the same `Lzero` at every point of
`Q0`.  (All its terms are built from `deriv`, which is a limit.) -/
theorem Lzero_congr (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0)
    (h : ∀ z' θ' : ℝ, (z', θ') ∈ Work.FTS.EllipticEst.Q0 → f z' θ' = g z' θ') :
    Work.Elliptic.Lzero f z θ = Work.Elliptic.Lzero g z θ := by
  have hU : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (z, θ) :=
    Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzp
  have hzslice : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    have hcont : ContinuousAt (fun z' : ℝ => (z', θ)) z := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds hU] with z' hz'
    exact h z' θ hz'
  have hthslice : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    have hcont : ContinuousAt (fun θ' : ℝ => (z, θ')) θ := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds hU] with θ' hθ'
    exact h z θ' hθ'
  have htan : (fun θ' : ℝ => Real.tan θ' * f z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Real.tan θ' * g z θ') := by
    filter_upwards [hthslice] with θ' hθ'
    rw [hθ']
  have hpth2 : Work.Spaces.pthIter 2 f z θ = Work.Spaces.pthIter 2 g z θ := by
    rw [pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv]
    exact hthslice.iteratedDeriv_eq 2
  have hcross : Work.Spaces.pth (fun z θ => Real.tan θ * f z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * g z θ) z θ := htan.deriv_eq
  have hpt : f z θ = g z θ := h z θ hzp
  simp only [Work.Elliptic.Lzero, hpth2, hcross, hpt]

/-- `bslOp` is local on the open quadrant. -/
theorem bslOp_congr (α : ℝ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0)
    (h : ∀ z' θ' : ℝ, (z', θ') ∈ Work.FTS.EllipticEst.Q0 → f z' θ' = g z' θ') :
    Work.Elliptic.bslOp α f z θ = Work.Elliptic.bslOp α g z θ := by
  have hU : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (z, θ) :=
    Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzp
  have hzslice : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    have hcont : ContinuousAt (fun z' : ℝ => (z', θ)) z := by fun_prop
    filter_upwards [hcont.preimage_mem_nhds hU] with z' hz'
    exact h z' θ hz'
  have hpz2 : Work.Spaces.pzIter 2 f z θ = Work.Spaces.pzIter 2 g z θ := by
    rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
    exact hzslice.iteratedDeriv_eq 2
  have hpz1 : Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
    simp only [Work.Spaces.pz]
    exact hzslice.deriv_eq
  have hL : Work.Elliptic.Lzero f z θ = Work.Elliptic.Lzero g z θ :=
    Lzero_congr f g hzp h
  simp only [Work.Elliptic.bslOp, hpz2, hpz1, hL]

/-! ## Transport of the class properties -/

/-- The zero-extension is `C^∞` on the open quadrant when `Φ` is. -/
theorem smoothOpen_zeroOffW {α : ℝ} {Φ : Fn}
    (h : Work.FTS.EllipticEst.SmoothOpen Φ) :
    Work.FTS.EllipticEst.SmoothOpen (ZeroOffW α Φ) := by
  unfold Work.FTS.EllipticEst.SmoothOpen at h ⊢
  refine h.congr (fun p hp => ?_)
  simp only [Function.uncurry]
  exact zeroOffW_eqOn α Φ p.1 p.2 hp

/-- The zero-extension solves the same profile equation. -/
theorem isBslSol_zeroOffW {α : ℝ} {Φ : Fn}
    (h : Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) Φ) :
    Work.Elliptic.IsBslSol α (Work.Construction.Fstar α) (ZeroOffW α Φ) := by
  obtain ⟨heq, h0, h1, hdec⟩ := h
  have hz0 : (∀ z : ℝ, (z, 0) ∉ Work.FTS.EllipticEst.Q0) := fun z =>
    fun hh => lt_irrefl (0 : ℝ) ((Work.FTS.EllipticEst.mem_Q0).mp hh).2.1
  have hz1 : (∀ z : ℝ, (z, π / 2) ∉ Work.FTS.EllipticEst.Q0) := fun z =>
    fun hh => lt_irrefl (π / 2) ((Work.FTS.EllipticEst.mem_Q0).mp hh).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz θ hθ hθ2
    have hzp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ, hθ2⟩
    rw [bslOp_congr α (ZeroOffW α Φ) Φ hzp (fun z' θ' h' => zeroOffW_eqOn α Φ z' θ' h')]
    exact heq z hz θ hθ hθ2
  · intro z
    unfold ZeroOffW
    rw [if_neg (hz0 z), (Theta_zero α z).1]
  · intro z
    unfold ZeroOffW
    rw [if_neg (hz1 z), (Theta_zero α z).2]
  · intro θ hθ
    rw [Work.Spaces.Iθ] at hθ
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [← hθ0]
      have hconst : (fun z : ℝ => ZeroOffW α Φ z 0) = fun _ => (0 : ℝ) := by
        funext z
        unfold ZeroOffW
        rw [if_neg (hz0 z), (Theta_zero α z).1]
      rw [hconst]
      exact tendsto_const_nhds
    rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
    · rw [hθ1]
      have hconst : (fun z : ℝ => ZeroOffW α Φ z (π / 2)) = fun _ => (0 : ℝ) := by
        funext z
        unfold ZeroOffW
        rw [if_neg (hz1 z), (Theta_zero α z).2]
      rw [hconst]
      exact tendsto_const_nhds
    · have hev : (fun z : ℝ => ZeroOffW α Φ z θ) =ᶠ[atTop] (fun z : ℝ => Φ z θ) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        exact zeroOffW_eqOn α Φ z θ ((Work.FTS.EllipticEst.mem_Q0).mpr ⟨hz, hθ0, hθ1⟩)
      exact (hdec θ ⟨le_of_lt hθ0, le_of_lt hθ1⟩).congr' hev.symm

end Work.FTS.PhiStar
