import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.tau0_Bl_geometry
import Submission.Work.L62.bl_geom_basic
import Submission.Work.L62.l62c_end
import Submission.Work.Horn.basic
import Submission.Work.Repel.pushdown_holo

/-!
# L62 — the lower end of the cylinder: coordinates, the domain `lowOmega`, the horn map `lowHorn`

This file collects the *definitions* used to mirror the upper-end cylinder picture
(`MandelDim.piExp`, `upOmega = {0} ∪ π '' Bu`, `pushdown d.E`) at the **lower** end of the
lift, where the cylinder coordinate is `τ₀ ∘ π` instead of `π`, i.e. the point of the cylinder
is `q w = -e^{-2πi w}` (the lower end `Im w → -∞` corresponds to `q w → 0`).

* `flip w = 1/2 - w` conjugates the lower end of the lift to the upper end (`q = π ∘ flip`);
* `qlow = π ∘ flip` (so `qlow w = τ₀ (π w)`);
* `lowOmega d hd = {0} ∪ q '' Bl`, the lower cylinder neighbourhood of the puncture 0; as a set
  it is exactly `tau0 '' (piExp '' hd.Bl)`, so all the geometry proved in
  `Work.L62.tau0_Bl_geometry` applies verbatim;
* `lowHorn d = pushdown (flip ∘ d.E ∘ flip)`, the pushed-down horn map of `d.E` in the lower
  cylinder coordinate.
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- `flip w = 1/2 - w`: the affine map conjugating the lower end of the lift to the upper end. -/
def flip (w : ℂ) : ℂ := 1 / 2 - w

/-- The lower-end cylinder coordinate `q w = π (flip w) = -e^{-2π i w} = τ₀ (π w)`. -/
def qlow (w : ℂ) : ℂ := MandelDim.piExp (flip w)

/-- The lower-end cylinder neighbourhood of the puncture `0`: `{0} ∪ τ₀ (π '' Bl)`. -/
def lowOmega (d : ParabData g₀ D) (hd : HornData d) : Set ℂ :=
  insert 0 (MandelDim.tau0 '' (MandelDim.piExp '' hd.Bl))

/-- The pushed-down horn map in the lower cylinder coordinate. -/
def lowHorn (d : ParabData g₀ D) : ℂ → ℂ :=
  MandelDim.pushdown (fun x => flip (d.E (flip x)))

/-! ## Elementary identities -/

theorem flip_flip (w : ℂ) : flip (flip w) = w := by
  simp [flip]

theorem flip_sub (a b : ℂ) : flip (a - b) = flip a + b := by
  simp [flip]; ring

theorem flip_add_one (w : ℂ) : flip (w + 1) = flip w - 1 := by
  simp [flip]; ring

/-- `q w = τ₀ (π w)`: the lower-end coordinate is `π` of the flipped point, which is the
inversion `τ₀` of `π`. -/
theorem qlow_eq_tau0 (w : ℂ) : qlow w = MandelDim.tau0 (MandelDim.piExp w) := by
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) * (1 / 2 - w)
      = (Real.pi : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) * (-w) := by ring
  have h1 : MandelDim.piExp (1 / 2 - w) = Complex.exp ((Real.pi : ℂ) * Complex.I) *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (-w)) := by
    rw [MandelDim.piExp, hpi, Complex.exp_add]
  have h2 : Complex.exp ((Real.pi : ℂ) * Complex.I) = -1 := Complex.exp_pi_mul_I
  have h3 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (-w))
      = (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w))⁻¹ := by
    rw [show (2 * (Real.pi : ℂ) * Complex.I) * (-w) = -(2 * (Real.pi : ℂ) * Complex.I * w) by ring]
    exact Complex.exp_neg _
  have h4 : MandelDim.tau0 (MandelDim.piExp w)
      = -(Complex.exp (2 * (Real.pi : ℂ) * Complex.I * w))⁻¹ := by
    rw [MandelDim.tau0, MandelDim.piExp, neg_div, one_div]
  show MandelDim.piExp (flip w) = _
  rw [show flip w = 1 / 2 - w from rfl, h1, h2, h3, h4]
  ring

theorem qlow_ne_zero (w : ℂ) : qlow w ≠ 0 := Complex.exp_ne_zero _

theorem norm_qlow (w : ℂ) : ‖qlow w‖ = Real.exp (2 * Real.pi * w.im) := by
  rw [qlow_eq_tau0]
  exact norm_tau0_piExp w

/-- `q (w + 1) = q w`: `q` is `ℤ`-periodic. -/
theorem qlow_add_one (w : ℂ) : qlow (w + 1) = qlow w := by
  have h : flip (w + 1) = flip w + ((-1 : ℤ) : ℂ) := by simp only [flip]; push_cast; ring
  show MandelDim.piExp (flip (w + 1)) = MandelDim.piExp (flip w)
  rw [h, Work.Horn.MandelDim.piExp_add_intCast]

theorem qlow_add_int (w : ℂ) (k : ℤ) : qlow (w + k) = qlow w := by
  have h : flip (w + k) = flip w + ((-k : ℤ) : ℂ) := by
    simp only [flip]; push_cast; ring
  show MandelDim.piExp (flip (w + k)) = MandelDim.piExp (flip w)
  rw [h, Work.Horn.MandelDim.piExp_add_intCast]

theorem lowOmega_eq_image_qlow (d : ParabData g₀ D) (hd : HornData d) :
    lowOmega d hd = insert 0 (qlow '' hd.Bl) := by
  rw [lowOmega]
  congr 1
  ext ζ
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, hx⟩
    exact ⟨w, hw, by rw [qlow_eq_tau0]; exact hx⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨MandelDim.piExp w, ⟨w, hw, rfl⟩, by rw [qlow_eq_tau0]⟩

theorem mem_lowOmega_iff (d : ParabData g₀ D) (hd : HornData d) {ζ : ℂ} :
    ζ ∈ lowOmega d hd ↔ ζ = 0 ∨ ∃ w ∈ hd.Bl, qlow w = ζ := by
  rw [lowOmega_eq_image_qlow]
  simp [eq_comm]

/-! ## Geometry of `lowOmega` (transported from `tau0_Bl_geometry`) -/

theorem isOpen_lowOmega (d : ParabData g₀ D) (hd : HornData d) : IsOpen (lowOmega d hd) :=
  (tau0_Bl_geometry d hd).1

theorem isBounded_lowOmega (d : ParabData g₀ D) (hd : HornData d) :
    Bornology.IsBounded (lowOmega d hd) :=
  (tau0_Bl_geometry d hd).2.1

theorem isPreconnected_lowOmega (d : ParabData g₀ D) (hd : HornData d) :
    IsPreconnected (lowOmega d hd) :=
  (tau0_Bl_geometry d hd).2.2.1

theorem ball_subset_lowOmega (d : ParabData g₀ D) (hd : HornData d) :
    Metric.ball 0 (Real.exp (-(2 * Real.pi * hd.η))) ⊆ lowOmega d hd :=
  (tau0_Bl_geometry d hd).2.2.2.1

theorem lowOmega_subset_closedBall (d : ParabData g₀ D) (hd : HornData d) :
    lowOmega d hd ⊆ Metric.closedBall 0 (Real.exp (2 * Real.pi * hd.η)) :=
  (tau0_Bl_geometry d hd).2.2.2.2

theorem zero_mem_lowOmega (d : ParabData g₀ D) (hd : HornData d) : (0 : ℂ) ∈ lowOmega d hd :=
  Set.mem_insert 0 _

theorem lowOmega_subset_ball_union (d : ParabData g₀ D) (hd : HornData d) {ζ : ℂ}
    (hζ : ζ ∈ lowOmega d hd) (_hζ0 : ζ ≠ 0) :
    ‖ζ‖ ≤ Real.exp (2 * Real.pi * hd.η) := by
  have h := lowOmega_subset_closedBall d hd hζ
  rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h

end

end Work.L62
