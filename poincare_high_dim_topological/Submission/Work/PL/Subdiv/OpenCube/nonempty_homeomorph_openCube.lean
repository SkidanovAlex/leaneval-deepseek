import Mathlib
import Submission.Work.PL.Subdiv.Defs

/-!
# The open cube `(-r, r)^n` is homeomorphic to `ℝⁿ`

Area A2 of the lead blueprint.  This file proves

`Work.PL.Subdiv.OpenCube.nonempty_homeomorph_openCube`:
for `0 < r` the sup-norm open cube `PL.openCube r = {x : PL.E n | ∀ i, |x i| < r}` is
homeomorphic to `PL.E n = ℝⁿ`.

The homeomorphism is built explicitly.  In coordinates it is the product of the classical
homeomorphisms `(-r, r) ≃ₜ ℝ`, `x ↦ tan (π x / (2 r))`, whose inverse is `y ↦ arctan y · 2r/π`;
the `π`'s are immaterial, all that is used is that the scaling factor is positive.

Concretely:
* `openBoxHomeomorph` is the homeomorphism `{f : Fin n → ℝ | ∀ i, |f i| < r} ≃ₜ ℝⁿ` given
  coordinatewise by `tan (π / (2 r) · ·)`.
* `PiLp.homeomorph 2 _` identifies `PL.E n` with `Fin n → ℝ`, and carries the open cube exactly
  onto the open box above; `Homeomorph.subtype` restricts it to the two subsets.
-/

open Set

namespace Work.PL.Subdiv.OpenCube

noncomputable section

/-- The homeomorphism `(-r, r)ⁿ ≃ₜ ℝⁿ`, in coordinates `f ↦ fun i ↦ tan (f i * π/(2r))`. -/
def openBoxHomeomorph (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ↥({f : Fin n → ℝ | ∀ i, |f i| < r}) ≃ₜ (Fin n → ℝ) := by
  let c : ℝ := Real.pi / (2 * r)
  let d : ℝ := 2 * r / Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hcd : c * d = 1 := by dsimp [c, d]; field_simp
  have hdc : d * c = 1 := by dsimp [c, d]; field_simp
  -- `t ∈ (-r, r)` scaled by `c` lies in `(-π/2, π/2)`, the domain of injectivity of `tan`.
  have hbound : ∀ t : ℝ, |t| < r → -(Real.pi / 2) < t * c ∧ t * c < Real.pi / 2 := by
    intro t ht
    have ht' : -r < t ∧ t < r := abs_lt.mp ht
    constructor
    · have h1 : -r * c < t * c := mul_lt_mul_of_pos_right ht'.1 hc
      have h2 : -r * c = -(Real.pi / 2) := by dsimp [c]; field_simp
      rwa [h2] at h1
    · have h1 : t * c < r * c := mul_lt_mul_of_pos_right ht'.2 hc
      have h2 : r * c = Real.pi / 2 := by dsimp [c]; field_simp
      rwa [h2] at h1
  let toFun : ↥({f : Fin n → ℝ | ∀ i, |f i| < r}) → (Fin n → ℝ) := fun f i => Real.tan (f.1 i * c)
  have toFun_cont : Continuous toFun := by
    rw [continuous_pi_iff]
    intro i
    rw [continuous_iff_continuousAt]
    intro x
    have hinner : Continuous (fun f : ↥({f : Fin n → ℝ | ∀ i, |f i| < r}) => f.1 i * c) :=
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
    have hcos : Real.cos ((fun f : ↥({f : Fin n → ℝ | ∀ i, |f i| < r}) => f.1 i * c) x) ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo (hbound (x.1 i) (x.2 i))).ne'
    exact ContinuousAt.comp (f := fun f : ↥({f : Fin n → ℝ | ∀ i, |f i| < r}) => f.1 i * c)
      (Real.continuousAt_tan.mpr hcos) hinner.continuousAt
  let invFun' : (Fin n → ℝ) → (Fin n → ℝ) := fun g i => Real.arctan (g i) * d
  have invFun'_mem : ∀ g, ∀ i, |invFun' g i| < r := by
    intro g i
    show |Real.arctan (g i) * d| < r
    rw [abs_mul, abs_of_pos hd]
    have hlt : |Real.arctan (g i)| < Real.pi / 2 :=
      abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    have hm := mul_lt_mul_of_pos_right hlt hd
    have h2 : Real.pi / 2 * d = r := by dsimp [d]; field_simp
    rwa [h2] at hm
  have invFun'_cont : Continuous invFun' := by
    rw [continuous_pi_iff]
    intro i
    exact (Real.continuous_arctan.comp (continuous_apply i)).mul continuous_const
  let invFun : (Fin n → ℝ) → ↥({f : Fin n → ℝ | ∀ i, |f i| < r}) :=
    fun g => ⟨invFun' g, invFun'_mem g⟩
  have invFun_cont : Continuous invFun := invFun'_cont.subtype_mk invFun'_mem
  have left_inv : Function.LeftInverse invFun toFun := by
    intro f
    apply Subtype.ext
    show invFun' (toFun f) = f.1
    funext i
    show Real.arctan (Real.tan (f.1 i * c)) * d = f.1 i
    obtain ⟨hb1, hb2⟩ := hbound (f.1 i) (f.2 i)
    rw [Real.arctan_tan hb1 hb2, mul_assoc, hcd, mul_one]
  have right_inv : Function.RightInverse invFun toFun := by
    intro g
    funext i
    show Real.tan (Real.arctan (g i) * d * c) = g i
    rw [mul_assoc, hdc, mul_one, Real.tan_arctan]
  exact Homeomorph.mk
    { toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv }
    toFun_cont invFun_cont

/-- The open cube `(-r, r)^n` in `PL.E n = ℝⁿ` is homeomorphic to `ℝⁿ`. -/
theorem nonempty_homeomorph_openCube (n : ℕ) (r : ℝ) (hr : 0 < r) :
    Nonempty ((PL.openCube (n := n) r) ≃ₜ PL.E n) := by
  refine ⟨(Homeomorph.subtype (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) (fun x => Iff.rfl)).trans
    ((openBoxHomeomorph n r hr).trans (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm)⟩

end

end Work.PL.Subdiv.OpenCube
