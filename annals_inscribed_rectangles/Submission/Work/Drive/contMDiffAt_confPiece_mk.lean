import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.chartedSpaceChangeModel
import Submission.Work.Drive.lensToProj_confTorus
import Submission.Work.Drive.stripConfigInterface
import Submission.Work.Drive.cappingSpace_homeomorph_prod
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff
import Submission.Work.Drive.chartedStructure_contMDiffWithinAt
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-!
## A local square root of a unit complex number near `1`

The configuration piece of the capping space reads a point of the configuration solid torus
`D² × S¹` by a *square root* of its `S¹`-coordinate: `lensToProj ⟦inr (d, η)⟧` is the
projectivisation of `confProjVecOf u d` for any `u` with `u ^ 2 = circleOf η`
(`Work.Drive.lensToProj_confTorus`).  No continuous choice of `u` exists globally, but near `1`
the elementary formula

> `circSqrt w = (w + 1) / ‖w + 1‖`

is a smooth square root of `w` on the unit circle (`(w+1) / ‖w+1‖ = e^{iθ/2}` when `w = e^{iθ}`
and `w ≠ -1`), and it is smooth at `1` because `w ↦ ‖w+1‖` is smooth there.  This is the tool
that turns the smoothness of the circle-valued map `x ↦ circleOf η x` into a smooth halving of it.
-/

/-- The unit-normalised half-angle formula: for `w` on the unit circle with `w ≠ -1` this is the
square root of `w` in the open right half plane. -/
def circSqrt (w : ℂ) : ℂ := (w + 1) / ((‖w + 1‖ : ℝ) : ℂ)

lemma circSqrt_eq (w : ℂ) :
    circSqrt w = (w + 1) * (((1 : ℝ) / ‖w + 1‖ : ℝ) : ℂ) := by
  rw [circSqrt, div_eq_mul_inv, one_div, Complex.ofReal_inv]

/-- `circSqrt` is `C^∞` at `1` (the only point where it is needed). -/
lemma contDiffAt_circSqrt_one : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) circSqrt 1 := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w + 1) 1 :=
    contDiffAt_id.add contDiffAt_const
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => ‖w + 1‖) 1 :=
    ContDiffAt.norm ℂ h1 (by norm_num)
  have h2i : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => (1 : ℝ) / ‖w + 1‖) 1 :=
    (contDiffAt_const : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℂ => (1 : ℝ)) 1).div h2 (by norm_num)
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => (((1 : ℝ) / ‖w + 1‖ : ℝ) : ℂ)) 1 :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp 1 h2i
  rw [show circSqrt = (fun w : ℂ => (w + 1) * (((1 : ℝ) / ‖w + 1‖ : ℝ) : ℂ))
        from funext circSqrt_eq]
  exact h1.mul h3

/-- `circSqrt w` is a unit complex number whenever `w + 1 ≠ 0`. -/
lemma norm_circSqrt {w : ℂ} (h : w + 1 ≠ 0) : ‖circSqrt w‖ = 1 := by
  rw [circSqrt, norm_div, Complex.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr h)]

/-- **`circSqrt` squares back to `w` on the unit circle** (away from `w = -1`). -/
lemma circSqrt_sq {w : ℂ} (hw : ‖w‖ = 1) (h : w + 1 ≠ 0) : circSqrt w ^ 2 = w := by
  have hww : w * star w = 1 := by
    have hc := Complex.mul_conj w
    rw [starRingEnd_apply, Complex.normSq_eq_norm_sq, hw] at hc
    norm_num at hc
    exact hc
  have hsw1 : star w + 1 ≠ 0 := by
    intro hc
    exact h (by simpa using congrArg star hc)
  have hnorm : ((‖w + 1‖ ^ 2 : ℝ) : ℂ) = (w + 1) * star (w + 1) := by
    rw [show ‖w + 1‖ ^ 2 = Complex.normSq (w + 1) from (Complex.normSq_eq_norm_sq _).symm,
      ← Complex.mul_conj (w + 1), starRingEnd_apply]
  have hR2 : (((‖w + 1‖ : ℝ) : ℂ)) ^ 2 = ((‖w + 1‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [circSqrt, div_pow, hR2, hnorm, star_add, star_one]
  rw [div_eq_iff (by exact mul_ne_zero h hsw1)]
  have key : (w + 1) = w * (star w + 1) := by rw [mul_add, mul_one, hww]; ring
  calc (w + 1) ^ 2 = (w + 1) * (w * (star w + 1)) := by rw [key]; ring
    _ = w * ((w + 1) * (star w + 1)) := by ring

end

open scoped Manifold ContDiff Topology

theorem contMDiffAt_confPiece_mk {k : ℕ}
    (g : EuclideanSpace ℝ (Fin k) → ℝ × ℂ × UnitAddCircle)
    (x₀ : EuclideanSpace ℝ (Fin k))
    (hg1 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (g x).1) x₀)
    (hg2 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (g x).2.1) x₀)
    (hg3 : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => circleOf ((g x).2.2)) x₀)
    (h1 : ∀ x, 0 < (g x).1) (h2 : ∀ x, ‖(g x).2.1‖ ≤ 1) :
    letI := cappingCharted
    ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (Quotient.mk'' (Sum.inl (⟨g x, h1 x, h2 x⟩ : ConfigPiece) : ConfigPiece ⊕ CapPiece) : CappingSpace))
      x₀ := by
  letI := cappingCharted
  -- the smooth circle-valued map and the normalised chart `w`
  set c : EuclideanSpace ℝ (Fin k) → ℂ := fun x => circleOf ((g x).2.2) with hcdef
  have hcs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) c x₀ := hg3
  have hcn : ∀ x, ‖c x‖ = 1 := fun x => norm_circleOf _
  set z : ℂ := c x₀ with hzdef
  have hzn : ‖z‖ = 1 := hcn x₀
  have hz0 : z ≠ 0 := by
    intro hzx
    rw [hzx] at hzn
    norm_num at hzn
  -- a square root of the value at the base point
  set u₀ : ℂ := Complex.exp (Complex.log z / 2) with hu₀def
  have hexp2 : Complex.exp (Complex.log z / 2) * Complex.exp (Complex.log z / 2)
      = Complex.exp (Complex.log z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hu₀sq : u₀ ^ 2 = z := by
    rw [hu₀def, pow_two, hexp2, Complex.exp_log hz0]
  have hu₀n : ‖u₀‖ = 1 := by
    have h2' : ‖u₀‖ ^ 2 = 1 := by rw [← norm_pow u₀ 2, hu₀sq, hzn]
    rw [← Real.sqrt_sq (norm_nonneg u₀), h2', Real.sqrt_one]
  have hzz : z * star z = 1 := by
    have hc := Complex.mul_conj z
    rw [starRingEnd_apply, Complex.normSq_eq_norm_sq, hzn] at hc
    norm_num at hc
    exact hc
  -- the normalised circle coordinate
  set w : EuclideanSpace ℝ (Fin k) → ℂ := fun x => c x * star z with hwdef
  have hwc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w x₀ :=
    hcs.contDiffAt.mul (contDiffAt_const : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : EuclideanSpace ℝ (Fin k) => star z) x₀)
  have hws : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) w x₀ :=
    contMDiffAt_iff_contDiffAt.mpr hwc
  have hwn : ∀ x, ‖w x‖ = 1 := by
    intro x
    show ‖c x * star z‖ = 1
    rw [norm_mul, hcn x, norm_star, hzn, one_mul]
  have hw1 : w x₀ = 1 := by
    show c x₀ * star z = 1
    rw [show c x₀ = z from hzdef.symm]
    exact hzz
  -- the halving
  set u : EuclideanSpace ℝ (Fin k) → ℂ :=
    fun x => if w x + 1 = 0 then u₀ else u₀ * circSqrt (w x) with hudef
  have hwnear : ∀ᶠ x in 𝓝 x₀, w x + 1 ≠ 0 := by
    have hca : ContinuousAt (fun x => w x + 1) x₀ :=
      hws.continuousAt.add continuousAt_const
    refine hca.eventually_ne ?_
    rw [hw1]
    norm_num
  have hu_eq_near : u =ᶠ[𝓝 x₀] fun x => u₀ * circSqrt (w x) := by
    filter_upwards [hwnear] with x hx
    show (if w x + 1 = 0 then u₀ else u₀ * circSqrt (w x)) = u₀ * circSqrt (w x)
    rw [if_neg hx]
  have hun : ∀ x, ‖u x‖ = 1 := by
    intro x
    by_cases hx : w x + 1 = 0
    · show ‖(if w x + 1 = 0 then u₀ else u₀ * circSqrt (w x))‖ = 1
      rw [if_pos hx]
      exact hu₀n
    · show ‖(if w x + 1 = 0 then u₀ else u₀ * circSqrt (w x))‖ = 1
      rw [if_neg hx, norm_mul, hu₀n, norm_circSqrt hx, one_mul]
  have hu_sq_near : ∀ᶠ x in 𝓝 x₀, u x ^ 2 = c x := by
    filter_upwards [hwnear] with x hx
    show (if w x + 1 = 0 then u₀ else u₀ * circSqrt (w x)) ^ 2 = c x
    rw [if_neg hx, mul_pow, hu₀sq, circSqrt_sq (hwn x) hx]
    show z * (c x * star z) = c x
    rw [show z * (c x * star z) = c x * (z * star z) by ring, hzz, mul_one]
  have hus : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) u x₀ := by
    have hc1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) circSqrt (w x₀) := by
      rw [hw1]
      exact contDiffAt_circSqrt_one
    have hsq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => circSqrt (w x)) x₀ :=
      ContDiffAt.comp (g := circSqrt) (f := w) x₀ hc1 hwc
    have hmul : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => u₀ * circSqrt (w x)) x₀ :=
      (contDiffAt_const : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : EuclideanSpace ℝ (Fin k) => u₀) x₀).mul hsq
    exact (contMDiffAt_iff_contDiffAt.mpr hmul).congr_of_eventuallyEq hu_eq_near
  -- the configuration-piece smoothness lemma, applied to the halving `u`
  refine (contMDiffAt_cappingSpace_configPiece (k := k) (r := fun x => (g x).1)
    (d := fun x => (g x).2.1) (u := u) (x₀ := x₀) h1 h2 hun hg1 hg2 hus).congr_of_eventuallyEq ?_
  filter_upwards [hu_sq_near] with x hx
  have hkey : (g x).2.2 =
      circOf (u x ^ 2) (by rw [norm_pow, hun x]; norm_num) := by
    symm
    apply circleOf_injective
    rw [circleOf_circOf, hx]
  have hpiece : (⟨g x, h1 x, h2 x⟩ : ConfigPiece) =
      ⟨((fun y => (g y).1) x, (fun y => (g y).2.1) x,
        circOf (u x ^ 2) (by rw [norm_pow, hun x]; norm_num)), h1 x, h2 x⟩ :=
    Subtype.ext (Prod.ext rfl (Prod.ext rfl hkey))
  rw [hpiece]

end Work.Drive
