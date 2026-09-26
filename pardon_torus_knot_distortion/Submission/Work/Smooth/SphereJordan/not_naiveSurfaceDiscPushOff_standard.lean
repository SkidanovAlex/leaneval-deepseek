import Mathlib
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.injOn_arcPoint
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint
import Submission.Work.CoreTopology.Basic
import Submission.Work.CoreTopology.TorusDichotomyDefs
import Submission.Work.CoreTopology.torusHeight_eq_one_iff
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk
import Submission.Work.CoreTopology.circle_lift_eq_of_extends_disk_of_normCircle
import Submission.Work.CoreTopology.horizVec_torusMap_div_norm
import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.WindingAPI

/-!
# The naive push-off of a surface disc is false: a counterexample

`Work.Smooth.SphereJordan.NaiveSurfaceDiscPushOff P` is `SurfaceDiscPushOff P` without the
innermost clause.  This file proves that it is **false** already for the standard torus of
revolution, by exhibiting an explicit configuration satisfying all its hypotheses for which no
cap exists.

The configuration.  Write `F = standard.carrier` for the standard torus of revolution (major
radius `2`, minor radius `1`), so that

* `torusHeight P = (r - 2)² + z²` (with `r = √(x² + y²)`) vanishes exactly on the *core circle*
  `C : θ ↦ (2 cos θ, 2 sin θ, 0)` of the solid torus bounded by `F`, and equals `1` exactly on
  `F` (`Work.CoreTopology.torusHeight_eq_one_iff`);
* the unit normal projection `horizVec P = x + y·i` is nonvanishing on the solid torus
  `{torusHeight < 1}` and its value on `C` is `2 exp (iθ)`, of winding number `1`.

Take

* `e = flatDiscC`: the flat disc of radius `3` in the plane `{z = 0}`; its boundary circle
  `e (e^{iθ}) = 3 (cos θ, sin θ, 0) = torusMap θ 0` is the outer equator of `F`;
* `γ = innerCurve`: the constant curve at the point `(1, 0, 0) = torusMap 0 π` of the **inner
  equator** of `F` — a legal `ClosedCurve` of `F`, inessential in `F` (it bounds a constant disc
  in the surface), and contained in `e(𝔻)` (indeed `(1,0,0) = e (1/3, 0)`);
* `z₁ = zOne`: the circle of radius `2/3` of the model disc, `z₁ θ = arcPoint (2/3) θ`;
* `h₁ = scaleDiscC`: scaling by `2/3`.

Then `e ∘ z₁` is the circle of radius `2` in `{z = 0}`, i.e. the **core circle `C`** of the solid
torus bounded by `F`, which is not null-homotopic in that solid torus, hence not null-homotopic in
`ℝ³ ∖ F`; no embedded disc with interior disjoint from `F` can span it.

The contradiction is made formal with the vanishing-winding lemma
`Work.CoreTopology.circle_lift_eq_of_extends_disk_of_normCircle`: if `cap` were such a disc, then

* the whole image `cap(𝔻)` is disjoint from `F` (the interior by hypothesis, the boundary because
  `C ∩ F = ∅`), so, `cap(𝔻)` being connected and `torusHeight` being continuous with
  `torusHeight = 1 ↔ · ∈ F`, the image of `cap` lies entirely in one of the two level regions
  `{torusHeight < 1}`, `{1 < torusHeight}`; the boundary value `torusHeight (cap (e^{iθ})) =
  torusHeight (corePoint θ) = 0` selects the inner region, so `torusHeight (cap z) < 1` for every
  `z` (lemma `horizVec_ne_zero_of_cap`);
* hence `W z := horizVec (cap z)` is a nowhere vanishing continuous complex function on the disc,
  whose boundary values are `W (e^{iθ}) = 2 e^{iθ}`; normalising gives a continuous lift
  `θ ↦ θ` of the boundary loop `θ ↦ e^{iθ}` over the disc, so by the vanishing-winding lemma
  `2π = 0` — absurd.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The model disc and the two self-maps used in the construction -/

/-- The closed unit disc contains its centre: `0 ∈ 𝔻`. -/
theorem norm_le_one_of_mem (z : Disc) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  exact h

/-- The point `(1/2, 0)` of the model disc. -/
def halfPoint : Disc :=
  ⟨(1 / 2 : ℂ), by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; norm_num⟩

/-- Multiplication by `2/3` on the model disc (the map `h₁` of the construction). -/
def scaleDisc (z : Disc) : Disc :=
  ⟨(2 / 3 : ℂ) * (z : ℂ), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_mul]
    have hz : ‖(z : ℂ)‖ ≤ 1 := norm_le_one_of_mem z
    have hc : ‖(2 / 3 : ℂ)‖ = 2 / 3 := by norm_num
    rw [hc]; linarith⟩

theorem scaleDisc_coe (z : Disc) : ((scaleDisc z : Disc) : ℂ) = (2 / 3 : ℂ) * (z : ℂ) := rfl

theorem continuous_scaleDisc : Continuous scaleDisc := by
  refine Continuous.subtype_mk ?_ (fun z => (scaleDisc z).2)
  show Continuous fun z : Disc => (2 / 3 : ℂ) * (z : ℂ)
  fun_prop

/-- The map `h₁` of the construction: scaling by `2/3`, as a continuous self-map of the disc. -/
def scaleDiscC : C(Disc, Disc) := ⟨scaleDisc, continuous_scaleDisc⟩

theorem scaleDiscC_apply (z : Disc) : scaleDiscC z = scaleDisc z := rfl

theorem scaleDiscC_injective : Function.Injective scaleDiscC := by
  intro z z' h
  have hcoe : ((scaleDisc z : Disc) : ℂ) = ((scaleDisc z' : Disc) : ℂ) := congrArg Subtype.val h
  rw [scaleDisc_coe, scaleDisc_coe] at hcoe
  exact Subtype.ext (mul_left_cancel₀ (by norm_num : (2 / 3 : ℂ) ≠ 0) hcoe)

theorem scaleDiscC_circlePoint (θ : ℝ) : scaleDiscC (circlePoint θ) = arcPoint (2 / 3) θ := by
  apply Subtype.ext
  rw [scaleDiscC_apply,
    show ((scaleDisc (circlePoint θ) : Disc) : ℂ) = (2 / 3 : ℂ) * (circlePoint θ : ℂ) from rfl,
    arcPoint_coe]
  norm_num

/-- The curve `z₁` of the construction: the circle of radius `2/3` of the model disc. -/
def zOne : ℝ → Disc := fun θ => arcPoint (2 / 3) θ

theorem continuous_arcPoint (r : ℝ) : Continuous (arcPoint r) := by
  refine Continuous.subtype_mk ?_ (fun θ => (arcPoint r θ).2)
  show Continuous fun θ : ℝ => ((max 0 (min r 1) : ℝ) : ℂ) * Complex.exp (θ * Complex.I)
  fun_prop

theorem continuous_zOne : Continuous zOne := continuous_arcPoint (2 / 3)

theorem periodic_zOne : Function.Periodic zOne (2 * Real.pi) := by
  intro t
  show arcPoint (2 / 3) (t + 2 * Real.pi) = arcPoint (2 / 3) t
  have h3 : Work.Smooth.Jordan.circlePoint (t + 2 * Real.pi)
      = Work.Smooth.Jordan.circlePoint t :=
    Work.InnermostDisk.circlePoint_add_two_pi t
  apply Subtype.ext
  rw [arcPoint_eq_radiusPoint (2 / 3) (t + 2 * Real.pi) (by norm_num) (by norm_num),
    arcPoint_eq_radiusPoint (2 / 3) t (by norm_num) (by norm_num), radiusPoint_coe,
    radiusPoint_coe, h3]

theorem injOn_zOne : Set.InjOn zOne (Set.Ico 0 (2 * Real.pi)) :=
  injOn_arcPoint (2 / 3) (by norm_num) (by norm_num) (by norm_num)

theorem norm_zOne (θ : ℝ) : ‖(zOne θ : ℂ)‖ < 1 := by
  have h := norm_arcPoint (2 / 3) θ (by norm_num) (by norm_num)
  simp only [zOne] at h ⊢
  rw [h]; norm_num

/-! ## The flat disc of radius `3` in the plane `{z = 0}` -/

/-- The flat disc of radius `3` in the plane `{z = 0}`, as a function. -/
def flatDiscFun (z : Disc) : R3 := WithLp.toLp 2 (fun i : Fin 3 =>
  if i.val = 0 then 3 * (z : ℂ).re else if i.val = 1 then 3 * (z : ℂ).im else 0)

theorem continuous_flatDiscFun : Continuous flatDiscFun := by
  have h : Continuous (fun z : Disc => fun i : Fin 3 =>
      (if i.val = 0 then 3 * (z : ℂ).re else if i.val = 1 then 3 * (z : ℂ).im else 0 : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

/-- The flat disc of radius `3` in the plane `{z = 0}`, as a continuous map (the disc `e`). -/
def flatDiscC : C(Disc, R3) := ⟨flatDiscFun, continuous_flatDiscFun⟩

theorem flatDiscC_injective : Function.Injective flatDiscC := by
  intro z z' h
  have h0 : 3 * (z : ℂ).re = 3 * (z' : ℂ).re := by
    show (flatDiscC z).ofLp 0 = (flatDiscC z').ofLp 0
    rw [h]
  have h1 : 3 * (z : ℂ).im = 3 * (z' : ℂ).im := by
    show (flatDiscC z).ofLp 1 = (flatDiscC z').ofLp 1
    rw [h]
  apply Subtype.ext
  apply Complex.ext <;> linarith

/-- The boundary circle of the flat disc of radius `3` is the outer equator of the standard
torus. -/
theorem flatDiscC_circlePoint (θ : ℝ) : flatDiscC (circlePoint θ) = Work.Core.torusMap θ 0 := by
  show WithLp.toLp 2 (fun i : Fin 3 => if i.val = 0 then 3 * (circlePoint θ : ℂ).re
        else if i.val = 1 then 3 * (circlePoint θ : ℂ).im else 0) = Work.Core.torusMap θ 0
  show _ = WithLp.toLp 2 (fun i : Fin 3 => if i.val = 0 then (2 + Real.cos 0) * Real.cos θ
        else if i.val = 1 then (2 + Real.cos 0) * Real.sin θ else Real.sin 0)
  congr 1
  funext i
  fin_cases i <;>
    simp [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;> norm_num

/-- The image of the point `(1/2, 0)` under the flat disc is the inner equator point
`(1, 0, 0) = torusMap 0 π`. -/
theorem flatDiscC_scaleDisc_halfPoint :
    flatDiscC (scaleDiscC halfPoint) = Work.Core.torusMap 0 Real.pi := by
  show WithLp.toLp 2 (fun i : Fin 3 => if i.val = 0 then 3 * ((scaleDiscC halfPoint : Disc) : ℂ).re
        else if i.val = 1 then 3 * ((scaleDiscC halfPoint : Disc) : ℂ).im else 0)
      = Work.Core.torusMap 0 Real.pi
  show _ = WithLp.toLp 2 (fun i : Fin 3 => if i.val = 0 then (2 + Real.cos Real.pi) * Real.cos 0
        else if i.val = 1 then (2 + Real.cos Real.pi) * Real.sin 0 else Real.sin Real.pi)
  congr 1
  funext i
  fin_cases i <;>
    simp [scaleDiscC_apply, scaleDisc_coe, halfPoint] <;>
    norm_num [Complex.ext_iff, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-! ## The core circle of the solid torus -/

/-- The point `(2 cos θ, 2 sin θ, 0)` of `ℝ³`: the core circle of the solid torus bounded by the
standard torus. -/
def corePoint (θ : ℝ) : R3 := WithLp.toLp 2 (fun i : Fin 3 =>
  if i.val = 0 then 2 * Real.cos θ else if i.val = 1 then 2 * Real.sin θ else 0)

@[simp] theorem corePoint_zero (θ : ℝ) : (corePoint θ) 0 = 2 * Real.cos θ := by
  simp [corePoint]
@[simp] theorem corePoint_one (θ : ℝ) : (corePoint θ) 1 = 2 * Real.sin θ := by
  simp [corePoint]
@[simp] theorem corePoint_two (θ : ℝ) : (corePoint θ) 2 = 0 := by
  simp [corePoint]

/-- The flat disc carries the circle of radius `2/3` of the model disc onto the core circle. -/
theorem flatDiscC_arcPoint (θ : ℝ) : flatDiscC (arcPoint (2 / 3) θ) = corePoint θ := by
  show WithLp.toLp 2 (fun i : Fin 3 => if i.val = 0 then 3 * ((arcPoint (2 / 3) θ : Disc) : ℂ).re
        else if i.val = 1 then 3 * ((arcPoint (2 / 3) θ : Disc) : ℂ).im else 0) = corePoint θ
  show _ = WithLp.toLp 2 (fun i : Fin 3 => if i.val = 0 then 2 * Real.cos θ
        else if i.val = 1 then 2 * Real.sin θ else 0)
  congr 1
  funext i
  fin_cases i <;>
    simp [arcPoint_coe, Work.Smooth.Jordan.circlePoint_coe, Complex.exp_ofReal_mul_I,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;> norm_num <;> ring

/-- The horizontal radius of a point of the core circle is `2`. -/
theorem horizRadius_corePoint (θ : ℝ) : Work.CoreTopology.horizRadius (corePoint θ) = 2 := by
  rw [Work.CoreTopology.horizRadius, Work.CoreTopology.horizRadiusSq, corePoint_zero,
    corePoint_one]
  rw [show (2 * Real.cos θ) ^ 2 + (2 * Real.sin θ) ^ 2 = 4 from by
    nlinarith [Real.sin_sq_add_cos_sq θ]]
  norm_num

/-- The height function vanishes on the core circle. -/
theorem torusHeight_corePoint (θ : ℝ) : Work.CoreTopology.torusHeight (corePoint θ) = 0 := by
  rw [Work.CoreTopology.torusHeight_apply, horizRadius_corePoint, corePoint_two]
  norm_num

/-- The horizontal projection of a point of the core circle is `2 e^{iθ}`. -/
theorem horizVec_corePoint (θ : ℝ) :
    Work.CoreTopology.horizVec (corePoint θ) = 2 * Complex.exp (θ * Complex.I) := by
  apply Complex.ext
  · rw [Work.CoreTopology.horizVec_re]
    simp [corePoint, Complex.exp_ofReal_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  · rw [Work.CoreTopology.horizVec_im]
    simp [corePoint, Complex.exp_ofReal_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The point `e ∘ z₁` of the construction is off the standard torus. -/
theorem flatDiscC_zOne_notMem (θ : ℝ) :
    flatDiscC (zOne θ) ∉ Work.CoreTopology.standard.carrier := by
  intro hmem
  have h1 := Work.CoreTopology.torusHeight_eq_one_of_mem_carrier hmem
  rw [show flatDiscC (zOne θ) = corePoint θ from flatDiscC_arcPoint θ,
    torusHeight_corePoint] at h1
  norm_num at h1

/-! ## The curve `γ`: the constant curve at the inner equator point -/

/-- The inner equator point `(1, 0, 0) = torusMap 0 π` of the standard torus. -/
def innerEquatorPoint : R3 := Work.Core.torusMap 0 Real.pi

theorem innerEquatorPoint_mem : innerEquatorPoint ∈ Work.CoreTopology.standard.carrier :=
  Work.CoreTopology.ParamTorus.psi_mem_carrier Work.CoreTopology.standard 0 Real.pi

/-- The constant closed curve of the standard torus at the inner equator point. -/
def innerCurve : Work.CoreTopology.ClosedCurve Work.CoreTopology.standard :=
  Work.InnermostDisk.constCurve Work.CoreTopology.standard innerEquatorPoint innerEquatorPoint_mem

theorem innerCurve_range : Set.range innerCurve.γ ⊆ Set.range flatDiscC := by
  rintro p ⟨t, rfl⟩
  exact ⟨scaleDiscC halfPoint, by
    rw [flatDiscC_scaleDisc_halfPoint]
    rfl⟩

theorem innerCurve_bounds :
    Work.InnermostDisk.BoundsDiscInSurface Work.CoreTopology.standard innerCurve :=
  ⟨⟨fun _ => ⟨innerEquatorPoint, innerEquatorPoint_mem⟩, continuous_const⟩, fun _ => rfl⟩

theorem innerCurve_subset_image (θ : ℝ) : innerCurve.γ θ = innerEquatorPoint := rfl

theorem innerCurve_range_image :
    Set.range innerCurve.γ ⊆ flatDiscC '' Set.range scaleDiscC := by
  rintro p ⟨t, rfl⟩
  refine ⟨scaleDiscC halfPoint, ⟨halfPoint, rfl⟩, ?_⟩
  rw [flatDiscC_scaleDisc_halfPoint]
  rfl

theorem scaleDiscC_circlePoint_eq_zOne (θ : ℝ) : scaleDiscC (circlePoint θ) = zOne θ :=
  scaleDiscC_circlePoint θ

/-! ## The horizontal projection of a cap never vanishes -/

/-- **The horizontal projection of a cap whose boundary is the core circle never vanishes.**

Let `cap : 𝔻 → ℝ³` be a continuous map whose boundary values `cap (e^{iθ})` lie strictly inside
the solid torus (`torusHeight < 1`) and whose open disc avoids the torus surface.  Then the
horizontal projection `x + y·i` of `cap z` is nonzero for every `z : 𝔻`.

Indeed `cap`'s image is disjoint from `F` on the open disc (hypothesis) and on the boundary
(where `torusHeight < 1`, while `torusHeight = 1` on `F`), so the continuous image of the
connected disc under `torusHeight ∘ cap` is a connected subset of `ℝ ∖ {1}`; the boundary value
`< 1` selects the region `{torusHeight < 1}`, where `(r - 2)² + z² < 1` forces `r > 1`, i.e. a
nonvanishing horizontal projection. -/
theorem horizVec_ne_zero_of_cap (cap : C(Disc, R3))
    (hHbd : ∀ z : Disc, ‖(z : ℂ)‖ = 1 → Work.CoreTopology.torusHeight (cap z) < 1)
    (hoff : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ Work.CoreTopology.standard.carrier) :
    ∀ z : Disc, Work.CoreTopology.horizVec (cap z) ≠ 0 := by
  have hHcont : Continuous fun z : Disc => Work.CoreTopology.torusHeight (cap z) :=
    Work.CoreTopology.continuous_torusHeight.comp cap.continuous
  have hpre : PreconnectedSpace Disc :=
    isPreconnected_iff_preconnectedSpace.mp (convex_closedBall (0 : ℂ) 1).isPreconnected
  have hAopen : IsOpen {z : Disc | 1 < Work.CoreTopology.torusHeight (cap z)} :=
    isOpen_Ioi.preimage hHcont
  have hBopen : IsOpen {z : Disc | Work.CoreTopology.torusHeight (cap z) < 1} :=
    isOpen_Iio.preimage hHcont
  have hdisj : Disjoint {z : Disc | 1 < Work.CoreTopology.torusHeight (cap z)}
      {z : Disc | Work.CoreTopology.torusHeight (cap z) < 1} := by
    rw [Set.disjoint_left]
    intro z h1
    rw [Set.mem_ofPred_eq] at h1 ⊢
    exact not_lt.mpr (le_of_lt h1)
  have hcover : (Set.univ : Set Disc) ⊆
      {z : Disc | 1 < Work.CoreTopology.torusHeight (cap z)} ∪
        {z : Disc | Work.CoreTopology.torusHeight (cap z) < 1} := by
    intro z _
    rcases lt_trichotomy (Work.CoreTopology.torusHeight (cap z)) 1 with h | h | h
    · exact Or.inr h
    · exfalso
      have hc : cap z ∈ Work.CoreTopology.standard.carrier :=
        (Work.CoreTopology.torusHeight_eq_one_iff (cap z)).mp h
      rcases lt_or_eq_of_le (norm_le_one_of_mem z) with hlt | heq
      · exact hoff z hlt hc
      · exact absurd (h ▸ hHbd z heq) (by norm_num)
    · exact Or.inl h
  rcases IsPreconnected.subset_or_subset hAopen hBopen hdisj hcover
      (isPreconnected_univ : IsPreconnected (Set.univ : Set Disc)) with hA | hB
  · exfalso
    have h1 := hA (Set.mem_univ (circlePoint 0))
    rw [Set.mem_ofPred_eq] at h1
    have h0 : Work.CoreTopology.torusHeight (cap (circlePoint 0)) < 1 := by
      apply hHbd
      rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
    linarith
  · intro z
    have hz : Work.CoreTopology.torusHeight (cap z) < 1 := by
      rcases lt_or_eq_of_le (norm_le_one_of_mem z) with hlt | heq
      · exact hB (Set.mem_univ z)
      · exact hHbd z heq
    intro hzero
    have hr : Work.CoreTopology.horizRadius (cap z) = 0 :=
      (Work.CoreTopology.horizVec_eq_zero_iff (cap z)).mp hzero
    rw [Work.CoreTopology.torusHeight_apply, hr] at hz
    nlinarith [sq_nonneg ((cap z).ofLp 2)]

/-! ## No cap exists -/

/-- **A cap spanning the core circle with interior disjoint from the torus does not exist.**

`cap : 𝔻 → ℝ³` is continuous, its boundary values are the core circle (`cap (e^{iθ}) = 
corePoint θ`, as produced by `e ∘ z₁` for the discs `e = flatDiscC`, `z₁ = zOne`), and its open
disc avoids the torus surface.  This is impossible: the normalised horizontal projection of `cap`
would be a continuous lift `θ ↦ θ` of the loop `θ ↦ e^{iθ}` over the disc, so its winding number
would vanish. -/
theorem not_exists_cap (cap : C(Disc, R3))
    (hcapbd : ∀ θ : ℝ, cap (circlePoint θ) = flatDiscC (zOne θ))
    (hcapp : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → cap z ∉ Work.CoreTopology.standard.carrier) :
    False := by
  -- the height function of the cap is `< 1` on the boundary circle of the disc
  have hHbd : ∀ z : Disc, ‖(z : ℂ)‖ = 1 → Work.CoreTopology.torusHeight (cap z) < 1 := by
    intro z hz
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    have hθ' : (circlePoint θ : Disc) = z := hθ
    rw [← hθ', hcapbd θ, show flatDiscC (zOne θ) = corePoint θ from flatDiscC_arcPoint θ,
      torusHeight_corePoint]
    norm_num
  have hW0 : ∀ z : Disc, Work.CoreTopology.horizVec (cap z) ≠ 0 :=
    horizVec_ne_zero_of_cap cap hHbd (fun z hz => hcapp z hz)
  have hb : ∀ t : ℝ,
      Work.CoreTopology.horizVec (cap (circlePoint t)) = 2 * Complex.exp (t * Complex.I) := by
    intro t
    rw [hcapbd t, show flatDiscC (zOne t) = corePoint t from flatDiscC_arcPoint t,
      horizVec_corePoint t]
  have hlift : ∀ t : ℝ,
      Work.CoreTopology.normCircle (Work.CoreTopology.horizVec (cap (circlePoint t)))
        (hW0 (circlePoint t)) = Circle.exp t := by
    intro t
    apply Subtype.ext
    rw [Work.CoreTopology.normCircle_coe, Circle.coe_exp, hb t, Complex.norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    have h2 : ‖(2 : ℂ)‖ = 2 := by
      rw [Complex.norm_def, Complex.normSq_apply]; norm_num
    rw [h2]
    rw [show (((2 : ℝ)) : ℂ) = 2 from by norm_num]
    exact mul_div_cancel_left₀ _ (by norm_num)
  have hloop := Work.CoreTopology.circle_lift_eq_of_extends_disk_of_normCircle
    (fun z : Disc => Work.CoreTopology.horizVec (cap z))
    (Work.CoreTopology.continuous_horizVec.comp cap.continuous) hW0 (fun t : ℝ => t)
    continuous_id hlift
  have hzero : (2 * Real.pi : ℝ) = 0 := hloop
  linarith [Real.pi_pos]

/-! ## The counterexample -/

/-- **The naive push-off of a surface disc is false for the standard torus.**  The configuration
of the header satisfies every hypothesis of `NaiveSurfaceDiscPushOff standard`, yet no cap exists
by `not_exists_cap`. -/
theorem not_naiveSurfaceDiscPushOff_standard :
    ¬ Work.Smooth.SphereJordan.NaiveSurfaceDiscPushOff Work.CoreTopology.standard := by
  intro h
  obtain ⟨cap, _hcapinj, hcapbd, hcapoff, _hcape⟩ :=
    h flatDiscC flatDiscC_injective
      (fun θ => by
        rw [flatDiscC_circlePoint θ]
        exact Work.CoreTopology.ParamTorus.psi_mem_carrier Work.CoreTopology.standard θ 0)
      innerCurve innerCurve_range innerCurve_bounds
      zOne continuous_zOne periodic_zOne injOn_zOne norm_zOne flatDiscC_zOne_notMem
      scaleDiscC scaleDiscC_injective scaleDiscC_circlePoint_eq_zOne innerCurve_range_image
  exact not_exists_cap cap hcapbd hcapoff

end

end Work.Smooth.SphereJordan
