import Mathlib
import Submission.Work.RatHurewicz.CompressionDefs
import Submission.Work.ThomBordism.TwoSet.ConeDescent

/-!
# The homotopy extension property of the cube pair

`Work.RatHurewicz.hepCube`: the pair `(I^{e+1}, ∂I^{e+1})` has the homotopy extension property:
given `f : I^{e+1} → Z` and a homotopy `h` of `f|∂I^{e+1}` starting at `f|∂I^{e+1}`, the homotopy
extends over the whole cube.

The explicit construction, in the `ℓ∞` coordinates of the cube: put `ρ x := rad x` (`0` at the
centre, `1` on the boundary), `ν x := max 0 (2 ρ x - 1)` (a collar function, `0` on the inner half
of the cube and `1` on the boundary) and `u (x,τ) := τ · ν x`.  On the region `ρ x + u ≤ 1` the value
is `f` of the point at radial parameter `ρ x + u` on the ray from the centre through `x`
(`Work.ThomBordism.TwoSet.bpt`), and on the region `ρ x + u ≥ 1` it is `h` of the boundary point on
that ray, with time parameter `u - (1 - ρ x)`.  The two formulas agree on `ρ x + u = 1` because
`h (·,0) = f`, and the value is `f x` for all `τ` when `ρ x ≤ 1/2` (there `ν = 0`, `u = 0` and the
point at radial parameter `ρ x` is `x`), which makes the formula continuous at the centre.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval
open Work.ThomBordism.TwoSet

namespace Work.RatHurewicz

noncomputable section

variable {e : ℕ}

/-! ## The radial structure of the cube -/

/-- Clamping a real number to `[0,1]`. -/
def clampI (x : ℝ) : unitInterval :=
  ⟨max 0 (min 1 x), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

@[simp] theorem clampI_coe (x : ℝ) : ((clampI x : unitInterval) : ℝ) = max 0 (min 1 x) := rfl

theorem continuous_clampI : Continuous clampI :=
  Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id)) _

theorem clampI_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clampI x = ⟨x, h0, h1⟩ := by
  apply Subtype.ext
  rw [clampI_coe, min_eq_right h1, max_eq_right h0]

theorem clampI_eq_of {x : ℝ} {θ : unitInterval} (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (hθ : (θ : ℝ) = x) : clampI x = θ := by
  apply Subtype.ext
  rw [clampI_coe, hθ, min_eq_right h1, max_eq_right h0]

/-- `rad` as an element of `I`. -/
def radI (hm : 1 ≤ e + 1) (x : ICube (e + 1)) : unitInterval :=
  ⟨rad hm x, rad_nonneg hm x, rad_le_one hm x⟩

@[simp] theorem radI_coe (hm : 1 ≤ e + 1) (x : ICube (e + 1)) :
    ((radI hm x : unitInterval) : ℝ) = rad hm x := rfl

/-- The collar function `ν x = max 0 (2 ρ x - 1)`: `0` on the inner half of the cube, `1` on the
boundary. -/
def nuFun (hm : 1 ≤ e + 1) (x : ICube (e + 1)) : ℝ := max 0 (2 * rad hm x - 1)

theorem nuFun_nonneg (hm : 1 ≤ e + 1) (x : ICube (e + 1)) : 0 ≤ nuFun hm x := le_max_left _ _

theorem nuFun_le_one (hm : 1 ≤ e + 1) (x : ICube (e + 1)) : nuFun hm x ≤ 1 := by
  refine max_le (by norm_num) ?_
  have := rad_le_one hm x
  linarith

theorem nuFun_eq_zero (hm : 1 ≤ e + 1) {x : ICube (e + 1)} (hx : rad hm x ≤ 1 / 2) :
    nuFun hm x = 0 := max_eq_left (by linarith)

theorem continuous_nuFun (hm : 1 ≤ e + 1) : Continuous (nuFun hm) :=
  continuous_const.max ((continuous_const.mul (continuous_rad hm)).sub continuous_const)

/-- The time coordinate `u (x,τ) = τ · ν x`. -/
def uFun (hm : 1 ≤ e + 1) (p : ICube (e + 1) × unitInterval) : ℝ :=
  (p.2 : ℝ) * nuFun hm p.1

theorem uFun_nonneg (hm : 1 ≤ e + 1) (p : ICube (e + 1) × unitInterval) : 0 ≤ uFun hm p :=
  mul_nonneg p.2.2.1 (nuFun_nonneg hm p.1)

theorem uFun_le_one (hm : 1 ≤ e + 1) (p : ICube (e + 1) × unitInterval) : uFun hm p ≤ 1 := by
  have h0 : 0 ≤ nuFun hm p.1 := nuFun_nonneg hm p.1
  have h1 : nuFun hm p.1 ≤ 1 := nuFun_le_one hm p.1
  have h2 : (p.2 : ℝ) ≤ 1 := p.2.2.2
  have h3 : 0 ≤ (p.2 : ℝ) := p.2.2.1
  rw [uFun]
  nlinarith

theorem continuous_uFun (hm : 1 ≤ e + 1) : Continuous (uFun hm) :=
  (continuous_subtype_val.comp continuous_snd).mul
    ((continuous_nuFun hm).comp continuous_fst)

/-- The point at radial parameter `θ` on the ray from the centre through `x`. -/
def rayPt (hm : 1 ≤ e + 1) (x : ICube (e + 1)) (θ : unitInterval) : ICube (e + 1) :=
  fun i => ⟨1 / 2 + (θ : ℝ) * (((bpt hm x) i : ℝ) - 1 / 2), by
    have hb : |(((bpt hm x) i : ℝ) - 1 / 2)| ≤ 1 / 2 := by
      have h1 : (0 : ℝ) ≤ ((bpt hm x) i : ℝ) := ((bpt hm x) i).2.1
      have h2 : ((bpt hm x) i : ℝ) ≤ 1 := ((bpt hm x) i).2.2
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    have hθ : |(θ : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg θ.2.1]
      exact θ.2.2
    have hmul : |(θ : ℝ) * (((bpt hm x) i : ℝ) - 1 / 2)| ≤ 1 / 2 := by
      rw [abs_mul]
      calc |(θ : ℝ)| * |(((bpt hm x) i : ℝ) - 1 / 2)| ≤ 1 * (1 / 2) :=
            mul_le_mul hθ hb (abs_nonneg _) (by norm_num)
        _ = 1 / 2 := by norm_num
    constructor
    · have := (abs_le.mp hmul).1; linarith
    · have := (abs_le.mp hmul).2; linarith⟩

@[simp] theorem rayPt_coe (hm : 1 ≤ e + 1) (x : ICube (e + 1)) (θ : unitInterval)
    (i : Fin (e + 1)) :
    ((rayPt hm x θ i : unitInterval) : ℝ)
      = 1 / 2 + (θ : ℝ) * (((bpt hm x) i : ℝ) - 1 / 2) := rfl

theorem rayPt_congr (hm : 1 ≤ e + 1) {x : ICube (e + 1)} {θ₁ θ₂ : unitInterval} (h : θ₁ = θ₂) :
    rayPt hm x θ₁ = rayPt hm x θ₂ := by rw [h]

theorem rayPt_one (hm : 1 ≤ e + 1) (x : ICube (e + 1)) : rayPt hm x 1 = bpt hm x := by
  funext i
  apply Subtype.ext
  rw [rayPt_coe]
  norm_num

theorem rayPt_radI (hm : 1 ≤ e + 1) (x : ICube (e + 1)) : rayPt hm x (radI hm x) = x := by
  by_cases hx : rad hm x = 0
  · have hx' : x = fun _ : Fin (e + 1) => (half : unitInterval) := eq_cen_of_rad_eq_zero hm hx
    funext i
    apply Subtype.ext
    rw [rayPt_coe, radI_coe, hx]
    have hb : ((bpt hm x) i : ℝ) = 1 / 2 := by
      rw [bpt_coe]
      simp only [bptR, hx, div_zero, add_zero]
    rw [hb]
    have hxi : (x i : ℝ) = 1 / 2 := by rw [hx']; rfl
    rw [hxi]
    ring
  · funext i
    apply Subtype.ext
    rw [rayPt_coe, radI_coe, bpt_coe, bptR]
    have hdiv : rad hm x * (((x i : ℝ) - 1 / 2) / rad hm x) = ((x i : ℝ) - 1 / 2) := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hx
    rw [show (1 : ℝ) / 2 + rad hm x * (1 / 2 + ((x i : ℝ) - 1 / 2) / rad hm x - 1 / 2)
        = 1 / 2 + rad hm x * (((x i : ℝ) - 1 / 2) / rad hm x) by ring, hdiv]
    ring

theorem continuous_rayPt (hm : 1 ≤ e + 1) :
    Continuous fun q : {x : ICube (e + 1) // rad hm x ≠ 0} × unitInterval =>
      rayPt hm q.1.1 q.2 := by
  refine continuous_pi fun i => ?_
  refine Continuous.subtype_mk ?_ _
  have hb : Continuous fun q : {x : ICube (e + 1) // rad hm x ≠ 0} × unitInterval =>
      (((bpt hm q.1.1) i : unitInterval) : ℝ) :=
    continuous_subtype_val.comp
      ((continuous_apply i).comp ((continuous_bpt hm).comp continuous_fst))
  have hθ : Continuous fun q : {x : ICube (e + 1) // rad hm x ≠ 0} × unitInterval =>
      ((q.2 : unitInterval) : ℝ) := continuous_subtype_val.comp continuous_snd
  exact continuous_const.add (hθ.mul (hb.sub continuous_const))

/-- The (total, junk-tolerant at the centre) boundary point of the cube in the direction of `x`. -/
def bdPt (hm : 1 ≤ e + 1) (x : ICube (e + 1)) : ↥(Cube.boundary (Fin (e + 1))) :=
  if h : rad hm x = 0 then ⟨fun _ => 0, ⟨0, Or.inl rfl⟩⟩
  else ⟨bpt hm x, bpt_mem_boundary hm x h⟩

theorem bdPt_eq (hm : 1 ≤ e + 1) {x : ICube (e + 1)} (h : rad hm x ≠ 0) :
    bdPt hm x = ⟨bpt hm x, bpt_mem_boundary hm x h⟩ := dif_neg h

/-! ## The candidate extension and its continuity -/

/-- The "inside" branch of the candidate extension: read `f` at the point at radial parameter
`ρ x + u` on the ray through `x`. -/
def hepIn (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z] (f : C(ICube (e + 1), Z))
    (p : ICube (e + 1) × unitInterval) : Z :=
  f (rayPt hm p.1 (clampI (rad hm p.1 + uFun hm p)))

/-- The "boundary" branch of the candidate extension: read `h` at the boundary point on the ray
through `x`, with time parameter `u - (1 - ρ x)`. -/
def hepOut (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (p : ICube (e + 1) × unitInterval) : Z :=
  h (bdPt hm p.1, clampI (uFun hm p - (1 - rad hm p.1)))

/-- The candidate for the extension: `f` inside the cube, `h` on the boundary, glued along the
level sets of `ρ x + τ ν x`. -/
def hepFun (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (f : C(ICube (e + 1), Z)) (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z)) :
    ICube (e + 1) × unitInterval → Z :=
  fun p => if rad hm p.1 + uFun hm p ≤ 1 then hepIn hm f p else hepOut hm h p

theorem hepFun_of_le (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (f : C(ICube (e + 1), Z)) (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (p : ICube (e + 1) × unitInterval) (hp : rad hm p.1 + uFun hm p ≤ 1) :
    hepFun hm f h p = hepIn hm f p := if_pos hp

theorem hepFun_of_gt (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (f : C(ICube (e + 1), Z)) (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (p : ICube (e + 1) × unitInterval) (hp : ¬ (rad hm p.1 + uFun hm p ≤ 1)) :
    hepFun hm f h p = hepOut hm h p := if_neg hp

theorem hepFun_zero (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (f : C(ICube (e + 1), Z)) (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (x : ICube (e + 1)) : hepFun hm f h (x, 0) = f x := by
  have hu : uFun hm (x, (0 : unitInterval)) = 0 := by
    rw [uFun]
    norm_num
  have hle : rad hm x + uFun hm (x, (0 : unitInterval)) ≤ 1 := by
    rw [hu]
    simpa using rad_le_one hm x
  rw [hepFun_of_le hm f h (x, (0 : unitInterval)) hle]
  rw [hepIn]
  congr 1
  refine Eq.trans (rayPt_congr hm ?_) (rayPt_radI hm x)
  exact clampI_eq_of (by linarith [rad_nonneg hm x, uFun_nonneg hm (x, 0)]) hle
    (by rw [hu, radI_coe]; ring)

theorem hepFun_boundary (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (f : C(ICube (e + 1), Z)) (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (h0 : ∀ x : ↥(Cube.boundary (Fin (e + 1))), h (x, 0) = f x.1)
    (x : ICube (e + 1)) (hx : x ∈ Cube.boundary (Fin (e + 1))) (τ : unitInterval) :
    hepFun hm f h (x, τ) = h (⟨x, hx⟩, τ) := by
  have hρ : rad hm x = 1 := rad_boundary_eq_one hm hx
  have hν : nuFun hm x = 1 := by
    rw [nuFun, hρ]
    norm_num
  have hu : uFun hm (x, τ) = (τ : ℝ) := by
    rw [uFun, hν, mul_one]
  have hx0 : rad hm x ≠ 0 := by rw [hρ]; norm_num
  have hbpt : bpt hm x = x := bpt_eq_self_of_mem_boundary hm hx
  by_cases hτ : τ = 0
  · subst hτ
    have hle : rad hm x + uFun hm (x, (0 : unitInterval)) ≤ 1 := by
      rw [hu, hρ]
      norm_num
    rw [hepFun_of_le hm f h (x, (0 : unitInterval)) hle]
    show f (rayPt hm x (clampI (rad hm x + uFun hm (x, (0 : unitInterval))))) = h (⟨x, hx⟩, 0)
    have hpar : clampI (rad hm x + uFun hm (x, (0 : unitInterval))) = 1 :=
      clampI_eq_of (by linarith [rad_nonneg hm x, uFun_nonneg hm (x, 0)]) hle (by
        rw [hu, hρ]
        norm_num)
    rw [hpar, rayPt_one, hbpt]
    exact (h0 ⟨x, hx⟩).symm
  · have hτpos : 0 < (τ : ℝ) := by
      refine lt_of_le_of_ne τ.2.1 ?_
      intro h
      exact hτ (Subtype.ext h.symm)
    have hgt : ¬ (rad hm x + uFun hm (x, τ) ≤ 1) := by
      rw [hu, hρ]
      intro hle
      linarith
    rw [hepFun_of_gt hm f h (x, τ) hgt]
    show h (bdPt hm x, clampI (uFun hm (x, τ) - (1 - rad hm x))) = h (⟨x, hx⟩, τ)
    have hbd : bdPt hm x = ⟨x, hx⟩ := by
      rw [bdPt_eq hm hx0]
      exact Subtype.ext hbpt
    have hpar : clampI (uFun hm (x, τ) - (1 - rad hm x)) = τ :=
      clampI_eq_of (by rw [hu, hρ]; linarith)
        (by
          have h1 : uFun hm (x, τ) ≤ 1 := uFun_le_one hm (x, τ)
          rw [hu] at h1
          rw [hρ]
          linarith)
        (by rw [hu, hρ]; ring)
    rw [hbd, hpar]

/-- On the seam `ρ x + u = 1` the two branches of the candidate extension agree (both are
`f` of the boundary point on the ray through `x`). -/
theorem hepIn_eq_hepOut_of_seam (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (f : C(ICube (e + 1), Z)) (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (h0 : ∀ x : ↥(Cube.boundary (Fin (e + 1))), h (x, 0) = f x.1)
    {p : ICube (e + 1) × unitInterval} (hρ : (1 : ℝ) / 2 ≤ rad hm p.1)
    (hseam : rad hm p.1 + uFun hm p = 1) :
    hepIn hm f p = hepOut hm h p := by
  have hne : rad hm p.1 ≠ 0 := by
    intro hcon
    rw [hcon] at hρ
    norm_num at hρ
  have h1 : clampI (rad hm p.1 + uFun hm p) = 1 := by
    rw [hseam]
    exact clampI_of_mem (by norm_num) (by norm_num)
  have h2 : uFun hm p - (1 - rad hm p.1) = 0 := by linarith
  have h3 : clampI (uFun hm p - (1 - rad hm p.1)) = 0 := by
    rw [h2]
    exact clampI_of_mem (le_refl (0 : ℝ)) (by norm_num)
  rw [hepIn, hepOut, h1, rayPt_one, h3, bdPt_eq hm hne]
  exact (h0 ⟨bpt hm p.1, bpt_mem_boundary hm p.1 hne⟩).symm

theorem continuous_hepFun (hm : 1 ≤ e + 1) {Z : Type} [TopologicalSpace Z]
    (f : C(ICube (e + 1), Z)) (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (h0 : ∀ x : ↥(Cube.boundary (Fin (e + 1))), h (x, 0) = f x.1) :
    Continuous (hepFun hm f h) := by
  have hA : IsClosed {p : ICube (e + 1) × unitInterval | rad hm p.1 ≤ 1 / 2} :=
    isClosed_le ((continuous_rad hm).comp continuous_fst) continuous_const
  have hB : IsClosed {p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} :=
    isClosed_le continuous_const ((continuous_rad hm).comp continuous_fst)
  have hC : IsClosed {p : ICube (e + 1) × unitInterval | rad hm p.1 + uFun hm p ≤ 1} :=
    isClosed_le (((continuous_rad hm).comp continuous_fst).add (continuous_uFun hm))
      continuous_const
  have hD : IsClosed {p : ICube (e + 1) × unitInterval | (1 : ℝ) ≤ rad hm p.1 + uFun hm p} :=
    isClosed_le continuous_const
      (((continuous_rad hm).comp continuous_fst).add (continuous_uFun hm))
  -- continuity on `{ρ ≤ 1/2}`, where the value is `f x` for every `τ`
  have hcontA : ContinuousOn (hepFun hm f h) {p : ICube (e + 1) × unitInterval |
      rad hm p.1 ≤ 1 / 2} := by
    refine ContinuousOn.congr (f := fun p : ICube (e + 1) × unitInterval => f p.1)
      (f.continuous.comp continuous_fst).continuousOn (fun p hp => ?_)
    have hu : uFun hm p = 0 := by
      rw [uFun, nuFun_eq_zero hm hp, mul_zero]
    have hle : rad hm p.1 + uFun hm p ≤ 1 := by
      rw [hu]
      simpa using rad_le_one hm p.1
    rw [hepFun_of_le hm f h p hle]
    show f (rayPt hm p.1 (clampI (rad hm p.1 + uFun hm p))) = f p.1
    congr 1
    refine Eq.trans (rayPt_congr hm ?_) (rayPt_radI hm p.1)
    exact clampI_eq_of (by linarith [rad_nonneg hm p.1, uFun_nonneg hm p]) hle
      (by rw [hu, radI_coe]; ring)
  -- continuity on `{1/2 ≤ ρ}`
  have hcontB : ContinuousOn (hepFun hm f h) {p : ICube (e + 1) × unitInterval |
      (1 : ℝ) / 2 ≤ rad hm p.1} := by
    have hS1 : ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
        {p | rad hm p.1 + uFun hm p ≤ 1})
        = {p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1 ∧
            rad hm p.1 + uFun hm p ≤ 1} := by
      ext p; exact Iff.rfl
    have hS2 : ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
        {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p})
        = {p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1 ∧
            (1 : ℝ) ≤ rad hm p.1 + uFun hm p} := by
      ext p; exact Iff.rfl
    have hB1 : ContinuousOn (hepFun hm f h)
        ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
          {p | rad hm p.1 + uFun hm p ≤ 1}) := by
      have hne : ∀ q : ↥({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
          {p | rad hm p.1 + uFun hm p ≤ 1}), rad hm q.1.1 ≠ 0 := fun q => by
        have h1 : (1 : ℝ) / 2 ≤ rad hm q.1.1 := q.2.1
        intro h0
        rw [h0] at h1
        norm_num at h1
      have hpair : Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | rad hm p.1 + uFun hm p ≤ 1}) =>
          ((⟨q.1.1, hne q⟩ : {x : ICube (e + 1) // rad hm x ≠ 0}),
            clampI (rad hm q.1.1 + uFun hm q.1)) :=
        Continuous.prodMk
          (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) hne)
          (continuous_clampI.comp
            (((continuous_rad hm).comp (continuous_fst.comp continuous_subtype_val)).add
              ((continuous_uFun hm).comp continuous_subtype_val)))
      have hpt : Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | rad hm p.1 + uFun hm p ≤ 1}) =>
          rayPt hm q.1.1 (clampI (rad hm q.1.1 + uFun hm q.1)) :=
        (continuous_rayPt hm).comp hpair
      have hc : Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | rad hm p.1 + uFun hm p ≤ 1}) =>
          hepIn hm f q.1 := by
        show Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | rad hm p.1 + uFun hm p ≤ 1}) =>
          f (rayPt hm q.1.1 (clampI (rad hm q.1.1 + uFun hm q.1)))
        exact f.continuous.comp hpt
      have hIn : ContinuousOn (fun p => hepIn hm f p)
          ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
            {p | rad hm p.1 + uFun hm p ≤ 1}) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact hc
      refine ContinuousOn.congr hIn (fun p hp => ?_)
      rw [Set.mem_inter_iff] at hp
      exact hepFun_of_le hm f h p hp.2
    have hB2 : ContinuousOn (hepFun hm f h)
        ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
          {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) := by
      have hne : ∀ q : ↥({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
          {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}), rad hm q.1.1 ≠ 0 := fun q => by
        have h1 : (1 : ℝ) / 2 ≤ rad hm q.1.1 := q.2.1
        intro h0
        rw [h0] at h1
        norm_num at h1
      have hbcongr : (fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
            h (bdPt hm q.1.1, clampI (uFun hm q.1 - (1 - rad hm q.1.1))))
          = (fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
            h (⟨bpt hm q.1.1, bpt_mem_boundary hm q.1.1 (hne q)⟩,
              clampI (uFun hm q.1 - (1 - rad hm q.1.1)))) := by
        funext q
        rw [bdPt_eq hm (hne q)]
      have hbpt : Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
          (⟨bpt hm q.1.1, bpt_mem_boundary hm q.1.1 (hne q)⟩ :
            ↥(Cube.boundary (Fin (e + 1)))) :=
        Continuous.subtype_mk
          ((continuous_bpt hm).comp (Continuous.subtype_mk
            (continuous_fst.comp continuous_subtype_val) hne))
          (fun q => bpt_mem_boundary hm q.1.1 (hne q))
      have htime : Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
          clampI (uFun hm q.1 - (1 - rad hm q.1.1)) := by
        have hreal : Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
              (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
            uFun hm q.1 - (1 - rad hm q.1.1) :=
          ((continuous_uFun hm).comp continuous_subtype_val).sub
            ((continuous_const : Continuous fun _ : ↥({p : ICube (e + 1) × unitInterval |
                (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
              (1 : ℝ)).sub
              ((continuous_rad hm).comp (continuous_fst.comp continuous_subtype_val)))
        exact continuous_clampI.comp hreal
      have hc : Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
          hepOut hm h q.1 := by
        show Continuous fun q : ↥({p : ICube (e + 1) × unitInterval |
            (1 : ℝ) / 2 ≤ rad hm p.1} ∩ {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) =>
          h (bdPt hm q.1.1, clampI (uFun hm q.1 - (1 - rad hm q.1.1)))
        rw [hbcongr]
        exact h.continuous.comp (hbpt.prodMk htime)
      have hOut : ContinuousOn (fun p => hepOut hm h p)
          ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
            {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p}) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact hc
      refine ContinuousOn.congr hOut (fun p hp => ?_)
      rw [Set.mem_inter_iff] at hp
      by_cases hcl : rad hm p.1 + uFun hm p ≤ 1
      · rw [hepFun_of_le hm f h p hcl]
        exact hepIn_eq_hepOut_of_seam hm f h h0 hp.1 (le_antisymm hcl hp.2)
      · exact hepFun_of_gt hm f h p hcl
    have hcov : ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
          {p | rad hm p.1 + uFun hm p ≤ 1}) ∪
        ({p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} ∩
          {p | (1 : ℝ) ≤ rad hm p.1 + uFun hm p})
        = {p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} := by
      ext p
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        by_cases hc : rad hm p.1 + uFun hm p ≤ 1
        · exact Or.inl ⟨h, hc⟩
        · exact Or.inr ⟨h, le_of_lt (not_le.mp hc)⟩
    have hres := ContinuousOn.union_of_isClosed hB1 hB2 (hB.inter hC) (hB.inter hD)
    rwa [hcov] at hres
  have hcov : {p : ICube (e + 1) × unitInterval | rad hm p.1 ≤ 1 / 2} ∪
      {p : ICube (e + 1) × unitInterval | (1 : ℝ) / 2 ≤ rad hm p.1} = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total (rad hm p.1) (1 / 2)
  have hall := ContinuousOn.union_of_isClosed hcontA hcontB hA hB
  rw [hcov] at hall
  exact continuousOn_univ.mp hall

/-- **The homotopy extension property of the cube pair.**  Given a map `f : I^{e+1} → Z` and a
homotopy `h` of its restriction to the boundary `∂I^{e+1}` (starting at `f`), the homotopy extends
over the cube. -/
theorem hepCube (e : ℕ) {Z : Type} [TopologicalSpace Z] (f : C(ICube (e + 1), Z))
    (h : C(↥(Cube.boundary (Fin (e + 1))) × unitInterval, Z))
    (h0 : ∀ x : ↥(Cube.boundary (Fin (e + 1))), h (x, 0) = f x.1) :
    ∃ H : C(ICube (e + 1) × unitInterval, Z), (∀ x, H (x, 0) = f x) ∧
      (∀ x : ↥(Cube.boundary (Fin (e + 1))), ∀ τ : unitInterval, H (x.1, τ) = h (x, τ)) :=
  ⟨⟨hepFun (Nat.succ_le_succ (Nat.zero_le e)) f h,
      continuous_hepFun (Nat.succ_le_succ (Nat.zero_le e)) f h h0⟩,
    fun x => hepFun_zero _ f h x,
    fun x τ => hepFun_boundary _ f h h0 x.1 x.2 τ⟩

end

end Work.RatHurewicz
