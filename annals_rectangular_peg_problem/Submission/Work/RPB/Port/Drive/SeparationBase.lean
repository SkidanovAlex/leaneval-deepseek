import Mathlib
import ChallengeDeps
import Submission.Work.RPB.Port.Measurable
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Submission.Work.RPB.Port.Drive.isOpen_Zc
import Submission.Work.RPB.Port.Drive.curve_deriv_ne_zero
import Submission.Work.RPB.Port.Drive.curve_eq_iff
import Submission.Work.RPB.Port.Drive.curve_periodic
import Submission.Work.RPB.Port.Drive.winding_preconnected
import Submission.Work.RPB.Port.Drive.WindingNumber
import Submission.Work.RPB.Port.Drive.degree_homotopic
import Submission.Work.RPB.Port.Drive.rot90

/-!
# The winding number of a smooth embedded closed plane curve

Base of the proof of the Jordan separation theorem for a smooth embedded circle `γ : Circle → ℝ × ℝ`.

A `Circle`-parametrised curve is converted into the `ℝ/ℤ`-parametrised curve `gammaU γ := γ ∘ toCircle`
(whose winding number is the one developed in `Submission/Work/Drive/WindingNumber`), and the winding
number `windG` of `γ` about a point is defined as that winding number.  Local constancy, vanishing far
away and constancy on preconnected pieces are transported from the existing API.
-/

namespace Work.RPB.Port.Drive

open Manifold Topology
open scoped ContDiff

/-- The complex number attached to a vector of `ℝ × ℝ`, matching the identification used by
`Work.RPB.Port.Collision.dirC` (namely `(x,y) ↦ x + y i`). -/
def cpx (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

@[simp] lemma cpx_re (p : ℝ × ℝ) : (cpx p).re = p.1 := rfl
@[simp] lemma cpx_im (p : ℝ × ℝ) : (cpx p).im = p.2 := rfl
@[simp] lemma cpx_zero : cpx (0 : ℝ × ℝ) = 0 := rfl
@[simp] lemma cpx_sub (p q : ℝ × ℝ) : cpx (p - q) = cpx p - cpx q := by
  apply Complex.ext <;> simp [cpx]
@[simp] lemma cpx_add (p q : ℝ × ℝ) : cpx (p + q) = cpx p + cpx q := by
  apply Complex.ext <;> simp [cpx]
@[simp] lemma cpx_neg (p : ℝ × ℝ) : cpx (-p) = -cpx p := by
  apply Complex.ext <;> simp [cpx]
@[simp] lemma cpx_smul (c : ℝ) (p : ℝ × ℝ) : cpx (c • p) = c • cpx p := by
  apply Complex.ext <;> simp [cpx]

lemma cpx_ne_zero_iff {p : ℝ × ℝ} : cpx p ≠ 0 ↔ p ≠ 0 := by
  constructor
  · intro h hp
    exact h (by rw [hp, cpx_zero])
  · intro h hp
    exact h (Prod.ext (by simpa using congrArg Complex.re hp)
      (by simpa using congrArg Complex.im hp))

lemma cpx_injective : Function.Injective cpx := by
  intro p q h
  exact Prod.ext (by simpa using congrArg Complex.re h) (by simpa using congrArg Complex.im h)

/-- The `ℝ/ℤ`-parametrisation of a closed plane curve: `t ↦ γ (exp (2π t))`. -/
noncomputable def gammaU (γ : Circle → ℝ × ℝ) : UnitAddCircle → ℝ × ℝ :=
  γ ∘ (AddCircle.toCircle : AddCircle (1 : ℝ) → Circle)

lemma continuous_gammaU {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) : Continuous (gammaU γ) :=
  hγ.comp AddCircle.continuous_toCircle

lemma gammaU_apply_coe (γ : Circle → ℝ × ℝ) (t : ℝ) :
    gammaU γ (t : UnitAddCircle) = curve γ (2 * Real.pi * t) := by
  have h : (AddCircle.toCircle (t : AddCircle (1 : ℝ))) = Circle.exp (2 * Real.pi * t) := by
    rw [AddCircle.toCircle_apply_mk]
    norm_num
  show γ (AddCircle.toCircle (t : AddCircle (1 : ℝ))) = γ (Circle.exp (2 * Real.pi * t))
  rw [h]

lemma range_gammaU (γ : Circle → ℝ × ℝ) : Set.range (gammaU γ) = Set.range γ := by
  have hfun : (AddCircle.toCircle : AddCircle (1 : ℝ) → Circle)
      = ⇑(AddCircle.homeomorphCircle (T := 1) one_ne_zero) := by
    funext x
    rw [AddCircle.homeomorphCircle_apply]
  have hsurj : Function.Surjective (AddCircle.toCircle : AddCircle (1 : ℝ) → Circle) := by
    rw [hfun]
    exact (AddCircle.homeomorphCircle (T := 1) one_ne_zero).surjective
  exact hsurj.range_comp γ

/-! ## The winding number of `γ` -/

/-- The winding number of the closed plane curve `γ` about a point `p` off it, in the units of
`Work.RPB.Port.Collision.dirC` (a full turn of the direction is `2`). -/
noncomputable def windG (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) : ℤ :=
  winding (gammaU γ) (continuous_gammaU hγ) (by rw [range_gammaU]; exact hp)

lemma windG_eq_winding {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) (hp' : p ∉ Set.range (gammaU γ)) :
    windG γ hγ hp = winding (gammaU γ) (continuous_gammaU hγ) hp' := rfl

lemma notMem_range_gammaU {γ : Circle → ℝ × ℝ} {p : ℝ × ℝ} (hp : p ∉ Set.range γ) :
    p ∉ Set.range (gammaU γ) := by rwa [range_gammaU]

/-- **The winding number is locally constant in the point.** -/
theorem exists_ball_windG_eq (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball p r, ∀ (hq : q ∉ Set.range γ),
      windG γ hγ hq = windG γ hγ hp := by
  obtain ⟨r, hr, hball⟩ :=
    exists_ball_winding_eq (gammaU γ) (continuous_gammaU hγ) (notMem_range_gammaU hp)
  refine ⟨r, hr, fun q hq hq' => ?_⟩
  rw [windG_eq_winding hγ hq' (notMem_range_gammaU hq'),
    windG_eq_winding hγ hp (notMem_range_gammaU hp),
    hball q hq (notMem_range_gammaU hq')]

/-- **The winding number is constant on preconnected pieces of the complement of the curve.** -/
theorem windG_preconnected {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) {C : Set (ℝ × ℝ)}
    (hC : C ⊆ (Set.range γ)ᶜ) (hconn : IsPreconnected C) (q q' : C) :
    windG γ hγ (hC q'.2) = windG γ hγ (hC q.2) := by
  refine winding_preconnected (continuous_gammaU hγ) (C := C) ?_ hconn q q'
  intro x hx hx'
  exact hC hx (by rwa [range_gammaU] at hx')

/-! ## The direction of a ratio

`dirZ z = (z.arg / π : ℝ/ℤ)` is the doubled direction of a non-zero complex number; it agrees with
`dirC` on pairs and, crucially, the *difference* of the doubled directions of two vectors is the
doubled direction of their ratio. -/

@[simp] lemma cpx_mk (z : ℂ) : cpx (z.re, z.im) = z := rfl

/-- `cpx` is continuous. -/
lemma continuous_cpx : Continuous cpx := by
  have h : cpx = fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
    funext p
    apply Complex.ext <;> simp [cpx]
  rw [h]
  exact (Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

/-- The doubled direction (`arg / π`, in `ℝ/ℤ`) of a complex number. -/
noncomputable def dirZ (z : ℂ) : UnitAddCircle := ((z.arg / Real.pi : ℝ) : UnitAddCircle)

lemma dirZ_eq_dirC (z : ℂ) : dirZ z = Work.RPB.Port.Collision.dirC (z.re, z.im) := rfl

/-- **The difference of the doubled directions is the doubled direction of the ratio.** -/
lemma dirC_sub_eq (A B : ℝ × ℝ) (hA : A ≠ 0) (hB : B ≠ 0) :
    Work.RPB.Port.Collision.dirC A - Work.RPB.Port.Collision.dirC B
      = dirZ (cpx A / cpx B) := by
  have hA' : cpx A ≠ 0 := by rwa [cpx_ne_zero_iff]
  have hB' : cpx B ≠ 0 := by rwa [cpx_ne_zero_iff]
  -- the arguments differ by a multiple of `2π`
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (cpx A / cpx B).arg
      = ((cpx A).arg - (cpx B).arg) + m * (2 * Real.pi) := by
    have h0 : (((cpx A / cpx B).arg - ((cpx A).arg - (cpx B).arg) : ℝ) : Real.Angle) = 0 := by
      simp only [Real.Angle.coe_sub]
      rw [← Complex.arg_div_coe_angle hA' hB', sub_self]
    obtain ⟨m, hm⟩ := Real.Angle.coe_eq_zero_iff.mp h0
    rw [zsmul_eq_mul] at hm
    exact ⟨m, by linarith⟩
  -- hence `dirZ (ratio) = dirC A - dirC B`
  have hdiff : ((((cpx A).arg / Real.pi : ℝ) : UnitAddCircle)
      - (((cpx B).arg / Real.pi : ℝ) : UnitAddCircle)
      - (((cpx A / cpx B).arg / Real.pi : ℝ) : UnitAddCircle)) = 0 := by
    rw [← AddCircle.coe_sub, ← AddCircle.coe_sub]
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨-2 * m, ?_⟩
    rw [zsmul_one]
    have hrw : (cpx A).arg / Real.pi - (cpx B).arg / Real.pi - (cpx A / cpx B).arg / Real.pi
        = -2 * (m : ℝ) := by
      rw [hm]; field_simp; ring
    rw [hrw]; push_cast; ring
  have := sub_eq_zero.mp hdiff
  simpa only [dirZ, Work.RPB.Port.Collision.dirC, cpx] using this

/-- **`degree` only depends on the function.** -/
lemma degree_congr_fun {f g : UnitAddCircle → UnitAddCircle} (h : f = g)
    (hf : Continuous f) (hg : Continuous g) : degree f hf = degree g hg := by
  subst h
  exact congrArg (fun p => degree f p) (Subsingleton.elim hf hg)

/-- The ratio loop of a curve about two points off it is continuous. -/
lemma continuous_dirZ_ratio {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) {p p' : ℝ × ℝ}
    (hp : p ∉ Set.range γ) (hp' : p' ∉ Set.range γ) :
    Continuous fun t : UnitAddCircle => dirZ (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')) := by
  have hval : ∀ t : UnitAddCircle, gammaU γ t ≠ p ∧ gammaU γ t ≠ p' := fun t =>
    ⟨fun h => notMem_range_gammaU hp ⟨t, h⟩, fun h => notMem_range_gammaU hp' ⟨t, h⟩⟩
  have hnum : Continuous fun t : UnitAddCircle => cpx (gammaU γ t - p) :=
    continuous_cpx.comp ((continuous_gammaU hγ).sub continuous_const)
  have hden : Continuous fun t : UnitAddCircle => cpx (gammaU γ t - p') :=
    continuous_cpx.comp ((continuous_gammaU hγ).sub continuous_const)
  have hne : ∀ t : UnitAddCircle, cpx (gammaU γ t - p') ≠ 0 := fun t => by
    rw [cpx_ne_zero_iff, sub_ne_zero]; exact (hval t).2
  have hratio : Continuous fun t : UnitAddCircle =>
      cpx (gammaU γ t - p) / cpx (gammaU γ t - p') := hnum.div hden hne
  have hpair : Continuous fun t : UnitAddCircle =>
      ((cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).re,
        (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).im) :=
    Continuous.prodMk (Complex.continuous_re.comp hratio)
      (Complex.continuous_im.comp hratio)
  have hpairC : ContinuousOn (fun t : UnitAddCircle =>
      ((cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).re,
        (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).im)) Set.univ := hpair.continuousOn
  have hneR : ∀ t : UnitAddCircle, cpx (gammaU γ t - p) / cpx (gammaU γ t - p') ≠ 0 := by
    intro t
    refine div_ne_zero ?_ ?_ <;> rw [cpx_ne_zero_iff, sub_ne_zero] <;>
      [exact (hval t).1; exact (hval t).2]
  have hne' : ∀ t : UnitAddCircle,
      ((cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).re,
        (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).im) ≠ 0 := by
    intro t h
    refine hneR t ?_
    rw [← cpx_mk (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')), h, cpx_zero]
  have hcont : Continuous fun t : UnitAddCircle =>
      Work.RPB.Port.Collision.dirC ((cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).re,
        (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')).im) := by
    have hc := Work.RPB.Port.Configuration.continuousOn_dirC.comp hpairC (fun x _ => hne' x)
    exact continuousOn_univ.mp hc
  simpa only [dirZ_eq_dirC] using hcont

/-- **The difference of the winding numbers about two points is the degree of the ratio loop.** -/
theorem windG_sub_eq_degree (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) {p p' : ℝ × ℝ}
    (hp : p ∉ Set.range γ) (hp' : p' ∉ Set.range γ) :
    windG γ hγ hp - windG γ hγ hp'
      = degree (fun t : UnitAddCircle =>
          dirZ (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')))
        (continuous_dirZ_ratio hγ hp hp') := by
  have hp2 := notMem_range_gammaU hp
  have hp3 := notMem_range_gammaU hp'
  have hfun : dirCurve (gammaU γ) (continuous_gammaU hγ) p hp2
      - dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3
      = fun t : UnitAddCircle => dirZ (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')) := by
    funext t
    rw [Pi.sub_apply]
    exact dirC_sub_eq _ _ (fun h => hp2 ⟨t, sub_eq_zero.mp h⟩)
      (fun h => hp3 ⟨t, sub_eq_zero.mp h⟩)
  have hA : degree (dirCurve (gammaU γ) (continuous_gammaU hγ) p hp2
        - dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3)
      ((continuous_dirCurve _ _ _ _).sub (continuous_dirCurve _ _ _ _))
      = degree (fun t : UnitAddCircle =>
          dirZ (cpx (gammaU γ t - p) / cpx (gammaU γ t - p')))
        (continuous_dirZ_ratio hγ hp hp') :=
    degree_congr_fun hfun _ _
  have hB : degree (dirCurve (gammaU γ) (continuous_gammaU hγ) p hp2
        - dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3)
      ((continuous_dirCurve _ _ _ _).sub (continuous_dirCurve _ _ _ _))
      = degree (dirCurve (gammaU γ) (continuous_gammaU hγ) p hp2)
          (continuous_dirCurve _ _ _ _)
        - degree (dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3)
          (continuous_dirCurve _ _ _ _) := by
    have hadd := degree_add (dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3)
      (dirCurve (gammaU γ) (continuous_gammaU hγ) p hp2
        - dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3)
      (continuous_dirCurve _ _ _ _)
      ((continuous_dirCurve _ _ _ _).sub (continuous_dirCurve _ _ _ _))
    have hsum : dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3
        + (dirCurve (gammaU γ) (continuous_gammaU hγ) p hp2
          - dirCurve (gammaU γ) (continuous_gammaU hγ) p' hp3)
        = dirCurve (gammaU γ) (continuous_gammaU hγ) p hp2 := by
      funext t; simp [Pi.sub_apply]
    have hcon := degree_congr_fun hsum
      ((continuous_dirCurve _ _ _ _).add
        ((continuous_dirCurve _ _ _ _).sub (continuous_dirCurve _ _ _ _)))
      (continuous_dirCurve _ _ _ _)
    rw [hcon] at hadd
    omega
  simp only [windG, winding]
  rw [← hB, hA]

/-- The winding number for a smooth embedded closed curve. -/
noncomputable def windE (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {p : ℝ × ℝ} (hp : p ∉ Set.range γ) : ℤ :=
  windG γ hγ.isEmbedding.continuous hp

/-- **Local separation data** at a point of a set `K`: an open neighbourhood `U` of the point, split
by `K` into two nonempty open path-connected pieces, each of which accumulates at every point of
`K ∩ U`. -/
structure LocalSep (K : Set (ℝ × ℝ)) (U U₁ U₂ : Set (ℝ × ℝ)) : Prop where
  isOpen_U : IsOpen U
  isOpen₁ : IsOpen U₁
  isOpen₂ : IsOpen U₂
  pc₁ : IsPathConnected U₁
  pc₂ : IsPathConnected U₂
  disjoint : Disjoint U₁ U₂
  union : U₁ ∪ U₂ = U \ K
  acc₁ : ∀ q ∈ U ∩ K, q ∈ closure U₁
  acc₂ : ∀ q ∈ U ∩ K, q ∈ closure U₂

/-- The ratio of the chords from `p` and `p'` to the point `G x` of the curve (as a complex number). -/
noncomputable def ratioMap (G : ℝ → ℝ × ℝ) (p p' : ℝ × ℝ) (x : ℝ) : ℂ :=
  cpx (G x - p) / cpx (G x - p')

lemma ratioMap_apply (G : ℝ → ℝ × ℝ) (p p' : ℝ × ℝ) (x : ℝ) :
    ratioMap G p p' x = cpx (G x - p) / cpx (G x - p') := rfl

lemma range_curve (γ : Circle → ℝ × ℝ) : Set.range (curve γ) = Set.range γ := by
  have h : curve γ = γ ∘ Circle.exp := rfl
  rw [h, Set.range_comp, Circle.exp_surjective.range_eq]
  simp

end Work.RPB.Port.Drive
