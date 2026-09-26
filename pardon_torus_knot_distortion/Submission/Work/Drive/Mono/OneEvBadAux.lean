import Mathlib
import Submission.Work.Drive.Mono.OneEventNDDefs
import Submission.Work.Drive.Mono.Band.BandChartDefs

/-!
# `oneEvBad_null3` (auxiliary definitions and lemmas)

Auxiliary definitions and lemmas for `Work.Drive.Mono.oneEvBad_null3`: the sweep height and the
slab coordinate in the parameter plane, the event charts (a `C¹` parametrisation of an event locus
by the tilt and the slab coordinate), and the local structure lemmas.
-/

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped RealInnerProductSpace ENNReal Topology

set_option maxHeartbeats 3000000

namespace Work.Drive.Mono

noncomputable section


/-! ## The sweep height and the slab coordinate in the parameter plane -/

/-- The sweep height of the tilt `τ`, read in the parameter plane: `x ↦ ⟪dirOf τ a₀ b₀, par ψ x⟫`. -/
def sH (ψ : Submission.Diffeo) (a₀ b₀ : R3) (τ : ℝ) : ℝ × ℝ → ℝ :=
  fun x => inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (Work.BoxShrink.Pinch.par ψ x)

/-- The slab-height coordinate in the parameter plane: `x ↦ ⟪v, par ψ x⟫`. -/
def hFn (ψ : Submission.Diffeo) (v : R3) : ℝ × ℝ → ℝ :=
  fun x => inner ℝ v (Work.BoxShrink.Pinch.par ψ x)

@[simp] theorem sH_apply (ψ : Submission.Diffeo) (a₀ b₀ : R3) (τ : ℝ) (x : ℝ × ℝ) :
    sH ψ a₀ b₀ τ x = inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)
      (Work.BoxShrink.Pinch.par ψ x) := rfl

@[simp] theorem hFn_apply (ψ : Submission.Diffeo) (v : R3) (x : ℝ × ℝ) :
    hFn ψ v x = inner ℝ v (Work.BoxShrink.Pinch.par ψ x) := rfl

/-- The level function of a chart `Ψ`: `(τ,σ) ↦ sH ψ a₀ b₀ τ (Ψ (τ,σ))`. -/
def evLevel (ψ : Submission.Diffeo) (a₀ b₀ : R3) (Ψ : ℝ × ℝ → ℝ × ℝ) : ℝ × ℝ → ℝ :=
  fun y => sH ψ a₀ b₀ y.1 (Ψ y)

@[simp] theorem evLevel_apply (ψ : Submission.Diffeo) (a₀ b₀ : R3) (Ψ : ℝ × ℝ → ℝ × ℝ)
    (y : ℝ × ℝ) : evLevel ψ a₀ b₀ Ψ y = sH ψ a₀ b₀ y.1 (Ψ y) := rfl

/-- **An event chart** for the events of the tilted sweep that are parametrised by the tilt `τ` and
the slab coordinate `σ = ⟪v, par ψ ·⟫`: a `C¹` map `Ψ` on an open set `V ∋ (τ₀,σ₀)` with
`hFn ψ v (Ψ (τ,σ)) = σ`, whose level function has a nonvanishing `σ`-derivative at `(τ₀,σ₀)` and
the envelope `τ`-derivative there, together with a uniqueness neighbourhood `U ∋ p₀`: any point
`q ∈ U` carrying the chart's event condition `care τ q` and the slab coordinate `σ` is `Ψ (τ,σ)`. -/
structure EvChart (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (care : ℝ → ℝ × ℝ → Prop)
    (τ₀ σ₀ : ℝ) (p₀ : ℝ × ℝ) where
  V : Set (ℝ × ℝ)
  hVopen : IsOpen V
  hVmem : (τ₀, σ₀) ∈ V
  Ψ : ℝ × ℝ → ℝ × ℝ
  hΨcd : ContDiffOn ℝ 1 Ψ V
  hΨmem : Ψ (τ₀, σ₀) = p₀
  hg : ∀ x ∈ V, hFn ψ v (Ψ x) = x.2
  hσ : fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (0, 1) ≠ 0
  hτ : fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (1, 0)
      = inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)
          (Work.BoxShrink.Pinch.par ψ p₀)
  U : Set (ℝ × ℝ)
  hUopen : IsOpen U
  hUmem : p₀ ∈ U
  huniq : ∀ (τ σ : ℝ) (q : ℝ × ℝ), (τ, σ) ∈ V → q ∈ U → care τ q → hFn ψ v q = σ →
    q = Ψ (τ, σ)

/-- **A critical-point chart** (a type-1 event): the nondegenerate critical point of the sweep
height continues as a `C¹` function `P` of the tilt, with the envelope formula for the level. -/
structure CritChart (ψ : Submission.Diffeo) (a₀ b₀ : R3) (τ₀ : ℝ) (p₀ : ℝ × ℝ) where
  V : Set ℝ
  hVopen : IsOpen V
  hVmem : τ₀ ∈ V
  P : ℝ → ℝ × ℝ
  hPcd : ContDiffOn ℝ 1 P V
  hPmem : P τ₀ = p₀
  hcrit : ∀ τ ∈ V, fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) (P τ) = 0
  hLτ : deriv (fun τ : ℝ => sH ψ a₀ b₀ τ (P τ)) τ₀
      = inner ℝ (deriv (fun s : ℝ => Work.Drive.Mono.Band.dirOf s a₀ b₀) τ₀)
          (Work.BoxShrink.Pinch.par ψ p₀)
  U : Set (ℝ × ℝ)
  hUopen : IsOpen U
  hUmem : p₀ ∈ U
  huniq : ∀ τ ∈ V, ∀ q ∈ U, fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) q = 0 → q = P τ


/-! ## The dictionary with the sweep height and the slab height -/

/-- `sH` is the sweep height of the tilt `τ`. -/
theorem sH_eq_sweepHeight (ψ : Submission.Diffeo) (a₀ b₀ : R3) (τ : ℝ) :
    sH ψ a₀ b₀ τ
      = Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀)) := by
  rw [Work.Drive.EpsForm.sweepHeight_innerSL]
  rfl

/-- `hFn` is `slabFnPar` up to the additive constant `⟪v,c⟫ + u`. -/
theorem hFn_eq_slabFnPar_add (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3) :
    Work.Drive.Final.slabFnPar ψ c u v
      = fun x : ℝ × ℝ => hFn ψ v x - (inner ℝ v c + u) := rfl

/-- The differentials of `slabFnPar` and of `hFn` coincide. -/
theorem fderiv_slabFnPar_eq (ψ : Submission.Diffeo) (c : R3) (u : ℝ) (v : R3) (x : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) x = fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x := by
  rw [hFn_eq_slabFnPar_add]
  exact fderiv_sub_const _

/-! ## Joint regularity -/

/-- The tilt direction `τ ↦ dirOf τ a₀ b₀` is `C²` for an orthonormal pair. -/
theorem contDiff_dirOf {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) :
    ContDiff ℝ 2 (fun τ : ℝ => Work.Drive.Mono.Band.dirOf τ a₀ b₀) := by
  have hlin : ContDiff ℝ 2 (fun τ : ℝ => τ • a₀ + b₀) := by fun_prop
  have hne : ∀ τ : ℝ, τ • a₀ + b₀ ≠ 0 :=
    fun τ => Work.Drive.Mono.Band.dirOf_denom_ne_zero ha hb hab τ
  have hnorm : ContDiff ℝ 2 (fun τ : ℝ => ‖τ • a₀ + b₀‖) := ContDiff.norm ℝ hlin hne
  have hpos : ∀ τ : ℝ, ‖τ • a₀ + b₀‖ ≠ 0 :=
    fun τ => norm_ne_zero_iff.mpr (hne τ)
  have hinv : ContDiff ℝ 2 (fun τ : ℝ => (‖τ • a₀ + b₀‖)⁻¹) := ContDiff.inv hnorm hpos
  have h := hinv.smul hlin
  have hfun : (fun τ : ℝ => Work.Drive.Mono.Band.dirOf τ a₀ b₀)
      = (fun τ : ℝ => (‖τ • a₀ + b₀‖)⁻¹) • (fun τ : ℝ => τ • a₀ + b₀) := by
    funext τ
    rw [Work.Drive.Mono.Band.dirOf]
    rfl
  rw [hfun]
  exact h

/-- The uncurried sweep height `(τ,x) ↦ sH ψ a₀ b₀ τ x` is `C²`. -/
theorem contDiff_sH_uncurry {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) :
    ContDiff ℝ 2 (Function.uncurry (sH ψ a₀ b₀)) := by
  have hdir : ContDiff ℝ 2 (fun p : ℝ × (ℝ × ℝ) => Work.Drive.Mono.Band.dirOf p.1 a₀ b₀) :=
    (contDiff_dirOf ha hb hab).comp contDiff_fst
  have hpar : ContDiff ℝ 2 (fun p : ℝ × (ℝ × ℝ) => Work.BoxShrink.Pinch.par ψ p.2) :=
    ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le (by exact WithTop.coe_le_coe.mpr le_top)).comp
      contDiff_snd
  have h : Function.uncurry (sH ψ a₀ b₀)
      = fun p : ℝ × (ℝ × ℝ) => inner ℝ (Work.Drive.Mono.Band.dirOf p.1 a₀ b₀)
          (Work.BoxShrink.Pinch.par ψ p.2) := rfl
  rw [h]
  exact ContDiff.clm_apply (f := fun p : ℝ × (ℝ × ℝ) =>
      (innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.1 a₀ b₀))
    (g := fun p : ℝ × (ℝ × ℝ) => Work.BoxShrink.Pinch.par ψ p.2)
    ((ContinuousLinearMap.contDiff (innerSL ℝ)).comp hdir) hpar

/-- The joint derivative `(τ,x) ↦ fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ x) x` is `C¹`. -/
theorem contDiff_fderiv_sH {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) :
    ContDiff ℝ 1 (fun q : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ q.1 x) q.2) := by
  have h1 : ContDiff ℝ 2 (Function.uncurry (fun q : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ q.1)) := by
    have h2 : Function.uncurry (fun q : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ q.1)
        = (Function.uncurry (sH ψ a₀ b₀)) ∘
            (fun p : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) => (p.1.1, p.2)) := rfl
    rw [h2]
    exact (contDiff_sH_uncurry ha hb hab ψ).comp (by fun_prop)
  exact ContDiff.fderiv (f := fun q : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ q.1)
    (g := fun q : ℝ × (ℝ × ℝ) => q.2) h1 contDiff_snd (by norm_num)

/-- The joint derivative applied to a fixed vector is `C¹`. -/
theorem contDiff_fderiv_sH_apply {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (e : ℝ × ℝ) :
    ContDiff ℝ 1 (fun q : ℝ × (ℝ × ℝ) =>
      (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ q.1 x) q.2) e) :=
  ((ContinuousLinearMap.apply ℝ ℝ e).contDiff.comp (contDiff_fderiv_sH ha hb hab ψ))

/-- The slab coordinate `hFn` is `C¹`. -/
theorem contDiff_hFn (ψ : Submission.Diffeo) (v : R3) : ContDiff ℝ 1 (hFn ψ v) :=
  (ContinuousLinearMap.contDiff (innerSL ℝ v)).comp
    ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le
      (by exact WithTop.coe_le_coe.mpr le_top))




/-! ## The witness space -/

/-- The witness space of a bad pair: `(u, h, τ, q, q')`. -/
abbrev Wit : Type := ℝ × ℝ × ℝ × (ℝ × ℝ) × (ℝ × ℝ)

/-- The cutting level `u` of a witness. -/
def wU (w : Wit) : ℝ := w.1
/-- The slab half-width `h` of a witness. -/
def wH (w : Wit) : ℝ := w.2.1
/-- The tilt parameter `τ` of a witness. -/
def wT (w : Wit) : ℝ := w.2.2.1
/-- The first parameter-plane point of a witness. -/
def wQ (w : Wit) : ℝ × ℝ := w.2.2.2.1
/-- The second parameter-plane point of a witness. -/
def wQ' (w : Wit) : ℝ × ℝ := w.2.2.2.2

/-- The witness with the given components. -/
def wit (u h τ : ℝ) (q q' : ℝ × ℝ) : Wit := (u, h, τ, q, q')

@[simp] theorem wU_wit (u h τ : ℝ) (q q' : ℝ × ℝ) : wU (wit u h τ q q') = u := rfl
@[simp] theorem wH_wit (u h τ : ℝ) (q q' : ℝ × ℝ) : wH (wit u h τ q q') = h := rfl
@[simp] theorem wT_wit (u h τ : ℝ) (q q' : ℝ × ℝ) : wT (wit u h τ q q') = τ := rfl
@[simp] theorem wQ_wit (u h τ : ℝ) (q q' : ℝ × ℝ) : wQ (wit u h τ q q') = q := rfl
@[simp] theorem wQ'_wit (u h τ : ℝ) (q q' : ℝ × ℝ) : wQ' (wit u h τ q q') = q' := rfl

/-- The projection of the witness space to the bad triples `(u,h,τ)`. -/
def witProj (w : Wit) : ℝ × ℝ × ℝ := (wU w, wH w, wT w)

@[simp] theorem witProj_wit (u h τ : ℝ) (q q' : ℝ × ℝ) :
    witProj (wit u h τ q q') = (u, h, τ) := rfl

/-- The tangency of the level functional with the slab functional at a point. -/
def Tangent (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (τ : ℝ) (q : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, fderiv ℝ (sH ψ a₀ b₀ τ) q = t • fderiv ℝ (hFn ψ v) q

/-! ## The face-event chart -/

/-- The coordinate encoding of a covector on `ℝ × ℝ`: its values on the two basis vectors. -/
def covec (T : (ℝ × ℝ) →L[ℝ] ℝ) : ℝ × ℝ := (T (1, 0), T (0, 1))

@[simp] theorem covec_fst (T : (ℝ × ℝ) →L[ℝ] ℝ) : (covec T).1 = T (1, 0) := rfl
@[simp] theorem covec_snd (T : (ℝ × ℝ) →L[ℝ] ℝ) : (covec T).2 = T (0, 1) := rfl

/-- The coordinate encoding is injective. -/
theorem covec_eq_zero {T : (ℝ × ℝ) →L[ℝ] ℝ} (h : covec T = 0) : T = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  have h1 : T (1, 0) = 0 := by rw [← covec_fst T, h]; rfl
  have h2 : T (0, 1) = 0 := by rw [← covec_snd T, h]; rfl
  rw [hv, map_add, map_smul, map_smul, h1, h2]
  simp

/-- The coordinate encoding as a continuous linear map. -/
def covecL : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := covec
      map_add' := fun T S => by ext <;> simp [covec]
      map_smul' := fun c T => by ext <;> simp [covec] }

@[simp] theorem covecL_apply (T : (ℝ × ℝ) →L[ℝ] ℝ) : covecL T = covec T := rfl

/-- The tilt-section of the sweep height is `C²`. -/
theorem contDiff_sH_section {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (τ₀ : ℝ) :
    ContDiff ℝ 2 (sH ψ a₀ b₀ τ₀) := by
  have h := (contDiff_sH_uncurry ha hb hab ψ).comp
    (show ContDiff ℝ 2 (fun x : ℝ × ℝ => ((τ₀ : ℝ), x)) from by fun_prop)
  have h2 : (Function.uncurry (sH ψ a₀ b₀)) ∘ (fun x : ℝ × ℝ => ((τ₀ : ℝ), x))
      = sH ψ a₀ b₀ τ₀ := by
    funext x
    rfl
  rwa [h2] at h

/-- The slab coordinate is `C²`. -/
theorem contDiff_hFn_two (ψ : Submission.Diffeo) (v : R3) : ContDiff ℝ 2 (hFn ψ v) :=
  (ContinuousLinearMap.contDiff (innerSL ℝ v)).comp
    ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le (by exact WithTop.coe_le_coe.mpr le_top))

/-- The gradient of the slab coordinate is `C¹`. -/
theorem contDiff_fderiv_hFn (ψ : Submission.Diffeo) (v : R3) :
    ContDiff ℝ 1 (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) := by
  have h2g : ContDiff ℝ 2 (hFn ψ v) := contDiff_hFn_two ψ v
  exact (contDiff_succ_iff_fderiv.mp h2g).2.2


/-- The chart function of a type-2 (face) event: the gradient of the Lagrangian
`λ ↦ sH ψ a₀ b₀ τ - λ·hFn ψ v` (encoded as a pair of coordinates) and the slab coordinate. -/
def faceFn (ψ : Submission.Diffeo) (v a₀ b₀ : R3) :
    ((ℝ × ℝ) × ((ℝ × ℝ) × ℝ)) → ((ℝ × ℝ) × ℝ) :=
  fun p => (covec (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ p.1.1 x) p.2.1
      - p.2.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) p.2.1),
    hFn ψ v p.2.1 - p.1.2)

/-- The `(x,λ)`-section of the chart function at a fixed tilt. -/
def faceSec (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (τ₀ σ₀ : ℝ) :
    ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) :=
  fun y => (covec (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) y.1 - y.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) y.1),
    hFn ψ v y.1 - σ₀)

/-- The `λ`-part of the derivative of the section. -/
def faceSecSmul (ψ : Submission.Diffeo) (v : R3) (x₀ : ℝ × ℝ) :
    ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).smulRight (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀)

/-- The first component of the derivative of the section, as a covector. -/
def faceSecD1 (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (τ₀ : ℝ) (x₀ : ℝ × ℝ) (mu₀ : ℝ) :
    ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))
    - (mu₀ • ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))
      + faceSecSmul ψ v x₀)

/-- The second component of the derivative of the section. -/
def faceSecD2 (ψ : Submission.Diffeo) (v : R3) (x₀ : ℝ × ℝ) :
    ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

/-- The derivative of the section, used as the invertibility hypothesis of the implicit function
theorem. -/
def faceSecDeriv (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (τ₀ : ℝ) (x₀ : ℝ × ℝ) (mu₀ : ℝ) :
    ((ℝ × ℝ) × ℝ) →L[ℝ] ((ℝ × ℝ) × ℝ) :=
  (covecL.comp (faceSecD1 ψ v a₀ b₀ τ₀ x₀ mu₀)).prod (faceSecD2 ψ v x₀)

/-- **The derivative of the face-chart section.** -/
theorem hasFDerivAt_faceSec {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (v : R3) (τ₀ σ₀ : ℝ) (x₀ : ℝ × ℝ)
    (mu₀ : ℝ) :
    HasFDerivAt (faceSec ψ v a₀ b₀ τ₀ σ₀) (faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀) (x₀, mu₀) := by
  have h2f : ContDiff ℝ 2 (sH ψ a₀ b₀ τ₀) := contDiff_sH_section ha hb hab ψ τ₀
  have h2g : ContDiff ℝ 2 (hFn ψ v) := contDiff_hFn_two ψ v
  have hf : ContDiff ℝ 1 (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) := (contDiff_succ_iff_fderiv.mp h2f).2.2
  have hg : ContDiff ℝ 1 (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) := (contDiff_succ_iff_fderiv.mp h2g).2.2
  have hf' : HasFDerivAt (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x))
      (fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀) x₀ :=
    ((hf.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hg' : HasFDerivAt (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x))
      (fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀) x₀ :=
    ((hg.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have h2g' : HasFDerivAt (hFn ψ v) (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) x₀ :=
    ((h2g.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  have hfst : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => y.1)
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) (x₀, mu₀) :=
    (hasFDerivAt_fst : HasFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) (x₀, mu₀))
  have hsnd : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => y.2)
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (x₀, mu₀) :=
    (hasFDerivAt_snd : HasFDerivAt Prod.snd (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (x₀, mu₀))
  have h1 : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) y.1)
      ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))
      (x₀, mu₀) :=
    HasFDerivAt.comp (x₀, mu₀) hf' hfst
  have hv : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) y.1)
      ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))
      (x₀, mu₀) :=
    HasFDerivAt.comp (x₀, mu₀) hg' hfst
  have h2 : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => y.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) y.1)
      (mu₀ • ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ))
        + faceSecSmul ψ v x₀)
      (x₀, mu₀) :=
    HasFDerivAt.smul hsnd hv
  have h3 : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) y.1
      - y.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) y.1)
      (faceSecD1 ψ v a₀ b₀ τ₀ x₀ mu₀) (x₀, mu₀) :=
    HasFDerivAt.sub h1 h2
  have h4 : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => hFn ψ v y.1 - σ₀)
      (faceSecD2 ψ v x₀) (x₀, mu₀) := by
    have h4a := HasFDerivAt.comp (x₀, mu₀) h2g' hfst
    have h4b := h4a.sub_const σ₀
    simpa [Function.comp_def, faceSecD2] using h4b
  have hc : HasFDerivAt (fun y : (ℝ × ℝ) × ℝ => covec (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) y.1
      - y.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) y.1))
      (covecL.comp (faceSecD1 ψ v a₀ b₀ τ₀ x₀ mu₀)) (x₀, mu₀) :=
    HasFDerivAt.comp (x₀, mu₀) (ContinuousLinearMap.hasFDerivAt covecL) h3
  exact HasFDerivAt.prodMk hc h4

/-- Evaluating the first component of the derivative of the section. -/
theorem faceSecD1_apply (ψ : Submission.Diffeo) (v a₀ b₀ : R3) (τ₀ : ℝ) (x₀ : ℝ × ℝ)
    (mu₀ : ℝ) (z : (ℝ × ℝ) × ℝ) :
    (faceSecD1 ψ v a₀ b₀ τ₀ x₀ mu₀ z) z.1
      = ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀) z.1) z.1
        - mu₀ * (((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀) z.1) z.1)
        - z.2 * (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ z.1) := by
  have hfst : ∀ y : (ℝ × ℝ) × ℝ, (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) y = y.1 := fun y => rfl
  have hsnd : ∀ y : (ℝ × ℝ) × ℝ, (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) y = y.2 := fun y => rfl
  simp only [faceSecD1, faceSecSmul, sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    hfst, hsnd]
  ring

/-- **Injectivity of the derivative of the face-chart section**, from the Lagrange non-degeneracy. -/
theorem faceSecDeriv_injective {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {ψ : Submission.Diffeo} {v : R3} (τ₀ : ℝ) (x₀ : ℝ × ℝ) (mu₀ : ℝ)
    (hbne : fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ ≠ 0)
    (hlag : ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ w = 0 →
      ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀) w) w
        - mu₀ * (((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀) w) w) ≠ 0)
    (z : (ℝ × ℝ) × ℝ) (hz : faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀ z = 0) : z = 0 := by
  have h1 : faceSecD1 ψ v a₀ b₀ τ₀ x₀ mu₀ z = 0 := by
    have h := congrArg Prod.fst hz
    have h' : covec (faceSecD1 ψ v a₀ b₀ τ₀ x₀ mu₀ z) = 0 := by simpa [faceSecDeriv] using h
    exact covec_eq_zero h'
  have h2 : fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ z.1 = 0 := by
    have h := congrArg Prod.snd hz
    simpa [faceSecDeriv, faceSecD2, ContinuousLinearMap.comp_apply] using h
  have h3 : ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀) z.1) z.1
      - mu₀ * (((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀) z.1) z.1) = 0 := by
    have h := congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ => T z.1) h1
    rw [faceSecD1_apply, h2, mul_zero, sub_zero] at h
    exact h
  by_cases hz1 : z.1 = 0
  · have hs : z.2 • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ = 0 := by
      have h := h1
      have hz1' : z = (0, z.2) := by ext <;> simp [hz1]
      rw [hz1'] at h
      simpa [faceSecD1, faceSecSmul, sub_apply, add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply] using h
    have hz2 : z.2 = 0 := by
      rcases smul_eq_zero.mp hs with h | h
      · exact h
      · exact absurd h hbne
    ext <;> simp [hz1, hz2]
  · exact absurd (hlag z.1 hz1 h2) (by rw [h3]; norm_num)

/-- **The derivative of the face-chart section is invertible** at a point satisfying the Lagrange
non-degeneracy. -/
theorem faceSecDeriv_isInvertible {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {ψ : Submission.Diffeo} {v : R3} (τ₀ : ℝ) (x₀ : ℝ × ℝ) (mu₀ : ℝ)
    (hbne : fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ ≠ 0)
    (hlag : ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀ w = 0 →
      ((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x)) x₀) w) w
        - mu₀ * (((fderiv ℝ (fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x)) x₀) w) w) ≠ 0) :
    (faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀).IsInvertible := by
  have hinj : Function.Injective (faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀) := by
    intro z w hzw
    have h1 : faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀ (z - w) = 0 := by
      rw [map_sub, hzw, sub_self]
    have h2 := faceSecDeriv_injective (ψ := ψ) (v := v) ha hb hab τ₀ x₀ mu₀ hbne hlag
      (z - w) h1
    exact sub_eq_zero.mp h2
  refine ⟨ContinuousLinearEquiv.ofBijective (faceSecDeriv ψ v a₀ b₀ τ₀ x₀ mu₀) ?_ ?_, rfl⟩
  · rw [LinearMap.ker_eq_bot]
    exact hinj
  · rw [LinearMap.range_eq_top]
    exact (LinearMap.injective_iff_surjective.mp hinj)


/-- The derivative of a slice in the second variable. -/
theorem fderiv_slice_inr {F : ℝ × (ℝ × ℝ) → ℝ} {τ : ℝ} {x : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F ((τ : ℝ), x)) (v : ℝ × ℝ) :
    (fderiv ℝ F ((τ : ℝ), x)) (0, v) = (fderiv ℝ (fun y : ℝ × ℝ => F ((τ : ℝ), y)) x) v := by
  have hsec : HasFDerivAt (fun y : ℝ × ℝ => ((τ : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_prodMk_right (τ : ℝ) x
  have hcomp : HasFDerivAt (fun y : ℝ × ℝ => F ((τ : ℝ), y))
      ((fderiv ℝ F ((τ : ℝ), x)) ∘SL ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) x :=
    HasFDerivAt.comp x (hF.hasFDerivAt) hsec
  rw [hcomp.fderiv]
  rfl

/-- The derivative of a slice in the first variable. -/
theorem fderiv_slice_inl {F : ℝ × (ℝ × ℝ) → ℝ} {τ : ℝ} {x : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F ((τ : ℝ), x)) (v : ℝ) :
    (fderiv ℝ F ((τ : ℝ), x)) (v, 0) = (fderiv ℝ (fun τ' : ℝ => F ((τ' : ℝ), x)) τ) v := by
  have hsec : HasFDerivAt (fun τ' : ℝ => ((τ' : ℝ), x))
      (ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) τ :=
    hasFDerivAt_prodMk_left (τ : ℝ) x
  have hcomp : HasFDerivAt (fun τ' : ℝ => F ((τ' : ℝ), x))
      ((fderiv ℝ F ((τ : ℝ), x)) ∘SL ContinuousLinearMap.inl ℝ ℝ (ℝ × ℝ)) τ :=
    HasFDerivAt.comp τ (hF.hasFDerivAt) hsec
  rw [hcomp.fderiv]
  rfl

/-- The derivative of the tilt curve `τ ↦ sH ψ a₀ b₀ τ x`. -/
theorem deriv_sH_fixed {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) (ψ : Submission.Diffeo) (x : ℝ × ℝ) (τ : ℝ) :
    deriv (fun t : ℝ => sH ψ a₀ b₀ t x) τ
      = inner ℝ (deriv (fun t : ℝ => Work.Drive.Mono.Band.dirOf t a₀ b₀) τ)
          (Work.BoxShrink.Pinch.par ψ x) := by
  have hdir : DifferentiableAt ℝ (fun t : ℝ => Work.Drive.Mono.Band.dirOf t a₀ b₀) τ :=
    ((contDiff_dirOf ha hb hab).differentiable (by norm_num)).differentiableAt
  have h1 : HasDerivAt (fun t : ℝ => Work.Drive.Mono.Band.dirOf t a₀ b₀)
      (deriv (fun t : ℝ => Work.Drive.Mono.Band.dirOf t a₀ b₀) τ) τ := hdir.hasDerivAt
  have h2 : HasDerivAt (fun _ : ℝ => Work.BoxShrink.Pinch.par ψ x) 0 τ := hasDerivAt_const _ _
  have h3 := h1.inner ℝ h2
  have h4 : HasDerivAt (fun t : ℝ => sH ψ a₀ b₀ t x)
      (inner ℝ (deriv (fun t : ℝ => Work.Drive.Mono.Band.dirOf t a₀ b₀) τ)
        (Work.BoxShrink.Pinch.par ψ x)) τ := by
    simpa only [sH, inner_zero_right, zero_add] using h3
  exact h4.deriv

/-- The `σ`-derivative of the level function of a face chart. -/
theorem evLevel_sigma {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {ψ : Submission.Diffeo} {v : R3} {τ₀ σ₀ mu₀ : ℝ} {x₀ : ℝ × ℝ}
    {Ψ : ℝ × ℝ → ℝ × ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hVmem : (τ₀, σ₀) ∈ V)
    (hΨcd : ContDiffOn ℝ 1 Ψ V) (hΨmem : Ψ (τ₀, σ₀) = x₀)
    (hg : ∀ y ∈ V, hFn ψ v (Ψ y) = y.2)
    (htang : fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀
      = mu₀ • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) :
    fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (0, 1) = mu₀ := by
  have hGd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2)
      (τ₀, Ψ (τ₀, σ₀)) :=
    ((contDiff_sH_uncurry ha hb hab ψ).differentiable (by norm_num)).differentiableAt
  have hΨd : DifferentiableAt ℝ Ψ (τ₀, σ₀) :=
    (hΨcd.contDiffAt (hV.mem_nhds hVmem)).differentiableAt one_ne_zero
  have hsecd : HasFDerivAt (fun y : ℝ × ℝ => (y.1, Ψ y))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ Ψ (τ₀, σ₀))) (τ₀, σ₀) :=
    hasFDerivAt_fst.prodMk (hΨd.hasFDerivAt)
  have hcomp := HasFDerivAt.comp (τ₀, σ₀)
    (hGd.hasFDerivAt : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2)
      (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) (τ₀, Ψ (τ₀, σ₀)))
      (τ₀, Ψ (τ₀, σ₀))) hsecd
  have hfun : (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) ∘
      (fun y : ℝ × ℝ => (y.1, Ψ y)) = evLevel ψ a₀ b₀ Ψ := by
    funext y; rfl
  have hchain : HasFDerivAt (fun y : ℝ × ℝ => hFn ψ v (Ψ y))
      ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) (Ψ (τ₀, σ₀))) ∘SL
        (fderiv ℝ Ψ (τ₀, σ₀))) (τ₀, σ₀) :=
    HasFDerivAt.comp (τ₀, σ₀)
      (((contDiff_hFn ψ v).differentiable one_ne_zero).differentiableAt.hasFDerivAt)
      (hΨd.hasFDerivAt)
  have heq : (fun y : ℝ × ℝ => hFn ψ v (Ψ y)) =ᶠ[𝓝 (τ₀, σ₀)] (fun y : ℝ × ℝ => y.2) :=
    eventually_of_mem (hV.mem_nhds hVmem) (fun y hy => hg y hy)
  have hderiv2 : fderiv ℝ (fun y : ℝ × ℝ => hFn ψ v (Ψ y)) (τ₀, σ₀)
      = ContinuousLinearMap.snd ℝ ℝ ℝ := by
    rw [heq.fderiv_eq, fderiv_snd]
  have hone : ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) (Ψ (τ₀, σ₀)))
      ((fderiv ℝ Ψ (τ₀, σ₀)) (0, 1))) = 1 := by
    have h1 := congrArg (fun (T : (ℝ × ℝ) →L[ℝ] ℝ) => T (0, 1)) hchain.fderiv
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [← h1, hderiv2]
    rfl
  have hbase : fderiv ℝ (evLevel ψ a₀ b₀ Ψ) (τ₀, σ₀)
      = (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) (τ₀, Ψ (τ₀, σ₀))) ∘SL
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ Ψ (τ₀, σ₀))) := by
    rw [← hfun]
    exact hcomp.fderiv
  rw [fderivWithin_of_isOpen hV hVmem, hbase]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  rw [show ((ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 1)) = (0 : ℝ) from rfl]
  rw [fderiv_slice_inr (F := fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) hGd]
  dsimp only
  rw [hΨmem, htang]
  simp only [smul_apply, smul_eq_mul]
  rw [show ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀)
      ((fderiv ℝ Ψ (τ₀, σ₀)) (0, 1))) = 1 by rw [← hΨmem]; exact hone, mul_one]


/-- The `τ`-derivative of the level function of a face chart (the envelope formula). -/
theorem evLevel_tau {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {ψ : Submission.Diffeo} {v : R3} {τ₀ σ₀ mu₀ : ℝ} {x₀ : ℝ × ℝ}
    {Ψ : ℝ × ℝ → ℝ × ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (hVmem : (τ₀, σ₀) ∈ V)
    (hΨcd : ContDiffOn ℝ 1 Ψ V) (hΨmem : Ψ (τ₀, σ₀) = x₀)
    (hg : ∀ y ∈ V, hFn ψ v (Ψ y) = y.2)
    (htang : fderiv ℝ (fun x : ℝ × ℝ => sH ψ a₀ b₀ τ₀ x) x₀
      = mu₀ • fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀) :
    fderivWithin ℝ (evLevel ψ a₀ b₀ Ψ) V (τ₀, σ₀) (1, 0)
      = inner ℝ (deriv (fun t : ℝ => Work.Drive.Mono.Band.dirOf t a₀ b₀) τ₀)
          (Work.BoxShrink.Pinch.par ψ x₀) := by
  have hGd : DifferentiableAt ℝ (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2)
      (τ₀, Ψ (τ₀, σ₀)) :=
    ((contDiff_sH_uncurry ha hb hab ψ).differentiable (by norm_num)).differentiableAt
  have hΨd : DifferentiableAt ℝ Ψ (τ₀, σ₀) :=
    (hΨcd.contDiffAt (hV.mem_nhds hVmem)).differentiableAt one_ne_zero
  have hsecd : HasFDerivAt (fun y : ℝ × ℝ => (y.1, Ψ y))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ Ψ (τ₀, σ₀))) (τ₀, σ₀) :=
    hasFDerivAt_fst.prodMk (hΨd.hasFDerivAt)
  have hcomp := HasFDerivAt.comp (τ₀, σ₀)
    (hGd.hasFDerivAt : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2)
      (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) (τ₀, Ψ (τ₀, σ₀)))
      (τ₀, Ψ (τ₀, σ₀))) hsecd
  have hfun : (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) ∘
      (fun y : ℝ × ℝ => (y.1, Ψ y)) = evLevel ψ a₀ b₀ Ψ := by
    funext y; rfl
  have hchain : HasFDerivAt (fun y : ℝ × ℝ => hFn ψ v (Ψ y))
      ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) (Ψ (τ₀, σ₀))) ∘SL
        (fderiv ℝ Ψ (τ₀, σ₀))) (τ₀, σ₀) :=
    HasFDerivAt.comp (τ₀, σ₀)
      (((contDiff_hFn ψ v).differentiable one_ne_zero).differentiableAt.hasFDerivAt)
      (hΨd.hasFDerivAt)
  have heq : (fun y : ℝ × ℝ => hFn ψ v (Ψ y)) =ᶠ[𝓝 (τ₀, σ₀)] (fun y : ℝ × ℝ => y.2) :=
    eventually_of_mem (hV.mem_nhds hVmem) (fun y hy => hg y hy)
  have hzero : ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) (Ψ (τ₀, σ₀)))
      ((fderiv ℝ Ψ (τ₀, σ₀)) (1, 0))) = 0 := by
    have h1 := congrArg (fun (T : (ℝ × ℝ) →L[ℝ] ℝ) => T (1, 0)) hchain.fderiv
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [← h1, heq.fderiv_eq, fderiv_snd]
    rfl
  have hbase : fderiv ℝ (evLevel ψ a₀ b₀ Ψ) (τ₀, σ₀)
      = (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) (τ₀, Ψ (τ₀, σ₀))) ∘SL
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (fderiv ℝ Ψ (τ₀, σ₀))) := by
    rw [← hfun]
    exact hcomp.fderiv
  rw [fderivWithin_of_isOpen hV hVmem, hbase]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    Prod.mk.injEq]
  rw [show ((ContinuousLinearMap.fst ℝ ℝ ℝ) (1, 0)) = (1 : ℝ) from rfl]
  rw [show (((1 : ℝ), (fderiv ℝ Ψ (τ₀, σ₀)) (1, 0)) : ℝ × (ℝ × ℝ))
      = (((1 : ℝ), (0 : ℝ × ℝ)) : ℝ × (ℝ × ℝ)) +
        (((0 : ℝ), (fderiv ℝ Ψ (τ₀, σ₀)) (1, 0)) : ℝ × (ℝ × ℝ)) from by
    ext <;> simp]
  rw [map_add]
  rw [fderiv_slice_inl (F := fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) hGd]
  rw [fderiv_slice_inr (F := fun p : ℝ × (ℝ × ℝ) => sH ψ a₀ b₀ p.1 p.2) hGd]
  dsimp only
  rw [show (fderiv ℝ (fun τ' : ℝ => sH ψ a₀ b₀ τ' (Ψ (τ₀, σ₀))) τ₀) (1 : ℝ)
      = deriv (fun τ' : ℝ => sH ψ a₀ b₀ τ' (Ψ (τ₀, σ₀))) τ₀ from rfl]
  rw [deriv_sH_fixed ha hb hab ψ (Ψ (τ₀, σ₀)) τ₀]
  rw [hΨmem, htang]
  simp only [smul_apply, smul_eq_mul]
  rw [show ((fderiv ℝ (fun x : ℝ × ℝ => hFn ψ v x) x₀)
      ((fderiv ℝ Ψ (τ₀, σ₀)) (1, 0))) = 0 by rw [← hΨmem]; exact hzero, mul_zero, add_zero]


end

end Work.Drive.Mono
