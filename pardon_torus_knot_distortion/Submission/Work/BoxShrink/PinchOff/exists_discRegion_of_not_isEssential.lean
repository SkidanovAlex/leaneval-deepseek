import Mathlib
import Submission.Work.SurgeryInvariance.All
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.Disk
import Submission.Work.Smooth.Plane.All
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.Schoenflies.All
import Submission.Work.TorusCover.Main
import Submission.Work.InnermostDisk.Defs
import Submission.Work.BoxShrink.Pinch.closure_V_translate_disjoint

/-!
# A simple inessential closed curve of a torus bounds an embedded disc

A simple closed curve `γ` on the surface `F = P.carrier` of a parametrised torus `P` which is
inessential (vanishing winding vector, `¬ IsEssential P γ`) bounds an embedded disc of the
surface whose boundary is exactly the image of `γ` — a `Work.SurgeryInvariance.DiscRegion P`.

The curve lifts to a `2π`-periodic simple closed plane curve `Λ` (a Jordan curve), whose bounded
side `V` projects *injectively* to `F`: the projection is a covering map, and two points of
`closure V` have the same image exactly when their difference is a lattice vector; the translate
disjointness `Work.BoxShrink.Pinch.closure_V_translate_disjoint` (with the simplicity of `γ`
supplying its hypothesis that the trace meets its translate only at the origin) rules out a
nonzero such difference.  Jordan–Schoenflies
(`Work.Smooth.Schoenflies.classicalInput`) fills the Jordan curve with an embedded disc inside
`closure V`, and its image in `F` is the required embedded disc.
-/

open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-! ## The identification `ℂ ≃ ℝ × ℝ` -/

/-- The real and imaginary parts of a complex number, as a point of the parameter plane. -/
def toR2 (z : ℂ) : ℝ × ℝ := (z.re, z.im)

/-- The complex number with the given real and imaginary parts. -/
def ofR2 (p : ℝ × ℝ) : ℂ := Complex.mk p.1 p.2

@[simp] theorem toR2_ofR2 (p : ℝ × ℝ) : toR2 (ofR2 p) = p := rfl

@[simp] theorem ofR2_toR2 (z : ℂ) : ofR2 (toR2 z) = z := rfl

theorem ofR2_injective : Function.Injective ofR2 := fun a b h => by
  have := congrArg toR2 h
  simpa using this

theorem toR2_injective : Function.Injective toR2 := fun a b h => by
  calc a = ofR2 (toR2 a) := (ofR2_toR2 a).symm
    _ = ofR2 (toR2 b) := by rw [h]
    _ = b := ofR2_toR2 b

@[simp] theorem ofR2_zero : ofR2 0 = 0 := rfl

theorem toR2_add (z w : ℂ) : toR2 (z + w) = toR2 z + toR2 w := by
  simp only [toR2, Complex.add_re, Complex.add_im, Prod.mk_add_mk]

theorem toR2_sub (z w : ℂ) : toR2 (z - w) = toR2 z - toR2 w := by
  simp only [toR2, Complex.sub_re, Complex.sub_im, Prod.mk_sub_mk]

theorem ofR2_add (p q : ℝ × ℝ) : ofR2 (p + q) = ofR2 p + ofR2 q := by
  apply toR2_injective
  simp only [toR2_add, toR2_ofR2]

theorem ofR2_sub (p q : ℝ × ℝ) : ofR2 (p - q) = ofR2 p - ofR2 q := by
  apply toR2_injective
  simp only [toR2_sub, toR2_ofR2]

theorem continuous_toR2 : Continuous toR2 :=
  Complex.continuous_re.prodMk Complex.continuous_im

theorem continuous_ofR2 : Continuous ofR2 := by
  have h : ofR2 = fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p
    apply Complex.ext
    · simp [ofR2, Complex.add_re, Complex.mul_re]
    · simp [ofR2, Complex.add_im, Complex.mul_im]
  rw [h]
  fun_prop

/-! ## Periodicity: two parameters giving the same point differ by a period -/

/-- **A `2π`-periodic map injective on one period is injective modulo `2π`.**  From
`f s = f t` one gets `s = t + k · 2π` for some integer `k`. -/
theorem eq_add_int_mul_of_periodic_injOn {α : Type*} {f : ℝ → α}
    (hf : Function.Periodic f (2 * Real.pi)) (hinj : Set.InjOn f (Set.Ico 0 (2 * Real.pi)))
    {s t : ℝ} (h : f s = f t) : ∃ k : ℤ, s = t + k * (2 * Real.pi) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have reduce : ∀ u : ℝ, ∃ u₀ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∃ k : ℤ,
      u = u₀ + k * (2 * Real.pi) := by
    intro u
    set n : ℤ := ⌊u / (2 * Real.pi)⌋ with hn
    refine ⟨u - (n : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, n, by ring⟩
    · have := (le_div_iff₀ hpi).mp (Int.floor_le (u / (2 * Real.pi)))
      linarith
    · have := (div_lt_iff₀ hpi).mp (Int.lt_floor_add_one (u / (2 * Real.pi)))
      linarith
  obtain ⟨s₀, hs₀, k, rfl⟩ := reduce s
  obtain ⟨t₀, ht₀, l, rfl⟩ := reduce t
  have hs : f (s₀ + (k : ℝ) * (2 * Real.pi)) = f s₀ := hf.int_mul k s₀
  have ht : f (t₀ + (l : ℝ) * (2 * Real.pi)) = f t₀ := hf.int_mul l t₀
  rw [hs, ht] at h
  have hst : s₀ = t₀ := hinj hs₀ ht₀ h
  refine ⟨k - l, ?_⟩
  rw [hst]
  push_cast
  ring

/-! ## The periodic lift of an inessential curve -/

/-- **An inessential closed curve of a torus admits a `2π`-periodic lift to the parameter
plane.** -/
theorem exists_periodic_lift {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (h : ¬ Work.CoreTopology.IsEssential P γ) :
    ∃ Λ : ℝ → ℝ × ℝ, Continuous Λ ∧ (∀ t : ℝ, P.psi (Λ t).1 (Λ t).2 = γ.γ t) ∧
      ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t := by
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  have hwind : L.winding = (0, 0) := by
    by_contra hne
    exact h ⟨L, hne⟩
  refine ⟨fun t => (L.Θ t, L.Φ t), L.contΘ.prodMk L.contΦ, fun t => L.lifts t, ?_⟩
  intro t
  have hp := L.period_shift_winding t
  rw [hwind] at hp
  exact Prod.ext (by simpa using hp.1) (by simpa using hp.2)

/-! ## The lift, as a closed plane curve -/

/-- The `2π`-periodic lift `Λ` of a closed curve, read as a closed plane curve. -/
def liftCurve (Λ : ℝ → ℝ × ℝ) (hc : Continuous Λ) (hp : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t) :
    Work.Smooth.Jordan.PlaneCurve where
  γ := fun t => ofR2 (Λ t)
  cont := continuous_ofR2.comp hc
  periodic := fun t => by
    show ofR2 (Λ (t + 2 * Real.pi)) = ofR2 (Λ t)
    rw [hp t]

@[simp] theorem liftCurve_apply (Λ : ℝ → ℝ × ℝ) (hc) (hp) (t : ℝ) :
    (liftCurve Λ hc hp).γ t = ofR2 (Λ t) := rfl

/-- The lift of a simple curve is a simple plane curve. -/
theorem liftCurve_isSimple {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (hsimple : Work.CoreTopology.IsSimple P γ)
    {Λ : ℝ → ℝ × ℝ} (hc : Continuous Λ) (hp : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t)
    (hlift : ∀ t : ℝ, P.psi (Λ t).1 (Λ t).2 = γ.γ t) :
    (liftCurve Λ hc hp).IsSimple := by
  intro s hs t ht hst
  have h1 : Λ s = Λ t := ofR2_injective hst
  have h2 : γ.γ s = γ.γ t := by rw [← hlift s, ← hlift t, h1]
  exact hsimple hs ht h2

/-! ## The trace of the lift meets its translates only at the origin -/

/-- **Simplicity forces the trace of the lift to be disjoint from its nonzero translates.**  If
`Λ` is a `2π`-periodic lift of the simple closed curve `γ`, and `z` is a nonzero vector whose
parameters lie in the period lattice, then the trace of `Λ` does not meet its translate by `z`. -/
theorem disjoint_trace_shift {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (hsimple : Work.CoreTopology.IsSimple P γ)
    {Λ : ℝ → ℝ × ℝ} (hc : Continuous Λ) (hp : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t)
    (hlift : ∀ t : ℝ, P.psi (Λ t).1 (Λ t).2 = γ.γ t)
    {z : ℂ} (hz : toR2 z ∈ Work.TorusCover.lattice) (hz0 : z ≠ 0) :
    Disjoint (Set.range (liftCurve Λ hc hp).γ)
      ((fun w : ℂ => w + z) '' Set.range (liftCurve Λ hc hp).γ) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨s, hs⟩ := hx
  obtain ⟨y, ⟨t, ht⟩, hyt⟩ := hx'
  have hs' : ofR2 (Λ s) = x := hs
  have ht' : ofR2 (Λ t) = y := ht
  have hseq : ofR2 (Λ s) = ofR2 (Λ t) + z := by
    rw [hs', ht']
    exact hyt.symm
  have h2 : Λ s = Λ t + toR2 z := by
    apply ofR2_injective
    rw [ofR2_add, ofR2_toR2]
    exact hseq
  -- hence `γ s = γ t`, so the parameters differ by a period
  have hγ : γ.γ s = γ.γ t := by
    rw [← hlift s, ← hlift t, h2]
    exact (Work.TorusCover.psiMap_eq_iff_param P).mpr (by simpa using hz)
  obtain ⟨k, hk⟩ := eq_add_int_mul_of_periodic_injOn γ.periodic hsimple hγ
  -- hence `Λ s = Λ t`, forcing `toR2 z = 0`
  have h3 : Λ s = Λ t := by
    rw [hk, (show Function.Periodic Λ (2 * Real.pi) from hp).int_mul k t]
  have h4 : toR2 z = 0 := by
    have h5 : Λ t + toR2 z = Λ t := by rw [← h2, h3]
    have := congrArg (fun p : ℝ × ℝ => p - Λ t) h5
    simpa using this
  exact hz0 (by rw [← ofR2_toR2 z, h4, ofR2_zero])

/-! ## The main theorem -/

theorem exists_discRegion_of_not_isEssential {P : Work.CoreTopology.ParamTorus}
    (γ : Work.CoreTopology.ClosedCurve P)
    (hsimple : Work.CoreTopology.IsSimple P γ)
    (hiness : ¬ Work.CoreTopology.IsEssential P γ) :
    ∃ D : Work.SurgeryInvariance.DiscRegion P, D.boundary = Set.range γ.γ := by
  obtain ⟨Λ, hΛcont, hΛlift, hΛper⟩ := exists_periodic_lift hiness
  set c : Work.Smooth.Jordan.PlaneCurve := liftCurve Λ hΛcont hΛper with hc
  have hcsimple : c.IsSimple := liftCurve_isSimple hsimple hΛcont hΛper hΛlift
  obtain ⟨h⟩ := Work.Smooth.Schoenflies.classicalInput c hcsimple
  -- The projection is injective on the closed bounded side of the lift.
  have hinjV : Set.InjOn (fun z : ℂ => Work.TorusCover.psiMap P.psi (toR2 z)) (closure h.V) := by
    intro x hx y hy hxy
    by_contra hne
    have hlat : toR2 (x - y) ∈ Work.TorusCover.lattice := by
      have h1 := (Work.TorusCover.psiMap_eq_iff_param P).mp hxy
      rwa [← toR2_sub] at h1
    have hz0 : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hdisj := Work.BoxShrink.Pinch.closure_V_translate_disjoint h.toPlaneSeparation hz0
      (disjoint_trace_shift hsimple hΛcont hΛper hΛlift hlat hz0)
    rw [Set.disjoint_left] at hdisj
    exact hdisj hx ⟨y, hy, by ring⟩
  -- The parametrisation of the disc.
  have heRcont : Continuous (fun z : Work.Smooth.Jordan.Disc =>
      Work.TorusCover.psiMap P.psi (toR2 (h.e z))) :=
    P.cont.comp (continuous_toR2.comp h.e.continuous)
  refine ⟨{ e := ⟨fun z => Work.TorusCover.psiMap P.psi (toR2 (h.e z)), heRcont⟩
            inj := ?_
            mem := ?_
            open_interior := ?_ }, ?_⟩
  · -- injectivity
    intro a b hab
    refine h.inj (hinjV ?_ ?_ hab)
    · rw [← h.range_e]; exact Set.mem_range_self a
    · rw [← h.range_e]; exact Set.mem_range_self b
  · -- the disc lies on the surface
    intro z
    exact P.psi_mem_carrier _ _
  · -- the interior is open in the surface
    unfold Work.SurgeryInvariance.IsOpenInCarrier
    have hVeq : h.V = h.e '' {z : Work.Smooth.Jordan.Disc | ‖(z : ℂ)‖ < 1} :=
      (Work.Smooth.Jordan.plane_schoenflies_openDisc_eq h).symm
    have himg : (fun z : Work.Smooth.Jordan.Disc =>
          Work.TorusCover.psiMap P.psi (toR2 (h.e z)))
        '' {z : Work.Smooth.Jordan.Disc | ‖(z : ℂ)‖ < 1}
        = Work.TorusCover.psiMap P.psi '' (toR2 '' h.V) := by
      have hcomp : (fun z : Work.Smooth.Jordan.Disc =>
            Work.TorusCover.psiMap P.psi (toR2 (h.e z)))
          = (Work.TorusCover.psiMap P.psi) ∘ (toR2 ∘ ⇑h.e) := rfl
      rw [hcomp, Set.image_comp, Set.image_comp, ← hVeq]
    change IsOpen (Subtype.val ⁻¹'
      ((fun z : Work.Smooth.Jordan.Disc =>
        Work.TorusCover.psiMap P.psi (toR2 (h.e z))) ''
        {z : Work.Smooth.Jordan.Disc | ‖(z : ℂ)‖ < 1}) : Set P.carrier)
    rw [himg]
    change IsOpen (Subtype.val ⁻¹' (Work.TorusCover.psiMap P.psi '' (toR2 '' h.V))
      : Set (Set.range (Work.TorusCover.psiMap P.psi)))
    have hA : IsOpen (toR2 '' h.V) := by
      have hpre : toR2 '' h.V = ofR2 ⁻¹' h.V := by
        ext p
        constructor
        · rintro ⟨z, hz, hzp⟩
          rw [← hzp]
          simpa only [Set.mem_preimage, ofR2_toR2] using hz
        · intro hp
          exact ⟨ofR2 p, hp, toR2_ofR2 p⟩
      rw [hpre]
      exact continuous_ofR2.isOpen_preimage h.V h.isOpen_V
    have hopen := (Work.TorusCover.isCoveringMap_psiMapToRange_param P).isLocalHomeomorph.isOpenMap
      (toR2 '' h.V) hA
    have hpre2 : (Subtype.val ⁻¹' (Work.TorusCover.psiMap P.psi '' (toR2 '' h.V))
        : Set (Set.range (Work.TorusCover.psiMap P.psi)))
        = Work.TorusCover.psiMapToRange P.psi '' (toR2 '' h.V) := by
      ext y
      constructor
      · rintro ⟨p, hp, hpy⟩
        exact ⟨p, hp, Subtype.ext hpy⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p, hp, rfl⟩
    rw [hpre2]
    exact hopen
  · -- the boundary is the curve
    show (fun z : Work.Smooth.Jordan.Disc => Work.TorusCover.psiMap P.psi (toR2 (h.e z)))
        '' {z : Work.Smooth.Jordan.Disc | ‖(z : ℂ)‖ = 1} = Set.range γ.γ
    ext x
    constructor
    · rintro ⟨z, hz, hzx⟩
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
      refine ⟨θ, ?_⟩
      rw [← hzx, ← hθ]
      change γ.γ θ = Work.TorusCover.psiMap P.psi
        (toR2 (h.e (Work.Smooth.Jordan.circlePoint θ)))
      rw [h.boundary θ, hc]
      show γ.γ θ = P.psi (Λ θ).1 (Λ θ).2
      exact (hΛlift θ).symm
    · rintro ⟨θ, rfl⟩
      refine ⟨Work.Smooth.Jordan.circlePoint θ, ?_, ?_⟩
      · show ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1
        rw [Work.Smooth.Jordan.circlePoint_coe]
        exact Complex.norm_exp_ofReal_mul_I θ
      · change Work.TorusCover.psiMap P.psi
          (toR2 (h.e (Work.Smooth.Jordan.circlePoint θ))) = γ.γ θ
        rw [h.boundary θ, hc]
        show P.psi (Λ θ).1 (Λ θ).2 = γ.γ θ
        exact hΛlift θ

end

end Work.BoxShrink.PinchOff
