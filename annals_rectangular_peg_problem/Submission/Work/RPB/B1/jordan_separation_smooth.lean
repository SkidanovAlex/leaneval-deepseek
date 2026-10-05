import Mathlib
import Submission.Work.RPB.Port.Drive.smooth_jordan_separation
import Submission.Work.RPB.Port.Drive.PolarTwist.isSmoothEmbedding_of_injective_deriv_ne_zero

set_option autoImplicit false

namespace Work.RPB.B1

open scoped Topology Manifold ContDiff
open Manifold

/-!
# Jordan separation for a smooth embedded closed curve

Let `u : ℝ → ℂ` be a `C^∞` curve which is `2π`-periodic, injective modulo `2π` and an immersion
(`deriv u t ≠ 0`).  Then `u` parametrises an embedded circle in the plane, and the complement of its
image splits into a bounded and an unbounded preconnected open piece.

The proof descends `u` through the quotient map `Circle.exp : ℝ → Circle` to an embedded circle
`γ : Circle → ℝ × ℝ` (via the linear homeomorphism `Complex.equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ`),
applies the ported theorem `Work.RPB.Port.Drive.smooth_jordan_separation` to `γ`, and transports the
two pieces back to `ℂ`.  The `Circle.exp`-parametrisation of `γ` is smooth because that of `u` is,
and its derivative is nowhere zero because `deriv u` is nowhere zero and `ℂ ≃ ℝ × ℝ` is linear.
-/

/-- **Descent through a quotient map.**  A continuous function on the source which is constant on the
fibres of a quotient map induces a continuous function on the quotient. -/
private theorem exists_continuous_descend {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} (hf : Topology.IsQuotientMap f) {g : X → Z}
    (hg : Continuous g) (h : g.FactorsThrough f) :
    ∃ G : Y → Z, Continuous G ∧ G ∘ f = g := by
  classical
  refine ⟨fun y => g (Classical.choose (hf.surjective y)), ?_, ?_⟩
  · rw [hf.continuous_iff]
    have hGf : (fun y => g (Classical.choose (hf.surjective y))) ∘ f = g :=
      funext fun x => h (Classical.choose_spec (hf.surjective (f x)))
    rw [hGf]; exact hg
  · funext x
    exact h (Classical.choose_spec (hf.surjective (f x)))

theorem jordan_separation_smooth (u : ℝ → ℂ) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t)
    (hinj : ∀ t t', u t = u t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    (himm : ∀ t, deriv u t ≠ 0) :
    ∃ ins out : Set ℂ,
      IsOpen ins ∧ IsOpen out ∧ IsPreconnected ins ∧ IsPreconnected out ∧
        Bornology.IsBounded ins ∧ ¬ Bornology.IsBounded out ∧ ins.Nonempty ∧
          (Set.range u)ᶜ = ins ∪ out ∧ Disjoint ins out := by
  -- The linear homeomorphism `ℂ ≃ ℝ × ℝ`.
  set e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM with he
  -- Periodicity by integer multiples of `2π`.
  have hper_z : ∀ (m : ℤ) (t : ℝ), u (t + ↑m * (2 * Real.pi)) = u t :=
    fun m t => (Function.Periodic.int_mul hper m) t
  -- `u` is constant on the fibres of `Circle.exp`.
  have hfac : (fun t : ℝ => e (u t)).FactorsThrough (⇑Circle.exp : ℝ → Circle) := by
    intro a b hab
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hab
    rw [hm]
    exact congrArg e (hper_z m b)
  have hf : Topology.IsQuotientMap (⇑Circle.exp : ℝ → Circle) :=
    IsOpenMap.isQuotientMap isLocalHomeomorph_circleExp.isOpenMap Circle.exp.continuous
      Circle.exp_surjective
  -- The descended map.
  obtain ⟨γ, hγcont, hγcomp⟩ :=
    exists_continuous_descend hf (e.continuous.comp hu.continuous) hfac
  have hγ_exp : ∀ t : ℝ, γ (Circle.exp t) = e (u t) := fun t => by
    have := congrFun hγcomp t
    simpa [Function.comp_def] using this
  -- Injectivity of the descended map.
  have hγinj : Function.Injective γ := by
    intro z₁ z₂ h
    obtain ⟨t₁, rfl⟩ := Circle.exp_surjective z₁
    obtain ⟨t₂, rfl⟩ := Circle.exp_surjective z₂
    have h2 : e (u t₁) = e (u t₂) := by rw [← hγ_exp t₁, ← hγ_exp t₂]; exact h
    have h3 : u t₁ = u t₂ := e.injective h2
    obtain ⟨m, hm⟩ := hinj t₁ t₂ h3
    rw [hm]
    exact Circle.exp_eq_exp.mpr ⟨-m, by push_cast; ring⟩
  -- Smoothness of the `Circle.exp`-parametrisation.
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => γ (Circle.exp t)) := by
    have hfun : (fun t : ℝ => γ (Circle.exp t)) = fun t => e (u t) := funext hγ_exp
    rw [hfun]
    simpa [Function.comp_def] using e.contDiff.comp (hu.of_le (by simp))
  -- Non-vanishing of the derivative.
  have hderiv : ∀ t : ℝ, deriv (fun u : ℝ => γ (Circle.exp u)) t ≠ 0 := by
    intro t
    have hfun : (fun u : ℝ => γ (Circle.exp u)) = fun s => e (u s) := funext hγ_exp
    rw [hfun]
    have hU : HasDerivAt u (deriv u t) t :=
      (hu.differentiable (by simp)).differentiableAt.hasDerivAt
    have hder : HasDerivAt (fun s : ℝ => e (u s)) (e (deriv u t)) t := by
      have h1 := (e : ℂ →L[ℝ] ℝ × ℝ).hasFDerivAt.comp_hasDerivAt t hU
      simpa [Function.comp_def] using h1
    rw [hder.deriv]
    intro h0
    exact himm t (e.injective (by simpa using h0))
  -- The descended curve is a smooth embedding.
  have hemb : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ :=
    Work.RPB.Port.Drive.PolarTwist.isSmoothEmbedding_of_injective_deriv_ne_zero
      γ hγcont hγinj hsmooth hderiv
  obtain ⟨ins, out, hinsopen, houtopen, hinsconn, houtconn, hinsbdd, houtbdd, hinsne, _houtne,
    hcover, hdisj, _hcl1, _hcl2⟩ := Work.RPB.Port.Drive.smooth_jordan_separation γ hemb
  -- Transport back to `ℂ`.
  have hpre : ∀ s : Set (ℝ × ℝ), (⇑e.symm) '' s = (⇑e) ⁻¹' s := by
    intro s
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, by simpa using hx, by simp⟩
  have himg : ∀ s : Set (ℝ × ℝ), (⇑e) '' ((⇑e.symm) '' s) = s := by
    intro s
    rw [Set.image_image]
    have hcomp : (fun x : ℝ × ℝ => e (e.symm x)) = id := by funext y; simp
    rw [hcomp, Set.image_id]
  refine ⟨e.symm '' ins, e.symm '' out, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpre ins]; exact hinsopen.preimage e.continuous
  · rw [hpre out]; exact houtopen.preimage e.continuous
  · exact (hinsconn.isConnected.isPreconnected).image (⇑e.symm) e.symm.continuous.continuousOn
  · exact (houtconn.isConnected.isPreconnected).image (⇑e.symm) e.symm.continuous.continuousOn
  · exact ((e.symm : ℝ × ℝ →L[ℝ] ℂ).lipschitzWith).isBounded_image hinsbdd
  · intro hb
    have h1 : Bornology.IsBounded (⇑e '' ((⇑e.symm) '' out)) :=
      ((e : ℂ →L[ℝ] ℝ × ℝ).lipschitzWith).isBounded_image hb
    rw [himg out] at h1
    exact houtbdd h1
  · exact hinsne.image (⇑e.symm)
  · ext x
    have hxr : x ∈ Set.range u ↔ e x ∈ Set.range γ := by
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨Circle.exp t, by rw [hγ_exp t]⟩
      · rintro ⟨z, hz⟩
        obtain ⟨t, rfl⟩ := Circle.exp_surjective z
        refine ⟨t, ?_⟩
        have h1 : γ (Circle.exp t) = e (u t) := hγ_exp t
        have h2 : e (u t) = e x := by rw [← h1, hz]
        exact e.injective h2
    have key : x ∈ (Set.range u)ᶜ ↔ e x ∈ (Set.range γ)ᶜ := by
      rw [Set.mem_compl_iff, Set.mem_compl_iff]
      exact not_congr hxr
    rw [key, hcover, Set.mem_union, Set.mem_union]
    constructor
    · rintro (h | h)
      · left; exact ⟨e x, h, by simp⟩
      · right; exact ⟨e x, h, by simp⟩
    · rintro (⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩)
      · left
        have hxy : e x = y := by rw [← hyx, e.apply_symm_apply]
        rwa [hxy]
      · right
        have hxy : e x = y := by rw [← hyx, e.apply_symm_apply]
        rwa [hxy]
  · rw [Set.disjoint_left] at hdisj ⊢
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := e.symm.injective (by rw [hax, hbx])
    subst hab
    exact hdisj ha hb

end Work.RPB.B1
