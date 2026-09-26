import Mathlib
import Submission.Work.Smooth.OneManifold.Basic

/-!
# From the repaired local-arc hypothesis to the local `1`-manifold structure

`isLocallyEuclidean_of_isLocalArcEmbedding`: if `Z ⊆ F` carries local arc descriptions that are
*open* maps onto the pieces of `Z` they cut out (`Work.Smooth.OneManifold.IsLocalArcEmbedding`),
then `Z` is locally Euclidean of dimension one: every point of `Z` has a neighbourhood in `Z`
homeomorphic to `ℝ`.

The local arc `ρ : I → Z` of the hypothesis restricts to a homeomorphism of an interval
`(s₀ - ε, s₀ + ε) ⊆ I` onto the relatively open set `W ∩ Z` cut out by the openness clause; that
homeomorphism, composed with `ℝ ≃ₜ (s₀ - ε, s₀ + ε)`, is the required chart.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-! ## Two elementary homeomorphisms of intervals -/

/-- `ℝ ≃ₜ ↥(Ioo (-ε) ε)`, sending `0` to `0` (the rescaled arctangent). -/
def homeomorphIooNeg (ε : ℝ) (hε : 0 < ε) : ℝ ≃ₜ ↥(Set.Ioo (-ε) ε) :=
  Work.Smooth.SphereJordan.LocalArc.homeomorphIoo ε hε

@[simp] theorem homeomorphIooNeg_zero (ε : ℝ) (hε : 0 < ε) :
    homeomorphIooNeg ε hε 0 = ⟨0, ⟨by linarith, by linarith⟩⟩ :=
  Work.Smooth.SphereJordan.LocalArc.homeomorphIoo_zero ε hε

/-- Translation of the interval `Ioo (-ε) ε` onto `Ioo (s - ε) (s + ε)`. -/
def homeomorphIooShift (s ε : ℝ) : ↥(Set.Ioo (-ε) ε) ≃ₜ ↥(Set.Ioo (s - ε) (s + ε)) where
  toFun t := ⟨s + (t : ℝ), by
    obtain ⟨h1, h2⟩ := t.2
    exact ⟨by linarith, by linarith⟩⟩
  invFun y := ⟨(y : ℝ) - s, by
    obtain ⟨h1, h2⟩ := y.2
    exact ⟨by linarith, by linarith⟩⟩
  left_inv t := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := Continuous.subtype_mk (continuous_const.add continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (continuous_subtype_val.sub continuous_const) _

@[simp] theorem homeomorphIooShift_apply (s ε : ℝ) (t : ↥(Set.Ioo (-ε) ε)) :
    (homeomorphIooShift s ε t : ℝ) = s + (t : ℝ) := rfl

/-- `ℝ ≃ₜ ↥(Ioo (s - ε) (s + ε))`, sending `0` to `s`. -/
def homeomorphIooCentre (s ε : ℝ) (hε : 0 < ε) : ℝ ≃ₜ ↥(Set.Ioo (s - ε) (s + ε)) :=
  (homeomorphIooNeg ε hε).trans (homeomorphIooShift s ε)

@[simp] theorem homeomorphIooCentre_zero (s ε : ℝ) (hε : 0 < ε) :
    (homeomorphIooCentre s ε hε 0 : ℝ) = s := by
  have h := homeomorphIooNeg_zero ε hε
  show (homeomorphIooShift s ε (homeomorphIooNeg ε hε 0) : ℝ) = s
  rw [h, homeomorphIooShift_apply]
  ring

/-! ## The bridge -/

theorem isLocallyEuclidean_of_isLocalArcEmbedding (ψ : Submission.Diffeo) {Z : Set R3}
    (hZ : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier)
    (h : IsLocalArcEmbedding ψ Z) : IsLocallyEuclidean Z := by
  intro x
  obtain ⟨U, I, s₀, ρ, _hU, hIopen, _hxU, hs₀I, hcont, hρs₀, hinj, hρI, hopen⟩ := h x.1 x.2
  -- a symmetric interval around `s₀` inside `I`
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hIopen.mem_nhds hs₀I)
  set S : Set ℝ := Set.Ioo (s₀ - ε) (s₀ + ε) with hSdef
  have hSsub : S ⊆ I := by
    intro t ht
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hs₀S : s₀ ∈ S := ⟨by linarith, by linarith⟩
  -- the relatively open piece of `Z` cut out by the arc
  obtain ⟨W, hW, hWZ⟩ := hopen S isOpen_Ioo
  have hWS : ρ '' S = W ∩ Z := by
    have hSI : S ∩ I = S := Set.inter_eq_left.mpr hSsub
    rw [hWZ, hSI]
  -- membership facts about `ρ` on `I` and on `S`
  have hρI' : ∀ s ∈ I, ρ s ∈ U ∧ ρ s ∈ Z := by
    intro s hs
    have h : ρ s ∈ ρ '' I := ⟨s, hs, rfl⟩
    rwa [hρI] at h
  have hρW : ∀ s ∈ S, ρ s ∈ W := by
    intro s hs
    have h : ρ s ∈ ρ '' S := ⟨s, hs, rfl⟩
    rw [hWS] at h
    exact h.1
  -- the neighbourhood of `x` in `Z`
  set V : Set Z := {y : Z | (y : R3) ∈ W} with hVdef
  have hVopen : IsOpen V := isOpenInSet_of_isOpenInCarrier hZ hW
  have hxV : x ∈ V := by
    show (x : R3) ∈ W
    rw [← hρs₀]
    exact hρW s₀ hs₀S
  -- the parametrisation of `V` by `S`
  let f : ↥S → ↥V := fun s =>
    ⟨⟨ρ (s : ℝ), (hρI' (s : ℝ) (hSsub s.2)).2⟩, hρW (s : ℝ) s.2⟩
  have hf_apply : ∀ s : ↥S, (f s).1.1 = ρ (s : ℝ) := fun s => rfl
  have hf_inj : Function.Injective f := by
    intro s t hst
    have h : ρ (s : ℝ) = ρ (t : ℝ) := by
      have h' := congrArg (fun y : ↥V => y.1.1) hst
      simpa only [hf_apply] using h'
    exact Subtype.ext (hinj (hSsub s.2) (hSsub t.2) h)
  have hf_surj : Function.Surjective f := by
    intro y
    have hy : y.1.1 ∈ W ∩ Z := ⟨y.2, y.1.2⟩
    rw [← hWS] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    refine ⟨⟨s, hs⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hsy
  have hf_cont : Continuous f := by
    have h1 : Continuous fun s : ↥S => ρ (s : ℝ) := (hcont.mono hSsub).domRestrict
    exact Continuous.subtype_mk
      (Continuous.subtype_mk h1 fun s => (hρI' (s : ℝ) (hSsub s.2)).2) fun s => hρW (s : ℝ) s.2
  have hf_open : IsOpenMap f := by
    intro O hO
    obtain ⟨O', hO'open, hO'eq⟩ := isOpen_induced_iff.mp hO
    obtain ⟨W', hW', hW'Z⟩ := hopen (O' ∩ S) (hO'open.inter isOpen_Ioo)
    have hW'ZS : ρ '' (O' ∩ S) = W' ∩ Z := by
      have hSI : (O' ∩ S) ∩ I = O' ∩ S := Set.inter_eq_left.mpr (fun t ht => hSsub ht.2)
      rw [hW'Z, hSI]
    have hmemO : ∀ s : ↥S, s ∈ O ↔ (s : ℝ) ∈ O' := by
      intro s
      rw [← hO'eq]
      exact Iff.rfl
    have himg : f '' O = (Subtype.val ⁻¹' (Subtype.val ⁻¹' (W' ∩ Z)) : Set ↥V) := by
      ext y
      constructor
      · rintro ⟨s, hs, rfl⟩
        have hs' : (s : ℝ) ∈ O' ∩ S := ⟨(hmemO s).mp hs, s.2⟩
        have : ρ (s : ℝ) ∈ ρ '' (O' ∩ S) := ⟨(s : ℝ), hs', rfl⟩
        rw [hW'ZS] at this
        exact this
      · intro hy
        have hy' : y.1.1 ∈ ρ '' (O' ∩ S) := by
          rw [hW'ZS]
          exact hy
        obtain ⟨s, hs, hsy⟩ := hy'
        refine ⟨⟨s, hs.2⟩, ?_, ?_⟩
        · exact (hmemO ⟨s, hs.2⟩).mpr hs.1
        · apply Subtype.ext
          apply Subtype.ext
          exact hsy
    rw [himg]
    exact (isOpenInSet_inter_of_isOpenInCarrier hZ hW').preimage continuous_subtype_val
  -- the chart
  let e₂ : ↥S ≃ₜ ↥V :=
    (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).toHomeomorphOfContinuousOpen hf_cont hf_open
  have he₂_s₀ : e₂ ⟨s₀, hs₀S⟩ = ⟨x, hxV⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    show ρ s₀ = (x : R3)
    exact hρs₀
  refine ⟨{ V := V
            isOpen_V := hVopen
            mem_V := hxV
            homeo := (homeomorphIooCentre s₀ ε hε).trans e₂
            homeo_zero := ?_ }⟩
  have h0 : (homeomorphIooCentre s₀ ε hε) 0 = ⟨s₀, hs₀S⟩ :=
    Subtype.ext (homeomorphIooCentre_zero s₀ ε hε)
  rw [Homeomorph.trans_apply, h0, he₂_s₀]

/-- **Conversely, the local `1`-manifold structure gives the repaired arc hypothesis**: the chart
homeomorphism `ℝ ≃ₜ V` of the local Euclidean structure, read in `ℝ³`, is a local arc which is
open onto the piece of `Z` it cuts out.

Together with `isLocallyEuclidean_of_isLocalArcEmbedding` this says that on a subset `Z` of the
surface the repaired local arc hypothesis `IsLocalArcEmbedding ψ Z` and the local `1`-manifold
structure `IsLocallyEuclidean Z` are *equivalent*.  The difference from
`Work.Smooth.Morse.IsLocalArc` is exactly the (non-)embedding condition of the local arc, which
fails at the crossing point of the figure eight. -/
theorem isLocalArcEmbedding_of_isLocallyEuclidean (ψ : Submission.Diffeo) {Z : Set R3}
    (hZ : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier) (h : IsLocallyEuclidean Z) :
    IsLocalArcEmbedding ψ Z := by
  rintro x hx
  obtain ⟨c⟩ := h ⟨x, hx⟩
  obtain ⟨U₀, hU₀open, hU₀⟩ := isOpen_induced_iff.mp c.isOpen_V
  refine ⟨U₀, Set.univ, 0, fun s => ((c.homeo s : c.V) : Z), ?_, isOpen_univ, ?_,
    Set.mem_univ _, ?_, ?_, ?_, ?_, ?_⟩
  · show IsOpen (Subtype.val ⁻¹' U₀ : Set (Work.Smooth.Morse.torus ψ).carrier)
    exact hU₀open.preimage continuous_subtype_val
  · show x ∈ U₀
    have : (⟨x, hx⟩ : Z) ∈ Subtype.val ⁻¹' U₀ := by rw [hU₀]; exact c.mem_V
    exact this
  · exact ((continuous_subtype_val.comp (continuous_subtype_val.comp
      c.homeo.continuous))).continuousOn
  · show ((c.homeo 0 : c.V) : Z) = x
    rw [c.homeo_zero]
  · intro s _ t _ hst
    exact c.homeo.injective (Subtype.ext (Subtype.ext hst))
  · ext z
    simp only [Set.mem_image, Set.mem_univ, true_and, and_true, Set.mem_inter_iff]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨?_, ((c.homeo s : c.V) : Z).2⟩
      have : ((c.homeo s : c.V) : Z) ∈ Subtype.val ⁻¹' U₀ := by
        rw [hU₀]; exact (c.homeo s).2
      exact this
    · rintro ⟨hzU, hzZ⟩
      have hmem : (⟨z, hzZ⟩ : Z) ∈ c.V := by
        have : (⟨z, hzZ⟩ : Z) ∈ Subtype.val ⁻¹' U₀ := hzU
        rwa [hU₀] at this
      obtain ⟨s, hs⟩ := c.homeo.surjective ⟨⟨z, hzZ⟩, hmem⟩
      refine ⟨s, ?_⟩
      rw [hs]
  · intro O hO
    have h1 : IsOpen ((Subtype.val : ↥c.V → ↥Z) '' (c.homeo '' O)) :=
      c.isOpen_V.isOpenMap_subtype_val _ (c.homeo.isOpenMap O hO)
    obtain ⟨W₀, hW₀open, hW₀⟩ := isOpen_induced_iff.mp h1
    refine ⟨W₀, ?_, ?_⟩
    · show IsOpen (Subtype.val ⁻¹' W₀ : Set (Work.Smooth.Morse.torus ψ).carrier)
      exact hW₀open.preimage continuous_subtype_val
    · ext z
      simp only [Set.mem_image, Set.mem_univ, true_and, and_true, Set.mem_inter_iff]
      constructor
      · rintro ⟨hzW, hzZ⟩
        have h2 : (⟨z, hzZ⟩ : Z) ∈ (Subtype.val : ↥c.V → ↥Z) '' (c.homeo '' O) := by
          have h3 : (⟨z, hzZ⟩ : Z) ∈ Subtype.val ⁻¹' W₀ := hzW
          rwa [hW₀] at h3
        obtain ⟨y, hy, hyz⟩ := h2
        obtain ⟨s, hs, hsy⟩ := hy
        refine ⟨s, hs, ?_⟩
        have h4 : (y : R3) = z := congrArg Subtype.val hyz
        show ((c.homeo s : c.V) : R3) = z
        rw [hsy]
        exact h4
      · rintro ⟨s, hs, rfl⟩
        refine ⟨?_, ((c.homeo s : c.V) : Z).2⟩
        have h2 : ((c.homeo s : c.V) : Z) ∈ Subtype.val ⁻¹' W₀ := by
          rw [hW₀]
          exact ⟨c.homeo s, ⟨s, hs, rfl⟩, rfl⟩
        exact h2
end

end Work.Smooth.OneManifold
