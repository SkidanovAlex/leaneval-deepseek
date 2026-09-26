import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Main

/-!
# The winding span of a region, read off from the *lifted components*

This module proves the dictionary between the winding span of a region `X` of a parametrised torus
`P` and the *invariance directions* of the connected components of the lifted region
`X̃ = Xtilde P X ⊆ ℂ`:

> `WindingSpan P X` is the `ℚ`-span of the lattice vectors `(a, b)` for which some connected
> component of `X̃` is stable under translation by the lattice vector `periodPt a b`.

Concretely:

* `ComponentInvariant P X a b` — some component of `X̃` is stable under `z ↦ z + periodPt a b`;
* `mem_windingSpan_of_componentInvariant` — such a direction is realised by a single loop of `X`
  (the component is open, hence path connected, and the path from `z` to `z + periodPt a b` inside
  it straightens out to a closed curve of winding `(a,b)`, `exists_closedCurve_of_path`);
* `componentInvariant_windingOf` — conversely the winding vector of *any* loop of `X` is such a
  direction: the lifted loop runs from `liftMap L 0` to `liftMap L 0 + periodPt (winding)`, so both
  endpoints lie in one component, and the lattice invariance of `X̃` makes that component stable
  under the translation;
* `windingSpan_eq_span_invariantDirections` — the resulting **dictionary**:
  `W = span_ℚ { (a,b) : ComponentInvariant P X a b }`;
* `windingSpan_eq_bot_iff_no_componentInvariant` — `W = ⊥` exactly when no component of `X̃` is
  invariant in a nonzero direction;
* `windingSpan_eq_bot_of_components_bounded` — in particular `W = ⊥` if every component of `X̃` is
  bounded (this is the abstract form of the "bounded components" case of the parent chapter's
  dichotomy engine `IB/Main.lean`).

The point of the dictionary for the pinch-off area is that it converts the residual `DropCase`
(equivalently `KeyTameClosed`) into the *geometric* statement

> no connected component of the lifted box region `Ω̃ = {B < s}` is invariant under two independent
> lattice translations,

which is the form recorded in `DropStab.lean` (`dropCase_iff_invariantDirections`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **A component of the lifted region is invariant in the lattice direction `(a,b)`**: some
connected component of `X̃` is stable under the translation `z ↦ z + periodPt a b`.

(The witness `z` is required to lie in `X̃`, so that the statement is not vacuous.) -/
def ComponentInvariant (P : Work.CoreTopology.ParamTorus) (X : Set R3) (a b : ℤ) : Prop :=
  ∃ z ∈ Xtilde P X,
    (fun w : ℂ => w + periodPt a b) '' connectedComponentIn (Xtilde P X) z =
      connectedComponentIn (Xtilde P X) z

/-- **An invariance direction is realised by a single loop.**  If a connected component of `X̃` is
stable under `z ↦ z + periodPt a b`, then `X` carries a closed curve of winding `(a,b)`.

The component is an open set of `ℂ`, hence locally path connected and path connected; the path
inside it from a point `z` to `z + periodPt a b` is straightened out modulo the lattice into a
quasi-periodic curve, which projects to the required loop. -/
theorem mem_windingSpan_of_componentInvariant {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (hXc : X ⊆ P.carrier) (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) {a b : ℤ}
    (h : ComponentInvariant P X a b) :
    ((((a : ℤ) : ℚ), ((b : ℤ) : ℚ)) : ℚ × ℚ) ∈ Work.SurgeryInvariance.WindingSpan P X := by
  classical
  obtain ⟨z, hz, hinv⟩ := h
  set C : Set ℂ := connectedComponentIn (Xtilde P X) z with hCdef
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hCsub : C ⊆ Xtilde P X := connectedComponentIn_subset _ _
  have hzp : z + periodPt a b ∈ C := by
    have h1 : z + periodPt a b ∈ (fun w : ℂ => w + periodPt a b) '' C := ⟨z, hzC, rfl⟩
    rwa [hinv] at h1
  have hCopen : IsOpen C := (isOpen_Xtilde hXc hX).connectedComponentIn
  have hCpc : ∀ u ∈ C, ∀ v ∈ C, JoinedIn C u v := by
    haveI : LocallyPathConnectedSpace ↥C := hCopen.locallyPathConnectedSpace
    haveI : PreconnectedSpace ↥C :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponentIn
    intro u hu v hv
    rw [joinedIn_iff_joined hu hv, ← connectedComponent_eq_iff_joined,
      PreconnectedSpace.connectedComponent_eq_univ, PreconnectedSpace.connectedComponent_eq_univ]
  obtain ⟨p, hp⟩ := hCpc z hzC (z + periodPt a b) hzp
  set c : ℝ → ℂ := fun t => p.extend (t / (2 * Real.pi)) with hcdef
  have hcont : Continuous c := by
    rw [hcdef]
    exact p.extend.continuous.comp (continuous_id.div_const _)
  have hc0 : c 0 = z := by
    rw [hcdef]
    simp [Path.extend_zero]
  have hc2 : c (2 * Real.pi) = z + periodPt a b := by
    have h : (2 * Real.pi) / (2 * Real.pi) = 1 := by field_simp
    rw [hcdef]
    simp [h, Path.extend_one]
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), c t ∈ Xtilde P X := by
    intro t ht
    have ht1 : t / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg ht.1 (by positivity)
      · rw [div_le_one (by positivity)]; exact ht.2
    change p.extend (t / (2 * Real.pi)) ∈ Xtilde P X
    rw [Path.extend_apply p ht1]
    exact hCsub (hp ⟨t / (2 * Real.pi), ht1⟩)
  obtain ⟨γ, hγ, hw⟩ := exists_closedCurve_of_path c hcont hc0 hc2 hmem
  refine Submodule.subset_span ⟨γ, hγ, ?_⟩
  rw [hw]

/-- **The winding vector of a loop is an invariance direction.** -/
theorem componentInvariant_windingOf {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (γ : Work.CoreTopology.ClosedCurve P) (hγ : ∀ t : ℝ, γ.γ t ∈ X) :
    ComponentInvariant P X (Work.SurgeryInvariance.windingOf P γ).1
      (Work.SurgeryInvariance.windingOf P γ).2 := by
  classical
  set L : Work.CoreTopology.LiftOf P γ :=
    Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ) with hLdef
  set w : ℤ × ℤ := Work.SurgeryInvariance.windingOf P γ with hwdef
  have hwend : Work.SurgeryInvariance.windingOf P γ = L.winding :=
    Work.SurgeryInvariance.windingOf_eq P γ L
  have hw_eq : w = L.winding := by rw [hwdef, hwend]
  have hpath_mem : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), liftMap L t ∈ Xtilde P X := by
    intro t _ht
    show planePsi P (liftMap L t) ∈ X
    rw [planePsi_liftMap]
    exact hγ t
  refine ⟨liftMap L 0, hpath_mem 0 ⟨le_refl 0, by positivity⟩, ?_⟩
  have himg_pre : IsPreconnected ((fun t : ℝ => liftMap L t) '' Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isPreconnected_Icc.image _ (continuous_liftMap L).continuousOn
  have hsub : (fun t : ℝ => liftMap L t) '' Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ Xtilde P X := by
    rintro y ⟨t, ht, rfl⟩
    exact hpath_mem t ht
  have hsame : liftMap L (2 * Real.pi) ∈ connectedComponentIn (Xtilde P X) (liftMap L 0) :=
    (himg_pre.subset_connectedComponentIn ⟨0, ⟨le_refl 0, by positivity⟩, rfl⟩ hsub)
      ⟨2 * Real.pi, ⟨by positivity, le_refl _⟩, rfl⟩
  have hshift : liftMap L (2 * Real.pi) = liftMap L 0 + periodPt w.1 w.2 := by
    have hspec := L.winding_spec
    have h1 : L.Θ (2 * Real.pi) = L.Θ 0 + (w.1 : ℝ) * (2 * Real.pi) := by
      rw [hw_eq]; exact hspec.1
    have h2 : L.Φ (2 * Real.pi) = L.Φ 0 + (w.2 : ℝ) * (2 * Real.pi) := by
      rw [hw_eq]; exact hspec.2
    apply Complex.ext <;> simp [liftMap, h1, h2, periodPt]
  have hInv : ∀ z v : ℂ, v ∈ periodLattice → (z + v ∈ Xtilde P X ↔ z ∈ Xtilde P X) :=
    fun z v hv => Xtilde_add_periodLattice P X z v hv
  have hshmem : periodPt w.1 w.2 ∈ periodLattice := ⟨(w.1, w.2), rfl⟩
  have hcompw : connectedComponentIn (Xtilde P X) (liftMap L (2 * Real.pi)) =
      (fun y : ℂ => y + periodPt w.1 w.2) '' connectedComponentIn (Xtilde P X) (liftMap L 0) := by
    have h := connectedComponentIn_add hInv hshmem (hpath_mem 0 ⟨le_refl 0, by positivity⟩)
    rwa [← hshift] at h
  rw [← hcompw, ← connectedComponentIn_eq hsame]

/-- **The dictionary**: the winding span is the span of the invariance directions of the lifted
components. -/
theorem windingSpan_eq_span_invariantDirections {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (hXc : X ⊆ P.carrier) (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) :
    Work.SurgeryInvariance.WindingSpan P X =
      Submodule.span ℚ
        {v : ℚ × ℚ | ∃ a b : ℤ, v = ((a : ℚ), (b : ℚ)) ∧ ComponentInvariant P X a b} := by
  apply le_antisymm
  · rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
    rintro v ⟨γ, hγ, rfl⟩
    exact Submodule.subset_span
      ⟨(Work.SurgeryInvariance.windingOf P γ).1, (Work.SurgeryInvariance.windingOf P γ).2,
        rfl, componentInvariant_windingOf γ hγ⟩
  · rw [Submodule.span_le]
    rintro v ⟨a, b, rfl, h⟩
    exact mem_windingSpan_of_componentInvariant hXc hX h

/-- **A region is inessential exactly when no component of its lift is invariant in a nonzero
direction.** -/
theorem windingSpan_eq_bot_iff_no_componentInvariant {P : Work.CoreTopology.ParamTorus}
    {X : Set R3} (hXc : X ⊆ P.carrier) (hX : Work.SurgeryInvariance.IsOpenInCarrier P X) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ ↔
      ∀ a b : ℤ, ComponentInvariant P X a b → a = 0 ∧ b = 0 := by
  constructor
  · intro hbot a b hab
    have hmem := mem_windingSpan_of_componentInvariant hXc hX hab
    rw [hbot, Submodule.mem_bot] at hmem
    have hzero : ((a : ℤ), (b : ℤ)) = 0 :=
      (Work.SurgeryInvariance.intPair_cast_eq_zero_iff (a, b)).mp (by simpa using hmem)
    exact ⟨by simpa using congrArg Prod.fst hzero, by simpa using congrArg Prod.snd hzero⟩
  · intro h
    rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_eq_bot]
    rintro v ⟨γ, hγ, rfl⟩
    obtain ⟨h1, h2⟩ := h _ _ (componentInvariant_windingOf γ hγ)
    simp [h1, h2]

/-- **If every component of the lift is bounded, the region is inessential.**

This is the abstract form of the "bounded components" half of the dichotomy engine
`windingSpan_bot_or_top_aux`: a bounded set cannot be stable under a nonzero translation, and
`windingSpan_eq_bot_iff_no_componentInvariant` converts that into the vanishing of the span. -/
theorem windingSpan_eq_bot_of_components_bounded {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    (hXc : X ⊆ P.carrier) (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    (hbdd : ∀ z : ℂ, Bornology.IsBounded (connectedComponentIn (Xtilde P X) z)) :
    Work.SurgeryInvariance.WindingSpan P X = ⊥ := by
  rw [windingSpan_eq_bot_iff_no_componentInvariant hXc hX]
  intro a b hab
  by_contra hne
  push_neg at hne
  have hne' : (a, b) ≠ (0, 0) := by
    intro h
    exact hne (by simpa using congrArg Prod.fst h) (by simpa using congrArg Prod.snd h)
  have hshift : periodPt a b ≠ 0 := periodPt_ne_zero hne'
  obtain ⟨z, hz, hinv⟩ := hab
  set C : Set ℂ := connectedComponentIn (Xtilde P X) z with hCdef
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hiter : ∀ n : ℕ, z + (n : ℂ) * periodPt a b ∈ C := by
    intro n
    induction n with
    | zero => simpa using hzC
    | succ n ih =>
        have hmem : z + (n : ℂ) * periodPt a b + periodPt a b
            ∈ (fun y : ℂ => y + periodPt a b) '' C := ⟨_, ih, rfl⟩
        rw [hinv] at hmem
        have heq : z + (((n + 1 : ℕ) : ℂ)) * periodPt a b
            = z + (n : ℂ) * periodPt a b + periodPt a b := by push_cast; ring
        rwa [heq]
  have hnorm_pos : (0 : ℝ) < ‖periodPt a b‖ := norm_pos_iff.mpr hshift
  obtain ⟨R, hR⟩ := (hbdd z).subset_closedBall (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖z‖) / ‖periodPt a b‖)
  have hmem := hiter n
  have hball := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  have hlow : (n : ℝ) * ‖periodPt a b‖ - ‖z‖ ≤ ‖z + (n : ℂ) * periodPt a b‖ := by
    have h1 : ‖(n : ℂ) * periodPt a b‖
        ≤ ‖z + (n : ℂ) * periodPt a b‖ + ‖z‖ := by
      calc ‖(n : ℂ) * periodPt a b‖
          = ‖(z + (n : ℂ) * periodPt a b) - z‖ := by ring_nf
        _ ≤ ‖z + (n : ℂ) * periodPt a b‖ + ‖z‖ := norm_sub_le _ _
    rw [norm_mul, Complex.norm_natCast] at h1
    linarith
  have hgt : R < (n : ℝ) * ‖periodPt a b‖ - ‖z‖ := by
    rw [div_lt_iff₀ hnorm_pos] at hn
    linarith
  linarith

/-- **A region all of whose lifted components are invariant in a single direction is at most
one-dimensional.**  This is the direction of the dictionary used to *bound* `finrank W(X)` from
above: it suffices to exhibit one line `ℚ ∙ d` which contains every invariance direction. -/
theorem finrank_windingSpan_le_one_of_single_direction {P : Work.CoreTopology.ParamTorus}
    {X : Set R3} (hXc : X ⊆ P.carrier) (hX : Work.SurgeryInvariance.IsOpenInCarrier P X)
    {d : ℚ × ℚ}
    (h : ∀ a b : ℤ, ComponentInvariant P X a b → ∃ c : ℚ, ((a : ℚ), (b : ℚ)) = c • d) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X) ≤ 1 := by
  have hsub : Work.SurgeryInvariance.WindingSpan P X ≤ ℚ ∙ d := by
    rw [windingSpan_eq_span_invariantDirections hXc hX, Submodule.span_le]
    rintro v ⟨a, b, rfl, hab⟩
    obtain ⟨c, hc⟩ := h a b hab
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  rcases eq_or_ne d 0 with hd | hd
  · have hbot : ℚ ∙ d = ⊥ :=
      Submodule.eq_bot_iff _ |>.mpr (fun x hx => by
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        simp [hd])
    rw [hbot] at hsub
    have hfin := Submodule.finrank_mono hsub
    rw [finrank_bot] at hfin
    omega
  · calc Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P X)
        ≤ Module.finrank ℚ ↥(ℚ ∙ d) := Submodule.finrank_mono hsub
      _ = 1 := finrank_span_singleton hd
      _ ≤ 1 := le_refl 1

end

end Work.BoxShrink.PinchOff
