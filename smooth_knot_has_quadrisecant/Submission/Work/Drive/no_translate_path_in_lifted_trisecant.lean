import Mathlib
import Submission.Work.Drive.strip_defs
import Submission.ComponentNullHomotopy
import Submission.ComponentIntervalSide
import Submission.SecantSpace

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

noncomputable section

set_option maxHeartbeats 1000000

namespace Work.Drive

/-!
# No translate path in the lifted trisecant locus

`Work.Drive.no_translate_path_in_lifted_trisecant`: for a smooth knot `r` which is
quadrisecant-free and in (transverse) general position, no point `z` of the lifted trisecant
locus `liftedTrisecant r ⊆ ℝ × (0, period)` is joined *inside* `liftedTrisecant r` to its
translate `(z.1 + period, z.2)`.

Equivalently: the trisecant set `O = trisecantSet r` contains no *essential* loop (no loop
whose lift to the universal cover of the band of secants is an open path), which is exactly
what the two structural inputs of the workspace give:

* `trisecantComponent_dichotomy` — every connected component of `O` is an open interval or a
  circle; interval components are contractible, so a loop inside one is null-homotopic;
* `circular_component_curve_nullHomotopic` — the embedded circle of a *circular* component is
  null-homotopic in the band (Kuperberg's winding measurement: a circular component of `O`
  does not wind).

Given either of these, the projected loop `ℓ = stripSecantClass ∘ γ` of a hypothetical path
`γ` from `z` to `(z.1 + period, z.2)` comes with a free homotopy to a constant with moving
basepoint; the covering argument then lifts the homotopy square through the double cover
`mobiusCover : OrderedPairs → OpenMobius` (`Submission/SecantSpace.lean`) and the first
parameter through `ℝ → AddCircle period`, and concludes `period = 0`.
-/

/-! ## Covering-space helper -/

/-- **Uniqueness of lifts** along a covering map, for maps from a simply connected,
locally path connected space. -/
lemma covering_lift_unique {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E]
    [TopologicalSpace X] [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    {p : E → X} (cov : IsCoveringMap p) {f : C(A, X)} {a₀ : A} {e₀ : E}
    (he : p e₀ = f a₀) {F₁ F₂ : C(A, E)} (h₁ : F₁ a₀ = e₀) (h₁' : p ∘ ⇑F₁ = ⇑f)
    (h₂ : F₂ a₀ = e₀) (h₂' : p ∘ ⇑F₂ = ⇑f) : F₁ = F₂ :=
  (cov.existsUnique_continuousMap_lifts f a₀ e₀ he).unique ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩

/-- Translating a real parameter by one period does not change its class in the circle. -/
lemma addCircle_coe_add_period (x : ℝ) : (((x + period : ℝ)) : AddCircle period) = (x : AddCircle period) := by
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- **The straight-line homotopy of the open unit interval**: convexity of `(0,1)` keeps
`(1-s) * x + s * x₀` inside `(0,1)`. -/
noncomputable def intervalLineMap (x₀ x : OpenRealInterval 0 1) (s : I) : OpenRealInterval 0 1 :=
  ⟨(1 - (s : ℝ)) * (x : ℝ) + (s : ℝ) * (x₀ : ℝ), by
    have h := (convex_Ioo (0 : ℝ) 1).lineMap_mem (x := (x : ℝ)) (y := (x₀ : ℝ)) x.2 x₀.2 s.2
    simpa [AffineMap.lineMap_apply_module, smul_eq_mul] using h⟩

lemma intervalLineMap_zero (x₀ x : OpenRealInterval 0 1) : intervalLineMap x₀ x 0 = x := by
  refine Subtype.ext ?_
  show (1 - ((0 : I) : ℝ)) * (x : ℝ) + ((0 : I) : ℝ) * (x₀ : ℝ) = (x : ℝ)
  simp

lemma intervalLineMap_one (x₀ x : OpenRealInterval 0 1) : intervalLineMap x₀ x 1 = x₀ := by
  refine Subtype.ext ?_
  show (1 - ((1 : I) : ℝ)) * (x : ℝ) + ((1 : I) : ℝ) * (x₀ : ℝ) = (x₀ : ℝ)
  simp

lemma continuous_intervalLineMap (x₀ : OpenRealInterval 0 1) :
    Continuous fun p : OpenRealInterval 0 1 × I => intervalLineMap x₀ p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun p : OpenRealInterval 0 1 × I =>
    (1 - (p.2 : ℝ)) * (p.1 : ℝ) + (p.2 : ℝ) * (x₀ : ℝ)
  fun_prop

/-- The secant class of a strip point depends only on the two parameter classes. -/
lemma stripSecantClass_eq_of_eq {p q : ℝ × ℝ} (h0 : 0 < p.2) (h1 : p.2 < period)
    (h0' : 0 < q.2) (h1' : q.2 < period)
    (h1e : ((p.1 : ℝ) : AddCircle period) = ((q.1 : ℝ) : AddCircle period))
    (h2e : (((p.1 + p.2 : ℝ)) : AddCircle period) = (((q.1 + q.2 : ℝ)) : AddCircle period)) :
    stripSecantClass p h0 h1 = stripSecantClass q h0' h1' := by
  rw [stripSecantClass_eq_mobiusCover, stripSecantClass_eq_mobiusCover]
  exact congrArg mobiusCover (Subtype.ext (Prod.ext h1e h2e))

/-! ## The covering argument

A path `γ` in the strip from `z` to its translate `(z.1 + period, z.2)`, whose
projected loop `ℓ` carries a null-homotopy with moving basepoint, is
impossible: lifting the whole homotopy square to the ordered double cover of the
band, and then the first parameter to `ℝ`, contradicts `period ≠ 0`. -/

lemma covering_contradiction (γ : C(I, ℝ × ℝ)) (z : ℝ × ℝ)
    (hz0 : 0 < z.2) (hz1 : z.2 < period)
    (hγ0 : γ 0 = z) (hγ1 : γ 1 = (z.1 + period, z.2))
    (hpos : ∀ t : I, 0 < (γ t).2) (hlt : ∀ t : I, (γ t).2 < period)
    (ℓ : C(I, OpenMobius))
    (hℓ : ∀ t : I, ℓ t = stripSecantClass (γ t) (hpos t) (hlt t))
    {K : C(I × I, OpenMobius)} {m₀ : OpenMobius}
    (hK0 : ∀ t : I, K (0, t) = ℓ t) (hK1 : ∀ t : I, K (1, t) = m₀)
    (hKper : ∀ s : I, K (s, 0) = K (s, 1)) : False := by
  classical
  haveI hIconn : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  haveI hIlpc : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  haveI hI2conn : ContractibleSpace (I × I) := inferInstance
  haveI hI2lpc : LocallyPathConnectedSpace (I × I) := inferInstance
  -- the ordered lift of the projected loop
  have hucont : Continuous fun t : I => stripPair (γ t) (hpos t) (hlt t) :=
    Continuous.subtype_mk (p := fun q : AddCircle period × AddCircle period => q.1 ≠ q.2)
      (((AddCircle.continuous_mk' period).comp (continuous_fst.comp γ.continuous)).prodMk
        ((AddCircle.continuous_mk' period).comp
          ((continuous_fst.comp γ.continuous).add (continuous_snd.comp γ.continuous))))
      (fun t => coe_ne_coe_of_lt (hpos t) (hlt t))
  let u : C(I, OrderedPairs) := ⟨fun t : I => stripPair (γ t) (hpos t) (hlt t), hucont⟩
  have hu_lift : mobiusCover ∘ ⇑u = ⇑ℓ := by
    funext t
    rw [Function.comp_apply]
    show mobiusCover (stripPair (γ t) (hpos t) (hlt t)) = ℓ t
    rw [← stripSecantClass_eq_mobiusCover, ← hℓ t]
  let u₀ : OrderedPairs := stripPair z hz0 hz1
  have hu0 : u 0 = u₀ := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (((γ 0).1 : ℝ) : AddCircle period) = ((z.1 : ℝ) : AddCircle period)
      rw [hγ0]
    · show ((((γ 0).1 + (γ 0).2 : ℝ)) : AddCircle period) = (((z.1 + z.2 : ℝ)) : AddCircle period)
      rw [hγ0]
  have hu1 : u 1 = u 0 := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (((γ 1).1 : ℝ) : AddCircle period) = (((γ 0).1 : ℝ) : AddCircle period)
      rw [hγ1, hγ0, AddCircle.coe_add, AddCircle.coe_period, add_zero]
    · show ((((γ 1).1 + (γ 1).2 : ℝ)) : AddCircle period) =
        ((((γ 0).1 + (γ 0).2 : ℝ)) : AddCircle period)
      rw [hγ1, hγ0]
      show ((((z.1 + period) + z.2 : ℝ)) : AddCircle period) = (((z.1 + z.2 : ℝ)) : AddCircle period)
      rw [show (z.1 + period) + z.2 = (z.1 + z.2) + period by ring, AddCircle.coe_add,
        AddCircle.coe_period, add_zero]
  -- the homotopy square lifted to the double cover
  have hKcompat : mobiusCover u₀ = K (0, 0) := by
    have h1 : mobiusCover (u 0) = ℓ 0 := congrFun hu_lift 0
    rw [← hu0, h1, hK0 0]
  obtain ⟨Kt, ⟨hKt0, hKtproj⟩, -⟩ :=
    (isCoveringMap_mobiusCover).existsUnique_continuousMap_lifts K (0, 0) u₀ hKcompat
  have hKt_at : ∀ p : I × I, mobiusCover (Kt p) = K p := fun p => by
    simpa using congrFun hKtproj p
  -- the vertical edge at the origin is the ordered lift `u`
  have hFK : (⟨fun t : I => Kt (0, t), by fun_prop⟩ : C(I, OrderedPairs)) = u := by
    refine covering_lift_unique isCoveringMap_mobiusCover (f := ℓ) (a₀ := (0 : I))
      (e₀ := u₀) ?_ ?_ ?_ ?_ ?_
    · rw [hKcompat, hK0 0]
    · exact hKt0
    · funext t
      simpa using (hKt_at (0, t)).trans (hK0 t)
    · exact hu0
    · exact hu_lift
  have hFKt : ∀ t : I, Kt (0, t) = u t := fun t => by
    simpa using congrFun (congrArg DFunLike.coe hFK) t
  have hcorner : Kt (0, 1) = Kt (0, 0) := by
    calc Kt (0, 1) = u 1 := hFKt 1
      _ = u 0 := hu1
      _ = u₀ := hu0
      _ = Kt (0, 0) := hKt0.symm
  -- the two horizontal edges of the lifted square agree
  have hedge : (⟨fun s : I => Kt (s, 0), by fun_prop⟩ : C(I, OrderedPairs)) =
      ⟨fun s : I => Kt (s, 1), by fun_prop⟩ := by
    refine covering_lift_unique isCoveringMap_mobiusCover
      (f := ⟨fun s : I => K (s, 0), by fun_prop⟩) (a₀ := (0 : I)) (e₀ := u₀) ?_ ?_ ?_ ?_ ?_
    · change mobiusCover u₀ = K (0, 0)
      rw [hKcompat]
    · exact hKt0
    · funext s
      simpa using hKt_at (s, 0)
    · show Kt (0, 1) = u₀
      rw [hcorner]
      exact hKt0
    · funext s
      simpa using (hKt_at (s, 1)).trans (hKper s).symm
  have hKt_edge : ∀ s : I, Kt (s, 0) = Kt (s, 1) := fun s => by
    simpa using congrFun (congrArg DFunLike.coe hedge) s
  -- the far vertical edge of the lifted square is constant
  have htop : (⟨fun t : I => Kt (1, t), by fun_prop⟩ : C(I, OrderedPairs)) =
      (⟨fun _ : I => Kt (1, 0), continuous_const⟩ : C(I, OrderedPairs)) := by
    refine covering_lift_unique isCoveringMap_mobiusCover
      (f := (⟨fun _ : I => m₀, continuous_const⟩ : C(I, OpenMobius))) (a₀ := (0 : I))
      (e₀ := Kt (1, 0)) ?_ ?_ ?_ ?_ ?_
    · simpa using (hKt_at (1, 0)).trans (hK1 0)
    · rfl
    · funext t
      simpa using (hKt_at (1, t)).trans (hK1 t)
    · rfl
    · funext t
      simpa using (hKt_at (1, 0)).trans (hK1 0)
  have hKt_vert : ∀ t : I, Kt (1, t) = Kt (1, 0) := fun t => by
    simpa using congrFun (congrArg DFunLike.coe htop) t
  -- the first parameter of the ordered pair, lifted to `ℝ`
  have hproj : Continuous fun q : OrderedPairs => q.1.1 :=
    continuous_fst.comp continuous_subtype_val
  let Ψ : C(I × I, AddCircle period) := ⟨fun p : I × I => (Kt p).1.1, hproj.comp Kt.continuous⟩
  have hΨcompat : ((z.1 : ℝ) : AddCircle period) = Ψ (0, 0) := by
    show ((z.1 : ℝ) : AddCircle period) = (Kt (0, 0)).1.1
    rw [hKt0]
    rfl
  have covR : IsCoveringMap (fun x : ℝ => (x : AddCircle period)) :=
    AddCircle.isCoveringMap_coe period
  obtain ⟨Ψt, ⟨hΨt0, hΨtproj⟩, -⟩ :=
    covR.existsUnique_continuousMap_lifts Ψ (0, 0) z.1 hΨcompat
  have hΨt_at : ∀ p : I × I, ((Ψt p : ℝ) : AddCircle period) = Ψ p := fun p => by
    simpa using congrFun hΨtproj p
  -- the initial edge of the lifted square is the first parameter of the strip path
  have hfirst : (⟨fun t : I => Ψt (0, t), by fun_prop⟩ : C(I, ℝ)) =
      (⟨fun t : I => (γ t).1, continuous_fst.comp γ.continuous⟩ : C(I, ℝ)) := by
    refine covering_lift_unique covR (f := ⟨fun t : I => Ψ (0, t), by fun_prop⟩) (a₀ := (0 : I))
      (e₀ := z.1) ?_ ?_ ?_ ?_ ?_
    · exact hΨcompat
    · exact hΨt0
    · funext t
      simpa using hΨt_at (0, t)
    · show (γ 0).1 = z.1
      rw [hγ0]
    · funext t
      show ((γ t).1 : AddCircle period) = Ψ (0, t)
      rw [show Ψ (0, t) = (Kt (0, t)).1.1 from rfl, hFKt t]
      rfl
  have hΨt01 : Ψt (0, 1) = z.1 + period := by
    have h1 : Ψt (0, 1) = (γ 1).1 := by
      simpa using congrFun (congrArg DFunLike.coe hfirst) 1
    rw [hγ1] at h1
    exact h1
  -- the translated edge: `s ↦ Ψ̃ (s,1)` is `s ↦ Ψ̃ (s,0) + period`
  have hshift : (⟨fun s : I => Ψt (s, 1), by fun_prop⟩ : C(I, ℝ)) =
      (⟨fun s : I => Ψt (s, 0) + period, by fun_prop⟩ : C(I, ℝ)) := by
    refine covering_lift_unique covR (f := ⟨fun s : I => Ψ (s, 0), by fun_prop⟩) (a₀ := (0 : I))
      (e₀ := z.1 + period) ?_ ?_ ?_ ?_ ?_
    · show (((z.1 + period : ℝ)) : AddCircle period) = Ψ (0, 0)
      rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]
      exact hΨcompat
    · exact hΨt01
    · funext s
      show ((Ψt (s, 1) : ℝ) : AddCircle period) = Ψ (s, 0)
      rw [hΨt_at (s, 1)]
      show (Kt (s, 1)).1.1 = (Kt (s, 0)).1.1
      rw [← hKt_edge s]
    · show Ψt (0, 0) + period = z.1 + period
      rw [hΨt0]
    · funext s
      show (((Ψt (s, 0) + period : ℝ)) : AddCircle period) = Ψ (s, 0)
      rw [AddCircle.coe_add, AddCircle.coe_period, add_zero, hΨt_at (s, 0)]
  have hshift1 : Ψt (1, 1) = Ψt (1, 0) + period := by
    simpa using congrFun (congrArg DFunLike.coe hshift) 1
  -- the far edge is constant
  have hconst : (⟨fun t : I => Ψt (1, t), by fun_prop⟩ : C(I, ℝ)) =
      (⟨fun _ : I => Ψt (1, 0), continuous_const⟩ : C(I, ℝ)) := by
    refine covering_lift_unique covR
      (f := (⟨fun _ : I => Ψ (1, 0), continuous_const⟩ : C(I, AddCircle period)))
      (a₀ := (0 : I)) (e₀ := Ψt (1, 0)) ?_ ?_ ?_ ?_ ?_
    · exact hΨt_at (1, 0)
    · rfl
    · funext t
      show ((Ψt (1, t) : ℝ) : AddCircle period) = Ψ (1, 0)
      rw [hΨt_at (1, t)]
      show (Kt (1, t)).1.1 = (Kt (1, 0)).1.1
      rw [hKt_vert t]
    · rfl
    · funext t
      simpa using hΨt_at (1, 0)
  have hconst1 : Ψt (1, 1) = Ψt (1, 0) := by
    simpa using congrFun (congrArg DFunLike.coe hconst) 1
  rw [hshift1] at hconst1
  have hzero : period = 0 := by linarith
  exact absurd hzero (ne_of_gt period_pos)

/-! ## The main theorem -/

theorem no_translate_path_in_lifted_trisecant {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hq : LeanEval.KnotTheory.Quadrisecant.QuadrisecantFree r)
    (hg : LeanEval.KnotTheory.Quadrisecant.TorusGeneralPositionTransverse r)
    {z : ℝ × ℝ} (hz : z ∈ LeanEval.KnotTheory.Quadrisecant.liftedTrisecant r) :
    ¬ JoinedIn (LeanEval.KnotTheory.Quadrisecant.liftedTrisecant r) z
      (z.1 + LeanEval.KnotTheory.Quadrisecant.period, z.2) := by
  classical
  rintro ⟨γ, hγmem⟩
  obtain ⟨hz0, hz1, hzc⟩ := hz
  have hγ0 : γ 0 = z := γ.source
  have hγ1 : γ 1 = (z.1 + period, z.2) := γ.target
  have hpos : ∀ t : I, 0 < (γ t).2 := fun t => (hγmem t).choose
  have hlt : ∀ t : I, (γ t).2 < period := fun t => (hγmem t).choose_spec.choose
  have hmem : ∀ t : I, stripSecantClass (γ t) (hpos t) (hlt t) ∈ trisecantSet r :=
    fun t => (hγmem t).choose_spec.choose_spec
  -- the projected loop
  let ℓ : C(I, OpenMobius) :=
    ⟨fun t : I => stripSecantClass (γ t) (hpos t) (hlt t),
      continuous_stripSecantClass.comp
        (Continuous.subtype_mk γ.continuous (fun t => ⟨hpos t, hlt t⟩))⟩
  have hℓ : ∀ t : I, ℓ t = stripSecantClass (γ t) (hpos t) (hlt t) := fun t => rfl
  -- the component of the trisecant set containing the loop
  let c₀ : OSub r := ⟨stripSecantClass z hz0 hz1, hzc⟩
  let L : I → OSub r := fun t => ⟨stripSecantClass (γ t) (hpos t) (hlt t), hmem t⟩
  have hLcont : Continuous L :=
    Continuous.subtype_mk ℓ.continuous (fun t => hmem t)
  have hℓ01 : ℓ 0 = ℓ 1 := by
    rw [hℓ 0, hℓ 1]
    refine stripSecantClass_eq_of_eq (hpos 0) (hlt 0) (hpos 1) (hlt 1) ?_ ?_
    · show (((γ 0).1 : ℝ) : AddCircle period) = (((γ 1).1 : ℝ) : AddCircle period)
      rw [hγ0, hγ1, addCircle_coe_add_period]
    · show ((((γ 0).1 + (γ 0).2 : ℝ)) : AddCircle period) =
        ((((γ 1).1 + (γ 1).2 : ℝ)) : AddCircle period)
      rw [hγ0, hγ1]
      show (((z.1 + z.2 : ℝ)) : AddCircle period) =
        ((((z.1 + period) + z.2 : ℝ)) : AddCircle period)
      rw [show (z.1 + period) + z.2 = (z.1 + z.2) + period by ring, addCircle_coe_add_period]
  have hL0 : L 0 = c₀ := by
    refine Subtype.ext (stripSecantClass_eq_of_eq (hpos 0) (hlt 0) hz0 hz1 ?_ ?_)
    · show (((γ 0).1 : ℝ) : AddCircle period) = ((z.1 : ℝ) : AddCircle period)
      rw [hγ0]
    · show ((((γ 0).1 + (γ 0).2 : ℝ)) : AddCircle period) = (((z.1 + z.2 : ℝ)) : AddCircle period)
      rw [hγ0]
  have hL1 : L 1 = c₀ := by
    refine Subtype.ext (stripSecantClass_eq_of_eq (hpos 1) (hlt 1) hz0 hz1 ?_ ?_)
    · show (((γ 1).1 : ℝ) : AddCircle period) = ((z.1 : ℝ) : AddCircle period)
      rw [hγ1, addCircle_coe_add_period]
    · show ((((γ 1).1 + (γ 1).2 : ℝ)) : AddCircle period) = (((z.1 + z.2 : ℝ)) : AddCircle period)
      rw [hγ1]
      show ((((z.1 + period) + z.2 : ℝ)) : AddCircle period) = (((z.1 + z.2 : ℝ)) : AddCircle period)
      rw [show (z.1 + period) + z.2 = (z.1 + z.2) + period by ring, addCircle_coe_add_period]
  have hrange : Set.range L ⊆ connectedComponent c₀ :=
    IsPreconnected.subset_connectedComponent (isPreconnected_range hLcont) ⟨0, hL0⟩
  -- the loop, as a path in the component
  let G : C(I, TrisecantComponent r c₀) :=
    ⟨fun t : I => ⟨L t, hrange (Set.mem_range_self t)⟩,
      Continuous.subtype_mk hLcont (fun t => hrange (Set.mem_range_self t))⟩
  have hG01 : G 0 = G 1 := by
    refine Subtype.ext ?_
    change L 0 = L 1
    rw [hL0, hL1]
  -- reduction to a free homotopy of `ℓ` with moving basepoint
  suffices hgoal : ∀ (K : C(I × I, OpenMobius)) (m₀ : OpenMobius),
      (∀ t : I, K (0, t) = ℓ t) → (∀ t : I, K (1, t) = m₀) →
      (∀ s : I, K (s, 0) = K (s, 1)) → False by
    rcases trisecantComponent_dichotomy hr hq hg c₀ with hcase | hcase
    · -- INTERVAL COMPONENT
      obtain ⟨e⟩ := hcase
      let f : C(I, OpenRealInterval 0 1) :=
        ⟨fun t : I => e.symm (G t), e.symm.continuous.comp G.continuous⟩
      have hf01 : f 0 = f 1 := by
        show e.symm (G 0) = e.symm (G 1)
        rw [hG01]
      have hlin_cont : Continuous fun p : I × I => intervalLineMap (f 0) (f p.2) p.1 :=
        (continuous_intervalLineMap (f 0)).comp
          ((f.continuous.comp continuous_snd).prodMk continuous_fst)
      let K : C(I × I, OpenMobius) :=
        ⟨fun p : I × I =>
            (((e (intervalLineMap (f 0) (f p.2) p.1) : TrisecantComponent r c₀) : OSub r) : OpenMobius),
          continuous_subtype_val.comp (continuous_subtype_val.comp (e.continuous.comp hlin_cont))⟩
      have hK_apply : ∀ p : I × I, K p =
          (((e (intervalLineMap (f 0) (f p.2) p.1) : TrisecantComponent r c₀) : OSub r) : OpenMobius) :=
        fun p => rfl
      have hK0 : ∀ t : I, K (0, t) = ℓ t := by
        intro t
        rw [hK_apply ((0 : I), t), intervalLineMap_zero]
        show (((e (f t) : TrisecantComponent r c₀) : OSub r) : OpenMobius) = ℓ t
        rw [show e (f t) = G t from e.apply_symm_apply (G t)]
        exact (hℓ t).symm
      have hK1 : ∀ t : I, K (1, t) = K (1, 0) := by
        intro t
        rw [hK_apply ((1 : I), t), hK_apply ((1 : I), 0)]
        show (((e (intervalLineMap (f 0) (f t) (1 : I)) : TrisecantComponent r c₀) : OSub r) :
              OpenMobius)
            = (((e (intervalLineMap (f 0) (f 0) (1 : I)) : TrisecantComponent r c₀) : OSub r) :
              OpenMobius)
        rw [intervalLineMap_one, intervalLineMap_one]
      have hKper : ∀ s : I, K (s, 0) = K (s, 1) := by
        intro s
        rw [hK_apply (s, 0), hK_apply (s, 1), ← hf01]
      exact hgoal K (K (1, 0)) hK0 hK1 hKper
    · -- CIRCULAR COMPONENT
      obtain ⟨χ⟩ := hcase
      obtain ⟨γc, hnull, himg⟩ := circular_component_curve_nullHomotopic hr hq hg c₀ χ
      obtain ⟨m₀, hHom⟩ := hnull
      obtain ⟨H⟩ := hHom
      have hℓmem : ∀ t : I, ℓ t ∈ γc.image := by
        intro t
        rw [himg]
        exact ⟨L t, hrange (Set.mem_range_self t), (hℓ t).symm⟩
      have hemb : Topology.IsEmbedding (γc.toCircleMap : Circle → OpenMobius) :=
        (γc.toCircleMap.continuous.isClosedEmbedding γc.injective').isEmbedding
      have hfcont : Continuous fun t : I => Function.invFun γc.toCircleMap (ℓ t) := by
        refine (Topology.IsEmbedding.continuous_iff hemb).mpr ?_
        have hfe : ⇑γc.toCircleMap ∘ (fun t : I => Function.invFun γc.toCircleMap (ℓ t)) = ⇑ℓ := by
          funext t
          exact Function.invFun_eq (hℓmem t)
        rw [hfe]
        exact ℓ.continuous
      let f : C(I, Circle) := ⟨fun t : I => Function.invFun γc.toCircleMap (ℓ t), hfcont⟩
      have hffac : ∀ t : I, γc.toCircleMap (f t) = ℓ t := fun t =>
        Function.invFun_eq (hℓmem t)
      have hf01 : f 0 = f 1 := by
        refine γc.injective' ?_
        rw [hffac 0, hffac 1, hℓ01]
      let K : C(I × I, OpenMobius) :=
        ⟨fun p : I × I => H (p.1, f p.2),
          H.continuous.comp (continuous_fst.prodMk (f.continuous.comp continuous_snd))⟩
      have hK0 : ∀ t : I, K (0, t) = ℓ t := by
        intro t
        show H (((0 : I), f t)) = ℓ t
        rw [ContinuousMap.Homotopy.apply_zero]
        exact hffac t
      have hK1 : ∀ t : I, K (1, t) = m₀ := by
        intro t
        show H (((1 : I), f t)) = m₀
        rw [ContinuousMap.Homotopy.apply_one]
        rfl
      have hKper : ∀ s : I, K (s, 0) = K (s, 1) := by
        intro s
        show H (s, f 0) = H (s, f 1)
        rw [hf01]
      exact hgoal K m₀ hK0 hK1 hKper
  intro K m₀ hK0 hK1 hKper
  exact covering_contradiction γ.toContinuousMap z hz0 hz1 hγ0 hγ1 hpos hlt ℓ hℓ hK0 hK1 hKper

end Work.Drive
