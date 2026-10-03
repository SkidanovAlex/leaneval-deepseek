import Mathlib

/-!
# Covering maps onto simply connected spaces

Elementary infrastructure for `Work.BasinSC.basin_sc` (Shishikura, Lemma 5.2).

* `IsCoveringMap.bijective_of_simplyConnected`: a covering map whose total space is path connected
  and whose base is simply connected and locally path connected is a homeomorphism.
* `IsCoveringMapOn.bijective_of_simplyConnected`: the same for a covering *on* an open subset,
  in the shape in which the rest of the development uses it.
* `isSimplyConnected_of_isCoveringMapOn`: the resulting transfer of simple connectivity, i.e. the
  "no critical point" half of Riemann–Hurwitz-lite (F4 in the plan).
-/

open Set Metric Filter Topology

namespace Work.BasinSC

/-- **A covering map with path connected total space onto a simply connected, locally path
connected space is bijective** (hence, being open, a homeomorphism).

Proof: the identity of the base lifts through the covering to a section `F` with `p ∘ F = id`;
along a path in `E` from a fixed lift `e₀` to an arbitrary `e`, the path together with `F ∘ (p ∘ γ)`
are two continuous lifts of the same path in the base starting at `e₀`, so they coincide, whence
`F (p e) = e`. -/
theorem covering_bijective_of_simplyConnected {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [PathConnectedSpace E] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {p : E → X} (hp : IsCoveringMap p) :
    Function.Bijective p := by
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  have hex := (hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) (p e₀) e₀ rfl).exists
  obtain ⟨F, hF⟩ := hex
  have hF₀ : F (p e₀) = e₀ := hF.1
  have hFp : ∀ x : X, p (F x) = x := fun x => congr_fun hF.2 x
  have hFe : ∀ e : E, F (p e) = e := by
    intro e
    have hγ : Path e₀ e := PathConnectedSpace.somePath e₀ e
    let γ : C(unitInterval, X) := ⟨fun t => p (hγ t), hp.continuous.comp hγ.continuous⟩
    have hγval : ∀ t, γ t = p (hγ t) := fun t => rfl
    have hγzero : γ 0 = p e₀ := by rw [hγval, hγ.source]
    have k1 : (fun t : unitInterval => F (γ t)) = ⇑(hp.liftPath γ e₀ hγzero) := by
      rw [hp.eq_liftPath_iff]
      exact ⟨F.continuous.comp γ.continuous, funext fun t => hFp (γ t), by simp [hF₀, hγzero]⟩
    have k2 : (fun t : unitInterval => hγ t) = ⇑(hp.liftPath γ e₀ hγzero) := by
      rw [hp.eq_liftPath_iff]
      exact ⟨hγ.continuous, funext fun t => (hγval t).symm, hγ.source⟩
    have h2 : (fun t : unitInterval => F (γ t)) 1 = (fun t : unitInterval => hγ t) 1 := by
      rw [k1, ← k2]
    simpa [hγval, hγ.target] using h2
  exact ⟨fun a b hab => by rw [← hFe a, ← hFe b, hab], fun x => ⟨F x, hFp x⟩⟩

/-- **Simple connectivity transfers along a homeomorphism.** -/
theorem simplyConnectedSpace_of_homeomorph {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : E ≃ₜ X) [SimplyConnectedSpace X] : SimplyConnectedSpace E :=
  (e.toHomotopyEquiv.simplyConnectedSpace_iff).mpr inferInstance

/-- **Simple connectivity transfers from the base of a covering to its total space.** -/
theorem simplyConnectedSpace_of_isCoveringMap {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [PathConnectedSpace E] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {p : E → X} (hp : IsCoveringMap p) :
    SimplyConnectedSpace E := by
  have hbij := covering_bijective_of_simplyConnected hp
  have key : ∀ s : Set X, IsOpen ((Equiv.ofBijective p hbij) ⁻¹' s) ↔ IsOpen s := by
    intro s
    show IsOpen (p ⁻¹' s) ↔ IsOpen s
    exact ⟨fun h => by
        have h' := hp.isOpenMap (p ⁻¹' s) h
        rwa [Set.image_preimage_eq s hbij.2] at h',
      fun h => h.preimage hp.continuous⟩
  exact simplyConnectedSpace_of_homeomorph ((Equiv.ofBijective p hbij).toHomeomorph key)

/-- **A covering *on* an open subset of `ℂ` whose base is simply connected has simply connected
total space.**  Concretely: `p : ℂ → ℂ` maps the open set `V'` onto the open simply connected set
`V`, `V'` is connected, and `IsCoveringMapOn (p|V') V`.  Then `V'` is simply connected.

Proof: the identity of `V` lifts through the covering to a continuous section `F : V → V'` of `p`;
the set of points `z ∈ V'` with `F (p z) = z` is clopen (open: `p` is injective near `z` because a
covering is a local homeomorphism; closed: continuity in a `T₂` space) and non-empty, hence all of
`V'`.  So `p` is injective on `V'` and, with surjectivity, a homeomorphism `V' ≅ V` with inverse
`F`. -/
theorem simplyConnected_of_isCoveringMapOn {V V' : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVsc : SimplyConnectedSpace ↥V) (hV'o : IsOpen V') (hV'c : IsConnected V')
    {p : ℂ → ℂ} (hmaps : MapsTo p V' V) (hcov : IsCoveringMapOn (fun z : ↥V' => p z) V)
    (hsurj : V ⊆ p '' V') : SimplyConnectedSpace ↥V' := by
  haveI : LocallyPathConnectedSpace ↥V := hVo.locallyPathConnectedSpace
  have hpcont : Continuous fun z : ↥V' => p z := by
    have hpre : (fun z : ↥V' => p z) ⁻¹' V = Set.univ := by
      ext z; exact ⟨fun _ => trivial, fun _ => hmaps z.2⟩
    rw [← continuousOn_univ, ← hpre]
    exact hcov.continuousOn
  have hqcont : Continuous fun z : ↥V' => (⟨p z, hmaps z.2⟩ : ↥V) := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact hpcont
  obtain ⟨a₀, ha₀V⟩ := hVne
  obtain ⟨e₀, he₀V', he₀⟩ := hsurj ha₀V
  obtain ⟨F, hF⟩ := (hcov.existsUnique_continuousMap_lifts
    (⟨fun v : ↥V => (v : ℂ), continuous_subtype_val⟩ : C(↥V, ℂ))
    (a₀ := (⟨a₀, ha₀V⟩ : ↥V)) (e₀ := (⟨e₀, he₀V'⟩ : ↥V')) (by simpa using he₀)
    (fun a => a.2)).exists
  have hFp : ∀ v : ↥V, p (F v : ℂ) = (v : ℂ) := fun v => congr_fun hF.2 v
  have hFa₀ : F ⟨a₀, ha₀V⟩ = ⟨e₀, he₀V'⟩ := hF.1
  have hΦcont : Continuous fun z : ↥V' => F (⟨p z, hmaps z.2⟩ : ↥V) := F.continuous.comp hqcont
  have hSclosed : IsClosed {z : ↥V' | F ⟨p z, hmaps z.2⟩ = z} :=
    isClosed_eq hΦcont continuous_id
  have hSopen : IsOpen {z : ↥V' | F ⟨p z, hmaps z.2⟩ = z} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨e, hze, hee⟩ := hcov.isLocalHomeomorphOn z (hmaps z.2)
    have hev : ∀ w : ↥V', e w = p w := fun w => (congr_fun hee w).symm
    have h1 : e.source ∈ 𝓝 z := e.open_source.mem_nhds hze
    have h2 : (fun z' : ↥V' => F ⟨p z', hmaps z'.2⟩) ⁻¹' e.source ∈ 𝓝 z :=
      hΦcont.continuousAt.preimage_mem_nhds (by rw [hz]; exact h1)
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro z' ⟨hz'src, hz'Φ⟩
    have h4 : e (F ⟨p z', hmaps z'.2⟩) = e z' := by
      rw [hev, hFp, hev]
    exact e.injOn hz'Φ hz'src h4
  have hSclopen : IsClopen {z : ↥V' | F ⟨p z, hmaps z.2⟩ = z} := ⟨hSclosed, hSopen⟩
  have hSne : ({z : ↥V' | F ⟨p z, hmaps z.2⟩ = z}).Nonempty := by
    refine ⟨F ⟨a₀, ha₀V⟩, ?_⟩
    show F (⟨p (F ⟨a₀, ha₀V⟩ : ℂ), hmaps (F ⟨a₀, ha₀V⟩).2⟩ : ↥V) = F ⟨a₀, ha₀V⟩
    congr 1
    exact Subtype.ext (hFp ⟨a₀, ha₀V⟩)
  haveI : PreconnectedSpace ↥V' := (isPreconnected_iff_preconnectedSpace).mp hV'c.isPreconnected
  have hkey : ∀ z : ↥V', F ⟨p z, hmaps z.2⟩ = z := by
    intro z
    have hz : z ∈ {z : ↥V' | F ⟨p z, hmaps z.2⟩ = z} := by
      rw [hSclopen.eq_univ hSne]; exact Set.mem_univ z
    exact hz
  let q : ↥V' → ↥V := fun z => ⟨p z, hmaps z.2⟩
  have hqcont' : Continuous q := hqcont
  refine simplyConnectedSpace_of_homeomorph
    { toEquiv :=
        { toFun := q
          invFun := F
          left_inv := fun z => hkey z
          right_inv := fun v => Subtype.ext (hFp v) }
      continuous_toFun := hqcont'
      continuous_invFun := F.continuous }

end Work.BasinSC
