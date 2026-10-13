/-
  WilE7 (`Work.WilE7.sheetSections`): the sheet assembly, in section form.

  Let `S` be a stratum of `ℝ^{p+q}` whose points project into `C ⊆ ℝ^p`, and suppose that the
  projection `SheetProj : SheetE S C → C` of the sheet domain over `C` is a covering map.  Assume
  moreover that `C` is *contractible to the point `c₀ ∈ C` along itself*: there is a continuous
  `K : ℝ^p × ℝ → ℝ^p` with `K (·, 0) = c₀`, `K (·, 1) = id` and `K (x, t) ∈ C` for `x ∈ C`,
  `t ∈ [0,1]`.

  Then every point of the sheet domain over `c₀` can be transported horizontally to every fibre:
  for each enumeration `e : Fin m ≃ SheetProj ⁻¹' {⟨c₀, hc₀⟩}` of the fibre over `c₀` there are `m`
  continuous sections `s j : C → SheetE S C` of `SheetProj`, and for every `x : C` the map
  `j ↦ s j x` is a bijection from `Fin m` onto the fibre of `SheetProj` over `x`.

  The proof is the standard path-lifting computation of covering space theory.  We use two
  ingredients, the first of which is a small general fact about covering maps recorded above.

  * *Transport along a path.*  For a covering map `p : E → X` and a path `γ` from `a` to `b`, the
    map `transportMap hcov γ` sending a point of the fibre over `a` to the endpoint of the lift of
    `γ` starting there is a bijection onto the fibre over `b` (the inverse is transport along the
    reversed path): `Work.WilE7.transportMap_bijective`.

  * *The homotopy lifting property.*  The homotopy `kb (t, x) = K (x, t) : I × C → C` starts at the
    *constant* map `x ↦ c₀`, so for every point `w` of the fibre over `c₀` the constant map at `w`
    lifts its `t = 0` end and `IsCoveringMap.liftHomotopy` produces a lift
    `hb w : I × C → SheetE S C` of `kb`, continuous in both variables.  Its value at `t = 1` is a
    continuous section `s` of `SheetProj` with `s (⟨c₀, hc₀⟩) = w`.

    For fixed `x`, uniqueness of path lifting identifies `t ↦ hb w (t, x)` with the lift of the
    path `γx = (t ↦ K (x, t))`; hence `s j x` is exactly `transportMap hcov (γx x) (e j)`, and
    bijectivity of `j ↦ s j x` follows from bijectivity of the transport.
-/
import Mathlib
import Submission.Work.WilE7.SheetDefs

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilE7

/-! ## Transport of points of a fibre along a path in the base -/

/-- Transport of points of a fibre along a path in the base of a covering map: `transportMap hcov γ`
sends a point `e` of the fibre of `p` over `γ 0` to the endpoint of the lift of `γ` starting at
`e`. -/
noncomputable def transportMap {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hcov : IsCoveringMap p) {a b : X} (γ : Path a b) (e : p ⁻¹' {a}) : p ⁻¹' {b} :=
  ⟨(hcov.liftPath γ e.1 (γ.source.trans e.2.symm)) 1,
    (congr_fun (hcov.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) 1).trans γ.target⟩

/-- Transporting along a path `γ` and then along the reversed path `γ.symm` is the identity on the
fibre over the starting point: the reversed lift is the reverse of the lift. -/
theorem transportMap_symm_apply {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hcov : IsCoveringMap p) {a b : X} (γ : Path a b) (e : p ⁻¹' {a}) :
    transportMap hcov γ.symm (transportMap hcov γ e) = e := by
  set Γ := hcov.liftPath γ e.1 (γ.source.trans e.2.symm) with hΓdef
  have hΓ0 : Γ 0 = e.1 := hcov.liftPath_zero γ e.1 (γ.source.trans e.2.symm)
  have hΓl : p ∘ (fun t => Γ t) = fun t => γ t := funext fun t =>
    congr_fun (hcov.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) t
  have hTr_e : transportMap hcov γ e
      = ⟨Γ 1, (congr_fun (hcov.liftPath_lifts γ e.1 _) 1).trans γ.target⟩ := rfl
  -- the reverse of the lift of `γ`, which lifts `γ.symm` from `Γ 1`
  let Γrev : C(unitInterval, E) := Γ.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  have hb2 : (hcov.liftPath γ.symm (Γ 1)
      (γ.symm.source.trans (transportMap hcov γ e).2.symm)) 1 = e.1 := by
    have hEq : Γrev
        = hcov.liftPath γ.symm (Γ 1) (γ.symm.source.trans (transportMap hcov γ e).2.symm) := by
      refine (hcov.eq_liftPath_iff' _).mpr ⟨?_, ?_⟩
      · ext t
        show p (Γ (unitInterval.symm t)) = γ.symm t
        rw [Path.symm_apply]
        exact congr_fun hΓl (unitInterval.symm t)
      · show Γrev 0 = Γ 1
        show Γ (unitInterval.symm 0) = Γ 1
        rw [unitInterval.symm_zero]
    rw [← hEq]
    show Γ (unitInterval.symm 1) = e.1
    rw [unitInterval.symm_one]
    exact hΓ0
  exact Subtype.ext (by simpa [transportMap, hTr_e] using hb2)

/-- **Transport is a bijection.**  For a covering map `p : E → X` and a path `γ` from `a` to `b`,
transport along `γ` is a bijection from the fibre over `a` onto the fibre over `b`. -/
theorem transportMap_bijective {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hcov : IsCoveringMap p) {a b : X} (γ : Path a b) :
    Function.Bijective (transportMap hcov γ) := by
  have key : ∀ (e : p ⁻¹' {a}), transportMap hcov γ.symm (transportMap hcov γ e) = e :=
    fun e => transportMap_symm_apply hcov γ e
  have key' : ∀ (e : p ⁻¹' {b}), transportMap hcov γ (transportMap hcov γ.symm e) = e := by
    intro e
    have h := transportMap_symm_apply hcov γ.symm e
    rwa [Path.symm_symm] at h
  refine ⟨fun e₁ e₂ h => ?_, fun e => ⟨transportMap hcov γ.symm e, key' e⟩⟩
  have h1 : transportMap hcov γ.symm (transportMap hcov γ e₁)
      = transportMap hcov γ.symm (transportMap hcov γ e₂) := congrArg _ h
  rwa [key e₁, key e₂] at h1

open WilkiesDesign WilkiesDesign.E

theorem sheetSections {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (C : Set (Fin p → ℝ))
    (hcov : IsCoveringMap (Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C)))
    {c₀ : Fin p → ℝ} (hc₀ : c₀ ∈ C)
    (K : (Fin p → ℝ) × ℝ → (Fin p → ℝ)) (hKcont : ContinuousOn K (C ×ˢ Set.Icc (0 : ℝ) 1))
    (hK0 : ∀ x ∈ C, K (x, 0) = c₀) (hK1 : ∀ x ∈ C, K (x, 1) = x)
    (hKmem : ∀ x ∈ C, ∀ t ∈ Set.Icc (0 : ℝ) 1, K (x, t) ∈ C)
    (m : ℕ) (e : Fin m ≃ (Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩})) :
    ∃ s : Fin m → C → Work.WilE7.SheetE S C,
      (∀ j, Continuous (s j)) ∧
      (∀ j, ∀ x : C,
        Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C) (s j x) = x) ∧
      (∀ x : C, Function.Injective fun j => s j x) ∧
      (∀ x : C, ∀ w : Work.WilE7.SheetE S C,
        Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C) w = x → ∃ j, s j x = w) := by
  classical
  -- the base homotopy `(t, x) ↦ K (x, t)`, as a map `I × C → C`
  have hg : Continuous fun z : unitInterval × C => ((z.2.1 : Fin p → ℝ), (z.1 : ℝ)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst)
  have hKc : Continuous fun z : unitInterval × C => K (z.2.1, (z.1 : ℝ)) :=
    hKcont.comp_continuous hg (fun z => ⟨z.2.2, z.1.2⟩)
  let kb : ContinuousMap (unitInterval × C) C :=
    ⟨fun z => ⟨K (z.2.1, (z.1 : ℝ)), hKmem z.2.1 z.2.2 z.1.1 z.1.2⟩,
      hKc.subtype_mk (fun z => hKmem z.2.1 z.2.2 z.1.1 z.1.2)⟩
  have hkb0 : ∀ x : C, kb (0, x) = ⟨c₀, hc₀⟩ := by
    intro x; refine Subtype.ext ?_; exact hK0 x.1 x.2
  have hkb1 : ∀ x : C, kb (1, x) = x := by
    intro x; refine Subtype.ext ?_; exact hK1 x.1 x.2
  -- a point of the fibre over `c₀` really projects to `⟨c₀, hc₀⟩`
  have hmemc : ∀ ε : Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩},
      Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C) ε.1 = ⟨c₀, hc₀⟩ :=
    fun ε => Set.mem_singleton_iff.mp (Set.mem_preimage.mp ε.2)
  -- the lifted homotopy starts at the constant lift of the constant map `x ↦ c₀`
  have hH0 : ∀ j : Fin m, ∀ x : C, kb (0, x) = Work.WilE7.SheetProj ((e j).1) := by
    intro j x
    refine Subtype.ext ?_
    show K (x.1, (0:unitInterval).1) = projFirst p q ((e j).1).1
    rw [show (0:unitInterval).1 = (0:ℝ) from rfl, hK0 x.1 x.2]
    exact (congrArg Subtype.val (hmemc (e j))).symm
  let hb : Fin m → ContinuousMap (unitInterval × C) (Work.WilE7.SheetE S C) :=
    fun j => hcov.liftHomotopy kb (ContinuousMap.const C (e j).1) (hH0 j)
  have hbz : ∀ j : Fin m, ∀ x : C, hb j (0, x) = (e j).1 := by
    intro j x
    exact hcov.liftHomotopy_zero kb (ContinuousMap.const C (e j).1) (hH0 j) x
  have hbl : ∀ j : Fin m, ∀ z : unitInterval × C,
      Work.WilE7.SheetProj (hb j z) = kb z := by
    intro j z
    exact congr_fun (hcov.liftHomotopy_lifts kb (ContinuousMap.const C (e j).1) (hH0 j)) z
  -- the path `t ↦ K (x, t)` in `C`, for each `x : C`
  let γx : (x : C) → Path (⟨c₀, hc₀⟩ : C) x := fun x =>
    Path.mk ⟨fun t : unitInterval => kb (t, x),
      kb.continuous.comp (continuous_id.prodMk continuous_const)⟩ (hkb0 x) (hkb1 x)
  -- transport of points of the fibre over `c₀` along the path `γx`
  let tr : (x : C) → (Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C) ⁻¹' {⟨c₀, hc₀⟩}) →
      (Work.WilE7.SheetProj (p := p) (q := q) (S := S) (C := C) ⁻¹' {x}) :=
    fun x => transportMap hcov (γx x)
  have htr_bij : ∀ x : C, Function.Bijective (tr x) :=
    fun x => transportMap_bijective hcov (γx x)
  -- `s j x` is the transport of `e j` along `γx`
  have hs_tr : ∀ (j : Fin m) (x : C), hb j (1, x) = (tr x (e j)).1 := by
    intro j x
    have hΓ : (fun t : unitInterval => hb j (t, x))
        = ⇑(hcov.liftPath (γx x) (e j).1 ((γx x).source.trans (hmemc (e j)).symm)) := by
      refine (hcov.eq_liftPath_iff ((γx x).source.trans (hmemc (e j)).symm)).mpr ⟨?_, ?_, ?_⟩
      · exact (hb j).continuous.comp (continuous_id.prodMk continuous_const)
      · funext t
        rw [Function.comp_apply]
        show Work.WilE7.SheetProj (hb j (t, x)) = kb (t, x)
        exact hbl j (t, x)
      · show hb j (0, x) = (e j).1
        exact hbz j x
    exact congrFun hΓ 1
  refine ⟨fun j x => hb j (1, x), ?_, ?_, ?_, ?_⟩
  · -- continuity
    intro j
    exact (hb j).continuous.comp (continuous_const.prodMk continuous_id)
  · -- the maps are sections of `SheetProj`
    intro j x
    refine Subtype.ext ?_
    show (Work.WilE7.SheetProj (hb j (1, x))).1 = x.1
    rw [show (Work.WilE7.SheetProj (hb j (1, x))).1 = (kb (1, x)).1 from
      congrArg Subtype.val (hbl j (1, x))]
    exact hK1 x.1 x.2
  · -- injectivity on each fibre
    intro x j j' hjj
    have h1 : tr x (e j) = tr x (e j') := by
      refine Subtype.ext ?_
      rw [← hs_tr j x, ← hs_tr j' x]
      exact hjj
    exact e.injective ((htr_bij x).1 h1)
  · -- surjectivity on each fibre
    intro x w hw
    obtain ⟨ε, hε⟩ := (htr_bij x).2 ⟨w, hw⟩
    refine ⟨e.symm ε, ?_⟩
    have h1 : tr x (e (e.symm ε)) = tr x ε := congrArg (tr x) (Equiv.apply_symm_apply e ε)
    exact (hs_tr (e.symm ε) x).trans ((congrArg Subtype.val h1).trans (congrArg Subtype.val hε))

end Work.WilE7
