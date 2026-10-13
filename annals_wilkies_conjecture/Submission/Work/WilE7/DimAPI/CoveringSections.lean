/-
  `Work.WilE7.DimAPI.CoveringSections`: the monodromy/transport construction for a covering map.

  Let `f : E → B` be a covering map, `c₀ : B`, and let `K : B → I → B` be a continuous contraction
  of `B` onto `c₀` (so `t ↦ K x t` is a path from `c₀` to `x`, continuously in `x`).  If the fibre
  `f ⁻¹' {c₀}` has exactly `k` elements, then the fibres `f ⁻¹' {x}` have exactly `k` elements as
  well, enumerated continuously in `x`.

  The construction is the standard one.  The homotopy `H (t, x) = K x t` has `H (0, x) = c₀`, so
  for each point `v` of the fibre over `c₀` the constant map `x ↦ v` lifts its `t = 0` end and the
  homotopy lifting property of a covering map produces a continuous lift
  `hb v : I × B → E` of `H`, whose value at `t = 1` is a continuous section of `f`.  For fixed `x`
  this section is the transport of `v` along the path `γx = (t ↦ K x t)`, and transport along a
  path is a bijection between the fibres (`Work.WilE7.DimAPI.transportMap_bijective`), which gives
  both injectivity and surjectivity of the enumeration `j ↦ s j x`.
-/
import Mathlib

set_option autoImplicit false
noncomputable section

open Classical

namespace Work.WilE7.DimAPI

/-! ## Transport of a fibre along a path -/

/-- Transport of a point of the fibre `p ⁻¹' {a}` to the fibre `p ⁻¹' {b}` along a path
`γ : Path a b`: lift `γ` starting at the given point and take the endpoint of the lift. -/
def transportMap {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
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

/-! ## The main statement -/

theorem CoveringSections {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {f : E → B}
    (hcov : IsCoveringMap f) {c₀ : B} (K : B → unitInterval → B)
    (hKcont : Continuous (Function.uncurry K))
    (hK0 : ∀ x : B, K x 0 = c₀) (hK1 : ∀ x : B, K x 1 = x)
    (k : ℕ) (e : Fin k ≃ (f ⁻¹' {c₀})) :
    ∃ s : Fin k → B → E,
      (∀ j, Continuous (s j)) ∧ (∀ j x, f (s j x) = x) ∧
      (∀ x, Function.Injective fun j => s j x) ∧
      (∀ x, ∀ w : E, f w = x → ∃ j, s j x = w) := by
  classical
  -- the base homotopy `(t, x) ↦ K x t`
  have hHcont : Continuous fun z : unitInterval × B => K z.2 z.1 :=
    hKcont.comp (continuous_snd.prodMk continuous_fst)
  let H : C(unitInterval × B, B) := ⟨fun z => K z.2 z.1, hHcont⟩
  -- the fibres over `c₀` sit above `c₀`
  have hmem : ∀ ε : f ⁻¹' {c₀}, f ε.1 = c₀ :=
    fun ε => Set.mem_singleton_iff.mp (Set.mem_preimage.mp ε.2)
  -- the lifted homotopy starts at the constant lift of the constant map `x ↦ c₀`
  have hH0 : ∀ j : Fin k, ∀ x : B, H (0, x) = f ((e j).1) := by
    intro j x
    show K x (0 : unitInterval) = f ((e j).1)
    rw [hK0 x]
    exact (hmem (e j)).symm
  let hb : Fin k → C(unitInterval × B, E) :=
    fun j => hcov.liftHomotopy H (ContinuousMap.const B (e j).1) (hH0 j)
  have hbz : ∀ (j : Fin k) (x : B), hb j (0, x) = (e j).1 :=
    fun j x => hcov.liftHomotopy_zero H (ContinuousMap.const B (e j).1) (hH0 j) x
  have hbl : ∀ (j : Fin k) (z : unitInterval × B), f (hb j z) = H z :=
    fun j z => congr_fun (hcov.liftHomotopy_lifts H (ContinuousMap.const B (e j).1) (hH0 j)) z
  -- the path `t ↦ K x t` in `B`, for each `x : B`
  let γx : (x : B) → Path c₀ x := fun x =>
    Path.mk ⟨fun t : unitInterval => K x t,
      hKcont.comp (continuous_const.prodMk continuous_id)⟩ (hK0 x) (hK1 x)
  -- transport of points of the fibre over `c₀` along the path `γx`
  let tr : (x : B) → (f ⁻¹' {c₀}) → (f ⁻¹' {x}) := fun x => transportMap hcov (γx x)
  have htr_bij : ∀ x : B, Function.Bijective (tr x) :=
    fun x => transportMap_bijective hcov (γx x)
  -- `s j x` is the transport of `e j` along `γx`
  have hs_tr : ∀ (j : Fin k) (x : B), hb j (1, x) = (tr x (e j)).1 := by
    intro j x
    have hΓ : (fun t : unitInterval => hb j (t, x))
        = ⇑(hcov.liftPath (γx x) (e j).1 ((γx x).source.trans (e j).2.symm)) := by
      refine (hcov.eq_liftPath_iff ((γx x).source.trans (e j).2.symm)).mpr ⟨?_, ?_, ?_⟩
      · exact (hb j).continuous.comp (continuous_id.prodMk continuous_const)
      · funext t
        rw [Function.comp_apply]
        show f (hb j (t, x)) = (γx x) t
        rw [hbl j (t, x)]
        rfl
      · show hb j (0, x) = (e j).1
        exact hbz j x
    exact congrFun hΓ 1
  refine ⟨fun j x => hb j (1, x), ?_, ?_, ?_, ?_⟩
  · -- continuity
    intro j
    exact (hb j).continuous.comp (continuous_const.prodMk continuous_id)
  · -- the maps are sections of `f`
    intro j x
    show f (hb j (1, x)) = x
    rw [hbl j (1, x)]
    show K x (1 : unitInterval) = x
    exact hK1 x
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

end Work.WilE7.DimAPI
