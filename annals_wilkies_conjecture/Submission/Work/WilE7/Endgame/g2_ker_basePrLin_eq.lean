import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.coordProj_fderiv_ker_eventually
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood

namespace Work.WilE7.Endgame

/-- **Linear-algebra endgame.** Let `J : V →ₗ A`, `g : V →ₗ W`, `π : W →ₗ Z` over `ℝ`, with `W`
finite dimensional.  Suppose the `π`-image of `g(ker J)` is everything (`⊤`), and that the
`g`-image of `ker J` has the same dimension as `Z`.  Then an element of `ker J` is killed by `g`
if and only if it is killed by `π ∘ g`.

This is the abstract form of `g2_ker_basePrLin_eq`: by `hvert` the base projection of the tangent
space `ker (jac T w)` already has the dimension of the target of the coordinate projection, while
`hpersw` says that the coordinate projection does not lose anything on it; hence the coordinate
projection is injective exactly on `g(ker J)` and `ker π ⊓ g(ker J) = ⊥`. -/
theorem ker_inf_eq_ker_comp_of_map_eq_top {V W Z A : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [AddCommGroup Z] [Module ℝ Z] [AddCommGroup A] [Module ℝ A]
    [FiniteDimensional ℝ W]
    (J : V →ₗ[ℝ] A) (g : V →ₗ[ℝ] W) (π : W →ₗ[ℝ] Z)
    (hfin : Module.finrank ℝ ((LinearMap.ker J).map g) = Module.finrank ℝ Z)
    (hsurj : (LinearMap.ker J).map (π.comp g) = ⊤) :
    LinearMap.ker J ⊓ LinearMap.ker g = LinearMap.ker J ⊓ LinearMap.ker (π.comp g) := by
  -- `π` is injective on `g(ker J)`: on that subspace it is a surjection between spaces of the
  -- same dimension.
  have hbot : (LinearMap.ker J).map g ⊓ LinearMap.ker π = ⊥ := by
    set M : Submodule ℝ W := (LinearMap.ker J).map g with hM
    have hMπ : M.map π = ⊤ := by
      rw [hM, ← Submodule.map_comp g π (LinearMap.ker J)]
      exact hsurj
    have hfinM : Module.finrank ℝ M = Module.finrank ℝ Z := by
      rw [hM]; exact hfin
    -- the restriction `ψ` of `π` to `M = g(ker J)`.
    set ψ : M →ₗ[ℝ] Z := π.comp M.subtype with hψ
    have hrange : ψ.range = ⊤ := by
      rw [hψ, LinearMap.range_comp, Submodule.range_subtype]
      exact hMπ
    have hfr : Module.finrank ℝ ψ.range = Module.finrank ℝ M := by
      rw [hrange, finrank_top ℝ Z, hfinM]
    -- rank–nullity forces `ker ψ = ⊥`.
    have hker0 : Module.finrank ℝ ψ.ker = 0 := by
      have hrn := LinearMap.finrank_range_add_finrank_ker ψ
      rw [hfr] at hrn
      omega
    have hkerbot : ψ.ker = ⊥ := Submodule.finrank_eq_zero.mp hker0
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    have hxψ : (⟨x, hx.1⟩ : M) ∈ ψ.ker := by
      rw [LinearMap.mem_ker, hψ]
      simpa using LinearMap.mem_ker.mp hx.2
    rw [hkerbot, Submodule.mem_bot] at hxψ
    exact congrArg Subtype.val hxψ
  refine le_antisymm ?_ ?_
  · -- `⊆`: `g v = 0` implies `(π ∘ g) v = 0`.
    intro v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨hv.1, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp hv.2, map_zero]
  · -- `⊇`: if `v ∈ ker J` and `π (g v) = 0`, then `g v ∈ g(ker J) ⊓ ker π = ⊥`.
    intro v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨hv.1, ?_⟩
    rw [LinearMap.mem_ker]
    have hgvM : g v ∈ (LinearMap.ker J).map g := Submodule.mem_map.mpr ⟨v, hv.1, rfl⟩
    have hgvπ : g v ∈ LinearMap.ker π :=
      LinearMap.mem_ker.mpr (by simpa only [LinearMap.comp_apply] using LinearMap.mem_ker.mp hv.2)
    have hmem : g v ∈ (LinearMap.ker J).map g ⊓ LinearMap.ker π := ⟨hgvM, hgvπ⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem

theorem g2_ker_basePrLin_eq {n m : ℕ}
    (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hvert : ∀ w ∈ T.X.set, Work.WilE7.MainDesign.projRank T w + 1 = n + (m + 1) - T.j)
    (e : Fin (n + (m + 1) - T.j - 1) ↪ Fin n)
    (w : Fin (0 + (n + (m + 1))) → ℝ) (hw : w ∈ T.X.set)
    (hpersw : (LinearMap.ker (Work.WilE7.MainDesign.jac T w)).map
      ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
        (Work.WilE7.MainDesign.basePrLin n (m + 1))) = ⊤) :
    LinearMap.ker (Work.WilE7.MainDesign.jac T w) ⊓
        (Work.WilE7.MainDesign.basePrLin n (m + 1)).ker
      = LinearMap.ker (Work.WilE7.MainDesign.jac T w) ⊓
        ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap.comp
          (Work.WilE7.MainDesign.basePrLin n (m + 1))).ker := by
  -- The base projection of `ker (jac T w)` has dimension `projRank T w`, and by `hvert` this is
  -- exactly the number of coordinates of the target of `coordProjCLM e`.
  have hfin : Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac T w)).map
        (Work.WilE7.MainDesign.basePrLin n (m + 1)))
      = Module.finrank ℝ (Fin (n + (m + 1) - T.j - 1) → ℝ) := by
    rw [Module.finrank_fin_fun]
    show Work.WilE7.MainDesign.projRank T w = n + (m + 1) - T.j - 1
    have hv := hvert w hw
    omega
  exact ker_inf_eq_ker_comp_of_map_eq_top (Work.WilE7.MainDesign.jac T w)
    (Work.WilE7.MainDesign.basePrLin n (m + 1))
    ((Work.WilE7.DimAPI.coordProjCLM e).toLinearMap) hfin hpersw

end Work.WilE7.Endgame
