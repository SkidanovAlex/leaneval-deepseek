import Mathlib

namespace Work.WilE7.FrontierCS

/-- Every linear map defined on a submodule extends to the ambient space.
(Every submodule of a module is a direct summand, via a complement and the associated
projection.) -/
lemma exists_linearMap_extend_of_submodule
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    (p : Submodule ℝ E) (g : p →ₗ[ℝ] E') :
    ∃ g' : E →ₗ[ℝ] E', g'.comp p.subtype = g := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  exact ⟨g.comp (p.projectionOnto q hq), by
    ext x
    simp [LinearMap.comp_apply, Submodule.projectionOnto_apply_left hq]⟩

/-- Key linear-algebra lemma. If `V ⊔ Q.range = ⊤` then there is a bijective endomorphism `M`
with `(M - Q).range ≤ V`. Construction: let `π := V.mkQ : E → E ⧸ V`; then `π ∘ Q` is surjective,
so `K := (π ∘ Q).ker` has `finrank K = finrank V` (rank–nullity together with
`finrank (E ⧸ V) + finrank V = finrank E`), hence there is a linear equivalence `S : K ≃ₗ V`.
Since `Q` maps `K` into `V`, the map `S - Q|_K : K →ₗ V` can be extended to a linear map
`ḡ : E →ₗ V` (every submodule is a direct summand). Then `T := V.subtype ∘ ḡ : E →ₗ E` has
`T.range ≤ V`, and `M := Q + T` is injective: if `M x = 0` then `Q x = -T x ∈ V`, so `x ∈ K`,
and on `K` the map `M` agrees with `S`, hence `x = 0`; by finite-dimensionality `M` is bijective.
Finally `M - Q = T` has range in `V`. -/
theorem exists_end_bij_range_sub_le
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (Q : E →ₗ[ℝ] E) (h : V ⊔ Q.range = ⊤) :
    ∃ M : E →ₗ[ℝ] E, Function.Bijective M ∧ (M - Q).range ≤ V := by
  classical
  -- `finrank (π ∘ Q).ker = finrank V`
  have hfr : Module.finrank ℝ (V.mkQ.comp Q).ker = Module.finrank ℝ V := by
    have hsurj : Function.Surjective (V.mkQ.comp Q) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_comp]
      have hmapV : Submodule.map V.mkQ V = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro y hy
        rw [Submodule.mem_map] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hx
      have hthis : Submodule.map V.mkQ Q.range = Submodule.map V.mkQ (V ⊔ Q.range) := by
        rw [Submodule.map_sup, hmapV, bot_sup_eq]
      rw [hthis, h, Submodule.map_top, Submodule.range_mkQ]
    have hran : (V.mkQ.comp Q).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hrange_fin : Module.finrank ℝ (V.mkQ.comp Q).range = Module.finrank ℝ (E ⧸ V) := by
      rw [hran]
      exact (Submodule.topEquiv : (⊤ : Submodule ℝ (E ⧸ V)) ≃ₗ[ℝ] (E ⧸ V)).finrank_eq
    have hfin1 :
        Module.finrank ℝ (E ⧸ V) + Module.finrank ℝ (V.mkQ.comp Q).ker =
          Module.finrank ℝ E := by
      rw [← hrange_fin]
      exact LinearMap.finrank_range_add_finrank_ker (V.mkQ.comp Q)
    have hfin2 : Module.finrank ℝ (E ⧸ V) + Module.finrank ℝ V = Module.finrank ℝ E :=
      Submodule.finrank_quotient_add_finrank V
    omega
  -- a linear equivalence `K ≃ₗ V`
  let S : (V.mkQ.comp Q).ker ≃ₗ[ℝ] V := LinearEquiv.ofFinrankEq _ _ hfr
  -- `Q` maps `K` into `V`
  have hmem : ∀ y : (V.mkQ.comp Q).ker, (Q.comp (V.mkQ.comp Q).ker.subtype) y ∈ V := by
    intro y
    have hy : V.mkQ (Q (y : E)) = 0 := by
      have h2 := y.2
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at h2
      exact h2
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at hy
    exact hy
  let QK : (V.mkQ.comp Q).ker →ₗ[ℝ] V :=
    (Q.comp (V.mkQ.comp Q).ker.subtype).codRestrict V hmem
  let g : (V.mkQ.comp Q).ker →ₗ[ℝ] V := S.toLinearMap - QK
  obtain ⟨gbar, hgbar⟩ := exists_linearMap_extend_of_submodule (V.mkQ.comp Q).ker g
  let T : E →ₗ[ℝ] E := V.subtype.comp gbar
  refine ⟨Q + T, ?_, ?_⟩
  · -- `M = Q + T` is injective, hence bijective
    have hker : (Q + T).ker = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hxT : T x ∈ V := by
        show (gbar x : E) ∈ V
        exact (gbar x).2
      have hxV : Q x ∈ V := by
        have hsum : Q x + T x = 0 := by rwa [LinearMap.add_apply] at hx
        have hq : Q x = -(T x) := by rw [eq_neg_iff_add_eq_zero]; exact hsum
        rw [hq]; exact V.neg_mem hxT
      have hxK : x ∈ (V.mkQ.comp Q).ker := by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hxV
      have hQKx : (QK ⟨x, hxK⟩ : E) = Q x := by
        simp only [QK, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      have hT_x : T x = (S ⟨x, hxK⟩ : E) - Q x := by
        have h1 : gbar x = g ⟨x, hxK⟩ := by
          have h2 := LinearMap.congr_fun hgbar ⟨x, hxK⟩
          rwa [LinearMap.comp_apply, Submodule.subtype_apply] at h2
        rw [show T x = V.subtype (gbar x) from rfl, h1]
        change V.subtype (S.toLinearMap ⟨x, hxK⟩ - QK ⟨x, hxK⟩) = (S ⟨x, hxK⟩ : E) - Q x
        rw [LinearMap.map_sub, Submodule.subtype_apply, Submodule.subtype_apply, hQKx]
        rfl
      have hSx : (Q + T) x = (S ⟨x, hxK⟩ : E) := by
        rw [LinearMap.add_apply, hT_x]
        abel
      rw [hSx] at hx
      have hS0 : S ⟨x, hxK⟩ = 0 := Subtype.ext hx
      have hz : (⟨x, hxK⟩ : (V.mkQ.comp Q).ker) = 0 := by
        apply S.injective
        rw [hS0, map_zero]
      simpa using congrArg Subtype.val hz
    have hinj : Function.Injective (Q + T) := LinearMap.ker_eq_bot.mp hker
    exact ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩
  · -- `(M - Q).range = T.range ≤ V`
    have hT_range : T.range ≤ V := by
      rw [show T = V.subtype.comp gbar from rfl, LinearMap.range_comp]
      exact Submodule.map_subtype_le V gbar.range
    have : Q + T - Q = T := by abel
    rw [this]
    exact hT_range

end Work.WilE7.FrontierCS
