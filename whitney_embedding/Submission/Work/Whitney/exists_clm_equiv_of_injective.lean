import Mathlib

/-!
# Extending an injective linear map to a continuous linear equivalence

Let `L : E →L[ℝ] F` be an injective continuous linear map between finite dimensional real
normed spaces, with `finrank ℝ F = 2 * finrank ℝ E`.  Then `E × E` and `F` have the same
dimension and there is a continuous linear equivalence `T : E × E ≃L[ℝ] F` whose restriction
to the first factor is `L`, i.e. `T (u, 0) = L u` for every `u : E`.

The construction is the elementary one: choose a linear complement `K` of the range `S` of `L`
in `F` (possible because `S ⊔ K = ⊤` and `S ⊓ K = ⊥`), observe that `finrank ℝ K = finrank ℝ E`
so that `K ≃ₗ F` is linearly isomorphic to `E`, and put `T (u, v) = L u + φ v` where
`φ : E ≃ₗ[ℝ] K`.  Injectivity follows from `S ⊓ K = ⊥` and `L` injective, surjectivity from
`S ⊔ K = ⊤` and `φ` surjective.  All linear maps between finite dimensional normed spaces are
continuous, which is the only place where the topology enters.
-/

namespace Work.Whitney

theorem exists_clm_equiv_of_injective
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Injective L)
    (hfin : Module.finrank ℝ F = Module.finrank ℝ E + Module.finrank ℝ E) :
    ∃ T : (E × E) ≃L[ℝ] F, ∀ u : E, T (u, 0) = L u := by
  classical
  -- View `L` as a plain linear map and let `S` be its range, `K` a linear complement in `F`.
  let f : E →ₗ[ℝ] F := L
  let S : Submodule ℝ F := f.range
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl S
  have hker : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr hL
  -- `finrank` bookkeeping: `finrank S = finrank E` and `F = S ⊕ K`.
  have hfinS : Module.finrank ℝ S = Module.finrank ℝ E := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hker, finrank_bot, add_zero] at h
    exact h
  have hsup : S ⊔ K = ⊤ := hK.sup_eq_top
  have hinf : S ⊓ K = ⊥ := hK.inf_eq_bot
  have hsum : Module.finrank ℝ S + Module.finrank ℝ K = Module.finrank ℝ F := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S K
    rw [hsup, hinf, finrank_top, finrank_bot, add_zero] at h
    exact h.symm
  have hfinK : Module.finrank ℝ K = Module.finrank ℝ E := by
    have h1 : Module.finrank ℝ E + Module.finrank ℝ K = Module.finrank ℝ E + Module.finrank ℝ E := by
      calc Module.finrank ℝ E + Module.finrank ℝ K
          = Module.finrank ℝ S + Module.finrank ℝ K := by rw [hfinS]
        _ = Module.finrank ℝ F := hsum
        _ = Module.finrank ℝ E + Module.finrank ℝ E := hfin
    exact add_left_cancel h1
  -- A linear isomorphism between `E` and the complement `K`.
  obtain ⟨φ⟩ : Nonempty (E ≃ₗ[ℝ] K) := ⟨LinearEquiv.ofFinrankEq E K hfinK.symm⟩
  -- The linear map `Tₗ (u, v) = L u + φ v`.
  let Tₗ : (E × E) →ₗ[ℝ] F :=
    { toFun := fun p => L p.1 + (φ p.2 : F)
      map_add' := by intro p q; simp [map_add]; abel
      map_smul' := by intro c p; simp [smul_add, map_smul] }
  have hTₗ_apply : ∀ p : E × E, Tₗ p = L p.1 + (φ p.2 : F) := fun p => rfl
  have hT_inj : Function.Injective Tₗ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, v⟩ h
    rw [LinearMap.mem_ker] at h
    have h1 : L u + (φ v : F) = 0 := by simpa [hTₗ_apply] using h
    have hmemS : L u ∈ S := ⟨u, rfl⟩
    have hmemK : L u ∈ K := by
      have h2 : L u = -(φ v : F) := eq_neg_of_add_eq_zero_left h1
      rw [h2]
      exact K.neg_mem (φ v).2
    have hzero : L u = 0 := by
      have : L u ∈ S ⊓ K := ⟨hmemS, hmemK⟩
      rw [hinf] at this
      simpa using this
    have hu : u = 0 := hL (by simpa using hzero)
    have hv : v = 0 := by
      apply φ.injective
      have h3 : (φ v : F) = 0 := by
        have h4 := h1
        rw [hzero, zero_add] at h4
        exact h4
      have h5 : (φ v : K) = (0 : K) := Subtype.coe_injective (by simpa using h3)
      simpa using h5
    exact Prod.ext hu hv
  have hT_surj : Function.Surjective Tₗ := by
    intro y
    have hy : y ∈ S ⊔ K := by rw [hsup]; trivial
    obtain ⟨s, hs, k, hk, hsk⟩ := Submodule.mem_sup.mp hy
    have hs' : s ∈ f.range := hs
    obtain ⟨u, hu⟩ := hs'
    obtain ⟨v, hv⟩ := φ.surjective ⟨k, hk⟩
    refine ⟨(u, v), ?_⟩
    rw [hTₗ_apply]
    rw [show L u = s from hu, show (φ v : F) = k from by rw [hv]]
    exact hsk
  -- Promote the linear equivalence to a continuous one (finite dimensional case).
  let Tₗ_equiv : (E × E) ≃ₗ[ℝ] F := LinearEquiv.ofBijective Tₗ ⟨hT_inj, hT_surj⟩
  let T : (E × E) ≃L[ℝ] F := Tₗ_equiv.toContinuousLinearEquiv
  refine ⟨T, ?_⟩
  intro u
  change Tₗ_equiv (u, 0) = L u
  change Tₗ (u, 0) = L u
  simp [hTₗ_apply]

end Work.Whitney
