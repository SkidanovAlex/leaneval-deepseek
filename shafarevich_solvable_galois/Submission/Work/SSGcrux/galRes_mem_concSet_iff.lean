import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.TPatom.noninvariantLevelDefs
import Submission.Work.SSGRoute.TatePoitouRoute.galRes_preimage_decompK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

set_option maxHeartbeats 1000000

/-- **Restriction of decomposition groups.**  Let `k ⊆ K ⊆ L` be number fields and let `w'` be a
place of `L` lying over the place `w` of `K`.  Then the restriction map
`galRes k K L : Gal(L/k) → Gal(K/k)` sends the decomposition group `D_{w'}` of `w'` into the
decomposition group `D_w` of `w`. -/
lemma galRes_mem_decompK {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K]
    {w : NK.GlobalCFT.Place K} {w' : NK.GlobalCFT.Place L}
    (hw' : NK.GlobalCFT.Place.LiesOver w' w) {δ : L ≃ₐ[k] L}
    (hδ : δ ∈ SSGRoute.PTExt.decompK (k := k) (K := L) w') :
    SSGRoute.PTExt.galRes k K L δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w := by
  rw [SSGRoute.PTExt.decompK, MulAction.mem_stabilizer_iff] at hδ ⊢
  have h2 := NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L) δ
    (SSGRoute.PTExt.galRes k K L δ) (fun y => AlgEquiv.restrictNormal_commutes δ K y) hw'
  rw [hδ] at h2
  exact (Work.SSGRoute.place_liesOver_unique w' hw' h2).symm

/-- Pure group-theoretic core of the *backward* implication: if `N ◁ Gal(K/k)`, `γ ∈ Gal(K/k)`,
`n ∈ N` and `d ∈ D_w`, then `n * γ * d ∈ γ · D_w · N`. -/
lemma mul_mem_concSet {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (γ : K ≃ₐ[k] K) {n d : K ≃ₐ[k] K} (hn : n ∈ N)
    (hd : d ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w) :
    n * γ * d ∈ Work.SSGRoute.TPatom.concSet k K w N γ := by
  rw [Work.SSGRoute.TPatom.concSet]
  refine ⟨d, hd, d⁻¹ * (γ⁻¹ * n * γ) * d, ?_, ?_⟩
  · have h1 : γ⁻¹ * n * γ ∈ N := (inferInstance : N.Normal).conj_mem n hn γ⁻¹
    exact (inferInstance : N.Normal).conj_mem _ h1 d⁻¹
  · group

/-- **The block of `σ` is the block of `γ` iff `galRes σ ∈ γ · D_w · N`.** -/
theorem galRes_mem_concSet_iff {k K L : Type} [Field k] [Field K] [Field L] [NumberField k]
    [NumberField K] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (σ₀ σ : L ≃ₐ[k] L) (γ : K ≃ₐ[k] K)
    (hγ : SSGRoute.PTExt.galRes k K L σ₀ = γ) :
    SSGRoute.PTExt.galRes k K L σ ∈ Work.SSGRoute.TPatom.concSet k K w N γ ↔
      ∃ h ∈ N.comap (SSGRoute.PTExt.galRes k K L),
        ∃ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := L) (NK.GlobalCFT.Place.ofFinite q'),
          σ = h * σ₀ * δ := by
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
  have hlies : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w := by
    rw [hwq]; exact NK.GlobalCFT.Place.liesOver_ofFinite hq'
  constructor
  · -- **Forward direction.**  `galRes σ ∈ γ · D_w · N` forces `σ ∈ N' · σ₀ · D_{q'}`.
    intro hmem
    rw [Work.SSGRoute.TPatom.concSet] at hmem
    obtain ⟨δ₁, hδ₁, n₁, hn₁, heq⟩ := hmem
    -- `γ * (δ₁ * n₁) = galRes σ`, hence `galRes (σ₀⁻¹ σ) = δ₁ n₁`.
    have hπτ : SSGRoute.PTExt.galRes k K L (σ₀⁻¹ * σ) = δ₁ * n₁ := by
      rw [map_mul, map_inv, hγ, ← heq]; group
    -- `n₂ = δ₁ n₁ δ₁⁻¹ ∈ N`, lifted to `Gal(L/k)` by `σ₁`.
    have hn₂ : δ₁ * n₁ * δ₁⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem n₁ hn₁ δ₁
    obtain ⟨σ₁, hσ₁⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K)
      L (δ₁ * n₁ * δ₁⁻¹)
    have hπx : SSGRoute.PTExt.galRes k K L (σ₁⁻¹ * (σ₀⁻¹ * σ)) = δ₁ := by
      rw [map_mul, map_inv, hσ₁, hπτ]; group
    -- The Galois step: an element restricting into `D_w` lies in `D_{q'} · N'`.
    obtain ⟨d, hd, n, hn, hdn⟩ :=
      Work.SSGRoute.TatePoitouRoute.galRes_preimage_decompK k K L N w q' hlies
        (σ₁⁻¹ * (σ₀⁻¹ * σ)) (by rw [hπx]; exact hδ₁)
    have hN' : (N.comap (SSGRoute.PTExt.galRes k K L)).Normal :=
      Subgroup.Normal.comap (inferInstance : N.Normal) (SSGRoute.PTExt.galRes k K L)
    have hσ₁N : σ₁ ∈ N.comap (SSGRoute.PTExt.galRes k K L) :=
      Subgroup.mem_comap.mpr (by rw [hσ₁]; exact hn₂)
    have hconj : d * n * d⁻¹ ∈ N.comap (SSGRoute.PTExt.galRes k K L) :=
      hN'.conj_mem n hn d
    have hh' : σ₁ * (d * n * d⁻¹) ∈ N.comap (SSGRoute.PTExt.galRes k K L) :=
      (N.comap (SSGRoute.PTExt.galRes k K L)).mul_mem hσ₁N hconj
    refine ⟨σ₀ * (σ₁ * (d * n * d⁻¹)) * σ₀⁻¹, ?_, d, hd, ?_⟩
    · exact hN'.conj_mem (σ₁ * (d * n * d⁻¹)) hh' σ₀
    · have hσeq : σ = σ₀ * (σ₁ * (d * n)) := by rw [hdn]; group
      rw [hσeq]; group
  · -- **Backward direction.**  An explicit `σ = h σ₀ δ` gives `galRes σ = galRes h · γ · galRes δ`.
    rintro ⟨h, hh, δ, hδ, hσ⟩
    rw [hσ, map_mul, map_mul, hγ]
    exact mul_mem_concSet w N γ (Subgroup.mem_comap.mp hh) (galRes_mem_decompK hlies hδ)

end Work.SSGcrux
