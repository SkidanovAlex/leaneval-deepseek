import Mathlib
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.zmod_roots_of_unity
import Submission.Work.AbsoluteKummer.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The transport `Ω ↝ AlgebraicClosure k` for the `Ш² = 0` route

`Ш²(k,M)` is defined for an arbitrary algebraic closure `Ω` of the number field `k`
(`SSGRoute.Z2loc`/`B2top`), while the arithmetic (Kummer theory and the Hasse principle for the
Brauer group, available for `AlgebraicClosure k`) is phrased for `k̄ = AlgebraicClosure k`.
This file transports the relevant cochain data along a `k`-algebra isomorphism `e : Ω ≃ₐ[k] k̄`:
conjugation by `e` identifies `Gal(Ω/k)` with `Gal(k̄/k)` and respects the subgroup topology, the
decomposition groups and the involutions.
-/

set_option linter.ambiguousOpen false
set_option maxHeartbeats 800000

namespace Work.SSGRoute

open scoped Pointwise Topology

open Filter

/-! ## The trivial module `Triv p` -/

@[simp] theorem triv_smul (p : ℕ) (Γ : Type) [Monoid Γ] (g : Γ) (x : Triv p) : g • x = x := rfl

/-! ## Conjugation by an algebra isomorphism -/

noncomputable def conjAlgEquiv {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω]
    [Field A] [Algebra k A] (e : Ω ≃ₐ[k] A) : (Ω ≃ₐ[k] Ω) ≃* (A ≃ₐ[k] A) where
  toFun σ := e.symm.trans (σ.trans e)
  invFun τ := e.trans (τ.trans e.symm)
  left_inv σ := by ext x; simp [AlgEquiv.trans_apply]
  right_inv τ := by ext x; simp [AlgEquiv.trans_apply]
  map_mul' σ τ := by ext x; simp [AlgEquiv.trans_apply, AlgEquiv.mul_apply]

@[simp] theorem conjAlgEquiv_apply {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω]
    [Field A] [Algebra k A] (e : Ω ≃ₐ[k] A) (σ : Ω ≃ₐ[k] Ω) :
    conjAlgEquiv e σ = e.symm.trans (σ.trans e) := rfl

theorem conjAlgEquiv_apply_apply {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω]
    [Field A] [Algebra k A] (e : Ω ≃ₐ[k] A) (σ : Ω ≃ₐ[k] Ω) (x : A) :
    conjAlgEquiv e σ x = e (σ (e.symm x)) := by
  rw [conjAlgEquiv_apply]
  simp only [AlgEquiv.trans_apply]

theorem conjAlgEquiv_mem_fixingSubgroup {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω]
    [Field A] [Algebra k A] (e : Ω ≃ₐ[k] A) (E : IntermediateField k Ω) (σ : Ω ≃ₐ[k] Ω) :
    conjAlgEquiv e σ ∈ (E.map e.toAlgHom).fixingSubgroup ↔ σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have hy : e x ∈ E.map e.toAlgHom := by
      rw [IntermediateField.mem_map]; exact ⟨x, hx, rfl⟩
    have h1 : conjAlgEquiv e σ (e x) = e x := h (e x) hy
    have h2 : e (σ x) = e x := by
      rw [conjAlgEquiv_apply_apply] at h1
      simpa only [AlgEquiv.symm_apply_apply] using h1
    exact e.injective h2
  · intro h y hy
    rw [IntermediateField.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change (e.symm.trans (σ.trans e)) (e x) = e x
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, h x hx]

theorem map_symm_map {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω] [Field A] [Algebra k A]
    (e : Ω ≃ₐ[k] A) (F : IntermediateField k A) :
    (F.map e.symm.toAlgHom).map e.toAlgHom = F := by
  ext y
  constructor
  · intro hy
    rw [IntermediateField.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    rw [IntermediateField.mem_map] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have hyz : y = z := by
      calc y = e.toAlgHom x := hxy.symm
        _ = e.toAlgHom (e.symm.toAlgHom z) := by rw [hzx]
        _ = z := by
              show e (e.symm z) = z
              rw [AlgEquiv.apply_symm_apply]
    rw [hyz]; exact hz
  · intro hy
    rw [IntermediateField.mem_map]
    refine ⟨e.symm y, ?_, ?_⟩
    · rw [IntermediateField.mem_map]
      exact ⟨y, hy, rfl⟩
    · show e.toAlgHom (e.symm.toAlgHom y) = y
      show e (e.symm y) = y
      rw [AlgEquiv.apply_symm_apply]

/-- Finite-dimensionality is preserved by `map` along a `k`-algebra isomorphism. -/
theorem finiteDimensional_map_algEquiv {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω]
    [Field A] [Algebra k A] (e : Ω ≃ₐ[k] A) (E : IntermediateField k Ω)
    [FiniteDimensional k E] : FiniteDimensional k (E.map e.toAlgHom) := by
  let f : ↥E →ₗ[k] ↥(E.map e.toAlgHom) :=
    { toFun := fun x => ⟨e x, by
        rw [IntermediateField.mem_map]; exact ⟨x, x.2, rfl⟩⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp }
  refine Module.Finite.of_surjective f ?_
  rintro ⟨y, hy⟩
  rw [IntermediateField.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

/-! ## Transport of local constancy -/

section Constancy

variable {k Ω A M : Type} [Field k] [Field Ω] [Algebra k Ω] [Field A] [Algebra k A]
variable {G : Type} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- Right invariance under `H ≤ Gal(Ω/k)` transports to right invariance under the corresponding
subgroup of `Gal(A/k)`, along conjugation by `e`. -/
theorem isLocConstOn_conjAlgEquiv (e : Ω ≃ₐ[k] A)
    {H : Subgroup (Ω ≃ₐ[k] Ω)} {H' : Subgroup (A ≃ₐ[k] A)}
    (hH : ∀ σ : Ω ≃ₐ[k] Ω, conjAlgEquiv e σ ∈ H' ↔ σ ∈ H)
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : SSGRoute.IsLocConstOn H f) :
    SSGRoute.IsLocConstOn H' (fun y => f ((conjAlgEquiv e).symm y)) := by
  obtain ⟨U, hUopen, hUf⟩ := hf
  have hUnhds : (U : Set (Ω ≃ₐ[k] Ω)) ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) := hUopen.mem_nhds U.one_mem
  obtain ⟨E, hEfin, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff k Ω (U : Set (Ω ≃ₐ[k] Ω))).mp hUnhds
  haveI : FiniteDimensional k E := hEfin
  haveI hEmap : FiniteDimensional k (E.map e.toAlgHom) := finiteDimensional_map_algEquiv e E
  refine ⟨(E.map e.toAlgHom).fixingSubgroup, IntermediateField.fixingSubgroup_isOpen _, ?_⟩
  intro y hy u hu huH'
  have huU : (conjAlgEquiv e).symm u ∈ U := by
    apply hEU
    have h1 : conjAlgEquiv e ((conjAlgEquiv e).symm u) ∈ (E.map e.toAlgHom).fixingSubgroup := by
      rw [MulEquiv.apply_symm_apply]; exact hu
    exact (conjAlgEquiv_mem_fixingSubgroup e E _).mp h1
  have huH : (conjAlgEquiv e).symm u ∈ H :=
    (hH ((conjAlgEquiv e).symm u)).mp (by rw [MulEquiv.apply_symm_apply]; exact huH')
  have hyH : (conjAlgEquiv e).symm y ∈ H :=
    (hH ((conjAlgEquiv e).symm y)).mp (by rw [MulEquiv.apply_symm_apply]; exact hy)
  have key : f ((conjAlgEquiv e).symm (y * u)) = f ((conjAlgEquiv e).symm y) := by
    rw [map_mul]
    exact hUf _ hyH _ huU huH
  exact key

/-- The reverse direction: right invariance under `H' ≤ Gal(A/k)` transports to right invariance
under the corresponding subgroup of `Gal(Ω/k)`. -/
theorem isLocConstOn_conjAlgEquiv_symm (e : Ω ≃ₐ[k] A)
    {H : Subgroup (Ω ≃ₐ[k] Ω)} {H' : Subgroup (A ≃ₐ[k] A)}
    (hH : ∀ σ : Ω ≃ₐ[k] Ω, conjAlgEquiv e σ ∈ H' ↔ σ ∈ H)
    {f : (A ≃ₐ[k] A) → M} (hf : SSGRoute.IsLocConstOn H' f) :
    SSGRoute.IsLocConstOn H (fun g => f (conjAlgEquiv e g)) := by
  obtain ⟨V, hVopen, hVf⟩ := hf
  have hVnhds : (V : Set (A ≃ₐ[k] A)) ∈ 𝓝 (1 : A ≃ₐ[k] A) := hVopen.mem_nhds V.one_mem
  obtain ⟨F, hFfin, hFV⟩ :=
    (krullTopology_mem_nhds_one_iff k A (V : Set (A ≃ₐ[k] A))).mp hVnhds
  haveI : FiniteDimensional k F := hFfin
  let E : IntermediateField k Ω := F.map e.symm.toAlgHom
  haveI hEfin : FiniteDimensional k E := finiteDimensional_map_algEquiv e.symm F
  have hEmap : E.map e.toAlgHom = F := map_symm_map e F
  refine ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E, ?_⟩
  intro g hg u hu huH
  have huV : conjAlgEquiv e u ∈ V := by
    apply hFV
    have h1 : conjAlgEquiv e u ∈ (E.map e.toAlgHom).fixingSubgroup :=
      (conjAlgEquiv_mem_fixingSubgroup e E u).mpr hu
    rwa [hEmap] at h1
  have huH' : conjAlgEquiv e u ∈ H' := (hH u).mpr huH
  have hgH' : conjAlgEquiv e g ∈ H' := (hH g).mpr hg
  have key : f (conjAlgEquiv e (g * u)) = f (conjAlgEquiv e g) := by
    rw [map_mul]
    exact hVf _ hgH' _ huV huH'
  exact key

/-- `IsLocConst2` transports along conjugation. -/
theorem isLocConst2_conjAlgEquiv (e : Ω ≃ₐ[k] A)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} (hc : SSGRoute.IsLocConst2 c) :
    SSGRoute.IsLocConst2
      (fun σ τ : A ≃ₐ[k] A => c ((conjAlgEquiv e).symm σ) ((conjAlgEquiv e).symm τ)) := by
  obtain ⟨U, hUopen, hUc⟩ := hc
  have hUnhds : (U : Set (Ω ≃ₐ[k] Ω)) ∈ 𝓝 (1 : Ω ≃ₐ[k] Ω) := hUopen.mem_nhds U.one_mem
  obtain ⟨E, hEfin, hEU⟩ :=
    (krullTopology_mem_nhds_one_iff k Ω (U : Set (Ω ≃ₐ[k] Ω))).mp hUnhds
  haveI : FiniteDimensional k E := hEfin
  haveI hEmap : FiniteDimensional k (E.map e.toAlgHom) := finiteDimensional_map_algEquiv e E
  refine ⟨(E.map e.toAlgHom).fixingSubgroup, IntermediateField.fixingSubgroup_isOpen _, ?_⟩
  intro σ τ u v hu hv
  have huU : (conjAlgEquiv e).symm u ∈ U := by
    apply hEU
    have h1 : conjAlgEquiv e ((conjAlgEquiv e).symm u) ∈ (E.map e.toAlgHom).fixingSubgroup := by
      rw [MulEquiv.apply_symm_apply]; exact hu
    exact (conjAlgEquiv_mem_fixingSubgroup e E _).mp h1
  have hvU : (conjAlgEquiv e).symm v ∈ U := by
    apply hEU
    have h1 : conjAlgEquiv e ((conjAlgEquiv e).symm v) ∈ (E.map e.toAlgHom).fixingSubgroup := by
      rw [MulEquiv.apply_symm_apply]; exact hv
    exact (conjAlgEquiv_mem_fixingSubgroup e E _).mp h1
  change c ((conjAlgEquiv e).symm (σ * u)) ((conjAlgEquiv e).symm (τ * v)) =
    c ((conjAlgEquiv e).symm σ) ((conjAlgEquiv e).symm τ)
  rw [map_mul, map_mul]
  exact hUc _ _ _ _ huU hvU

end Constancy

end Work.SSGRoute

namespace Work.SSGRoute

open scoped Pointwise Topology

open Filter

/-! ## Places and involutions -/

section Places

variable {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω] [Field A] [Algebra k A]

theorem isFinPlace_comap (e : Ω ≃ₐ[k] A) (B : ValuationSubring A) :
    SSGRoute.IsFinPlace k (B.comap (e : Ω →+* A)) ↔ SSGRoute.IsFinPlace k B := by
  have hmem : ∀ x : k, x ∈ (B.comap (e : Ω →+* A)).comap (algebraMap k Ω) ↔
      x ∈ B.comap (algebraMap k A) := by
    intro x
    simp only [ValuationSubring.mem_comap]
    exact iff_of_eq (congrArg (fun z : A => z ∈ B) (e.commutes x))
  have h : (B.comap (e : Ω →+* A)).comap (algebraMap k Ω) = B.comap (algebraMap k A) :=
    SetLike.ext hmem
  unfold SSGRoute.IsFinPlace
  rw [h]

/-- `conjAlgEquiv e` carries the decomposition group of `B.comap e` onto the decomposition group
of `B`. -/
theorem mem_decomp_comap (e : Ω ≃ₐ[k] A) (B : ValuationSubring A) (σ : Ω ≃ₐ[k] Ω) :
    conjAlgEquiv e σ ∈ SSGRoute.decomp k B ↔
      σ ∈ SSGRoute.decomp k (B.comap (e : Ω →+* A)) := by
  set X : ValuationSubring Ω := B.comap (e : Ω →+* A) with hX
  have hXmem : ∀ x : Ω, x ∈ X ↔ e x ∈ B := fun x => ValuationSubring.mem_comap
  have hXcoe : ∀ x : Ω, x ∈ σ • X ↔ ∃ s : Ω, e s ∈ B ∧ σ s = x := by
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hσs⟩
      exact ⟨s, (hXmem s).mp hs, hσs⟩
    · rintro ⟨s, hs, hσs⟩
      exact ⟨s, (hXmem s).mpr hs, hσs⟩
  have hBcoe : ∀ y : A, y ∈ conjAlgEquiv e σ • B ↔
      ∃ b : A, b ∈ B ∧ e (σ (e.symm b)) = y := by
    intro y
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, hb, hbeq⟩
      exact ⟨b, hb, hbeq⟩
    · rintro ⟨b, hb, hbeq⟩
      exact ⟨b, hb, hbeq⟩
  have hA : (σ • X = X) ↔ (∀ t : Ω, e (σ t) ∈ B ↔ e t ∈ B) := by
    constructor
    · intro h t
      have key : e (σ t) ∈ B ↔ (σ t ∈ σ • X) := by
        rw [← hXmem (σ t)]
        exact ⟨fun h2 => h.symm ▸ h2, fun h2 => h ▸ h2⟩
      have key2 : (σ t ∈ σ • X) ↔ e t ∈ B := by
        rw [hXcoe (σ t)]
        exact ⟨fun ⟨s, hs, hst⟩ => by rwa [σ.injective hst] at hs,
          fun ht => ⟨t, ht, rfl⟩⟩
      rw [key, key2]
    · intro h
      ext x
      rw [hXcoe x]
      constructor
      · rintro ⟨s, hs, rfl⟩
        rw [hXmem, h s]
        exact hs
      · intro hx
        refine ⟨σ.symm x, ?_, by rw [σ.apply_symm_apply]⟩
        rw [hXmem] at hx
        rw [← h (σ.symm x), σ.apply_symm_apply]
        exact hx
  have hB : ((conjAlgEquiv e σ) • B = B) ↔ (∀ t : Ω, e (σ t) ∈ B ↔ e t ∈ B) := by
    constructor
    · intro h t
      have key : e (σ t) ∈ B ↔ ∃ b : A, b ∈ B ∧ e (σ (e.symm b)) = e (σ t) := by
        have h1 : e (σ t) ∈ B ↔ e (σ t) ∈ (conjAlgEquiv e σ) • B := by rw [h]
        rw [h1, hBcoe (e (σ t))]
      have key2 : (∃ b : A, b ∈ B ∧ e (σ (e.symm b)) = e (σ t)) ↔ e t ∈ B := by
        constructor
        · rintro ⟨b, hb, hbeq⟩
          have hb1 : e.symm b = t := σ.injective (e.injective hbeq)
          have hb' : b = e t := by rw [← AlgEquiv.apply_symm_apply e b, hb1]
          rwa [hb'] at hb
        · intro ht
          exact ⟨e t, ht, by rw [AlgEquiv.symm_apply_apply]⟩
      rw [key, key2]
    · intro h
      ext y
      rw [hBcoe y]
      constructor
      · rintro ⟨b, hb, hbeq⟩
        rw [← hbeq]
        have hb' : e (e.symm b) ∈ B := by rwa [AlgEquiv.apply_symm_apply]
        exact (h (e.symm b)).mpr hb'
      · intro hy
        refine ⟨e (σ.symm (e.symm y)), ?_, ?_⟩
        · have h1 : e (σ (σ.symm (e.symm y))) ∈ B := by
            rw [σ.apply_symm_apply, AlgEquiv.apply_symm_apply]; exact hy
          exact (h (σ.symm (e.symm y))).mp h1
        · show e (σ (e.symm (e (σ.symm (e.symm y))))) = y
          rw [AlgEquiv.symm_apply_apply, σ.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [SSGRoute.decomp, SSGRoute.decomp, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]
  exact hB.trans hA.symm

end Places

/-! ## Involutions -/

section Involutions

variable {k Ω A : Type} [Field k] [Field Ω] [Algebra k Ω] [Field A] [Algebra k A]

theorem conjAlgEquiv_mem_zpowers (e : Ω ≃ₐ[k] A) (σ₀ σ : Ω ≃ₐ[k] Ω) :
    conjAlgEquiv e σ ∈ Subgroup.zpowers (conjAlgEquiv e σ₀) ↔ σ ∈ Subgroup.zpowers σ₀ := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (conjAlgEquiv e).injective (by rw [map_zpow]; exact hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, map_zpow]⟩

theorem conjAlgEquiv_involution (e : Ω ≃ₐ[k] A) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) :
    conjAlgEquiv e σ ^ 2 = 1 := by
  rw [← map_pow, hσ, map_one]

end Involutions

/-! ## Push-forward of local coboundaries along an equivariant coefficient map -/

section Push

variable {Γ G M N : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]

theorem isCoboundary2On_map (χ : M →+ N) (hχ : Work.GroupCohomology.IsEquivariant G χ)
    {act : Γ →* G} {H : Subgroup Γ} {c : Γ → Γ → M}
    (hc : SSGRoute.IsCoboundary2On act H c) :
    SSGRoute.IsCoboundary2On act H (fun g h => χ (c g h)) := by
  obtain ⟨b, hb, hbc⟩ := hc
  refine ⟨fun g => χ (b g), ?_, ?_⟩
  · obtain ⟨U, hU, hUb⟩ := hb
    exact ⟨U, hU, fun g hg u hu huH => by
      show χ (b (g * u)) = χ (b g)
      rw [hUb g hg u hu huH]⟩
  · intro g hg h hh
    show χ (c g h) = act g • χ (b h) - χ (b (g * h)) + χ (b g)
    rw [hbc g hg h hh, map_add, map_sub, hχ]

end Push

end Work.SSGRoute

namespace Work.SSGRoute

open scoped Pointwise Topology

open Filter

/-! ## The coefficient identification `𝔽_p ≅ μ_p` when `μ_p ⊆ k` -/

section Coeff

/-- A primitive `p`-th root of unity in `k̄`, obtained by pushing one in `k` forward. -/
noncomputable def rootOfUnityUnit (k : Type) [Field k] (p : ℕ) [Fact p.Prime]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p) : (AlgebraicClosure k)ˣ :=
  ((hμ.choose_spec.map_of_injective (f := algebraMap k (AlgebraicClosure k))
    (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k))).isUnit
      (Fact.out : p.Prime).ne_zero).unit

theorem isPrimitiveRoot_rootOfUnityUnit (k : Type) [Field k] (p : ℕ) [Fact p.Prime]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p) :
    IsPrimitiveRoot (rootOfUnityUnit k p hμ) p := by
  have hζA : IsPrimitiveRoot (algebraMap k (AlgebraicClosure k) hμ.choose) p :=
    hμ.choose_spec.map_of_injective (f := algebraMap k (AlgebraicClosure k))
      (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k))
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : IsPrimitiveRoot (↑((hζA.isUnit hp).unit) : AlgebraicClosure k) p := by
    rw [IsUnit.unit_spec]; exact hζA
  exact IsPrimitiveRoot.coe_units_iff.mp this

/-- The additive isomorphism `𝔽_p ≅ μ_p(k̄)`. -/
noncomputable def muAddEquiv (k : Type) [Field k] (p : ℕ) [Fact p.Prime]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p) :
    Triv p ≃+ Additive (rootsOfUnity p (AlgebraicClosure k)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let e : Multiplicative (ZMod p) ≃* ↥(rootsOfUnity p (AlgebraicClosure k)) :=
    zr (isPrimitiveRoot_rootOfUnityUnit k p hμ)
  exact
    { toFun := fun x => Additive.ofMul (e (Multiplicative.ofAdd x))
      invFun := fun y => Multiplicative.toAdd (e.symm (Additive.toMul y))
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_add' := fun x y => by
        show Additive.ofMul (e (Multiplicative.ofAdd (x + y))) =
          Additive.ofMul (e (Multiplicative.ofAdd x)) +
            Additive.ofMul (e (Multiplicative.ofAdd y))
        rw [show Multiplicative.ofAdd (x + y) =
          Multiplicative.ofAdd x * Multiplicative.ofAdd y from rfl, map_mul]
        rfl }

theorem muAddEquiv_equivariant (k : Type) [Field k] (p : ℕ) [Fact p.Prime]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p) :
    Work.GroupCohomology.IsEquivariant (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      (muAddEquiv k p hμ : Triv p →+ Additive (rootsOfUnity p (AlgebraicClosure k))) := by
  intro g a
  show muAddEquiv k p hμ (g • a) = g • muAddEquiv k p hμ a
  rw [triv_smul p (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) g a]
  exact (Work.AbsoluteKummer.smul_rootsOfUnity (k := k) hμ.choose_spec g
    (muAddEquiv k p hμ a)).symm

theorem muAddEquiv_symm_equivariant (k : Type) [Field k] (p : ℕ) [Fact p.Prime]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p) :
    Work.GroupCohomology.IsEquivariant (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
      ((muAddEquiv k p hμ).symm : Additive (rootsOfUnity p (AlgebraicClosure k)) →+ Triv p) := by
  intro g a
  show (muAddEquiv k p hμ).symm (g • a) = g • (muAddEquiv k p hμ).symm a
  rw [Work.AbsoluteKummer.smul_rootsOfUnity (k := k) hμ.choose_spec g a,
    triv_smul p (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) g _]

theorem smul_kummerIota_eq (k : Type) [Field k] (p : ℕ) [Fact p.Prime]
    (hμ : ∃ ζ : k, IsPrimitiveRoot ζ p)
    (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)
    (a : Additive (rootsOfUnity p (AlgebraicClosure k))) :
    σ • Work.AbsoluteKummer.Kummer.kummerIota (k := k) p a =
      Work.AbsoluteKummer.Kummer.kummerIota (k := k) p a := by
  rw [← Work.AbsoluteKummer.Kummer.kummerIota_equivariant (k := k) p σ a,
    Work.AbsoluteKummer.smul_rootsOfUnity (k := k) hμ.choose_spec σ a]

end Coeff

/-! ## An equivariant isomorphism of coefficients induces an injection on `H²` -/

theorem mapH2_injective_of_addEquiv {G : Type} [TopologicalSpace G] [Group G]
    {M N : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup N] [DistribMulAction G N]
    (φ : M ≃+ N) (hφ : Work.GroupCohomology.IsEquivariant G (φ : M →+ N))
    (hφ' : Work.GroupCohomology.IsEquivariant G (φ.symm : N →+ M)) :
    Function.Injective (Work.AbsoluteKummer.mapH2 (G := G) (φ : M →+ N) hφ) := by
  have hleft : ∀ x : Work.AbsoluteKummer.H2 G M,
      Work.AbsoluteKummer.mapH2 (G := G) (φ.symm : N →+ M) hφ'
        (Work.AbsoluteKummer.mapH2 (G := G) (φ : M →+ N) hφ x) = x := by
    intro x
    refine Work.AbsoluteKummer.SES.H2_induction_on
      (C := fun y => Work.AbsoluteKummer.mapH2 (G := G) (φ.symm : N →+ M) hφ'
        (Work.AbsoluteKummer.mapH2 (G := G) (φ : M →+ N) hφ y) = y) x ?_
    intro c
    have hcomp : ((φ.symm : N →+ M).comp (φ : M →+ N)) = AddMonoidHom.id M := by
      ext x; simp
    rw [← Work.AbsoluteKummer.mapH2_comp_H2π (G := G) (φ : M →+ N) (φ.symm : N →+ M) hφ hφ' c]
    simpa only [hcomp] using Work.AbsoluteKummer.mapH2_id_H2π (G := G) c
  intro x y hxy
  rw [← hleft x, ← hleft y, hxy]

end Work.SSGRoute
