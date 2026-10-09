import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.vfShared
import Submission.Work.SSGRoute.PT.archSwapHalf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **Existence of the level-`L` cocycle of the involution pairing**, at a *global* locally
constant cocycle `b`.

`b` is a `1`-cocycle on all of `G_k` (`IsCocycleOn … ⊤ b`) which is locally constant
(`IsLocConstOn ⊤ b`), so it factors through `Gal(L₀/k)` for a finite Galois level `L₀` (a constancy
level: `IsLocConstOn`'s open subgroup is open, hence of finite index).  Enlarging so that an open
normal subgroup `U ⊆ Gal(Ω/L₀) ∩ Gal(Ω/K)` with `c ∉ U` is fixed (`c ≠ 1`, Krull separation) gives a
finite Galois level `L = Ω^U ≥ K` with `res_L c ≠ 1` through which `b` still factors; the factor `ψ`
is well defined because `res k L` is surjective, and its cocycle condition follows from `hb` because
`galRes k ↥K ↥L ∘ res k L = res k K`.

This is the existence half of the `Classical.choose` that defines `G1⁺`'s pairing at `⟨c⟩` (v6's
`hpairArch` is quantified over every such `ψ`, so the pairing must be independent of the choice; that
independence is a separate `H1π`-restriction lemma). -/
theorem archPairData_exists (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (hl : SSGRoute.IsLocConstOn ⊤ b) :
    ∃ (L : IntermediateField k Ω) (_ : FiniteDimensional k L) (_ : IsGalois k L) (hKL : K ≤ L),
      SSGRoute.res k L c ≠ 1 ∧
      (letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
       letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
       letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
       ∃ ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T,
         (∀ g h : ↥L ≃ₐ[k] ↥L,
           ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g) ∧
         ∀ σ : Ω ≃ₐ[k] Ω, b σ = ψ (SSGRoute.res k L σ)) := by
  classical
  -- the constancy subgroup of `b` is an open subgroup of `G_k`
  obtain ⟨U₀, hU₀open, hU₀⟩ := hl
  have hb_inv : ∀ σ : Ω ≃ₐ[k] Ω, ∀ u ∈ U₀, b (σ * u) = b σ :=
    fun σ u hu => hU₀ σ (Subgroup.mem_top σ) u hu (Subgroup.mem_top u)
  -- Krull separation: an open subgroup of `G_k` avoiding the non-identity element `c`
  obtain ⟨E, _hEfin, hcE⟩ :
      ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧ c ∉ E.fixingSubgroup := by
    have h1c : (1 : Ω ≃ₐ[k] Ω) ≠ c := fun h => hc1 h.symm
    have hnhds : ({c}ᶜ : Set (Ω ≃ₐ[k] Ω)) ∈ nhds (1 : Ω ≃ₐ[k] Ω) :=
      isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff] using h1c)
    obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff k Ω ({c}ᶜ)).mp hnhds
    exact ⟨E, hEfin, fun hc => hEsub hc (by simp)⟩
  -- the open subgroup of which we take the fixed field
  set U : Subgroup (Ω ≃ₐ[k] Ω) := U₀ ⊓ K.fixingSubgroup ⊓ E.fixingSubgroup with hUdef
  have hUopen : IsOpen (U : Set (Ω ≃ₐ[k] Ω)) := by
    rw [hUdef]
    exact (hU₀open.inter (IntermediateField.fixingSubgroup_isOpen K)).inter
      (IntermediateField.fixingSubgroup_isOpen E)
  -- a finite normal level `L ⊇ K` whose fixing subgroup lies inside `U`
  obtain ⟨L, hLfin, hLnorm, hKL, hfixL⟩ :=
    Work.SSGRoute.PT.exists_finiteNormal_fixingSubgroup_le_of_isOpen k Ω K U hUopen
  have hLgal : IsGalois k ↥L := by
    haveI : FiniteDimensional k ↥L := hLfin
    haveI : Normal k ↥L := hLnorm
    infer_instance
  haveI : FiniteDimensional k L := hLfin
  haveI : Normal k L := hLnorm
  haveI : IsGalois k L := hLgal
  have hfixU₀ : L.fixingSubgroup ≤ U₀ := fun σ hσ => (hfixL hσ).1.1
  have hfixE : L.fixingSubgroup ≤ E.fixingSubgroup := fun σ hσ => (hfixL hσ).2
  -- `c` survives at the level `L`
  have hcL : SSGRoute.res k L c ≠ 1 := by
    intro h
    have hc : c ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker (E := L)]
      exact MonoidHom.mem_ker.mpr h
    exact hcE (hfixE hc)
  -- `b` is constant on the fibres of the restriction map to `L`
  have hb_coset : ∀ σ τ : Ω ≃ₐ[k] Ω, σ⁻¹ * τ ∈ L.fixingSubgroup → b τ = b σ := by
    intro σ τ h
    have h1 : b (σ * (σ⁻¹ * τ)) = b σ := hb_inv σ _ (hfixU₀ h)
    rwa [mul_inv_cancel_left] at h1
  -- the level-`L` structure maps, matching the statement
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  letI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- restriction to `L` is onto, `L/k` being normal
  have hsurj : Function.Surjective (SSGRoute.res k L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  -- the descended cocycle
  let ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T :=
    fun g => b (Classical.choose (hsurj g))
  have hψfac : ∀ σ : Ω ≃ₐ[k] Ω, ψ (SSGRoute.res k L σ) = b σ := by
    intro σ
    have hmem : σ⁻¹ * Classical.choose (hsurj (SSGRoute.res k L σ)) ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker (E := L), MonoidHom.mem_ker]
      rw [map_mul, map_inv, Classical.choose_spec (hsurj (SSGRoute.res k L σ)), inv_mul_cancel]
    have h : b (Classical.choose (hsurj (SSGRoute.res k L σ))) = b σ := by
      have h2 : b (σ * (σ⁻¹ * Classical.choose (hsurj (SSGRoute.res k L σ)))) = b σ :=
        hb_inv σ _ (hfixU₀ hmem)
      rwa [mul_inv_cancel_left] at h2
    show b (Classical.choose (hsurj (SSGRoute.res k L σ))) = b σ
    exact h
  have hψcoc : ∀ g h : ↥L ≃ₐ[k] ↥L,
      ψ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g := by
    intro g h
    have hg : SSGRoute.res k L (Classical.choose (hsurj g)) = g := Classical.choose_spec (hsurj g)
    have hh : SSGRoute.res k L (Classical.choose (hsurj h)) = h := Classical.choose_spec (hsurj h)
    have hmem : ((Classical.choose (hsurj g) * Classical.choose (hsurj h))⁻¹ *
        Classical.choose (hsurj (g * h))) ∈ L.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker (E := L), MonoidHom.mem_ker]
      rw [map_mul, map_inv, map_mul, hg, hh, Classical.choose_spec (hsurj (g * h)), inv_mul_cancel]
    have h1 : ψ (g * h) = b (Classical.choose (hsurj g) * Classical.choose (hsurj h)) := by
      show b (Classical.choose (hsurj (g * h)))
        = b (Classical.choose (hsurj g) * Classical.choose (hsurj h))
      exact hb_coset _ _ hmem
    have htrans := SSGRoute.PTExt.galRes_trans (k := k) (K := ↥K) (L := ↥L) (L' := Ω)
      (Classical.choose (hsurj g))
    calc ψ (g * h) = b (Classical.choose (hsurj g) * Classical.choose (hsurj h)) := h1
      _ = b (Classical.choose (hsurj g)) +
            (SSGRoute.res k K (Classical.choose (hsurj g))) • b (Classical.choose (hsurj h)) :=
            hb _ (Subgroup.mem_top _) _ (Subgroup.mem_top _)
      _ = b (Classical.choose (hsurj g)) +
            SSGRoute.PTExt.galRes k (↥K) (↥L) g • b (Classical.choose (hsurj h)) := by
            congr 1
            rw [← htrans, hg]
      _ = ψ g + SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h := by
            rw [show ψ g = b (Classical.choose (hsurj g)) from rfl,
                show ψ h = b (Classical.choose (hsurj h)) from rfl]
      _ = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ h + ψ g := add_comm _ _
  exact ⟨L, hLfin, hLgal, hKL, hcL, ψ, hψcoc, fun σ => (hψfac σ).symm⟩

end Work.SSGRoute.PT
