import Mathlib
import Submission.Work.PTCore.TransgressionDefs
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `chiExt` is locally constant on the decomposition group

`chiExt S χ = χ ∘ projG` on the decomposition group `D_A` (and `0` outside it), where `projG` is
the `C`-coordinate of the semidirect decomposition `D_A = I ⋊ C`.

Since `projG` is the `C`-coordinate, it is a group homomorphism `D_A → C`, and it is **continuous**
(`Work.SSGRoute.HSRow.continuous_proj`).  Hence the preimage `V ≤ D_A` of an open subgroup `U₀ ≤ G_k`
is an open subgroup of `D_A`; since `D_A` is closed in the compact totally disconnected group `G_k`,
one finds an open subgroup `U ≤ G_k` with `U ∩ D_A ⊆ V`.  Then for `g ∈ D_A` and `u ∈ U ∩ D_A`,

  `chiExt (g * u) = χ (projG (g * u)) = χ (projG g * projG u) = χ (projG g) = chiExt g`,

the middle equality being the local constancy of `χ` on `C`, which `u` inherits through `projG`.
-/

open Classical

namespace Work.PTCore

open Work.SSGRoute

theorem chiExt_isLocConstOn {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : Work.PTCore.DCtx k Ω) {M : Type} [AddCommGroup M]
    (χ : (Ω ≃ₐ[k] Ω) → M)
    (hχ : SSGRoute.IsLocConstOn (Subgroup.topologicalClosure (Subgroup.zpowers S.σ)) χ) :
    SSGRoute.IsLocConstOn (SSGRoute.decomp k S.A) (Work.PTCore.chiExt S χ) := by
  classical
  obtain ⟨U₀, hU₀open, hU₀⟩ := hχ
  -- The `C`-coordinate as a continuous map `↥D → G_k`.
  let p : ↥(SSGRoute.decomp k S.A) → (Ω ≃ₐ[k] Ω) := fun d =>
    ((Work.SSGRoute.HS.proj S.A S.I S.σ S.hI S.hnorm
      (Work.SSGRoute.HS.CC_le_DD S.A S.σ S.hσ) S.hsup d :
        ↥(Subgroup.topologicalClosure (Subgroup.zpowers S.σ))) : Ω ≃ₐ[k] Ω)
  have hpcont : Continuous p :=
    continuous_subtype_val.comp
      (Work.SSGRoute.HSRow.continuous_proj k Ω S.A S.I S.σ S.hI S.hnorm S.hσ S.hsup S.hinf
        S.hIclosed)
  -- Its preimage of `U₀` is open in `↥D`; realise it as `O ∩ ↥D` with `O` open in `G_k`.
  have hVopen : IsOpen (p ⁻¹' U₀) := hU₀open.preimage hpcont
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hVopen
  -- `1 ∈ O`
  have hp1 : p (⟨(1 : Ω ≃ₐ[k] Ω), (SSGRoute.decomp k S.A).one_mem⟩ :
      ↥(SSGRoute.decomp k S.A)) = 1 := by
    have h1 : p ⟨(1 : Ω ≃ₐ[k] Ω), (SSGRoute.decomp k S.A).one_mem⟩ =
        projG S (1 : Ω ≃ₐ[k] Ω) :=
      (projG_of_mem S (SSGRoute.decomp k S.A).one_mem).symm
    rw [h1, projG_eq_one_of_mem_I S S.I.one_mem]
  have h1O : (1 : Ω ≃ₐ[k] Ω) ∈ O := by
    have hmem : (⟨(1 : Ω ≃ₐ[k] Ω), (SSGRoute.decomp k S.A).one_mem⟩ :
        ↥(SSGRoute.decomp k S.A)) ∈ p ⁻¹' U₀ := by
      rw [Set.mem_preimage, hp1]
      exact U₀.one_mem
    rw [← hOeq] at hmem
    exact hmem
  -- An open subgroup of `G_k` inside `O`.
  obtain ⟨H, hHO⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOopen h1O
  refine ⟨(H : Subgroup (Ω ≃ₐ[k] Ω)), H.isOpen, ?_⟩
  intro g hg u huH huD
  have hgu : g * u ∈ SSGRoute.decomp k S.A := (SSGRoute.decomp k S.A).mul_mem hg huD
  -- `projG u ∈ U₀`, because `u ∈ H ⊆ O` and `u ∈ D`.
  have hpu : projG S u ∈ U₀ := by
    have hmem : p (⟨u, huD⟩ : ↥(SSGRoute.decomp k S.A)) ∈ U₀ := by
      have hOu : (⟨u, huD⟩ : ↥(SSGRoute.decomp k S.A)) ∈ Subtype.val ⁻¹' O := hHO huH
      rw [hOeq] at hOu
      exact hOu
    rwa [show p (⟨u, huD⟩ : ↥(SSGRoute.decomp k S.A)) = projG S u from
      (projG_of_mem S huD).symm] at hmem
  rw [chiExt_of_mem S χ hgu, chiExt_of_mem S χ hg, projG_mul S hg huD]
  exact hU₀ (projG S g) (projG_mem_C S hg) (projG S u) hpu (projG_mem_C S huD)

end Work.PTCore
