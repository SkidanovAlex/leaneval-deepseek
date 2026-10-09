import Mathlib
import Submission.Work.PTCore.TransgressionDefs
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local constancy of the `E`-correction `corrE`

The correction term `corrE S c₀ g = - c₀ (projG g) (coorG g)` (with `0` outside the decomposition
group `D`) is (uniformly) locally constant on `D` whenever the constituent `2`-cochain `c₀` is
locally constant on `D × D`.

The point is that, restricted to `D`, the pair `(projG, coorG)` is *continuous*: the two
coordinates of the semidirect decomposition `D = I ⋊ C` are continuous
(`Work.SSGRoute.HSTwoRow.continuous_ip_proj`).  Hence, after replacing the local-constancy subgroup
of `c₀` by its (open) normal core `W`, the set of `d ∈ D` with `projG d ∈ W` and `coorG d ∈ W` is an
open neighbourhood of `1` in `D`; it contains `V ∩ D` for some open subgroup `V ≤ G_k`
(`Work.SSGRoute.exists_openSubgroup_comap_le`).  For `u ∈ V ∩ D` the two arguments of `c₀` change
by elements of `W ∩ D`, so the local constancy of `c₀` applies.
-/

open scoped Pointwise
open Classical

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.PTCore

/-- `projG` of the identity is the identity. -/
theorem projG_one {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : Work.PTCore.DCtx k Ω) :
    Work.PTCore.projG S (1 : Ω ≃ₐ[k] Ω) = 1 := by
  have hone : (1 : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k S.A := (SSGRoute.decomp k S.A).one_mem
  have h := Work.SSGRoute.HS.factor_unique S.A S.I S.σ S.hinf (S.I.one_mem)
    (Work.PTCore.ipG_mem_I S hone) ((Subgroup.topologicalClosure _).one_mem)
    (Work.PTCore.projG_mem_C S hone) ?_
  · exact h.2.symm
  · simp only [Work.PTCore.ipG_mul_projG S hone, mul_one]

/-- `coorG` of the identity is the identity. -/
theorem coorG_one {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : Work.PTCore.DCtx k Ω) :
    Work.PTCore.coorG S (1 : Ω ≃ₐ[k] Ω) = 1 := by
  have hone : (1 : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k S.A := (SSGRoute.decomp k S.A).one_mem
  rw [Work.PTCore.coorG_of_mem S hone, projG_one S, inv_one, one_mul]

/-- The `C`-coordinate `projG` is continuous as a function on the decomposition group. -/
theorem continuous_projG_subtype {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : Work.PTCore.DCtx k Ω) :
    Continuous (fun d : ↥(SSGRoute.decomp k S.A) => Work.PTCore.projG S (d : Ω ≃ₐ[k] Ω)) := by
  have hC : Subgroup.topologicalClosure (Subgroup.zpowers S.σ) ≤ SSGRoute.decomp k S.A :=
    Work.SSGRoute.HS.CC_le_DD S.A S.σ S.hσ
  have heq : (fun d : ↥(SSGRoute.decomp k S.A) => Work.PTCore.projG S (d : Ω ≃ₐ[k] Ω))
      = fun d => ((Work.SSGRoute.HS.proj S.A S.I S.σ S.hI S.hnorm hC S.hsup d :
          ↥(Subgroup.topologicalClosure (Subgroup.zpowers S.σ))) : Ω ≃ₐ[k] Ω) := by
    funext d
    exact Work.PTCore.projG_of_mem S d.2
  rw [heq]
  exact (Work.SSGRoute.HSTwoRow.continuous_ip_proj (k := k) (Ω := Ω) (A := S.A) (I := S.I)
    (σ := S.σ) (hI := S.hI) (hIclosed := S.hIclosed) (hnorm := S.hnorm) (hσ := S.hσ)
    (hsup := S.hsup) (hinf := S.hinf)).1

/-- The `I`-coordinate `coorG` is continuous as a function on the decomposition group. -/
theorem continuous_coorG_subtype {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (S : Work.PTCore.DCtx k Ω) :
    Continuous (fun d : ↥(SSGRoute.decomp k S.A) => Work.PTCore.coorG S (d : Ω ≃ₐ[k] Ω)) := by
  have heq : (fun d : ↥(SSGRoute.decomp k S.A) => Work.PTCore.coorG S (d : Ω ≃ₐ[k] Ω))
      = fun d : ↥(SSGRoute.decomp k S.A) =>
          (Work.PTCore.projG S (d : Ω ≃ₐ[k] Ω))⁻¹ * (d : Ω ≃ₐ[k] Ω) := by
    funext d
    exact Work.PTCore.coorG_of_mem S d.2
  rw [heq]
  exact (continuous_projG_subtype S).inv.mul continuous_subtype_val

theorem corrE_isLocConstOn {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : Work.PTCore.DCtx k Ω) (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c₀ : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hc : SSGRoute.IsLocConst2On p k Ω K M (SSGRoute.decomp k S.A) c₀) :
    SSGRoute.IsLocConstOn (SSGRoute.decomp k S.A) (Work.PTCore.corrE (M := M) S c₀) := by
  classical
  obtain ⟨U₀, hU₀open, hU₀⟩ := hc
  -- the open *normal* subgroup `W = U₀.normalCore` on which `c₀` is still locally constant
  let W : Subgroup (Ω ≃ₐ[k] Ω) := U₀.normalCore
  have hWnorm : W.Normal := Subgroup.normalCore_normal U₀
  have hWle : W ≤ U₀ := Subgroup.normalCore_le U₀
  have hWopen : IsOpen (W : Set (Ω ≃ₐ[k] Ω)) := by
    have hU0fin : U₀.FiniteIndex := by
      rw [Subgroup.finiteIndex_iff_finite_quotient]
      haveI : DiscreteTopology ((Ω ≃ₐ[k] Ω) ⧸ U₀) := QuotientGroup.discreteTopology_iff.mpr hU₀open
      exact finite_of_compact_of_discrete
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
      (Subgroup.normalCore_isClosed U₀ (Subgroup.isClosed_of_isOpen U₀ hU₀open))
  have hcont_proj : Continuous (fun d : ↥(SSGRoute.decomp k S.A) =>
      Work.PTCore.projG S (d : Ω ≃ₐ[k] Ω)) := continuous_projG_subtype S
  have hcont_coor : Continuous (fun d : ↥(SSGRoute.decomp k S.A) =>
      Work.PTCore.coorG S (d : Ω ≃ₐ[k] Ω)) := continuous_coorG_subtype S
  -- the open neighbourhood of `1 ∈ D` on which both coordinates already lie in `W`
  let Sset : Set ↥(SSGRoute.decomp k S.A) :=
    {d | Work.PTCore.projG S (d : Ω ≃ₐ[k] Ω) ∈ W ∧ Work.PTCore.coorG S (d : Ω ≃ₐ[k] Ω) ∈ W}
  have hSopen : IsOpen Sset :=
    (hWopen.preimage hcont_proj).inter (hWopen.preimage hcont_coor)
  have hS1 : (1 : ↥(SSGRoute.decomp k S.A)) ∈ Sset := by
    refine ⟨?_, ?_⟩
    · show Work.PTCore.projG S ((1 : ↥(SSGRoute.decomp k S.A)) : Ω ≃ₐ[k] Ω) ∈ W
      rw [show ((1 : ↥(SSGRoute.decomp k S.A)) : Ω ≃ₐ[k] Ω) = 1 from rfl, projG_one S]
      exact W.one_mem
    · show Work.PTCore.coorG S ((1 : ↥(SSGRoute.decomp k S.A)) : Ω ≃ₐ[k] Ω) ∈ W
      rw [show ((1 : ↥(SSGRoute.decomp k S.A)) : Ω ≃ₐ[k] Ω) = 1 from rfl, coorG_one S]
      exact W.one_mem
  -- lift the open neighbourhood from `D` to an open subgroup `V ≤ G_k`
  obtain ⟨O, hOopen, hOeq⟩ := isOpen_induced_iff.mp hSopen
  have h1O : (1 : Ω ≃ₐ[k] Ω) ∈ O := by
    have h : (1 : ↥(SSGRoute.decomp k S.A)) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]; exact hS1
    exact h
  obtain ⟨F, hFfin, hFnorm, hFsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω O).mp (hOopen.mem_nhds h1O)
  haveI : FiniteDimensional k F := hFfin
  haveI : Normal k F := hFnorm
  obtain ⟨V, hVopen, hVsub⟩ := Work.SSGRoute.exists_openSubgroup_comap_le
    (SSGRoute.decomp k S.A)
    (Subgroup.comap (Subgroup.subtype (SSGRoute.decomp k S.A)) (F.fixingSubgroup :
      Subgroup (Ω ≃ₐ[k] Ω)))
    (by
      rw [Subgroup.coe_comap]
      exact (IntermediateField.fixingSubgroup_isOpen F).preimage continuous_subtype_val)
  refine ⟨V, hVopen, ?_⟩
  intro g hg u hu huD
  have huN : (⟨u, huD⟩ : ↥(SSGRoute.decomp k S.A)) ∈
      Subgroup.comap (Subgroup.subtype (SSGRoute.decomp k S.A))
        (F.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) := by
    rw [Subgroup.mem_comap]
    exact hVsub hu
  have huO : u ∈ O := by
    have := huN
    rw [Subgroup.mem_comap] at this
    exact hFsub this
  have huS : (⟨u, huD⟩ : ↥(SSGRoute.decomp k S.A)) ∈ Sset := by
    rw [← hOeq]
    exact huO
  have hpuW : Work.PTCore.projG S u ∈ W := huS.1
  have hkuW : Work.PTCore.coorG S u ∈ W := huS.2
  have hguD : g * u ∈ SSGRoute.decomp k S.A := mul_mem hg huD
  have hpD : Work.PTCore.projG S u ∈ SSGRoute.decomp k S.A := Work.PTCore.projG_mem_D S huD
  have hkD : Work.PTCore.coorG S u ∈ SSGRoute.decomp k S.A :=
    S.hI (Work.PTCore.coorG_mem_I S huD)
  have hPD : Work.PTCore.projG S g ∈ SSGRoute.decomp k S.A := Work.PTCore.projG_mem_D S hg
  have hhD : Work.PTCore.coorG S g ∈ SSGRoute.decomp k S.A :=
    S.hI (Work.PTCore.coorG_mem_I S hg)
  -- the "correction" `w = h⁻¹ p⁻¹ h p k` lies in `W` and in `D`
  have hwW : (Work.PTCore.coorG S g)⁻¹ * (Work.PTCore.projG S u)⁻¹ * (Work.PTCore.coorG S g)
      * (Work.PTCore.projG S u) * (Work.PTCore.coorG S u) ∈ W := by
    have hconj : (Work.PTCore.coorG S g)⁻¹ * (Work.PTCore.projG S u)⁻¹ *
        (Work.PTCore.coorG S g) ∈ W := by
      have h1 := hWnorm.conj_mem (Work.PTCore.projG S u)⁻¹ (W.inv_mem hpuW)
        (Work.PTCore.coorG S g)⁻¹
      simpa using h1
    exact W.mul_mem (W.mul_mem hconj hpuW) hkuW
  have hwD : (Work.PTCore.coorG S g)⁻¹ * (Work.PTCore.projG S u)⁻¹ * (Work.PTCore.coorG S g)
      * (Work.PTCore.projG S u) * (Work.PTCore.coorG S u) ∈ SSGRoute.decomp k S.A := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhD) (Subgroup.inv_mem _ hpD)) hhD) hpD) hkD
  rw [Work.PTCore.corrE_of_mem S c₀ hguD, Work.PTCore.corrE_of_mem S c₀ hg]
  congr 1
  -- local constancy of `c₀` along `W` identifies the two arguments
  have hloc := hU₀ (Work.PTCore.projG S g) hPD (Work.PTCore.coorG S g) hhD
    (Work.PTCore.projG S u) (hWle hpuW)
    ((Work.PTCore.coorG S g)⁻¹ * (Work.PTCore.projG S u)⁻¹ * (Work.PTCore.coorG S g)
      * (Work.PTCore.projG S u) * (Work.PTCore.coorG S u)) (hWle hwW) hpD hwD
  rw [← hloc]
  congr 1
  · exact Work.PTCore.projG_mul S hg huD
  · rw [Work.PTCore.coorG_of_mem S hguD, Work.PTCore.projG_mul S hg huD,
      Work.PTCore.coorG_of_mem S hg, Work.PTCore.coorG_of_mem S huD]
    group

end Work.PTCore
