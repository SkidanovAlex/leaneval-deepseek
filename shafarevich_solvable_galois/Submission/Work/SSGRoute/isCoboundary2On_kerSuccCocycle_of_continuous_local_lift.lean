import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.kerSuccCocycle_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The section cocycle is locally a coboundary, from a *continuous* local lift

`φ : G_ℚ →* Γ_m^τ` is a homomorphism with open kernel, `s` a normalized section of the
projection `flowGroupSucc : Γ_m^{τ+1} →* Γ_m^τ`, and `l : H →* Γ_m^{τ+1}` a homomorphism on a
subgroup `H ≤ G_ℚ` lifting `φ|_H` (`LiftsFlowAt`) whose kernel is **open** in `H`.

Then the section `2`-cocycle `κ = kerSuccCocycle φ s` has a primitive `b` which is *locally
constant on `H`*, i.e. `κ|_H` is a continuous coboundary — what is needed to feed
`SSGRoute.sha2_image_of_Hm2` at a place `A` with `H = decomp ℚ A`.

The primitive is `b(σ) = s(φ σ) · l(σ)⁻¹` (`σ ∈ H`).  Its local constancy uses exactly the two
openness hypotheses: on `U ∩ H`, with `U` an open subgroup of `G_ℚ` contained in `ker l ∩ ker φ`,
both `φ` and `l` are unchanged.

Without the continuity hypothesis on `l` the statement is false: the abstract splitting of the
pullback extension does not imply its splitting over the finite quotient `φ(H)`.
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open _root_.SSGRoute
open Work.CohomologicalShrinking

/-- Elementary rearrangement in an additive commutative group. -/
private theorem add_comm_group_identity {M : Type*} [AddCommGroup M] (A B C K : M)
    (h : (-A + -C) + K = -B) : K = (C + -B) + A := by
  rw [← h]
  abel

theorem isCoboundary2On_kerSuccCocycle_of_continuous_local_lift (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hopen : IsOpen (φ.ker : Set SSGRoute.GalQ))
    (s : Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j →
      Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (s x) = x) (h1 : s 1 = 1)
    (H : Subgroup SSGRoute.GalQ)
    (l : ↥H →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hl : ∀ σ : ↥H, SSGRoute.LiftsFlowAt (l σ) (φ σ))
    (hcont : IsOpen (l.ker : Set ↥H)) :
    ∃ b : SSGRoute.GalQ → Additive ↥(Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker,
      SSGRoute.IsLocConstOn H b ∧
      ∀ σ ∈ H, ∀ τ ∈ H,
        Work.SSGRoute.kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ
          = Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
                (Work.SSGRoute.flowGroupSucc p (K ≃ₐ[ℚ] K) m i j)
                (s (φ σ)) (Additive.toMul (b τ))) - b (σ * τ) + b σ := by
  classical
  -- `l` is a lift of `φ|_H`
  have hcomp : ∀ σ : ↥H,
      flowGroupSucc p (K ≃ₐ[ℚ] K) m i j (l σ) = φ σ := fun σ =>
    (liftsFlowAt_iff_flowGroupSucc p K m i j (l σ) (φ σ)).mp (hl σ)
  -- the kernel elements `d σ = s (φ σ) * (l σ)⁻¹`
  have hmem : ∀ σ : ↥H,
      s (φ σ) * (l σ)⁻¹ ∈ (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker := by
    intro σ
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, hcomp σ, mul_inv_cancel]
  let d : ↥H → ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker :=
    fun σ => ⟨s (φ σ) * (l σ)⁻¹, hmem σ⟩
  have hcomm : ∀ a b : ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker, a * b = b * a :=
    fun a b =>
      (flowGroupSucc_ker_isMulCommutative p (K ≃ₐ[ℚ] K) m i j).is_comm.comm a b
  -- the induced addition on `Additive (ker)` is commutative
  have hadd : ∀ x y : Additive ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker, x + y = y + x := by
    intro x y
    have h := congrArg Additive.ofMul (hcomm (Additive.toMul x) (Additive.toMul y))
    simpa using h
  -- the section cocycle as a kernel element
  have hκ : ∀ σ τ : ↥H,
      kerSuccCocycle p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ =
        Additive.ofMul (⟨s (φ σ) * s (φ τ) * (s (φ (σ * τ)))⁻¹, by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hs, hs, hs]; simp⟩ :
            ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker) := by
    intro σ τ
    apply Additive.ext
    exact Subtype.ext rfl
  -- the key multiplicative identity, in the abelian kernel:
  -- `(d a)⁻¹ * (conj (d b))⁻¹ * κ = (d (a * b))⁻¹`
  have key_mul : ∀ a b : ↥H,
      (d a)⁻¹ * (Work.AbsoluteGalois.conjKernelMul
            (flowGroupSucc p (K ≃ₐ[ℚ] K) m i j) (s (φ a)) (d b))⁻¹ *
          kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j φ s hs a b
        = (d (a * b))⁻¹ := by
    intro a b
    apply Subtype.ext
    simp only [d, Subgroup.coe_mul, Subgroup.coe_inv, Work.AbsoluteGalois.conjKernelMul,
      kerSuccCocycleMul]
    rw [map_mul l a b]
    group
  -- openness: an open *subgroup* of `G_ℚ` on which both `l` and `φ` are trivial
  obtain ⟨U0, hU0open, hU0pre⟩ := isOpen_induced_iff.mp hcont
  have h1mem : (1 : SSGRoute.GalQ) ∈ U0 := by
    have h1k : (1 : ↥H) ∈ (l.ker : Set ↥H) := Subgroup.one_mem _
    rw [← hU0pre] at h1k
    simpa using h1k
  obtain ⟨E, hEfin, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff ℚ SSGRoute.QBar U0).mp (hU0open.mem_nhds h1mem)
  haveI : FiniteDimensional ℚ ↥E := hEfin
  have hEopen : IsOpen ((E.fixingSubgroup : Subgroup SSGRoute.GalQ) : Set SSGRoute.GalQ) :=
    IntermediateField.fixingSubgroup_isOpen E
  refine ⟨fun σ => if h : σ ∈ H then Additive.ofMul (d ⟨σ, h⟩) else 0, ?_, ?_⟩
  · -- local constancy of `b`
    refine ⟨E.fixingSubgroup ⊓ φ.ker, hEopen.inter hopen, ?_⟩
    intro g hg u hu huH
    have hgu : g * u ∈ H := H.mul_mem hg huH
    have huU0 : u ∈ U0 := hEsub hu.1
    have hul : l ⟨u, huH⟩ = 1 := by
      have hk : (⟨u, huH⟩ : ↥H) ∈ (l.ker : Set ↥H) := by
        rw [← hU0pre]
        simpa using huU0
      simpa using hk
    have hφu : φ u = 1 := MonoidHom.mem_ker.mp hu.2
    have hφ : φ (g * u) = φ g := by rw [map_mul, hφu, mul_one]
    have hl' : l ⟨g * u, hgu⟩ = l ⟨g, hg⟩ := by
      have hsplit : (⟨g * u, hgu⟩ : ↥H) = ⟨g, hg⟩ * ⟨u, huH⟩ := Subtype.ext rfl
      rw [hsplit, map_mul, hul, mul_one]
    simp only [dif_pos hg, dif_pos hgu]
    apply Additive.ofMul.injective
    apply Subtype.ext
    simp only [d, hφ, hl']
  · -- the coboundary identity
    intro σ hσ τ hτ
    have hστ : σ * τ ∈ H := H.mul_mem hσ hτ
    dsimp only
    have hbσ : (if h : σ ∈ H then Additive.ofMul (d ⟨σ, h⟩) else 0)
        = Additive.ofMul (d ⟨σ, hσ⟩) := dif_pos hσ
    have hbτ : (if h : τ ∈ H then Additive.ofMul (d ⟨τ, h⟩) else 0)
        = Additive.ofMul (d ⟨τ, hτ⟩) := dif_pos hτ
    have hbστ : (if h : σ * τ ∈ H then Additive.ofMul (d ⟨σ * τ, h⟩) else 0)
        = Additive.ofMul (d (⟨σ, hσ⟩ * ⟨τ, hτ⟩)) := by
      rw [dif_pos hστ]
      exact congrArg (fun x => Additive.ofMul (d x)) (Subtype.ext rfl)
    rw [hbσ, hbτ, hbστ, toMul_ofMul]
    -- the additive form of the key identity
    have h2 := congrArg Additive.ofMul (key_mul ⟨σ, hσ⟩ ⟨τ, hτ⟩)
    rw [ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, ofMul_inv] at h2
    dsimp only at h2
    change Additive.ofMul (kerSuccCocycleMul p (K ≃ₐ[ℚ] K) m i j φ s hs σ τ) = _
    simp only [sub_eq_add_neg]
    letI : CommGroup ↥(flowGroupSucc p (K ≃ₐ[ℚ] K) m i j).ker :=
      { (inferInstance : Group _) with mul_comm := hcomm }
    exact add_comm_group_identity _ _ _ _ h2

end Work.SSGRoute
