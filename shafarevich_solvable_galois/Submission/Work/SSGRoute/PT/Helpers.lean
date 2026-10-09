import Mathlib
import Mathlib.FieldTheory.Galois.Profinite
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HSRestrict
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.HS.Basic
import Submission.Work.SSGRoute.exists_openSubgroup_comap_le
import Submission.Work.SSGRoute.map_topologicalClosure_zpowers_subtype
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Helpers for the degree-`1` row of the Hochschild–Serre two-row decomposition

This module collects, in the namespace `Work.SSGRoute.PT`, the basic input for
`Work.SSGRoute.PT.hs_H1row`:

* `lcCocycleOn_zpowers_eq_zero_of_gen_eq_zero` — a locally constant `1`-cocycle on
  `C = closure (zpowers σ)` vanishing at `σ` vanishes on `C` (uniqueness of the value at `σ`);
* `continuous_ip_proj` — the two coordinates `ip`, `proj` of `D_A = I ⋊ C` are continuous;
* `res1_mem_invariants` — the restriction `H¹_loc(D_A,M) → H¹_loc(I,M)` lands in the invariants of
  `conj₁`;
* the group theory of the procyclic group `C = closure (zpowers σ)` coming from `hZ`
  (`σ` has infinite order, `C` is commutative, `C^n` is open, finite index subgroups of `C` are
  open, and every open normal `U ≤ C` contains an open normal `V` with `p ∣ [U : V]`);
* stability of `H⁰_loc(I,M) = M^I` under the action of `C`.
-/

open scoped Pointwise
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

lemma lcCocycleOn_zpowers_eq_zero_of_gen_eq_zero
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (σ : Ω ≃ₐ[k] Ω) (a : (Ω ≃ₐ[k] Ω) → M)
    (hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K)
      (Subgroup.topologicalClosure (Subgroup.zpowers σ)) a)
    (hlc : SSGRoute.IsLocConstOn (Subgroup.topologicalClosure (Subgroup.zpowers σ)) a)
    (hσ : a σ = 0) :
    ∀ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ), a γ = 0 := by
  classical
  set C : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.topologicalClosure (Subgroup.zpowers σ) with hCdef
  have hσC : σ ∈ C := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)
  obtain ⟨U, hUo, hU⟩ := hlc
  -- `a 1 = 0`
  have ha1 : a 1 = 0 := by
    have h := hcoc 1 (Subgroup.one_mem C) 1 (Subgroup.one_mem C)
    simp only [mul_one, map_one, one_smul] at h
    have h' : a 1 + 0 = a 1 + a 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  let T : Subgroup ↥C :=
    { carrier := {γ | a (γ : Ω ≃ₐ[k] Ω) = 0}
      one_mem' := ha1
      mul_mem' := by
        intro x y hx hy
        change a ((x : Ω ≃ₐ[k] Ω) * (y : Ω ≃ₐ[k] Ω)) = 0
        rw [hcoc _ x.2 _ y.2, hx, hy, smul_zero, add_zero]
      inv_mem' := by
        intro x hx
        change a ((x : Ω ≃ₐ[k] Ω)⁻¹) = 0
        have h11 : a (1 : Ω ≃ₐ[k] Ω)
            = a (x : Ω ≃ₐ[k] Ω) + SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) • a ((x : Ω ≃ₐ[k] Ω)⁻¹) := by
          have h := hcoc _ x.2 _ (C.inv_mem x.2)
          rwa [mul_inv_cancel] at h
        rw [ha1, hx, zero_add] at h11
        calc a ((x : Ω ≃ₐ[k] Ω)⁻¹)
            = SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)⁻¹
                • (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) • a ((x : Ω ≃ₐ[k] Ω)⁻¹)) := by
              rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
          _ = 0 := by rw [h11.symm, smul_zero] }
  have hσT : (⟨σ, hσC⟩ : ↥C) ∈ T := hσ
  have hTopen : IsOpen (T : Set ↥C) := by
    have h1 : (Subgroup.comap (Subgroup.subtype C) U : Subgroup ↥C) ≤ T := by
      intro x hx
      change a (x : Ω ≃ₐ[k] Ω) = 0
      have hxU : (x : Ω ≃ₐ[k] Ω) ∈ U := hx
      have h := hU 1 (Subgroup.one_mem C) (x : Ω ≃ₐ[k] Ω) hxU x.2
      rw [one_mul, ha1] at h
      exact h
    have hUopen' : IsOpen ((Subgroup.comap (Subgroup.subtype C) U : Subgroup ↥C) : Set ↥C) := by
      rw [Subgroup.coe_comap]
      exact hUo.preimage continuous_subtype_val
    exact Subgroup.isOpen_mono h1 hUopen'
  have hTclosed : IsClosed (T : Set ↥C) := Subgroup.isClosed_of_isOpen T hTopen
  have hle : Subgroup.zpowers (⟨σ, hσC⟩ : ↥C) ≤ T := Subgroup.zpowers_le.mpr hσT
  have hcl : Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C)) ≤ T :=
    Subgroup.topologicalClosure_minimal _ hle hTclosed
  have hmap : (Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C))).map
      (Subgroup.subtype C) = C := by
    exact Work.SSGRoute.map_topologicalClosure_zpowers_subtype C
      (Subgroup.isClosed_topologicalClosure _) σ hσC
  intro γ hγ
  have hx : γ ∈ (Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C))).map
      (Subgroup.subtype C) := by
    rw [hmap]
    exact hγ
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyeq : y = (⟨γ, hγ⟩ : ↥C) := Subtype.ext hyx
  exact hcl (hyeq ▸ hy)


/-- **`ip` and `proj` are continuous.**  The multiplication map `↥I × ↥C → ↥D` is a continuous
bijection between compact Hausdorff spaces, hence a homeomorphism; `ip` and `proj` are its two
components. -/
lemma continuous_ip_proj
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hI : I ≤ SSGRoute.decomp k A)
    (hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω)))
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    (hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ))
    (hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥) :
    Continuous (fun d : ↥(SSGRoute.decomp k A) =>
        ((HS.proj A I σ hI hnorm (HS.CC_le_DD A σ hσ) hsup d :
          ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω)) ∧
    Continuous (fun d : ↥(SSGRoute.decomp k A) =>
        ((HS.ip A I σ hI hnorm (HS.CC_le_DD A σ hσ) hsup d : ↥I) : Ω ≃ₐ[k] Ω)) := by
  classical
  haveI : T2Space (Ω ≃ₐ[k] Ω) := krullTopology_t2 (K := k) (L := Ω)
  have hCD : Subgroup.topologicalClosure (Subgroup.zpowers σ) ≤ SSGRoute.decomp k A :=
    HS.CC_le_DD A σ hσ
  haveI : CompactSpace ↥I := isCompact_iff_compactSpace.mp hIclosed.isCompact
  haveI : CompactSpace ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_topologicalClosure _).isCompact
  let Ψ : ↥I × ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) → ↥(SSGRoute.decomp k A) :=
    fun x => ⟨(x.1 : Ω ≃ₐ[k] Ω) * (x.2 : Ω ≃ₐ[k] Ω),
      (SSGRoute.decomp k A).mul_mem (hI x.1.2) (hCD x.2.2)⟩
  have hΨcont : Continuous Ψ := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  have hΨbij : Function.Bijective Ψ := by
    constructor
    · intro x y hxy
      have h : (x.1 : Ω ≃ₐ[k] Ω) * (x.2 : Ω ≃ₐ[k] Ω)
          = (y.1 : Ω ≃ₐ[k] Ω) * (y.2 : Ω ≃ₐ[k] Ω) := by
        simpa [Ψ] using congrArg (fun z : ↥(SSGRoute.decomp k A) => (z : Ω ≃ₐ[k] Ω)) hxy
      obtain ⟨h1, h2⟩ := HS.factor_unique A I σ hinf x.1.2 y.1.2 x.2.2 y.2.2 h
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro d
      obtain ⟨i, hi, γ, hγ, hprod⟩ := HS.exists_factor A I σ hI hnorm hCD hsup d.2
      exact ⟨(⟨i, hi⟩, ⟨γ, hγ⟩), Subtype.ext hprod⟩
  let eH : ↥I × ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) ≃ₜ
      ↥(SSGRoute.decomp k A) :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Ψ hΨbij) hΨcont
  have hkey : ∀ d : ↥(SSGRoute.decomp k A),
      ((eH.symm d).1 : Ω ≃ₐ[k] Ω) * ((eH.symm d).2 : Ω ≃ₐ[k] Ω)
        = (d : Ω ≃ₐ[k] Ω) := by
    intro d
    have h := congrArg (fun z : ↥(SSGRoute.decomp k A) => (z : Ω ≃ₐ[k] Ω))
      (eH.apply_symm_apply d)
    rw [← h]
    rfl
  have hproj_eq : ∀ d : ↥(SSGRoute.decomp k A),
      HS.proj A I σ hI hnorm hCD hsup d = (eH.symm d).2 := by
    intro d
    have h1 := HS.ip_mul_proj A I σ hI hnorm hCD hsup d
    obtain ⟨-, hγ⟩ := HS.factor_unique A I σ hinf
      (HS.ip A I σ hI hnorm hCD hsup d).2 (eH.symm d).1.2
      (HS.proj A I σ hI hnorm hCD hsup d).2 (eH.symm d).2.2
      (by rw [h1, hkey d])
    exact Subtype.ext hγ
  have hip_eq : ∀ d : ↥(SSGRoute.decomp k A),
      HS.ip A I σ hI hnorm hCD hsup d = (eH.symm d).1 := by
    intro d
    have h1 := HS.ip_mul_proj A I σ hI hnorm hCD hsup d
    obtain ⟨hi, -⟩ := HS.factor_unique A I σ hinf
      (HS.ip A I σ hI hnorm hCD hsup d).2 (eH.symm d).1.2
      (HS.proj A I σ hI hnorm hCD hsup d).2 (eH.symm d).2.2
      (by rw [h1, hkey d])
    exact Subtype.ext hi
  refine ⟨?_, ?_⟩
  · have hfun : (fun d : ↥(SSGRoute.decomp k A) =>
        ((HS.proj A I σ hI hnorm hCD hsup d :
          ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω))
        = fun d => (((eH.symm d).2 :
            ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ))) : Ω ≃ₐ[k] Ω) :=
      funext (fun d => by rw [hproj_eq d])
    rw [hfun]
    exact (continuous_subtype_val.comp continuous_snd).comp eH.symm.continuous
  · have hfun : (fun d : ↥(SSGRoute.decomp k A) =>
        ((HS.ip A I σ hI hnorm hCD hsup d : ↥I) : Ω ≃ₐ[k] Ω))
        = fun d => (((eH.symm d).1 : ↥I) : Ω ≃ₐ[k] Ω) :=
      funext (fun d => by rw [hip_eq d])
    rw [hfun]
    exact (continuous_subtype_val.comp continuous_fst).comp eH.symm.continuous

end

end Work.SSGRoute.PT
