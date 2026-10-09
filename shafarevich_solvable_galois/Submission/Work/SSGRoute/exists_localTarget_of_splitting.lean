import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.twistLayer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

set_option maxHeartbeats 1000000

/-- The copy `flowEKer p G n i j` of the graded piece `E(n,τ)` inside the level-`τ+1` group is the
range of `gradeInl`.  (A local copy of the corresponding statement of
`properStageAssemblyData`, so that this module does not depend on it.) -/
theorem localTargetOfSplitting_flowEKer_eq_range_gradeInl (p : ℕ) (G : Type*) [Group G]
    (n i j : ℕ) :
    flowEKer p G n i j = (gradeInl p G n i j).range := by
  ext x
  constructor
  · intro hx
    change x ∈ (flowGroupProj p G n i j).ker at hx
    rw [MonoidHom.mem_ker] at hx
    have hleft : flowQuotientProj p G n i j x.left = 1 := by
      have h := congrArg SemidirectProduct.left hx
      simpa [flowGroupProj] using h
    have hright : x.right = 1 := by
      have h := congrArg SemidirectProduct.right hx
      simpa [flowGroupProj] using h
    have hmem : x.left ∈ (stageProjQuotient p G n i j).ker := hleft
    rw [stageProjQuotient_ker] at hmem
    obtain ⟨v, hv⟩ := hmem
    refine ⟨v, ?_⟩
    show SemidirectProduct.mk (gradeIncl p G n i j v) 1 = x
    rw [show x = SemidirectProduct.mk x.left x.right from rfl, hv, hright]
  · rintro ⟨v, rfl⟩
    exact flowGroupProj_gradeInl p G n i j v

/-- Membership form of `localTargetOfSplitting_flowEKer_eq_range_gradeInl`. -/
theorem localTargetOfSplitting_mem_flowEKer_iff_exists_gradeInl (p : ℕ) (G : Type*) [Group G]
    (n i j : ℕ) (x : flowGroup p G n (tauSucc i j).1 (tauSucc i j).2) :
    x ∈ flowEKer p G n i j ↔ ∃ v, gradeInl p G n i j v = x := by
  rw [show flowEKer p G n i j = (gradeInl p G n i j).range from
    localTargetOfSplitting_flowEKer_eq_range_gradeInl p G n i j]
  exact Iff.rfl

theorem exists_localTarget_of_splitting (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m i j : ℕ}
    (φm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ,
      Work.SSGRoute.flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ) = φm σ)
    (hquot : ∀ σ : SSGRoute.GalQ, Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1
      (Work.CohomologicalShrinking.tauSucc i j).2 (ψm σ) = Work.SSGRoute.restrict K σ)
    (hopenψ : IsOpen (ψm.ker : Set SSGRoute.GalQ))
    (A : ValuationSubring SSGRoute.QBar)
    (l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hopenl : ∃ U : Subgroup SSGRoute.GalQ, IsOpen (U : Set SSGRoute.GalQ) ∧
      ∀ u (hu : u ∈ U) (hu' : u ∈ SSGRoute.decomp ℚ A),
        l ⟨u, hu'⟩ = 1)
    (hlift : ∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φm ↑σ)) :
    ∃ α : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j,
      SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) α ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) α ∧
      ∀ σ : ↥(SSGRoute.decomp ℚ A),
        Work.SSGRoute.gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α ↑σ)) =
          l σ * (ψm ↑σ)⁻¹ := by
  classical
  -- The ratio of two lifts of `φm` lies in the copy of the graded piece.
  have hval : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      ∃ v : E p (K ≃ₐ[ℚ] K) m i j,
        gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul v) = l σ * (ψm ↑σ)⁻¹ := by
    intro σ
    have hlproj : flowGroupProj p (K ≃ₐ[ℚ] K) m i j (l σ) = φm ↑σ :=
      flowGroupProj_eq_of_liftsFlowAt (hlift σ)
    have hmem : l σ * (ψm ↑σ)⁻¹ ∈ flowEKer p (K ≃ₐ[ℚ] K) m i j := by
      change l σ * (ψm ↑σ)⁻¹ ∈ (flowGroupProj p (K ≃ₐ[ℚ] K) m i j).ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlproj, hproj, mul_inv_cancel]
    obtain ⟨v, hv⟩ :=
      (localTargetOfSplitting_mem_flowEKer_iff_exists_gradeInl p (K ≃ₐ[ℚ] K) m i j _).mp hmem
    exact ⟨Additive.ofMul v, hv⟩
  let αD : ↥(SSGRoute.decomp ℚ A) → E p (K ≃ₐ[ℚ] K) m i j := fun σ => (hval σ).choose
  have hαD : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (αD σ)) = l σ * (ψm ↑σ)⁻¹ :=
    fun σ => (hval σ).choose_spec
  refine ⟨fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0, ?_, ?_, ?_⟩
  · -- the crossed-homomorphism identity
    intro g hg h hh
    have hmul : (⟨g * h, Subgroup.mul_mem _ hg hh⟩ : ↥(SSGRoute.decomp ℚ A))
        = ⟨g, hg⟩ * ⟨h, hh⟩ := by ext; rfl
    have hl_mul : l ⟨g * h, Subgroup.mul_mem _ hg hh⟩ = l ⟨g, hg⟩ * l ⟨h, hh⟩ := by
      rw [hmul, map_mul]
    have hgh1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) (g * h)
        = αD ⟨g * h, Subgroup.mul_mem _ hg hh⟩ := dif_pos (Subgroup.mul_mem _ hg hh)
    have hg1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) g
        = αD ⟨g, hg⟩ := dif_pos hg
    have hh1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) h
        = αD ⟨h, hh⟩ := dif_pos hh
    rw [hgh1, hg1, hh1]
    apply Additive.toMul.injective
    rw [toMul_add]
    have hsm : Additive.toMul ((Work.SSGRoute.restrict K g) • αD ⟨h, hh⟩)
        = (Work.SSGRoute.restrict K g) • Additive.toMul (αD ⟨h, hh⟩) := rfl
    rw [hsm]
    apply gradeInl_injective p (K ≃ₐ[ℚ] K) m i j
    rw [map_mul, hαD ⟨g * h, Subgroup.mul_mem _ hg hh⟩, hαD ⟨g, hg⟩,
      ← gradeInl_conj p K m i j ψm g (hquot g) (Additive.toMul (αD ⟨h, hh⟩)),
      hαD ⟨h, hh⟩, hl_mul]
    simp only [map_mul]
    group
  · -- local constancy
    obtain ⟨U, hUopen, hUtriv⟩ := hopenl
    refine ⟨U ⊓ ψm.ker, ?_, ?_⟩
    · rw [Subgroup.coe_inf]; exact hUopen.inter hopenψ
    · intro g hg u hu huH
      have huU : u ∈ U := hu.1
      have huker : u ∈ ψm.ker := hu.2
      have hlu : l ⟨u, huH⟩ = 1 := hUtriv u huU huH
      have huk : ψm (↑(⟨u, huH⟩ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) = 1 :=
        MonoidHom.mem_ker.mp huker
      have hmu : (⟨g * u, Subgroup.mul_mem _ hg huH⟩ : ↥(SSGRoute.decomp ℚ A))
          = ⟨g, hg⟩ * ⟨u, huH⟩ := by ext; rfl
      have hl_mul : l ⟨g * u, Subgroup.mul_mem _ hg huH⟩ = l ⟨g, hg⟩ := by
        rw [hmu, map_mul, hlu, mul_one]
      have hpsi_mul : ψm (↑(⟨g * u, Subgroup.mul_mem _ hg huH⟩ :
            ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
          = ψm (↑(⟨g, hg⟩ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) := by
        rw [show (↑(⟨g * u, Subgroup.mul_mem _ hg huH⟩ :
              ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
            = (↑(⟨g, hg⟩ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)
              * (↑(⟨u, huH⟩ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) from rfl,
          map_mul, huk, mul_one]
      have h1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) (g * u)
          = αD ⟨g * u, Subgroup.mul_mem _ hg huH⟩ := dif_pos (Subgroup.mul_mem _ hg huH)
      have h2 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) g
          = αD ⟨g, hg⟩ := dif_pos hg
      rw [h1, h2]
      apply Additive.toMul.injective
      apply gradeInl_injective p (K ≃ₐ[ℚ] K) m i j
      rw [hαD ⟨g * u, Subgroup.mul_mem _ hg huH⟩, hαD ⟨g, hg⟩, hl_mul, hpsi_mul]
  · -- the prescribed values on the decomposition group
    intro σ
    have h1 : (fun τ : SSGRoute.GalQ =>
        if h : τ ∈ SSGRoute.decomp ℚ A then αD ⟨τ, h⟩ else 0) (↑σ)
        = αD ⟨(↑σ : SSGRoute.GalQ), σ.2⟩ := dif_pos σ.2
    rw [h1]
    exact hαD σ

end Work.SSGRoute
