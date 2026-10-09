import Mathlib
import Submission.Work.PTCore.TransgressionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.PTCore

open Classical

/-- The step relation for the `E`-correction: on the decomposition group, `corrE` satisfies the
"derivation" rule along the normal subgroup `I`.  This is exactly the inhomogeneous `2`-cocycle
identity applied to the triple `(projG g, coorG g, n)`, using that `c₀` vanishes on `I × I`. -/
theorem corrE_step {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (S : Work.PTCore.DCtx k Ω) (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c₀ : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hcoc : SSGRoute.IsCocycle2On p k Ω K M (SSGRoute.decomp k S.A) c₀)
    (hzero : ∀ n ∈ S.I, ∀ m ∈ S.I, c₀ n m = 0)
    {g n : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) (hn : n ∈ S.I) :
    Work.PTCore.corrE (M := M) S c₀ (g * n) = Work.PTCore.corrE (M := M) S c₀ g - c₀ g n := by
  have hnD : n ∈ SSGRoute.decomp k S.A := S.hI hn
  have hgnD : g * n ∈ SSGRoute.decomp k S.A := mul_mem hg hnD
  -- the coordinate identities
  have hproj : projG S (g * n) = projG S g := by
    rw [projG_mul S hg hnD, projG_eq_one_of_mem_I S hn, mul_one]
  have hcoor : coorG S (g * n) = coorG S g * n := coorG_mul_of_mem_I S hg hn
  -- the cocycle identity on the triple `(projG g, coorG g, n)`
  have hcocyc := hcoc (projG S g) (projG_mem_D S hg) (coorG S g)
    (S.hI (coorG_mem_I S hg)) n hnD
  have hgc : projG S g * coorG S g = g := by
    rw [coorG_of_mem S hg]; group
  have hz : c₀ (coorG S g) n = 0 := hzero (coorG S g) (coorG_mem_I S hg) n hn
  have hkey : c₀ (projG S g) (coorG S g * n) = c₀ (projG S g) (coorG S g) + c₀ g n := by
    have h := hcocyc
    rw [hz, smul_zero, hgc] at h
    have h' : c₀ (projG S g) (coorG S g * n)
        - (c₀ (projG S g) (coorG S g) + c₀ g n) = 0 := by
      rw [← h]; abel
    exact sub_eq_zero.mp h'
  rw [corrE_of_mem S c₀ hgnD, corrE_of_mem S c₀ hg, hproj, hcoor, hkey]
  abel

end Work.PTCore
