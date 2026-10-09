import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSRow

/-- **`β - b` is a locally constant `1`-cocycle on `I`.**

If `c` is the coboundary on `D` of a locally constant `1`-cochain `b`
(`c g h = res g • b h - b (g * h) + b g` for `g, h ∈ D`) and `β` is a locally constant primitive of
`c` on `I ≤ D` (`res n • β m - β (n * m) + β n = c n m` for `n, m ∈ I`), then the difference
`β - b` is again a locally constant `1`-cocycle on `I`:

  `res n • (β - b) m - (β - b) (n * m) + (β - b) n = 0`  for `n, m ∈ I`. -/
lemma sub_primitive_mem_lcCocycles
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (D I : Subgroup (Ω ≃ₐ[k] Ω)) (hI : I ≤ D)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (b β : (Ω ≃ₐ[k] Ω) → M)
    (hbcob : ∀ g ∈ D, ∀ h ∈ D,
      c g h = SSGRoute.res k K g • b h - b (g * h) + b g)
    (hblc : SSGRoute.IsLocConstOn D b)
    (hβlc : SSGRoute.IsLocConstOn I β)
    (hβ : ∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m) :
    (fun x => β x - b x) ∈ Work.SSGRoute.lcCocycles p k Ω K M I := by
  rw [Work.SSGRoute.mem_lcCocycles]
  refine ⟨?_, ?_⟩
  · -- the cocycle identity: `β` and `b` have the same defect on `I` (both equal `c`)
    intro n hn m hm
    have hnD : n ∈ D := hI hn
    have hmD : m ∈ D := hI hm
    have h1 : SSGRoute.res k K n • β m - β (n * m) + β n
        = SSGRoute.res k K n • b m - b (n * m) + b n := by
      rw [hβ n hn m hm, hbcob n hnD m hmD]
    rw [smul_sub]
    rw [← sub_eq_zero]
    have hA : SSGRoute.res k K n • β m - β (n * m) + β n
          - (SSGRoute.res k K n • b m - b (n * m) + b n) = 0 := by rw [h1]; abel
    have hrel : β (n * m) - b (n * m)
          - (β n - b n + (SSGRoute.res k K n • β m - SSGRoute.res k K n • b m))
        = -((SSGRoute.res k K n • β m - β (n * m) + β n)
          - (SSGRoute.res k K n • b m - b (n * m) + b n)) := by abel
    rw [hrel, hA, neg_zero]
  · -- local constancy, as for any difference of locally constant cochains
    obtain ⟨Ub, hUbo, hUb⟩ := hblc
    obtain ⟨Uβ, hUβo, hUβ⟩ := hβlc
    refine ⟨Uβ ⊓ Ub, ?_, ?_⟩
    · rw [Subgroup.coe_inf]; exact hUβo.inter hUbo
    · intro g hg u hu huI
      obtain ⟨huβ, hub⟩ := Subgroup.mem_inf.mp hu
      simp only [hUβ g hg u huβ huI, hUb g (hI hg) u hub (hI huI)]

end Work.SSGRoute.HSRow
