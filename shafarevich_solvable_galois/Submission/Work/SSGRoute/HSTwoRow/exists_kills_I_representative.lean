import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.HSRestrict
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.HSTwoRow

/-- **A representative of `x` killed on `I`.**  If the restriction `res1 x` of a class
`x ∈ H¹_loc(D,M)` (`D = decomp k A`) to a subgroup `I ≤ D` vanishes, then `x` admits a locally
constant `1`-cocycle representative on `D` that vanishes identically on `I`.

Indeed, pick any representative `f₀` of `x`; then `f₀|_I` is a coboundary on `I`, say
`f₀ n = res n • m - m` for `n ∈ I`, and `f = f₀ - (res · m - m)` has the same class as `f₀`
(the correction is a coboundary on `D`) and vanishes on `I`. -/
theorem exists_kills_I_representative
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω))
    (hI : I ≤ SSGRoute.decomp k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (x : Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A))
    (hx : res1 p k Ω K M I A hI x = 0) :
    ∃ f : (Ω ≃ₐ[k] Ω) → M,
      f ∈ Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A) ∧
      Work.SSGRoute.toClass p k Ω K M (SSGRoute.decomp k A) f = x ∧
      ∀ n ∈ I, f n = 0 := by
  -- choose a locally constant cocycle representative of `x` on `D = decomp k A`
  obtain ⟨f₀, hf₀, hf₀class⟩ := toClass_surjective p k Ω K M (SSGRoute.decomp k A) x
  -- its restriction to `I` is again a locally constant cocycle
  have hrestrict : f₀ ∈ lcCocycles p k Ω K M I :=
    (restrictCocycle1 p k Ω K M I A hI ⟨f₀, hf₀⟩).2
  -- and has class `res1 x = 0`
  have hres : toClass p k Ω K M I f₀ = 0 := by
    rw [← res1_toClass p k Ω K M I A hI f₀ hf₀, hf₀class]
    exact hx
  -- hence `f₀|_I` is a coboundary on `I`
  obtain ⟨m, hm⟩ := (toClass_eq_zero_iff p k Ω K M I hrestrict).mp hres
  -- the global coboundary `b g = res g • m - m`
  let b : (Ω ≃ₐ[k] Ω) → M := fun g => SSGRoute.res k K g • m - m
  have hb_cob : b ∈ coboundaries p k Ω K M (SSGRoute.decomp k A) :=
    ⟨m, fun g _ => rfl⟩
  have hb_lc : b ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
    coboundaries_le_lcCocycles p k Ω K M (SSGRoute.decomp k A) hb_cob
  have hb_class : toClass p k Ω K M (SSGRoute.decomp k A) b = 0 :=
    (toClass_eq_zero_iff p k Ω K M (SSGRoute.decomp k A) hb_lc).mpr hb_cob
  have hsub_lc : f₀ - b ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) :=
    Submodule.sub_mem _ hf₀ hb_lc
  refine ⟨f₀ - b, hsub_lc, ?_, ?_⟩
  · -- the class is unchanged: subtracting a coboundary does not change the class
    have h1 : toClass p k Ω K M (SSGRoute.decomp k A) (f₀ - b)
        = toClass p k Ω K M (SSGRoute.decomp k A) f₀
          - toClass p k Ω K M (SSGRoute.decomp k A) b := by
      rw [eq_sub_iff_add_eq, ← toClass_add p k Ω K M (SSGRoute.decomp k A) hsub_lc hb_lc,
        sub_add_cancel]
    rw [h1, hb_class, sub_zero, hf₀class]
  · -- and it vanishes on `I`
    intro n hn
    have : (f₀ - b) n = f₀ n - (SSGRoute.res k K n • m - m) := rfl
    rw [this, hm n hn, sub_self]

end Work.SSGRoute.HSTwoRow
