import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs
import Submission.Work.Hering.GL32.AppIXAssembly
import Submission.Work.Hering.GL32.exists_surjective_W_to

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX of Peterfalvi I: the irreducible `F₂`-representations of `GL(3,2)`

Every finite simple `F₂[GL(3,2)]`-module has dimension `1`, `3` or `8`
(`Work.Hering.AppIXProp`).

The proof: the Frobenius step (`exists_surjective_W_to`) produces a surjective `GL(3,2)`-equivariant
map `ψ : W ↠ M` from the permutation module `W = F₂[Ω]` on the `21` pairs of points of `PG(2,2)`.
Then

* if `ψ ∘ phiStar ≠ 0`, the composite is injective and surjective because `V*` and `M` are simple,
  so `M ≅ V*` and `dim M = 3`;
* if `ψ ∘ phiStar = 0 ≠ ψ ∘ psiStar`, similarly `M ≅ V` and `dim M = 3`;
* otherwise `K₄ = phiStar.range ⊔ psiStar.range ≤ ker ψ`, so `M` is a quotient of
  `W/K₄ ≅ k × V × V* × M₄`, and by the four simplicity statements `M` is isomorphic to one of the
  four factors, of dimension `1`, `3`, `3` or `8`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Hering.GL32

theorem appIX : AppIXProp := by
  intro M _ _ _ ρ hne hsimple
  obtain ⟨ψ, hsurj, hψ⟩ := exists_surjective_W_to ρ hne hsimple
  by_cases h1 : ψ.comp phiStar = 0
  · by_cases h2 : ψ.comp psiStar = 0
    · have hK4 : K4 ≤ LinearMap.ker ψ := by
        rw [K4_eq_sup]
        refine sup_le ?_ ?_
        · rintro f ⟨s, rfl⟩
          rw [LinearMap.mem_ker]
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun h1 s
        · rintro f ⟨v, rfl⟩
          rw [LinearMap.mem_ker]
          simpa [LinearMap.comp_apply] using LinearMap.congr_fun h2 v
      exact finrank_eq_of_K4_le ρ hne hsimple ψ hsurj hψ hK4
    · exact finrank_eq_of_psiStar_ne ρ hsimple ψ hψ h2
  · exact finrank_eq_of_phiStar_ne ρ hsimple ψ hψ h1

end Work.Hering.GL32
