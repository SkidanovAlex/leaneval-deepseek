import Mathlib
import Submission.Work.Pi6.MSS.e1CohDualDefs
import Submission.Work.Pi6.MSS.evSaux
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS.e1CohDual

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

/-- The inclusion of the chains of the `k`-th Serre subcomplex into the chains of `E` is injective;
equivalently, its underlying linear functional on `n`-chains is an injective linear map. -/
lemma e1cIncl_injective (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (k n : ℕ) :
    Function.Injective (((Work.Pi6.MSS.e1cIncl 𝕜 p k).f n).hom) := by
  rw [show (Work.Pi6.MSS.e1cIncl 𝕜 p k :
        Work.Pi6.MSS.e1cCc 𝕜 p k ⟶ Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)) =
      Work.SSSR.sChainMap 𝕜 (Work.Pi6.MSS.e1cSub p k).ι from rfl]
  rw [Work.SSSR.sChainMap_f 𝕜 ((Work.Pi6.MSS.e1cSub p k).ι) n]
  exact (ModuleCat.mono_iff_injective _).mp
    (Work.SSSR.mono_sigma_map'_of_injective 𝕜
      (fun x : ((Work.Pi6.MSS.e1cSub p k) : SSet) _⦋n⦌ =>
        ((Work.Pi6.MSS.e1cSub p k).ι.app (op ⦋n⦌) x : (Work.SSS.sSing E) _⦋n⦌))
      (Work.SSSR.injective_app_of_mono (Work.Pi6.MSS.e1cSub p k).ι inferInstance n))

/-- **The lift of a linear functional on the `s`-th graded piece to a cochain in `F^s`.**

Given a linear functional `ψ` on the `n`-chains of the graded piece
`grF (serF 𝕜 (Sing p)) s = C(A_{s+1})/C(A_s)`, there is a cochain `y` of the singular cochains of
`E` which lies in the `s`-th Serre filtration step `F^s` and which on the chains of `A_{s+1}`
agrees with the functional induced by `ψ`. -/
theorem secLift (𝕜 : Type) [Field 𝕜] {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s n : ℕ) (ψ : (Work.Pi6.MSS.e1cKg 𝕜 p s).X n →ₗ[𝕜] 𝕜) :
    ∃ y : (Work.Pi6.MSS.serreCF 𝕜 E B p).C.X n,
      y ∈ (Work.Pi6.MSS.serreCF 𝕜 E B p).F s n ∧
      ∀ v : (Work.Pi6.MSS.e1cCc 𝕜 p (s+1)).X n,
        (Work.Pi6.MSS.e1cCochFun 𝕜 p n y)
            (((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f n).hom v)
          = ψ (((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f n).hom v) := by
  -- A linear section `g` of the inclusion `C(A_{s+1}) ⟶ C(E)` in degree `n`; the inclusion is
  -- injective, so such a left inverse exists over a field.
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
    (show ((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.e1cF p)).obj s).X n →ₗ[𝕜]
        (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n from
      ((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f n).hom)
    (LinearMap.ker_eq_bot.mpr (by
      change Function.Injective (((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f n).hom)
      exact e1cIncl_injective 𝕜 p (s+1) n))
  have hg' : ∀ x : ((Work.SSSR.serF 𝕜 (Work.Pi6.MSS.e1cF p)).obj s).X n,
      g (((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f n).hom x) = x :=
    fun x => LinearMap.congr_fun hg x
  -- The candidate cochain: `ψ` composed with the projection onto the `s`-th graded piece,
  -- transported back to the chains of `E` along the section `g`.
  refine ⟨(ψ.comp ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f n).hom).comp g, ?_, ?_⟩
  · -- Membership in `F^s`.
    rcases s with _ | k
    · -- `F^0 = C`, so there is nothing to prove.
      rw [(Work.Pi6.MSS.serreCF 𝕜 E B p).F_zero n]; exact Submodule.mem_top
    · -- `y` kills the chains of `A_{k+1}`: those are the image of the structure map
      -- `C(A_{k+1}) ⟶ C(A_{k+2})`, which the projection onto the graded piece annihilates.
      apply Work.Pi6.MSS.e1cF_of_kill
      intro w
      rw [← Work.Pi6.MSS.e1cIncl_incF 𝕜 p k n w]
      rw [LinearMap.comp_apply, hg' _]
      rw [LinearMap.comp_apply]
      have hzero : ((Work.Pi6.MSS.e1cKgπ 𝕜 p (k+1)).f n).hom
          (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.e1cF p)) k).f n) w) = 0 := by
        have hcond : (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.e1cF p)) k) ≫
            (Work.Pi6.MSS.e1cKgπ 𝕜 p (k+1)) = 0 := by
          rw [Work.Pi6.MSS.e1cKgπ_succ]
          exact CategoryTheory.Limits.cokernel.condition _
        have h2 : ((Work.Pi6.MSS.e1cKgπ 𝕜 p (k+1)).f n).hom.comp
            (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.e1cF p)) k).f n).hom) = 0 := by
          have hf := HomologicalComplex.comp_f
            (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.e1cF p)) k)
            (Work.Pi6.MSS.e1cKgπ 𝕜 p (k+1)) n
          rw [hcond, HomologicalComplex.zero_f] at hf
          rw [← ModuleCat.hom_comp, ← hf, ModuleCat.hom_zero]
        have h3 := LinearMap.congr_fun h2 w
        change ((Work.Pi6.MSS.e1cKgπ 𝕜 p (k+1)).f n).hom
            (((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.Pi6.MSS.e1cF p)) k).f n) w) = 0 at h3
        exact h3
      rw [hzero, map_zero]
  · -- The agreement on the chains of `A_{s+1}`: `y` is `ψ ∘ Kgπ` retracted along `g`.
    intro v
    show ((ψ.comp ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f n).hom).comp g)
        (((Work.Pi6.MSS.e1cIncl 𝕜 p (s+1)).f n).hom v)
      = ψ (((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f n).hom v)
    rw [LinearMap.comp_apply, hg' v]
    rfl

end Work.Pi6.MSS.e1CohDual
