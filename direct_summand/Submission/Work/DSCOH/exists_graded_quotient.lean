import Mathlib
import Submission.Work.DSCOH.ChartFree
import Submission.Work.DSCOH.exists_homogeneous_generators

namespace Work.DSCOH

/-- Auxiliary: transporting an internal direct sum decomposition along a linear equivalence. -/
theorem isInternal_map_of_linearEquiv {R : Type*} [Ring R] {N N' : Type*} [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] {ι : Type*} [DecidableEq ι]
    (ℳ : ι → Submodule R N) [DirectSum.Decomposition ℳ] (φ : N ≃ₗ[R] N') :
    DirectSum.IsInternal fun e => Submodule.map (φ : N →ₗ[R] N') (ℳ e) := by
  have h := DirectSum.Decomposition.isInternal ℳ
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  obtain ⟨hind, htop⟩ := h
  refine ⟨LinearMap.iSupIndep_map (φ : N →ₗ[R] N') φ.injective hind, ?_⟩
  rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearMap.range_eq_top]
  exact φ.surjective

theorem exists_graded_quotient {A : Type*} [CommRing A] [IsNoetherianRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul (homSub A n) ℳ]
    [Module.Finite (Poly A n) M] :
    ∃ (r : ℕ) (d : Fin r → ℕ) (π : (Fin r → Poly A n) →ₗ[Poly A n] M),
      Function.Surjective π ∧
        (∀ e, Submodule.map (π.restrictScalars A) (freeGraded (A := A) (n := n) d e) ≤ ℳ e) ∧
        ∃ (𝒬 : ℕ → Submodule A ((Fin r → Poly A n) ⧸ LinearMap.ker π)),
          SetLike.GradedSMul (homSub A n) 𝒬 ∧
            DirectSum.IsInternal 𝒬 ∧
            Module.Finite (Poly A n) ((Fin r → Poly A n) ⧸ LinearMap.ker π) ∧
            ∃ (φ : M ≃ₗ[Poly A n] ((Fin r → Poly A n) ⧸ LinearMap.ker π)),
              ∀ e, Submodule.map ((φ : M →ₗ[Poly A n] ((Fin r → Poly A n) ⧸ LinearMap.ker π)).restrictScalars A)
                (ℳ e) = 𝒬 e := by
  classical
  -- a finite family of homogeneous generators of `M` over `A[X₀,…,X_{n-1}]`
  obtain ⟨k, g, d, hg, hgen⟩ := exists_homogeneous_generators (A := A) (n := n) (M := M) ℳ
  -- the associated graded cover `π : ∏_{j : Fin k} S(-d j) → M`
  refine ⟨k, d, freeCover (A := A) (n := n) g, freeCover_surjective (A := A) (n := n) hgen,
    fun e => freeCover_map_freeGraded_le (A := A) (n := n) ℳ hg e, ?_⟩
  set π : (Fin k → Poly A n) →ₗ[Poly A n] M := freeCover (A := A) (n := n) g with hπdef
  have hπ : Function.Surjective π := freeCover_surjective (A := A) (n := n) hgen
  -- the first isomorphism theorem identifies `M` with the quotient by the kernel of the cover
  let φ : M ≃ₗ[Poly A n] ((Fin k → Poly A n) ⧸ LinearMap.ker π) :=
    (LinearMap.quotKerEquivOfSurjective π hπ).symm
  refine ⟨fun e => Submodule.map
      ((φ : M →ₗ[Poly A n] ((Fin k → Poly A n) ⧸ LinearMap.ker π)).restrictScalars A) (ℳ e),
    ?_, ?_, ?_, φ, ?_⟩
  · -- the transported grading is a graded `S`-module structure
    refine ⟨fun i j a q ha hq => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hq
    refine Submodule.mem_map.mpr ⟨a • m, SetLike.GradedSMul.smul_mem ha hm, ?_⟩
    simp only [LinearMap.restrictScalars_apply]
    exact LinearMap.map_smul
      (φ : M →ₗ[Poly A n] ((Fin k → Poly A n) ⧸ LinearMap.ker π)) a m
  · -- the transported grading is an internal direct sum
    exact isInternal_map_of_linearEquiv ℳ (φ.restrictScalars A)
  · -- the quotient is finite over `S`
    infer_instance
  · -- `φ` intertwines the two gradings, by construction
    intro e
    rfl

end Work.DSCOH
