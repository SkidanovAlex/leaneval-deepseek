import Mathlib.Analysis.InnerProductSpace.LinearPMap

noncomputable section

namespace Commons.Analysis.InnerProductSpace.LinearPMap

open RCLike

set_option linter.unusedVariables false in
/-- If `T` is densely defined and `T†† = T`, then `T†` is densely defined. -/
lemma dense_adjoint_domain_of_adjoint_adjoint {K E F : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]
    (T : LinearPMap (RingHom.id K) E F) (hT : Dense (T.domain : Set E))
    (hvn : LinearPMap.adjoint (LinearPMap.adjoint T) = T) :
    Dense ((LinearPMap.adjoint T).domain : Set F) := by
  by_contra hh
  have hTzero : ∀ x : T.domain, T x = 0 := by
    intro x
    have hdom : (x : E) ∈ (LinearPMap.adjoint (LinearPMap.adjoint T)).domain := by
      rw [(LinearPMap.ext_iff.mp hvn).1]
      exact x.2
    have hzero : (LinearPMap.adjoint (LinearPMap.adjoint T)) ⟨(x : E), hdom⟩ = 0 :=
      LinearPMap.adjoint_apply_of_not_dense (T := LinearPMap.adjoint T) hh ⟨(x : E), hdom⟩
    have hval := (LinearPMap.ext_iff.mp hvn).2 (x := (x : E)) (hf := hdom) (hg := x.2)
    rw [← hval]
    exact hzero
  have htop : (LinearPMap.adjoint T).domain = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    exact LinearPMap.mem_adjoint_domain_of_exists (T := T) y ⟨0, by intro x; simp [hTzero x]⟩
  rw [htop] at hh
  exact hh dense_univ

theorem exists_orthogonal_decomposition {K F G : Type*} [RCLike K] [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F] [NormedAddCommGroup G] [InnerProductSpace K G] [CompleteSpace G] (S : LinearPMap (RingHom.id K) F G) (hS : Dense (S.domain : Set F)) (hvnS : LinearPMap.adjoint (LinearPMap.adjoint S) = S) (x : F) : ∃ (x' : F) (h1 : x' ∈ S.domain), S ⟨x', h1⟩ = 0 ∧ (∀ (y : F) (hy : y ∈ S.domain), S ⟨y, hy⟩ = 0 → inner K y (x - x') = 0) := by
  have hT : Dense ((LinearPMap.adjoint S).domain : Set G) :=
    dense_adjoint_domain_of_adjoint_adjoint S hS hvnS
  have hmem : ∀ z : F, z ∈ (LinearMap.range (LinearPMap.adjoint S).toFun)ᗮ ↔
      ∃ h : z ∈ S.domain, S ⟨z, h⟩ = 0 := by
    intro z
    constructor
    · intro hz
      have hz' : ∀ w : (LinearPMap.adjoint S).domain,
          inner K z ((LinearPMap.adjoint S) w) = 0 := by
        intro w
        have h0 : inner K ((LinearPMap.adjoint S) w) z = 0 :=
          (Submodule.mem_orthogonal _ z).1 hz _ (LinearMap.mem_range_self _ w)
        rwa [inner_eq_zero_symm] at h0
      have hdom : z ∈ (LinearPMap.adjoint (LinearPMap.adjoint S)).domain :=
        LinearPMap.mem_adjoint_domain_of_exists (T := LinearPMap.adjoint S) z
          ⟨0, fun w => by rw [inner_zero_left]; exact (hz' w).symm⟩
      have hzS : z ∈ S.domain := by
        rw [← (LinearPMap.ext_iff.mp hvnS).1]
        exact hdom
      have hval0 : (LinearPMap.adjoint (LinearPMap.adjoint S)) ⟨z, hdom⟩ = 0 :=
        LinearPMap.adjoint_apply_eq (T := LinearPMap.adjoint S) hT ⟨z, hdom⟩ (x₀ := 0)
          (fun w => by rw [inner_zero_left]; exact (hz' w).symm)
      refine ⟨hzS, ?_⟩
      have hval := (LinearPMap.ext_iff.mp hvnS).2 (x := z) (hf := hdom) (hg := hzS)
      rw [← hval]
      exact hval0
    · rintro ⟨hzS, hz0⟩
      have hzdom : z ∈ (LinearPMap.adjoint (LinearPMap.adjoint S)).domain :=
        (LinearPMap.ext_iff.mp hvnS).1.symm ▸ hzS
      rw [Submodule.mem_orthogonal]
      rintro u ⟨w, rfl⟩
      have h1 := (LinearPMap.adjoint_isFormalAdjoint (T := LinearPMap.adjoint S) hT).symm
        w ⟨z, hzdom⟩
      have h2 : (LinearPMap.adjoint (LinearPMap.adjoint S)) ⟨z, hzdom⟩ = 0 := by
        have hval := (LinearPMap.ext_iff.mp hvnS).2 (x := z) (hf := hzdom) (hg := hzS)
        rw [hval]
        exact hz0
      rw [h2, inner_zero_right] at h1
      exact h1
  obtain ⟨w, hwK, hwperp⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal
      (K := (LinearMap.range (LinearPMap.adjoint S).toFun)ᗮ) x
  obtain ⟨h1, hval⟩ := (hmem w).1 hwK
  refine ⟨w, h1, hval, ?_⟩
  intro y hy hy0
  have hyK : y ∈ (LinearMap.range (LinearPMap.adjoint S).toFun)ᗮ := (hmem y).2 ⟨hy, hy0⟩
  exact Submodule.inner_right_of_mem_orthogonal hyK hwperp

end Commons.Analysis.InnerProductSpace.LinearPMap