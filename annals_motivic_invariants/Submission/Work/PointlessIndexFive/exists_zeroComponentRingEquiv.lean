import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- A multivariate polynomial that is homogeneous of degree `0` is a constant: it is the
image under `C` of its constant coefficient. -/
private lemma eq_C_constantCoeff_of_isHomogeneous_zero {𝕜 : Type} [Field 𝕜] {σ : Type}
    (p : MvPolynomial σ 𝕜) (hp : p.IsHomogeneous 0) :
    MvPolynomial.C (MvPolynomial.constantCoeff p) = p := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, MvPolynomial.homogeneousSubmodule_zero,
    Submodule.mem_one] at hp
  obtain ⟨r, hr⟩ := hp
  rw [MvPolynomial.algebraMap_eq] at hr
  rw [← hr, MvPolynomial.constantCoeff_C]

/-- The degree-`0` part of the standard grading on `MvPolynomial σ 𝕜` is the field of constants:
there is a ring isomorphism `↥(homogeneousSubmodule σ 𝕜 0) ≃+* 𝕜` sending a degree-`0` polynomial
`p` to `C (e p) = p`, i.e. reading off its constant coefficient.  Used to put the projective model
`Proj (homogeneousSubmodule (Fin (n+1)) 𝕜)` over `Spec 𝕜`. -/
theorem exists_zeroComponentRingEquiv (𝕜 : Type) [Field 𝕜] (σ : Type) :
    ∃ e : ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0) ≃+* 𝕜,
      ∀ p : ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0),
        MvPolynomial.C (e p) = (p : MvPolynomial σ 𝕜) := by
  let f : ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0) →+* 𝕜 :=
    { toFun := fun p => MvPolynomial.constantCoeff (p : MvPolynomial σ 𝕜)
      map_one' := by simp
      map_mul' := by intro x y; simp
      map_zero' := by simp
      map_add' := by intro x y; simp }
  let g : 𝕜 →+* ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0) :=
    { toFun := fun r => ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C σ r⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hfg : ∀ r : 𝕜, f (g r) = r := fun r => MvPolynomial.constantCoeff_C σ r
  have hgf : ∀ p : ↥(MvPolynomial.homogeneousSubmodule σ 𝕜 0), g (f p) = p := by
    intro p
    apply Subtype.ext
    exact eq_C_constantCoeff_of_isHomogeneous_zero (p : MvPolynomial σ 𝕜) p.2
  refine ⟨RingEquiv.ofBijective f ?_, ?_⟩
  · exact ⟨fun a b hab => by rw [← hgf a, hab, hgf b], fun r => ⟨g r, hfg r⟩⟩
  · intro p
    exact eq_C_constantCoeff_of_isHomogeneous_zero (p : MvPolynomial σ 𝕜) p.2

end Work.PointlessIndexFive
