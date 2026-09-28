import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.ModelIncl.Zs_le_Zsq
import Submission.Work.SSS.ModelIncl.Bsq_le_Bs

namespace Work.SSS.ModelQuot

attribute [-instance] AddCommGroup.toIntModule

/-- **Transfer of finite generation to a subquotient.**  If the quotient `A ⧸ A ∩ B` of the
submodule `A` is a finitely generated `ℤ`-module, and `A' ≤ A`, `B ≤ B'` are submodules, then the
subquotient `A' ⧸ (A' ∩ B')` is finitely generated as well.

The kernel of the composite `A' → A → A ⧸ (A ∩ B)` is exactly `A' ∩ B`, so `A' ⧸ (A' ∩ B)` embeds
into the finitely generated module `A ⧸ (A ∩ B)`; and since `A' ∩ B ≤ A' ∩ B'`, the module
`A' ⧸ (A' ∩ B')` is a quotient of `A' ⧸ (A' ∩ B)`. -/
private theorem finite_quot_comap_of_le {M : Type*} [AddCommGroup M] [Module ℤ M]
    {A A' B B' : Submodule ℤ M} (hA : A' ≤ A) (hB : B ≤ B')
    (hfin : Module.Finite ℤ (↥A ⧸ Submodule.comap A.subtype B)) :
    Module.Finite ℤ (↥A' ⧸ Submodule.comap A'.subtype B') := by
  -- The map `A' → A ⧸ (A ∩ B)` has kernel `A' ∩ B`, so `A' ⧸ (A' ∩ B)` is a submodule of a
  -- finitely generated module, hence finitely generated.
  have hstep1 : Module.Finite ℤ (↥A' ⧸ Submodule.comap A'.subtype B) := by
    let φ : ↥A' →ₗ[ℤ] ↥A ⧸ Submodule.comap A.subtype B :=
      (Submodule.mkQ (Submodule.comap A.subtype B)).comp (Submodule.inclusion hA)
    have hker : φ.ker = Submodule.comap A'.subtype B := by
      show (((Submodule.mkQ (Submodule.comap A.subtype B)).comp
        (Submodule.inclusion hA)) : ↥A' →ₗ[ℤ] ↥A ⧸ Submodule.comap A.subtype B).ker = _
      ext x
      simp only [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.comp_apply,
        Submodule.mkQ_apply, Submodule.inclusion_apply, Submodule.subtype_apply,
        Submodule.Quotient.mk_eq_zero]
    let g := (Submodule.comap A'.subtype B).liftQ φ (le_of_eq hker.symm)
    have hg : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot,
        Submodule.ker_liftQ_eq_bot _ φ (le_of_eq hker.symm) (le_of_eq hker)]
    haveI : IsNoetherian ℤ (↥A ⧸ Submodule.comap A.subtype B) :=
      isNoetherian_of_isNoetherianRing_of_finite ℤ _
    exact Module.Finite.of_injective g hg
  -- `A' ∩ B ≤ A' ∩ B'`, so `A' ⧸ (A' ∩ B')` is a quotient of the finitely generated
  -- `A' ⧸ (A' ∩ B)`.
  haveI := hstep1
  have hle : Submodule.comap A'.subtype B ≤ Submodule.comap A'.subtype B' :=
    Submodule.comap_mono hB
  have hstep2 : Function.Surjective
      ((Submodule.comap A'.subtype B).liftQ (Submodule.mkQ (Submodule.comap A'.subtype B'))
        (by rw [Submodule.ker_mkQ]; exact hle)) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk x, Submodule.liftQ_apply _ _ x⟩
  exact Module.Finite.of_surjective _ hstep2

/-- If the model quotient `Z²_{s,n}/B²_{s,n}` of the `E²` term is finitely generated, then so is the
transgression source `Z^s_{s,n}/B^s_{s,n}` of the left column.  Indeed the chains of `F_s` whose
boundary lies in `F_0` are among those whose boundary lifts to `F_{s-2}` (`Z^s ⊆ Z²`, using
`F_0 ⊆ F_{s-2}`) and boundaries coming from `F_{s+1}` are among those coming from `F_{2s-1}`
(`B² ⊆ B^s`, using `F_{s+1} ⊆ F_{2s-1}`); hence `Z^s/B^s` is a quotient of the submodule
`Z^s/(Z^s ∩ B²)` of `Z²/B²`, and both inclusions are proved by monotonicity of `Submodule.map`
and the functoriality of `Finc` (the maps `F_{s'} → F_s` are the components of the functor `ξ.F`).

(No element chasing is needed: this is pure `Submodule` bookkeeping.) -/
theorem Zs_quot_finite_of_Zsq_quot_finite {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C)
    (s n : ℕ) (hs : 2 ≤ s)
    (h : Module.Finite ℤ (↥(Zsq ξ s n) ⧸ BsqZ ξ s n)) :
    Module.Finite ℤ (↥(Zs ξ s n) ⧸ BsZ ξ s n) := by
  have hZ : Zs ξ s n ≤ Zsq ξ s n := ModelIncl.Zs_le_Zsq ξ s n hs
  have hB : Bsq ξ s n ≤ Bs ξ s n := ModelIncl.Bsq_le_Bs ξ s n hs
  exact finite_quot_comap_of_le hZ hB h

end Work.SSS.ModelQuot
