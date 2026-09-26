import Mathlib
import Submission.Work.Modular.GroupAlgebra
import Submission.Work.Modular.quotient_linearIndependent
import Submission.Work.Modular.mul_basisElem_sub_mem_idealI

namespace Work.Modular

open Work.Modular
open scoped MonoidAlgebra

/-- The `ℂ`-span of the six images `1, T, TS, S, ST, STS` in `ℂ[Γ]/I`. -/
private noncomputable def spanSix : Submodule ℂ (GroupRing ⧸ idealI) :=
  Submodule.span ℂ (Set.range (fun i : Fin 6 => Submodule.mkQ idealI (basisElem i)))

/-- The image of any group element lies in the span of the six basis images: this is the
reduction `M i * γ = σ(γ) M i + I` of the group algebra, read in the first row. -/
private lemma mkQ_of_mem_spanSix (γ : Gamma) :
    Submodule.mkQ idealI (MonoidAlgebra.of ℂ Gamma γ) ∈ spanSix := by
  have hmem := mul_basisElem_sub_mem_idealI γ (0 : Fin 6)
  have hzero : Submodule.mkQ idealI
      (basisElem 0 * MonoidAlgebra.of ℂ Gamma γ -
        ∑ j, (sigmaAlg (MonoidAlgebra.of ℂ Gamma γ)) 0 j • basisElem j) = 0 := by
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero idealI).mpr hmem
  rw [map_sub, sub_eq_zero] at hzero
  rw [show basisElem (0 : Fin 6) = (1 : GroupRing) by simp [basisElem], one_mul] at hzero
  rw [hzero, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem spanSix _ (Submodule.subset_span ?_)
  exact ⟨j, rfl⟩

/-- Every element of `ℂ[Γ]` maps into the span of the six basis images. -/
private lemma mkQ_mem_spanSix (x : GroupRing) : Submodule.mkQ idealI x ∈ spanSix :=
  MonoidAlgebra.induction_on (R := ℂ) (M := Gamma)
    (motive := fun y => Submodule.mkQ idealI y ∈ spanSix) x
    (fun m => mkQ_of_mem_spanSix m)
    (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem spanSix ha hb)
    (fun c a ha => by rw [map_smul]; exact Submodule.smul_mem spanSix c ha)

/-- The six images `1, T, TS, S, ST, STS` span `ℂ[Γ]/I`. -/
private theorem spanSix_eq_top : spanSix = ⊤ := by
  rw [eq_top_iff]
  intro r _
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective idealI r
  exact mkQ_mem_spanSix x

/-- **Proposition 3.3 of the paper**: the images of `1, T, TS, S, ST, STS` form a basis of
`ℂ[Γ]/I`; in particular `dim_ℂ ℂ[Γ]/I = 6`. -/
theorem quotient_basis : ∃ b : Module.Basis (Fin 6) ℂ (GroupRing ⧸ idealI),
    ∀ i, b i = Submodule.mkQ idealI (basisElem i) := by
  refine ⟨Module.Basis.mk quotient_linearIndependent ?_, fun i => ?_⟩
  · show ⊤ ≤ spanSix
    rw [spanSix_eq_top]
  · rw [Module.Basis.mk_apply]

end Work.Modular
