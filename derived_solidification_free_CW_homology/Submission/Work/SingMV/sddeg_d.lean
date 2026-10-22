import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.gen_d
import Submission.Work.SingMV.sddeg_naturality
import Submission.Work.SingMV.singEquiv_delta
import Submission.Work.SingMV.sddeg_aux
import Submission.Work.SingMV.sddeg_Sd

/-!
# The degreewise barycentric subdivision is a chain map

`Work.SingMV.sddeg X n` is the `n`-th degree of the barycentric subdivision operator on the
singular chains of a topological space `X`: on the generator of a singular simplex `σ` it is the
pushforward along `σ` of the subdivision `Sd n` of the fundamental `n`-simplex.  This file proves

`∂ (sddeg X (n+1) z) = sddeg X n (∂ z)`,

i.e. that `sddeg` is a chain map.

## Proof

The singular chains are a coproduct of copies of `ℤ` indexed by the singular simplices
(`genHom_hom_ext`), so it suffices to check the identity on the summand inclusions.  For a
singular `(n+1)`-simplex `σ`:

* `sddeg X (n+1) (gen X (n+1) σ) = (σ_*) (Sd (n+1))` (`sddeg_gen`), so
  `∂ (sddeg X (n+1) (gen X (n+1) σ)) = (σ_*) (∂ (Sd (n+1))) = (σ_*) (Bdry n)`
  by `Sd_d_aux` (`∂ (Sd (n+1)) = Bdry n`) and the chain map property of `(σ_*)`
  (`chainMap_d_apply`);
* on the other side, `∂ (gen X (n+1) σ) = Σᵢ (-1)ⁱ gen X n (σ ∘ δᵢ)` (`gen_d`), so
  `sddeg X n (∂ (gen X (n+1) σ)) = Σᵢ (-1)ⁱ (σ ∘ δᵢ)_* (Sd n) = (σ_*) (Σᵢ (-1)ⁱ (δᵢ)_* (Sd n))`
  by `sddeg_gen` and functoriality (`push_comp`), and `Σᵢ (-1)ⁱ (δᵢ)_* (Sd n) = SdBdry n (Sd n)`,
  which is `Bdry n` by `SdBdry_eq_phi` and the definition of `Bdry`.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

noncomputable section

namespace Work.SingMV

theorem sddeg_d (X : TopCat) (n : ℕ) (z : ((Submission.Blueprint.singC).obj X).X (n+1)) :
    (((Submission.Blueprint.singC).obj X).d (n+1) n) (Work.SingMV.sddeg X (n+1) z) =
      Work.SingMV.sddeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n) z) := by
  have key : sddeg X (n+1) ≫ ((Submission.Blueprint.singC).obj X).d (n+1) n
      = ((Submission.Blueprint.singC).obj X).d (n+1) n ≫ sddeg X n := by
    apply genHom_hom_ext
    intro x
    apply hom_int_ext
    have hgen : (ConcreteCategory.hom (genHom X (n+1) x)) (1 : ℤ)
        = gen X (n+1) (singEquiv X (n+1) x) := rfl
    have hL1 : (genHom X (n+1) x ≫
          (sddeg X (n+1) ≫ ((Submission.Blueprint.singC).obj X).d (n+1) n)) (1 : ℤ)
        = (((Submission.Blueprint.singC).obj X).d (n+1) n)
            (((Submission.Blueprint.singC).map
              (TopCat.ofHom (singEquiv X (n+1) x))).f (n+1) (Sd (n+1))) := by
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hgen, sddeg_gen]
    have hL2 : (((Submission.Blueprint.singC).obj X).d (n+1) n)
            (((Submission.Blueprint.singC).map
              (TopCat.ofHom (singEquiv X (n+1) x))).f (n+1) (Sd (n+1)))
        = ((Submission.Blueprint.singC).map
              (TopCat.ofHom (singEquiv X (n+1) x))).f n (Bdry n) :=
      (chainMap_d_apply (tSplx (n+1)) X (TopCat.ofHom (singEquiv X (n+1) x)) n
          (Sd (n+1))).trans
        (congrArg (fun w => ((Submission.Blueprint.singC).map
          (TopCat.ofHom (singEquiv X (n+1) x))).f n w) (Sd_d_aux n))
    have hL := hL1.trans hL2
    have hR1 : (genHom X (n+1) x ≫
          (((Submission.Blueprint.singC).obj X).d (n+1) n ≫ sddeg X n)) (1 : ℤ)
        = sddeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n)
              (gen X (n+1) (singEquiv X (n+1) x))) := by
      rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hgen]
    have hR2 : sddeg X n ((((Submission.Blueprint.singC).obj X).d (n+1) n)
              (gen X (n+1) (singEquiv X (n+1) x)))
        = ((Submission.Blueprint.singC).map
              (TopCat.ofHom (singEquiv X (n+1) x))).f n (Bdry n) := by
      rw [gen_d]
      rw [map_sum]
      simp only [map_zsmul, sddeg_gen]
      refine (Finset.sum_congr rfl (fun (i : Fin (n+2))
          (_ : i ∈ (Finset.univ : Finset (Fin (n+2)))) =>
          congrArg (fun w => (-1 : ℤ) ^ (i : ℕ) • w)
            (push_comp X n (singEquiv X (n+1) x) i (Sd n)))).trans ?_
      refine ((push_SdBdry X n (singEquiv X (n+1) x)).symm).trans ?_
      exact congrArg (fun w => ((Submission.Blueprint.singC).map
          (TopCat.ofHom (singEquiv X (n+1) x))).f n w)
        ((SdBdry_eq_phi n (Sd n)).trans rfl)
    exact hL.trans (hR1.trans hR2).symm
  have hz := congrArg (fun m => m z) key
  simpa only [CategoryTheory.comp_apply] using hz

end Work.SingMV
