import Mathlib
import Submission.Work.SINGMV.Defs
import Submission.Work.SingMV.gen_d
import Submission.Work.SingMV.sddeg_naturality

/-!
# Auxiliary lemmas for the degreewise barycentric subdivision

Elementary algebraic lemmas used in `Submission.Work.SingMV.sddeg_d`:

* `hom_int_ext`: a morphism `ℤ ⟶ M` in `ModuleCat ℤ` is determined by its value at `1`;
* `chainComplex_sum_f`: evaluation at a fixed degree of a finite sum of chain maps;
* `SdBdry_eq_phi`: the elementwise alternating coface sum `SdBdry` agrees with `phi`;
* `sddeg_gen`: the value of the degreewise subdivision on a generator;
* `chainMap_d_apply`: pushforward along a map of spaces commutes with the differential;
* `push_comp`, `push_SdBdry`: bookkeeping for pushing chains forward along a composite.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

noncomputable section

namespace Work.SingMV

/-- A morphism `ℤ ⟶ M` in `ModuleCat ℤ` is determined by its value at `1`. -/
lemma hom_int_ext {M : ModuleCat ℤ} {f g : ModuleCat.of ℤ ℤ ⟶ M} (h : f (1 : ℤ) = g (1 : ℤ)) :
    f = g := by
  apply ModuleCat.hom_ext
  exact LinearMap.ext_ring h

/-- Evaluation at a fixed degree of a finite sum of chain maps. -/
lemma chainComplex_sum_f {C D : ChainComplex (ModuleCat ℤ) ℕ} {ι : Type*} (f : ι → (C ⟶ D))
    (s : Finset ι) (n : ℕ) : (s.sum f).f n = s.sum (fun i => (f i).f n) := by
  classical
  induction s using Finset.induction with
  | empty => simp [HomologicalComplex.zero_f]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, HomologicalComplex.add_f_apply, ih]

/-- `SdBdry` is the alternating coface sum applied elementwise. -/
lemma SdBdry_eq_phi (n : ℕ) (s : ((Submission.Blueprint.singC).obj (tSplx n)).X n) :
    SdBdry n s = (phi n).f n s := by
  have h1 : (phi n).f n
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
          ((Submission.Blueprint.singC).map (coface n i)).f n := by
    rw [phi, chainComplex_sum_f]
    exact Finset.sum_congr rfl (fun i _ => HomologicalComplex.zsmul_f_apply _ _ _)
  rw [h1]
  simp only [SdBdry, ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.sum_apply,
    LinearMap.smul_apply]

/-- The value of the degreewise subdivision on a generator. -/
lemma sddeg_gen (X : TopCat) (n : ℕ) (σ : singMap X n) :
    sddeg X n (gen X n σ) =
      ((Submission.Blueprint.singC.map (TopCat.ofHom σ)).f n (Sd n)) := by
  let x := (singEquiv X n).symm σ
  have hfac := sddeg_fac X n x
  have h := congrArg (fun f => f (1 : ℤ)) hfac
  rw [CategoryTheory.comp_apply] at h
  rw [ModuleCat.ofHom_apply, LinearMap.toSpanSingleton_apply_one] at h
  have hx : (ConcreteCategory.hom (genHom X n x)) (1 : ℤ) = gen X n σ := rfl
  rw [hx] at h
  have hx2 : (singEquiv X n) x = σ := by simp [x]
  rw [hx2] at h
  exact h

/-- The pushforward along a map of spaces commutes with the differential. -/
lemma chainMap_d_apply (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (y : ((Submission.Blueprint.singC).obj X).X (n+1)) :
    (((Submission.Blueprint.singC).obj Y).d (n+1) n)
        (((Submission.Blueprint.singC).map f).f (n+1) y)
      = ((Submission.Blueprint.singC).map f).f n
        ((((Submission.Blueprint.singC).obj X).d (n+1) n) y) := by
  have h := HomologicalComplex.Hom.comm ((Submission.Blueprint.singC).map f) (n+1) n
  exact congrArg (fun m => m y) h

/-- Pushing a chain forward along `σ ∘ δᵢ` is pushing forward along `σ` after `δᵢ`. -/
lemma push_comp (X : TopCat) (n : ℕ) (σ : singMap X (n+1)) (i : Fin (n+2))
    (y : ((Submission.Blueprint.singC).obj (tSplx n)).X n) :
    ((Submission.Blueprint.singC).map (TopCat.ofHom (σ.comp (coface n i).hom))).f n y
      = ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f n
          (((Submission.Blueprint.singC).map (coface n i)).f n y) := by
  rw [show (Submission.Blueprint.singC).map (TopCat.ofHom (σ.comp (coface n i).hom))
      = (Submission.Blueprint.singC).map (coface n i) ≫
          (Submission.Blueprint.singC).map (TopCat.ofHom σ) from by
    rw [TopCat.ofHom_comp, Functor.map_comp]
    rfl]
  rw [HomologicalComplex.comp_f, CategoryTheory.comp_apply]

/-- Linear expansion of the pushforward of the alternating coface sum of `Sd n`. -/
lemma push_SdBdry (X : TopCat) (n : ℕ) (σ : singMap X (n+1)) :
    ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f n (SdBdry n (Sd n))
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
          ((Submission.Blueprint.singC).map (TopCat.ofHom σ)).f n
            (((Submission.Blueprint.singC).map (coface n i)).f n (Sd n)) := by
  rw [show SdBdry n (Sd n)
      = ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
          ((Submission.Blueprint.singC).map (coface n i)).f n (Sd n) from rfl]
  rw [map_sum]
  simp only [map_zsmul]

end Work.SingMV
