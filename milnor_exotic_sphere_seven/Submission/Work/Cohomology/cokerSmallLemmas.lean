import Mathlib
import Submission.Work.Cohomology.cokerSmallAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Two elementwise lemmas about the Mayer–Vietoris map `(a, b) ↦ a - b`

* `cokernel_pi_f_eq_zero_iff` — an element of the cokernel of a chain map is killed by the
  projection iff it lies in the range of the chain map (degreewise exactness of a cokernel
  sequence);
* `exists_smallOfU_sub_smallOfV` — every small chain of the cover `{A, V}` is of the form
  `u a - v b` with `u = smallOfU A V`, `v = smallOfV A V` (surjectivity of the middle
  Mayer–Vietoris map, `Work.Cohomology.mv_degreewise`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- If the projection to the cokernel of a chain map kills an element, that element lies in the
range of the chain map. -/
lemma cokernel_pi_f_eq_zero_iff {K L : ChainComplex (ModuleCat ℤ) ℕ} (u : K ⟶ L) (n : ℕ)
    (z : L.X n) :
    ((cokernel.π u).f n) z = 0 ↔ ∃ y : K.X n, (u.f n) y = z := by
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hex : S.Exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u)
  have hd : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).Exact :=
    (HomologicalComplex.exact_iff_degreewise_exact S).1 hex n
  have h := (ShortComplex.moduleCat_exact_iff
    (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n))).1 hd
  have hg : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g
      = (cokernel.π u).f n := by
    rw [ShortComplex.map_g]; rfl
  have hf : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f
      = u.f n := by
    rw [ShortComplex.map_f]; rfl
  rw [hg, hf] at h
  refine ⟨fun hz => h z hz, ?_⟩
  rintro ⟨y, hy⟩
  have hcomp : (u ≫ cokernel.π u).f n = u.f n ≫ (cokernel.π u).f n :=
    HomologicalComplex.comp_f _ _ n
  have hzero : (0 : K ⟶ cokernel u).f n = u.f n ≫ (cokernel.π u).f n := by
    rw [← hcomp, cokernel.condition]
  have h2 := congrArg (fun (g : K.X n ⟶ (cokernel u).X n) => g y) hzero
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← hy]
  exact h2.symm

/-- Every element of the small chains of `(A, V)` is of the form `u a - v b`. -/
lemma exists_smallOfU_sub_smallOfV (A V : Set X) (n : ℕ) (d : (smallChains A V).X n) :
    ∃ (a : (singularChains ℤ (TopCat.of A)).X n) (b : (singularChains ℤ (TopCat.of V)).X n),
      (smallOfU A V).f n a - (smallOfV A V).f n b = d := by
  have hS := mv_degreewise A V n
  have hg : Epi ((mvRight A V).f n) := by
    have h := hS.epi_g
    rw [ShortComplex.map_g] at h
    exact h
  have hsurj : Function.Surjective ((mvRight A V).f n).hom := (ModuleCat.epi_iff_surjective _).1 hg
  obtain ⟨w, hw⟩ := hsurj d
  have htot := biprodX_total_apply (K := singularChains ℤ (TopCat.of A))
    (L := singularChains ℤ (TopCat.of V)) w
  have hd : (mvRight A V).f n
      ((biprod.inl : singularChains ℤ (TopCat.of A) ⟶ singularChains ℤ (TopCat.of A) ⊞
          singularChains ℤ (TopCat.of V)).f n
        ((biprod.fst : singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of V) ⟶
          singularChains ℤ (TopCat.of A)).f n w)
      + (biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of A) ⊞
          singularChains ℤ (TopCat.of V)).f n
        ((biprod.snd : singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of V) ⟶
          singularChains ℤ (TopCat.of V)).f n w)) = d := by
    rw [htot]; exact hw
  rw [map_add, mvRight_inl_eval, mvRight_inr_eval] at hd
  exact ⟨(biprod.fst : singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of V) ⟶
      singularChains ℤ (TopCat.of A)).f n w,
    (biprod.snd : singularChains ℤ (TopCat.of A) ⊞ singularChains ℤ (TopCat.of V) ⟶
      singularChains ℤ (TopCat.of V)).f n w,
    by
      rw [smallOfU_f, smallOfV_f, sub_eq_add_neg]
      exact hd⟩

end

end Work.Cohomology
