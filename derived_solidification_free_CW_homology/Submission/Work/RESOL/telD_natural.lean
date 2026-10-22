import Mathlib
import Submission.Work.RESOL.Telescope

open CategoryTheory Limits

namespace Work.RESOL

/-- Naturality of the shift map `smap`:  a family `g n : P n ⟶ P' n` commuting with the
transition maps (`t n ≫ g (n+1) = g n ≫ t' n`) induces a map `∐ P ⟶ ∐ P'` of coproducts
which commutes with the shifts. -/
lemma smap_natural (P P' : ℕ → Work.RESOL.Cpx)
    [CategoryTheory.Limits.HasCoproduct P] [CategoryTheory.Limits.HasCoproduct P']
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (t' : ∀ n : ℕ, P' n ⟶ P' (n+1))
    (g : ∀ n : ℕ, P n ⟶ P' n)
    (hgt : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (t n) (g (n+1)) =
      CategoryTheory.CategoryStruct.comp (g n) (t' n)) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.smap P t)
        (CategoryTheory.Limits.Sigma.desc (fun n : ℕ =>
          CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n))) =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.Sigma.desc (fun n : ℕ =>
          CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n)))
        (Work.RESOL.smap P' t') := by
  apply Sigma.hom_ext
  intro n
  have hA : CategoryTheory.CategoryStruct.comp (Sigma.ι P n)
      (CategoryTheory.CategoryStruct.comp (smap P t)
        (Sigma.desc (fun m : ℕ => CategoryTheory.CategoryStruct.comp (g m) (Sigma.ι P' m)))) =
      CategoryTheory.CategoryStruct.comp (t n)
        (CategoryTheory.CategoryStruct.comp (g (n+1)) (Sigma.ι P' (n+1))) := by
    rw [← Category.assoc, Sigma_ι_smap, Category.assoc, Sigma.ι_comp_desc]
  have hB : CategoryTheory.CategoryStruct.comp (Sigma.ι P n)
      (CategoryTheory.CategoryStruct.comp
        (Sigma.desc (fun m : ℕ => CategoryTheory.CategoryStruct.comp (g m) (Sigma.ι P' m)))
        (smap P' t')) =
      CategoryTheory.CategoryStruct.comp (g n)
        (CategoryTheory.CategoryStruct.comp (t' n) (Sigma.ι P' (n+1))) := by
    rw [← Category.assoc, Sigma.ι_comp_desc, Category.assoc, Sigma_ι_smap]
  rw [hA, hB]
  conv_lhs => rw [← Category.assoc]
  conv_rhs => rw [← Category.assoc]
  rw [hgt n]

theorem telD_natural (P P' : ℕ → Work.RESOL.Cpx)
    [CategoryTheory.Limits.HasCoproduct P] [CategoryTheory.Limits.HasCoproduct P']
    (t : ∀ n : ℕ, P n ⟶ P (n+1)) (t' : ∀ n : ℕ, P' n ⟶ P' (n+1))
    (g : ∀ n : ℕ, P n ⟶ P' n)
    (hgt : ∀ n : ℕ, CategoryTheory.CategoryStruct.comp (t n) (g (n+1)) =
      CategoryTheory.CategoryStruct.comp (g n) (t' n)) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.telD P t)
        (CategoryTheory.Limits.Sigma.desc (fun n : ℕ =>
          CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n))) =
      CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.Sigma.desc (fun n : ℕ =>
          CategoryTheory.CategoryStruct.comp (g n) (CategoryTheory.Limits.Sigma.ι P' n)))
        (Work.RESOL.telD P' t') := by
  rw [telD, telD, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    Category.comp_id, smap_natural P P' t t' g hgt]

end Work.RESOL
