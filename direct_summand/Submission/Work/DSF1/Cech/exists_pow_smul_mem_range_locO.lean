import Mathlib
import Submission.Work.DSF1.Cech.CechOLocal
import Submission.Work.DSF1.Cech.CechQo
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.DSF1.Cech

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped BigOperators

theorem exists_pow_smul_mem_range_locO (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (U : ι → (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens)
    (V : (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens) (g : R)
    (hsurj : ∀ (n : ℕ)
      (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I),
      ∀ z : (Work.DSF1.Cech.specPresheaf R).obj
          (Opposite.op (Work.DSF1.Cech.Eobj U n x ⊓ V)),
        ∃ (k : ℕ) (t : (Work.DSF1.Cech.specPresheaf R).obj
            (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
          ((Work.DSF1.Cech.specPresheaf R).map
            (homOfLE (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ V ≤
              Work.DSF1.Cech.Eobj U n x)).op).hom t = g ^ k • z)
    (n : ℕ) (z : (Work.DSF1.Cech.cechOQ R U V).X n) :
    ∃ (k : ℕ) (t : (Work.DSF1.Cech.cechO R U).X n),
      (Work.DSF1.Cech.locO R U V).f n t = g ^ k • z := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  -- For every simplex `x` we clear denominators in the `x`-th component of `z`.
  have hcomp : ∀ x : Fin (n+1) → ι,
      ∃ (k : ℕ) (t : (specPresheaf R).obj (op (Eobj U n x))),
        ((specPresheaf R).map (homOfLE (inf_le_left : Eobj U n x ⊓ V ≤ Eobj U n x)).op).hom t
          = g ^ k • (Pi.π (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y))) x).hom z :=
    fun x => hsurj n x _
  choose k tk hk using hcomp
  have hK : ∀ x, k x ≤ ∑ y, k y := fun x =>
    Finset.single_le_sum (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
  -- Reassemble the components, clearing all denominators with the common exponent `∑ k`.
  refine ⟨∑ y, k y, (ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj U n x)))).inv.hom
      (fun x => g ^ ((∑ y, k y) - k x) • tk x), ?_⟩
  -- Check the identity componentwise.
  have hkey : ∀ x : Fin (n+1) → ι,
      (Pi.π (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y))) x).hom
        ((locO R U V).f n ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj U n x)))).inv.hom
          (fun x => g ^ ((∑ y, k y) - k x) • tk x)))
      = (Pi.π (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y))) x).hom
          (g ^ (∑ y, k y) • z) := by
    intro x
    have hstep : (Pi.π (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y))) x).hom
          ((locO R U V).f n ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj U n x)))).inv.hom
            (fun x => g ^ ((∑ y, k y) - k x) • tk x)))
        = ((specPresheaf R).map (homOfLE (inf_le_left : Eobj U n x ⊓ V ≤ Eobj U n x)).op).hom
            ((Pi.π (fun y : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj U n y))) x).hom
              ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj U n x)))).inv.hom
                (fun x => g ^ ((∑ y, k y) - k x) • tk x))) := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (cechComplexFunctor_map_pi U (etaO (specPresheaf R) V) n x))
        ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj U n x)))).inv.hom
          (fun x => g ^ ((∑ y, k y) - k x) • tk x))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    rw [hstep, ModuleCat.piIsoPi_inv_kernel_ι_apply]
    rw [map_smul, hk x, smul_smul, ← pow_add, Nat.sub_add_cancel (hK x)]
    exact (map_smul (Pi.π (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y))) x).hom (g ^ (∑ y, k y)) z).symm
  have h1 : (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y)))).hom.hom
        ((locO R U V).f n ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι => (specPresheaf R).obj (op (Eobj U n x)))).inv.hom
          (fun x => g ^ ((∑ y, k y) - k x) • tk x)))
      = (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y)))).hom.hom
          (g ^ (∑ y, k y) • z) := by
    funext x
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact hkey x
  have h2 := congrArg (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι => (Qo (specPresheaf R) V).obj (op (Eobj U n y)))).inv.hom h1
  simpa only [Iso.hom_inv_id_apply] using h2

end Work.DSF1.Cech
