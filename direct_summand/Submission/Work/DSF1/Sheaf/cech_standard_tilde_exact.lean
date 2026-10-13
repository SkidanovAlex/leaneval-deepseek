import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSF1.Sheaf.assembly
import Submission.Work.DSF1.Sheaf.forget_cech_iso

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

/-- Exactness of an `ℕ`-graded cochain complex of abelian groups in positive degrees, in
elementwise form. -/
theorem exactAt_succ_iff_ab (K : CochainComplex AddCommGrpCat.{u} ℕ) (n : ℕ) :
    K.ExactAt (n + 1) ↔ ∀ s : ↥(K.X (n + 1)), (K.d (n + 1) (n + 2)) s = 0 →
      ∃ t : ↥(K.X n), (K.d n (n + 1)) t = s := by
  have hp : (ComplexShape.up ℕ).prev (n + 1) = n :=
    ComplexShape.prev_eq' (c := ComplexShape.up ℕ) (by rfl)
  have hn : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
    ComplexShape.next_eq' (c := ComplexShape.up ℕ) (by rfl)
  rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) hp hn, ShortComplex.ab_exact_iff]
  exact Iff.rfl

/-- The Čech complex of the standard cover `D (f i)` of `Spec R` with coefficients in `M^~`
has no homology in positive degrees. -/
theorem cech_standard_tilde_exact (R : CommRingCat.{u}) {ι : Type u} [Finite ι] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤) (M : ModuleCat.{u} R) (p : ℕ) :
    CategoryTheory.Limits.IsZero (HomologicalComplex.homology
      ((CategoryTheory.cechComplexFunctor (fun i ↦ PrimeSpectrum.basicOpen (f i))).obj
        ((_root_.SheafOfModules.toSheaf (AlgebraicGeometry.Spec R).ringCatSheaf).obj
          (AlgebraicGeometry.tilde M)).obj) (p + 1)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let U : ι → Och R := fun i => PrimeSpectrum.basicOpen (f i)
  let P : MPSheaf R := tildePresheaf M
  have hcompl : ((CategoryTheory.cechComplexFunctor
        (fun i ↦ PrimeSpectrum.basicOpen (f i))).obj
      ((_root_.SheafOfModules.toSheaf (AlgebraicGeometry.Spec R).ringCatSheaf).obj
        (AlgebraicGeometry.tilde M)).obj) = cechAb R U P := rfl
  rw [hcompl, ← HomologicalComplex.exactAt_iff_isZero_homology,
    exactAt_succ_iff_ab]
  obtain ⟨e⟩ := forget_cech_iso R U P
  intro x₂ hx₂
  set y₂ : ↥((forgetComplex R U P).X (p + 1)) := (e.inv.f (p + 1)) x₂ with hy₂
  have hy₂_zero : (forgetComplex R U P).d (p + 1) (p + 2) y₂ = 0 := by
    have hcomm := (e.inv).comm' (p + 1) (p + 2) (by simp)
    have key : (forgetComplex R U P).d (p + 1) (p + 2) ((e.inv.f (p + 1)) x₂) =
        (e.inv.f (p + 2)) ((cechAb R U P).d (p + 1) (p + 2) x₂) := by
      have h := congrArg (fun (g : (cechAb R U P).X (p + 1) ⟶
        (forgetComplex R U P).X (p + 2)) => g x₂) hcomm
      simpa only [ConcreteCategory.comp_apply] using h
    rw [hy₂, key, hx₂, map_zero]
  obtain ⟨y₁, hy₁⟩ := cechGen_tildePresheaf_exact R f hf M p y₂ hy₂_zero
  have hy₁' : (forgetComplex R U P).d p (p + 1) y₁ = y₂ := hy₁
  refine ⟨(e.hom.f p) y₁, ?_⟩
  have hcomm := (e.hom).comm' p (p + 1) (by simp)
  have key : (cechAb R U P).d p (p + 1) ((e.hom.f p) y₁) =
      (e.hom.f (p + 1)) ((forgetComplex R U P).d p (p + 1) y₁) := by
    have h := congrArg (fun (g : (forgetComplex R U P).X p ⟶
      (cechAb R U P).X (p + 1)) => g y₁) hcomm
    simpa only [ConcreteCategory.comp_apply] using h
  rw [key, hy₁', hy₂]
  have hcomp : (e.inv.f (p + 1)) ≫ (e.hom.f (p + 1)) = 𝟙 ((cechAb R U P).X (p + 1)) := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  exact congrArg (fun (g : (cechAb R U P).X (p + 1) ⟶ (cechAb R U P).X (p + 1)) =>
    g x₂) hcomp

end Work.DSF1.Sheaf
