import Mathlib
import Submission.Work.DSEQP.EqpCechSetup
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSF1.Cech.exists_pow_smul_mem_range_locO

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.DSEQP

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

/-- Clearing denominators for the comparison map of Čech complexes
`locCech A X f U g : DSMap.cech A X f U ⟶ cechLoc A X f U g`, where `cechLoc A X f U g` is the Čech
complex of the presheaf `W ↦ Γ(X, W ⊓ X_g)` (`presheafLoc`).

If every *component* of the comparison map is surjective up to powers of `g` (hypothesis `hsurj`:
for every simplex `x`, every element of `Γ(X, Eobj U n x ⊓ X_g)` is `g ^ k` times the restriction
of an element of `Γ(X, Eobj U n x)`), then so is the map in every degree.

In degree `n` the Čech complex is the finite product, over the simplices `x`, of the section
modules `Γ(X, Eobj U n x)` (resp. `Γ(X, Eobj U n x ⊓ X_g)`), and the comparison map is the product
of the restrictions.  Use `Work.DSF1.Cech.cechComplexFunctor_map_pi` for the component formula of
the differential/chain map, `ModuleCat.piIsoPi` to reassemble the product, and `Finset.sup` to
collect the finitely many exponents.  This is exactly
`Work.DSF1.Cech.exists_pow_smul_mem_range_locO`
(`Submission/Work/DSF1/Cech/exists_pow_smul_mem_range_locO.lean`) with `specPresheaf R`, `Spec R`,
`basicOpens f` replaced by `DSMap.cechPresheaf A X f`, `X`, `Xg A X f g`; its proof can be
generalised line by line (the only `R`-specific input there is the componentwise lemma, which here
is the hypothesis `hsurj`). -/
theorem eqp_cech_clear_denoms (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (g : A)
    (hsurj : ∀ (n : ℕ) (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n))).I),
      ∀ z : (Work.DSEQP.presheafLoc A X f g).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)),
        ∃ (k : ℕ) (t : (DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
          ((DSMap.cechPresheaf A X f).map
            (CategoryTheory.homOfLE
              (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ Work.DSEQP.Xg A X f g ≤
                Work.DSF1.Cech.Eobj U n x)).op).hom t = g ^ k • z)
    (n : ℕ) (z : (Work.DSEQP.cechLoc A X f U g).X n) :
    ∃ (k : ℕ) (t : (DSMap.cech A X f U).X n),
      (Work.DSEQP.locCech A X f U g).f n t = g ^ k • z := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  -- For every simplex `x` we clear denominators in the `x`-th component of `z`.
  have hcomp : ∀ x : Fin (n+1) → ι,
      ∃ (k : ℕ) (t : (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n x))),
        ((DSMap.cechPresheaf A X f).map
            (homOfLE (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ Xg A X f g ≤
              Work.DSF1.Cech.Eobj U n x)).op).hom t
          = g ^ k • (Pi.π (fun y : Fin (n+1) → ι =>
              (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y))) x).hom z :=
    fun x => hsurj n x _
  choose k tk hk using hcomp
  have hK : ∀ x, k x ≤ ∑ y, k y := fun x =>
    Finset.single_le_sum (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
  -- Reassemble the components, clearing all denominators with the common exponent `∑ k`.
  refine ⟨∑ y, k y, (ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
      (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n x)))).inv.hom
      (fun x => g ^ ((∑ y, k y) - k x) • tk x), ?_⟩
  -- Check the identity componentwise.
  have hkey : ∀ x : Fin (n+1) → ι,
      (Pi.π (fun y : Fin (n+1) → ι =>
          (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y))) x).hom
        ((locCech A X f U g).f n
          ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
            (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n x)))).inv.hom
            (fun x => g ^ ((∑ y, k y) - k x) • tk x)))
      = (Pi.π (fun y : Fin (n+1) → ι =>
          (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y))) x).hom
          (g ^ (∑ y, k y) • z) := by
    intro x
    have hstep : (Pi.π (fun y : Fin (n+1) → ι =>
          (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y))) x).hom
          ((locCech A X f U g).f n
            ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
              (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n x)))).inv.hom
              (fun x => g ^ ((∑ y, k y) - k x) • tk x)))
        = ((DSMap.cechPresheaf A X f).map
            (homOfLE (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ Xg A X f g ≤
              Work.DSF1.Cech.Eobj U n x)).op).hom
            ((Pi.π (fun y : Fin (n+1) → ι =>
              (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n y))) x).hom
              ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
                (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n x)))).inv.hom
                (fun x => g ^ ((∑ y, k y) - k x) • tk x))) := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (Work.DSF1.Cech.cechComplexFunctor_map_pi U
          (Work.DSF1.Cech.etaO (DSMap.cechPresheaf A X f) (Xg A X f g)) n x))
        ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
          (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n x)))).inv.hom
          (fun x => g ^ ((∑ y, k y) - k x) • tk x))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    rw [hstep, ModuleCat.piIsoPi_inv_kernel_ι_apply]
    rw [map_smul, hk x, smul_smul, ← pow_add, Nat.sub_add_cancel (hK x)]
    exact (map_smul (Pi.π (fun y : Fin (n+1) → ι =>
      (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y))) x).hom
      (g ^ (∑ y, k y)) z).symm
  have h1 : (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι =>
        (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y)))).hom.hom
        ((locCech A X f U g).f n
          ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
            (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n x)))).inv.hom
            (fun x => g ^ ((∑ y, k y) - k x) • tk x)))
      = (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι =>
          (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y)))).hom.hom
          (g ^ (∑ y, k y) • z) := by
    funext x
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact hkey x
  have h2 := congrArg (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι =>
    (presheafLoc A X f g).obj (op (Work.DSF1.Cech.Eobj U n y)))).inv.hom h1
  simpa only [Iso.hom_inv_id_apply] using h2

end Work.DSEQP
