import Mathlib
import Submission.Work.DSF1.Sheaf.CechGen
import Submission.Work.DSF1.Cech.exists_pow_smul_mem_range_loc
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero

/-!
# Clearing denominators for the comparison maps, arbitrary coefficient presheaf

Let `R` be a commutative ring, `f : ι → R` a finite family, `U i = D (f i)` the principal
opens of `Spec R`, and `P` a presheaf of `R`-modules on the opens of `Spec R`.  If the
componentwise clearing of denominators `CompLoc P (f i)` holds, then the comparison map
`loc i : Č(P) ⟶ Č(Qi U P i)` of Čech complexes clears denominators at the level of the
complexes: every element of a term of the localized complex is, up to a power of `f i`, in
the image of the comparison map, and the kernel of the comparison map is killed by a power
of `f i`.

These are the coefficient-agnostic versions of `Work.DSF1.Cech.exists_pow_smul_mem_range_loc`
and `Work.DSF1.Cech.eq_zero_of_loc_eq_zero` (the case `P = specPresheaf R`).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

variable {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]

/-- **Componentwise clearing of denominators (surjectivity).** -/
lemma Eobj_loc_component_S (f : ι → R) (P : MPSheaf (CommRingCat.of R)) (i : ι)
    (hP : CompLoc P (f i)) (n : ℕ) (x : Fin (n+1) → ι)
    (z : ↥((Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
      (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))) :
    ∃ (k : ℕ) (t : ↥(P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))),
      (P.map (homOfLE (inf_le_left :
        Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
          Work.DSF1.Cech.basicOpens f i ≤
          Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)).op).hom t = f i ^ k • z := by
  have hx : Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x =
      PrimeSpectrum.basicOpen (∏ a, f (x a)) := Work.DSF1.Cech.Eobj_basicOpens f n x
  have hi : Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
      Work.DSF1.Cech.basicOpens f i =
      PrimeSpectrum.basicOpen (∏ a, f (x a)) ⊓ PrimeSpectrum.basicOpen (f i) :=
    congrArg (fun U => U ⊓ Work.DSF1.Cech.basicOpens f i) hx
  obtain ⟨k, t', ht'⟩ := hP.1 (∏ a, f (x a))
    ((P.map (eqToHom hi.symm).op).hom z)
  refine ⟨k, (P.map (eqToHom hx).op).hom t', ?_⟩
  have hsq : P.map (eqToHom hx).op ≫
        (P.map (homOfLE (inf_le_left :
          Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
            Work.DSF1.Cech.basicOpens f i ≤
            Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)).op) =
      (P.map (homOfLE (inf_le_left :
          PrimeSpectrum.basicOpen (∏ a, f (x a)) ⊓ PrimeSpectrum.basicOpen (f i) ≤
            PrimeSpectrum.basicOpen (∏ a, f (x a)))).op) ≫
        (P.map (eqToHom hi).op) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hsq, ModuleCat.hom_comp,
    LinearMap.comp_apply, ht', map_smul]
  congr 1
  simp

end Work.DSF1.Sheaf

namespace Work.DSF1.Sheaf

universe u

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

variable {R : Type u} [CommRing R] {ι : Type u} [Fintype ι]

/-- **Componentwise clearing of denominators (vanishing).** -/
lemma Eobj_loc_component_K (f : ι → R) (P : MPSheaf (CommRingCat.of R)) (i : ι)
    (hP : CompLoc P (f i)) (n : ℕ) (x : Fin (n+1) → ι)
    (t : ↥(P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x))))
    (h : (P.map (homOfLE (inf_le_left :
        Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
          Work.DSF1.Cech.basicOpens f i ≤
          Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)).op).hom t = 0) :
    ∃ k : ℕ, f i ^ k • t = 0 := by
  have hx : Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x =
      PrimeSpectrum.basicOpen (∏ a, f (x a)) := Work.DSF1.Cech.Eobj_basicOpens f n x
  have hi : Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
      Work.DSF1.Cech.basicOpens f i =
      PrimeSpectrum.basicOpen (∏ a, f (x a)) ⊓ PrimeSpectrum.basicOpen (f i) :=
    congrArg (fun U => U ⊓ Work.DSF1.Cech.basicOpens f i) hx
  have hsq : P.map (eqToHom hx.symm).op ≫
        (P.map (homOfLE (inf_le_left :
          PrimeSpectrum.basicOpen (∏ a, f (x a)) ⊓ PrimeSpectrum.basicOpen (f i) ≤
            PrimeSpectrum.basicOpen (∏ a, f (x a)))).op) =
      (P.map (homOfLE (inf_le_left :
          Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
            Work.DSF1.Cech.basicOpens f i ≤
            Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)).op) ≫
        (P.map (eqToHom hi.symm).op) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have h' : (P.map (homOfLE (inf_le_left :
        PrimeSpectrum.basicOpen (∏ a, f (x a)) ⊓ PrimeSpectrum.basicOpen (f i) ≤
          PrimeSpectrum.basicOpen (∏ a, f (x a)))).op).hom
      ((P.map (eqToHom hx.symm).op).hom t) = 0 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, hsq, ModuleCat.hom_comp,
      LinearMap.comp_apply, h, map_zero]
  obtain ⟨k, hk⟩ := hP.2 (∏ a, f (x a)) _ h'
  refine ⟨k, (ConcreteCategory.bijective_of_isIso (P.map (eqToHom hx.symm).op)).1 ?_⟩
  rw [map_smul, hk, map_zero]

/-- **Clearing denominators for `locGen` (surjectivity).** -/
theorem clearing_surj (f : ι → R) (P : MPSheaf (CommRingCat.of R))
    (i : ι) (hP : CompLoc P (f i)) (n : ℕ)
    (z : ↥((cechGen (Work.DSF1.Cech.basicOpens f)
      (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i)).X n)) :
    ∃ (k : ℕ) (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X n)),
      (locGen (Work.DSF1.Cech.basicOpens f) P i).f n t = f i ^ k • z := by
  classical
  have hcomp : ∀ x : Fin (n+1) → ι,
      ∃ (k : ℕ) (t : ↥(P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))),
        (P.map (homOfLE (inf_le_left :
          Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
            Work.DSF1.Cech.basicOpens f i ≤
          Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)).op).hom t
          = f i ^ k • (Pi.π (fun y : Fin (n+1) → ι =>
              (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
                (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y))) x).hom z :=
    fun x => Eobj_loc_component_S f P i hP n x _
  choose k tk hk using hcomp
  have hK : ∀ x, k x ≤ ∑ y, k y := fun x =>
    Finset.single_le_sum (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
  refine ⟨∑ y, k y, (ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
    P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))).inv.hom
      (fun x => f i ^ ((∑ y, k y) - k x) • tk x), ?_⟩
  have hkey : ∀ x : Fin (n+1) → ι,
      (Pi.π (fun y : Fin (n+1) → ι =>
          (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
            (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y))) x).hom
        ((locGen (Work.DSF1.Cech.basicOpens f) P i).f n
          ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
            P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))).inv.hom
            (fun x => f i ^ ((∑ y, k y) - k x) • tk x)))
      = (Pi.π (fun y : Fin (n+1) → ι =>
          (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
            (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y))) x).hom
          (f i ^ (∑ y, k y) • z) := by
    intro x
    have hstep : (Pi.π (fun y : Fin (n+1) → ι =>
          (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
            (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y))) x).hom
          ((locGen (Work.DSF1.Cech.basicOpens f) P i).f n
            ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
              P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))).inv.hom
              (fun x => f i ^ ((∑ y, k y) - k x) • tk x)))
        = (P.map (homOfLE (inf_le_left :
            Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
              Work.DSF1.Cech.basicOpens f i ≤
            Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)).op).hom
            ((Pi.π (fun y : Fin (n+1) → ι =>
              P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y))) x).hom
              ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
                P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))).inv.hom
                (fun x => f i ^ ((∑ y, k y) - k x) • tk x))) := by
      have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (Work.DSF1.Cech.cechComplexFunctor_map_pi (Work.DSF1.Cech.basicOpens f)
          (Work.DSF1.Cech.etaI (Work.DSF1.Cech.basicOpens f) P i) n x))
        ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
          P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))).inv.hom
          (fun x => f i ^ ((∑ y, k y) - k x) • tk x))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
    rw [hstep, ModuleCat.piIsoPi_inv_kernel_ι_apply]
    rw [map_smul, hk x, smul_smul, ← pow_add, Nat.sub_add_cancel (hK x)]
    exact (map_smul (Pi.π (fun y : Fin (n+1) → ι =>
      (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
        (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y))) x).hom
      (f i ^ (∑ y, k y)) z).symm
  have h1 : (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι =>
        (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
          (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y)))).hom.hom
        ((locGen (Work.DSF1.Cech.basicOpens f) P i).f n
          ((ModuleCat.piIsoPi (fun x : Fin (n+1) → ι =>
            P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)))).inv.hom
            (fun x => f i ^ ((∑ y, k y) - k x) • tk x)))
      = (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι =>
          (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
            (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y)))).hom.hom
          (f i ^ (∑ y, k y) • z) := by
    funext x
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    exact hkey x
  have h2 := congrArg (ModuleCat.piIsoPi (fun y : Fin (n+1) → ι =>
    (Work.DSF1.Cech.Qi (Work.DSF1.Cech.basicOpens f) P i).obj
      (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y)))).inv.hom h1
  simpa only [Iso.hom_inv_id_apply] using h2

/-- **Clearing denominators for `locGen` (vanishing).** -/
theorem clearing_ker (f : ι → R) (P : MPSheaf (CommRingCat.of R))
    (i : ι) (hP : CompLoc P (f i)) (n : ℕ)
    (t : ↥((cechGen (Work.DSF1.Cech.basicOpens f) P).X n))
    (h : (locGen (Work.DSF1.Cech.basicOpens f) P i).f n t = 0) :
    ∃ k : ℕ, f i ^ k • t = 0 := by
  classical
  let F : ((FormalCoproduct.mk ι (Work.DSF1.Cech.basicOpens f)).cech.obj (op ⦋n⦌)).I →
      ModuleCat.{u} R :=
    fun y => P.obj (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n y))
  have hstep : ∀ x, ∃ k : ℕ, f i ^ k • ((Pi.π F x).hom t) = 0 := by
    intro x
    have hA : ((Work.DSF1.Cech.etaI (Work.DSF1.Cech.basicOpens f) P i).app
        (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x))).hom
        ((Pi.π F x).hom t) = 0 := by
      have hmap := Work.DSF1.Cech.cechComplexFunctor_map_pi (Work.DSF1.Cech.basicOpens f)
        (Work.DSF1.Cech.etaI (Work.DSF1.Cech.basicOpens f) P i) n x
      have key := congrArg (fun m => ModuleCat.Hom.hom m t) hmap
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at key
      have hl : (((cechComplexFunctor (Work.DSF1.Cech.basicOpens f)).map
          (Work.DSF1.Cech.etaI (Work.DSF1.Cech.basicOpens f) P i)).f n).hom t = 0 := h
      rw [hl, map_zero] at key
      exact key.symm
    rw [show (Work.DSF1.Cech.etaI (Work.DSF1.Cech.basicOpens f) P i).app
        (op (Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x))
        = (P.map (homOfLE (inf_le_left :
            Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x ⊓
              Work.DSF1.Cech.basicOpens f i ≤
            Work.DSF1.Cech.Eobj (Work.DSF1.Cech.basicOpens f) n x)).op)
        from rfl] at hA
    exact Eobj_loc_component_K f P i hP n x _ hA
  choose K hK using hstep
  letI : Fintype ((FormalCoproduct.mk ι (Work.DSF1.Cech.basicOpens f)).cech.obj
      (op ⦋n⦌)).I := inferInstanceAs (Fintype (Fin (n+1) → ι))
  refine ⟨Finset.univ.sup K, ?_⟩
  apply Work.DSF1.Cech.pi_ext (F := F)
  intro x
  rw [map_smul, map_zero]
  have hle : K x ≤ Finset.univ.sup K := Finset.le_sup (Finset.mem_univ x)
  have hp : f i ^ (Finset.univ.sup K) = f i ^ (Finset.univ.sup K - K x) * f i ^ (K x) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp, mul_smul, hK x, smul_zero]

end Work.DSF1.Sheaf
