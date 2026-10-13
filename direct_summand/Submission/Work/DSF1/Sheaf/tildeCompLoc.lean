import Mathlib
import Submission.Work.DSF1.Sheaf.CechGen

/-!
# Clearing denominators for `M^~` over basic opens

Proves `Work.DSF1.Sheaf.CompLoc (tildePresheaf M) h`: the restriction
`Γ(D g, M^~) ⟶ Γ(D g ⊓ D h, M^~)` is the localization of the source away from `h`.

The proof uses Mathlib's localization statements
`IsLocalizedModule.Away g (tilde.toOpen M (basicOpen g))` and
`IsLocalizedModule.Away (g * h) (tilde.toOpen M (basicOpen (g * h)))`, together with the
compatibility `tilde.toOpen_res` of the restriction with the structure maps.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped AlgebraicGeometry Simplicial BigOperators

namespace Work.DSF1.Sheaf

universe u

variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R)

/-- The basic open `D g` as an open of `Spec R`. -/
noncomputable abbrev tOpen (g : R) : (Spec R).Opens := PrimeSpectrum.basicOpen g

lemma tOpen_mul (g h : R) : tOpen R (g * h) = tOpen R g ⊓ tOpen R h :=
  PrimeSpectrum.basicOpen_mul g h

/-- Sections of `M^~` over `D g`. -/
noncomputable abbrev tSec (g : R) : Type u :=
  ↥((tildePresheaf M).obj (op (tOpen R g)))

/-- The restriction `Γ(D g, M^~) ⟶ Γ(D (g * h), M^~)`. -/
noncomputable abbrev tRes (g h : R) : tSec R M g →ₗ[R] tSec R M (g * h) :=
  ((tildePresheaf M).map
    (homOfLE (by rw [tOpen_mul]; exact inf_le_left)).op).hom

/-- The structure map `M ⟶ Γ(D g, M^~)`. -/
noncomputable abbrev tTo (g : R) : ↥M →ₗ[R] tSec R M g :=
  (AlgebraicGeometry.tilde.toOpen M (tOpen R g)).hom

/-- The structure map `M ⟶ Γ(D (g * h), M^~)`. -/
noncomputable abbrev tTo' (g h : R) : ↥M →ₗ[R] tSec R M (g * h) :=
  (AlgebraicGeometry.tilde.toOpen M (tOpen R (g * h))).hom

instance instAwayTo (g : R) : IsLocalizedModule.Away g (tTo R M g) :=
  inferInstanceAs (IsLocalizedModule.Away g (AlgebraicGeometry.tilde.toOpen M (tOpen R g)).hom)

instance instAwayTo' (g h : R) : IsLocalizedModule.Away (g * h) (tTo' R M g h) :=
  inferInstanceAs (IsLocalizedModule.Away (g * h)
    (AlgebraicGeometry.tilde.toOpen M (tOpen R (g * h))).hom)

variable {R M}

lemma tRes_comp_tTo (g h : R) :
    (tRes R M g h).comp (tTo R M g) = tTo' R M g h := by
  have h1 := AlgebraicGeometry.tilde.toOpen_res M (tOpen R g) (tOpen R (g * h))
    (homOfLE (by rw [tOpen_mul]; exact inf_le_left))
  ext m
  exact congrArg (fun (f : M ⟶ (AlgebraicGeometry.modulesSpecToSheaf.obj
      (AlgebraicGeometry.tilde M)).presheaf.obj (op (tOpen R (g * h)))) => f.hom m) h1

/-- The restriction commutes with the action of an element invertible on both sides. -/
lemma tRes_unit_inv_smul (g h : R) (c : R)
    (hcA : IsUnit (algebraMap R (Module.End R (tSec R M g)) c))
    (hcB : IsUnit (algebraMap R (Module.End R (tSec R M (g * h))) c)) (a : tSec R M g) :
    tRes R M g h ((↑(hcA.unit⁻¹) : Module.End R (tSec R M g)) a) =
      (↑(hcB.unit⁻¹) : Module.End R (tSec R M (g * h))) (tRes R M g h a) := by
  have hcj : Function.Injective (fun b : tSec R M (g * h) => c • b) :=
    ((Module.End.isUnit_iff _).mp hcB).1
  have hA : c • ((↑(hcA.unit⁻¹) : Module.End R (tSec R M g)) a) = a :=
    Module.End.isUnit_apply_inv_apply_of_isUnit hcA a
  have hB : ∀ b : tSec R M (g * h),
      c • ((↑(hcB.unit⁻¹) : Module.End R (tSec R M (g * h))) b) = b := fun b =>
    Module.End.isUnit_apply_inv_apply_of_isUnit hcB b
  apply hcj
  change c • tRes R M g h ((↑(hcA.unit⁻¹) : Module.End R (tSec R M g)) a) =
    c • ((↑(hcB.unit⁻¹) : Module.End R (tSec R M (g * h))) (tRes R M g h a))
  rw [← map_smul, hA, hB]

/-- On `Γ(D (g * h), M^~)` the action of `g ^ n` is invertible. -/
lemma isUnit_pow_tSec_mul (g h : R) (n : ℕ) :
    IsUnit (algebraMap R (Module.End R (tSec R M (g * h))) (g ^ n)) := by
  have hgh : IsUnit (algebraMap R (Module.End R (tSec R M (g * h))) (g * h)) :=
    IsLocalizedModule.Away.isUnit_algebraMap (tTo' R M g h) (g * h)
  have h3 : IsUnit (algebraMap R (Module.End R (tSec R M (g * h))) ((g * h) ^ n)) := by
    simpa only [map_pow] using hgh.pow n
  have h2 : IsUnit (algebraMap R (Module.End R (tSec R M (g * h))) (g ^ n) *
      algebraMap R (Module.End R (tSec R M (g * h))) (h ^ n)) := by
    rw [← map_mul, ← mul_pow]
    exact h3
  exact ((Algebra.commute_algebraMap_left (g ^ n)
    (algebraMap R (Module.End R (tSec R M (g * h))) (h ^ n))).isUnit_mul_iff.mp h2).1

/-- The action of `g ^ n` on `Γ(D g, M^~)` is invertible. -/
lemma isUnit_pow_tSec (g : R) (n : ℕ) :
    IsUnit (algebraMap R (Module.End R (tSec R M g)) (g ^ n)) := by
  have h := IsLocalizedModule.Away.isUnit_algebraMap (tTo R M g) g
  simpa only [map_pow] using h.pow n

/-- **Clearing denominators, surjectivity.** -/
theorem tRes_surj (g h : R) (z : tSec R M (g * h)) :
    ∃ (k : ℕ) (t : tSec R M g), tRes R M g h t = h ^ k • z := by
  obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj (r := g * h) (f := tTo' R M g h) z
  have hA := isUnit_pow_tSec (R := R) (M := M) g n
  have hB := isUnit_pow_tSec_mul (R := R) (M := M) g h n
  refine ⟨2 * n, (↑(hA.unit⁻¹) : Module.End R (tSec R M g)) (tTo R M g (h ^ n • y)), ?_⟩
  rw [tRes_unit_inv_smul (R := R) (M := M) (g := g) (h := h) (c := g ^ n) hA hB,
    ← LinearMap.comp_apply (f := tRes R M g h) (g := tTo R M g), tRes_comp_tTo, map_smul,
    ← hy]
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff R]
  simp only [smul_smul]
  congr 1
  rw [mul_pow, two_mul, pow_add]
  ac_rfl

/-- **Clearing denominators, vanishing.** -/
theorem tRes_ker (g h : R) (t : tSec R M g) (ht : tRes R M g h t = 0) :
    ∃ k : ℕ, h ^ k • t = 0 := by
  obtain ⟨m, y, hy⟩ := IsLocalizedModule.Away.surj (r := g) (f := tTo R M g) t
  have hy' : tTo' R M g h y = 0 := by
    rw [← tRes_comp_tTo (R := R) (M := M) g h, LinearMap.comp_apply, ← hy, map_smul, ht, smul_zero]
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (r := g * h) (f := tTo' R M g h)
    (x := y) (y := 0) (by rw [hy', map_zero])
  have hgn : g ^ n • (h ^ n • y) = 0 := by
    rw [smul_smul, ← mul_pow, hn, smul_zero]
  have hzero : g ^ (m + n) • (h ^ n • t) = 0 := by
    have h1 : tTo R M g (g ^ n • (h ^ n • y)) = 0 := by
      rw [hgn, map_zero]
    rw [map_smul, map_smul, ← hy] at h1
    rw [← h1]
    simp only [smul_smul]
    congr 1
    rw [pow_add]
    ac_rfl
  have hA := isUnit_pow_tSec (R := R) (M := M) g (m + n)
  have h2 : (↑(hA.unit⁻¹) : Module.End R (tSec R M g)) (g ^ (m + n) • (h ^ n • t)) =
      h ^ n • t := Module.End.isUnit_inv_apply_apply_of_isUnit hA (h ^ n • t)
  rw [hzero, map_zero] at h2
  exact ⟨n, h2.symm⟩

/-- The restriction to `D (g * h)` is the composite of the restriction to `D g ⊓ D h` with the
identification of the two opens (which are equal by `basicOpen_mul`). -/
lemma tRes_eq_comp (g h : R) :
    tRes R M g h =
      (((tildePresheaf M).map (eqToHom (tOpen_mul R g h)).op).hom).comp
        (((tildePresheaf M).map (homOfLE
          (inf_le_left : tOpen R g ⊓ tOpen R h ≤ tOpen R g)).op).hom) := by
  ext t
  have hmap : (tildePresheaf M).map
        (homOfLE (inf_le_left : tOpen R g ⊓ tOpen R h ≤ tOpen R g)).op ≫
      (tildePresheaf M).map (eqToHom (tOpen_mul R g h)).op =
      (tildePresheaf M).map (homOfLE (by rw [tOpen_mul]; exact inf_le_left)).op := by
    rw [← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have h2 := congrArg (fun (f : (tildePresheaf M).obj (op (tOpen R g)) ⟶
      (tildePresheaf M).obj (op (tOpen R (g * h)))) => f.hom t) hmap
  have h3 : ((tildePresheaf M).map
        (homOfLE (inf_le_left : tOpen R g ⊓ tOpen R h ≤ tOpen R g)).op ≫
      (tildePresheaf M).map (eqToHom (tOpen_mul R g h)).op).hom t =
      (((tildePresheaf M).map (eqToHom (tOpen_mul R g h)).op).hom)
        ((((tildePresheaf M).map (homOfLE
          (inf_le_left : tOpen R g ⊓ tOpen R h ≤ tOpen R g)).op).hom) t) := by
    rw [ModuleCat.hom_comp]
    rfl
  rw [h3] at h2
  exact h2

/-- **Clearing denominators for `M^~`.**  The restriction `Γ (D g, M^~) ⟶ Γ (D g ⊓ D h, M^~)`
exhibits the target as the localization of the source away from `h`. -/
theorem tilde_compLoc (h : R) : CompLoc (tildePresheaf M) h := by
  constructor
  · intro g z
    have hinj : Function.Injective
        (((tildePresheaf M).map (eqToHom (tOpen_mul R g h)).op).hom) :=
      (ConcreteCategory.bijective_of_isIso _).1
    obtain ⟨k, t, ht⟩ := tRes_surj (R := R) (M := M) g h
      (((tildePresheaf M).map (eqToHom (tOpen_mul R g h)).op).hom z)
    refine ⟨k, t, ?_⟩
    apply hinj
    rw [map_smul, ← ht, tRes_eq_comp]
    rfl
  · intro g t ht
    have h2 : tRes R M g h t =
        (((tildePresheaf M).map (eqToHom (tOpen_mul R g h)).op).hom)
          ((((tildePresheaf M).map (homOfLE
            (inf_le_left : tOpen R g ⊓ tOpen R h ≤ tOpen R g)).op).hom) t) := by
      rw [tRes_eq_comp]
      rfl
    have hzero : tRes R M g h t = 0 := by
      rw [h2, ht, map_zero]
    obtain ⟨k, hk⟩ := tRes_ker (R := R) (M := M) g h t hzero
    exact ⟨k, hk⟩

end Work.DSF1.Sheaf
