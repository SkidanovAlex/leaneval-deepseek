import Mathlib
import Submission.Work.Thom.ThomClass
import Submission.Work.Thom.MixedCup
import Submission.Work.Cohomology.cupNaturalH

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-!
# The Gysin sequence of the sphere bundle of a real vector bundle

Let `E → B` be a real bundle with a **Thom class** `T : Work.Thom.ThomClass Z n` (so `Z` is an
oriented rank-`n` bundle, `Submission/Work/Thom/ThomClass.lean`), let `S E = E∖0` be its sphere
bundle and `π : E → B`, `z : B → E` the projection and the zero section.

The long exact sequence of the pair `(E,E∖0)` is `Work.Thom.pairExact₁/₂/₃`.  Transporting it along
the Thom isomorphism `T.thomEquiv : H^k(B;ℤ) ≅ H^{k+n}(E,E∖0;ℤ)` and along the homotopy
equivalence `π` (whose inverse on cohomology is `z^*`,
`Work.Thom.bijective_CohMap_bundleProj`) gives the **Gysin sequence** of the sphere bundle

  `… → H^k(B) --∪e--> H^{k+n}(B) --π_S^*--> H^{k+n}(S E) --δ--> H^{k+1}(B) --∪e--> H^{k+n+1}(B) → …`

with

* `Work.Thom.gysinEuler T k : H^k(B;ℤ) → H^{k+n}(B;ℤ)` — the map `∪e`;

  **`Work.Thom.gysinEuler_eq_cupEuler`** identifies it with multiplication by the Euler class
  `T.eulerClass`, using `Work.Thom.mixedCup_relToAbs` and the naturality of the cup product;

* `Work.Thom.gysinπ Z k : H^k(B;ℤ) → H^k(S E;ℤ)` — the restriction of `π^*`;

* `Work.Thom.gysinδ T k : H^{k+n}(S E;ℤ) → H^{k+1}(B;ℤ)` — the transgression
  (`ThomClass.lean`), whose exactness is the remaining statement.

## Main results of this module

* `Work.Thom.pairRange_eq_ker₁/₂/₃` — the pair sequence in `range = ker` form;
* `Work.Thom.gysinEuler_eq_cupEuler` — `∪e` is multiplication by the Euler class;
* `Work.Thom.gysin_exact_at_base` — exactness of the Gysin sequence at `H^{k+n}(B;ℤ)`;
* `Work.Thom.gysin_exact_at_sphere` — exactness at `H^{k+n}(S E;ℤ)`, in the equivalent
  `ker (thom⁻¹ ∘ pairδ)` form (`Work.Thom.gysinδ_eq_zero_iff`).
-/

namespace Work.Thom

open CategoryTheory
open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-! ## The pair sequence in `range = ker` form -/

/-- The connecting map of the pair followed by the forgetful map is zero. -/
theorem pairδC_ker_le {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (pairδC A n).hom.range = (relToAbs ℤ A (n + 1)).hom.ker :=
  ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₁ A n)

/-- Exactness of the pair sequence at `H^n(X)`: `range (H^n(X,A) → H^n(X)) = ker (H^n(X) → H^n(A))`. -/
theorem pairRange_eq_ker₂ {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (relToAbs ℤ A n).hom.range = (restrCoh A ℤ n).hom.ker :=
  ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₂ A n)

/-- Exactness of the pair sequence at `H^n(A)`: `range (H^n(X) → H^n(A)) = ker (H^n(A) → H^{n+1}(X,A))`. -/
theorem pairRange_eq_ker₃ {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (restrCoh A ℤ n).hom.range = (pairδC A n).hom.ker :=
  ShortComplex.Exact.moduleCat_range_eq_ker (pairExact₃ A n)

/-! ## The map `∪e` is multiplication by the Euler class -/

/-- **The Gysin map `∪e` is multiplication by the Euler class.**  The composite defining
`Work.Thom.gysinEuler` — the Thom isomorphism, the forgetful map, and the pullback along the zero
section — is `x ↦ x ⌣ e(E)`. -/
theorem gysinEuler_eq_cupEuler {Z : RealBundle B F ι} {n : ℕ} (T : ThomClass Z n) (k : ℕ)
    (x : Coh ℤ k B) :
    gysinEuler T k x =
      Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of B)) k n x T.eulerClass := by
  have h1 : (CohMap (zeroSection Z) ℤ k).hom ((CohMap (bundleProj Z) ℤ k).hom x) = x :=
    LinearMap.congr_fun (CohMap_zeroSection_comp_bundleProj Z k) x
  have h2 : (thomMap Z n T.τ k) x
      = (mixedCupC ℤ (zeroComplement Z) k n) ((CohMap (bundleProj Z) ℤ k).hom x) T.τ :=
    thomMap_apply Z n T.τ k x
  show (CohMap (zeroSection Z) ℤ (k + n)).hom
      ((relToAbs ℤ (zeroComplement Z) (k + n)).hom ((thomMap Z n T.τ k) x)) = _
  rw [h2, mixedCup_relToAbs]
  rw [Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (zeroSection Z)) k n
    ((CohMap (bundleProj Z) ℤ k).hom x) ((relToAbs ℤ (zeroComplement Z) n).hom T.τ)]
  rw [h1]
  rfl

/-! ## Exactness of the Gysin sequence -/

/-- **Exactness of the Gysin sequence at the base term `H^{k+n}(B;ℤ)`**:
`range (∪e) = ker (π_S^*)`. -/
theorem gysin_exact_at_base {Z : RealBundle B F ι} {n : ℕ} (T : ThomClass Z n) (k : ℕ) :
    Set.range (gysinEuler T k)
      = {x : Coh ℤ (k + n) B | gysinπ Z (k + n) x = 0} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have h1 : (CohMap (bundleProj Z) ℤ (k + n)).hom (gysinEuler T k x)
        = (relToAbs ℤ (zeroComplement Z) (k + n)).hom (thomMap Z n T.τ k x) :=
      LinearMap.congr_fun (CohMap_bundleProj_comp_zeroSection Z (k + n))
        ((relToAbs ℤ (zeroComplement Z) (k + n)).hom (thomMap Z n T.τ k x))
    have h2 : (CohMap (subtypeMap (zeroComplement Z)) ℤ (k + n)).hom
        ((relToAbs ℤ (zeroComplement Z) (k + n)).hom (thomMap Z n T.τ k x)) = 0 := by
      have h := congrArg (fun f => ModuleCat.Hom.hom f)
        (relToAbs_comp_CohMap_subtype ℤ (zeroComplement Z) (k + n))
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact congrArg (fun g => g (thomMap Z n T.τ k x)) h
    show (CohMap (subtypeMap (zeroComplement Z)) ℤ (k + n)).hom
      ((CohMap (bundleProj Z) ℤ (k + n)).hom (gysinEuler T k x)) = 0
    rw [h1, h2]
  · intro hy
    have hre : (CohMap (subtypeMap (zeroComplement Z)) ℤ (k + n)).hom
        ((CohMap (bundleProj Z) ℤ (k + n)).hom y) = 0 := hy
    have hmem : (CohMap (bundleProj Z) ℤ (k + n)).hom y
        ∈ (relToAbs ℤ (zeroComplement Z) (k + n)).hom.range := by
      rw [pairRange_eq_ker₂]
      exact hre
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    obtain ⟨x, hx⟩ := (T.isThom k).2 w
    refine ⟨x, ?_⟩
    have hy1 : (CohMap (zeroSection Z) ℤ (k + n)).hom
        ((CohMap (bundleProj Z) ℤ (k + n)).hom y) = y :=
      LinearMap.congr_fun (CohMap_zeroSection_comp_bundleProj Z (k + n)) y
    calc gysinEuler T k x = (CohMap (zeroSection Z) ℤ (k + n)).hom
          ((relToAbs ℤ (zeroComplement Z) (k + n)).hom (thomMap Z n T.τ k x)) := rfl
      _ = (CohMap (zeroSection Z) ℤ (k + n)).hom
            ((relToAbs ℤ (zeroComplement Z) (k + n)).hom w) := by rw [← hx]
      _ = (CohMap (zeroSection Z) ℤ (k + n)).hom
            ((CohMap (bundleProj Z) ℤ (k + n)).hom y) := by rw [← hw]
      _ = y := hy1

/-- **Exactness of the Gysin sequence at the sphere-bundle term `H^{k+n}(S E;ℤ)`**, in the
equivalent form `range (π_S^*) = ker (pairδ)`: since the transgression
`Work.Thom.gysinδ T k` is the inverse Thom isomorphism applied to the connecting map `pairδ` of the
pair, its kernel is that of `pairδ`. -/
theorem gysin_exact_at_sphere {Z : RealBundle B F ι} {n : ℕ} (T : ThomClass Z n) (k : ℕ) :
    Set.range (gysinπ Z (k + n))
      = {y : Coh ℤ (k + n) (zeroComplement Z)
          | (pairδC (zeroComplement Z) (k + n)).hom y = 0} := by
  have h1 : Set.range (gysinπ Z (k + n))
      = Set.range ((CohMap (subtypeMap (zeroComplement Z)) ℤ (k + n)).hom) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨(CohMap (bundleProj Z) ℤ (k + n)).hom x, rfl⟩
    · rintro y ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := (bijective_CohMap_bundleProj Z (k + n)).2 z
      exact ⟨x, rfl⟩
  rw [h1]
  ext y
  rw [Set.mem_range, Set.mem_setOf_eq, ← LinearMap.mem_ker,
    ← pairRange_eq_ker₃ (zeroComplement Z) (k + n), LinearMap.mem_range]

/-! ## The transgression, and exactness of the Gysin sequence at `H^{k+1}(B;ℤ)`

The transgression `Work.Thom.gysinδ` is *defined* (`Submission/Work/Thom/ThomClass.lean`) as the
inverse Thom isomorphism applied to the connecting map `pairδ` of the pair `(E,E∖0)`.  The one
technical point is the **degree cast**: `gysinδ` must move from `H^{(k+n)+1}(E,E∖0)` to
`H^{(k+1)+n}(E,E∖0)`, and `(k+n)+1` and `(k+1)+n` are equal (`Nat.add_right_comm`) but not
definitionally equal.  The next lemmas handle that cast:

* `Work.Thom.cast_apply_lm` — applying a transported linear map is transporting the value;
* `Work.Thom.cast_zero`, `Work.Thom.cast_eq_zero` — the cast preserves (and reflects) zero;
* `Work.Thom.cast_symm_cast` — the two casts are inverse to one another;
* `Work.Thom.relToAbs_cast` — the forgetful map of the pair commutes with the cast.

With these, `Work.Thom.gysinδ_apply` is the defining property of the transgression,
`Work.Thom.gysinδ_eq_zero_iff` says that its kernel is the kernel of the connecting map, and
**`Work.Thom.gysin_exact_at_cobase`** completes the Gysin sequence:

  `Set.range (gysinδ T k) = {x | gysinEuler T (k+1) x = 0}`.
-/

theorem cast_apply_lm {A : Type} [AddCommMonoid A] [Module ℤ A]
    (M : ℕ → Type) [∀ k, AddCommMonoid (M k)] [∀ k, Module ℤ (M k)]
    {m m' : ℕ} (h : m = m') (f : A →ₗ[ℤ] M m) (y : A) :
    (Eq.mp (congrArg (fun k : ℕ => (A →ₗ[ℤ] M k)) h) f) y = Eq.mp (congrArg M h) (f y) := by
  cases h
  rfl

theorem cast_zero {M : ℕ → Type} [∀ k, Zero (M k)] {m m' : ℕ} (h : m = m') :
    Eq.mp (congrArg M h) (0 : M m) = 0 := by
  subst h
  rfl

theorem cast_eq_zero {M : ℕ → Type} [∀ k, Zero (M k)] {m m' : ℕ} (h : m = m') (x : M m) :
    Eq.mp (congrArg M h) x = 0 ↔ x = 0 := by
  subst h
  rfl

theorem cast_symm_cast {M : ℕ → Type} {m m' : ℕ} (h : m = m') (x : M m') :
    Eq.mp (congrArg M h) (Eq.mp (congrArg M h.symm) x) = x := by
  subst h
  rfl

theorem relToAbs_cast {X : Type} [TopologicalSpace X] (A : Set X) {m m' : ℕ} (h : m = m')
    (x : RelCoh ℤ m X A) :
    (relToAbs ℤ A m').hom (Eq.mp (congrArg (fun k : ℕ => (RelCoh ℤ k X A : Type)) h) x)
      = Eq.mp (congrArg (fun k : ℕ => (Coh ℤ k X : Type)) h) ((relToAbs ℤ A m).hom x) := by
  subst h
  rfl

theorem gysinδ_apply {Z : RealBundle B F ι} {n : ℕ} (T : ThomClass Z n) (k : ℕ)
    (y : Coh ℤ (k + n) (zeroComplement Z)) :
    gysinδ T k y = (T.thomEquiv (k + 1)).symm
      (Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1))
        ((pairδC (zeroComplement Z) (k + n)).hom y)) := by
  rw [gysinδ, LinearMap.comp_apply]
  exact congrArg _ (cast_apply_lm (fun m => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1)
    _ y)

theorem gysinδ_eq_zero_iff {Z : RealBundle B F ι} {n : ℕ} (T : ThomClass Z n) (k : ℕ)
    (y : Coh ℤ (k + n) (zeroComplement Z)) :
    gysinδ T k y = 0 ↔ (pairδC (zeroComplement Z) (k + n)).hom y = 0 := by
  rw [gysinδ_apply T k y]
  rw [show (T.thomEquiv (k + 1)).symm
      (Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1))
        ((pairδC (zeroComplement Z) (k + n)).hom y)) = 0
      ↔ Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1))
        ((pairδC (zeroComplement Z) (k + n)).hom y) = 0 from
    LinearEquiv.map_eq_zero_iff (T.thomEquiv (k + 1)).symm]
  exact cast_eq_zero (M := fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1) _

theorem gysin_exact_at_cobase {Z : RealBundle B F ι} {n : ℕ} (T : ThomClass Z n) (k : ℕ) :
    Set.range (gysinδ T k) = {x : Coh ℤ (k + 1) B | gysinEuler T (k + 1) x = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have h0 : (relToAbs ℤ (zeroComplement Z) ((k + n) + 1)).hom
        ((pairδC (zeroComplement Z) (k + n)).hom y) = 0 := by
      have hmem : (pairδC (zeroComplement Z) (k + n)).hom y
          ∈ (relToAbs ℤ (zeroComplement Z) ((k + n) + 1)).hom.ker := by
        rw [← pairδC_ker_le (zeroComplement Z) (k + n)]
        exact ⟨y, rfl⟩
      exact LinearMap.mem_ker.mp hmem
    have hcast := relToAbs_cast (zeroComplement Z) (Nat.add_right_comm k n 1)
      ((pairδC (zeroComplement Z) (k + n)).hom y)
    rw [h0, cast_zero (M := fun m : ℕ => (Coh ℤ m Z.TotalSpace : Type))
      (Nat.add_right_comm k n 1)] at hcast
    show gysinEuler T (k + 1) (gysinδ T k y) = 0
    rw [gysinδ_apply T k y]
    show (CohMap (zeroSection Z) ℤ (k + 1 + n)).hom
      ((relToAbs ℤ (zeroComplement Z) (k + 1 + n)).hom
        (thomMap Z n T.τ (k + 1) ((T.thomEquiv (k + 1)).symm
          (Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1))
            ((pairδC (zeroComplement Z) (k + n)).hom y))))) = 0
    rw [show thomMap Z n T.τ (k + 1) ((T.thomEquiv (k + 1)).symm
        (Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1))
          ((pairδC (zeroComplement Z) (k + n)).hom y)))
      = Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1))
          ((pairδC (zeroComplement Z) (k + n)).hom y) from
      LinearEquiv.apply_symm_apply (T.thomEquiv (k + 1)) _]
    rw [hcast, map_zero]
  · intro hx
    have hz : (relToAbs ℤ (zeroComplement Z) (k + 1 + n)).hom
        (thomMap Z n T.τ (k + 1) x) = 0 := by
      have hx' : (CohMap (zeroSection Z) ℤ (k + 1 + n)).hom
          ((relToAbs ℤ (zeroComplement Z) (k + 1 + n)).hom (thomMap Z n T.τ (k + 1) x)) = 0 := hx
      have hleft : (CohMap (bundleProj Z) ℤ (k + 1 + n)).hom
          ((CohMap (zeroSection Z) ℤ (k + 1 + n)).hom
            ((relToAbs ℤ (zeroComplement Z) (k + 1 + n)).hom (thomMap Z n T.τ (k + 1) x)))
          = (relToAbs ℤ (zeroComplement Z) (k + 1 + n)).hom (thomMap Z n T.τ (k + 1) x) :=
        LinearMap.congr_fun (CohMap_bundleProj_comp_zeroSection Z (k + 1 + n))
          ((relToAbs ℤ (zeroComplement Z) (k + 1 + n)).hom (thomMap Z n T.τ (k + 1) x))
      rw [hx', map_zero] at hleft
      exact hleft.symm
    set w : OpenThom Z ((k + n) + 1) :=
      Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1)).symm
        (thomMap Z n T.τ (k + 1) x) with hw
    have hw' : Eq.mp (congrArg (fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1)) w
        = thomMap Z n T.τ (k + 1) x :=
      cast_symm_cast (M := fun m : ℕ => (OpenThom Z m : Type)) (Nat.add_right_comm k n 1)
        (thomMap Z n T.τ (k + 1) x)
    have hw0 : (relToAbs ℤ (zeroComplement Z) ((k + n) + 1)).hom w = 0 := by
      have h1 := relToAbs_cast (zeroComplement Z) (Nat.add_right_comm k n 1) w
      rw [hw', hz] at h1
      exact (cast_eq_zero (M := fun m : ℕ => (Coh ℤ m Z.TotalSpace : Type))
        (Nat.add_right_comm k n 1) _).mp h1.symm
    have hmem : w ∈ (pairδC (zeroComplement Z) (k + n)).hom.range := by
      rw [pairδC_ker_le (zeroComplement Z) (k + n)]
      exact LinearMap.mem_ker.mpr hw0
    obtain ⟨y, hy⟩ := hmem
    refine ⟨y, ?_⟩
    rw [gysinδ_apply T k y, hy, hw']
    exact LinearEquiv.symm_apply_apply (T.thomEquiv (k + 1)) x


end

end Work.Thom
