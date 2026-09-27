/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The even-dimensional part of Adams' theorem

For even `n ≥ 2` the sphere `Sⁿ` is not an H-space.  This file proves the classical cup-product
contradiction: an H-space structure `μ` on `Sⁿ` induces a multiplication
`m : singSph n ⊗ singSph n ⟶ singSph n` on the singular complex, the two unit laws show
`m^*(x) = pr₁^*(x) + pr₂^*(x)` for `x ∈ Hⁿ(Sⁿ; ℚ)` with `x ≠ 0` (using the hypothesis `hdim`),
while naturality of the cup product together with `H^{2n}(Sⁿ) = 0` (`htop`) gives
`0 = m^*(x ⌣ x) = (m^*x)² = 2 · pr₁^*x ⌣ pr₂^*x`,
contradicting the non-vanishing of the cross product over `ℚ`.
-/
import Mathlib
import Submission.Work.Sphere.Suspension
import Submission.Work.Cohomology.H_map_comp
import Submission.Work.Cohomology.H_map_cupOf
import Submission.Work.Cohomology.H_cup_comm
import Submission.Work.Cohomology.H_cup_cross_ne_zero
import Submission.Work.Cohomology.H_subsingleton_of_contractible
import Submission.Work.Cohomology.H_map_homotopic
import Submission.Work.Cohomology.H_cupOf_mk
import Submission.Work.Cohomology.H_cupOf_add_left
import Submission.Work.Cohomology.H_cupOf_add_right

open CategoryTheory MonoidalCategory Simplicial Opposite
open Submission.Cohomology

namespace Work.HSpace

set_option maxHeartbeats 1000000

noncomputable section

variable {n : ℕ}

/-! ## The multiplication induced on the singular complex -/

/-- The multiplication `Sⁿ × Sⁿ → Sⁿ` of an H-space structure, as a morphism in `TopCat`. -/
def mult (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    Submission.Sphere.Sph n ⊗ Submission.Sphere.Sph n ⟶ Submission.Sphere.Sph n :=
  TopCat.ofHom μ.hmul

/-- The induced multiplication `singSph n ⊗ singSph n ⟶ singSph n` on the singular complex. -/
def mulMap (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    Submission.Sphere.singSph n ⊗ Submission.Sphere.singSph n ⟶ Submission.Sphere.singSph n :=
  Functor.LaxMonoidal.μ TopCat.toSSet (Submission.Sphere.Sph n) (Submission.Sphere.Sph n) ≫
    TopCat.toSSet.map (mult μ)

/-- The point `μ.e` as a `0`-simplex of the singular complex. -/
def eSimplex (μ : HSpace (↥(Submission.Sphere.Sph n))) : (Submission.Sphere.singSph n) _⦋0⦌ :=
  TopCat.toSSetObj₀Equiv.symm μ.e

/-- The map `x ↦ (x, e)` on the singular complex. -/
def sOne (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    Submission.Sphere.singSph n ⟶ Submission.Sphere.singSph n ⊗ Submission.Sphere.singSph n :=
  CartesianMonoidalCategory.lift (𝟙 _) (SSet.const (eSimplex μ))

/-- The map `x ↦ (e, x)` on the singular complex. -/
def sTwo (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    Submission.Sphere.singSph n ⟶ Submission.Sphere.singSph n ⊗ Submission.Sphere.singSph n :=
  CartesianMonoidalCategory.lift (SSet.const (eSimplex μ)) (𝟙 _)

/-- The map `x ↦ μ (x, e)` on `Sⁿ`, as a morphism in `TopCat`. -/
def gOne (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    Submission.Sphere.Sph n ⟶ Submission.Sphere.Sph n :=
  CartesianMonoidalCategory.lift (𝟙 _) (TopCat.const μ.e) ≫ mult μ

/-- The map `x ↦ μ (e, x)` on `Sⁿ`, as a morphism in `TopCat`. -/
def gTwo (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    Submission.Sphere.Sph n ⟶ Submission.Sphere.Sph n :=
  CartesianMonoidalCategory.lift (TopCat.const μ.e) (𝟙 _) ≫ mult μ

/-! ## Computing the underlying continuous maps -/

/-- The underlying continuous map of the canonical map into a product. -/
lemma lift_hom {X Y Z : TopCat} (f : X ⟶ Y) (g : X ⟶ Z) :
    (CartesianMonoidalCategory.lift f g).hom = f.hom.prodMk g.hom := by
  apply ContinuousMap.ext
  intro x
  have key : ((ConcreteCategory.hom (CartesianMonoidalCategory.lift f g)) x : ↥Y × ↥Z)
      = (f.hom.prodMk g.hom) x := by
    refine Prod.ext ?_ ?_
    · have h1 := ConcreteCategory.congr_hom (CartesianMonoidalCategory.lift_fst f g) x
      simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h1
      rw [show (SemiCartesianMonoidalCategory.fst Y Z)
            ((ConcreteCategory.hom (CartesianMonoidalCategory.lift f g)) x)
            = ((ConcreteCategory.hom (CartesianMonoidalCategory.lift f g)) x : ↥Y × ↥Z).1
              from rfl] at h1
      simpa [ContinuousMap.prod_eval] using h1
    · have h2 := ConcreteCategory.congr_hom (CartesianMonoidalCategory.lift_snd f g) x
      simp only [CategoryTheory.comp_apply] at h2
      rw [show (SemiCartesianMonoidalCategory.snd Y Z)
            ((ConcreteCategory.hom (CartesianMonoidalCategory.lift f g)) x)
            = ((ConcreteCategory.hom (CartesianMonoidalCategory.lift f g)) x : ↥Y × ↥Z).2
              from rfl] at h2
      simpa [ContinuousMap.prod_eval] using h2
  exact key

/-! ## The two unit laws -/

/-- `(x ↦ (x, e)) ≫ m` is the map `x ↦ μ (x, e)`; the first unit law makes it homotopic to the
identity. -/
lemma sOne_mulMap (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    sOne μ ≫ mulMap μ = TopCat.toSSet.map (gOne μ) := by
  rw [sOne, eSimplex, mulMap, gOne, ← Category.assoc]
  rw [show (𝟙 (Submission.Sphere.singSph n))
        = TopCat.toSSet.map (𝟙 (Submission.Sphere.Sph n)) from by simp,
      ← TopCat.toSSet_map_const]
  rw [Functor.Monoidal.lift_μ]
  rw [← Functor.map_comp]

/-- `(x ↦ (e, x)) ≫ m` is the map `x ↦ μ (e, x)`; the second unit law makes it homotopic to the
identity. -/
lemma sTwo_mulMap (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    sTwo μ ≫ mulMap μ = TopCat.toSSet.map (gTwo μ) := by
  rw [sTwo, eSimplex, mulMap, gTwo, ← Category.assoc]
  rw [show (𝟙 (Submission.Sphere.singSph n))
        = TopCat.toSSet.map (𝟙 (Submission.Sphere.Sph n)) from by simp,
      ← TopCat.toSSet_map_const]
  rw [Functor.Monoidal.lift_μ]
  rw [← Functor.map_comp]

/-- The first unit homotopy, transported to the singular complex. -/
def homotopy_sOne (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    TopCat.Homotopy (gOne μ) (𝟙 (Submission.Sphere.Sph n)) := by
  have hg : ConcreteCategory.hom (gOne μ)
      = μ.hmul.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ μ.e)) := by
    rw [gOne]
    change (TopCat.ofHom μ.hmul).hom.comp
      (CartesianMonoidalCategory.lift (𝟙 (Submission.Sphere.Sph n)) (TopCat.const μ.e)).hom = _
    rw [lift_hom]
    rfl
  convert μ.hmulE.toHomotopy using 1
  all_goals rfl

/-- The second unit homotopy, transported to the singular complex. -/
def homotopy_sTwo (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    TopCat.Homotopy (gTwo μ) (𝟙 (Submission.Sphere.Sph n)) := by
  have hg : ConcreteCategory.hom (gTwo μ)
      = μ.hmul.comp ((ContinuousMap.const _ μ.e).prodMk (ContinuousMap.id _)) := by
    rw [gTwo]
    change (TopCat.ofHom μ.hmul).hom.comp
      (CartesianMonoidalCategory.lift (TopCat.const μ.e) (𝟙 (Submission.Sphere.Sph n))).hom = _
    rw [lift_hom]
    rfl
  convert μ.eHmul.toHomotopy using 1
  all_goals rfl

/-- The simplicial homotopy `(x ↦ (x,e)) ≫ m ≃ 1`. -/
def SSetHomotopy_sOne (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    SSet.Homotopy (sOne μ ≫ mulMap μ) (𝟙 (Submission.Sphere.singSph n)) := by
  rw [sOne_mulMap]
  simpa using TopCat.Homotopy.toSSet (homotopy_sOne μ)

/-- The simplicial homotopy `(x ↦ (e,x)) ≫ m ≃ 1`. -/
def SSetHomotopy_sTwo (μ : HSpace (↥(Submission.Sphere.Sph n))) :
    SSet.Homotopy (sTwo μ ≫ mulMap μ) (𝟙 (Submission.Sphere.singSph n)) := by
  rw [sTwo_mulMap]
  simpa using TopCat.Homotopy.toSSet (homotopy_sTwo μ)


/-! ## The cohomological unit laws -/

open Submission.Cohomology in
/-- Functoriality of `H.map` applied pointwise. -/
lemma H_map_comp_apply {S T U : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) (g : T ⟶ U)
    (k : ℕ) (y : H U R k) : H.map R f k (H.map R g k y) = H.map R (f ≫ g) k y :=
  (Work.Cohomology.H_map_comp f g k y).symm

/-- Pullback along a constant simplicial map vanishes in positive degrees. -/
theorem H_map_const_eq_zero {S : SSet.{0}} (e : S _⦋0⦌) {m : ℕ} (hm : 0 < m) :
    H.map ℚ (SSet.const (X := S) e) m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set π : S ⟶ Work.Cohomology.Pt := SSet.const (Work.Cohomology.ptSimplex 0) with hπ
  set v : Work.Cohomology.Pt ⟶ S := SSet.const e with hv
  have hcv : π ≫ v = SSet.const e := SSet.comp_const π e
  haveI : Subsingleton (H Work.Cohomology.Pt ℚ (k + 1)) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
    rintro ⟨u, hu⟩
    rw [boundariesInCycles, Submodule.mem_comap]
    exact Work.Cohomology.cycles_le_boundaries_stdSimplex_zero ℚ k hu
  apply LinearMap.ext
  intro y
  rw [← hcv, Work.Cohomology.H_map_comp]
  have hzero : H.map ℚ v (k + 1) y = 0 := Subsingleton.elim _ _
  simp [hzero]

/-- The unit law at the level of cohomology, first version. -/
theorem H_map_sOne_mulMap (μ : HSpace (↥(Submission.Sphere.Sph n)))
    (y : H (Submission.Sphere.singSph n) ℚ n) :
    H.map ℚ (sOne μ) n (H.map ℚ (mulMap μ) n y) = y := by
  rw [H_map_comp_apply]
  have h := LinearMap.congr_fun (Work.Cohomology.H_map_homotopic (SSetHomotopy_sOne μ) n) y
  simpa [H.map_id] using h

/-- The unit law at the level of cohomology, second version. -/
theorem H_map_sTwo_mulMap (μ : HSpace (↥(Submission.Sphere.Sph n)))
    (y : H (Submission.Sphere.singSph n) ℚ n) :
    H.map ℚ (sTwo μ) n (H.map ℚ (mulMap μ) n y) = y := by
  rw [H_map_comp_apply]
  have h := LinearMap.congr_fun (Work.Cohomology.H_map_homotopic (SSetHomotopy_sTwo μ) n) y
  simpa [H.map_id] using h

/-- `sOne` composed with the first projection is the identity on cohomology. -/
theorem H_map_sOne_fst (μ : HSpace (↥(Submission.Sphere.Sph n)))
    (y : H (Submission.Sphere.singSph n) ℚ n) :
    H.map ℚ (sOne μ) n
      (H.map ℚ (SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
        (Submission.Sphere.singSph n)) n y) = y := by
  rw [sOne, H_map_comp_apply, CartesianMonoidalCategory.lift_fst, H.map_id]
  rfl

/-- `sOne` composed with the second projection is the constant map, which vanishes on
positive-degree cohomology. -/
theorem H_map_sOne_snd (μ : HSpace (↥(Submission.Sphere.Sph n))) (hn : 0 < n)
    (y : H (Submission.Sphere.singSph n) ℚ n) :
    H.map ℚ (sOne μ) n
      (H.map ℚ (SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
        (Submission.Sphere.singSph n)) n y) = 0 := by
  rw [sOne, H_map_comp_apply, CartesianMonoidalCategory.lift_snd,
    H_map_const_eq_zero (eSimplex μ) hn]
  rfl

/-- The two-fold cup product of a nonzero class with itself vanishes in degree `2n`, since the
cohomology of `Sⁿ` vanishes there. -/
lemma subsingleton_H_two_mul (htop : Subsingleton (H (Submission.Sphere.singSph n) ℚ (2 * n))) :
    Subsingleton (H (Submission.Sphere.singSph n) ℚ (n + n)) := by
  rw [← Nat.two_mul]
  exact htop


/-- `sTwo` composed with the first projection is the constant map. -/
theorem H_map_sTwo_fst (μ : HSpace (↥(Submission.Sphere.Sph n))) (hn : 0 < n)
    (y : H (Submission.Sphere.singSph n) ℚ n) :
    H.map ℚ (sTwo μ) n
      (H.map ℚ (SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
        (Submission.Sphere.singSph n)) n y) = 0 := by
  rw [sTwo, H_map_comp_apply, CartesianMonoidalCategory.lift_fst,
    H_map_const_eq_zero (eSimplex μ) hn]
  rfl

/-- `sTwo` composed with the second projection is the identity on cohomology. -/
theorem H_map_sTwo_snd (μ : HSpace (↥(Submission.Sphere.Sph n)))
    (y : H (Submission.Sphere.singSph n) ℚ n) :
    H.map ℚ (sTwo μ) n
      (H.map ℚ (SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
        (Submission.Sphere.singSph n)) n y) = y := by
  rw [sTwo, H_map_comp_apply, CartesianMonoidalCategory.lift_snd, H.map_id]
  rfl

/-- Graded commutativity of the cup product in a fixed even degree, in `cupOf` form. -/
lemma H_cupOf_comm_of_even {S : SSet.{0}} {n : ℕ} (heven : Even n) (u v : H S ℚ n) :
    H.cupOf (rfl : n + n = n + n) v u = H.cupOf (rfl : n + n = n + n) u v := by
  have h := Work.Cohomology.H_cup_comm (S := S) (R := ℚ) n u v
  rw [Even.neg_one_pow (heven.mul_right n), one_smul] at h
  exact h

/-! ## A compatibility alias for the range of a linear map

The delegated statement is phrased with `Submodule.range`.  That name is not a declaration in the
present revision of Mathlib (the range of a linear map is `LinearMap.range`), so we provide it as
an abbreviation, keeping the requested statement text intact. -/

namespace Submodule

/-- The range of a linear map, under its historical name `Submodule.range`. -/
abbrev range {R R₂ M M₂ : Type*} [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R₂ M₂] {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
    (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=
  LinearMap.range f

end Submodule

/-! ## The main theorem -/

theorem no_hSpace_sph_even (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (hdim : Submodule.range (Submission.Cohomology.H.map ℚ
          (CategoryTheory.SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
            (Submission.Sphere.singSph n)) n)
        ⊔ Submodule.range (Submission.Cohomology.H.map ℚ
          (CategoryTheory.SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
            (Submission.Sphere.singSph n)) n) = ⊤)
    (htop : Subsingleton (Submission.Cohomology.H (Submission.Sphere.singSph n) ℚ (2 * n)))
    (x : Submission.Cohomology.H (Submission.Sphere.singSph n) ℚ n) (hx : x ≠ 0)
    (μ : HSpace (↥(Submission.Sphere.Sph n))) : False := by
  have hnpos : 0 < n := by omega
  have hP : H.cupOf (rfl : n + n = n + n) x x = 0 :=
    (subsingleton_H_two_mul (n := n) htop).elim _ _
  -- (1) The class `m^*x` lies in the range of `pr₁^*` plus the range of `pr₂^*`.
  have hmem : H.map ℚ (mulMap μ) n x ∈
      Submodule.range (H.map ℚ (SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
        (Submission.Sphere.singSph n)) n)
      ⊔ Submodule.range (H.map ℚ (SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
        (Submission.Sphere.singSph n)) n) := by
    rw [hdim]
    exact Submodule.mem_top
  rw [Submodule.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  rw [LinearMap.mem_range] at hy hz
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := hz
  -- (2) The two unit laws force `a = x` and `b = x`.
  have hax : a = x := by
    have h1 := H_map_sOne_mulMap (n := n) μ x
    have h2 : H.map ℚ (sOne μ) n
        (H.map ℚ (SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
            (Submission.Sphere.singSph n)) n a
          + H.map ℚ (SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
            (Submission.Sphere.singSph n)) n b) = a := by
      rw [map_add, H_map_sOne_fst (n := n) μ a, H_map_sOne_snd (n := n) μ hnpos b, add_zero]
    rw [← hyz] at h1
    rw [h2] at h1
    exact h1
  have hbx : b = x := by
    have h1 := H_map_sTwo_mulMap (n := n) μ x
    have h2 : H.map ℚ (sTwo μ) n
        (H.map ℚ (SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
            (Submission.Sphere.singSph n)) n a
          + H.map ℚ (SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
            (Submission.Sphere.singSph n)) n b) = b := by
      rw [map_add, H_map_sTwo_fst (n := n) μ hnpos a, H_map_sTwo_snd (n := n) μ b, zero_add]
    rw [← hyz] at h1
    rw [h2] at h1
    exact h1
  -- Abbreviate `pr₁^*x` and `pr₂^*x` so that the cup-product algebra below is cheap.
  set A : H (Submission.Sphere.singSph n ⊗ Submission.Sphere.singSph n) ℚ n :=
    H.map ℚ (SemiCartesianMonoidalCategory.fst (Submission.Sphere.singSph n)
      (Submission.Sphere.singSph n)) n x with hA
  set B : H (Submission.Sphere.singSph n ⊗ Submission.Sphere.singSph n) ℚ n :=
    H.map ℚ (SemiCartesianMonoidalCategory.snd (Submission.Sphere.singSph n)
      (Submission.Sphere.singSph n)) n x with hB
  -- (3) `m^*x = pr₁^*x + pr₂^*x`.
  have hmx : H.map ℚ (mulMap μ) n x = A + B := by
    rw [← hyz, hax, hbx, ← hA, ← hB]
  -- (4) `m^*` is a ring homomorphism and `H^{2n}(Sⁿ) = 0`.
  have hsq : H.cupOf (rfl : n + n = n + n)
      (H.map ℚ (mulMap μ) n x) (H.map ℚ (mulMap μ) n x) = 0 := by
    have h := Work.Cohomology.H_map_cupOf (mulMap μ) (rfl : n + n = n + n) x x
    rw [hP, map_zero] at h
    exact h.symm
  -- (5) Expansion of the square using `x ⌣ x = 0` and graded commutativity.
  have hAA : H.cupOf (rfl : n + n = n + n) A A = 0 := by
    have h := Work.Cohomology.H_map_cupOf (SemiCartesianMonoidalCategory.fst
        (Submission.Sphere.singSph n) (Submission.Sphere.singSph n))
        (rfl : n + n = n + n) x x
    rw [hP, map_zero] at h
    rw [← hA] at h
    exact h.symm
  have hBB : H.cupOf (rfl : n + n = n + n) B B = 0 := by
    have h := Work.Cohomology.H_map_cupOf (SemiCartesianMonoidalCategory.snd
        (Submission.Sphere.singSph n) (Submission.Sphere.singSph n))
        (rfl : n + n = n + n) x x
    rw [hP, map_zero] at h
    rw [← hB] at h
    exact h.symm
  have hBA : H.cupOf (rfl : n + n = n + n) B A = H.cupOf (rfl : n + n = n + n) A B :=
    (H_cupOf_comm_of_even (S := Submission.Sphere.singSph n ⊗ Submission.Sphere.singSph n)
      (n := n) heven B A).symm
  have hexp : H.cupOf (rfl : n + n = n + n) (A + B) (A + B)
      = (2 : ℚ) • H.cupOf (rfl : n + n = n + n) A B := by
    simp only [Work.Cohomology.H_cupOf_add_left, Work.Cohomology.H_cupOf_add_right,
      hAA, hBB, hBA, zero_add, add_zero, two_smul]
  have hsq' : H.cupOf (rfl : n + n = n + n) (A + B) (A + B) = 0 := by
    rw [← hmx]
    exact hsq
  -- (6) Over `ℚ` the factor `2` is invertible, so the cross product must vanish.
  have hp : H.cupOf (rfl : n + n = n + n) A B = 0 := by
    have h2 : (2 : ℚ) • H.cupOf (rfl : n + n = n + n) A B = 0 := by
      rw [← hexp]
      exact hsq'
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  have hne := Work.Cohomology.H_cup_cross_ne_zero x x hx hx
  rw [← hA, ← hB] at hne
  exact hne hp

end

end Work.HSpace
