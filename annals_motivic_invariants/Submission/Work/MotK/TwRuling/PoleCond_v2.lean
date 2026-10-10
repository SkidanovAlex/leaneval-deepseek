import Mathlib
import Submission.Work.MotC2.PoleCond
import Submission.Work.MotC2.CoordPreserved
import Submission.Work.MotC2.Places
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pole conditions at infinity for a cross-curve isomorphism

`Work.MotC2.PoleCond` proves that if an `L`-algebra automorphism `Θ` of `L(E)` maps the local ring
`infPlace E` of the point at infinity onto itself, then `Θ x · w²` and `Θ y · w³` are regular at
`O` (`x = genX E`, `y = genY E`, `w = infW E = y/x²`).

Here we need the *cross-curve* version: `E, E'` are two elliptic Weierstrass curves over `L`,
`Θ : L(E) ≃ₐ[L] L(E')` and `hO : Subalgebra.map Θ.toAlgHom (infPlace E) = infPlace E'`; the
conclusion is that `Θ x · w'²` and `Θ y · w'³` are regular at the point at infinity `O'` of `E'`,
where now `w' = infW E'` is the uniformizer of the *target* curve.

## The argument

Write `w = infW E` and `w' = infW E'`.  The two key inputs are

* `x·w²` and `y·w³` lie in `infPlace E` (`genX_mul_infW_sq`, `genY_mul_infW_cube`), so their
  `Θ`-images lie in `infPlace E'`;
* `w'` is **not a unit** of the local ring `↥(infPlace E')`: if `w'·h = 1` with `h ∈ infPlace E'`,
  write `h = a/b` with `a, b` in the chart ring and `b ∉ ⟨1/x, y/x²⟩`; then
  `b = w'·a` lies in the ideal `⟨1/x, y/x²⟩`, hence `b` lies in the maximal ideal after all,
  a contradiction (`infPlace_mem_iff`, `mem_infIdealR_iff`).

Applying the dichotomy `Work.MotC2.infPlace_dichotomy` to `Θ⁻¹(w') ∈ infPlace E` — which is a
non-unit because `Θ` carries units to units and `w'` is not a unit — produces `g ∈ infPlace E` with
`Θ⁻¹(w') = w·g`, i.e. `w' = Θ(w)·Θ(g)` with `Θ(g) ∈ infPlace E'`.  Hence

`Θ(x)·w'² = Θ(x·w²)·(Θ g)²`,   `Θ(y)·w'³ = Θ(y·w³)·(Θ g)³`,

and both right hand sides are products of elements of `infPlace E'`.  (No division is involved, so
the argument is also valid when `x`, `y` or `w` happen to vanish.)

## Tags

elliptic curve, function field, place at infinity, pole order
-/

namespace Work.MotK.TwRuling

open Work.MotC2

/-- The uniformizer `w = y/x²` of the point at infinity is regular at `O`. -/
private lemma infW_mem_infPlace_aux {L : Type*} [Field L] (E : WeierstrassCurve L) :
    infW E ∈ infPlace E :=
  PoleAux.mem_infPlace_of_mem E ⟨infW E, PoleAux.infW_mem_infCoordRing E⟩

/-- `u = 1/x` is regular at the point at infinity. -/
private lemma infU_mem_infPlace_aux {L : Type*} [Field L] (E : WeierstrassCurve L) :
    infU E ∈ infPlace E :=
  PoleAux.mem_infPlace_of_mem E ⟨infU E, PoleAux.infU_mem_infCoordRing E⟩

/-- `x·w²` is a chart function, hence regular at the point at infinity. -/
private lemma genX_infW_sq_mem {L : Type*} [Field L] (E : WeierstrassCurve L) :
    genX E * (infW E) ^ 2 ∈ infPlace E := by
  have hu : infU E ∈ infPlace E := infU_mem_infPlace_aux E
  have hw : infW E ∈ infPlace E := infW_mem_infPlace_aux E
  rw [genX_mul_infW_sq]
  exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _ (Subalgebra.add_mem _
    (Subalgebra.one_mem _) (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hu))
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ hu 2)))
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ hu 3)))
    (Subalgebra.mul_mem _ (Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hu)) hw)

/-- `y·w³ = (x·w²)²` is regular at the point at infinity. -/
private lemma genY_infW_cube_mem {L : Type*} [Field L] (E : WeierstrassCurve L) :
    genY E * (infW E) ^ 3 ∈ infPlace E := by
  rw [genY_mul_infW_cube]
  exact pow_mem (genX_infW_sq_mem E) 2

/-- **`w = y/x²` generates the maximal ideal of the local ring at infinity.**  Equivalently, `w` is
not a unit of `↥(infPlace E)`: if `w·h = 1` with `h ∈ infPlace E`, writing `h = a/b` with `b`
outside the maximal ideal `⟨1/x, y/x²⟩` of the chart ring gives `b = w·a ∈ ⟨1/x, y/x²⟩`, so `b`
lies in the maximal ideal after all. -/
private lemma infW_not_unit_aux {L : Type*} [Field L] (E : WeierstrassCurve L) :
    ¬ ∃ h : Func E, h ∈ infPlace E ∧ infW E * h = 1 := by
  rintro ⟨h, hh, hh1⟩
  obtain ⟨a, b, hb, hab⟩ := (PoleAux.infPlace_mem_iff E h).mp hh
  have hbval : (b : Func E) = (a : Func E) * infW E := by
    have key : (infW E * h) * (b : Func E) = (a : Func E) * infW E := by
      rw [← hab]; ring
    rwa [hh1, one_mul] at key
  have hbI : (b : Func E) ∈ infIdeal E := by
    rw [hbval]
    have hsm : a • infW E = (a : Func E) * infW E := by
      rw [Subalgebra.smul_def, Algebra.smul_def]; simp
    rw [← hsm]
    exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  exact hb ((PoleAux.mem_infIdealR_iff E b).mp hbI)

theorem PoleCond_v2 (L : Type*) [Field L] (E E' : WeierstrassCurve L) [E.IsElliptic] [E'.IsElliptic]
    (Θ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E')
    (hO : Subalgebra.map Θ.toAlgHom (Work.MotC2.infPlace E) = Work.MotC2.infPlace E') :
    Θ (Work.MotC2.genX E) * (Work.MotC2.infW E') ^ 2 ∈ Work.MotC2.infPlace E' ∧
      Θ (Work.MotC2.genY E) * (Work.MotC2.infW E') ^ 3 ∈ Work.MotC2.infPlace E' := by
  -- `Θ` maps `infPlace E` onto `infPlace E'`, in both directions
  have hiff : ∀ x : Func E, Θ x ∈ infPlace E' ↔ x ∈ infPlace E := by
    intro x
    constructor
    · intro hx
      have hx' : Θ x ∈ Subalgebra.map Θ.toAlgHom (infPlace E) := by rw [hO]; exact hx
      obtain ⟨y, hy, hyx⟩ := Subalgebra.mem_map.mp hx'
      have hyx' : y = x := Θ.injective hyx
      rwa [hyx'] at hy
    · intro hx
      exact hO.le (Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩)
  have hΘ : ∀ x : Func E, x ∈ infPlace E → Θ x ∈ infPlace E' := fun x hx => (hiff x).mpr hx
  have hΘ' : ∀ x : Func E', x ∈ infPlace E' → Θ.symm x ∈ infPlace E := fun x hx =>
    (hiff (Θ.symm x)).mp (by simpa using hx)
  -- the uniformizer `w'` of `E'` is not a unit of the local ring at `O'`
  have hw'nu : ¬ ∃ h : Func E', h ∈ infPlace E' ∧ infW E' * h = 1 := infW_not_unit_aux E'
  -- hence neither is its preimage `Θ⁻¹(w')` in `infPlace E`
  have hfnu : ¬ ∃ g : Func E, g ∈ infPlace E ∧ Θ.symm (infW E') * g = 1 := by
    rintro ⟨g, hg, hg1⟩
    refine hw'nu ⟨Θ g, hΘ g hg, ?_⟩
    have h := congrArg (fun z : Func E => Θ z) hg1
    simp only [map_mul, map_one, AlgEquiv.apply_symm_apply] at h
    exact h
  have hmemf : Θ.symm (infW E') ∈ infPlace E :=
    hΘ' (infW E') (infW_mem_infPlace_aux E')
  -- the dichotomy: `Θ⁻¹(w') = w · g` with `g ∈ infPlace E`, i.e. `w' = Θ w · Θ g`
  obtain ⟨g, hg, hge⟩ := (infPlace_dichotomy L E (Θ.symm (infW E')) hmemf).resolve_left hfnu
  have hg' : Θ g ∈ infPlace E' := hΘ g hg
  have hw'eq : infW E' = Θ (infW E) * Θ g := by
    have h := congrArg (fun z : Func E => Θ z) hge
    simp only [map_mul, AlgEquiv.apply_symm_apply] at h
    exact h
  constructor
  · have hmain : Θ (genX E * (infW E) ^ 2) ∈ infPlace E' := hΘ _ (genX_infW_sq_mem E)
    have hkey : Θ (genX E) * (infW E') ^ 2 = Θ (genX E * (infW E) ^ 2) * (Θ g) ^ 2 := by
      rw [map_mul, map_pow, hw'eq, mul_pow]
      first | refl_ring1 | ring
    rw [hkey]
    exact Subalgebra.mul_mem _ hmain (Subalgebra.pow_mem _ hg' 2)
  · have hmain : Θ (genY E * (infW E) ^ 3) ∈ infPlace E' := hΘ _ (genY_infW_cube_mem E)
    have hkey : Θ (genY E) * (infW E') ^ 3 = Θ (genY E * (infW E) ^ 3) * (Θ g) ^ 3 := by
      rw [map_mul, map_pow, hw'eq, mul_pow]
      first | refl_ring1 | ring
    rw [hkey]
    exact Subalgebra.mul_mem _ hmain (Subalgebra.pow_mem _ hg' 3)

end Work.MotK.TwRuling
