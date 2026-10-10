import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.AffPlaceSetup

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-- From a nonzero order of vanishing at an affine rational place, produce the evaluation map.

`a` is a nonzero element of the affine coordinate ring of the elliptic curve `E` over `N`, `(c,d)`
a nonsingular affine point and `S = affPlaceAt E c d` its local ring (with `hplace` the proof that
`S` is a rational place, e.g. `(Work.MotC2.AffPlace N E c d h).1`). If the order of vanishing of
`algebraMap a` at `S` is nonzero, then `algebraMap a` vanishes at `(c,d)`: there is an `N`-algebra
map `CoordinateRing E →ₐ[N] N` with `x ↦ c`, `y ↦ d` and `a ↦ 0`.

Route. Let `f := algebraMap (CoordinateRing E) (Func E) a`. `hplace` gives the discrete valuation
ring structure on `↥S`; `f ∈ S` by `Work.MotC2.algebraMap_mem_affPlaceAt`, and `f ≠ 0` from `ha`
and `IsFractionRing.injective`. From `H.ord_nonneg` (`0 ≤ ord ↔ f ∈ S`) and `hord` get
`0 < Work.MotV.ordOfPlace E (affPlaceAt E c d) hplace f`.

Then `f` is not a unit of `↥S`: if `f * v = 1` with `v ∈ S`, then `f⁻¹ = (v : Func E) ∈ S`, so
`0 ≤ ordOfPlace ... f⁻¹ = -ordOfPlace ... f` by `Work.MotV.H1Data.ord_inv`, contradiction with
`0 < ord`. Hence `(⟨f, _⟩ : ↥S) ∈ IsLocalRing.maximalIdeal ↥S` by `IsLocalRing.mem_maximalIdeal.mpr`.

Build the residue map as in the proof of `Work.MotC2.Classification`: write
`hplace = ⟨⟨hDVR, hres⟩, hfrac⟩`, `letI := hDVR`, and set
`e : N ≃ₐ[N] (↥S ⧸ IsLocalRing.maximalIdeal ↥S) := AlgEquiv.ofBijective
((Ideal.Quotient.mkₐ N _).comp (Algebra.ofId N ↥S)) hres`,
`ψ : ↥S →ₐ[N] N := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ N _)`. Then `ψ` kills the maximal
ideal and `ψ (algebraMap N ↥S n) = n`.

`Work.MotC2.affPlaceAt_XClass_mem_maximalIdeal` says
`X' := algebraMap (CoordinateRing E) ↥S (CoordinateRing.XClass E c) ∈ 𝔪_S`, and
`Work.MotC2.XClass_eq_coordX_sub` with `Work.MotC2.affPlaceAt_algebraMap_XClass` compute
`X' = algebraMap (CoordinateRing E) ↥S (coordX E) - algebraMap N ↥S c`; hence
`ψ (algebraMap (CoordinateRing E) ↥S (coordX E)) = c`. The same with `CoordinateRing.YClass` and
`Work.MotC2.YClass_eq_coordY_sub` gives `d` for `coordY E`. Finish with
`φ := ψ.comp (Work.MotC2.affPlaceAtAlgHom E c d)`, whose value at `a` is `ψ ⟨f,_⟩ = 0` since
`⟨f,_⟩ ∈ 𝔪_S`. (statement `theorem`: `Work.MotV.algHomOfOrdNeZero`) -/
theorem algHomOfOrdNeZero {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E) (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0)
    (c d : N) (h : WeierstrassCurve.Affine.Nonsingular E c d)
    (hplace : Work.MotC2.IsRatPlace E (Work.MotC2.affPlaceAt E c d))
    (hord : Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) hplace
      (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) ≠ 0) :
    ∃ φ : WeierstrassCurve.Affine.CoordinateRing E →ₐ[N] N,
      φ (Work.MotC2.coordX E) = c ∧ φ (Work.MotC2.coordY E) = d ∧ φ a = 0 := by
  haveI : Work.MotC2.IsNonsingularPoint E c d := ⟨h⟩
  -- The function `f = algebraMap a` is regular at the place and has strictly positive order.
  set f : Work.MotC2.Func E := algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a with hf
  have hf_mem : f ∈ Work.MotC2.affPlaceAt E c d := by
    rw [hf]; exact Work.MotC2.algebraMap_mem_affPlaceAt E c d a
  have hf_ne : f ≠ 0 := by
    rw [hf]
    intro h0
    exact ha (IsFractionRing.injective (Work.MotC2.Coord E) (Work.MotC2.Func E)
      (by simpa using h0))
  have hle : 0 ≤ Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) hplace f :=
    (H.ord_nonneg (Work.MotC2.affPlaceAt E c d) hplace f).mpr hf_mem
  have hpos : 0 < Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) hplace f :=
    lt_of_le_of_ne' hle hord
  -- `f` is not a unit of the local ring, hence lies in its maximal ideal.
  have hnotunit : ¬ IsUnit (⟨f, hf_mem⟩ : ↥(Work.MotC2.affPlaceAt E c d)) := by
    rintro ⟨u, hu⟩
    have hval : ((↑u : ↥(Work.MotC2.affPlaceAt E c d)) : Work.MotC2.Func E) = f := by rw [hu]
    have h3 : ((↑u : ↥(Work.MotC2.affPlaceAt E c d)) : Work.MotC2.Func E) *
        ((((u⁻¹ : (↥(Work.MotC2.affPlaceAt E c d))ˣ)) : ↥(Work.MotC2.affPlaceAt E c d)) :
          Work.MotC2.Func E) = 1 :=
      congrArg (fun z : ↥(Work.MotC2.affPlaceAt E c d) => (z : Work.MotC2.Func E))
        (Units.mul_inv u)
    have h2 : f * ((((u⁻¹ : (↥(Work.MotC2.affPlaceAt E c d))ˣ)) :
        ↥(Work.MotC2.affPlaceAt E c d)) : Work.MotC2.Func E) = 1 := by
      rw [hval] at h3; exact h3
    have hinv : f⁻¹ = ((((u⁻¹ : (↥(Work.MotC2.affPlaceAt E c d))ˣ)) :
        ↥(Work.MotC2.affPlaceAt E c d)) : Work.MotC2.Func E) :=
      inv_eq_of_mul_eq_one_right h2
    have hmem_inv : f⁻¹ ∈ Work.MotC2.affPlaceAt E c d := by
      rw [hinv]
      exact (((u⁻¹ : (↥(Work.MotC2.affPlaceAt E c d))ˣ)) :
        ↥(Work.MotC2.affPlaceAt E c d)).2
    have hle' : 0 ≤ Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) hplace f⁻¹ :=
      (H.ord_nonneg _ hplace f⁻¹).mpr hmem_inv
    rw [H.ord_inv (Work.MotC2.affPlaceAt E c d) hplace f hf_ne] at hle'
    linarith
  have hmem : (⟨f, hf_mem⟩ : ↥(Work.MotC2.affPlaceAt E c d)) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E c d) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnotunit
  -- The residue map `ψ` of the rational place, killing the maximal ideal.
  obtain ⟨⟨hDVR, hres⟩, hfrac⟩ := hplace
  letI : IsDiscreteValuationRing ↥(Work.MotC2.affPlaceAt E c d) := hDVR
  let F : N →ₐ[N] (↥(Work.MotC2.affPlaceAt E c d) ⧸
        IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E c d)) :=
      (Ideal.Quotient.mkₐ N _).comp (Algebra.ofId N _)
  have hres' : Function.Bijective ⇑F := by
    have hfun : ⇑F = fun n : N => Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E c d))
        (algebraMap N ↥(Work.MotC2.affPlaceAt E c d) n) := by
      funext n
      simp only [F, AlgHom.comp_apply, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [hfun]; exact hres
  let e : N ≃ₐ[N] (↥(Work.MotC2.affPlaceAt E c d) ⧸
        IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E c d)) :=
      AlgEquiv.ofBijective F hres'
  let ψ : ↥(Work.MotC2.affPlaceAt E c d) →ₐ[N] N :=
      e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ N _)
  have he : ∀ n : N, e n = Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E c d))
        (algebraMap N ↥(Work.MotC2.affPlaceAt E c d) n) := by
    intro n
    rw [show e = AlgEquiv.ofBijective F hres' from rfl]
    rw [AlgEquiv.ofBijective_apply]
    simp only [F, AlgHom.comp_apply, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]
  have hψ_alg : ∀ n : N, ψ (algebraMap N ↥(Work.MotC2.affPlaceAt E c d) n) = n := by
    intro n
    simp only [ψ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [show Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E c d))
          (algebraMap N ↥(Work.MotC2.affPlaceAt E c d) n) = e n from (he n).symm]
    exact AlgEquiv.symm_apply_apply e n
  have hψ_kill : ∀ x : ↥(Work.MotC2.affPlaceAt E c d),
      x ∈ IsLocalRing.maximalIdeal ↥(Work.MotC2.affPlaceAt E c d) → ψ x = 0 := by
    intro x hx
    simp only [ψ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  -- Values of `ψ` on the coordinates.
  have hX : ψ (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E c d)
      (Work.MotC2.coordX E)) = c := by
    have hz := hψ_kill _ (Work.MotC2.affPlaceAt_XClass_mem_maximalIdeal E c d)
    rw [Work.MotC2.affPlaceAt_algebraMap_XClass E c d, map_sub, hψ_alg c] at hz
    exact sub_eq_zero.mp hz
  have hY : ψ (algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E c d)
      (Work.MotC2.coordY E)) = d := by
    have hz := hψ_kill _ (Work.MotC2.affPlaceAt_YClass_mem_maximalIdeal E c d)
    rw [Work.MotC2.affPlaceAt_algebraMap_YClass E c d, map_sub, hψ_alg d] at hz
    exact sub_eq_zero.mp hz
  have hφa : ψ ((Work.MotC2.affPlaceAtAlgHom E c d) a) = 0 := by
    have hthis : (Work.MotC2.affPlaceAtAlgHom E c d) a
        = (⟨f, hf_mem⟩ : ↥(Work.MotC2.affPlaceAt E c d)) := by
      apply Subtype.ext
      show algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) a = f
      rw [hf]
    rw [hthis]
    exact hψ_kill _ hmem
  refine ⟨ψ.comp (Work.MotC2.affPlaceAtAlgHom E c d), ?_, ?_, ?_⟩
  · show ψ ((Work.MotC2.affPlaceAtAlgHom E c d) (Work.MotC2.coordX E)) = c
    rw [show (Work.MotC2.affPlaceAtAlgHom E c d) (Work.MotC2.coordX E)
        = algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E c d)
            (Work.MotC2.coordX E) from rfl]
    exact hX
  · show ψ ((Work.MotC2.affPlaceAtAlgHom E c d) (Work.MotC2.coordY E)) = d
    rw [show (Work.MotC2.affPlaceAtAlgHom E c d) (Work.MotC2.coordY E)
        = algebraMap (Work.MotC2.Coord E) ↥(Work.MotC2.affPlaceAt E c d)
            (Work.MotC2.coordY E) from rfl]
    exact hY
  · show ψ ((Work.MotC2.affPlaceAtAlgHom E c d) a) = 0
    exact hφa

end Work.MotV
