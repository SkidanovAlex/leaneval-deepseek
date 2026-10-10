import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Linear disjointness of a finite Galois subextension from a linearly disjoint complement

Let `K ⊆ Ω` be fields and let `A`, `B ⊆ Ω` be intermediate fields with `A ⊓ B = ⊥`.  If `A / K` is
Galois (and finite dimensional, so that `A` has a primitive element over `K`), then `A` and `B` are
linearly disjoint over `K`.

This is the standard Galois criterion for linear disjointness.  Mathlib's
`IntermediateField.LinearDisjoint.of_inf_eq_bot` states it under the additional hypothesis
`FiniteDimensional K ↥B`; here `B` is arbitrary — in the applications it is an infinite extension
of `K` (a function field), so the finite dimensionality of `B` genuinely cannot be assumed and the
criterion has to be proved in the general form.

The mathematical content is the following minimal-polynomial computation.  For `θ ∈ A`, put
`f := minpoly K θ` and `g := minpoly ↥B θ` (viewing `θ` as an element of `Ω`).  Since `f(θ) = 0`
and `f ∈ (↥B)[X]`, we have `g ∣ f`; hence, after base change to `Ω`, `g` divides `f`.  Because
`A / K` is normal, `f` splits into linear factors over `A`; consequently every monic divisor of
`f` over `Ω` that comes from `↥B[X]` has all its roots in `A` and therefore, being a product of
linear factors with roots in `A`, has all its coefficients in `A`.  Those coefficients also lie in
`B`, so they lie in `A ⊓ B = K`, and the divisor is (the base change of a monic polynomial over
`K`) dividing the irreducible `f`, hence equals `f`.  Thus `minpoly ↥B θ` is the base change of
`f`; specializing this to a primitive element `θ` of `A / K` shows that the powers of `θ`, which
form a `K`-basis of `A`, remain linearly independent over `B`, which is linear disjointness by
`IntermediateField.LinearDisjoint.of_basis_left`.
-/

namespace Work.MotV5.LamAS

open Polynomial IntermediateField

/-- Let `A / K` be Galois, `B ⊆ Ω` an intermediate field with `A ⊓ B = ⊥`, and `θ : ↥A`.  Then
the minimal polynomial of `θ` over `B` is the base change to `B` of the minimal polynomial of `θ`
over `K`, up to base change to `Ω`. -/
private theorem minpoly_map_eq_of_isGalois_inf_bot_aux {K : Type*} [Field K] {Ω : Type*}
    [Field Ω] [Algebra K Ω] (A B : IntermediateField K Ω) [IsGalois K ↥A] (θ : ↥A)
    (hint : IsIntegral K θ) (h : A ⊓ B = ⊥) :
    (minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)
      = (minpoly K θ).map (algebraMap K Ω) := by
  classical
  have hfm : (minpoly K θ).Monic := minpoly.monic hint
  have hfne : minpoly K θ ≠ 0 := hfm.ne_zero
  have hsplitA : ((minpoly K θ).map (algebraMap K ↥A)).Splits := IsGalois.splits K θ
  have hβint : IsIntegral ↥B (algebraMap ↥A Ω θ) :=
    ((isIntegral_algebraMap_iff (A := ↥A) (B := Ω)).mpr hint).tower_top
  have hgm : (minpoly ↥B (algebraMap ↥A Ω θ)).Monic := minpoly.monic hβint
  have hgne : minpoly ↥B (algebraMap ↥A Ω θ) ≠ 0 := hgm.ne_zero
  -- `θ` is a root of `(minpoly K θ).map (algebraMap K ↥B)`
  have hroot : (Polynomial.aeval (R := ↥B) (algebraMap ↥A Ω θ))
      ((minpoly K θ).map (algebraMap K ↥B)) = 0 := by
    have h1 : (Polynomial.aeval (R := ↥B) (algebraMap ↥A Ω θ))
        ((minpoly K θ).map (algebraMap K ↥B))
        = (Polynomial.aeval (R := K) (algebraMap ↥A Ω θ)) (minpoly K θ) :=
      aeval_map_algebraMap ↥B (algebraMap ↥A Ω θ) (minpoly K θ)
    have h2 : (Polynomial.aeval (R := K) (algebraMap ↥A Ω θ)) (minpoly K θ)
        = algebraMap ↥A Ω ((Polynomial.aeval (R := K) θ) (minpoly K θ)) :=
      aeval_algebraMap_apply Ω θ (minpoly K θ)
    rw [h1, h2, minpoly.aeval, map_zero]
  have hgdvd : minpoly ↥B (algebraMap ↥A Ω θ) ∣ (minpoly K θ).map (algebraMap K ↥B) :=
    minpoly.dvd ↥B (algebraMap ↥A Ω θ) hroot
  have hGdvd : (minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)
      ∣ (minpoly K θ).map (algebraMap K Ω) := by
    have h1 := Polynomial.map_dvd (algebraMap ↥B Ω) hgdvd
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K ↥B Ω] at h1
  have hsplitΩ : ((minpoly K θ).map (algebraMap K Ω)).Splits := by
    have h1 := hsplitA.map (algebraMap ↥A Ω)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K ↥A Ω] at h1
  have hfΩne : (minpoly K θ).map (algebraMap K Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K Ω)).mpr hfne
  have hGsplit : ((minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)).Splits :=
    Splits.of_dvd hsplitΩ hfΩne hGdvd
  have hGmonic : ((minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)).Monic := hgm.map _
  have hGne : (minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω) ≠ 0 := hGmonic.ne_zero
  -- the roots of the divisor `g` all lie in the image of `↥A`
  have hrootsA : ((minpoly K θ).map (algebraMap K Ω)).roots
      = ((minpoly K θ).map (algebraMap K ↥A)).roots.map (algebraMap ↥A Ω) := by
    have h1 := Splits.roots_map_of_injective hsplitA (FaithfulSMul.algebraMap_injective ↥A Ω)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K ↥A Ω] at h1
  have hroots : ∀ a ∈ ((minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)).roots,
      a ∈ (algebraMap ↥A Ω).range := by
    intro a ha
    have h1 : ((minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)).IsRoot a :=
      (mem_roots hGne).mp ha
    have h2 : ((minpoly K θ).map (algebraMap K Ω)).IsRoot a := by
      obtain ⟨H, hH⟩ := hGdvd
      rw [Polynomial.IsRoot.def] at h1 ⊢
      rw [hH, Polynomial.eval_mul, h1, zero_mul]
    have h3 : a ∈ ((minpoly K θ).map (algebraMap K Ω)).roots := (mem_roots hfΩne).mpr h2
    rw [hrootsA, Multiset.mem_map] at h3
    obtain ⟨y, _, hy⟩ := h3
    exact ⟨y, hy⟩
  have hGlift : (minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)
      ∈ Polynomial.lifts (algebraMap ↥A Ω) :=
    Splits.mem_lift_of_roots_mem_range hGsplit hGmonic (algebraMap ↥A Ω) hroots
  obtain ⟨F, hF⟩ := (Polynomial.mem_lifts _).mp hGlift
  have hFmonic : F.Monic := by
    apply Polynomial.monic_of_monic_mapAlg (S := Ω)
    rw [Polynomial.mapAlg_eq_map, hF]
    exact hGmonic
  -- the coefficients of `F` lie in `K`
  have hFcoeff : ∀ n, F.coeff n ∈ (algebraMap K ↥A).range := by
    intro n
    have hcoeff : algebraMap ↥A Ω (F.coeff n)
        = algebraMap ↥B Ω ((minpoly ↥B (algebraMap ↥A Ω θ)).coeff n) := by
      rw [← Polynomial.coeff_map (algebraMap ↥A Ω) n, hF,
        Polynomial.coeff_map (algebraMap ↥B Ω) n]
    have hmem : algebraMap ↥A Ω (F.coeff n) ∈ (⊥ : IntermediateField K Ω) := by
      rw [← h, IntermediateField.mem_inf]
      exact ⟨(F.coeff n).2, by rw [hcoeff]; exact ((minpoly ↥B (algebraMap ↥A Ω θ)).coeff n).2⟩
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
    refine ⟨c, ?_⟩
    apply FaithfulSMul.algebraMap_injective ↥A Ω
    rw [← IsScalarTower.algebraMap_apply K ↥A Ω, hc]
  have hFlift : F ∈ Polynomial.lifts (algebraMap K ↥A) :=
    (Polynomial.lifts_iff_coeff_lifts F).mpr hFcoeff
  obtain ⟨f₁, hf₁map, hf₁deg, hf₁monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hFlift hFmonic
  -- `θ` is a root of `f₁`
  have hθroot : (Polynomial.aeval (R := K) θ) f₁ = 0 := by
    apply FaithfulSMul.algebraMap_injective ↥A Ω
    have h1 : algebraMap ↥A Ω ((Polynomial.aeval (R := K) θ) f₁)
        = (Polynomial.aeval (R := K) (algebraMap ↥A Ω θ)) f₁ :=
      (aeval_algebraMap_apply Ω θ f₁).symm
    have h2 : (Polynomial.aeval (R := K) (algebraMap ↥A Ω θ)) f₁
        = (Polynomial.aeval (R := Ω) (algebraMap ↥A Ω θ)) (f₁.map (algebraMap K Ω)) :=
      (aeval_map_algebraMap Ω (algebraMap ↥A Ω θ) f₁).symm
    have h3 : f₁.map (algebraMap K Ω)
        = (minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω) := by
      rw [IsScalarTower.algebraMap_eq K ↥A Ω, ← Polynomial.map_map, hf₁map, hF]
    have h4 : (Polynomial.aeval (R := Ω) (algebraMap ↥A Ω θ))
        ((minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω))
        = (Polynomial.aeval (R := ↥B) (algebraMap ↥A Ω θ))
            (minpoly ↥B (algebraMap ↥A Ω θ)) :=
      aeval_map_algebraMap Ω (algebraMap ↥A Ω θ) (minpoly ↥B (algebraMap ↥A Ω θ))
    rw [h1, h2, h3, h4, minpoly.aeval, map_zero]
  have hfdvd : minpoly K θ ∣ f₁ := minpoly.dvd K θ hθroot
  have hnat : f₁.natDegree ≤ (minpoly K θ).natDegree := by
    calc f₁.natDegree = F.natDegree := hf₁deg
      _ = ((minpoly ↥B (algebraMap ↥A Ω θ)).map (algebraMap ↥B Ω)).natDegree := by
            rw [← Polynomial.natDegree_map_eq_of_injective
              (FaithfulSMul.algebraMap_injective ↥A Ω) F, hF]
      _ ≤ ((minpoly K θ).map (algebraMap K Ω)).natDegree :=
            Polynomial.natDegree_le_of_dvd hGdvd hfΩne
      _ = (minpoly K θ).natDegree :=
            Polynomial.natDegree_map_eq_of_injective
              (FaithfulSMul.algebraMap_injective K Ω) (minpoly K θ)
  have hf₁eq : f₁ = minpoly K θ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hfm hf₁monic hfdvd hnat
  rw [← hF, ← hf₁map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq K ↥A Ω, hf₁eq]

/-- If `A ⊓ B = ⊥` and `A / K` is a finite Galois extension, then `A` and `B` are linearly
disjoint over `K`.  (Note that no finiteness hypothesis is imposed on `B`.) -/
theorem linearDisjoint_of_isGalois_of_inf_bot {K : Type*} [Field K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] (A B : IntermediateField K Ω) [IsGalois K ↥A] [FiniteDimensional K ↥A]
    (h : A ⊓ B = ⊥) : A.LinearDisjoint ↥B := by
  classical
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K ↥A
  have hint : IsIntegral K θ := IsIntegral.of_finite K θ
  set pb : PowerBasis K ↥A := PowerBasis.ofAdjoinSimpleEqTop hint hθ with hpb
  have hdim : pb.dim = (minpoly ↥B (algebraMap ↥A Ω θ)).natDegree := by
    rw [hpb, PowerBasis.ofAdjoinSimpleEqTop_dim hint hθ]
    rw [← natDegree_map_eq_of_injective (algebraMap ↥B Ω).injective
          (minpoly ↥B (algebraMap ↥A Ω θ)),
      minpoly_map_eq_of_isGalois_inf_bot_aux A B θ hint h,
      natDegree_map_eq_of_injective (algebraMap K Ω).injective (minpoly K θ)]
  have hLI : LinearIndependent ↥B
      (fun i : Fin pb.dim => (algebraMap ↥A Ω θ) ^ (i : ℕ)) := by
    rw [hdim]
    exact linearIndependent_pow (algebraMap ↥A Ω θ)
  refine IntermediateField.LinearDisjoint.of_basis_left (A := A) (L := ↥B) pb.basis ?_
  convert hLI using 2 with i
  simp only [Function.comp_apply, hpb, PowerBasis.basis_eq_pow, PowerBasis.ofAdjoinSimpleEqTop_gen]
  rfl

end Work.MotV5.LamAS
