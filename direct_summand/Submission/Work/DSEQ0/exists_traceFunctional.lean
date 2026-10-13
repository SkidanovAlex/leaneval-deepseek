import Mathlib
import Submission.Work.DSEQ0.SuperTraceWindow
import Submission.Work.DSEQ0.sum_Icc_shift_boundary
import Submission.Work.DSEQ0.sum_Icc_mul_add_succ
import Submission.Work.DSEQ0.trace_mul_identity

/-!
# `Work.DSEQ0`: the trace functional attached to a strictly Leibniz product

This file proves the "P-A2" node of area `EQ0` (see `Submission/Work/DSEQ0/NEXT_input4.md`): on a
bounded complex `F` of finite free `A`-modules carrying

* a bilinear product `μ` satisfying the strict Leibniz rule `hLeib`, and
* a homotopy `H` exhibiting `μ 0 · (ε 1)` as the identity up to homotopy,

the *supertrace of the product*, `φ₀ x := Σᵢ (-1)ⁱ tr (μ x (−))ᵢ`, is an `A`-linear functional on
`F⁰` which

* kills the differential `F⁻¹ ⟶ F⁰` (the Leibniz rule plus cyclicity of the trace, telescoping
  over the window), and
* takes the value `Σ_{i∈[lo,hi]} (-1)ⁱ rk (Fⁱ)` at the coaugmentation `ε 1` (homotopy invariance
  of the supertrace, `Work.DSEQ0.superTraceWindow_eq_eulerChar_of_homotopy`).

The two combinatorial inputs are delegated:
`Work.DSEQ0.sum_Icc_mul_add_succ` (the telescoping of the windowed sum) and
`Work.DSEQ0.trace_mul_identity` (the per-degree trace identity coming from the Leibniz rule).

## The two halves of the computation

Writing `Φ x : ∀ i, F.X i →ₗ F.X i` for the family "multiplication by `x ∈ F⁰` (transported along
the canonical isomorphism `F.X (0+i) ≅ F.X i`)", so that `φ₀ = superTraceWindow A F lo hi ∘ Φ`:

* `φ₀ (d y) = Σ_{i∈[lo,hi]} degreeSign A i * (L i + L (i+1))` where
  `L m = tr (d(-1+m,m) ∘ μ(-1,m)(y))`.  This is `Work.DSEQ0.trace_mul_identity` summed over the
  window; the telescoping lemma `Work.DSEQ0.sum_Icc_mul_add_succ` (with the alternating sign, which
  satisfies `degreeSign A (m+1) = - degreeSign A m`) turns the sum into
  `degreeSign A lo * L lo - degreeSign A (hi+1) * L (hi+1)`, and both boundary terms vanish because
  `F` is concentrated in the window: `F.X (-1+lo)` and `F.X (hi+1)` are zero objects.
* `φ₀ (ε 1) = superTraceWindow A F lo hi (Φ (ε 1)) = eulerCharWindow A F lo hi` by homotopy
  invariance of the supertrace applied to `hunit`, and the Euler characteristic over the window is
  the stated integer `Σ (-1)ⁱ rk (Fⁱ)`.
-/

universe a

namespace Work.DSEQ0

set_option linter.style.haveILetI false in
/-- The degree sign `degreeSign A i = (-1)ⁱ` is `(-1)` to the absolute value of the degree. -/
theorem degreeSign_eq_neg_one_pow (A : Type a) [Ring A] (i : ℤ) :
    degreeSign A i = (-1 : A) ^ i.natAbs := by
  rw [degreeSign, neg_one_pow_eq_ite]
  by_cases h : Even i
  · have h2 : Even i.natAbs := Int.natAbs_even.mpr h
    rw [if_pos h, if_pos h2]
  · have h2 : ¬ Even i.natAbs := fun hc => h (Int.natAbs_even.mp hc)
    rw [if_neg h, if_neg h2]

/-- The degree sign is alternating: `degreeSign A (i + 1) = - degreeSign A i`. -/
theorem degreeSign_add_one (A : Type a) [Ring A] (i : ℤ) :
    degreeSign A (i + 1) = -degreeSign A i := by
  rw [degreeSign, degreeSign]
  by_cases hE : Even i
  · have h2 : ¬ Even (i + 1) := fun hc => (Int.even_add_one.mp hc) hE
    simp [hE, h2]
  · have h2 : Even (i + 1) := Int.even_add_one.mpr hE
    simp [hE, h2]

/-- `superTraceWindow` is additive in the family of endomorphisms. -/
theorem superTraceWindow_add (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ)
    (α β : ∀ i : ℤ, ↥(P.X i) →ₗ[A] ↥(P.X i)) :
    superTraceWindow A P a b (fun i => α i + β i) =
      superTraceWindow A P a b α + superTraceWindow A P a b β := by
  simp only [superTraceWindow, ← Finset.sum_add_distrib, ← mul_add, map_add]

/-- `superTraceWindow` is homogeneous in the family of endomorphisms. -/
theorem superTraceWindow_smul (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ) (c : A)
    (α : ∀ i : ℤ, ↥(P.X i) →ₗ[A] ↥(P.X i)) :
    superTraceWindow A P a b (fun i => c • α i) = c * superTraceWindow A P a b α := by
  simp only [superTraceWindow, map_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The windowed supertrace, as an `A`-linear functional on the module of families of
endomorphisms. -/
noncomputable def superTraceWindowLin (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ) :
    (∀ i : ℤ, ↥(P.X i) →ₗ[A] ↥(P.X i)) →ₗ[A] A where
  toFun := superTraceWindow A P a b
  map_add' := superTraceWindow_add A P a b
  map_smul' := superTraceWindow_smul A P a b

@[simp]
theorem superTraceWindowLin_apply (A : Type a) [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) [∀ i, Module.Finite A (P.X i)]
    [∀ i, Module.Free A (P.X i)] (a b : ℤ)
    (α : ∀ i : ℤ, ↥(P.X i) →ₗ[A] ↥(P.X i)) :
    superTraceWindowLin A P a b α = superTraceWindow A P a b α := rfl

set_option linter.style.haveILetI false in
theorem exists_traceFunctional (A : Type a) [CommRing A]
    (F : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ F.X 0) (lo hi : ℤ)
    (hbdd : ∀ i : ℤ, i < lo ∨ hi < i → CategoryTheory.Limits.IsZero (F.X i))
    (hfin : ∀ i : ℤ, Module.Finite A ↥(F.X i)) (hfree : ∀ i : ℤ, Module.Free A ↥(F.X i))
    (μ : ∀ i j : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X j) →ₗ[A] ↥(F.X (i + j)))
    (hLeib : ∀ (i j : ℤ) (x : ↥(F.X i)) (y : ↥(F.X j)),
        (F.d (i + j) (i + j + 1)).hom ((μ i j x) y) =
          (F.XIsoOfEq (by omega : i + 1 + j = i + j + 1)).hom
              (((μ (i + 1) j) ((F.d i (i + 1)).hom x)) y)
          + (-1 : A) ^ i.natAbs •
              ((F.XIsoOfEq (by omega : i + (j + 1) = i + j + 1)).hom
                ((μ i (j + 1) x) ((F.d j (j + 1)).hom y))))
    (H : ∀ j : ℤ, ↥(F.X (j + 1)) →ₗ[A] ↥(F.X j))
    (hunit : ∀ (j : ℤ) (y : ↥(F.X (j + 1))),
          (F.XIsoOfEq (by omega : 0 + (j + 1) = j + 1)).hom ((μ 0 (j + 1) (ε.hom 1)) y) - y =
            (F.d j (j + 1)).hom (H j y) + H (j + 1) ((F.d (j + 1) ((j + 1) + 1)).hom y)) :
    ∃ φ₀ : ↥(F.X 0) →ₗ[A] A,
      (∀ y : ↥(F.X (-1)), φ₀ ((F.d (-1) 0).hom y) = 0) ∧
      φ₀ (ε.hom 1) =
        ((∑ i ∈ Finset.Icc lo hi, (-1 : ℤ) ^ i.natAbs * (Module.finrank A ↥(F.X i) : ℤ) : ℤ) : A) := by
  haveI := hfin
  haveI := hfree
  -- The family of endomorphisms "multiplication by `x ∈ F⁰`", graded over `ℤ`.
  let Φ : ↥(F.X 0) →ₗ[A] (∀ i : ℤ, ↥(F.X i) →ₗ[A] ↥(F.X i)) :=
    { toFun := fun x i => (F.XIsoOfEq (by omega : 0 + i = i)).hom.hom.comp (μ 0 i x)
      map_add' := fun x x' => by
        funext i
        simp only [Pi.add_apply]
        rw [map_add, LinearMap.comp_add]
      map_smul' := fun c x => by
        funext i
        simp only [Pi.smul_apply]
        rw [map_smul, LinearMap.comp_smul, RingHom.id_apply] }
  refine ⟨superTraceWindowLin A F lo hi ∘ₗ Φ, ?_, ?_⟩
  · -- `φ₀` kills the differential: the Leibniz rule telescopes the windowed sum to zero.
    intro y
    let L : ℤ → A := fun m => LinearMap.trace A ↥(F.X m) ((F.d (-1 + m) m).hom.comp (μ (-1) m y))
    have hsum : superTraceWindow A F lo hi (Φ ((F.d (-1) 0).hom y))
        = ∑ i ∈ Finset.Icc lo hi, degreeSign A i * (L i + L (i + 1)) := by
      rw [superTraceWindow]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (Φ ((F.d (-1) 0).hom y)) i
            = ((F.XIsoOfEq (by omega : 0 + i = i)).hom.hom.comp (μ 0 i ((F.d (-1) 0).hom y))) from rfl,
          trace_mul_identity A F μ hLeib y i]
    rw [LinearMap.comp_apply, superTraceWindowLin_apply, hsum]
    by_cases hle : lo ≤ hi
    · rw [sum_Icc_mul_add_succ A (degreeSign A) (fun m => degreeSign_add_one A m) L lo hi hle]
      -- the two boundary terms vanish because `F` is concentrated in the window
      have hLlo : L lo = 0 := by
        haveI : Subsingleton ↥(F.X (-1 + lo)) :=
          (ModuleCat.isZero_iff_subsingleton).mp (hbdd (-1 + lo) (Or.inl (by omega)))
        show LinearMap.trace A ↥(F.X lo) ((F.d (-1 + lo) lo).hom.comp (μ (-1) lo y)) = 0
        have hz : ((F.d (-1 + lo) lo).hom.comp (μ (-1) lo y)) = 0 := by
          ext z
          rw [LinearMap.comp_apply, show (μ (-1) lo y) z = 0 from Subsingleton.elim _ _, map_zero,
            LinearMap.zero_apply]
        rw [hz, map_zero]
      have hLhi : L (hi + 1) = 0 := by
        haveI : Subsingleton ↥(F.X (hi + 1)) :=
          (ModuleCat.isZero_iff_subsingleton).mp (hbdd (hi + 1) (Or.inr (by omega)))
        show LinearMap.trace A ↥(F.X (hi + 1))
          ((F.d (-1 + (hi + 1)) (hi + 1)).hom.comp (μ (-1) (hi + 1) y)) = 0
        have hz : ((F.d (-1 + (hi + 1)) (hi + 1)).hom.comp (μ (-1) (hi + 1) y)) = 0 := by
          ext z
          rw [LinearMap.comp_apply, show z = 0 from Subsingleton.elim z 0, map_zero, map_zero,
            LinearMap.zero_apply]
        rw [hz, map_zero]
      rw [hLlo, hLhi]
      ring
    · -- empty window
      rw [Finset.Icc_eq_empty_iff.mpr hle]
      simp
  · -- the value at the coaugmentation: homotopy invariance of the supertrace.
    rw [LinearMap.comp_apply, superTraceWindowLin_apply]
    have hμ : ∀ j : ℤ, (Φ (ε.hom 1)) (j + 1) - 1 =
        (F.d j (j + 1)).hom.comp (H j) + (H (j + 1)).comp ((F.d (j + 1) ((j + 1) + 1)).hom) := by
      intro j
      ext z
      rw [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      show (Φ (ε.hom 1)) (j + 1) z - z
        = (F.d j (j + 1)).hom (H j z) + H (j + 1) ((F.d (j + 1) ((j + 1) + 1)).hom z)
      exact hunit j z
    have he := superTraceWindow_eq_eulerChar_of_homotopy A F lo hi hbdd (Φ (ε.hom 1)) H hμ
    rw [he, eulerCharWindow]
    -- identify the Euler characteristic with the stated integer expression
    have hcast : ((∑ i ∈ Finset.Icc lo hi,
          (-1 : ℤ) ^ i.natAbs * (Module.finrank A ↥(F.X i) : ℤ) : ℤ) : A)
        = ∑ i ∈ Finset.Icc lo hi, degreeSign A i * (Module.finrank A ↥(F.X i) : A) := by
      push_cast
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [degreeSign_eq_neg_one_pow]
    rw [hcast]

end Work.DSEQ0
