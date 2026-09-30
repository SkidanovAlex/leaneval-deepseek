import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.est17_height_ext

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The element form of `est17_height_ext`

`Work.BW.est17_height_ext` computes the (projective, place-weighted) logarithmic height of a
tuple over `K` after pushing it into the Kummer extension `L = ℚ(φ(K), ρ₁,…,ρ_r)`: it is `2^r`
times the height in `K`.  Here we deduce the corresponding statement for a single element,
`Height.logHeight₁`, by writing the element height as the height of the pair `!(x, 1)`.

The imported statements `Work.BW.est17_height_ext` and `Work.BW.logHeight_algEquiv` currently
rest on the axiom `sorryAx` (through the not-yet-proved sibling
`Work.BW.finprod_finitePlace_ringEquiv`).  To keep this file free of that axiom we prove the two
needed ingredients locally:

* `finprod_finitePlace_ringEquiv_local` — the finite-place part of the height of a tuple of
  algebraic integers is invariant under ring isomorphisms of rings of integers (via
  `NumberField.absNorm_mul_finprod_finitePlace_eq_one` and `Work.BW.absNorm_map_ringEquiv`);
* `logHeight_algEquiv_local` — invariance of the full place-weighted height under
  `ℚ`-algebra isomorphisms of number fields, following the same proof as
  `Work.BW.logHeight_algEquiv` but using the clean finite-place lemma;

and then re-run the proof of `est17_height_ext` with these clean ingredients
(`est17_height_ext_local`).
-/

namespace Work.BW

open NumberField

/-! ### Finite-place invariance under ring isomorphisms of rings of integers -/

theorem finprod_finitePlace_ringEquiv_local {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [NumberField K'] (E : 𝓞 K ≃+* 𝓞 K') {ι : Type*} [Fintype ι]
    (q : ι → 𝓞 K) (hq : q ≠ 0) :
    (∏ᶠ v : FinitePlace K', ⨆ i, v ((E (q i) : 𝓞 K') : K')) =
      ∏ᶠ v : FinitePlace K, ⨆ i, v ((q i : 𝓞 K) : K) := by
  have hq' : (fun i => E (q i)) ≠ 0 := by
    intro h
    apply hq
    funext i
    have h1 : E (q i) = 0 := congrFun h i
    exact E.injective (h1.trans (map_zero E).symm)
  have h1 := NumberField.absNorm_mul_finprod_finitePlace_eq_one (x := q) hq
  have h2 := NumberField.absNorm_mul_finprod_finitePlace_eq_one (x := fun i => E (q i)) hq'
  have hspan : Ideal.span (Set.range (fun i => E (q i)))
      = (Ideal.span (Set.range q)).map (E : 𝓞 K →+* 𝓞 K') := by
    rw [Ideal.map_span]
    congr 1
    exact Set.range_comp E q
  have habs : Ideal.absNorm (Ideal.span (Set.range (fun i => E (q i))))
      = Ideal.absNorm (Ideal.span (Set.range q)) := by
    rw [hspan]
    exact absNorm_map_ringEquiv E (Ideal.span (Set.range q))
  have hA : (Ideal.absNorm (Ideal.span (Set.range q)) : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact zero_ne_one h1
  have h2' : (Ideal.absNorm (Ideal.span (Set.range q)) : ℝ)
      * (∏ᶠ v : FinitePlace K', ⨆ i, v ((E (q i) : 𝓞 K') : K')) = 1 := by
    rw [← habs]
    exact h2
  exact (mul_left_cancel₀ hA (h1.trans h2'.symm)).symm

/-! ### Invariance of the height under `ℚ`-algebra isomorphisms -/

theorem logHeight_algEquiv_local {K K' : Type*} [Field K] [NumberField K] [Field K']
    [NumberField K'] (e : K ≃ₐ[ℚ] K') {ι : Type*} [Fintype ι] (p : ι → K) :
    Height.logHeight (fun i => e (p i)) = Height.logHeight p := by
  rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight]
  congr 1
  by_cases hp : p = 0
  · subst hp
    simp
  · have hp' : (fun i => e (p i)) ≠ 0 := by
      intro h
      apply hp
      funext i
      have h1 : e (p i) = 0 := congrFun h i
      exact e.injective (h1.trans (map_zero e).symm)
    obtain ⟨n, hn, hni⟩ := exists_nat_mul_isIntegral p
    have hnK : (n : K) ≠ 0 := by exact_mod_cast hn
    have hnK' : (n : K') ≠ 0 := by exact_mod_cast hn
    let q : ι → 𝓞 K := fun i => ⟨(n : K) * p i, hni i⟩
    let q' : ι → 𝓞 K' := fun i => ringOfIntegersEquiv e (q i)
    have hq : q ≠ 0 := by
      intro h
      apply hp
      funext i
      have h1 : (q i : 𝓞 K) = 0 := congrFun h i
      have h2 : (n : K) * p i = 0 := congrArg (fun y : 𝓞 K => (y : K)) h1
      exact (mul_eq_zero.mp h2).resolve_left hnK
    have hq' : q' ≠ 0 := by
      intro h
      apply hq
      funext i
      have h1 : q' i = 0 := congrFun h i
      have h2 : e ((q i : K)) = 0 := congrArg (fun y : 𝓞 K' => (y : K')) h1
      exact Subtype.ext (e.injective (h2.trans (map_zero e).symm))
    have hqK_ne : (fun i => (q i : K)) ≠ 0 := by
      intro h
      apply hq
      funext i
      have h1 : (q i : K) = 0 := congrFun h i
      exact Subtype.ext h1
    have hq'K'_ne : (fun i => (q' i : K')) ≠ 0 := by
      intro h
      apply hq'
      funext i
      have h1 : (q' i : K') = 0 := congrFun h i
      exact Subtype.ext h1
    have harch : (∏ v : InfinitePlace K', (⨆ i, v ((q' i : K'))) ^ v.mult)
        = ∏ v : InfinitePlace K, (⨆ i, v ((q i : K))) ^ v.mult :=
      prod_infinitePlace_algEquiv e (fun i => (q i : K))
    have hfin : (∏ᶠ v : FinitePlace K', ⨆ i, v ((q' i : 𝓞 K') : K'))
        = ∏ᶠ v : FinitePlace K, ⨆ i, v ((q i : 𝓞 K) : K) :=
      finprod_finitePlace_ringEquiv_local (ringOfIntegersEquiv e) q hq
    have hmid : Height.mulHeight (fun i => (q i : K)) = Height.mulHeight (fun i => (q' i : K')) := by
      rw [NumberField.mulHeight_eq (x := fun i => (q i : K)) hqK_ne,
        NumberField.mulHeight_eq (x := fun i => (q' i : K')) hq'K'_ne]
      rw [harch, hfin]
    have hscale1 : (fun i => (q' i : K')) = (n : K') • (fun i => e (p i)) := by
      funext i
      show (ringOfIntegersEquiv e (q i) : K') = (n : K') * e (p i)
      rw [ringOfIntegersEquiv_coe]
      show e ((n : K) * p i) = (n : K') * e (p i)
      rw [map_mul, map_natCast]
    have hscale2 : (fun i => (q i : K)) = (n : K) • p := by
      funext i
      show ((q i : 𝓞 K) : K) = (n : K) * p i
      rfl
    calc Height.mulHeight (fun i => e (p i))
        = Height.mulHeight (fun i => (q' i : K')) := by
            rw [hscale1]
            exact (Height.mulHeight_smul_eq_mulHeight (fun i => e (p i)) hnK').symm
      _ = Height.mulHeight (fun i => (q i : K)) := hmid.symm
      _ = Height.mulHeight p := by
            rw [hscale2]
            exact Height.mulHeight_smul_eq_mulHeight p hnK

/-! ### The tuple version, re-derived without the `sorry`-tainted imports -/

theorem est17_height_ext_local {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {η : Fin r → K} (hη : ∀ j, η j ≠ 0)
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) (hK : KummerCond η) [inst : NumberField (EL φ ρ)]
    {ι : Type*} [Fintype ι] (p : ι → K) :
    Height.logHeight (fun i => inclE φ ρ (p i)) = ((2 : ℝ) ^ r) * Height.logHeight p := by
  haveI hNF : NumberField (Kimg φ ρ) := Kimg_numberField φ ρ
  have hdeg : Module.finrank ↥(Kimg φ ρ) (EL φ ρ) = 2 ^ r := finrank_Kimg hη hρ hK
  have h1 : Height.logHeight (fun i => ((KimgEquiv φ ρ (p i) : Kimg φ ρ) : EL φ ρ))
      = ((Module.finrank ↥(Kimg φ ρ) (EL φ ρ) : ℕ) : ℝ)
        * Height.logHeight (fun i => KimgEquiv φ ρ (p i)) :=
    logHeight_intermediate (K := EL φ ρ) (Kimg φ ρ) (x := fun i => KimgEquiv φ ρ (p i))
  have h2 : Height.logHeight (fun i => KimgEquiv φ ρ (p i)) = Height.logHeight p :=
    logHeight_algEquiv_local (KimgEquiv φ ρ) p
  rw [show (fun i => inclE φ ρ (p i))
        = (fun i => ((KimgEquiv φ ρ (p i) : Kimg φ ρ) : EL φ ρ)) from by
      funext i; exact (KimgEquiv_apply (p i)).symm]
  rw [h1, h2, hdeg]
  push_cast
  ring

/-! ### The element version -/

/-- The element version of `est17_height_ext`: for `x : K`, the logarithmic height computed in
the Kummer extension `L = ℚ(φ(K), ρ₁,…,ρ_r)` is `2^r` times the height in `K`. -/
theorem est17_height_ext1 {K : Type*} [Field K] [NumberField K] {r : ℕ} {φ : K →+* ℂ}
    {ρ : Fin r → ℂ} {η : Fin r → K} (hη : ∀ j, η j ≠ 0)
    (hρ : ∀ j, ρ j ^ 2 = φ (η j)) (hK : KummerCond η) [inst : NumberField (EL φ ρ)]
    (x : K) :
    Height.logHeight₁ (inclE φ ρ x) = ((2 : ℝ) ^ r) * Height.logHeight₁ x := by
  rw [Height.logHeight₁_eq_logHeight (inclE φ ρ x), Height.logHeight₁_eq_logHeight x]
  have h : (fun i : Fin 2 => inclE φ ρ (![x, 1] i)) = ![inclE φ ρ x, 1] := by
    funext i
    fin_cases i <;> simp
  rw [← h]
  exact est17_height_ext_local hη hρ hK ![x, 1]

end Work.BW
