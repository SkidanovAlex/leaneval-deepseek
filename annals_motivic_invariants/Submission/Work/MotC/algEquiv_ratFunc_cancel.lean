import Mathlib

set_option linter.unusedVariables false -- v435-speed

/-!
# Rigidity of the constants of a rational function field (`MotC`, audit node C4)

If a `𝕜`-algebra isomorphism `RatFunc F₁ ≃ₐ[𝕜] RatFunc F₂` of rational function fields carries
the constants of `RatFunc F₁` into the constants of `RatFunc F₂`, then the base fields `F₁`, `F₂`
are themselves isomorphic as `𝕜`-algebras.

The mathematical content is that `F` is precisely the set of elements of `RatFunc F` algebraic
over `F` (`RatFunc.transcendental_of_ne_C`); equivalently every non-constant element of `RatFunc F`
is transcendental over `F`.

The proof strategy is as follows.  Choose the induced map `φ : F₁ → F₂` on constants; it is
injective and a ring homomorphism, hence gives `F₁ →ₐ[𝕜] F₂`.  For surjectivity, suppose `y ∈ F₂`
is not in the image and put `z := e⁻¹ y`.  Let `D` be the preimage under `e` of the constants of
`RatFunc F₂`; it is an `F₁`-intermediate field containing `z` but not `X₁`, hence is not `⊥`.  By
`RatFunc.IntermediateField.isAlgebraic_X`, `X₁` is algebraic over `D`, and transporting this
relation along `e` shows that `u := e X₁` is algebraic over `F₂`.  But `u` generates `RatFunc F₂`
over `F₂` (`RatFunc.adjoin_X`), so then `X₂` would be algebraic over `F₂`, contradicting
`RatFunc.transcendental_X`.  Hence `φ` is surjective.
-/

namespace Work.MotC

namespace RatFuncCancel

open Polynomial

/-- `aeval` commutes with a ring homomorphism `ψ` whose restriction to scalars is a ring
homomorphism `φ`: `ψ (aeval x p) = aeval (ψ x) (p.map φ)`. -/
lemma map_aeval_eq {K L M N : Type*} [CommSemiring K] [CommSemiring L] [CommSemiring M]
    [CommSemiring N] [Algebra K L] [Algebra M N]
    (ψ : L →+* N) (φ : K →+* M) (x : L)
    (h : ∀ k, ψ (algebraMap K L k) = algebraMap M N (φ k)) (p : K[X]) :
    ψ (Polynomial.aeval x p) = Polynomial.aeval (ψ x) (p.map φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, map_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, map_mul, map_pow, h a, Polynomial.map_monomial,
      Polynomial.aeval_monomial]

/-- Algebraicity transfers along a ring homomorphism of fields which is compatible with the
scalar structures. -/
lemma isAlgebraic_of_ringHom {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra M N] (ψ : L →+* N) (φ : K →+* M) (hφ : Function.Injective φ)
    (h : ∀ k, ψ (algebraMap K L k) = algebraMap M N (φ k)) {x : L} (hx : IsAlgebraic K x) :
    IsAlgebraic M (ψ x) := by
  obtain ⟨p, hp, hp0⟩ := hx
  refine ⟨p.map φ, ?_, ?_⟩
  · intro hzero
    exact hp ((Polynomial.map_eq_zero_iff hφ).mp hzero)
  · rw [← map_aeval_eq ψ φ x h p, hp0, map_zero]

/-- If a ring equivalence `ψ` maps the scalars `K` into the scalars `M` compatibly with `φ`, then
`ψ` sends a field generated over `K` by one element to the field generated over `M` by its image. -/
lemma adjoin_singleton_eq_top_of_ringEquiv {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra M N] (ψ : L ≃+* N) (φ : K →+* M)
    (h : ∀ k, ψ (algebraMap K L k) = algebraMap M N (φ k)) {x : L}
    (hx : IntermediateField.adjoin K {x} = ⊤) :
    IntermediateField.adjoin M {ψ x} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨v, rfl⟩ := ψ.surjective z
  have hv : v ∈ IntermediateField.adjoin K {x} := hx.ge trivial
  rw [IntermediateField.mem_adjoin_simple_iff] at hv ⊢
  obtain ⟨r, s, hv⟩ := hv
  refine ⟨r.map φ, s.map φ, ?_⟩
  rw [hv, map_div₀]
  congr 1
  · exact map_aeval_eq (ψ := (ψ : L →+* N)) φ x h r
  · exact map_aeval_eq (ψ := (ψ : L →+* N)) φ x h s

/-- If `RatFunc F` is generated over `F` by `u`, then `u` is transcendental over `F`. -/
lemma not_isAlgebraic_of_adjoin_eq_top {F : Type*} [Field F] {u : RatFunc F}
    (hgen : IntermediateField.adjoin F {u} = ⊤) : ¬ IsAlgebraic F u := by
  intro hu
  set E := IntermediateField.adjoin F {u} with hE
  have halg : Algebra.IsAlgebraic F ↥E :=
    (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic F (RatFunc F)).mpr
      (by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hu)
  have hmem : (RatFunc.X : RatFunc F) ∈ E := hgen.ge trivial
  have hX : IsAlgebraic F (⟨(RatFunc.X : RatFunc F), hmem⟩ : ↥E) :=
    Algebra.IsAlgebraic.isAlgebraic _
  have : IsAlgebraic F (RatFunc.X : RatFunc F) := by
    obtain ⟨p, hp, hp0⟩ := hX
    refine ⟨p, hp, ?_⟩
    have h3 := congrArg (algebraMap ↥E (RatFunc F)) hp0
    rw [map_zero] at h3
    rw [← Polynomial.aeval_algebraMap_apply (A := ↥E) (B := RatFunc F)
      (x := (⟨(RatFunc.X : RatFunc F), hmem⟩ : ↥E)) (p := p)] at h3
    simpa using h3
  exact RatFunc.transcendental_X this

/-- The constants of `RatFunc F` are exactly the elements algebraic over `F`. -/
lemma exists_eq_algebraMap_of_isAlgebraic {F : Type*} [Field F] {z : RatFunc F}
    (hz : IsAlgebraic F z) : ∃ x : F, z = algebraMap F (RatFunc F) x := by
  by_contra hc
  push Not at hc
  have hne : ¬ ∃ c, z = RatFunc.C c := by
    rintro ⟨c, hc'⟩
    exact hc c (by simpa [RatFunc.algebraMap_eq_C] using hc')
  exact (RatFunc.transcendental_of_ne_C z hne) hz

end RatFuncCancel

open RatFuncCancel

/-- **Audit node C4.**  A `𝕜`-algebra isomorphism of rational function fields
`RatFunc F₁ ≃ RatFunc F₂` which sends the constants of `RatFunc F₁` into the constants of
`RatFunc F₂` is induced by an isomorphism `F₁ ≃ₐ[𝕜] F₂` of the base fields. -/
theorem algEquiv_ratFunc_cancel {𝕜 F₁ F₂ : Type*} [Field 𝕜] [Field F₁] [Field F₂]
    [Algebra 𝕜 F₁] [Algebra 𝕜 F₂]
    (e : RatFunc F₁ ≃ₐ[𝕜] RatFunc F₂)
    (h : ∀ x : F₁, ∃ y : F₂,
      e (algebraMap F₁ (RatFunc F₁) x) = algebraMap F₂ (RatFunc F₂) y) :
    Nonempty (F₁ ≃ₐ[𝕜] F₂) := by
  classical
  choose φ hφ using h
  have hC₁ : Function.Injective (algebraMap F₁ (RatFunc F₁)) := by
    simpa [RatFunc.algebraMap_eq_C] using (RatFunc.C_injective (K := F₁))
  have hC₂ : Function.Injective (algebraMap F₂ (RatFunc F₂)) := by
    simpa [RatFunc.algebraMap_eq_C] using (RatFunc.C_injective (K := F₂))
  -- the values of `φ` are uniquely determined, so `φ` is a ring homomorphism
  have huniq : ∀ x y, e (algebraMap F₁ (RatFunc F₁) x) = algebraMap F₂ (RatFunc F₂) y →
      y = φ x := by
    intro x y hy
    exact hC₂ (by rw [← hy, hφ x])
  let φa : F₁ →ₐ[𝕜] F₂ :=
    { toFun := φ
      map_one' := (huniq 1 1 (by simp)).symm
      map_mul' := fun a b => (huniq (a * b) (φ a * φ b)
        (by rw [map_mul, map_mul, hφ a, hφ b, map_mul])).symm
      map_zero' := (huniq 0 0 (by simp)).symm
      map_add' := fun a b => (huniq (a + b) (φ a + φ b)
        (by rw [map_add, map_add, hφ a, hφ b, map_add])).symm
      commutes' := fun c => (huniq (algebraMap 𝕜 F₁ c) (algebraMap 𝕜 F₂ c) (by
        rw [← IsScalarTower.algebraMap_apply 𝕜 F₁ (RatFunc F₁), AlgEquiv.commutes,
          IsScalarTower.algebraMap_apply 𝕜 F₂ (RatFunc F₂)])).symm }
  have hφa_inj : Function.Injective φa := by
    intro x y hxy
    have hxy' : φ x = φ y := hxy
    exact hC₁ (e.injective (by rw [hφ x, hφ y, hxy']))
  -- surjectivity
  have hsurj : Function.Surjective φa := by
    intro y
    by_contra hy
    push Not at hy
    set z : RatFunc F₁ := e.symm (algebraMap F₂ (RatFunc F₂) y) with hz
    have hze : e z = algebraMap F₂ (RatFunc F₂) y := by rw [hz]; simp
    -- the `F₁`-subfield of elements mapping to constants of `RatFunc F₂`
    let K₂ : Subfield (RatFunc F₂) := (⊥ : IntermediateField F₂ (RatFunc F₂)).toSubfield
    let D : Subfield (RatFunc F₁) := K₂.comap (e : RatFunc F₁ →+* RatFunc F₂)
    have hD : ∀ c : F₁, algebraMap F₁ (RatFunc F₁) c ∈ D := by
      intro c
      rw [Subfield.mem_comap]
      simp only [K₂, IntermediateField.mem_toSubfield, IntermediateField.mem_bot]
      exact ⟨φ c, (hφ c).symm⟩
    let D' : IntermediateField F₁ (RatFunc F₁) := D.toIntermediateField hD
    have hzmem : z ∈ D' := by
      show z ∈ D
      rw [Subfield.mem_comap]
      simp only [K₂, IntermediateField.mem_toSubfield, IntermediateField.mem_bot]
      exact ⟨y, hze.symm⟩
    have hD'_ne : D' ≠ ⊥ := by
      intro hbot
      have hzbot : z ∈ (⊥ : IntermediateField F₁ (RatFunc F₁)) := hbot ▸ hzmem
      rw [IntermediateField.mem_bot] at hzbot
      obtain ⟨x, hx⟩ := hzbot
      exact hy x (huniq x y (by rw [hx, hze])).symm
    -- `X₁` is algebraic over `D'`, since `D'` is a nontrivial intermediate field
    have hX₁alg : IsAlgebraic ↥D' (RatFunc.X : RatFunc F₁) :=
      RatFunc.IntermediateField.isAlgebraic_X hD'_ne
    -- the induced map `D' → F₂` on the constants
    have hex : ∀ d : ↥D', ∃ c : F₂, algebraMap F₂ (RatFunc F₂) c = e (d : RatFunc F₁) := by
      intro d
      have hd : e (d : RatFunc F₁) ∈ (⊥ : IntermediateField F₂ (RatFunc F₂)) := d.2
      rw [IntermediateField.mem_bot] at hd
      obtain ⟨c, hc⟩ := hd
      exact ⟨c, hc⟩
    choose ψ hψ using hex
    have hψinj : Function.Injective ψ := by
      intro a b hab
      apply Subtype.ext
      apply e.injective
      rw [← hψ a, ← hψ b, hab]
    have h1 : ψ 1 = 1 := by
      refine hC₂ ?_
      rw [map_one, hψ 1]
      simp
    have hmul : ∀ a b : ↥D', ψ (a * b) = ψ a * ψ b := by
      intro a b
      refine hC₂ ?_
      rw [map_mul, hψ a, hψ b, hψ (a * b)]
      simp
    have h0 : ψ 0 = 0 := by
      refine hC₂ ?_
      rw [map_zero, hψ 0]
      simp
    have hadd : ∀ a b : ↥D', ψ (a + b) = ψ a + ψ b := by
      intro a b
      refine hC₂ ?_
      rw [map_add, hψ a, hψ b, hψ (a + b)]
      simp
    let ψr : ↥D' →+* F₂ :=
      { toFun := ψ, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }
    have hcomp : ∀ d : ↥D', e (algebraMap ↥D' (RatFunc F₁) d)
        = algebraMap F₂ (RatFunc F₂) (ψr d) := by
      intro d
      rw [IntermediateField.algebraMap_apply]
      exact (hψ d).symm
    -- transport: `u = e X₁` is algebraic over `F₂`
    have htr : IsAlgebraic F₂ ((e : RatFunc F₁ →+* RatFunc F₂) (RatFunc.X : RatFunc F₁)) :=
      isAlgebraic_of_ringHom (ψ := (e : RatFunc F₁ →+* RatFunc F₂)) (φ := ψr) hψinj hcomp hX₁alg
    -- but `u` generates `RatFunc F₂` over `F₂`, so `u` must be transcendental
    have hgen : IntermediateField.adjoin F₂
        {(e.toRingEquiv : RatFunc F₁ ≃+* RatFunc F₂) (RatFunc.X : RatFunc F₁)} = ⊤ :=
      adjoin_singleton_eq_top_of_ringEquiv (ψ := (e.toRingEquiv : RatFunc F₁ ≃+* RatFunc F₂))
        (φ := φa.toRingHom) (fun k => hφ k) RatFunc.adjoin_X
    exact (not_isAlgebraic_of_adjoin_eq_top hgen) (by simpa using htr)
  exact ⟨AlgEquiv.ofBijective φa ⟨hφa_inj, hsurj⟩⟩

end Work.MotC
