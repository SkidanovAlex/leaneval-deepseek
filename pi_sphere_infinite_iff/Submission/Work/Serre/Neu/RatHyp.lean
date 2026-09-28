-- PORTED COPY (neutral island) of `Submission/Work/Serre/ratHypotheses.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.Defs
import Submission.Work.Serre.relCohRat_dual
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.StemsB.CollarRat
import Submission.Work.StemsB.FieldDualUCT

/-!
# The rational hypotheses of the Serre pair argued in integral homology

This file proves `Work.Serre.ratHypotheses`, the "input dictionary" of the Serre spectral
sequence computation: given a pair `(X,A)` whose **rational** relative cohomology vanishes in
degrees `0 < n ≤ N+1`, `n ≠ r+1`, is trivial in degree `0`, and is a line in degree `r+1`, one can
choose an integral relative cycle `z` in degree `r+1`, non-zero, which rationally generates the
degree-`r+1` integral relative homology and detects the torsion of the other degrees:

* `H_j(X,A;ℤ) ⊗ ℚ` is trivial for `j ≤ N+1`, `j ≠ r+1`;
* for every `w ∈ H_{r+1}(X,A;ℤ)` there are `n > 0` and `m : ℤ` with
  `(n • w) ⊗ 1 = (m • [z]) ⊗ 1` in `H_{r+1}(X,A;ℤ) ⊗ ℚ`.

The bridge between the hypotheses (which are about cohomology over `ℚ`) and the conclusion (which
is about integral homology) is the universal coefficient theorem over the field `ℚ` in the form
`Work.Serre.relCohRat_dual`:
`Hⁿ(X,A;ℚ) ≅ Hom_ℤ(Hₙ(X,A;ℤ), ℚ)`, together with the elementary fact that a `ℚ`-vector space
with trivial `ℚ`-dual is trivial, and the fact that the base change `- ⊗[ℤ] ℚ` is
`ModuleCat.extendScalars (ℤ → ℚ)` (`Work.StemsB.IntRatF`), whose carrier is `ℚ ⊗[ℤ] Hₙ`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Work.Serre

noncomputable section

/-! ## Elementary linear algebra over `ℚ` -/

/-- **A `ℚ`-vector space with trivial `ℚ`-dual is trivial.**  Over a field a non-zero vector admits
a linear functional which does not kill it (`Module.Projective.exists_dual_ne_zero`). -/
theorem subsingleton_of_subsingleton_dual_Q {V : Type*} [AddCommGroup V] [Module ℚ V]
    (h : Subsingleton (V →ₗ[ℚ] ℚ)) : Subsingleton V := by
  rw [subsingleton_iff] at h ⊢
  intro x y
  by_contra hxy
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (V := V) ℚ (x := x - y)
    (sub_ne_zero.mpr hxy)
  exact hf (by rw [h f 0, LinearMap.zero_apply])

/-- **The dual of a line is a line.**  If the `ℚ`-dual of `V` is one-dimensional, so is `V`: this
is the identity `finrank K (Dual K V) = finrank K V` (`Subspace.dual_finrank_eq`). -/
theorem finrank_one_of_dual_iso_rat {V : Type*} [AddCommGroup V] [Module ℚ V]
    (h : Nonempty ((V →ₗ[ℚ] ℚ) ≃ₗ[ℚ] ℚ)) : Module.finrank ℚ V = 1 := by
  obtain ⟨e⟩ := h
  rw [← Subspace.dual_finrank_eq (K := ℚ) (V := V)]
  show Module.finrank ℚ (V →ₗ[ℚ] ℚ) = 1
  rw [e.finrank_eq, Module.finrank_self]

/-- **In a one-dimensional `ℚ`-vector space every element is a multiple of any non-zero
element.** -/
theorem exists_rat_smul_eq_of_finrank_one {V : Type*} [AddCommGroup V] [Module ℚ V]
    (h1 : Module.finrank ℚ V = 1) {u₀ u : V} (hu₀ : u₀ ≠ 0) : ∃ c : ℚ, u = c • u₀ := by
  obtain ⟨v, _hv, hsurj⟩ := (finrank_eq_one_iff' (K := ℚ) (V := V)).mp h1
  obtain ⟨c₀, hc₀⟩ := hsurj u₀
  obtain ⟨c, hc⟩ := hsurj u
  have hc₀' : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₀
    exact hu₀ hc₀.symm
  refine ⟨c * c₀⁻¹, ?_⟩
  have hv' : v = c₀⁻¹ • u₀ := by
    rw [← hc₀, smul_smul, inv_mul_cancel₀ hc₀', one_smul]
  rw [← hc, hv', smul_smul]

/-- **Every rational number is a quotient of an integer by a positive natural number.** -/
theorem exists_nat_int_of_rat (c : ℚ) : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, (n : ℚ) * c = (m : ℚ) := by
  refine ⟨c.den, c.den_pos, c.num, ?_⟩
  have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  have h : (c.num : ℚ) = c * (c.den : ℚ) := by
    have h0 := Rat.num_div_den c
    rw [div_eq_iff hd] at h0
    exact h0
  rw [h, mul_comm]

/-! ## Moving natural and integer multiples across `⊗ₜ`

The tensor product `M ⊗[ℤ] ℚ` is only a `ℤ`-module (its second factor `ℚ` is not used as the
scalar ring, since `ℚ` acts on the *right*), so multiples have to be pushed across the pure tensor
`x ⊗ₜ 1` by hand. -/

/-- `n • (x ⊗ₜ 1) = (n • x) ⊗ₜ 1`, proved by induction on `n` (only the additive structure of the
tensor product is used). -/
theorem nsmul_tmul_one (M : Type*) [AddCommGroup M] [Module ℤ M] (n : ℕ) (x : M) :
    n • (TensorProduct.tmul ℤ x (1 : ℚ)) = TensorProduct.tmul ℤ (n • x) (1 : ℚ) := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, TensorProduct.zero_tmul]
  | succ k ih => rw [succ_nsmul, succ_nsmul, ih, TensorProduct.add_tmul]

/-- `m • (x ⊗ₜ 1) = (m • x) ⊗ₜ 1` for an integer `m`, deduced from the natural case. -/
theorem zsmul_tmul_one (M : Type*) [AddCommGroup M] [Module ℤ M] (m : ℤ) (x : M) :
    m • (TensorProduct.tmul ℤ x (1 : ℚ)) = TensorProduct.tmul ℤ (m • x) (1 : ℚ) := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [natCast_zsmul, natCast_zsmul, nsmul_tmul_one]
  · rw [neg_zsmul, natCast_zsmul, neg_zsmul, natCast_zsmul, nsmul_tmul_one,
      ← TensorProduct.neg_tmul]

/-! ## The main statement -/

/-- **The rational hypotheses of the Serre pair, in integral homology.** -/
theorem ratHypotheses (X : TopCat) (A : Set X) (r N : ℕ)
    (hvan : ∀ n : ℕ, 0 < n → n ≤ N + 1 → n ≠ r + 1 →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.relComplex ℚ X A).homology n))
    (hzero : CategoryTheory.Limits.IsZero ((Work.Cohomology.relComplex ℚ X A).homology 0))
    (hgen : Nonempty ((Work.Cohomology.relComplex ℚ X A).homology (r + 1) ≅
      ModuleCat.of ℚ ℚ)) :
    ∃ z : ↥((Work.Cohomology.relChains X A).cycles (r + 1)), z ≠ 0 ∧
      (∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
        Subsingleton (TensorProduct ℤ
          ↥((Work.Cohomology.relChains X A).homology j) ℚ)) ∧
      (∀ w : ↥((Work.Cohomology.relChains X A).homology (r + 1)),
        ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
          TensorProduct.tmul ℤ (n • w) (1 : ℚ)
            = TensorProduct.tmul ℤ
                (m • ((Work.Cohomology.relChains X A).homologyπ (r + 1)).hom z)
                (1 : ℚ)) := by
  obtain ⟨eC⟩ := hgen
  obtain ⟨eD⟩ := Work.Serre.relCohRat_dual ↥X A (r + 1)
  -- the identification `H^{r+1}(X,A;ℚ) ≅ Hom_ℤ(H_{r+1}(X,A;ℤ), ℚ) ≅ ℚ`
  have e3 : ModuleCat.of ℚ
      (↥((Work.Cohomology.relChains X A).homology (r + 1)) →ₗ[ℤ] ℚ) ≅ ModuleCat.of ℚ ℚ :=
    eD.symm ≪≫ eC
  -- a generator of the one-dimensional space `Hom_ℤ(H_{r+1},ℚ)` and an element it does not kill
  let g : ↥((Work.Cohomology.relChains X A).homology (r + 1)) →ₗ[ℤ] ℚ :=
    e3.toLinearEquiv.symm 1
  have hg : g ≠ 0 := by
    intro hg0
    have h1 : e3.toLinearEquiv g = 1 := LinearEquiv.apply_symm_apply e3.toLinearEquiv (1 : ℚ)
    rw [hg0, map_zero] at h1
    exact one_ne_zero h1.symm
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, g m₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (LinearMap.ext h)
  -- a cycle representing `m₀`
  have hsurj : Function.Surjective
      ((Work.Cohomology.relChains X A).homologyπ (r + 1)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, hz⟩ := hsurj m₀
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 : m₀ = 0 := by rw [← hz, h0, map_zero]
    exact hm₀ (by rw [h1, map_zero])
  refine ⟨z, hz0, ?_, ?_⟩
  · -- the vanishing degrees: cohomology `0` gives trivial `ℚ`-dual, hence trivial rationalisation
    intro j hjle hjne
    have key : IsZero ((Work.Cohomology.relComplex ℚ X A).homology j) := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; exact hzero
      · exact hvan j hpos hjle hjne
    obtain ⟨e⟩ := Work.Serre.relCohRat_dual ↥X A j
    have h1 : IsZero (ModuleCat.of ℚ
        (↥((Work.Cohomology.relChains X A).homology j) →ₗ[ℤ] ℚ)) := key.of_iso e.symm
    have h2 : Subsingleton (↥((Work.Cohomology.relChains X A).homology j) →ₗ[ℤ] ℚ) :=
      ModuleCat.isZero_iff_subsingleton.mp h1
    -- `Hom_ℤ(M,ℚ) ≅ Hom_ℚ(ℚ ⊗[ℤ] M, ℚ)`
    have h3 : Subsingleton (↥(Work.StemsB.IntRatF.obj
        ((Work.Cohomology.relChains X A).homology j)) →ₗ[ℚ] ℚ) :=
      Function.Surjective.subsingleton
        (f := fun x : ↥((Work.Cohomology.relChains X A).homology j) →ₗ[ℤ] ℚ =>
          (Work.Serre.intDual_baseChange ((Work.Cohomology.relChains X A).homology j)).symm x)
        (Work.Serre.intDual_baseChange ((Work.Cohomology.relChains X A).homology j)).symm.surjective
    have h4 : Subsingleton ↥(Work.StemsB.IntRatF.obj
        ((Work.Cohomology.relChains X A).homology j)) :=
      subsingleton_of_subsingleton_dual_Q h3
    have h5 : Subsingleton (TensorProduct ℤ ℚ
        ↥((Work.Cohomology.relChains X A).homology j)) := h4
    -- commute the two tensor factors
    exact Function.Surjective.subsingleton
      (f := fun x : TensorProduct ℤ ℚ ↥((Work.Cohomology.relChains X A).homology j) =>
        (TensorProduct.comm ℤ ↥((Work.Cohomology.relChains X A).homology j) ℚ).symm x)
      (TensorProduct.comm ℤ ↥((Work.Cohomology.relChains X A).homology j) ℚ).symm.surjective
  · -- the detecting element `m₀ ⊗ 1` is non-zero
    obtain ⟨ev, hev⟩ : ∃ ev : TensorProduct ℤ
          ↥((Work.Cohomology.relChains X A).homology (r + 1)) ℚ →ₗ[ℤ] ℚ,
        ∀ (x : ↥((Work.Cohomology.relChains X A).homology (r + 1))) (q : ℚ),
          ev (TensorProduct.tmul ℤ x q) = q * g x :=
      ⟨TensorProduct.lift (LinearMap.mk₂ ℤ (fun x q => q * g x)
        (fun a b q => by rw [map_add, mul_add])
        (fun c m q => by
          rw [LinearMap.map_smul, ← Int.cast_smul_eq_zsmul ℚ c (g m), smul_eq_mul,
            ← Int.cast_smul_eq_zsmul ℚ c (q * g m), smul_eq_mul]; ring)
        (fun a q q' => by rw [add_mul])
        (fun c m q => by
          rw [← Int.cast_smul_eq_zsmul ℚ c q, smul_eq_mul,
            ← Int.cast_smul_eq_zsmul ℚ c (q * g m), smul_eq_mul]; ring)),
        fun x q => rfl⟩
    -- `ℚ ⊗[ℤ] H_{r+1}` is a line: it is the domain of `Hom_ℤ(H_{r+1},ℚ) ≅ ℚ`
    let U := TensorProduct ℤ ℚ ↥((Work.Cohomology.relChains X A).homology (r + 1))
    let u₀ : U := (TensorProduct.comm ℤ
        ↥((Work.Cohomology.relChains X A).homology (r + 1)) ℚ)
      (TensorProduct.tmul ℤ m₀ (1 : ℚ))
    have hu₀ : u₀ ≠ 0 := by
      intro h0
      have hv₀ : TensorProduct.tmul ℤ m₀ (1 : ℚ) ≠ 0 := by
        intro h1
        have h2 := congrArg ev h1
        simp only [hev, map_zero, one_mul] at h2
        exact hm₀ h2
      refine hv₀ ((TensorProduct.comm ℤ _ ℚ).injective (calc
        (TensorProduct.comm ℤ _ ℚ) (TensorProduct.tmul ℤ m₀ (1 : ℚ)) = u₀ := rfl
        _ = 0 := h0
        _ = (TensorProduct.comm ℤ _ ℚ) 0 := (map_zero _).symm))
    have hUline : Nonempty ((U →ₗ[ℚ] ℚ) ≃ₗ[ℚ] ℚ) :=
      ⟨(Work.Serre.intDual_baseChange ((Work.Cohomology.relChains X A).homology (r + 1))).trans
        e3.toLinearEquiv⟩
    have hfin : Module.finrank ℚ U = 1 := finrank_one_of_dual_iso_rat hUline
    intro w
    let uW : U := (TensorProduct.comm ℤ
        ↥((Work.Cohomology.relChains X A).homology (r + 1)) ℚ)
      (TensorProduct.tmul ℤ w (1 : ℚ))
    -- rational proportionality in the line `U`
    obtain ⟨c, hc⟩ := exists_rat_smul_eq_of_finrank_one hfin (u₀ := u₀) (u := uW) hu₀
    obtain ⟨n, hn, m, hnm⟩ := exists_nat_int_of_rat c
    refine ⟨n, hn, m, ?_⟩
    have key : n • uW = m • u₀ := by
      rw [hc, ← Nat.cast_smul_eq_nsmul ℚ n (c • u₀), smul_smul, hnm, Int.cast_smul_eq_zsmul]
    have key2 : n • (TensorProduct.tmul ℤ w (1 : ℚ))
        = m • (TensorProduct.tmul ℤ m₀ (1 : ℚ)) := by
      have h2 := congrArg (TensorProduct.comm ℤ
        ↥((Work.Cohomology.relChains X A).homology (r + 1)) ℚ).symm key
      simpa only [uW, u₀, LinearEquiv.symm_apply_apply, map_nsmul, map_zsmul] using h2
    have key3 : TensorProduct.tmul ℤ (n • w) (1 : ℚ)
        = TensorProduct.tmul ℤ (m • m₀) (1 : ℚ) := by
      calc TensorProduct.tmul ℤ (n • w) (1 : ℚ)
          = n • (TensorProduct.tmul ℤ w (1 : ℚ)) := (nsmul_tmul_one _ n w).symm
        _ = m • (TensorProduct.tmul ℤ m₀ (1 : ℚ)) := key2
        _ = TensorProduct.tmul ℤ (m • m₀) (1 : ℚ) := zsmul_tmul_one _ m m₀
    rw [hz]
    exact key3

end

end Work.Serre
