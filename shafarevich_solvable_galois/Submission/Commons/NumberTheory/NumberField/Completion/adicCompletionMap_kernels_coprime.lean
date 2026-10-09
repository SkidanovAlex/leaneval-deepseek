import Mathlib
import Submission.Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.adicCompletion_residueField_equiv_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField TensorProduct Valued
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
attribute [local instance] Algebra.TensorProduct.rightAlgebra
noncomputable section

open IsDedekindDomain.HeightOneSpectrum
open Commons.RingTheory.Henselian
open Commons.NumberTheory.NumberField

namespace Commons.NumberTheory.NumberField.Completion

/-- An element of the completion has value `1` iff it and its inverse are integral. -/
lemma val_eq_one_iff {M : Type*} [Field M] [NumberField M]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (z : p.adicCompletion M) (hz : z ≠ 0) :
    Valued.v z = (1 : Zstar0) ↔
      z ∈ (p.adicCompletionIntegers M : Set (p.adicCompletion M)) ∧
      z⁻¹ ∈ (p.adicCompletionIntegers M : Set (p.adicCompletion M)) := by
  have hval_ne : Valued.v z ≠ 0 := (Valuation.zero_iff (v := Valued.v)).not.mpr hz
  have hpos : 0 < Valued.v z := pos_iff_ne_zero.mpr hval_ne
  constructor
  · intro h
    constructor
    · exact (mem_adicCompletionIntegers (R := NumberField.RingOfIntegers M) (K := M) p).mpr (by rw [h])
    · exact (mem_adicCompletionIntegers (R := NumberField.RingOfIntegers M) (K := M) p).mpr (by
        rw [map_inv₀ (f := (Valued.v : Valuation (p.adicCompletion M) Zstar0)) z]
        rw [h, inv_one])
  · rintro ⟨h1, h2⟩
    have hle : Valued.v z ≤ 1 := (mem_adicCompletionIntegers (R := NumberField.RingOfIntegers M) (K := M) p).mp h1
    have hinv : Valued.v (z⁻¹) ≤ 1 := (mem_adicCompletionIntegers (R := NumberField.RingOfIntegers M) (K := M) p).mp h2
    have hinv' : (Valued.v z)⁻¹ ≤ 1 := by
      rwa [map_inv₀ (f := (Valued.v : Valuation (p.adicCompletion M) Zstar0)) z] at hinv
    have hge : (1 : Zstar0) ≤ Valued.v z := (inv_le_one₀ (ha := hpos)).mp hinv'
    exact le_antisymm hle hge

/-- An algebraic integer lies in the prime ideal `p` iff its image in the completion has
valuation different from `1`. -/
lemma adicCompletionIntegers_not_val_eq_one_iff_mem_asIdeal {M : Type*} [Field M] [NumberField M]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M)) (r : NumberField.RingOfIntegers M) :
    r ∈ p.asIdeal ↔ ¬ Valued.v (algebraMap M (p.adicCompletion M) (r : M)) = (1 : Zstar0) := by
  have hva : Valued.v (algebraMap M (p.adicCompletion M) (r : M)) = p.valuation M (r : M) := by
    rw [show algebraMap M (p.adicCompletion M) (r : M) = ((r : M) : p.adicCompletion M) from rfl]
    exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := NumberField.RingOfIntegers M) (v := p) (r : M)
  have hle1 : Valued.v (algebraMap M (p.adicCompletion M) (r : M)) ≤ (1 : Zstar0) := by
    rw [hva]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one (R := NumberField.RingOfIntegers M) (K := M) p r
  constructor
  · intro hr hval
    have hlt : p.valuation M (r : M) < (1 : Zstar0) := by
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (R := NumberField.RingOfIntegers M) (K := M) p r).mpr hr
    have hval' : p.valuation M (r : M) = (1 : Zstar0) := by simpa [hva] using hval
    exact (ne_of_lt hlt) hval'
  · intro hnot
    have hlt : Valued.v (algebraMap M (p.adicCompletion M) (r : M)) < (1 : Zstar0) := lt_of_le_of_ne hle1 hnot
    have hlt' : p.valuation M (r : M) < (1 : Zstar0) := by rwa [hva] at hlt
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (R := NumberField.RingOfIntegers M) (K := M) p r).mp hlt'

/-- The kernels of the canonical surjections from `L ⊗_K (Q.adicCompletion K)` onto the
completions of `L` at two DIFFERENT primes over `Q` are comaximal.

Let `K ⊆ L` be number fields, `Q` a height-one prime of the ring of integers of `K`, and
`q1 ≠ q2` two height-one primes of the ring of integers of `L` both lying over `Q`; let
`φᵢ : (L ⊗[K] Q.adicCompletion K) →+* qᵢ.adicCompletion L` be the canonical surjective
`K_Q`-algebra homomorphisms obtained from
`Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon Q qᵢ hqᵢ`.
Then `RingHom.ker φ₁` and `RingHom.ker φ₂` are coprime ideals of the `K_Q`-algebra
`L ⊗[K] Q.adicCompletion K` (`IsCoprime` in the semiring of ideals).

*Proof recipe (ingredients in Mathlib / commons).*
1. `mᵢ := RingHom.ker φᵢ` is a maximal ideal (`RingHom.ker_isMaximal_of_surjective`).
2. Distinct maximal ideals are comaximal: `Ideal.IsMaximal.coprime_of_ne` gives `m₁ ⊔ m₂ = ⊤`,
   and `Ideal.isCoprime_iff_codisjoint` turns this into `IsCoprime m₁ m₂`; so show `m₁ ≠ m₂`.
3. Suppose `m₁ = m₂`. Let `F := Q.adicCompletion K`, `V := L ⊗[K] F` (F-module via
   `Algebra.TensorProduct.rightAlgebra`, activated with
   `attribute [local instance] Algebra.TensorProduct.rightAlgebra`). Build quotient F-algebra
   isomorphisms `ψᵢ : (V ⧸ m₁) ≃ₐ[F] qᵢ.adicCompletion L` from `AlgEquiv.ofBijective` of the
   algebra hom `V ⧸ m₁ →ₐ[F] qᵢ.adicCompletion L := AlgHom.mk (RingHom.kerLift φᵢ) commutes`
   (codomain algebra `RingHom.toAlgebra (adicCompletionMap Q qᵢ hqᵢ)`, `commutes'` from
   `adicCompletionMap_apply`). Then `θ := (ψ₁.symm).trans ψ₂` satisfies
   `θ (algebraMap L (q₁.adicCompletion L) l) = algebraMap L (q₂.adicCompletion L) l` for all
   `l : L` (both equal `ψᵢ` on the class of `l ⊗ₜ[K] 1`; well-defined since `m₂ = m₁`).
4. Hence `t ∈ q₁.asIdeal ↔ t ∈ q₂.asIdeal` for all `t : 𝓞 L`: use
   `t ∈ q.asIdeal ↔ σ_q t ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)` with
   `σ_q t := algebraMap (𝓞 L) (q.adicCompletionIntegers L) t` (via `Valued.v` values `< 1`,
   `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation`,
   `valuation_lt_one_iff_mem`), and `θ` preserves the integer rings and their maximal ideals
   (the integer ring of `qᵢ.adicCompletion L` is the closure of the image of `𝓞 L` --
   `Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers` -- and
   `θ` is continuous as a linear equivalence of finite-dimensional spaces over the complete
   field `F`; alternatively use integral closures).
5. Extensionality gives `q₁.asIdeal = q₂.asIdeal`, contradicting `hne`. -/
theorem adicCompletionMap_kernels_coprime
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q1 q2 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq1 : q1.asIdeal.LiesOver Q.asIdeal) (hq2 : q2.asIdeal.LiesOver Q.asIdeal)
    (hne : q1.asIdeal ≠ q2.asIdeal) :
    IsCoprime (RingHom.ker
        (Classical.choose
          (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon Q q1 hq1)))
      (RingHom.ker
        (Classical.choose
          (Commons.RingTheory.Henselian.exists_surjective_ringHom_tensor_completion_canon Q q2 hq2))) := by
  classical
  let F := Q.adicCompletion K
  let V := L ⊗[K] F
  let φ1 : V →+* q1.adicCompletion L := Classical.choose (exists_surjective_ringHom_tensor_completion_canon Q q1 hq1)
  let φ2 : V →+* q2.adicCompletion L := Classical.choose (exists_surjective_ringHom_tensor_completion_canon Q q2 hq2)
  have hφ1 : Function.Surjective φ1 := (Classical.choose_spec (exists_surjective_ringHom_tensor_completion_canon Q q1 hq1)).1
  have hφ2 : Function.Surjective φ2 := (Classical.choose_spec (exists_surjective_ringHom_tensor_completion_canon Q q2 hq2)).1
  have hφ1f : ∀ (l : L) (f0 : F), φ1 (l ⊗ₜ[K] f0) =
      (algebraMap L (q1.adicCompletion L) l) * (adicCompletionMap Q q1 hq1 f0) :=
    (Classical.choose_spec (exists_surjective_ringHom_tensor_completion_canon Q q1 hq1)).2
  have hφ2f : ∀ (l : L) (f0 : F), φ2 (l ⊗ₜ[K] f0) =
      (algebraMap L (q2.adicCompletion L) l) * (adicCompletionMap Q q2 hq2 f0) :=
    (Classical.choose_spec (exists_surjective_ringHom_tensor_completion_canon Q q2 hq2)).2
  have hker_max1 : (RingHom.ker φ1).IsMaximal := by
    exact RingHom.ker_isMaximal_of_surjective φ1 hφ1
  have hker_max2 : (RingHom.ker φ2).IsMaximal := by
    exact RingHom.ker_isMaximal_of_surjective φ2 hφ2
  have hker_ne : RingHom.ker φ1 ≠ RingHom.ker φ2 := by
    intro hm
    -- ==== under the assumption the kernels agree, derive q1 = q2 ====
    letI : Algebra F (q1.adicCompletion L) := RingHom.toAlgebra (adicCompletionMap Q q1 hq1)
    letI : Algebra F (q2.adicCompletion L) := RingHom.toAlgebra (adicCompletionMap Q q2 hq2)
    have hφ1c : ∀ f0 : F, φ1 (algebraMap F V f0) = adicCompletionMap Q q1 hq1 f0 := by
      intro f0
      rw [Algebra.TensorProduct.right_algebraMap_apply (R := K) (A := L) (B := F) f0]
      rw [hφ1f (1 : L) f0]
      simp
    have hφ2c : ∀ f0 : F, φ2 (algebraMap F V f0) = adicCompletionMap Q q2 hq2 f0 := by
      intro f0
      rw [Algebra.TensorProduct.right_algebraMap_apply (R := K) (A := L) (B := F) f0]
      rw [hφ2f (1 : L) f0]
      simp
    let ψq1 : (V ⧸ RingHom.ker φ1) →ₐ[F] q1.adicCompletion L :=
      AlgHom.mk (RingHom.kerLift φ1) (by
        intro r
        change (RingHom.kerLift φ1) (Ideal.Quotient.mk (RingHom.ker φ1) (algebraMap F V r)) =
          adicCompletionMap Q q1 hq1 r
        rw [RingHom.kerLift_mk]
        exact hφ1c r)
    have hbij1 : Function.Bijective ⇑ψq1 := by
      constructor
      · exact RingHom.kerLift_injective φ1
      · intro y
        rcases hφ1 y with ⟨a, ha⟩
        refine ⟨Ideal.Quotient.mk (RingHom.ker φ1) a, ?_⟩
        change (RingHom.kerLift φ1) (Ideal.Quotient.mk (RingHom.ker φ1) a) = y
        rw [RingHom.kerLift_mk]
        exact ha
    let e1 : (V ⧸ RingHom.ker φ1) ≃ₐ[F] q1.adicCompletion L := AlgEquiv.ofBijective ψq1 hbij1
    let ψq2 : (V ⧸ RingHom.ker φ2) →ₐ[F] q2.adicCompletion L :=
      AlgHom.mk (RingHom.kerLift φ2) (by
        intro r
        change (RingHom.kerLift φ2) (Ideal.Quotient.mk (RingHom.ker φ2) (algebraMap F V r)) =
          adicCompletionMap Q q2 hq2 r
        rw [RingHom.kerLift_mk]
        exact hφ2c r)
    have hbij2 : Function.Bijective ⇑ψq2 := by
      constructor
      · exact RingHom.kerLift_injective φ2
      · intro y
        rcases hφ2 y with ⟨a, ha⟩
        refine ⟨Ideal.Quotient.mk (RingHom.ker φ2) a, ?_⟩
        change (RingHom.kerLift φ2) (Ideal.Quotient.mk (RingHom.ker φ2) a) = y
        rw [RingHom.kerLift_mk]
        exact ha
    let e2 : (V ⧸ RingHom.ker φ2) ≃ₐ[F] q2.adicCompletion L := AlgEquiv.ofBijective ψq2 hbij2
    let e2' : (V ⧸ RingHom.ker φ1) ≃ₐ[F] q2.adicCompletion L :=
      (Ideal.quotientEquivAlgOfEq F hm).trans e2
    let θ : q1.adicCompletion L ≃ₐ[F] q2.adicCompletion L := (e1.symm).trans e2'
    have hθ_l : ∀ l : L, θ (algebraMap L (q1.adicCompletion L) l) = algebraMap L (q2.adicCompletion L) l := by
      intro l
      have hmain1 : e1 (Ideal.Quotient.mk (RingHom.ker φ1) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q1.adicCompletion L) l := by
        change (AlgEquiv.ofBijective ψq1 hbij1) (Ideal.Quotient.mk (RingHom.ker φ1) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q1.adicCompletion L) l
        change ψq1 (Ideal.Quotient.mk (RingHom.ker φ1) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q1.adicCompletion L) l
        change (RingHom.kerLift φ1) (Ideal.Quotient.mk (RingHom.ker φ1) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q1.adicCompletion L) l
        rw [RingHom.kerLift_mk]
        rw [hφ1f l (1 : F)]
        simp
      have h1 : (e1.symm) (algebraMap L (q1.adicCompletion L) l) = Ideal.Quotient.mk (RingHom.ker φ1) (l ⊗ₜ[K] (1 : F)) := by
        apply e1.injective
        have hs : e1 ((e1.symm) (algebraMap L (q1.adicCompletion L) l)) = algebraMap L (q1.adicCompletion L) l := by simp
        rw [hs, hmain1]
      have h2 : e2' (Ideal.Quotient.mk (RingHom.ker φ1) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q2.adicCompletion L) l := by
        change e2 (Ideal.Quotient.mk (RingHom.ker φ2) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q2.adicCompletion L) l
        change (AlgEquiv.ofBijective ψq2 hbij2) (Ideal.Quotient.mk (RingHom.ker φ2) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q2.adicCompletion L) l
        change ψq2 (Ideal.Quotient.mk (RingHom.ker φ2) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q2.adicCompletion L) l
        change (RingHom.kerLift φ2) (Ideal.Quotient.mk (RingHom.ker φ2) (l ⊗ₜ[K] (1 : F))) = algebraMap L (q2.adicCompletion L) l
        rw [RingHom.kerLift_mk]
        rw [hφ2f l (1 : F)]
        simp
      calc
        θ (algebraMap L (q1.adicCompletion L) l)
            = e2' (e1.symm (algebraMap L (q1.adicCompletion L) l)) := rfl
        _ = e2' (Ideal.Quotient.mk (RingHom.ker φ1) (l ⊗ₜ[K] (1 : F))) := by rw [h1]
        _ = algebraMap L (q2.adicCompletion L) l := h2
    -- continuity
    haveI : Module.Finite F (q1.adicCompletion L) := module_finite_adicCompletion Q q1 hq1
    haveI : Module.Finite F (q2.adicCompletion L) := module_finite_adicCompletion Q q2 hq2
    have hc1 : Continuous (algebraMap F (q1.adicCompletion L)) := by
      change Continuous (adicCompletionMap Q q1 hq1 : F → q1.adicCompletion L)
      exact adicCompletionMap_continuous Q q1 hq1
    haveI : ContinuousSMul F (q1.adicCompletion L) := continuousSMul_of_algebraMap F (q1.adicCompletion L) hc1
    have hc2 : Continuous (algebraMap F (q2.adicCompletion L)) := by
      change Continuous (adicCompletionMap Q q2 hq2 : F → q2.adicCompletion L)
      exact adicCompletionMap_continuous Q q2 hq2
    haveI : ContinuousSMul F (q2.adicCompletion L) := continuousSMul_of_algebraMap F (q2.adicCompletion L) hc2
    haveI : T2Space (q1.adicCompletion L) := (R1Space.t2Space_iff_t0Space (X := q1.adicCompletion L)).mpr inferInstance
    haveI : T2Space (q2.adicCompletion L) := (R1Space.t2Space_iff_t0Space (X := q2.adicCompletion L)).mpr inferInstance
    have hcontθ : Continuous (θ : q1.adicCompletion L → q2.adicCompletion L) := by
      exact (θ : q1.adicCompletion L →ₗ[F] q2.adicCompletion L).continuous_of_finiteDimensional
    have hcontθi : Continuous (θ.symm : q2.adicCompletion L → q1.adicCompletion L) := by
      exact (θ.symm : q2.adicCompletion L →ₗ[F] q1.adicCompletion L).continuous_of_finiteDimensional
    -- integer rings as closures of images of 𝓞L
    let S1 : Set (q1.adicCompletion L) := {y | ∃ r : 𝓞 L, (algebraMap L (q1.adicCompletion L) (r : L)) = y}
    let S2 : Set (q2.adicCompletion L) := {y | ∃ r : 𝓞 L, (algebraMap L (q2.adicCompletion L) (r : L)) = y}
    let R1 : Set (q1.adicCompletion L) := (q1.adicCompletionIntegers L : Set (q1.adicCompletion L))
    let R2 : Set (q2.adicCompletion L) := (q2.adicCompletionIntegers L : Set (q2.adicCompletion L))
    have hS1mem : S1 ⊆ R1 := by
      rintro y ⟨r, rfl⟩
      exact (mem_adicCompletionIntegers (R := 𝓞 L) (K := L) q1).mpr (by
        change Valued.v ((r : L) : q1.adicCompletion L) ≤ (1 : Zstar0)
        rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (v := q1) (r : L)]
        exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one (R := 𝓞 L) (K := L) q1 r)
    have hS2mem : S2 ⊆ R2 := by
      rintro y ⟨r, rfl⟩
      exact (mem_adicCompletionIntegers (R := 𝓞 L) (K := L) q2).mpr (by
        change Valued.v ((r : L) : q2.adicCompletion L) ≤ (1 : Zstar0)
        rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (v := q2) (r : L)]
        exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one (R := 𝓞 L) (K := L) q2 r)
    have hclosedR1 : IsClosed R1 := by
      dsimp [R1]
      exact Valued.isClosed_valuationSubring (q1.adicCompletion L)
    have hclosedR2 : IsClosed R2 := by
      dsimp [R2]
      exact Valued.isClosed_valuationSubring (q2.adicCompletion L)
    have hcl1 : closure S1 = R1 := by
      apply le_antisymm
      · exact closure_minimal hS1mem hclosedR1
      · intro x hx
        exact ringOfIntegers_dense_in_adicIntegers L q1 ⟨x, by simpa [R1] using hx⟩
    have hcl2 : closure S2 = R2 := by
      apply le_antisymm
      · exact closure_minimal hS2mem hclosedR2
      · intro x hx
        exact ringOfIntegers_dense_in_adicIntegers L q2 ⟨x, by simpa [R2] using hx⟩
    have hθS : θ '' S1 = S2 := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with ⟨r, hr⟩
        refine ⟨r, ?_⟩
        calc
          algebraMap L (q2.adicCompletion L) (r : L) = θ (algebraMap L (q1.adicCompletion L) (r : L)) := (hθ_l (r : L)).symm
          _ = θ x := by rw [hr]
      · rintro ⟨r, rfl⟩
        refine ⟨algebraMap L (q1.adicCompletion L) (r : L), ⟨r, rfl⟩, ?_⟩
        exact hθ_l (r : L)
    have hθR_forward : θ '' R1 ⊆ R2 := by
      rintro y ⟨x, hxR1, rfl⟩
      have hy1 : θ x ∈ θ '' closure S1 := Set.mem_image_of_mem θ (by rwa [hcl1])
      have hy2 : θ x ∈ closure (θ '' S1) := image_closure_subset_closure_image hcontθ hy1
      rwa [hθS, hcl2] at hy2
    have hθSrev : θ.symm '' S2 = S1 := by
      ext x; constructor
      · rintro ⟨y, hyS2, rfl⟩
        rcases hyS2 with ⟨r, hr⟩
        refine ⟨r, ?_⟩
        calc
          algebraMap L (q1.adicCompletion L) (r : L) = θ.symm (algebraMap L (q2.adicCompletion L) (r : L)) := by
            rw [← hθ_l (r : L)]
            simp
          _ = θ.symm y := by rw [hr]
      · rintro ⟨r, rfl⟩
        refine ⟨algebraMap L (q2.adicCompletion L) (r : L), ⟨r, rfl⟩, ?_⟩
        rw [← hθ_l (r : L)]
        simp
    have hθR_back : θ.symm '' R2 ⊆ R1 := by
      rintro x ⟨y, hyR2, rfl⟩
      have hy1 : θ.symm y ∈ θ.symm '' closure S2 := Set.mem_image_of_mem θ.symm (by rwa [hcl2])
      have hy2 : θ.symm y ∈ closure (θ.symm '' S2) := image_closure_subset_closure_image hcontθi hy1
      rwa [hθSrev, hcl1] at hy2
    have hθR_eq : θ '' R1 = R2 := by
      apply le_antisymm
      · exact hθR_forward
      · intro y hyR2
        refine ⟨θ.symm y, ?_, ?_⟩
        · exact hθR_back (Set.mem_image_of_mem θ.symm hyR2)
        · simp

    have hmem1 : ∀ z : q1.adicCompletion L, z ∈ R1 ↔ Valued.v z ≤ (1 : Zstar0) := by
      intro z; rfl
    have hmem2 : ∀ z : q2.adicCompletion L, z ∈ R2 ↔ Valued.v z ≤ (1 : Zstar0) := by
      intro z; rfl
    have hθmem : ∀ z : q1.adicCompletion L, z ∈ R1 ↔ θ z ∈ R2 := by
      intro z; constructor
      · intro hz
        have h1 : θ z ∈ θ '' R1 := Set.mem_image_of_mem θ hz
        rwa [hθR_eq] at h1
      · intro hz2
        have h1 : θ.symm (θ z) ∈ θ.symm '' R2 := Set.mem_image_of_mem θ.symm hz2
        have h2 : θ.symm (θ z) ∈ R1 := hθR_back h1
        simpa using h2

    -- membership of the integer ring
    have hmem1 : ∀ z : q1.adicCompletion L, z ∈ R1 ↔ Valued.v z ≤ (1 : Zstar0) := by
      intro z
      exact (mem_adicCompletionIntegers (R := 𝓞 L) (K := L) q1)
    have hmem2 : ∀ z : q2.adicCompletion L, z ∈ R2 ↔ Valued.v z ≤ (1 : Zstar0) := by
      intro z
      exact (mem_adicCompletionIntegers (R := 𝓞 L) (K := L) q2)
    have hθmem : ∀ z : q1.adicCompletion L, z ∈ R1 ↔ θ z ∈ R2 := by
      intro z; constructor
      · intro hz
        have h1 : θ z ∈ θ '' R1 := Set.mem_image_of_mem θ hz
        rwa [hθR_eq] at h1
      · intro hz2
        have h1 : θ.symm (θ z) ∈ θ.symm '' R2 := Set.mem_image_of_mem θ.symm hz2
        have h2 : θ.symm (θ z) ∈ R1 := hθR_back h1
        simpa using h2
    have hθinv : ∀ x : q1.adicCompletion L, x ≠ 0 → θ (x⁻¹) = (θ x)⁻¹ := by
      intro x hx
      exact map_inv₀ (f := (θ : q1.adicCompletion L →+* q2.adicCompletion L)) x
    have hvalOne_transfer : ∀ x : q1.adicCompletion L, Valued.v x = (1 : Zstar0) ↔ Valued.v (θ x) = (1 : Zstar0) := by
      intro x
      by_cases hx0 : x = 0
      · subst x
        simp
      · have hθne : θ x ≠ 0 := by
          intro hθx
          have hθx' : θ x = θ (0 : q1.adicCompletion L) := by simpa using hθx
          exact hx0 (θ.injective hθx')
        calc
          Valued.v x = (1 : Zstar0) ↔ x ∈ R1 ∧ x⁻¹ ∈ R1 := val_eq_one_iff q1 x hx0
          _ ↔ θ x ∈ R2 ∧ θ (x⁻¹) ∈ R2 := by rw [hθmem x, hθmem (x⁻¹)]
          _ ↔ θ x ∈ R2 ∧ (θ x)⁻¹ ∈ R2 := by rw [hθinv x hx0]
          _ ↔ Valued.v (θ x) = (1 : Zstar0) := (val_eq_one_iff q2 (θ x) hθne).symm
    have hmain : ∀ t : 𝓞 L, t ∈ q1.asIdeal ↔ t ∈ q2.asIdeal := by
      intro t
      rw [adicCompletionIntegers_not_val_eq_one_iff_mem_asIdeal q1 t,
          adicCompletionIntegers_not_val_eq_one_iff_mem_asIdeal q2 t]
      apply not_congr
      have htr := hvalOne_transfer (algebraMap L (q1.adicCompletion L) (t : L))
      simpa [hθ_l (t : L)] using htr
    have hqeq : q1.asIdeal = q2.asIdeal := by
      apply Ideal.ext
      intro t
      exact hmain t
    exact (hne hqeq)
  haveI : (RingHom.ker φ1).IsMaximal := hker_max1
  haveI : (RingHom.ker φ2).IsMaximal := hker_max2
  exact Ideal.isCoprime_of_isMaximal hker_ne
end Commons.NumberTheory.NumberField.Completion
