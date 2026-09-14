import Mathlib
import Submission.Vdw.BlockNorm
import Submission.Vdw.Height
import Submission.Vdw.Counting
import Submission.Vdw.BlockPolyComplex
import Submission.Commons.Analysis.Polynomial.mahlerMeasure_prod
import Submission.Commons.Analysis.Polynomial.one_le_mahlerMeasure_of_monic
import Submission.Commons.NumberTheory.NumberField.mahlerK_eq_prod_algHom
import Submission.Commons.NumberTheory.NumberField.mahlerK_algEquiv
import Submission.Commons.NumberTheory.NumberField.card_algHom_eq_finrank

open Polynomial
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# The Mahler bounds for the imprimitive slice

For a monic box polynomial `f ∈ Box n H` with a block `B` of the naive Galois
action, the field of definition `L = blockField p hsep B` (`p = f.map φℚ`),
the block polynomial `P_L = spolyL p hsep B` (monic of degree `|B|`) and its
coefficients `c_i`, the Mahler measure of `L` (at the infinite places) of every
`c_i` is bounded by `2^(|B|·[L:ℚ]) · M(f_ℂ)`:

* `mahlerK_eq_prod_algHom` turns `mahlerK L c_i` into a product over the
  complex embeddings of `L`;
* each `‖χ c_i‖` is a coefficient of the conjugate polynomial `P_L^χ`, bounded
  by `choose(|B|,i)·M(P_L^χ) ≤ 2^|B|·M(P_L^χ)`;
* the product `∏_χ P_L^χ` is `p.map (algebraMap ℚ ℂ)` (`normIdentity`) and the
  Mahler measure is multiplicative (`mahlerMeasure_prod`).

Almost the same argument bounds `mahlerK L γ` for the generator
`γ = Σ_i μ_i c_i` of `L`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## Height and Mahler measure of a box polynomial -/

lemma polyHeight_le_of_mem_Box {n H : ℕ} {f : ℤ[X]} (hf : f ∈ Box n H) :
    polyHeight f ≤ max H 1 := by
  rw [polyHeight]
  refine Finset.sup_le ?_
  intro i hi
  have hne : f.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  have hsplit : i ≤ n := by
    have hdeg : f.natDegree = n := by
      rw [← Polynomial.natDegree_eq_of_degree_eq_some hf.2.1]
    have := Polynomial.le_natDegree_of_ne_zero hne
    omega
  rcases lt_or_eq_of_le hsplit with hlt | heq
  · have h1 : |f.coeff i| ≤ ((H : ℤ)) := hf.2.2 i hlt
    rw [Int.abs_eq_natAbs] at h1
    exact le_trans (by exact_mod_cast h1) (le_max_left H 1)
  · have hcoeff : f.coeff i = 1 := by
      have h1 : f.coeff i = f.leadingCoeff := by
        rw [heq, Polynomial.leadingCoeff,
          Polynomial.natDegree_eq_of_degree_eq_some hf.2.1]
      rw [h1, hf.1.leadingCoeff]
    rw [hcoeff]
    simp

lemma mahlerMeasure_mem_Box_le {n H : ℕ} {f : ℤ[X]} (hf : f ∈ Box n H) :
    (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤ ((n : ℝ) + 1) * ((H : ℝ) + 1) := by
  have hmon : f.Monic := hf.1
  have hdeg : (f.map (Int.castRingHom ℂ)).natDegree = n := by
    rw [hmon.natDegree_map, Polynomial.natDegree_eq_of_degree_eq_some hf.2.1]
  have hsup : (f.map (Int.castRingHom ℂ)).supNorm = (polyHeight f : ℝ) :=
    supNorm_map_eq_polyHeight f hmon
  have h1 : (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      Real.sqrt (((f.map (Int.castRingHom ℂ)).natDegree : ℝ) + 1) *
        (f.map (Int.castRingHom ℂ)).supNorm :=
    Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _
  rw [hsup, hdeg] at h1
  have hH1 : (polyHeight f : ℝ) ≤ (H : ℝ) + 1 := by
    have h := polyHeight_le_of_mem_Box hf
    have : (polyHeight f : ℝ) ≤ (max H 1 : ℕ) := by exact_mod_cast h
    have h2 : ((max H 1 : ℕ) : ℝ) ≤ (H : ℝ) + 1 := by
      have hh : (max H 1 : ℕ) ≤ H + 1 := max_le (Nat.le_succ H) (by omega)
      exact_mod_cast hh
    linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hs : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨hn0, by nlinarith⟩
  refine h1.trans ?_
  have hsup0 : (0 : ℝ) ≤ (polyHeight f : ℝ) := by positivity
  calc Real.sqrt ((n : ℝ) + 1) * (polyHeight f : ℝ)
      ≤ ((n : ℝ) + 1) * ((H : ℝ) + 1) :=
        mul_le_mul hs hH1 hsup0 hn0

/-! ## Integrality and the Mahler bound for the block coefficients -/

section BlockBound

variable {f : ℤ[X]} {hsep : (f.map φℚ).Separable}

/-- The coefficients of the block polynomial over its field of definition are
integral over `ℤ`. -/
lemma isIntegral_spolyL_coeff (hm : f.Monic) (B : Set (Fin (f.map φℚ).natDegree))
    (i : ℕ) :
    IsIntegral ℤ ((spolyL (f.map φℚ) hsep B).coeff i) := by
  have hinj : Function.Injective
      (algebraMap ↥(sfield (f.map φℚ) hsep B) (f.map φℚ).SplittingField) :=
    fun a b h => Subtype.ext h
  refine (isIntegral_algebraMap_iff hinj).mp ?_
  rw [show (algebraMap ↥(sfield (f.map φℚ) hsep B) (f.map φℚ).SplittingField)
        ((spolyL (f.map φℚ) hsep B).coeff i)
      = (spoly (f.map φℚ) hsep B).coeff i from spolyL_coeff_val (f.map φℚ) hsep B i]
  exact isIntegral_coeff_blockPoly f hm hsep (setFin B) i

end BlockBound

/-! ## The block polynomial over its field of definition is monic -/

lemma spolyL_monic (p : ℚ[X]) (hsep : p.Separable) (B : Set (Fin p.natDegree)) :
    (spolyL p hsep B).Monic := by
  have hmap : (spolyL p hsep B).map (algebraMap ↥(sfield p hsep B) p.SplittingField)
      = spoly p hsep B := spolyL_map_val p hsep B
  have hlc := congrArg Polynomial.leadingCoeff hmap
  rw [Polynomial.leadingCoeff_map, (spoly_monic p hsep B).leadingCoeff] at hlc
  have hinj : Function.Injective (algebraMap ↥(sfield p hsep B) p.SplittingField) :=
    fun a b h => Subtype.ext h
  show (spolyL p hsep B).leadingCoeff = 1
  exact hinj (by rw [hlc, map_one])

lemma spolyL_natDegree (p : ℚ[X]) (hsep : p.Separable) (B : Set (Fin p.natDegree)) :
    (spolyL p hsep B).natDegree = B.ncard := by
  rw [← (spolyL_monic p hsep B).natDegree_map
      (algebraMap ↥(sfield p hsep B) p.SplittingField), spolyL_map_val, spoly_natDegree]

/-! ## The Mahler bound for the block polynomial coefficients -/

section MahlerBound

variable (p : ℚ[X]) (hsep : p.Separable)

/-- The Fourier coefficient bound: the image of a block coefficient under an
embedding of the block field is bounded by `2^|B|` times the Mahler measure of
the conjugate block polynomial. -/
lemma norm_algHom_coeff_le (p : ℚ[X]) (hsep : p.Separable) (B : Set (Fin p.natDegree))
    (χ : ↥(sfield p hsep B) →ₐ[ℚ] ℂ) (j : ℕ) :
    ‖χ ((spolyL p hsep B).coeff j)‖
      ≤ (2 : ℝ) ^ B.ncard * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure := by
  rw [show χ ((spolyL p hsep B).coeff j)
      = ((spolyL p hsep B).map χ.toRingHom).coeff j from
    (Polynomial.coeff_map χ.toRingHom j).symm]
  have hnd : ((spolyL p hsep B).map χ.toRingHom).natDegree = B.ncard := by
    rw [(spolyL_monic p hsep B).natDegree_map χ.toRingHom, spolyL_natDegree]
  have hMnn : 0 ≤ ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure :=
    Polynomial.mahlerMeasure_nonneg _
  have hc := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure j
      ((spolyL p hsep B).map χ.toRingHom)
  rw [hnd] at hc
  have hch : ((B.ncard.choose j : ℕ) : ℝ) ≤ (2 : ℝ) ^ B.ncard := by
    exact_mod_cast Nat.choose_le_two_pow B.ncard j
  exact hc.trans (mul_le_mul_of_nonneg_right hch hMnn)

/-- **The Mahler bound for the block coefficients.**  For an irreducible monic
`p : ℚ[X]` with a block `B` of the naive Galois action on its roots, the Mahler
measure of `L = blockField p hsep B` (at the infinite places) of every
coefficient `c_i` of the block polynomial `P_L` is at most
`2^(|B|·[L:ℚ]) · M(p)`. -/
theorem mahlerK_spolyL_coeff_le [Fact (Irreducible p)]
    [MulAction.IsPretransitive (↥(galImg p hsep)) (Fin p.natDegree)]
    {B : Set (Fin p.natDegree)}
    (hB : MulAction.IsBlock (↥(galImg p hsep)) B) (hne : B.Nonempty)
    (ι : p.SplittingField →ₐ[ℚ] ℂ) (hmonic : p.Monic) {Y : ℝ}
    (hY : (p.map (algebraMap ℚ ℂ)).mahlerMeasure ≤ Y)
    (hint : ∀ i, IsIntegral ℤ ((spolyL p hsep B).coeff i)) (i : ℕ) :
    Commons.NumberTheory.NumberField.mahlerK ↥(sfield p hsep B) ((spolyL p hsep B).coeff i)
      ≤ 2 ^ (B.ncard * Module.finrank ℚ ↥(sfield p hsep B)) * Y := by
  classical
  haveI : NumberField ↥(sfield p hsep B) := ⟨⟩
  have hK : Module.finrank ℚ ↥(sfield p hsep B)
      = Fintype.card (↥(sfield p hsep B) →ₐ[ℚ] ℂ) :=
    (Commons.NumberTheory.NumberField.card_algHom_eq_finrank).symm
  rw [Commons.NumberTheory.NumberField.mahlerK_eq_prod_algHom (hint i)]
  have hfac : ∀ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
      max 1 ‖χ ((spolyL p hsep B).coeff i)‖
        ≤ 2 ^ B.ncard * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure := by
    intro χ
    refine max_le ?_ ?_
    · have hM1 := Commons.Analysis.Polynomial.one_le_mahlerMeasure_of_monic
        ((spolyL_monic p hsep B).map χ.toRingHom)
      have hMnn := Polynomial.mahlerMeasure_nonneg ((spolyL p hsep B).map χ.toRingHom)
      have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ B.ncard := one_le_pow₀ (by norm_num)
      nlinarith
    · exact norm_algHom_coeff_le p hsep B χ i
  have hprod : ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
        ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure
      = (p.map (algebraMap ℚ ℂ)).mahlerMeasure := by
    rw [← Commons.Analysis.Polynomial.mahlerMeasure_prod,
      normIdentity p hsep hmonic hB hne ι]
  calc ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ), max 1 ‖χ ((spolyL p hsep B).coeff i)‖
      ≤ ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
          (2 ^ B.ncard * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure) :=
        Finset.prod_le_prod (fun χ _ => by positivity) (fun χ _ => hfac χ)
    _ = (2 ^ B.ncard) ^ (Fintype.card (↥(sfield p hsep B) →ₐ[ℚ] ℂ))
          * ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
              ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        rfl
    _ = (2 ^ B.ncard) ^ (Module.finrank ℚ ↥(sfield p hsep B))
          * (p.map (algebraMap ℚ ℂ)).mahlerMeasure := by
        rw [hprod, ← hK]
    _ ≤ 2 ^ (B.ncard * Module.finrank ℚ ↥(sfield p hsep B)) * Y := by
        rw [pow_mul]
        exact mul_le_mul_of_nonneg_left hY (by positivity)

/-! ## The Mahler bound for the generator -/

/-- The candidate generator `Σ_j μ_j c_j` of the block field, from the
coefficients of the block polynomial. -/
noncomputable def blockGamma (p : ℚ[X]) (hsep : p.Separable) (B : Set (Fin p.natDegree))
    (μ : Fin p.natDegree → ℕ) : ↥(sfield p hsep B) :=
  ∑ j : Fin p.natDegree, ((μ j : ℕ) : ↥(sfield p hsep B)) * (spolyL p hsep B).coeff j

lemma isIntegral_natCast' {A : Type*} [CommRing A] [Algebra ℤ A] (n : ℕ) :
    IsIntegral ℤ ((n : ℕ) : A) := by
  refine ⟨Polynomial.X - Polynomial.C (n : ℤ), Polynomial.monic_X_sub_C _, ?_⟩
  simp

lemma isIntegral_blockGamma (p : ℚ[X]) (hsep : p.Separable) (B : Set (Fin p.natDegree))
    (hint : ∀ i, IsIntegral ℤ ((spolyL p hsep B).coeff i)) (μ : Fin p.natDegree → ℕ) :
    IsIntegral ℤ (blockGamma p hsep B μ) := by
  refine IsIntegral.sum _ fun j _ => ?_
  exact IsIntegral.mul (isIntegral_natCast' (μ j)) (hint j)

/-- **The Mahler bound for the generator.**  With `γ = Σ_j μ_j c_j`
(`μ_j ≤ M0`) a generator of the block field, the Mahler measure of `L` at `γ`
is at most `(|B|·M0·2^|B|)^[L:ℚ] · M(p)`. -/
theorem mahlerK_spolyL_gamma_le [Fact (Irreducible p)]
    [MulAction.IsPretransitive (↥(galImg p hsep)) (Fin p.natDegree)]
    {B : Set (Fin p.natDegree)}
    (hB : MulAction.IsBlock (↥(galImg p hsep)) B) (hne : B.Nonempty)
    (ι : p.SplittingField →ₐ[ℚ] ℂ) (hmonic : p.Monic) {Y : ℝ}
    (hY : (p.map (algebraMap ℚ ℂ)).mahlerMeasure ≤ Y)
    (hint : ∀ i, IsIntegral ℤ ((spolyL p hsep B).coeff i))
    (μ : Fin p.natDegree → ℕ) {M0 : ℕ} (hM0 : 1 ≤ M0) (hμ : ∀ j, μ j ≤ M0) :
    Commons.NumberTheory.NumberField.mahlerK ↥(sfield p hsep B) (blockGamma p hsep B μ)
      ≤ (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
          ^ (Module.finrank ℚ ↥(sfield p hsep B))) * Y := by
  classical
  haveI : NumberField ↥(sfield p hsep B) := ⟨⟩
  have hK : Module.finrank ℚ ↥(sfield p hsep B)
      = Fintype.card (↥(sfield p hsep B) →ₐ[ℚ] ℂ) :=
    (Commons.NumberTheory.NumberField.card_algHom_eq_finrank).symm
  rw [Commons.NumberTheory.NumberField.mahlerK_eq_prod_algHom
    (isIntegral_blockGamma p hsep B hint μ)]
  have hfac : ∀ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
      max 1 ‖χ (blockGamma p hsep B μ)‖
        ≤ (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
            * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure) := by
    intro χ
    have hM1 : 1 ≤ ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure :=
      Commons.Analysis.Polynomial.one_le_mahlerMeasure_of_monic
        ((spolyL_monic p hsep B).map χ.toRingHom)
    have hMnn : 0 ≤ ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure :=
      Polynomial.mahlerMeasure_nonneg _
    have hmap : χ (blockGamma p hsep B μ)
        = ∑ j : Fin p.natDegree, ((μ j : ℕ) : ℂ)
            * χ ((spolyL p hsep B).coeff j) := by
      rw [blockGamma, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_natCast]
    have hstep : ‖χ (blockGamma p hsep B μ)‖
        ≤ (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
            * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure) := by
      rw [hmap]
      calc ‖∑ j : Fin p.natDegree, ((μ j : ℕ) : ℂ)
              * χ ((spolyL p hsep B).coeff j)‖
          ≤ ∑ j : Fin p.natDegree, ‖((μ j : ℕ) : ℂ)
              * χ ((spolyL p hsep B).coeff j)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin p.natDegree, ((M0 : ℝ)
              * ((2 : ℝ) ^ B.ncard
                * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul, Complex.norm_natCast]
            have h1 : ((μ j : ℕ) : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hμ j
            have h2 : ‖χ ((spolyL p hsep B).coeff j)‖
                ≤ (2 : ℝ) ^ B.ncard
                  * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure :=
              norm_algHom_coeff_le p hsep B χ j
            exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
              * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    refine max_le ?_ hstep
    have hC1 : (1 : ℝ) ≤ ((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ) := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ B.ncard := one_le_pow₀ (by norm_num)
      have hpn1 : 1 ≤ p.natDegree := by
        rw [Nat.succ_le_iff, Polynomial.natDegree_pos_iff_degree_pos]
        exact Polynomial.degree_pos_of_irreducible Fact.out
      have h0 : (1 : ℝ) ≤ (p.natDegree : ℝ) := by exact_mod_cast hpn1
      have h0' : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0
      push_cast
      have hb : (1 : ℝ) ≤ (p.natDegree : ℝ) * (M0 : ℝ) := by
        nlinarith [h0, h0', mul_nonneg (by linarith : (0:ℝ) ≤ (p.natDegree : ℝ))
          (by linarith : (0:ℝ) ≤ (M0 : ℝ))]
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((p.natDegree : ℝ) * (M0 : ℝ)) * (2 : ℝ) ^ B.ncard :=
            mul_le_mul hb h2 (by norm_num) (by positivity)
    nlinarith [hC1, hM1, hMnn]
  have hprod : ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
        ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure
      = (p.map (algebraMap ℚ ℂ)).mahlerMeasure := by
    rw [← Commons.Analysis.Polynomial.mahlerMeasure_prod,
      normIdentity p hsep hmonic hB hne ι]
  calc ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ), max 1 ‖χ (blockGamma p hsep B μ)‖
      ≤ ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
          (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
            * ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure) :=
        Finset.prod_le_prod (fun χ _ => by positivity) (fun χ _ => hfac χ)
    _ = (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
            ^ (Fintype.card (↥(sfield p hsep B) →ₐ[ℚ] ℂ)))
          * ∏ χ : (↥(sfield p hsep B) →ₐ[ℚ] ℂ),
              ((spolyL p hsep B).map χ.toRingHom).mahlerMeasure := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        rfl
    _ = (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
            ^ (Module.finrank ℚ ↥(sfield p hsep B)))
          * (p.map (algebraMap ℚ ℂ)).mahlerMeasure := by
        rw [hprod, ← hK]
    _ ≤ (((p.natDegree * M0 * 2 ^ B.ncard : ℕ) : ℝ)
            ^ (Module.finrank ℚ ↥(sfield p hsep B))) * Y :=
        mul_le_mul_of_nonneg_left hY (by positivity)

end MahlerBound

end

end Submission.Vdw
