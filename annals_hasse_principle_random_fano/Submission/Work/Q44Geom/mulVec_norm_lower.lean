import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.MulMono
import Submission.Work.HP.Vero.mulVec_formEvalR
import Submission.Work.Q44Geom.ReducDefs

/-!
# The product of coefficient vectors is bounded below in norm

For coefficient vectors `A : Mon a 4 → ℝ` and `B : Mon b 4 → ℝ` of two forms in `5` variables,
the Euclidean norm `rNorm` of the coefficient vector `mulVec a b (a+b) A B` of the *product* form
is bounded below by `c * rNorm A * rNorm B` for a constant `c > 0` depending only on the degrees
`a, b` (here `a + b = 4`).

The mathematical content is the standard compactness argument for a bilinear map without zero
divisors:

* `mulVec_eq_zero_imp`: the product of two nonzero coefficient vectors is nonzero (the product
  of two nonzero forms is a nonzero form, since `ℝ[X₀,…,X₄]` is a domain);
* `bilinear_norm_lower`: any continuous bilinear map `Φ` with `Φ v w = 0 → v = 0 ∨ w = 0` between
  proper real normed spaces satisfies `‖Φ v w‖ ≥ c ‖v‖ ‖w‖` — the function
  `(v,w) ↦ ‖Φ v w‖` is continuous and strictly positive on the compact product of the two unit
  spheres, so it has a positive minimum there, and biadditivity propagates this bound to all
  `(v,w)` by scaling;
* the comparison `rNorm v ≤ ‖v‖ √(card ι)` (and `‖v‖ ≤ rNorm v`) transfers the bound to the
  Euclidean norms used in the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Finset

namespace Work.Q44Geom

open Work.HP

/-! ## An abstract lower bound for nondegenerate bilinear maps -/

/-- A continuous bilinear map without zero divisors between proper real normed spaces is bounded
below, uniformly, by a positive multiple of the product of the norms. -/
lemma bilinear_norm_lower {V W Z : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Φ : V →ₗ[ℝ] W →ₗ[ℝ] Z) (hcont : Continuous fun p : V × W => Φ p.1 p.2)
    (h : ∀ v w, Φ v w = 0 → v = 0 ∨ w = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ v w, c * ‖v‖ * ‖w‖ ≤ ‖Φ v w‖ := by
  set s : Set (V × W) := Metric.sphere (0 : V) 1 ×ˢ Metric.sphere (0 : W) 1 with hs
  have hsc : IsCompact s := by
    rw [hs]
    exact (isCompact_sphere (0 : V) 1).prod (isCompact_sphere (0 : W) 1)
  have hpos : ∀ b ∈ s, (0 : ℝ) < ‖Φ b.1 b.2‖ := by
    intro b hb
    rw [hs, Set.mem_prod, Metric.mem_sphere, Metric.mem_sphere, dist_eq_norm, dist_eq_norm,
      sub_zero, sub_zero] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine norm_pos_iff.mpr fun hzero => ?_
    rcases h b.1 b.2 hzero with h1 | h2
    · rw [h1, norm_zero] at hb1; norm_num at hb1
    · rw [h2, norm_zero] at hb2; norm_num at hb2
  obtain ⟨c, hcpos, hcle⟩ := hsc.exists_forall_le'
    (f := fun p : V × W => ‖Φ p.1 p.2‖) hcont.norm.continuousOn hpos
  refine ⟨c, hcpos, fun v w => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  by_cases hw : w = 0
  · subst hw; simp
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hmem : ((‖v‖⁻¹ : ℝ) • v, (‖w‖⁻¹ : ℝ) • w) ∈ s := by
    have e1 : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ (ne_of_gt hvn)]
    have e2 : ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        inv_mul_cancel₀ (ne_of_gt hwn)]
    rw [hs, Set.mem_prod, Metric.mem_sphere, Metric.mem_sphere, dist_eq_norm, dist_eq_norm,
      sub_zero, sub_zero]
    exact ⟨e1, e2⟩
  have hbnd : c ≤ ‖Φ ((‖v‖⁻¹ : ℝ) • v) ((‖w‖⁻¹ : ℝ) • w)‖ := hcle _ hmem
  have hsmul : Φ ((‖v‖⁻¹ : ℝ) • v) ((‖w‖⁻¹ : ℝ) • w)
      = ((‖v‖⁻¹ : ℝ) * (‖w‖⁻¹ : ℝ)) • Φ v w := by
    simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_smul]
  have hkey : Φ v w = (‖v‖ * ‖w‖) • Φ ((‖v‖⁻¹ : ℝ) • v) ((‖w‖⁻¹ : ℝ) • w) := by
    rw [hsmul, smul_smul]
    have hc : (‖v‖ * ‖w‖) * ((‖v‖⁻¹ : ℝ) * (‖w‖⁻¹ : ℝ)) = 1 := by
      rw [mul_comm (‖v‖⁻¹ : ℝ) (‖w‖⁻¹ : ℝ), ← mul_inv_rev,
        mul_inv_cancel₀ (mul_ne_zero (ne_of_gt hvn) (ne_of_gt hwn))]
    rw [hc, one_smul]
  calc c * ‖v‖ * ‖w‖ = ‖v‖ * ‖w‖ * c := by ring
    _ ≤ ‖v‖ * ‖w‖ * ‖Φ ((‖v‖⁻¹ : ℝ) • v) ((‖w‖⁻¹ : ℝ) • w)‖ :=
        mul_le_mul_of_nonneg_left hbnd (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖Φ v w‖ := by
        rw [hkey, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/-! ## The Euclidean norm versus the product norm on a finite type -/

section NormLemmas

variable {ι : Type*} [Fintype ι]

/-- A coordinate of `v` is bounded by `rNorm v`. -/
lemma abs_le_rNorm_aux (v : ι → ℝ) (i : ι) : |v i| ≤ rNorm v := by
  have h : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  calc |v i| = Real.sqrt ((v i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (v j) ^ 2) := Real.sqrt_le_sqrt h
    _ = rNorm v := rfl

/-- The product norm on `ι → ℝ` is bounded by the Euclidean norm `rNorm`. -/
lemma norm_le_rNorm (v : ι → ℝ) : ‖v‖ ≤ rNorm v := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg (∑ i, (v i) ^ 2))).mpr ?_
  intro i
  rw [Real.norm_eq_abs]
  exact abs_le_rNorm_aux v i

/-- The Euclidean norm `rNorm` is bounded by `√(card ι)` times the product norm. -/
lemma rNorm_le_norm_mul_sqrt_card (v : ι → ℝ) :
    rNorm v ≤ ‖v‖ * Real.sqrt (Fintype.card ι) := by
  have h1 : ∀ i, (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    have h := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h
    calc (v i) ^ 2 = |v i| ^ 2 := by rw [sq_abs]
      _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : ∑ i, (v i) ^ 2 ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
    calc ∑ i, (v i) ^ 2 ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ = (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc rNorm v = Real.sqrt (∑ i, (v i) ^ 2) := rfl
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖v‖ * Real.sqrt (Fintype.card ι) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg v), mul_comm]

end NormLemmas

/-! ## The monomial index is nonempty -/

/-- `Mon d n` is nonempty: the monomial `X₀^d`. -/
lemma monNonempty (d n : ℕ) : Nonempty (Mon d n) :=
  ⟨⟨fun i => if i = 0 then ⟨d, Nat.lt_succ_self d⟩ else 0, by
    have h : ∀ i : Fin (n + 1),
        (((if i = 0 then (⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)) else 0 : Fin (d + 1))) : ℕ)
          = if i = 0 then d else 0 := by
      intro i; split <;> simp
    simp only [h]
    simp⟩⟩

/-! ## The product of two nonzero coefficient vectors is nonzero -/

/-- `MvPolynomial.eval` of `polyOfR` is `formEvalR`. -/
lemma eval_polyOfR {d : ℕ} (C : Mon d 4 → ℝ) (z : Fin 5 → ℝ) :
    MvPolynomial.eval z (polyOfR C) = formEvalR d 4 C z := by
  rw [polyOfR, map_sum]
  simp only [MvPolynomial.eval_monomial, formEvalR, veronese]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [Mon_toFinsupp_apply]

/-- The coefficient vector of a product of forms vanishes only if one of the factors does
(`ℝ[X₀,…,X₄]` is a domain). -/
lemma mulVec_eq_zero_imp {a b : ℕ} (A : Mon a 4 → ℝ) (B : Mon b 4 → ℝ)
    (h : Vero.mulVec a b (a + b) A B = 0) : A = 0 ∨ B = 0 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hPQ : polyOfR A * polyOfR B = 0 := by
    refine MvPolynomial.funext (fun z => ?_)
    rw [MvPolynomial.eval_mul, eval_polyOfR, eval_polyOfR, ← Vero.mulVec_formEvalR, h]
    simp [formEvalR]
  rcases mul_eq_zero.mp hPQ with hP | hQ
  · exact hA (polyOfR_injective (by rw [hP, polyOfR_zero]))
  · exact hB (polyOfR_injective (by rw [hQ, polyOfR_zero]))

/-! ## The product as a bilinear map, and its continuity -/

/-- The product of coefficient vectors as a bilinear map. -/
def phiMul (a b : ℕ) :
    (Mon a 4 → ℝ) →ₗ[ℝ] (Mon b 4 → ℝ) →ₗ[ℝ] (Mon (a + b) 4 → ℝ) :=
  LinearMap.mk₂ ℝ (fun A B => Vero.mulVec a b (a + b) A B)
    (fun A A' B => Vero.mulVec_add_left (a := a) (b := b) (d := a + b) (n := 4) A A' B)
    (fun c A B => Vero.mulVec_smul_left (a := a) (b := b) (d := a + b) (n := 4) c A B)
    (fun A B B' => Vero.mulVec_add_right (a := a) (b := b) (d := a + b) (n := 4) A B B')
    (fun c A B => Vero.mulVec_smul_right (a := a) (b := b) (d := a + b) (n := 4) c A B)

/-- `phiMul` is continuous (each coefficient is a polynomial in the coordinates). -/
lemma continuous_phiMul (a b : ℕ) :
    Continuous fun p : (Mon a 4 → ℝ) × (Mon b 4 → ℝ) => phiMul a b p.1 p.2 := by
  rw [continuous_pi_iff]
  intro M
  have hcoord : (fun p : (Mon a 4 → ℝ) × (Mon b 4 → ℝ) => phiMul a b p.1 p.2 M)
      = fun p => ∑ p' : Mon a 4, ∑ q' : Mon b 4,
          if Vero.addMon p' q' = M then p.1 p' * p.2 q' else 0 := by
    funext p
    simp only [phiMul, LinearMap.mk₂_apply, Vero.mulVec_apply_addMon]
  rw [hcoord]
  refine continuous_finsetSum _ (fun p' _ => continuous_finsetSum _ (fun q' _ => ?_))
  by_cases hc : Vero.addMon p' q' = M
  · have hprod : Continuous fun p : (Mon a 4 → ℝ) × (Mon b 4 → ℝ) => p.1 p' * p.2 q' :=
      ((continuous_apply p').comp continuous_fst).mul
        ((continuous_apply q').comp continuous_snd)
    simpa only [ite_eq_left hc] using hprod
  · have hz : Continuous fun _ : (Mon a 4 → ℝ) × (Mon b 4 → ℝ) => (0 : ℝ) := continuous_const
    simpa only [ite_eq_right hc] using hz

/-! ## The main statement -/

theorem mulVec_norm_lower (a b : ℕ) (hab : a + b = 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Work.HP.Mon a 4 → ℝ) (B : Work.HP.Mon b 4 → ℝ),
      c * Work.HP.rNorm A * Work.HP.rNorm B
        ≤ Work.HP.rNorm (Work.HP.Vero.mulVec a b (a + b) A B) := by
  haveI hP1 : ProperSpace (Mon a 4 → ℝ) := FiniteDimensional.proper ℝ _
  haveI hP2 : ProperSpace (Mon b 4 → ℝ) := FiniteDimensional.proper ℝ _
  have hcont : Continuous fun p : (Mon a 4 → ℝ) × (Mon b 4 → ℝ) => phiMul a b p.1 p.2 :=
    continuous_phiMul a b
  have hnd : ∀ A B, phiMul a b A B = 0 → A = 0 ∨ B = 0 := by
    intro A B hAB
    refine mulVec_eq_zero_imp A B ?_
    simpa only [phiMul, LinearMap.mk₂_apply] using hAB
  obtain ⟨c₀, hc₀pos, hc₀⟩ := bilinear_norm_lower (Φ := phiMul a b) hcont hnd
  have hNa : 0 < Real.sqrt (Fintype.card (Mon a 4)) := by
    apply Real.sqrt_pos.mpr
    have h : 0 < Fintype.card (Mon a 4) := Fintype.card_pos_iff.mpr (monNonempty a 4)
    exact_mod_cast h
  have hNb : 0 < Real.sqrt (Fintype.card (Mon b 4)) := by
    apply Real.sqrt_pos.mpr
    have h : 0 < Fintype.card (Mon b 4) := Fintype.card_pos_iff.mpr (monNonempty b 4)
    exact_mod_cast h
  refine ⟨c₀ * (Real.sqrt (Fintype.card (Mon a 4)))⁻¹
      * (Real.sqrt (Fintype.card (Mon b 4)))⁻¹, ?_, ?_⟩
  · exact mul_pos (mul_pos hc₀pos (inv_pos.mpr hNa)) (inv_pos.mpr hNb)
  · intro A B
    have h1 : ‖Vero.mulVec a b (a + b) A B‖ ≤ rNorm (Vero.mulVec a b (a + b) A B) :=
      norm_le_rNorm _
    have h2 : c₀ * ‖A‖ * ‖B‖ ≤ ‖Vero.mulVec a b (a + b) A B‖ := hc₀ A B
    have hA : rNorm A * (Real.sqrt (Fintype.card (Mon a 4)))⁻¹ ≤ ‖A‖ := by
      rw [mul_inv_le_iff₀ hNa]
      exact rNorm_le_norm_mul_sqrt_card A
    have hB : rNorm B * (Real.sqrt (Fintype.card (Mon b 4)))⁻¹ ≤ ‖B‖ := by
      rw [mul_inv_le_iff₀ hNb]
      exact rNorm_le_norm_mul_sqrt_card B
    have hnn : 0 ≤ rNorm B * (Real.sqrt (Fintype.card (Mon b 4)))⁻¹ :=
      mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    calc c₀ * (Real.sqrt (Fintype.card (Mon a 4)))⁻¹
          * (Real.sqrt (Fintype.card (Mon b 4)))⁻¹ * rNorm A * rNorm B
        = c₀ * (rNorm A * (Real.sqrt (Fintype.card (Mon a 4)))⁻¹)
            * (rNorm B * (Real.sqrt (Fintype.card (Mon b 4)))⁻¹) := by ring
      _ ≤ c₀ * ‖A‖ * ‖B‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA hc₀pos.le) hB hnn
            (mul_nonneg hc₀pos.le (norm_nonneg A))
      _ ≤ ‖Vero.mulVec a b (a + b) A B‖ := h2
      _ ≤ rNorm (Vero.mulVec a b (a + b) A B) := h1

end Work.Q44Geom
