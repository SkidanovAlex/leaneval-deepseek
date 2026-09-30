import Mathlib
import Submission.Work.BW.exists_monomial_basis
import Submission.Work.BW.discr_le_discr_of_isIntegral_basis
import Submission.Work.BW.discr_le_of_embeddings_bound


namespace Work.BW

open NumberField

/-- The logarithm of the absolute value of `φ x` under a complex embedding of a number field is
at most the logarithmic height of `x`. -/
theorem log_norm_ringHom_le_logHeight₁ {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (x : K) : Real.log ‖φ x‖ ≤ Height.logHeight₁ x := by
  rw [NumberField.logHeight₁_eq]
  have hsingle : Real.log ‖φ x‖ ≤
      (InfinitePlace.mk φ).mult * ((InfinitePlace.mk φ) x).posLog := by
    have h1 : (1:ℝ) ≤ ((InfinitePlace.mk φ).mult : ℝ) := InfinitePlace.one_le_mult
    have h2 : Real.log ‖φ x‖ ≤ ((InfinitePlace.mk φ) x).posLog := le_max_right _ _
    have h3 : (0:ℝ) ≤ ((InfinitePlace.mk φ) x).posLog := Real.posLog_nonneg
    nlinarith [h1, h2, h3]
  refine le_trans hsingle (le_trans ?_
    (le_add_of_nonneg_right (finsum_nonneg fun v => Real.posLog_nonneg)))
  exact Finset.single_le_sum (f := fun v : InfinitePlace K => (v.mult : ℝ) * (v x).posLog)
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg) (Finset.mem_univ _)

/-- The logarithmic height of a monomial `∏ j, β j ^ e j` is at most
`∑ j, e j * h(β j)`. -/
theorem logHeight_monomial_le' {F : Type*} [Field F] [NumberField F] {r : ℕ}
    (β : Fin r → F) (e : Fin r → ℕ) :
    Height.logHeight₁ (∏ j, β j ^ e j) ≤ ∑ j, (e j : ℝ) * Height.logHeight₁ (β j) := by
  refine le_trans (Height.logHeight₁_prod_le Finset.univ fun j => β j ^ e j) ?_
  exact le_of_eq (Finset.sum_congr rfl fun j _ => Height.logHeight₁_pow (β j) (e j))

/-- Scaling the elements of a family by rational scalars (through the algebra structure) scales
the discriminant by the square of the product of the scalars. -/
theorem discr_diag_algebraMap {F : Type*} [Field F] [Algebra ℚ F] {d : ℕ}
    (b : Fin d → F) (c : Fin d → ℚ) :
    Algebra.discr ℚ (fun k => algebraMap ℚ F (c k) * b k) =
      (∏ k, c k) ^ 2 * Algebra.discr ℚ b := by
  have h := Algebra.discr_of_matrix_mulVec (A := ℚ) b (Matrix.diagonal c)
  have hfun : Matrix.mulVec ((Matrix.diagonal c).map (algebraMap ℚ F)) b =
      fun k => algebraMap ℚ F (c k) * b k := by
    funext k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k]
    · simp
    · intro i _ hi
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hi)]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hfun, Matrix.det_diagonal] at h
  exact h

/-- **Crude discriminant bound.**  If `β : Fin r → F` (`r ≥ 2`) generates the number field `F` over
`ℚ` and `σ : Fin r → ℝ` satisfies `h(βⱼ) ≤ [F:ℚ] · σⱼ` (with `h = Height.logHeight₁` and
`σⱼ > 0`), then

`½ log|disc F| ≤ log([F:ℚ]!) + 2·[F:ℚ]³·(σ₁ + ⋯ + σᵣ)`.

This is a deliberately crude (but fully elementary) version of the Baker–Wüstholz/`discriminant_bound`
estimate: constants do not matter, only that the height dependence is linear.

Proof sketch.  Let `d = [F:ℚ]`, `S = ∑ⱼ h(βⱼ) ≤ d·∑σⱼ`.
1. (`BW/exists_monomial_basis`) pick a `ℚ`-basis `b : Fin d → F` of monomials `∏ⱼ βⱼ^(eᵢⱼ)` of total
   degree `≤ d-1`; hence `h(bᵢ) ≤ (d-1)·maxⱼ h(βⱼ) ≤ d·S`.
2. (`NumberField.exists_nat_le_mulHeight₁`) pick `nⱼ ≠ 0` with `nⱼ βⱼ` integral and
   `log nⱼ ≤ log(mulHeight₁ βⱼ) = h(βⱼ)`.
3. The monomials `bᵢ' = ∏ⱼ (nⱼ βⱼ)^(eᵢⱼ) = (∏ⱼ nⱼ^(eᵢⱼ))·bᵢ` are algebraic integers, and `bᵢ'` is
   again a `ℚ`-basis (diagonal nonzero rescaling), so
   (`BW/discr_le_discr_of_isIntegral_basis`) `|disc F| ≤ |discr ℚ b'|`; and by
   `Algebra.discr_of_matrix_vecMul` (change of basis by the diagonal matrix `diag(∏ⱼ nⱼ^(eᵢⱼ))`)
   `discr ℚ b' = (∏ᵢ ∏ⱼ nⱼ^(eᵢⱼ))² · discr ℚ b`, so
   `log|disc F| ≤ 2·d·(d-1)·maxⱼ log nⱼ + log|discr ℚ b|`.
4. (`BW/discr_le_of_embeddings_bound`) `|discr ℚ b| ≤ (d! · M^d)²` where `M = max_{i,σ} ‖σ(bᵢ)‖`;
   taking `M = exp(d·S)` (using `log‖σ(bᵢ)‖ ≤ h(bᵢ) ≤ S ≤ d·S`) gives
   `log|discr ℚ b| ≤ 2 log(d!) + 2·d²·S`.
5. Add up: `log|disc F| ≤ 2 log(d!) + 4·d²·S`, i.e.
   `½ log|disc F| ≤ log(d!) + 2·d²·S ≤ log(d!) + 2·d³·∑σⱼ`. -/
theorem half_log_discr_le {F : Type*} [Field F] [NumberField F] {r : ℕ} (hr : 2 ≤ r)
    (β : Fin r → F) (hgen : IntermediateField.adjoin ℚ (Set.range β) = ⊤)
    (σ : Fin r → ℝ) (hσ : ∀ j, 0 < σ j)
    (hH : ∀ j, Height.logHeight₁ (β j) ≤ (Module.finrank ℚ F : ℝ) * σ j) :
    (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| ≤
      Real.log (((Module.finrank ℚ F).factorial : ℝ)) +
        2 * (Module.finrank ℚ F : ℝ) ^ 3 * (Finset.univ.sum fun j => σ j) := by
  classical
  set d : ℕ := Module.finrank ℚ F with hd
  have hdpos : 0 < d := by rw [hd]; exact Module.finrank_pos
  set S : ℝ := ∑ j, Height.logHeight₁ (β j) with hSdef
  set T : ℝ := ∑ j, σ j with hTdef
  have hS_le : S ≤ (d : ℝ) * T := by
    rw [hSdef, hTdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hH j
  obtain ⟨m, e, hm, he, hli⟩ := exists_monomial_basis β hgen
  -- Step 1: heights of the monomials of the basis
  have hmh : ∀ k, Height.logHeight₁ (m k) ≤ (d : ℝ) * S := by
    intro k
    rw [hm k]
    refine le_trans (logHeight_monomial_le' β (e k)) ?_
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (le_of_lt (he k j)))
      (Height.zero_le_logHeight₁ _)
  -- Step 2: denominators clearing the generators
  have hden : ∀ j, ∃ n : ℕ, n ≠ 0 ∧ (n : ℝ) ≤ Height.mulHeight₁ (β j) ∧
      IsIntegral ℤ ((n : F) * β j) := fun j => NumberField.exists_nat_le_mulHeight₁ (β j)
  choose n hn using hden
  have hn0 : ∀ j, n j ≠ 0 := fun j => (hn j).1
  have hnle : ∀ j, (n j : ℝ) ≤ Height.mulHeight₁ (β j) := fun j => (hn j).2.1
  have hnint : ∀ j, IsIntegral ℤ ((n j : F) * β j) := fun j => (hn j).2.2
  have hlog_n : ∀ j, Real.log (n j) ≤ Height.logHeight₁ (β j) := by
    intro j
    rw [Height.logHeight₁_eq_log_mulHeight₁]
    exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (hn0 j)) (hnle j)
  -- Step 3: the rescaled integral monomial basis
  set nn : Fin r → F := fun j => (n j : F) * β j with hnn
  set c : Fin d → ℚ := fun k => ((∏ j, (n j) ^ (e k j) : ℕ) : ℚ) with hc
  set cr : Fin d → ℝ := fun k => ((∏ j, (n j) ^ (e k j) : ℕ) : ℝ) with hcr
  set bp : Fin d → F := fun k => c k • m k with hbp
  have hc_apply : ∀ k, c k = ((∏ j, (n j) ^ (e k j) : ℕ) : ℚ) := by
    intro k; rw [hc]
  have hcr_apply : ∀ k, cr k = ((∏ j, (n j) ^ (e k j) : ℕ) : ℝ) := by
    intro k; rw [hcr]
  have hnn_apply : ∀ j, nn j = (n j : F) * β j := by
    intro j; rw [hnn]
  have hbp_apply : ∀ k, bp k = c k • m k := by
    intro k; rw [hbp]
  have hcR : ∀ k, ((c k : ℚ) : ℝ) = cr k := by
    intro k
    rw [hc_apply k, hcr_apply k]
    push_cast
    rfl
  have hNne : ∀ k, (∏ j, (n j) ^ (e k j) : ℕ) ≠ 0 := by
    intro k
    rw [Finset.prod_ne_zero_iff]
    exact fun j _ => pow_ne_zero _ (hn0 j)
  have hcr0 : ∀ k, cr k ≠ 0 := by
    intro k
    rw [hcr_apply k]
    exact Nat.cast_ne_zero.mpr (hNne k)
  have hc0 : ∀ k, c k ≠ 0 := by
    intro k
    rw [hc_apply k]
    exact Nat.cast_ne_zero.mpr (hNne k)
  have hli_bp : LinearIndependent ℚ bp := by
    have h := LinearIndependent.units_smul hli (fun k => Units.mk0 (c k) (hc0 k))
    have h2 : (fun k => c k • m k) = ((fun k => Units.mk0 (c k) (hc0 k)) • m) := by
      funext k
      simp
    rw [hbp, h2]
    exact h
  have hbpeq : ∀ k, bp k = algebraMap ℚ F (c k) * m k := by
    intro k
    rw [hbp_apply k, Algebra.smul_def]
  have hbp_mono : ∀ k, bp k = ∏ j, nn j ^ (e k j) := by
    intro k
    rw [hbpeq k, hm k, hc_apply k]
    push_cast
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [hnn_apply j, mul_pow]
  have hint' : ∀ k, IsIntegral ℤ (bp k) := by
    intro k
    rw [hbp_mono k]
    exact IsIntegral.prod (s := Finset.univ) (fun j => nn j ^ (e k j))
      (fun j _ => (hnint j).pow _)
  -- the basis and the discriminant comparison
  have hcard : Fintype.card (Fin d) = Module.finrank ℚ F := Fintype.card_fin d
  let b : Module.Basis (Fin d) ℚ F :=
    basisOfLinearIndependentOfCardEqFinrank' m hli hcard
  have hb_coe : (b : Fin d → F) = m :=
    coe_basisOfLinearIndependentOfCardEqFinrank' m hli hcard
  let b2 : Module.Basis (Fin d) ℚ F :=
    basisOfLinearIndependentOfCardEqFinrank' bp hli_bp hcard
  have hb2_coe : (b2 : Fin d → F) = bp :=
    coe_basisOfLinearIndependentOfCardEqFinrank' bp hli_bp hcard
  have hne_disc_b : Algebra.discr ℚ m ≠ 0 := by
    rw [← hb_coe]
    exact Algebra.discr_not_zero_of_basis ℚ b
  have hdisc_le : |((NumberField.discr F : ℤ) : ℝ)| ≤ |((Algebra.discr ℚ bp : ℚ) : ℝ)| := by
    have h := discr_le_discr_of_isIntegral_basis b2 (fun i => (congrFun hb2_coe i) ▸ hint' i)
    simpa only [hb2_coe] using h
  -- the discriminant of the rescaled family
  have hdiscr_eq : Algebra.discr ℚ bp =
      (∏ k, c k) ^ 2 * Algebra.discr ℚ m := by
    have h := discr_diag_algebraMap (d := d) m c
    have hfun : (fun k => algebraMap ℚ F (c k) * m k) = bp := by
      funext k
      exact (hbpeq k).symm
    rw [hfun] at h
    exact h
  -- log of the product of the scalars
  have hlog_Nk : ∀ k, Real.log (cr k) ≤ (d : ℝ) * S := by
    intro k
    have hz : ∀ j ∈ (Finset.univ : Finset (Fin r)), ((n j ^ e k j : ℕ) : ℝ) ≠ 0 := by
      intro j _
      exact_mod_cast pow_ne_zero _ (hn0 j)
    have hlogprodk : Real.log (cr k) = ∑ j, Real.log ((n j : ℝ) ^ (e k j)) := by
      rw [hcr_apply k, Nat.cast_prod, Real.log_prod hz]
      simp only [Nat.cast_pow]
    rw [hlogprodk]
    calc ∑ j, Real.log ((n j : ℝ) ^ (e k j))
        = ∑ j, (e k j : ℝ) * Real.log (n j) :=
          Finset.sum_congr rfl fun j _ => Real.log_pow _ _
      _ ≤ ∑ j, (e k j : ℝ) * Height.logHeight₁ (β j) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hlog_n j) (Nat.cast_nonneg _)
      _ ≤ ∑ j, (d : ℝ) * Height.logHeight₁ (β j) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (by exact_mod_cast (le_of_lt (he k j)))
              (Height.zero_le_logHeight₁ _)
      _ = (d : ℝ) * S := by rw [hSdef, Finset.mul_sum]
  have hcrprod0 : (∏ k, cr k) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun k _ => hcr0 k
  have hlog_prodN : Real.log (∏ k, cr k) ≤ (d : ℝ) * ((d : ℝ) * S) := by
    rw [Real.log_prod (fun k _ => hcr0 k)]
    calc ∑ k, Real.log (cr k) ≤ ∑ _k : Fin d, (d : ℝ) * S :=
          Finset.sum_le_sum fun k _ => hlog_Nk k
      _ = (d : ℝ) * ((d : ℝ) * S) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Step 4: the embedding bound
  have hM : ∀ (k : Fin d) (τ : F →ₐ[ℚ] ℂ), ‖τ (m k)‖ ≤ Real.exp ((d : ℝ) * S) := by
    intro k τ
    refine le_trans (Real.le_exp_log _) (Real.exp_le_exp.mpr ?_)
    exact le_trans (log_norm_ringHom_le_logHeight₁ (τ : F →+* ℂ) (m k)) (hmh k)
  have hdiscr_bnd : |((Algebra.discr ℚ m : ℚ) : ℝ)| ≤
      (((d).factorial : ℝ) * (Real.exp ((d : ℝ) * S)) ^ d) ^ 2 :=
    discr_le_of_embeddings_bound m (Real.exp ((d : ℝ) * S)) (Real.exp_pos _).le hM
  have hlog_disc_b : Real.log |((Algebra.discr ℚ m : ℚ) : ℝ)| ≤
      2 * Real.log ((d.factorial : ℝ)) + 2 * (d : ℝ) * ((d : ℝ) * S) := by
    have habs : 0 < |((Algebra.discr ℚ m : ℚ) : ℝ)| :=
      abs_pos.mpr (Rat.cast_ne_zero.mpr hne_disc_b)
    have h := Real.log_le_log habs hdiscr_bnd
    have h1 : Real.log ((((d).factorial : ℝ) * (Real.exp ((d : ℝ) * S)) ^ d) ^ 2) =
        2 * Real.log ((d.factorial : ℝ)) + 2 * (d : ℝ) * ((d : ℝ) * S) := by
      rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp]
      ring
    rw [h1] at h
    exact h
  -- Combine
  have hFpos : 0 < |((NumberField.discr F : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))
  have hcrprod : (∏ k, ((c k : ℚ) : ℝ)) = ∏ k, cr k :=
    Finset.prod_congr rfl fun k _ => hcR k
  have hdiscm0 : ((Algebra.discr ℚ m : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr hne_disc_b
  have hmain : Real.log |((NumberField.discr F : ℤ) : ℝ)| ≤
      2 * Real.log ((d.factorial : ℝ)) + 4 * (d : ℝ) ^ 2 * S := by
    have h4 : Real.log |((NumberField.discr F : ℤ) : ℝ)| ≤
        Real.log |((Algebra.discr ℚ bp : ℚ) : ℝ)| := Real.log_le_log hFpos hdisc_le
    have h3 : |((Algebra.discr ℚ bp : ℚ) : ℝ)| =
        (∏ k, cr k) ^ 2 * |((Algebra.discr ℚ m : ℚ) : ℝ)| := by
      rw [hdiscr_eq]
      push_cast
      rw [hcrprod, abs_mul, abs_of_nonneg (by positivity)]
    have h5 : Real.log ((∏ k, cr k) ^ 2 * |((Algebra.discr ℚ m : ℚ) : ℝ)|) =
        2 * Real.log (∏ k, cr k) + Real.log |((Algebra.discr ℚ m : ℚ) : ℝ)| := by
      rw [Real.log_mul (pow_ne_zero _ hcrprod0) (ne_of_gt (abs_pos.mpr hdiscm0)),
        Real.log_pow]
      ring
    have h6 : Real.log |((Algebra.discr ℚ bp : ℚ) : ℝ)| =
        2 * Real.log (∏ k, cr k) + Real.log |((Algebra.discr ℚ m : ℚ) : ℝ)| := by
      rw [h3, h5]
    rw [h6] at h4
    have h7 : 2 * Real.log (∏ k, cr k) ≤ 2 * ((d : ℝ) * ((d : ℝ) * S)) :=
      mul_le_mul_of_nonneg_left hlog_prodN (by norm_num)
    linarith [h4, h7, hlog_disc_b]
  have hfinal : (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| ≤
      Real.log ((d.factorial : ℝ)) + 2 * (d : ℝ) ^ 3 * T := by
    have h1 : (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| ≤
        Real.log ((d.factorial : ℝ)) + 2 * (d : ℝ) ^ 2 * S := by linarith
    have h2 : 2 * (d : ℝ) ^ 2 * S ≤ 2 * (d : ℝ) ^ 3 * T := by
      have h3 := mul_le_mul_of_nonneg_left hS_le (show (0:ℝ) ≤ 2 * (d : ℝ) ^ 2 by positivity)
      nlinarith [h3]
    linarith [h1, h2]
  exact hfinal

end Work.BW
