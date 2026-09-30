import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ray Hilbert function: foundational API

This file develops the elementary API of the multigraded pieces `homPiece N d` of
`MR N = ℂ[X_{ij} : i ∈ Fin (N+1), j ∈ Fin 2]` and of the ray Hilbert function
`rayHilb N D I t = dim_ℂ (R/I)_{tD}`.
-/

namespace Work.BW

open MvPolynomial

noncomputable section

variable {N : ℕ}

/-! ## The multigraded pieces -/

lemma rb_weight_mdeg_apply (e : Fin (N + 1) × Fin 2 →₀ ℕ) (j : Fin (N + 1)) :
    Finsupp.weight (mdeg N) e j = e (j, 0) + e (j, 1) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_prod_type]
  simp only [mdeg, Finset.sum_apply', Fin.sum_univ_two]
  simp [Finsupp.smul_apply, Finsupp.single_apply, Finset.sum_ite_eq', mul_add,
    Finset.sum_add_distrib]

lemma rb_weight_mdeg_eq_iff (e : Fin (N + 1) × Fin 2 →₀ ℕ) (d : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (mdeg N) e = d ↔ ∀ j, e (j, 0) + e (j, 1) = d j := by
  constructor
  · intro h j; rw [← rb_weight_mdeg_apply e j, h]
  · intro h; ext j; rw [rb_weight_mdeg_apply, h]

lemma rb_mem_homPiece_iff (d : Fin (N + 1) →₀ ℕ) (p : MR N) :
    p ∈ homPiece N d ↔ IsWeightedHomogeneous (mdeg N) p d :=
  MvPolynomial.mem_weightedHomogeneousSubmodule ℂ (mdeg N) d p

/-- The exponent vector with `(i,0) ↦ a i` and `(i,1) ↦ d i - a i`. -/
def rb_expOf (d : Fin (N + 1) →₀ ℕ) (a : (i : Fin (N + 1)) → Fin (d i + 1)) :
    Fin (N + 1) × Fin 2 →₀ ℕ :=
  ∑ i, Finsupp.single (i, 0) (a i : ℕ) + ∑ i, Finsupp.single (i, 1) (d i - a i)

lemma rb_sum_single_same (c : Fin (N + 1) → ℕ) (j : Fin (N + 1)) (w : Fin 2) :
    (∑ i, Finsupp.single (i, w) (c i)) (j, w) = c j := by
  simp [Finsupp.single_apply, Finset.sum_ite_eq']

lemma rb_sum_single_ne (c : Fin (N + 1) → ℕ) (j : Fin (N + 1)) {v w : Fin 2} (h : v ≠ w) :
    (∑ i, Finsupp.single (i, v) (c i)) (j, w) = 0 := by
  simp [Finsupp.single_apply, Finset.sum_ite_eq', Prod.ext_iff, h]

lemma rb_expOf_apply_zero (d : Fin (N + 1) →₀ ℕ)
    (a : (i : Fin (N + 1)) → Fin (d i + 1)) (j : Fin (N + 1)) :
    rb_expOf d a (j, 0) = a j := by
  rw [rb_expOf, Finsupp.add_apply, rb_sum_single_same]
  rw [rb_sum_single_ne (c := fun i => d i - a i) j (by decide : (1 : Fin 2) ≠ 0), add_zero]

lemma rb_expOf_apply_one (d : Fin (N + 1) →₀ ℕ)
    (a : (i : Fin (N + 1)) → Fin (d i + 1)) (j : Fin (N + 1)) :
    rb_expOf d a (j, 1) = d j - a j := by
  rw [rb_expOf, Finsupp.add_apply]
  rw [rb_sum_single_ne (c := fun i => (a i : ℕ)) j (by decide : (0 : Fin 2) ≠ 1), zero_add]
  rw [rb_sum_single_same]

lemma rb_weight_expOf (d : Fin (N + 1) →₀ ℕ) (a : (i : Fin (N + 1)) → Fin (d i + 1)) :
    Finsupp.weight (mdeg N) (rb_expOf d a) = d := by
  rw [rb_weight_mdeg_eq_iff]
  intro j
  rw [rb_expOf_apply_zero, rb_expOf_apply_one]
  omega

lemma expOf_injective (d : Fin (N + 1) →₀ ℕ) :
    Function.Injective (fun a : (i : Fin (N + 1)) → Fin (d i + 1) => rb_expOf d a) := by
  intro a a' h
  funext j
  apply Fin.ext
  have h' := congr_arg (fun e => e (j, 0)) h
  simpa [rb_expOf_apply_zero] using h'

lemma expOf_surjective (d : Fin (N + 1) →₀ ℕ) (e : Fin (N + 1) × Fin 2 →₀ ℕ)
    (he : Finsupp.weight (mdeg N) e = d) : ∃ a, rb_expOf d a = e := by
  refine ⟨fun j => Fin.mk (e (j, 0)) (by
    have h : e (j, 0) + e (j, 1) = d j := by rw [← rb_weight_mdeg_apply e j, he]
    omega), ?_⟩
  apply Finsupp.ext
  intro v
  obtain ⟨j, c⟩ := v
  fin_cases c
  · show (rb_expOf d (fun j => Fin.mk (e (j, 0)) (by
      have h : e (j, 0) + e (j, 1) = d j := by rw [← rb_weight_mdeg_apply e j, he]
      omega))) (j, 0) = e (j, 0)
    simp [rb_expOf_apply_zero]
  · have h : e (j, 0) + e (j, 1) = d j := by rw [← rb_weight_mdeg_apply e j, he]
    show (rb_expOf d (fun j => Fin.mk (e (j, 0)) (by
      have h : e (j, 0) + e (j, 1) = d j := by rw [← rb_weight_mdeg_apply e j, he]
      omega))) (j, 1) = e (j, 1)
    rw [rb_expOf_apply_one]
    simp only [Fin.val_mk]
    omega

/-- Bijection between tuples `a i ≤ d i` and exponent vectors of weight `d`. -/
def rb_mdegEquiv (d : Fin (N + 1) →₀ ℕ) :
    ((i : Fin (N + 1)) → Fin (d i + 1)) ≃
      {e : Fin (N + 1) × Fin 2 →₀ ℕ | Finsupp.weight (mdeg N) e = d} :=
  Equiv.ofBijective
    (fun a => (⟨rb_expOf d a, rb_weight_expOf d a⟩ :
      {e : Fin (N + 1) × Fin 2 →₀ ℕ | Finsupp.weight (mdeg N) e = d}))
    ⟨fun a a' h => expOf_injective d (congrArg Subtype.val h), fun e => by
      obtain ⟨a, ha⟩ := expOf_surjective d e.1 e.2
      exact ⟨a, Subtype.ext ha⟩⟩

instance rbInstFintypeWeightSet (d : Fin (N + 1) →₀ ℕ) :
    Fintype {e : Fin (N + 1) × Fin 2 →₀ ℕ | Finsupp.weight (mdeg N) e = d} :=
  Fintype.ofEquiv _ (rb_mdegEquiv d)

lemma rb_homPiece_eq_restrictSupport (d : Fin (N + 1) →₀ ℕ) :
    homPiece N d =
      MvPolynomial.restrictSupport ℂ {e : Fin (N + 1) × Fin 2 →₀ ℕ |
        Finsupp.weight (mdeg N) e = d} := by
  rw [homPiece, MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    MvPolynomial.restrictSupport]

/-- The multihomogeneous piece of multidegree `d` is finite dimensional, of dimension
`∏ᵢ (dᵢ + 1)`. -/
theorem rb_finrank_homPiece (d : Fin (N + 1) →₀ ℕ) :
    Module.finrank ℂ (homPiece N d) = ∏ i, (d i + 1) := by
  rw [rb_homPiece_eq_restrictSupport,
    Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℂ
      {e : Fin (N + 1) × Fin 2 →₀ ℕ | Finsupp.weight (mdeg N) e = d})]
  rw [← Fintype.card_congr (rb_mdegEquiv d), Fintype.card_pi]
  simp

instance rbInstModuleFiniteHomPiece (d : Fin (N + 1) →₀ ℕ) : Module.Finite ℂ (homPiece N d) := by
  rw [rb_homPiece_eq_restrictSupport]
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport ℂ _)

lemma rb_finrank_homPiece_smul (D : Fin (N + 1) →₀ ℕ) (t : ℕ) :
    Module.finrank ℂ (homPiece N (t • D)) = ∏ i, (t * D i + 1) := by
  rw [rb_finrank_homPiece]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Finsupp.smul_apply]

/-! ## The ray Hilbert function -/

lemma rb_rayHilb_bot (D : Fin (N + 1) →₀ ℕ) (t : ℕ) :
    rayHilb N D ⊥ t = ∏ i, (t * D i + 1) := by
  have h1 : (⊥ : Ideal (MR N)).restrictScalars ℂ = ⊥ := rfl
  rw [rayHilb, h1, Submodule.comap_bot, Submodule.ker_subtype]
  have h2 := Submodule.finrank_quotient_add_finrank (⊥ : Submodule ℂ (homPiece N (t • D)))
  rw [finrank_bot, add_zero] at h2
  rw [h2, rb_finrank_homPiece_smul]

/-- The ray Hilbert function is antitone in the ideal. -/
lemma rb_rayHilb_le_rayHilb {D : Fin (N + 1) →₀ ℕ} {I J : Ideal (MR N)} (h : I ≤ J) (t : ℕ) :
    rayHilb N D J t ≤ rayHilb N D I t := by
  have hsub : Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ) ≤
      Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ) := by
    intro x hx
    simp only [Submodule.mem_comap] at hx ⊢
    exact h hx
  have h1 := Submodule.finrank_quotient_add_finrank
    (N := Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ))
  have h2 := Submodule.finrank_quotient_add_finrank
    (N := Submodule.comap (homPiece N (t • D)).subtype (J.restrictScalars ℂ))
  have h3 : Module.finrank ℂ ↥(Submodule.comap (homPiece N (t • D)).subtype
      (I.restrictScalars ℂ)) ≤
      Module.finrank ℂ ↥(Submodule.comap (homPiece N (t • D)).subtype
        (J.restrictScalars ℂ)) := Submodule.finrank_mono hsub
  rw [rayHilb, rayHilb]
  omega

/-! ## `IsRayPoly`, `rayPoly` -/

theorem IsRayPoly.rb_unique {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)} {q q' : Polynomial ℚ}
    (h : IsRayPoly N D I q) (h' : IsRayPoly N D I q') : q = q' := by
  rw [IsRayPoly] at h h'
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 h
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.1 h'
  have hsub : Set.Ici (max a b) ⊆ {t : ℕ | q.eval (t : ℚ) = q'.eval (t : ℚ)} := by
    intro t ht
    simp only [Set.mem_ofPred_eq]
    rw [← ha t (le_trans (le_max_left a b) ht), ← hb t (le_trans (le_max_right a b) ht)]
  have hinj : Set.InjOn (fun t : ℕ => (t : ℚ)) (Set.Ici (max a b)) :=
    fun s _ t _ h => Nat.cast_injective h
  have himg := Set.Infinite.image hinj (Set.Ici_infinite (max a b))
  refine Polynomial.eq_of_infinite_eval_eq q q' (Set.Infinite.mono ?_ himg)
  rintro x ⟨t, ht, rfl⟩
  exact hsub ht

theorem rb_rayPoly_spec {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)}
    (h : ∃ q, IsRayPoly N D I q) : IsRayPoly N D I (rayPoly N D I) := by
  rw [rayPoly, dif_pos h]
  exact Classical.choose_spec h

theorem rb_rayPoly_eq_iff {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)} (h : ∃ q, IsRayPoly N D I q)
    {q : Polynomial ℚ} : rayPoly N D I = q ↔ IsRayPoly N D I q := by
  constructor
  · intro he; rw [← he]; exact rb_rayPoly_spec h
  · intro hq; exact IsRayPoly.rb_unique (rb_rayPoly_spec h) hq

theorem rb_rayPoly_ne_zero_iff {D : Fin (N + 1) →₀ ℕ} {I : Ideal (MR N)} :
    rayPoly N D I ≠ 0 ↔ ∃ q : Polynomial ℚ, IsRayPoly N D I q ∧ q ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    have hc' : ∀ q : Polynomial ℚ, IsRayPoly N D I q → q = 0 := by
      intro q hq
      by_contra hq0
      exact hc ⟨q, hq, hq0⟩
    rw [rayPoly] at h
    split at h
    · next hh => exact h (hc' _ (Classical.choose_spec hh))
    · next hh => exact h rfl
  · rintro ⟨q, hq, hq0⟩ h
    exact hq0 (IsRayPoly.rb_unique hq ((rb_rayPoly_eq_iff ⟨q, hq⟩).1 h))

/-! ## `⊥`: the ray polynomial is `∏ᵢ (t Dᵢ + 1)` -/

/-- The polynomial `t ↦ ∏ᵢ (t Dᵢ + 1)`. -/
noncomputable def rb_botPoly (N : ℕ) (D : Fin (N + 1) →₀ ℕ) : Polynomial ℚ :=
  ∏ i, (Polynomial.C (D i : ℚ) * Polynomial.X + 1)

lemma rb_botPoly_eval (D : Fin (N + 1) →₀ ℕ) (t : ℕ) :
    (rb_botPoly N D).eval (t : ℚ) = ((∏ i, (t * D i + 1) : ℕ) : ℚ) := by
  rw [rb_botPoly, Polynomial.eval_prod]
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one]
  ring

theorem rb_isRayPoly_bot (D : Fin (N + 1) →₀ ℕ) : IsRayPoly N D ⊥ (rb_botPoly N D) := by
  rw [IsRayPoly]
  refine Filter.Eventually.of_forall fun t => ?_
  rw [rb_rayHilb_bot, rb_botPoly_eval]

lemma rb_natDegree_C_mul_X_add_one (a : ℚ) (ha : a ≠ 0) :
    (Polynomial.C a * Polynomial.X + 1 : Polynomial ℚ).natDegree = 1 := by
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_one]
    have h1 : n ≠ 1 := by omega
    have h0 : n ≠ 0 := by omega
    simp [h1, h0]
  · apply Polynomial.le_natDegree_of_ne_zero (n := 1)
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
    simp [ha]

lemma rb_leadingCoeff_C_mul_X_add_one (a : ℚ) (ha : a ≠ 0) :
    (Polynomial.C a * Polynomial.X + 1 : Polynomial ℚ).leadingCoeff = a := by
  rw [Polynomial.leadingCoeff, rb_natDegree_C_mul_X_add_one a ha]
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
  simp [ha]

lemma rb_C_mul_X_add_one_ne_zero (a : ℚ) :
    (Polynomial.C a * Polynomial.X + 1 : Polynomial ℚ) ≠ 0 := by
  intro h
  have := congr_arg (fun p : Polynomial ℚ => p.coeff 0) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_one,
    Polynomial.coeff_zero] at this
  simp at this

lemma rb_natDegree_botPoly (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) :
    (rb_botPoly N D).natDegree = N + 1 := by
  rw [rb_botPoly, Polynomial.natDegree_prod _ _ (fun i _ => rb_C_mul_X_add_one_ne_zero _)]
  rw [Finset.sum_congr rfl (fun i _ => rb_natDegree_C_mul_X_add_one _ (by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (hD i))))]
  simp

lemma rb_leadingCoeff_botPoly (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) :
    (rb_botPoly N D).leadingCoeff = ∏ i, (D i : ℚ) := by
  rw [rb_botPoly, Polynomial.leadingCoeff_prod]
  exact Finset.prod_congr rfl fun i _ => rb_leadingCoeff_C_mul_X_add_one _ (by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (hD i)))

lemma rb_botPoly_ne_zero (D : Fin (N + 1) →₀ ℕ) : rb_botPoly N D ≠ 0 := by
  rw [rb_botPoly]
  exact Finset.prod_ne_zero_iff.2 fun i _ => rb_C_mul_X_add_one_ne_zero _

/-- **A3c**: `H(G; D) = (N+1)! ∏ Dᵢ`. -/
theorem rb_rayDeg_bot (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) :
    rayPoly N D ⊥ ≠ 0 ∧ rayDim N D ⊥ = N + 1 ∧
      rayDeg N D ⊥ = ((N + 1).factorial : ℚ) * ∏ i, (D i : ℚ) := by
  have hq := rb_isRayPoly_bot (N := N) D
  have hpoly : rayPoly N D ⊥ = rb_botPoly N D := (rb_rayPoly_eq_iff ⟨_, hq⟩).2 hq
  refine ⟨?_, ?_, ?_⟩
  · rw [hpoly]; exact rb_botPoly_ne_zero D
  · rw [rayDim, hpoly, rb_natDegree_botPoly D hD]
  · rw [rayDeg, hpoly, rb_natDegree_botPoly D hD, rb_leadingCoeff_botPoly D hD]

/-- A polynomial that is non-negative at all large natural numbers has non-negative leading
coefficient. -/
lemma rb_leadingCoeff_nonneg_of_eventually {q : Polynomial ℚ}
    (h : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ q.eval (t : ℚ)) : 0 ≤ q.leadingCoeff := by
  by_contra hc
  rw [not_le] at hc
  rcases eq_or_ne q 0 with rfl | hq
  · simp at hc
  have hdeg : 0 ≤ q.degree := Polynomial.zero_le_degree_iff.mpr hq
  rcases eq_or_lt_of_le hdeg with h0 | hpos
  · have hcoeff : q.coeff 0 = q.leadingCoeff := by
      rw [Polynomial.leadingCoeff]
      congr 1
      exact (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0.symm)).symm
    have hqC : q = Polynomial.C q.leadingCoeff :=
      (Polynomial.eq_C_of_degree_le_zero (le_of_eq h0.symm)).trans
        (congrArg Polynomial.C hcoeff)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    have := hN N le_rfl
    rw [hqC, Polynomial.eval_C] at this
    linarith
  · have htend : Filter.Tendsto (fun t : ℚ => q.eval t) Filter.atTop Filter.atBot :=
      q.tendsto_atBot_of_leadingCoeff_nonpos hpos (le_of_lt hc)
    have hevN : ∀ᶠ t : ℕ in Filter.atTop, q.eval (t : ℚ) < 0 :=
      (htend.comp tendsto_natCast_atTop_atTop) (Filter.eventually_lt_atBot 0)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hevN
    have h1 := hN (max N M) (le_max_left _ _)
    have h2 := hM (max N M) (le_max_right _ _)
    linarith

/-! ## Monotonicity of `rayDim` -/

/-- If two polynomials are non-negative at all large natural numbers and one dominates the other
there, then its degree is at most the other's. -/
lemma rb_natDegree_le_of_eventually_le {p q : Polynomial ℚ}
    (hp : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ p.eval (t : ℚ))
    (h : ∀ᶠ t : ℕ in Filter.atTop, p.eval (t : ℚ) ≤ q.eval (t : ℚ)) :
    p.natDegree ≤ q.natDegree := by
  by_contra hc
  rw [not_le] at hc
  have hp_ne : p ≠ 0 := by
    rintro rfl
    simp at hc
  have hpdeg : 0 < p.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    exact lt_of_le_of_lt (Nat.zero_le _) hc
  have hlc : 0 < p.leadingCoeff := by
    have h1 : 0 ≤ p.leadingCoeff := rb_leadingCoeff_nonneg_of_eventually hp
    have h2 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have hqp : q.degree < p.degree := by
    calc q.degree ≤ ((q.natDegree : ℕ) : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < ((p.natDegree : ℕ) : WithBot ℕ) := by exact_mod_cast hc
      _ = p.degree := (Polynomial.degree_eq_natDegree hp_ne).symm
  have hsub : (p - q).leadingCoeff = p.leadingCoeff :=
    Polynomial.leadingCoeff_sub_of_degree_lt hqp
  have hsubdeg : 0 < (p - q).degree := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hqp]
    exact hpdeg
  have htend : Filter.Tendsto (fun t : ℚ => (p - q).eval t) Filter.atTop Filter.atTop :=
    (p - q).tendsto_atTop_of_leadingCoeff_nonneg hsubdeg (le_of_lt (by rw [hsub]; exact hlc))
  have hev : ∀ᶠ t : ℕ in Filter.atTop, 0 < (p - q).eval (t : ℚ) :=
    (htend.comp tendsto_natCast_atTop_atTop) (Filter.eventually_gt_atTop 0)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.1 h
  have h1 := hT (max T S) (le_max_left _ _)
  have h2 := hS (max T S) (le_max_right _ _)
  rw [Polynomial.eval_sub] at h1
  linarith

/-- `rayDim` is antitone in the ideal: a larger multihomogeneous ideal (with ray polynomials) has
no larger ray dimension. -/
theorem rb_rayDim_anti {D : Fin (N + 1) →₀ ℕ} {I J : Ideal (MR N)} (hIJ : I ≤ J)
    (hI : ∃ q, IsRayPoly N D I q) (hJ : ∃ q, IsRayPoly N D J q) :
    rayDim N D J ≤ rayDim N D I := by
  refine rb_natDegree_le_of_eventually_le ?_ ?_
  · filter_upwards [rb_rayPoly_spec hJ] with t ht
    rw [← ht]; positivity
  · filter_upwards [rb_rayPoly_spec hI, rb_rayPoly_spec hJ] with t ht1 ht2
    rw [← ht1, ← ht2]
    exact_mod_cast rb_rayHilb_le_rayHilb hIJ t


end

end Work.BW
