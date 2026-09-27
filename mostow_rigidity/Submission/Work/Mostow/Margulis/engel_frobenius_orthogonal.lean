import Mathlib

/-!
# The Engel/Frobenius lemma for orthogonal transformations close to the identity

`Work.Mostow.Margulis.engel_frobenius_orthogonal`: if `A` and `B` are linear isometries of a
finite-dimensional real inner product space which are close to the identity
(`‖A - 1‖ ≤ 1/2`, `‖B - 1‖ ≤ 1/2` in operator norm) and `A` commutes with the commutator
`[A,B] = A * B * A⁻¹ * B⁻¹`, then `A` and `B` commute.

The proof has two independent halves.

* **The Engel power identity.**  In any group, if `a` commutes with `c = a * b * a⁻¹ * b⁻¹`, then
  `a ^ k * b * (a ^ k)⁻¹ = c ^ k * b` for every `k` (`pow_conj_commutator`).  Mapping this into
  the algebra `V →L[ℝ] V` and multiplying by `B⁻¹` expresses `c ^ k - 1` as
  `A ^ k * (B * (A ^ k)⁻¹ - (A ^ k)⁻¹ * B) * B⁻¹`, whose norm is at most
  `2 * ‖B - 1‖ ≤ 1` (`commutator_pow_norm_le`).  Here `hA` is not needed.

* **A power-norm characterisation of the identity.**  If *every* positive power `T ^ k` of an
  isometry `T` satisfies `‖T ^ k - 1‖ ≤ 1`, then `T = 1` (`isometry_eq_one_of_pow_norm_one`).
  Otherwise pick `u` with `(T - 1) u ≠ 0` and put `v = (T - 1) u`.  Then `‖T ^ k v - v‖ ≤ ‖v‖`
  for all `k ≥ 1`, so `⟨T ^ k v, v⟩ ≥ ‖v‖² / 2`, while the Cesàro means
  `w_N = N⁻¹ • ∑_{k<N} T ^ k v = N⁻¹ • (T ^ N u - u)` tend to `0`; for large `N` this contradicts
  `⟨v, w_N⟩ ≥ ‖v‖² / 2`.

Since `‖c ^ k - 1‖ ≤ 1` for all `k ≥ 1`, the second half gives `c = 1`, i.e. `A * B = B * A`.
-/

namespace Work.Mostow.Margulis

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open scoped BigOperators

variable {V : Type*}

/-! ## The Engel power identity in a group -/

/-- **Engel power identity.**  In a group, if `a` commutes with the commutator
`c = a * b * a⁻¹ * b⁻¹`, then `a ^ k * b * (a ^ k)⁻¹ = c ^ k * b` for every `k : ℕ`. -/
theorem pow_conj_commutator {G : Type*} [Group G] (a b c : G)
    (hc : c = a * b * a⁻¹ * b⁻¹) (h : a * c = c * a) (k : ℕ) :
    a ^ k * b * (a ^ k)⁻¹ = c ^ k * b := by
  have hcomm : Commute a c := h
  have hcab : a * b * a⁻¹ = c * b := by
    rw [hc]; group
  have hck : ∀ k : ℕ, a * c ^ k * a⁻¹ = c ^ k := by
    intro k
    rw [(hcomm.pow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
  induction k with
  | zero => simp
  | succ n ih =>
    calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹
        = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by rw [pow_succ']; group
      _ = a * (c ^ n * b) * a⁻¹ := by rw [ih]
      _ = (a * c ^ n * a⁻¹) * (a * b * a⁻¹) := by group
      _ = c ^ n * (c * b) := by rw [hck n, hcab]
      _ = c ^ (n + 1) * b := by rw [pow_succ']; group

/-! ## Coercions from isometries to continuous linear maps -/

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The coercion of a power of a linear isometry to a continuous linear map is the power of the
coercion. -/
@[simp] lemma coe_pow_eq (T : V ≃ₗᵢ[ℝ] V) (m : ℕ) :
    ((T ^ m : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = (T : V →L[ℝ] V) ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : ((T ^ (n+1) : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
        = (T : V →L[ℝ] V) * ((T ^ n : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) := by
      rw [pow_succ']; simp
    rw [h, ih, pow_succ']

/-- The coercion of an isometry composed with the coercion of its inverse is the identity. -/
lemma coe_mul_inv (T : V ≃ₗᵢ[ℝ] V) :
    (T : V →L[ℝ] V) * ((T⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = 1 := by
  ext x
  rw [mul_apply_eq_comp]
  change (T : V → V) ((T : V ≃L[ℝ] V).symm x) = x
  exact (T : V ≃L[ℝ] V).apply_symm_apply x

/-- The coercion of the inverse of an isometry composed with the coercion of the isometry is the
identity. -/
lemma coe_inv_mul (T : V ≃ₗᵢ[ℝ] V) :
    ((T⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (T : V →L[ℝ] V) = 1 := by
  ext x
  rw [mul_apply_eq_comp]
  change ((T : V ≃ₗᵢ[ℝ] V).symm) ((T : V → V) x) = x
  exact (T : V ≃ₗᵢ[ℝ] V).symm_apply_apply x

/-- The operator norm of a coerced linear isometry is at most one. -/
lemma norm_coe_le_one (T : V ≃ₗᵢ[ℝ] V) : ‖(T : V →L[ℝ] V)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound (T : V →L[ℝ] V) (by norm_num) ?_
  intro x
  show ‖(T : V → V) x‖ ≤ 1 * ‖x‖
  rw [LinearIsometryEquiv.norm_map]
  simp

/-- A coerced linear isometry preserves norms. -/
lemma norm_coe_apply (T : V ≃ₗᵢ[ℝ] V) (x : V) : ‖(T : V →L[ℝ] V) x‖ = ‖x‖ :=
  LinearIsometryEquiv.norm_map T x

/-- A power of a coerced linear isometry preserves norms. -/
lemma norm_coe_pow_apply (T : V ≃ₗᵢ[ℝ] V) (k : ℕ) (x : V) :
    ‖((T : V →L[ℝ] V) ^ k) x‖ = ‖x‖ := by
  induction k generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply]
    rw [ih, norm_coe_apply]

/-! ## The power-norm characterisation of the identity -/

/-- **An isometry all of whose powers stay within operator norm `1` of the identity is the
identity.** -/
lemma isometry_eq_one_of_pow_norm_one [FiniteDimensional ℝ V] (T : V ≃ₗᵢ[ℝ] V)
    (hT : ∀ k : ℕ, 1 ≤ k → ‖(T ^ k : V →L[ℝ] V) - 1‖ ≤ 1) : T = 1 := by
  by_contra hne
  have hcoe : (⇑T) ≠ (⇑(1 : V ≃ₗᵢ[ℝ] V)) := fun h => hne (DFunLike.coe_injective h)
  obtain ⟨u, hu⟩ := Function.ne_iff.mp hcoe
  have hu' : T u ≠ u := by simpa using hu
  set v : V := (T : V →L[ℝ] V) u - u with hv
  have hvne : v ≠ 0 := by
    rw [hv]
    exact sub_ne_zero.mpr hu'
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have key : ∀ k : ℕ, 1 ≤ k → ‖(T ^ k : V →L[ℝ] V) v - v‖ ≤ ‖v‖ := by
    intro k hk
    have heq : (T ^ k : V →L[ℝ] V) v - v = ((T ^ k : V →L[ℝ] V) - 1) v := by simp
    rw [heq]
    calc ‖((T ^ k : V →L[ℝ] V) - 1) v‖
        ≤ ‖(T ^ k : V →L[ℝ] V) - 1‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (hT k hk) (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have hip : ∀ k : ℕ, ‖v‖ ^ 2 / 2 ≤ inner ℝ ((T ^ k : V →L[ℝ] V) v) v := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [pow_zero, ContinuousLinearMap.one_apply]
      rw [real_inner_self_eq_norm_sq]
      nlinarith [sq_nonneg ‖v‖]
    · have hkn : ‖(T ^ k : V →L[ℝ] V) v - v‖ ≤ ‖v‖ := key k hk
      have hsq : ‖(T ^ k : V →L[ℝ] V) v - v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
        nlinarith [norm_nonneg ((T ^ k : V →L[ℝ] V) v - v), norm_nonneg v, hkn]
      rw [norm_sub_sq_real] at hsq
      have hmap : ‖(T ^ k : V →L[ℝ] V) v‖ = ‖v‖ := norm_coe_pow_apply T k v
      rw [hmap] at hsq
      nlinarith [hsq]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 4 * ‖u‖ < (N : ℝ) * ‖v‖ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (4 * ‖u‖ / ‖v‖)
    refine ⟨N, ?_⟩
    have h : 4 * ‖u‖ / ‖v‖ < (N : ℝ) := hN
    have h2 := mul_lt_mul_of_pos_right h hvpos
    rw [div_mul_cancel₀ _ (ne_of_gt hvpos)] at h2
    exact h2
  have hNpos : 0 < N := by
    by_contra h
    have h0 : N = 0 := Nat.eq_zero_of_not_pos h
    subst h0
    simp at hN
    linarith [norm_nonneg u]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  set w : V := (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, (T ^ k : V →L[ℝ] V) v with hw
  have hlow : ‖v‖ ^ 2 / 2 ≤ inner ℝ v w := by
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNr
    rw [hw, inner_smul_right, inner_sum]
    have hsum : ∑ k ∈ Finset.range N, inner ℝ v ((T ^ k : V →L[ℝ] V) v)
        ≥ (N : ℝ) * (‖v‖ ^ 2 / 2) := by
      calc ∑ k ∈ Finset.range N, inner ℝ v ((T ^ k : V →L[ℝ] V) v)
          ≥ ∑ k ∈ Finset.range N, (‖v‖ ^ 2 / 2) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [real_inner_comm]
            exact hip k
        _ = (N : ℝ) * (‖v‖ ^ 2 / 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (N : ℝ)⁻¹ * (∑ k ∈ Finset.range N, inner ℝ v ((T ^ k : V →L[ℝ] V) v))
        ≥ (N : ℝ)⁻¹ * ((N : ℝ) * (‖v‖ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (le_of_lt hNr))
      _ = ‖v‖ ^ 2 / 2 := by rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  have htel : ∑ k ∈ Finset.range N, (T ^ k : V →L[ℝ] V) v
      = (T ^ N : V →L[ℝ] V) u - u := by
    have hstep : ∀ k : ℕ, (T ^ k : V →L[ℝ] V) v
        = (T ^ (k + 1) : V →L[ℝ] V) u - (T ^ k : V →L[ℝ] V) u := by
      intro k
      rw [hv, map_sub]
      congr 1
    simp_rw [hstep]
    rw [Finset.sum_range_sub (fun k => (T ^ k : V →L[ℝ] V) u)]
    simp
  have hwnorm : ‖w‖ ≤ (N : ℝ)⁻¹ * (2 * ‖u‖) := by
    rw [hw, htel, norm_smul]
    have h1 : ‖(T ^ N : V →L[ℝ] V) u - u‖ ≤ 2 * ‖u‖ := by
      calc ‖(T ^ N : V →L[ℝ] V) u - u‖ ≤ ‖(T ^ N : V →L[ℝ] V) u‖ + ‖u‖ := norm_sub_le _ _
        _ = ‖u‖ + ‖u‖ := by rw [norm_coe_pow_apply]
        _ = 2 * ‖u‖ := by ring
    have hNr' : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hNr)
    rw [Real.norm_of_nonneg hNr']
    exact mul_le_mul_of_nonneg_left h1 hNr'
  have hlt : ‖v‖ * ((N : ℝ)⁻¹ * (2 * ‖u‖)) < ‖v‖ ^ 2 / 2 := by
    have h2 : 2 * ‖u‖ < (N : ℝ) * (‖v‖ / 2) := by
      have h3 : (N : ℝ) * (‖v‖ / 2) = (N : ℝ) * ‖v‖ / 2 := by ring
      linarith [hN]
    have h3 : (N : ℝ)⁻¹ * (2 * ‖u‖) < (N : ℝ)⁻¹ * ((N : ℝ) * (‖v‖ / 2)) :=
      mul_lt_mul_of_pos_left h2 (inv_pos.mpr hNr)
    have h4 : (N : ℝ)⁻¹ * ((N : ℝ) * (‖v‖ / 2)) = ‖v‖ / 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hNr), one_mul]
    rw [h4] at h3
    calc ‖v‖ * ((N : ℝ)⁻¹ * (2 * ‖u‖)) < ‖v‖ * (‖v‖ / 2) :=
          mul_lt_mul_of_pos_left h3 hvpos
      _ = ‖v‖ ^ 2 / 2 := by ring
  have hupper : inner ℝ v w ≤ ‖v‖ * ((N : ℝ)⁻¹ * (2 * ‖u‖)) := by
    calc inner ℝ v w ≤ ‖v‖ * ‖w‖ := real_inner_le_norm v w
      _ ≤ ‖v‖ * ((N : ℝ)⁻¹ * (2 * ‖u‖)) := mul_le_mul_of_nonneg_left hwnorm (le_of_lt hvpos)
  linarith [hlow, hupper, hlt]

/-! ## The norm bound for the powers of the commutator -/

/-- If `A` commutes with the commutator `c = A * B * A⁻¹ * B⁻¹` and `‖B - 1‖ ≤ 1/2`, then every
positive power of `c` is within operator norm `1` of the identity. -/
lemma commutator_pow_norm_le [FiniteDimensional ℝ V] (A B : V ≃ₗᵢ[ℝ] V)
    (hB : ‖(B : V →L[ℝ] V) - 1‖ ≤ 1 / 2)
    (h : A * (A * B * A⁻¹ * B⁻¹) = (A * B * A⁻¹ * B⁻¹) * A)
    (m : ℕ) (hm : 1 ≤ m) :
    ‖(((A * B * A⁻¹ * B⁻¹) ^ m : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) - 1‖ ≤ 1 := by
  set c : V ≃ₗᵢ[ℝ] V := A * B * A⁻¹ * B⁻¹ with hc
  have h1 : A ^ m * B * (A ^ m)⁻¹ = c ^ m * B := pow_conj_commutator A B c hc h m
  have hAmAmi : (A ^ m : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = 1 := by
    rw [← coe_pow_eq A m]; exact coe_mul_inv (A ^ m)
  have hBmBi : (B : V →L[ℝ] V) * ((B⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) = 1 := coe_mul_inv B
  have hCmB : ((c ^ m : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V)
      = (A ^ m : V →L[ℝ] V) * (B : V →L[ℝ] V)
          * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) := by
    have h2 := congrArg (fun X : V ≃ₗᵢ[ℝ] V => (X : V →L[ℝ] V)) h1
    simpa using h2.symm
  have hfac : ((c ^ m : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) - 1
      = (A ^ m : V →L[ℝ] V)
        * ((B : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
            - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V))
        * ((B⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) := by
    have hleft : ((c ^ m : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) - 1
        = (((c ^ m : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V) - (B : V →L[ℝ] V))
            * ((B⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) := by
      rw [sub_mul, mul_assoc, hBmBi, mul_one]
    have hmid : ((c ^ m : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V) - (B : V →L[ℝ] V)
        = (A ^ m : V →L[ℝ] V)
          * ((B : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
              - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V)) := by
      rw [hCmB, mul_sub, mul_assoc]
      congr 1
      rw [← mul_assoc, hAmAmi, one_mul]
    rw [hleft, hmid]
  have hAm : ‖(A ^ m : V →L[ℝ] V)‖ ≤ 1 := by
    simpa using norm_coe_le_one (A ^ m)
  have hAmi : ‖(((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖ ≤ 1 :=
    norm_coe_le_one ((A ^ m)⁻¹)
  have hBi : ‖((B⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖ ≤ 1 := norm_coe_le_one (B⁻¹)
  have hinner : ‖(B : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
      - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V)‖
      ≤ 2 * ‖(B : V →L[ℝ] V) - 1‖ := by
    have hsplit : (B : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
        - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V)
        = ((B : V →L[ℝ] V) - 1) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
          - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * ((B : V →L[ℝ] V) - 1) := by
      noncomm_ring
    rw [hsplit]
    calc ‖((B : V →L[ℝ] V) - 1) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
          - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * ((B : V →L[ℝ] V) - 1)‖
        ≤ ‖((B : V →L[ℝ] V) - 1) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖
          + ‖(((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * ((B : V →L[ℝ] V) - 1)‖ :=
            norm_sub_le _ _
      _ ≤ ‖(B : V →L[ℝ] V) - 1‖ * ‖(((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖
          + ‖(((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖ * ‖(B : V →L[ℝ] V) - 1‖ :=
            add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖(B : V →L[ℝ] V) - 1‖ * 1 + 1 * ‖(B : V →L[ℝ] V) - 1‖ :=
            add_le_add (mul_le_mul_of_nonneg_left hAmi (norm_nonneg _))
              (mul_le_mul_of_nonneg_right hAmi (norm_nonneg _))
      _ = 2 * ‖(B : V →L[ℝ] V) - 1‖ := by ring
  rw [hfac]
  calc ‖(A ^ m : V →L[ℝ] V)
        * ((B : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
            - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V))
        * ((B⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖
      ≤ ‖(A ^ m : V →L[ℝ] V)
          * ((B : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
              - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V))‖
          * ‖((B⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖ := norm_mul_le _ _
    _ ≤ (‖(A ^ m : V →L[ℝ] V)‖
          * ‖(B : V →L[ℝ] V) * (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)
              - (((A ^ m)⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V) * (B : V →L[ℝ] V)‖)
          * ‖((B⁻¹ : V ≃ₗᵢ[ℝ] V) : V →L[ℝ] V)‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * (2 * ‖(B : V →L[ℝ] V) - 1‖)) * 1 := by
          refine mul_le_mul ?_ hBi (by positivity) (by positivity)
          exact mul_le_mul hAm hinner (norm_nonneg _) (by norm_num)
    _ = 2 * ‖(B : V →L[ℝ] V) - 1‖ := by ring
    _ ≤ 1 := by linarith [hB]

/-! ## The target lemma -/

theorem engel_frobenius_orthogonal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (A B : V ≃ₗᵢ[ℝ] V)
    (hA : ‖(A : V →L[ℝ] V) - 1‖ ≤ 1 / 2) (hB : ‖(B : V →L[ℝ] V) - 1‖ ≤ 1 / 2)
    (h : A * (A * B * A⁻¹ * B⁻¹) = (A * B * A⁻¹ * B⁻¹) * A) : A * B = B * A := by
  set c : V ≃ₗᵢ[ℝ] V := A * B * A⁻¹ * B⁻¹ with hc
  have hc1 : c = 1 := by
    refine isometry_eq_one_of_pow_norm_one c ?_
    intro m hm
    have h2 := commutator_pow_norm_le A B hB h m hm
    simpa [← hc] using h2
  have h1 : A * B * A⁻¹ = B := by
    calc A * B * A⁻¹ = A * B * A⁻¹ * 1 := (mul_one _).symm
      _ = A * B * A⁻¹ * (B⁻¹ * B) := by rw [inv_mul_cancel, mul_one]
      _ = (A * B * A⁻¹ * B⁻¹) * B := by group
      _ = c * B := by rw [← hc]
      _ = 1 * B := by rw [hc1]
      _ = B := one_mul _
  calc A * B = A * B * A⁻¹ * A := by group
    _ = B * A := by rw [h1]

end Work.Mostow.Margulis
