import Submission.ZagierHoffmanProof.OmegaD
import Submission.ZagierHoffmanProof.SuperEntire
import Submission.Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le

/-!
# The period function `Ω` and the `L`-series lie in ABP's ring `ε`

Anderson–Brownawell–Papanikolas attach to `K∞` the ring `ε` of series converging *everywhere*
(`SuperEntire` in this workspace).  The Anderson–Thakur period function and Chang's `L`-series
are the two basic elements of that ring used in the proof of the ABP criterion
(`Ω ∈ T^×` is proved in `Omega.lean`; Lemma 5.3.1 of Chang, `𝓛(𝔰;Q) ∈ ε`, is the input that the
criterion needs).

The point of this file is that the *existing* Tate-algebra bounds are far from sharp: the
coefficients of the partial products of `Ω` are elementary symmetric functions of
`x_i = θ^{-q^i}`, whose dominant term is `x_1⋯x_m`, so

  `v (coeff m Ω) ≤ exp (-(d q + d q² + ⋯ + d q^m))`  (`d = v θ` in the additive exponent),

i.e. the coefficients decay like `exp (-d q^m)`: *doubly exponentially*.  This is exactly the
super-entireness of `Ω`.  Consequently the depth-one `L`-series `∑_{i≥0} (ω^s Q)^{(i)}`, whose
`n`-th coefficient is the `t`-sum of the `q^i`-th powers of a single coefficient of `ω^s Q` (and
is therefore bounded by the `i = 0` term), is super-entire too.

## Main results

* `sharpExp d q m` — the exponent `d(q + q² + ⋯ + q^m)` of the sharp coefficient bound.
* `coeff_omPartial_eq_zero_of_lt` — `omPartial q θ N` has degree `N`.
* ★ `v_coeff_omPartial_le_sharp`, ★ `v_coeff_atOmega_le_sharp` — the sharp bounds.
* ★★ `superEntire_atOmega` — **`Ω ∈ ε`**.
* ★★★ `superEntire_atL1Fold`, `superEntire_atL1` — **the depth-one `L`-series is in `ε`**
  (Chang, Lemma 5.3.1, depth one).
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

section arith

/-- The exponent `d·(q + q² + ⋯ + q^m) = ∑_{i<m} d·q^{i+1}` of the sharp bound for the
coefficients of the partial products of `Ω` (with `v θ = exp d`). -/
def sharpExp (d : ℤ) (q m : ℕ) : ℤ := ∑ i ∈ Finset.range m, d * ((q : ℤ)) ^ (i + 1)

lemma sharpExp_zero (d : ℤ) (q : ℕ) : sharpExp d q 0 = 0 := by
  simp [sharpExp]

lemma sharpExp_succ (d : ℤ) (q m : ℕ) :
    sharpExp d q (m + 1) = sharpExp d q m + d * ((q : ℤ)) ^ (m + 1) := by
  rw [sharpExp, Finset.sum_range_succ, sharpExp]

lemma sharpExp_nonneg (d : ℤ) (q : ℕ) (hd : 0 ≤ d) (m : ℕ) : 0 ≤ sharpExp d q m :=
  Finset.sum_nonneg fun i _ => mul_nonneg hd (pow_nonneg (by positivity) _)

lemma sharpExp_mono (d : ℤ) (q : ℕ) (hd : 0 ≤ d) {m n : ℕ} (h : m ≤ n) :
    sharpExp d q m ≤ sharpExp d q n :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun i _ _ => mul_nonneg hd (pow_nonneg (by positivity) _))

/-- The last summand of `sharpExp` is `d q^m`, so for `m ≥ 1` and `d ≥ 1` the sharp exponent
dominates `q^m`. -/
lemma pow_le_sharpExp (d : ℤ) (q m : ℕ) (hd : 1 ≤ d) (hq : 2 ≤ q) (m1 : 1 ≤ m) :
    ((q : ℤ)) ^ m ≤ sharpExp d q m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [sharpExp_succ]
  calc ((q : ℤ)) ^ (m' + 1) = 1 * ((q : ℤ)) ^ (m' + 1) := (one_mul _).symm
    _ ≤ d * ((q : ℤ)) ^ (m' + 1) :=
        mul_le_mul_of_nonneg_right hd (pow_nonneg (by positivity) _)
    _ ≤ sharpExp d q m' + d * ((q : ℤ)) ^ (m' + 1) :=
        le_add_of_nonneg_left (sharpExp_nonneg d q (by omega) m')

/-- Squares grow slower than powers of two. -/
lemma sq_le_two_pow : ∀ m : ℕ, 4 ≤ m → m ^ 2 ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 4 with h | h
    · have hm3 : m = 3 := by omega
      rw [hm3]; norm_num
    · have hm4 : 4 ≤ m := h
      have h1 : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
      have h2 : 2 * m + 1 ≤ m ^ 2 := by nlinarith
      have h3 : m ^ 2 ≤ 2 ^ m := ih hm4
      calc (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := h1
        _ ≤ m ^ 2 + m ^ 2 := Nat.add_le_add_left h2 _
        _ = 2 * m ^ 2 := by ring
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 h3
        _ = 2 ^ (m + 1) := by ring

/-- For `m ≥ max M 4` the product `M·m` is bounded by `2^m`. -/
lemma mul_le_two_pow (M m : ℕ) (h : max M 4 ≤ m) : M * m ≤ 2 ^ m := by
  have h4 : 4 ≤ m := le_trans (le_max_right _ _) h
  have hM : M ≤ m := le_trans (le_max_left _ _) h
  calc M * m ≤ m * m := Nat.mul_le_mul_right m hM
    _ = m ^ 2 := (pow_two m).symm
    _ ≤ 2 ^ m := sq_le_two_pow m h4

end arith

section bounds

variable (q : ℕ) (θ : K)

/-- The partial product `omPartial q θ N` has degree at most `N`, so its `m`-th coefficient
vanishes for `m > N`. -/
lemma coeff_omPartial_eq_zero_of_lt (N m : ℕ) (h : N < m) :
    PowerSeries.coeff m (omPartial q θ N) = 0 := by
  induction N generalizing m with
  | zero =>
    rw [omPartial_zero, PowerSeries.coeff_one, if_neg (by omega)]
  | succ N ih =>
    rw [coeff_omPartial_succ]
    have h1 : PowerSeries.coeff m (omPartial q θ N) = 0 := ih m (by omega)
    have h2 : PowerSeries.coeff (m - 1) (omPartial q θ N) = 0 := ih (m - 1) (by omega)
    rw [h1]
    by_cases hm : 1 ≤ m
    · rw [if_pos hm, h2, zero_mul, sub_zero]
    · rw [if_neg hm, sub_zero]

/-- **The sharp coefficient bound for the partial products of `Ω`**: with `v θ = exp d`, `d ≥ 1`,

  `v (coeff m (omPartial q θ N)) ≤ exp (-(d q + d q² + ⋯ + d q^m))`,

the dominant term being the elementary symmetric function `x_1⋯x_m` of `x_i = θ^{-q^i}`. -/
lemma v_coeff_omPartial_le_sharp (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : ∀ (N m : ℕ), Valued.v (PowerSeries.coeff m (omPartial q θ N))
      ≤ WithZero.exp (-(sharpExp d q m)) := by
  intro N
  induction N with
  | zero =>
    intro m
    rw [omPartial_zero, PowerSeries.coeff_one]
    by_cases h : m = 0
    · subst h
      rw [if_pos rfl, map_one, sharpExp_zero]
      simp
    · rw [if_neg h, map_zero]
      exact bot_le
  | succ N ih =>
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [coeff_omPartial_succ, if_neg (by omega : ¬ (1 ≤ 0)), sub_zero]
      exact ih 0
    · have hm1 : 1 ≤ m := hm
      by_cases hcase : m ≤ N + 1
      · rw [coeff_omPartial_succ]
        refine Valuation.map_sub_le _ (ih m) ?_
        rw [if_pos hm1, Valuation.map_mul, v_omX_d q θ d hθ (N + 1)]
        calc Valued.v (PowerSeries.coeff (m - 1) (omPartial q θ N))
                * WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ)))
            ≤ WithZero.exp (-(sharpExp d q (m - 1)))
                * WithZero.exp (-(d * (((q ^ (N + 1) : ℕ)) : ℤ))) :=
              mul_le_mul' (ih (m - 1)) le_rfl
          _ = WithZero.exp (-(sharpExp d q (m - 1))
                + -(d * (((q ^ (N + 1) : ℕ)) : ℤ))) := by rw [← WithZero.exp_add]
          _ ≤ WithZero.exp (-(sharpExp d q m)) := by
              apply WithZero.exp_le_exp.mpr
              have hm1' : m - 1 + 1 = m := by omega
              have hm2 : sharpExp d q m = sharpExp d q (m - 1) + d * ((q : ℤ)) ^ m := by
                conv_lhs => rw [← hm1']
                rw [sharpExp_succ, hm1']
              rw [hm2]
              have hpow : ((q : ℤ)) ^ m ≤ ((q ^ (N + 1) : ℕ) : ℤ) := by
                have hqm : ((q : ℤ)) ^ m = ((q ^ m : ℕ) : ℤ) := by push_cast; ring
                rw [hqm]
                exact_mod_cast Nat.pow_le_pow_right (by omega) hcase
              linarith [mul_le_mul_of_nonneg_left hpow (by omega : (0 : ℤ) ≤ d)]
      · rw [coeff_omPartial_eq_zero_of_lt q θ (N + 1) m (by omega), map_zero]
        exact bot_le

/-- **The sharp coefficient bound for `Ω`**: `v (coeff m Ω) ≤ exp (-(d q + ⋯ + d q^m))`. -/
lemma v_coeff_atOmega_le_sharp (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) [CompleteSpace K] [NonarchimedeanAddGroup K] (m : ℕ) :
    Valued.v (PowerSeries.coeff m (atOmega q θ)) ≤ WithZero.exp (-(sharpExp d q m)) := by
  rw [coeff_atOmega, omCoeff]
  refine Valuation.map_add_le _ ?_ (v_coeff_omPartial_le_sharp q θ d hd hθ hq 0 m)
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
    (summable_telescope_d q θ d hd hθ hq m) (fun N => ?_)
  refine Valuation.map_sub_le _ (v_coeff_omPartial_le_sharp q θ d hd hθ hq (N + 1) m)
    (v_coeff_omPartial_le_sharp q θ d hd hθ hq N m)

/-- **The Anderson–Thakur period function is super-entire**: `Ω ∈ ε`. -/
theorem superEntire_atOmega (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) [CompleteSpace K] [NonarchimedeanAddGroup K] :
    SuperEntire (atOmega q θ) := by
  intro M
  refine ⟨(M : ℤ) * (max M 4 : ℕ), fun m => ?_⟩
  refine le_trans (v_coeff_atOmega_le_sharp q θ d hd hθ hq m) ?_
  apply WithZero.exp_le_exp.mpr
  have hME : (0 : ℤ) ≤ (M : ℤ) * ((max M 4 : ℕ) : ℤ) := by positivity
  rcases le_or_gt m (max M 4) with h | h
  · have hm : (m : ℤ) ≤ ((max M 4 : ℕ) : ℤ) := by exact_mod_cast h
    have : (M : ℤ) * (m : ℤ) ≤ (M : ℤ) * ((max M 4 : ℕ) : ℤ) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have h5 : (0 : ℤ) ≤ sharpExp d q m := sharpExp_nonneg d q (by omega) m
    linarith
  · have h1 : ((q : ℤ)) ^ m ≤ sharpExp d q m := pow_le_sharpExp d q m hd hq (by omega)
    have h2 : ((M * m : ℕ) : ℤ) ≤ ((2 ^ m : ℕ) : ℤ) := by
      exact_mod_cast mul_le_two_pow M m (le_of_lt h)
    have h2' : (M : ℤ) * (m : ℤ) ≤ ((q : ℤ)) ^ m := by
      have h3 : ((M * m : ℕ) : ℤ) = (M : ℤ) * (m : ℤ) := by push_cast; ring
      rw [h3] at h2
      calc (M : ℤ) * (m : ℤ) ≤ ((2 ^ m : ℕ) : ℤ) := h2
        _ ≤ ((q ^ m : ℕ) : ℤ) := by exact_mod_cast Nat.pow_le_pow_left hq m
        _ = ((q : ℤ)) ^ m := by push_cast; ring
    linarith

end bounds

section lseries

variable (q : ℕ) [FrobPow K q] [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- The geometric series `∑ t^n` is a Tate series but not super-entire: its coefficients have
valuation `1`, so its coefficients do not decay at all.  Hence `ε` is a *proper* subring of the
Tate algebra `T`. -/
theorem not_superEntire_mk_one : ¬ SuperEntire (PowerSeries.mk fun _ : ℕ => (1 : K)) := by
  intro h
  obtain ⟨a, ha⟩ := h 1
  have h1 := ha (a.natAbs + 1)
  rw [PowerSeries.coeff_mk, map_one] at h1
  have hne : ¬ ((1 : ℤᵐ⁰) ≤ WithZero.exp (a - (1 : ℤ) * (((a.natAbs + 1 : ℕ)) : ℤ))) := by
    rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm, not_le, WithZero.exp_lt_exp]
    have h4 : (((a.natAbs + 1 : ℕ)) : ℤ) = (((a.natAbs : ℕ)) : ℤ) + 1 := by push_cast; ring
    rw [h4, one_mul]
    linarith [Int.le_natAbs (a := a)]
  exact hne h1

/-- The geometric series is a Tate series. -/
theorem seriesBounded_mk_one : SeriesBounded (PowerSeries.mk fun _ : ℕ => (1 : K)) := by
  refine ⟨0, fun n => ?_⟩
  rw [PowerSeries.coeff_mk, map_one,
    show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm]

/-- **`ε ⊊ T`**: there is a Tate series which is not super-entire. -/
theorem exists_tate_not_superEntire :
    ∃ f : PowerSeries K, SeriesBounded f ∧ ¬ SuperEntire f :=
  ⟨_, seriesBounded_mk_one, not_superEntire_mk_one⟩

/-- Super-entireness is inherited by series whose coefficients are pointwise dominated. -/
lemma SuperEntire.of_le {f g : PowerSeries K} (hf : SuperEntire f)
    (h : ∀ n : ℕ, Valued.v (PowerSeries.coeff n g) ≤ Valued.v (PowerSeries.coeff n f)) :
    SuperEntire g :=
  fun M => let ⟨a, ha⟩ := hf M; ⟨a, fun n => le_trans (h n) (ha n)⟩

/-- The `ε`-membership of the entries `𝓛(𝔰;Q)·Ω^{w-w'}` of the rigid analytic trivialisation
matrix `Ψ`: a product of finitely many super-entire series is super-entire. -/
lemma SuperEntire.mul_powers {f g : PowerSeries K} (hf : SuperEntire f) (hg : SuperEntire g)
    (s t : ℕ) : SuperEntire (f ^ s * g ^ t) :=
  (hf.pow s).mul (hg.pow t)

/-- A constant with small value gives a small series. -/
lemma isSmall_C {c : K} (hc : Valued.v c ≤ WithZero.exp (-1)) :
    IsSmall (PowerSeries.C c) := by
  intro n
  rw [PowerSeries.coeff_C]
  by_cases h : n = 0
  · subst h
    rw [if_pos rfl]
    exact hc
  · rw [if_neg h, map_zero]
    exact bot_le

/-- The defining family of `∑_{i≥0} f^{(q^i)}` is coefficientwise summable whenever `f` is
small: the `i`-th term has valuation `≤ (exp (-1))^{q^i} → 0`. -/
lemma summable_frobTwist_coeff (hq : 2 ≤ q) {f : PowerSeries K} (hsmall : IsSmall f) (n : ℕ) :
    Summable fun i : ℕ => PowerSeries.coeff n (frobTwist (R := K) (p := q) i f) := by
  refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero (fun N => ?_)
  rw [Filter.eventually_atTop]
  refine ⟨N.natAbs + 1, fun i hi => ?_⟩
  rw [frobTwist_coeff, map_pow]
  calc (Valued.v (PowerSeries.coeff n f)) ^ (q ^ i) ≤ (WithZero.exp (-1)) ^ (q ^ i) :=
        pow_le_pow_left' (hsmall n) _
    _ = WithZero.exp (-1 * (((q ^ i : ℕ)) : ℤ)) := expmul (-1) (q ^ i)
    _ = WithZero.exp (-(((q ^ i : ℕ)) : ℤ)) := by rw [neg_one_mul]
    _ < WithZero.exp N := by
        apply WithZero.exp_lt_exp.mpr
        have h1 : i < q ^ i := Nat.lt_pow_self (by omega : 1 < q)
        have hi' : (N.natAbs : ℤ) + 1 ≤ (i : ℤ) := by
          have : N.natAbs + 1 ≤ i := by omega
          exact_mod_cast this
        have hq' : (i : ℤ) ≤ ((q ^ i : ℕ) : ℤ) := by exact_mod_cast le_of_lt h1
        have hN : (N : ℤ) ≤ (N.natAbs : ℤ) := Int.le_natAbs
        omega

/-- **A depth-one `L`-series built from a super-entire small series is super-entire.**
For `f = ω^sQ ∈ ε` with all coefficients in the maximal ideal, the `n`-th coefficient of
`∑_{i≥0} f^{(q^i)}` is the `t`-sum of the `q^i`-th powers of a single coefficient of `f`, hence
bounded by that coefficient (`v`-powers of small elements decrease). -/
theorem superEntire_foldTwist (hq : 2 ≤ q) {f : PowerSeries K} (hsmall : IsSmall f)
    (hse : SuperEntire f) :
    SuperEntire (PowerSeries.mk fun n => ∑' i : ℕ,
      PowerSeries.coeff n (frobTwist (R := K) (p := q) i f)) := by
  intro M
  obtain ⟨a, ha⟩ := hse M
  refine ⟨a, fun n => ?_⟩
  rw [PowerSeries.coeff_mk]
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
    (summable_frobTwist_coeff q hq hsmall n) (fun i => ?_)
  rw [frobTwist_coeff, map_pow]
  have hroot : (Valued.v (PowerSeries.coeff n f)) ^ (q ^ i)
      ≤ Valued.v (PowerSeries.coeff n f) := by
    simpa using pow_le_pow_of_le_one bot_le
      (le_trans (hsmall n) exp_neg_one_le_one) (Nat.one_le_pow i q (by omega))
  exact le_trans hroot (ha n)

/-- **Chang's Lemma 5.3.1 in the depth-one case**: the `L`-series `∑_{i≥0}(ω^sQ)^{(i)}` of a
super-entire small pair `(ω,Q)` is super-entire. -/
theorem superEntire_atL1Fold (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    (hωse : SuperEntire ω) {Q : PowerSeries K} (hQ : IsSmall Q) (hQse : SuperEntire Q)
    (s : ℕ) : SuperEntire (atL1 q ω s Q) :=
  superEntire_foldTwist q hq (IsSmall.pow_mul hω hQ s) ((hωse.pow s).mul hQse)

end lseries

end ZagierHoffmanPositiveChar
