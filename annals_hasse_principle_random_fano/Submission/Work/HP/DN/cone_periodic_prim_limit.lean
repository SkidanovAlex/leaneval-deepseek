import Mathlib
import Submission.Work.HP.DN.Defs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.DNC.shifted_card_div_pow_tendsto
import Submission.Work.HP.DNC.periodic_count_real
import Submission.Work.HP.DNC.moebius_prim_ncard

set_option autoImplicit false
noncomputable section

namespace Work.HP.DN

open Filter Finset MeasureTheory Pointwise
open Work.HP

/-! ## Elementary facts about `eNorm`, `rNorm`, primitivity and scaling -/

private lemma cpl_abs_coord_le_eNorm {ι : Type*} [Fintype ι] (a : ι → ℤ) (i : ι) :
    |(a i : ℝ)| ≤ eNorm a := by
  have h : ((a i : ℝ)) ^ 2 ≤ ∑ j, ((a j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((a j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc |(a i : ℝ)| = Real.sqrt (((a i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((a j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h
    _ = eNorm a := rfl

private lemma cpl_abs_coord_le_rNorm {ι : Type*} [Fintype ι] (t : ι → ℝ) (i : ι) :
    |t i| ≤ rNorm t := by
  have h : (t i) ^ 2 ≤ ∑ j, (t j) ^ 2 :=
    Finset.single_le_sum (f := fun j => (t j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc |t i| = Real.sqrt ((t i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, (t j) ^ 2) := Real.sqrt_le_sqrt h
    _ = rNorm t := rfl

private lemma cpl_rNorm_nonneg {ι : Type*} [Fintype ι] (t : ι → ℝ) : 0 ≤ rNorm t :=
  Real.sqrt_nonneg _

private lemma cpl_rNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (t : ι → ℝ) :
    rNorm (c • t) = |c| * rNorm t := by
  have h1 : ∑ i, ((c • t) i) ^ 2 = c ^ 2 * ∑ i, (t i) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [rNorm, rNorm, h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

private lemma cpl_one_le_eNorm {ι : Type*} [Fintype ι] {a : ι → ℤ} (ha : a ≠ 0) :
    (1 : ℝ) ≤ eNorm a := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact ha (funext h)
  have h1 : (1 : ℝ) ≤ |(a i : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |a i| := Int.one_le_abs hi
    exact_mod_cast h2
  exact le_trans h1 (cpl_abs_coord_le_eNorm a i)

private lemma cpl_isPrim_ne_zero {ι : Type*} [Fintype ι] {a : ι → ℤ} (h : IsPrim a) :
    a ≠ 0 := by
  intro h0
  rw [IsPrim] at h
  have h1 : Finset.univ.gcd a = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun i _ => by rw [h0]; rfl)
  rw [h] at h1
  exact one_ne_zero h1

private lemma cpl_toR_int_smul {ι : Type*} (k : ℤ) (b : ι → ℤ) :
    toR (k • b) = (k : ℝ) • toR b := by
  funext i
  simp only [toR, Pi.smul_apply, smul_eq_mul, Int.cast_mul]

private lemma cpl_eNorm_int_smul {ι : Type*} [Fintype ι] (k : ℤ) (b : ι → ℤ) :
    eNorm (k • b) = |(k : ℝ)| * eNorm b := by
  have h1 : ∑ i, (((k • b) i : ℝ)) ^ 2 = ((k : ℝ)) ^ 2 * ∑ i, ((b i : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    ring
  rw [eNorm, eNorm, h1, Real.sqrt_mul (sq_nonneg (k : ℝ)), Real.sqrt_sq_eq_abs]

private lemma cpl_moebius_zero : ArithmeticFunction.moebius 0 = 0 :=
  ArithmeticFunction.moebius_eq_zero_of_not_squarefree not_squarefree_zero

/-! ## The unit ball is bounded and closed -/

private lemma cpl_isBounded_unitBallR {ι : Type*} [Fintype ι] :
    Bornology.IsBounded (unitBallR ι) := by
  refine (Metric.isBounded_closedBall (x := (0 : ι → ℝ)) (r := 1)).subset ?_
  intro t ht
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  simpa [Real.norm_eq_abs] using le_trans (cpl_abs_coord_le_rNorm t i) ht

private lemma cpl_isClosed_unitBallR {ι : Type*} [Fintype ι] : IsClosed (unitBallR ι) := by
  have hcont : Continuous (fun t : ι → ℝ => ∑ i, (t i) ^ 2) :=
    continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)
  have h1 : unitBallR ι = {t : ι → ℝ | ∑ i, (t i) ^ 2 ≤ 1} := by
    ext t
    simp only [unitBallR, Set.mem_setOf_eq, rNorm]
    exact Real.sqrt_le_one
  rw [h1]
  exact isClosed_le hcont continuous_const

/-! ## Finiteness of the set of integer vectors of bounded norm -/

private lemma cpl_finite_eNorm_le {ι : Type*} [Fintype ι] (T : ℝ) :
    ({b : ι → ℤ | eNorm b ≤ T} : Set (ι → ℤ)).Finite := by
  classical
  set K : ℕ := ⌈T⌉₊ with hKdef
  refine Set.Finite.subset (Finset.finite_toSet
    (Fintype.piFinset (fun _ : ι => Finset.Icc (-((K : ℤ))) ((K : ℤ))))) ?_
  intro b hb
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 : |(b i : ℝ)| ≤ ((K : ℕ) : ℝ) := by
    rw [hKdef]
    exact le_trans (le_trans (cpl_abs_coord_le_eNorm b i) hb) (Nat.le_ceil T)
  have h2 : |(b i : ℤ)| ≤ ((K : ℕ) : ℤ) := by exact_mod_cast h1
  exact abs_le.mp h2

private lemma cpl_ncard_eNorm_le_pow {ι : Type*} [Fintype ι] (T : ℝ) (hT : 1 ≤ T) :
    ((({b : ι → ℤ | eNorm b ≤ T} : Set (ι → ℤ)).ncard : ℝ)) ≤ (5 * T) ^ Fintype.card ι := by
  classical
  set K : ℕ := ⌈T⌉₊ with hKdef
  have hbox : ∀ b : ι → ℤ, eNorm b ≤ T →
      b ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-((K : ℤ))) ((K : ℤ))) := by
    intro b hb
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 : |(b i : ℝ)| ≤ ((K : ℕ) : ℝ) := by
      rw [hKdef]
      exact le_trans (le_trans (cpl_abs_coord_le_eNorm b i) hb) (Nat.le_ceil T)
    have h2 : |(b i : ℤ)| ≤ ((K : ℕ) : ℤ) := by exact_mod_cast h1
    exact abs_le.mp h2
  have h1 : ({b : ι → ℤ | eNorm b ≤ T} : Set (ι → ℤ)).ncard ≤
      (Fintype.piFinset (fun _ : ι => Finset.Icc (-((K : ℤ))) ((K : ℤ)))).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun b hb => hbox b hb) (Finset.finite_toSet _)
  have hIcc : ∀ _ : ι, (Finset.Icc (-((K : ℤ))) ((K : ℤ))).card = 2 * K + 1 := by
    intro _
    rw [Int.card_Icc]
    have h4 : ((K : ℤ) + 1 - -((K : ℤ))) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h4, Int.toNat_natCast]
  have h2 : (Fintype.piFinset (fun _ : ι => Finset.Icc (-((K : ℤ))) ((K : ℤ)))).card =
      (2 * K + 1) ^ Fintype.card ι := by
    rw [Fintype.card_piFinset, Finset.prod_congr rfl (fun i _ => hIcc i), Finset.prod_const,
      Finset.card_univ]
  have h3 : ((2 * K + 1 : ℕ) : ℝ) ≤ 5 * T := by
    have h5 : (K : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
    have h6 : (1 : ℝ) ≤ T := hT
    push_cast
    linarith
  calc (({b : ι → ℤ | eNorm b ≤ T} : Set (ι → ℤ)).ncard : ℝ)
      ≤ ((Fintype.piFinset (fun _ : ι => Finset.Icc (-((K : ℤ))) ((K : ℤ)))).card : ℝ) := by
        exact_mod_cast h1
    _ = (((2 * K + 1 : ℕ)) : ℝ) ^ Fintype.card ι := by rw [h2, Nat.cast_pow]
    _ ≤ (5 * T) ^ Fintype.card ι := pow_le_pow_left₀ (by positivity) h3 _

/-! ## The scale invariance of the cone, in the form used by `periodic_count_real` -/

private lemma cpl_star_of_cone {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (hK : ∀ (s : ℝ) (t : ι → ℝ), 0 < s → (t ∈ K ↔ s • t ∈ K)) :
    ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → ∀ z : ι → ℝ, z ∈ K ∩ unitBallR ι →
      (x / y) • z ∈ K ∩ unitBallR ι := by
  intro x y hx hxy z hz
  obtain ⟨hzK, hzu⟩ := hz
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxy1 : x / y ≤ 1 := (div_le_one hy).mpr hxy
  have hpos : (0 : ℝ) < x / y := by positivity
  refine ⟨(hK (x / y) z hpos).mp hzK, ?_⟩
  have hz2 : rNorm z ≤ 1 := hzu
  show rNorm ((x / y) • z) ≤ 1
  rw [cpl_rNorm_smul, abs_of_pos hpos]
  calc x / y * rNorm z ≤ 1 * 1 := mul_le_mul hxy1 hz2 (cpl_rNorm_nonneg z) (by norm_num)
    _ = 1 := by norm_num

/-! ## Membership in `K ∩ unitBallR` in terms of `b / T` -/

private lemma cpl_mem_inter_iff {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (hK : ∀ (s : ℝ) (t : ι → ℝ), 0 < s → (t ∈ K ↔ s • t ∈ K))
    {T : ℝ} (hT : 0 < T) (b : ι → ℤ) :
    ((fun i => (b i : ℝ) / T) ∈ K ∩ unitBallR ι) ↔ (toR b ∈ K ∧ eNorm b ≤ T) := by
  have hdiv : (fun i => (b i : ℝ) / T) = (1 / T) • toR b := by
    funext i
    simp only [toR, Pi.smul_apply, smul_eq_mul]
    ring
  have h1T : (0 : ℝ) < 1 / T := by positivity
  rw [Set.mem_inter_iff, hdiv]
  constructor
  · rintro ⟨hK', hball⟩
    refine ⟨(hK (1 / T) (toR b) h1T).mpr hK', ?_⟩
    have hball' : rNorm ((1 / T) • toR b) ≤ 1 := hball
    rw [cpl_rNorm_smul, abs_of_pos h1T, show rNorm (toR b) = eNorm b from rfl,
      one_div_mul_eq_div] at hball'
    exact (div_le_one hT).mp hball'
  · rintro ⟨hK', hle⟩
    refine ⟨(hK (1 / T) (toR b) h1T).mp hK', ?_⟩
    show rNorm ((1 / T) • toR b) ≤ 1
    rw [cpl_rNorm_smul, abs_of_pos h1T, show rNorm (toR b) = eNorm b from rfl,
      one_div_mul_eq_div]
    exact (div_le_one hT).mpr hle

/-! ## Elementary arithmetic -/

private lemma cpl_div_pow_div {n : ℕ} (c x y : ℝ) (hy : y ≠ 0) :
    c / (x / y) ^ n / y ^ n = c / x ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [zero_pow hn]
  · have hxy : x / y ≠ 0 := div_ne_zero hx hy
    have hxyn : (x / y) ^ n ≠ 0 := pow_ne_zero _ hxy
    have hyn : y ^ n ≠ 0 := pow_ne_zero _ hy
    field_simp
    rw [mul_assoc, ← mul_pow, div_mul_cancel₀ x hy]

private lemma cpl_five_div {N : ℕ} (A k : ℝ) (hA : A ≠ 0) (hk : k ≠ 0) :
    (5 * (A / k)) ^ N / A ^ N = (5 : ℝ) ^ N / k ^ N := by
  have hAn : A ^ N ≠ 0 := pow_ne_zero _ hA
  have hkn : k ^ N ≠ 0 := pow_ne_zero _ hk
  rw [mul_pow, div_pow]
  field_simp

/-! ## Removing `b = 0` and passing to a quotient -/

private lemma cpl_abs_ncard_sdiff_zero {ι : Type*} [Fintype ι] {s : Set (ι → ℤ)}
    (hs : s.Finite) :
    |(((s \ {0}).ncard : ℕ) : ℝ) - (((s.ncard : ℕ) : ℝ))| ≤ 1 := by
  have h1 : (s \ {0}).ncard ≤ s.ncard := Set.ncard_le_ncard Set.sdiff_subset hs
  have h2 : s.ncard ≤ (s \ {0}).ncard + 1 := by
    by_cases h0 : (0 : ι → ℤ) ∈ s
    · calc s.ncard = (insert (0 : ι → ℤ) (s \ {0})).ncard := by
            rw [Set.insert_sdiff_singleton, Set.insert_eq_of_mem h0]
        _ ≤ (s \ {0}).ncard + 1 := Set.ncard_insert_le _ _
    · rw [Set.sdiff_singleton_eq_self h0]
      omega
  have h1' : (((s \ {0}).ncard : ℕ) : ℝ) ≤ ((s.ncard : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : ((s.ncard : ℕ) : ℝ) ≤ (((s \ {0}).ncard : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

private lemma cpl_tendsto_div_of_sub_le_one {N : ℕ} (hN : N ≠ 0) {L : ℝ} {F G : ℝ → ℝ}
    (hF : Tendsto (fun T : ℝ => F T / T ^ N) atTop (nhds L))
    (hdiff : ∀ᶠ T : ℝ in atTop, |F T - G T| ≤ 1) :
    Tendsto (fun T : ℝ => G T / T ^ N) atTop (nhds L) := by
  have hpow : Tendsto (fun T : ℝ => T ^ N) atTop atTop := tendsto_pow_atTop hN
  have hε : Tendsto (fun T : ℝ => (F T - G T) / T ^ N) atTop (nhds 0) := by
    have h1 : Tendsto (fun T : ℝ => (1 : ℝ) / T ^ N) atTop (nhds 0) := hpow.const_div_atTop 1
    have h2 : Tendsto (fun T : ℝ => (-1 : ℝ) / T ^ N) atTop (nhds 0) := hpow.const_div_atTop (-1)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 ?_ ?_
    · filter_upwards [hdiff, eventually_gt_atTop (0 : ℝ)] with T hd hT
      have hTp : 0 < T ^ N := pow_pos hT _
      rw [div_le_div_iff_of_pos_right hTp]
      exact (abs_le.mp hd).1
    · filter_upwards [hdiff, eventually_gt_atTop (0 : ℝ)] with T hd hT
      have hTp : 0 < T ^ N := pow_pos hT _
      rw [div_le_div_iff_of_pos_right hTp]
      exact (abs_le.mp hd).2
  have h3 : Tendsto (fun T : ℝ => F T / T ^ N - (F T - G T) / T ^ N) atTop (nhds (L - 0)) :=
    hF.sub hε
  have hfin : (fun T : ℝ => F T / T ^ N - (F T - G T) / T ^ N) =ᶠ[atTop]
      (fun T : ℝ => G T / T ^ N) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hT0 : T ^ N ≠ 0 := pow_ne_zero _ (ne_of_gt hT)
    field_simp
    ring
  simpa using h3.congr' hfin

/-! ## The two counting functions -/

/-- All vectors with `b / T ∈ K`, `toR b ∈ K`, satisfying the predicate `P` composed with `k •`. -/
private noncomputable def cplH {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (P : (ι → ℤ) → Prop) (k : ℕ) (T : ℝ) : ℝ :=
  (({b : ι → ℤ | eNorm b ≤ T ∧ toR b ∈ K ∧ P ((k : ℤ) • b)} : Set (ι → ℤ)).ncard : ℝ)

/-- The same count restricted to `b ≠ 0`. -/
private noncomputable def cplG {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (P : (ι → ℤ) → Prop) (k : ℕ) (T : ℝ) : ℝ :=
  (({b : ι → ℤ | b ≠ 0 ∧ eNorm b ≤ T ∧ toR b ∈ K ∧ P ((k : ℤ) • b)} : Set (ι → ℤ)).ncard : ℝ)

/-- The primitive count. -/
private noncomputable def cplF {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (P : (ι → ℤ) → Prop) (A : ℝ) : ℝ :=
  (({a : ι → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a} : Set (ι → ℤ)).ncard : ℝ)

/-- The `k`-th Tannery summand. -/
private noncomputable def cplu {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (P : (ι → ℤ) → Prop) : ℝ → ℕ → ℝ := fun A k =>
  (ArithmeticFunction.moebius k : ℝ) * (cplG K P k (A / (k : ℝ)) / A ^ Fintype.card ι)

/-- The pointwise limit of the Tannery summands. -/
private noncomputable def cplg (ι : Type*) [Fintype ι] (Lk : ℕ → ℝ) : ℕ → ℝ := fun k =>
  (ArithmeticFunction.moebius k : ℝ) * Lk k / (k : ℝ) ^ Fintype.card ι

/-- The dominating function. -/
private noncomputable def cplbound (ι : Type*) [Fintype ι] : ℕ → ℝ := fun k =>
  (5 : ℝ) ^ Fintype.card ι * (1 / (k : ℝ) ^ Fintype.card ι)

/-! ## The main theorem -/

/-- Primitive integer vectors in a closed, positively scale-invariant set `K` with null frontier
inside the unit ball, satisfying a `Q`-periodic condition `P`: those of Euclidean norm at most `A`,
counted and divided by `A ^ Fintype.card ι`, have a limit as `A → ∞`.

Route. (1) For a fixed residue class `c` modulo `Q`, count
`#{b | b ≡ c [MOD Q] ∧ eNorm b ≤ B ∧ toR b ∈ K}` by a Voronoi/cube sandwich: with `β = √(card ι) * Q`,
the half-open cubes `a + [0,Q)^ι` over the counted points are pairwise disjoint of volume `Q ^ card ι`,
they lie in `K ^ β ∩ closedBall 0 (B + β)`, and their union covers `K ⊖ β ∩ closedBall 0 (B - β)`
(via the nearest point of the coset). Positive scale invariance gives
`K ^ β ∩ closedBall 0 R = R • (K ^ (β/R) ∩ unitBallR ι)`; continuity of measure for the
decreasing family `K ^ δ ∩ unitBallR ι ↓ K ∩ unitBallR ι` (closedness) and the increasing family
`K ⊖ δ ∩ unitBallR ι ↑ interior K ∩ unitBallR ι` together with the null-frontier hypothesis make
both sandwich bounds tend to `volume (K ∩ unitBallR ι)`, so the count over `B ^ card ι` converges to
`volume (K ∩ unitBallR ι) / Q ^ card ι`; also record a uniform bound `count ≤ C * B ^ card ι` for
`B ≥ 1`. (2) Sum (1) over the `Q ^ card ι` classes: by `hP`, `P` depends only on `a mod Q`.
(3) Remove primitivity by Möbius inversion (`1_[IsPrim a] = ∑_{k ∣ gcd a} μ k`): the count is
`∑_{k ≥ 1} μ k * #{b ≠ 0 | eNorm b ≤ A / k ∧ toR b ∈ K ∧ P (k • b)}`, and each summand is a finite
sum of counts from (2) since `P (k • b)` depends only on `k mod Q` and `b mod Q`. Finish by
dominated convergence over `k` with dominating function `C * k ^ (- card ι)`
(`card ι ≥ 2`).-/
theorem cone_periodic_prim_limit {ι : Type*} [Fintype ι] (hι : 2 ≤ Fintype.card ι)
    (K : Set (ι → ℝ)) (hKc : IsClosed K)
    (hK : ∀ (s : ℝ) (t : ι → ℝ), 0 < s → (t ∈ K ↔ s • t ∈ K))
    (hfr : volume (frontier (K ∩ unitBallR ι)) = 0)
    (Q : ℕ) (hQ : 1 ≤ Q) (P : (ι → ℤ) → Prop) (hP : ∀ a b, P a ↔ P (a + (Q : ℤ) • b)) :
    ∃ L : ℝ, Tendsto (fun A : ℝ =>
        ({a : ι → ℤ | IsPrim a ∧ eNorm a ≤ A ∧ toR a ∈ K ∧ P a}.ncard : ℝ) /
          A ^ Fintype.card ι) atTop (nhds L) := by
  classical
  have hsbd : Bornology.IsBounded (K ∩ unitBallR ι) :=
    (cpl_isBounded_unitBallR (ι := ι)).subset Set.inter_subset_right
  have hsmeas : MeasurableSet (K ∩ unitBallR ι) :=
    hKc.measurableSet.inter (cpl_isClosed_unitBallR (ι := ι)).measurableSet
  have hstar := cpl_star_of_cone (ι := ι) K hK
  -- the predicate `b ↦ P (k • b)` is again `Q`-periodic
  have hPk : ∀ (k : ℕ) (a b : ι → ℤ), P ((k : ℤ) • a) ↔ P ((k : ℤ) • (a + (Q : ℤ) • b)) := by
    intro k a b
    have h : (k : ℤ) • (a + (Q : ℤ) • b) = (k : ℤ) • a + (Q : ℤ) • ((k : ℤ) • b) := by
      funext i
      simp only [Pi.smul_apply, Pi.add_apply]
      ring
    rw [h, hP ((k : ℤ) • a) ((k : ℤ) • b)]
  -- the common value of the limits, per `k`
  set Lk : ℕ → ℝ := fun k =>
      (Nat.card {c : ι → Fin Q // P ((k : ℤ) • (fun i => ((c i : ℕ) : ℤ)))} : ℝ) /
        (Q : ℝ) ^ Fintype.card ι * (volume (K ∩ unitBallR ι)).toReal with hLkdef
  -- Step 1: the periodic count, without the restriction `b ≠ 0`
  have keyH : ∀ k : ℕ,
      Tendsto (fun T : ℝ => cplH K P k T / T ^ Fintype.card ι) atTop (nhds (Lk k)) := by
    intro k
    rw [hLkdef]
    refine (Work.HP.DNC.periodic_count_real hsbd hsmeas hfr hstar Q hQ
      (fun b => P ((k : ℤ) • b)) (hPk k)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hset : ({b : ι → ℤ | (fun i => (b i : ℝ) / T) ∈ K ∩ unitBallR ι ∧
          P ((k : ℤ) • b)} : Set (ι → ℤ))
        = {b : ι → ℤ | eNorm b ≤ T ∧ toR b ∈ K ∧ P ((k : ℤ) • b)} := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq]
      rw [cpl_mem_inter_iff K hK hT b]
      tauto
    simp only [cplH]
    rw [hset]
  -- Step 2: remove `b = 0`
  have keyG : ∀ k : ℕ,
      Tendsto (fun T : ℝ => cplG K P k T / T ^ Fintype.card ι) atTop (nhds (Lk k)) := by
    intro k
    refine cpl_tendsto_div_of_sub_le_one (N := Fintype.card ι) (by omega) (keyH k) ?_
    refine Eventually.of_forall (fun T => ?_)
    simp only [cplH, cplG]
    set S : Set (ι → ℤ) := {b | eNorm b ≤ T ∧ toR b ∈ K ∧ P ((k : ℤ) • b)} with hS
    have hSfin : S.Finite := (cpl_finite_eNorm_le T).subset (fun b hb => hb.1)
    have hset : ({b : ι → ℤ | b ≠ 0 ∧ eNorm b ≤ T ∧ toR b ∈ K ∧ P ((k : ℤ) • b)} :
        Set (ι → ℤ)) = S \ {0} := by
      ext b
      simp only [hS, Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      tauto
    rw [hset, abs_sub_comm]
    exact cpl_abs_ncard_sdiff_zero hSfin
  -- Step 3: Tannery's theorem
  have hsum : Summable (cplbound ι) := by
    have h1 : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ Fintype.card ι) :=
      (Real.summable_one_div_nat_pow (p := Fintype.card ι)).mpr (by omega)
    exact h1.mul_left ((5 : ℝ) ^ Fintype.card ι)
  have hconv : ∀ k : ℕ, Tendsto (fun A : ℝ => cplu K P A k) atTop (nhds (cplg ι Lk k)) := by
    intro k
    rcases eq_or_ne k 0 with hk0 | hk0
    · subst hk0
      have h1 : (fun A : ℝ => cplu K P A 0) = fun _ : ℝ => (0 : ℝ) := by
        funext A
        simp only [cplu]
        rw [cpl_moebius_zero, Int.cast_zero, zero_mul]
      have h2 : cplg ι Lk 0 = 0 := by
        simp only [cplg]
        rw [cpl_moebius_zero, Int.cast_zero, zero_mul, zero_div]
      rw [h1, h2]
      exact tendsto_const_nhds
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
      have hsub : Tendsto (fun A : ℝ =>
          cplG K P k (A / (k : ℝ)) / (A / (k : ℝ)) ^ Fintype.card ι) atTop (nhds (Lk k)) :=
        (keyG k).comp (tendsto_id.atTop_div_const hkpos)
      have hdiv : Tendsto (fun A : ℝ =>
          cplG K P k (A / (k : ℝ)) / (A / (k : ℝ)) ^ Fintype.card ι /
            (k : ℝ) ^ Fintype.card ι) atTop (nhds (Lk k / (k : ℝ) ^ Fintype.card ι)) :=
        hsub.div_const _
      have heqc : (fun A : ℝ =>
            cplG K P k (A / (k : ℝ)) / (A / (k : ℝ)) ^ Fintype.card ι /
              (k : ℝ) ^ Fintype.card ι)
          =ᶠ[atTop] (fun A : ℝ => cplG K P k (A / (k : ℝ)) / A ^ Fintype.card ι) := by
        filter_upwards with A
        exact cpl_div_pow_div _ A (k : ℝ) hkne
      have hlim : Tendsto (fun A : ℝ => cplG K P k (A / (k : ℝ)) / A ^ Fintype.card ι)
          atTop (nhds (Lk k / (k : ℝ) ^ Fintype.card ι)) := hdiv.congr' heqc
      have hc : Tendsto (fun _ : ℝ => (ArithmeticFunction.moebius k : ℝ)) atTop
          (nhds (ArithmeticFunction.moebius k : ℝ)) := tendsto_const_nhds
      have hmul := hc.mul hlim
      have hgoal : cplg ι Lk k
          = (ArithmeticFunction.moebius k : ℝ) * (Lk k / (k : ℝ) ^ Fintype.card ι) := by
        simp only [cplg]
        exact mul_div_assoc ((ArithmeticFunction.moebius k : ℝ)) (Lk k)
          ((k : ℝ) ^ Fintype.card ι)
      rw [hgoal]
      simp only [cplu]
      exact hmul
  have hdom : ∀ᶠ A : ℝ in atTop, ∀ k : ℕ, ‖cplu K P A k‖ ≤ cplbound ι k := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with A hA1
    intro k
    rw [Real.norm_eq_abs]
    rcases eq_or_ne k 0 with hk0 | hk0
    · subst hk0
      simp only [cplu, cplbound]
      rw [cpl_moebius_zero, Int.cast_zero, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (by positivity)
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
      have hAnz : A ≠ 0 := ne_of_gt hApos
      have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      have hCn : 0 ≤ cplG K P k (A / (k : ℝ)) := by simp only [cplG]; positivity
      simp only [cplu]
      rw [abs_mul, abs_of_nonneg (div_nonneg hCn (by positivity))]
      by_cases hkA : (k : ℝ) ≤ A
      · have hT1 : 1 ≤ A / (k : ℝ) := (le_div_iff₀ hkpos).mpr (by simpa using hkA)
        have hle : cplG K P k (A / (k : ℝ)) ≤ (5 * (A / (k : ℝ))) ^ Fintype.card ι := by
          simp only [cplG]
          have h1 : ({b : ι → ℤ | b ≠ 0 ∧ eNorm b ≤ A / (k : ℝ) ∧ toR b ∈ K ∧
              P ((k : ℤ) • b)} : Set (ι → ℤ)).ncard ≤
              ({b : ι → ℤ | eNorm b ≤ A / (k : ℝ)} : Set (ι → ℤ)).ncard :=
            Set.ncard_le_ncard (fun b hb => hb.2.1) (cpl_finite_eNorm_le _)
          have h2 : ((({b : ι → ℤ | eNorm b ≤ A / (k : ℝ)} : Set (ι → ℤ)).ncard : ℕ) : ℝ) ≤
              (5 * (A / (k : ℝ))) ^ Fintype.card ι :=
            cpl_ncard_eNorm_le_pow (A / (k : ℝ)) hT1
          exact le_trans (by exact_mod_cast h1) h2
        calc |(ArithmeticFunction.moebius k : ℝ)| *
              (cplG K P k (A / (k : ℝ)) / A ^ Fintype.card ι)
            ≤ 1 * ((5 * (A / (k : ℝ))) ^ Fintype.card ι / A ^ Fintype.card ι) :=
              mul_le_mul hmu (div_le_div_of_nonneg_right hle (le_of_lt (pow_pos hApos _)))
                (by positivity) (by norm_num)
          _ = cplbound ι k := by
              simp only [cplbound]
              rw [one_mul, cpl_five_div A (k : ℝ) hAnz (ne_of_gt hkpos), div_eq_mul_one_div]
      · have hz : cplG K P k (A / (k : ℝ)) = 0 := by
          simp only [cplG]
          have hset0 : ({b : ι → ℤ | b ≠ 0 ∧ eNorm b ≤ A / (k : ℝ) ∧ toR b ∈ K ∧
              P ((k : ℤ) • b)} : Set (ι → ℤ)) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro b ⟨hb0, hbT, -, -⟩
            have h1 := cpl_one_le_eNorm hb0
            have h2 : A / (k : ℝ) < 1 := (div_lt_one hkpos).mpr (not_le.mp hkA)
            linarith
          rw [hset0, Set.ncard_empty]
          norm_num
        rw [hz, zero_div, mul_zero]
        simp only [cplbound]
        exact mul_nonneg (by positivity) (by positivity)
  have hDCT : Tendsto (fun A : ℝ => ∑' k : ℕ, cplu K P A k) atTop
      (nhds (∑' k : ℕ, cplg ι Lk k)) :=
    tendsto_tsum_of_dominated_convergence (f := cplu K P) (g := cplg ι Lk) (bound := cplbound ι)
      hsum hconv hdom
  -- Step 4: identify the series with the Moebius inversion of the primitive count
  have heq : (fun A : ℝ => ∑' k : ℕ, cplu K P A k) =ᶠ[atTop]
      (fun A : ℝ => cplF K P A / A ^ Fintype.card ι) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with A hA
    have hsupp : ∀ k : ℕ, k ∉ Finset.Icc 1 ⌊A⌋₊ → cplu K P A k = 0 := by
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        simp only [cplu]
        rw [cpl_moebius_zero, Int.cast_zero, zero_mul]
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
        have hkgt : ⌊A⌋₊ < k := by
          by_contra hcon
          exact hk (Finset.mem_Icc.mpr ⟨hk1, Nat.le_of_not_lt hcon⟩)
        have hAk : A / (k : ℝ) < 1 := by
          refine (div_lt_one hkpos).mpr ?_
          have h1 : A < (⌊A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one A
          have h2 : (⌊A⌋₊ : ℝ) + 1 ≤ (k : ℝ) := by
            have h3 : ⌊A⌋₊ + 1 ≤ k := hkgt
            exact_mod_cast h3
          linarith
        have hz : cplG K P k (A / (k : ℝ)) = 0 := by
          simp only [cplG]
          have hset0 : ({b : ι → ℤ | b ≠ 0 ∧ eNorm b ≤ A / (k : ℝ) ∧ toR b ∈ K ∧
              P ((k : ℤ) • b)} : Set (ι → ℤ)) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro b ⟨hb0, hbT, -, -⟩
            have h1 := cpl_one_le_eNorm hb0
            linarith
          rw [hset0, Set.ncard_empty]
          norm_num
        simp only [cplu]
        rw [hz, zero_div, mul_zero]
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊A⌋₊) hsupp]
    rw [show (∑ k ∈ Finset.Icc 1 ⌊A⌋₊, cplu K P A k)
        = (∑ k ∈ Finset.Icc 1 ⌊A⌋₊,
            (ArithmeticFunction.moebius k : ℝ) * cplG K P k (A / (k : ℝ))) /
          A ^ Fintype.card ι from by
      simp only [cplu]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k hk => (mul_div_assoc _ _ _).symm)]
    have hm : (∑ k ∈ Finset.Icc 1 ⌊A⌋₊,
        (ArithmeticFunction.moebius k : ℝ) * cplG K P k (A / (k : ℝ))) = cplF K P A := by
      have hmm := Work.HP.DNC.moebius_prim_ncard (ι := ι) K hK P A hA
      simp only [cplF, cplG]
      exact hmm.symm
    rw [hm]
  exact ⟨∑' k : ℕ, cplg ι Lk k, hDCT.congr' heq⟩

end Work.HP.DN
