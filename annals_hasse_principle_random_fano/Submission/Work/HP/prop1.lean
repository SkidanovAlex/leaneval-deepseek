import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.EE_bound
import Submission.Work.HP.diag_bound
import Submission.Work.HP.moment_D
import Submission.Work.HP.moment_mix_loc

/-!
# `Work.HP.prop1` — Proposition 1 of Browning–Le Boudec–Sawin

`prop1` is the Chebyshev/variance consequence: for fixed `φ > 1`, the number of primitive
coefficient vectors `a` of Euclidean norm at most `A` for which the global counting function
`N_V(Aφ)` and the localised counting function `N_V^loc(Aφ)` differ by more than `φ^{2/3}` is
`≪ A^N / φ^{1/3}`, uniformly in `φ`.

The proof is the paper's:

* multiply the second moment `Σ_a (N_V(Aφ) - N_V^loc(Aφ))^2` by `φ^{-4/3}` (Chebyshev),
* expand the square and use the three second-moment estimates (`Dglob`, `Dmix`, `Dloc`, whose
  leading terms `mainTerm` cancel) and the diagonal bound
  `Σ_a (N_V + 2 Δ_V^mix + Δ_V^loc) ≪ A^N · (B/A)` (first moment + `Δ` estimates).

Everything here is the *assembly*; the analytic estimates themselves are separate lemmas in
this directory (`moment_D`, `moment_mix_loc`, `first_moment`, `diag_bound`, `EE_bound`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter
open scoped BigOperators

namespace Work.HP

/-! ## Elementary helpers -/

/-- Every coordinate of a vector is bounded by its Euclidean norm. -/
private lemma p1_abs_coord_le_eNorm {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |(v i : ℝ)| ≤ eNorm v := by
  rw [eNorm, Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i)

/-- The Euclidean norm is nonnegative. -/
private lemma p1_eNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v :=
  Real.sqrt_nonneg _

/-- The Euclidean norm is positive for a nonzero vector. -/
private lemma p1_eNorm_pos {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) : 0 < eNorm v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  rw [eNorm, Real.sqrt_pos]
  refine Finset.sum_pos' (fun j _ => sq_nonneg ((v j : ℝ))) ⟨i, Finset.mem_univ i, ?_⟩
  have hvi : (v i : ℝ) ≠ 0 := by exact_mod_cast hi
  simpa using sq_pos_of_ne_zero hvi

/-- `primSet` is finite: it is contained in a box. -/
private lemma p1_primSet_finite (d n : ℕ) (A : ℝ) (P : (Mon d n → ℤ) → Prop) :
    (primSet d n A P).Finite := by
  refine Set.Finite.subset
    (Finset.finite_toSet (Fintype.piFinset fun _ : Mon d n => Finset.Icc (-⌈A⌉) ⌈A⌉)) ?_
  intro a ha
  simp only [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 : |(a i : ℝ)| ≤ eNorm a := p1_abs_coord_le_eNorm a i
  have h2 : eNorm a ≤ A := ha.2.1
  have h3 := abs_le.mp (le_trans h1 h2)
  constructor
  · have hc : -(⌈A⌉ : ℝ) ≤ (a i : ℝ) := by
      have := Int.le_ceil A
      linarith [h3.1]
    exact_mod_cast hc
  · have hc : (a i : ℝ) ≤ ((⌈A⌉ : ℤ) : ℝ) := by
      have := Int.le_ceil A
      linarith [h3.2]
    exact_mod_cast hc

/-- A primitive vector is nonzero. -/
private lemma p1_ne_zero_of_isPrim {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : IsPrim v) : v ≠ 0 := by
  intro h0
  have h1 : Finset.univ.gcd (0 : ι → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun x _ => rfl)
  rw [h0] at hv
  simp only [IsPrim] at hv
  rw [h1] at hv
  exact one_ne_zero hv.symm

/-- A `finsum` over a finite set is a `Finset` sum. -/
private lemma p1_finsum_eq_sum_of_finite {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ) :
    ∑ᶠ a ∈ s, f a = ∑ a ∈ hs.toFinset, f a := by
  set h2 : (s ∩ Function.support f).Finite := hs.subset Set.inter_subset_left with h2def
  have hsub : h2.toFinset ⊆ hs.toFinset := fun x hx => by
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact hx.1
  rw [finsum_mem_eq_sum f h2]
  exact Finset.sum_subset hsub (fun x hx hx' => by
    rw [Set.Finite.mem_toFinset] at hx
    by_contra h
    exact hx' (by rw [Set.Finite.mem_toFinset]; exact ⟨hx, Function.mem_support.mpr h⟩))

/-- Chebyshev's inequality in the form used below. -/
private lemma p1_ncard_mul_le_sum {α : Type*} {s : Set α} (hs : s.Finite) (f : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ s, c ≤ f a) : (s.ncard : ℝ) * c ≤ ∑ a ∈ hs.toFinset, f a := by
  rw [Set.ncard_eq_toFinset_card s hs]
  have h1 := Finset.card_nsmul_le_sum hs.toFinset f c
    (fun a ha => h a (by rwa [Set.Finite.mem_toFinset] at ha))
  rwa [nsmul_eq_mul] at h1

/-- Monotonicity of a sum of nonnegative terms over a subset. -/
private lemma p1_sum_mono_set {α : Type*} {s t : Set α} (hst : s ⊆ t) (ht : t.Finite) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ (ht.subset hst).toFinset, f a ≤ ∑ a ∈ ht.toFinset, f a := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact hst hx
  · intro x _ _
    exact hf x

/-- `E_{d,n}(B) ≥ 0`: every summand is a reciprocal of a (nonnegative) determinant. -/
private lemma p1_EE_nonneg (d n : ℕ) (B : ℝ) : 0 ≤ EE d n B := by
  simp only [EE]
  refine finsum_nonneg (fun p => ?_)
  refine finsum_nonneg (fun _ => ?_)
  exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

/-- Positivity of the second-moment normalising constant. -/
private lemma p1_iotaDN_nonneg (d n : ℕ) : 0 ≤ iotaDN d n := by
  rw [iotaDN]
  refine div_nonneg ENNReal.toReal_nonneg ?_
  refine mul_nonneg (by norm_num) ?_
  exact tsum_nonneg (fun k => by positivity)

/-- The common main term is nonnegative. -/
private lemma p1_mainTerm_nonneg (d n : ℕ) {A B : ℝ} (hA : 0 ≤ A) : 0 ≤ mainTerm d n A B := by
  rw [mainTerm]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (p1_iotaDN_nonneg d n))
    (pow_nonneg hA _)) (p1_EE_nonneg d n B)

/-- `Δ_V^mix(B) ≥ 0`. -/
private lemma p1_DeltaMix_nonneg (d n : ℕ) {a : Mon d n → ℤ} {B : ℝ} (ha : a ≠ 0) (hB : 1 ≤ B) :
    0 ≤ DeltaMix d n a B := by
  rw [DeltaMix]
  refine mul_nonneg (mul_nonneg (by norm_num) ?_) ?_
  · refine div_nonneg (mul_nonneg (Real.log_nonneg hB) (by positivity)) (p1_eNorm_pos ha).le
  · refine finsum_nonneg (fun x => ?_)
    refine finsum_nonneg (fun _ => ?_)
    exact div_nonneg zero_le_one (p1_eNorm_nonneg _)

/-! ## Algebraic identities for the variance expansion -/

/-- Splitting a sum of a fixed linear combination of four functions. -/
private lemma p1_sum_combine {ι : Type*} (s : Finset ι) (X Y Z W : ι → ℝ) :
    (∑ a ∈ s, (X a - 2 * Y a + Z a + W a))
      = (∑ a ∈ s, X a) - 2 * (∑ a ∈ s, Y a) + (∑ a ∈ s, Z a) + (∑ a ∈ s, W a) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Pointwise expansion of the square `(N_V - N_V^loc)^2`. -/
private lemma p1_variance_pointwise (d n : ℕ) (A B : ℝ) (a : Mon d n → ℤ) :
    (NV d n a B - NVloc d n a B) ^ 2
      = (NV d n a B ^ 2 - NV d n a B) - 2 * (NV d n a B * NVloc d n a B - DeltaMix d n a B)
        + (NVloc d n a B ^ 2 - DeltaLoc d n a B)
        + (NV d n a B - 2 * DeltaMix d n a B + DeltaLoc d n a B) := by
  ring

/-- Pointwise inequality version, where the diagonal term is replaced by the (larger)
`N_V + 2 Δ_V^mix + Δ_V^loc`. -/
private lemma p1_variance_pointwise_le (d n : ℕ) {B : ℝ} {a : Mon d n → ℤ}
    (hΔ : 0 ≤ DeltaMix d n a B) :
    (NV d n a B - NVloc d n a B) ^ 2
      ≤ (NV d n a B ^ 2 - NV d n a B) - 2 * (NV d n a B * NVloc d n a B - DeltaMix d n a B)
        + (NVloc d n a B ^ 2 - DeltaLoc d n a B)
        + (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B) := by
  have h := p1_variance_pointwise d n 0 B a
  linarith

/-- The variance expansion: the second moment of `N_V - N_V^loc` is the combination of the
three second moments plus the diagonal sum. -/
private lemma p1_variance_expansion (d n : ℕ) {A B : ℝ} (hB : 1 ≤ B)
    (hs : (primSet d n A (fun _ => True)).Finite) :
    ∑ a ∈ hs.toFinset, (NV d n a B - NVloc d n a B) ^ 2
      ≤ (Dglob d n A B - 2 * Dmix d n A B + Dloc d n A B)
        + ∑ a ∈ hs.toFinset, (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B) := by
  have hstep : ∑ a ∈ hs.toFinset, (NV d n a B - NVloc d n a B) ^ 2
      ≤ ∑ a ∈ hs.toFinset, ((NV d n a B ^ 2 - NV d n a B)
          - 2 * (NV d n a B * NVloc d n a B - DeltaMix d n a B)
          + (NVloc d n a B ^ 2 - DeltaLoc d n a B)
          + (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B)) := by
    refine Finset.sum_le_sum (fun a ha => ?_)
    have ha' := (Set.Finite.mem_toFinset hs).mp ha
    exact p1_variance_pointwise_le d n (p1_DeltaMix_nonneg d n (p1_ne_zero_of_isPrim ha'.1) hB)
  refine le_trans hstep ?_
  rw [p1_sum_combine]
  simp only [Dglob, Dmix, Dloc]
  rw [← p1_finsum_eq_sum_of_finite hs (fun a => NV d n a B ^ 2 - NV d n a B),
    ← p1_finsum_eq_sum_of_finite hs (fun a => NV d n a B * NVloc d n a B - DeltaMix d n a B),
    ← p1_finsum_eq_sum_of_finite hs (fun a => NVloc d n a B ^ 2 - DeltaLoc d n a B)]

/-! ## Real-variable helpers -/

/-- `φ ^ (2/3) < |g|` implies `φ ^ (4/3) ≤ g ^ 2`. -/
private lemma p1_rpow_lt_sq_abs {φ g : ℝ} (hφ : 0 < φ) (h : φ ^ ((2 : ℝ) / 3) < |g|) :
    φ ^ ((4 : ℝ) / 3) ≤ g ^ 2 := by
  have h1 : (φ ^ ((2 : ℝ) / 3)) ^ 2 < g ^ 2 := by
    rw [sq_lt_sq, abs_of_nonneg (Real.rpow_nonneg hφ.le _)]
    exact h
  have h2 : (φ ^ ((2 : ℝ) / 3)) ^ 2 = φ ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hφ.le]
    congr 1
    norm_num
  rw [h2] at h1
  exact le_of_lt h1

/-- `A ^ (N - 2) * A ^ 2 = A ^ N` for `2 ≤ N`. -/
private lemma p1_pow_sub_two_mul_pow_two {A : ℝ} {N : ℕ} (hN : 2 ≤ N) :
    A ^ (N - 2) * A ^ 2 = A ^ N := by
  rw [← pow_add, Nat.sub_add_cancel hN]

/-- `(A φ) ^ (5/6) ≤ A` when `φ ^ 5 ≤ A`. -/
private lemma p1_rpow_frac_56_le {A φ : ℝ} (hA : 0 < A) (hφ : 0 ≤ φ) (h : φ ^ 5 ≤ A) :
    (A * φ) ^ ((5 : ℝ) / 6) ≤ A := by
  rw [Real.mul_rpow hA.le hφ]
  have h1 : φ ^ ((5 : ℝ) / 6) ≤ A ^ ((1 : ℝ) / 6) := by
    have h2 : φ ^ ((5 : ℝ) / 6) = (φ ^ 5) ^ ((1 : ℝ) / 6) := by
      rw [show (5 : ℝ) / 6 = 5 * ((1 : ℝ) / 6) by norm_num, Real.rpow_mul hφ]
      norm_num
    rw [h2]
    exact Real.rpow_le_rpow (by positivity) h (by norm_num)
  calc A ^ ((5 : ℝ) / 6) * φ ^ ((5 : ℝ) / 6)
      ≤ A ^ ((5 : ℝ) / 6) * A ^ ((1 : ℝ) / 6) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA.le _)
    _ = A ^ ((5 : ℝ) / 6 + (1 : ℝ) / 6) := (Real.rpow_add hA _ _).symm
    _ = A := by rw [show (5 : ℝ) / 6 + (1 : ℝ) / 6 = 1 by norm_num, Real.rpow_one]

/-- `(A φ) ^ (4/5) ≤ A` when `φ ^ 4 ≤ A`. -/
private lemma p1_rpow_frac_45_le {A φ : ℝ} (hA : 0 < A) (hφ : 0 ≤ φ) (h : φ ^ 4 ≤ A) :
    (A * φ) ^ ((4 : ℝ) / 5) ≤ A := by
  rw [Real.mul_rpow hA.le hφ]
  have h1 : φ ^ ((4 : ℝ) / 5) ≤ A ^ ((1 : ℝ) / 5) := by
    have h2 : φ ^ ((4 : ℝ) / 5) = (φ ^ 4) ^ ((1 : ℝ) / 5) := by
      rw [show (4 : ℝ) / 5 = 4 * ((1 : ℝ) / 5) by norm_num, Real.rpow_mul hφ]
      norm_num
    rw [h2]
    exact Real.rpow_le_rpow (by positivity) h (by norm_num)
  calc A ^ ((4 : ℝ) / 5) * φ ^ ((4 : ℝ) / 5)
      ≤ A ^ ((4 : ℝ) / 5) * A ^ ((1 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hA.le _)
    _ = A ^ ((4 : ℝ) / 5 + (1 : ℝ) / 5) := (Real.rpow_add hA _ _).symm
    _ = A := by rw [show (4 : ℝ) / 5 + (1 : ℝ) / 5 = 1 by norm_num, Real.rpow_one]

/-- Triangle inequality for `x - 2y + z`. -/
private lemma p1_abs_sub_two_mul_add_le (x y z : ℝ) : |x - 2 * y + z| ≤ |x| + 2 * |y| + |z| := by
  have h1 : |x - 2 * y + z| ≤ |x - 2 * y| + |z| := abs_add_le _ _
  have h2 : |x - 2 * y| ≤ |x| + |2 * y| := abs_sub _ _
  rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at h2
  linarith

/-- The variance bound for the difference of the three second moments. -/
private lemma p1_var_chain {Dg Dm Dl KG Km r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (h1 : |Dg - M| ≤ KG * M / r)
    (h2 : |Dm - M| ≤ Km * M / r)
    (h3 : |Dl - M| ≤ Km * M / r) :
    Dg - 2 * Dm + Dl ≤ max (KG + 3 * Km) 0 * M / r := by
  have e1 : |Dg - M| * r ≤ KG * M :=
    (le_div_iff₀ hr).mp h1
  have e2 : |Dm - M| * r ≤ Km * M :=
    (le_div_iff₀ hr).mp h2
  have e3 : |Dl - M| * r ≤ Km * M :=
    (le_div_iff₀ hr).mp h3
  have hmid : (|Dg - M| + 2 * |Dm - M|
      + |Dl - M|) * r ≤ (KG + 3 * Km) * M := by
    have h : (|Dg - M| + 2 * |Dm - M|
          + |Dl - M|) * r
        = |Dg - M| * r + 2 * (|Dm - M| * r)
          + |Dl - M| * r := by ring
    rw [h]
    nlinarith [e1, e2, e3]
  have htri : Dg - 2 * Dm + Dl
      ≤ |Dg - M| + 2 * |Dm - M| + |Dl - M| := by
    have h : Dg - 2 * Dm + Dl
        = (Dg - M) - 2 * (Dm - M)
          + (Dl - M) := by ring
    rw [h]
    have h2' : |(Dg - M) - 2 * (Dm - M)
          + (Dl - M)|
        ≤ |Dg - M| + 2 * |Dm - M|
          + |Dl - M| :=
      p1_abs_sub_two_mul_add_le _ _ _
    linarith [le_abs_self ((Dg - M) - 2 * (Dm - M)
      + (Dl - M)), h2']
  have hCc : KG + 3 * Km ≤ max (KG + 3 * Km) 0 := le_max_left _ _
  calc Dg - 2 * Dm + Dl
      ≤ |Dg - M| + 2 * |Dm - M|
        + |Dl - M| := htri
    _ ≤ max (KG + 3 * Km) 0 * M / r := by
        rw [le_div_iff₀ hr]
        calc (|Dg - M| + 2 * |Dm - M|
              + |Dl - M|) * r ≤ (KG + 3 * Km) * M := hmid
          _ ≤ max (KG + 3 * Km) 0 * M :=
              mul_le_mul_of_nonneg_right hCc hM

/-! ## Bounding the main term by `A^{N-2} B^2` -/

/-- `mainTerm = 2 ι A^{N-2} E` is bounded by `(2 |ι| K + 1) A^{N-2} B^2` as soon as
`E ≪ K B^2`. -/
private lemma p1_mainTerm_le_of_EE_le (d n : ℕ) {A B K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (h : EE d n B ≤ K * B ^ 2) :
    mainTerm d n A B ≤ (2 * |iotaDN d n| * K + 1) * A ^ (NN d n - 2) * B ^ 2 := by
  have hA2 : 0 ≤ A ^ (NN d n - 2) := pow_nonneg hA _
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  rw [mainTerm]
  calc 2 * iotaDN d n * A ^ (NN d n - 2) * EE d n B
      ≤ 2 * |iotaDN d n| * A ^ (NN d n - 2) * (K * B ^ 2) := by
        refine mul_le_mul ?_ h (p1_EE_nonneg d n B) ?_
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) hA2
        · exact mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hA2
    _ = (2 * |iotaDN d n| * K) * (A ^ (NN d n - 2) * B ^ 2) := by ring
    _ ≤ (2 * |iotaDN d n| * K + 1) * (A ^ (NN d n - 2) * B ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA2 hB2)
        linarith
    _ = (2 * |iotaDN d n| * K + 1) * A ^ (NN d n - 2) * B ^ 2 := by ring

/-! ## The assembly of `prop1` from the four analytic estimates -/

/-- **Assembly.** `prop1` follows from the three second-moment estimates (`Dglob`, and
`Dmix`/`Dloc` against the common main term), the bound `E_{d,n}(B) ≪ B^2` and the diagonal
bound `Σ_a (N_V + 2 Δ_V^mix + Δ_V^loc) ≪ A^N · B/A`. -/
theorem p1_prop1_of_bounds (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n)
    (hglob : ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      |Dglob d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2))
    (hmix : ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      |Dmix d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) ∧
      |Dloc d n A B - mainTerm d n A B| ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2))
    (hE : ∃ K B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → EE d n B ≤ K * B ^ 2)
    (hD : ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ a ∈ primSet d n A (fun _ => True),
        (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B)) ≤ K * A ^ NN d n * (B / A)) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ : ℝ, 1 < φ → ∀ᶠ A in atTop,
      primCount d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a (A * φ) - NVloc d n a (A * φ)|)
        ≤ K * A ^ NN d n / φ ^ ((1 : ℝ) / 3) := by
  obtain ⟨KG, BG, hG⟩ := hglob
  obtain ⟨Km, Bm, hm⟩ := hmix
  obtain ⟨KE, BE, hE⟩ := hE
  obtain ⟨KD, BD, hKD, hD⟩ := hD
  have hN2 : 2 ≤ NN d n := le_trans (by norm_num) (six_le_NN d n hd hdn)
  -- the constants of the estimate
  set CC : ℝ := max (KG + 3 * Km) 0 with hCC
  set CM : ℝ := 2 * |iotaDN d n| * max KE 0 + 1 with hCM
  set C1 : ℝ := 2 * CC * CM with hC1
  set Bmax : ℝ := max (max BG Bm) (max BE BD) with hBmax
  have hCC0 : 0 ≤ CC := by rw [hCC]; exact le_max_right _ _
  have hCM0 : 0 ≤ 2 * |iotaDN d n| * max KE 0 :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (le_max_right KE 0)
  have hCM1 : 1 ≤ CM := by rw [hCM]; linarith
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  have hBGmax : BG ≤ Bmax := by
    rw [hBmax]; exact le_trans (le_max_left BG Bm) (le_max_left _ _)
  have hBmmax : Bm ≤ Bmax := by
    rw [hBmax]; exact le_trans (le_max_right BG Bm) (le_max_left _ _)
  have hBEmax : BE ≤ Bmax := by
    rw [hBmax]; exact le_trans (le_max_left BE BD) (le_max_right _ _)
  have hBDmax : BD ≤ Bmax := by
    rw [hBmax]; exact le_trans (le_max_right BE BD) (le_max_right _ _)
  refine ⟨max KD 0 + 1, by have := le_max_right KD 0; linarith, ?_⟩
  intro φ hφ
  have hφ0 : 0 < φ := lt_trans zero_lt_one hφ
  have hφ1 : 1 ≤ φ := le_of_lt hφ
  set T0 : ℝ := max ((C1 * φ) ^ 2) (2 * φ) with hT0
  set T : ℝ := max 1 (max (φ ^ 5) (max (Bmax / φ + 1) (Real.exp T0))) with hT
  have hT1 : 1 ≤ T := by rw [hT]; exact le_max_left _ _
  have hT5 : φ ^ 5 ≤ T := by rw [hT]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hTB : Bmax / φ + 1 ≤ T := by
    rw [hT]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hTe : Real.exp T0 ≤ T := by
    rw [hT]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  rw [Filter.eventually_atTop]
  refine ⟨T, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := le_trans hT1 hA
  have hA5 : φ ^ 5 ≤ A := le_trans hT5 hA
  have hAB : Bmax / φ + 1 ≤ A := le_trans hTB hA
  have hAe : Real.exp T0 ≤ A := le_trans hTe hA
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hlogT0 : T0 ≤ Real.log A := by
    have h1 : Real.log (Real.exp T0) ≤ Real.log A := Real.log_le_log (Real.exp_pos T0) hAe
    rwa [Real.log_exp] at h1
  rw [hT0] at hlogT0
  have hlogC : (C1 * φ) ^ 2 ≤ Real.log A := le_trans (le_max_left _ _) hlogT0
  have hlog2 : 2 * φ ≤ Real.log A := le_trans (le_max_right _ _) hlogT0
  have hlog0 : 0 < Real.log A := lt_of_lt_of_le (by linarith) hlog2
  set B : ℝ := A * φ with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith [hA1, hφ1]
  have hBmax_le : Bmax ≤ B := by
    have h1 : Bmax + φ ≤ (Bmax / φ + 1) * φ := by
      rw [add_mul, one_mul, div_mul_cancel₀ Bmax hφ0.ne']
    have h2 : (Bmax / φ + 1) * φ ≤ A * φ := mul_le_mul_of_nonneg_right hAB hφ0.le
    rw [hB]
    linarith
  have hBG : BG ≤ B := le_trans hBGmax hBmax_le
  have hBm : Bm ≤ B := le_trans hBmmax hBmax_le
  have hBE : BE ≤ B := le_trans hBEmax hBmax_le
  have hBD : BD ≤ B := le_trans hBDmax hBmax_le
  have hlogB : φ ≤ Real.log B := by
    rw [hB, Real.log_mul hApos.ne' hφ0.ne']
    have := Real.log_nonneg hφ1
    linarith
  have hlogBpos : 0 < Real.log B := lt_of_lt_of_le hφ0 hlogB
  have hBdiv : B / Real.log B ≤ A := by
    rw [div_le_iff₀ hlogBpos, hB]
    exact mul_le_mul_of_nonneg_left hlogB hApos.le
  have hB56 : B ^ ((5 : ℝ) / 6) ≤ A := by
    rw [hB]; exact p1_rpow_frac_56_le hApos hφ0.le hA5
  have hB45 : B ^ ((4 : ℝ) / 5) ≤ A := by
    rw [hB]
    exact p1_rpow_frac_45_le hApos hφ0.le
      (le_trans (pow_le_pow_right₀ hφ1 (by norm_num : 4 ≤ 5)) hA5)
  have hAleB2 : A ≤ B ^ 2 := by rw [hB]; nlinarith [hA1, hφ1, hApos.le, hφ0.le]
  have hBA : B / A = φ := by rw [hB]; field_simp
  -- the four analytic inputs
  have hGl := hG A B hBG hBdiv hAleB2
  obtain ⟨hm1, hm2⟩ := hm A B hBm hB56 hAleB2
  have hEl := hE B hBE
  have hDl := hD A B hBD hBdiv hAleB2
  -- the variance estimates
  set M : ℝ := mainTerm d n A B with hM
  set r : ℝ := Real.log A ^ ((1 : ℝ) / 2) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hlog0 _
  have hMnn : 0 ≤ M := by rw [hM]; exact p1_mainTerm_nonneg d n hApos.le
  have hG1 : |Dglob d n A B - M| ≤ KG * M / r := by rw [hM, hr]; exact hGl
  have hm1' : |Dmix d n A B - M| ≤ Km * M / r := by rw [hM, hr]; exact hm1
  have hm2' : |Dloc d n A B - M| ≤ Km * M / r := by rw [hM, hr]; exact hm2
  have hvar : Dglob d n A B - 2 * Dmix d n A B + Dloc d n A B ≤ CC * M / r := by
    rw [hCC]
    exact p1_var_chain hrpos hMnn hG1 hm1' hm2'
  have hMle : M ≤ CM * A ^ (NN d n - 2) * B ^ 2 := by
    rw [hM, hCM]
    exact p1_mainTerm_le_of_EE_le d n hApos.le (le_max_right KE 0)
      (le_trans hEl (mul_le_mul_of_nonneg_right (le_max_left KE 0) (sq_nonneg B)))
  -- Chebyshev
  have hSfin : (primSet d n A (fun _ => True)).Finite := p1_primSet_finite d n A _
  have hPfin :
      (primSet d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a B - NVloc d n a B|)).Finite :=
    p1_primSet_finite d n A _
  have hcheb : primCount d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a B - NVloc d n a B|)
      * φ ^ ((4 : ℝ) / 3)
      ≤ ∑ a ∈ hSfin.toFinset, (NV d n a B - NVloc d n a B) ^ 2 := by
    have h1 : primCount d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a B - NVloc d n a B|)
          * φ ^ ((4 : ℝ) / 3)
        ≤ ∑ a ∈ hPfin.toFinset, (NV d n a B - NVloc d n a B) ^ 2 :=
      p1_ncard_mul_le_sum hPfin _ _ (fun a ha => p1_rpow_lt_sq_abs hφ0 ha.2.2)
    refine le_trans h1 (p1_sum_mono_set ?_ hSfin _ (fun a => sq_nonneg _))
    exact fun a ha => ⟨ha.1, ha.2.1, trivial⟩
  have hdiag : ∑ a ∈ hSfin.toFinset, (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B)
      ≤ KD * A ^ NN d n * φ := by
    rw [← p1_finsum_eq_sum_of_finite hSfin
      (fun a => NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B)]
    rw [← hBA]
    exact hDl
  -- the key inequality
  have hkey : ∑ a ∈ hSfin.toFinset, (NV d n a B - NVloc d n a B) ^ 2
      ≤ A ^ NN d n * φ * (1 / 2 + KD) := by
    have hr_sqrt : r = Real.sqrt (Real.log A) := by rw [hr, Real.sqrt_eq_rpow]
    have hsqrtC : C1 * φ ≤ r := by
      rw [hr_sqrt]
      exact (Real.le_sqrt (by rw [hC1]; positivity) hlog0.le).mpr hlogC
    have hφr : CC * CM * φ / r ≤ 1 / 2 := by
      rw [div_le_iff₀ hrpos]
      have h := hsqrtC
      rw [hC1] at h
      nlinarith [h]
    have hpow : CM * A ^ (NN d n - 2) * B ^ 2 = CM * (A ^ NN d n * φ ^ 2) := by
      rw [hB, mul_pow]
      have h1 : CM * A ^ (NN d n - 2) * (A ^ 2 * φ ^ 2)
          = CM * (A ^ (NN d n - 2) * A ^ 2) * φ ^ 2 := by ring
      rw [h1, p1_pow_sub_two_mul_pow_two hN2]
      ring
    have h1 : CC * M / r ≤ CC * (CM * A ^ (NN d n - 2) * B ^ 2) / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMle hCC0) hrpos.le
    have h2 : CC * (CM * A ^ (NN d n - 2) * B ^ 2) / r
        = A ^ NN d n * φ * (CC * CM * φ / r) := by
      rw [hpow]
      field_simp
    have h3 : A ^ NN d n * φ * (CC * CM * φ / r) ≤ A ^ NN d n * φ * (1 / 2) :=
      mul_le_mul_of_nonneg_left hφr (by positivity)
    refine le_trans (p1_variance_expansion d n hB1 hSfin) ?_
    calc (Dglob d n A B - 2 * Dmix d n A B + Dloc d n A B)
          + ∑ a ∈ hSfin.toFinset, (NV d n a B + 2 * DeltaMix d n a B + DeltaLoc d n a B)
        ≤ CC * M / r + KD * A ^ NN d n * φ := add_le_add hvar hdiag
      _ ≤ CC * (CM * A ^ (NN d n - 2) * B ^ 2) / r + KD * A ^ NN d n * φ := by
          linarith [h1]
      _ = A ^ NN d n * φ * (CC * CM * φ / r) + KD * A ^ NN d n * φ := by rw [h2]
      _ ≤ A ^ NN d n * φ * (1 / 2) + KD * A ^ NN d n * φ := by linarith [h3]
      _ = A ^ NN d n * φ * (1 / 2 + KD) := by ring
  -- Chebyshev's inequality, finished
  have hfinal : primCount d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a B - NVloc d n a B|)
      ≤ (max KD 0 + 1) * A ^ NN d n / φ ^ ((1 : ℝ) / 3) := by
    have hφ43 : 0 < φ ^ ((4 : ℝ) / 3) := Real.rpow_pos_of_pos hφ0 _
    have hφ13 : 0 < φ ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hφ0 _
    have hdiv : φ / φ ^ ((4 : ℝ) / 3) = 1 / φ ^ ((1 : ℝ) / 3) := by
      rw [div_eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos hφ0 _))
        (ne_of_gt (Real.rpow_pos_of_pos hφ0 _)), one_mul]
      nth_rewrite 1 [← Real.rpow_one φ]
      rw [← Real.rpow_add hφ0]
      norm_num
    have hstep : primCount d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a B - NVloc d n a B|)
        ≤ A ^ NN d n * φ * (1 / 2 + KD) / φ ^ ((4 : ℝ) / 3) := by
      rw [le_div_iff₀ hφ43]
      exact le_trans hcheb hkey
    calc primCount d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a B - NVloc d n a B|)
        ≤ A ^ NN d n * φ * (1 / 2 + KD) / φ ^ ((4 : ℝ) / 3) := hstep
      _ = A ^ NN d n * (1 / 2 + KD) * (φ / φ ^ ((4 : ℝ) / 3)) := by ring
      _ = A ^ NN d n * (1 / 2 + KD) * (1 / φ ^ ((1 : ℝ) / 3)) := by rw [hdiv]
      _ ≤ (max KD 0 + 1) * A ^ NN d n / φ ^ ((1 : ℝ) / 3) := by
          rw [mul_one_div]
          refine div_le_div_of_nonneg_right ?_ hφ13.le
          have h4 : A ^ NN d n * (1 / 2 + KD) ≤ A ^ NN d n * (max KD 0 + 1) :=
            mul_le_mul_of_nonneg_left (by have := le_max_left KD 0; linarith)
              (pow_nonneg hApos.le _)
          calc A ^ NN d n * (1 / 2 + KD) ≤ A ^ NN d n * (max KD 0 + 1) := h4
            _ = (max KD 0 + 1) * A ^ NN d n := by ring
  simpa only [hB] using hfinal

/-! ## Proposition 1 -/

/-- N10. Proposition 1 (via the variance bound, the first moment, and Chebyshev), for constant `φ`. -/
theorem prop1 (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    ∃ K : ℝ, 0 < K ∧ ∀ φ : ℝ, 1 < φ → ∀ᶠ A in atTop,
      primCount d n A (fun a => φ ^ ((2 : ℝ) / 3) < |NV d n a (A * φ) - NVloc d n a (A * φ)|)
        ≤ K * A ^ NN d n / φ ^ ((1 : ℝ) / 3) := by
  obtain ⟨K, B₀, _, hE⟩ := EE_bound d n hd hdn h22 h33
  exact p1_prop1_of_bounds d n hd hdn (moment_D d n hd hdn h22 h33)
    (moment_mix_loc d n hd hdn h22) ⟨K, B₀, hE⟩ (diag_bound d n hd hdn)

end Work.HP
