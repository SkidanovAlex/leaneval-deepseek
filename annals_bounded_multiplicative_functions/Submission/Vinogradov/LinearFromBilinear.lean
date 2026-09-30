/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.BilinearReduction
import Submission.Commons.Combinatorics.Dyadic.whitney_decomposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ Lemma 2.2: the bilinear reduction

This module proves **Lemma 2.2** of Guo–Li–Yung–Zorin-Kranich,
*[A short proof of ℓ² decoupling for the moment curve](https://arxiv.org/abs/1912.09798)*:
the linear decoupling inequality `DecLin k (2^N) C` at dyadic scale `2^{-N}` follows from
the symmetric bilinear decoupling inequalities `BilinDec k (2^{N-n}) (C n)` at all the
intermediate dyadic scales `2 ≤ n ≤ N`.

The proof is the one of the paper's §2: expand `(Σ_J f_J)²` as a double sum, split the
pairs `(I,I')` of pieces according to the Whitney decomposition of the square (the
combinatorial content being `Commons.Combinatorics.Dyadic.whitney_decomposition`), bound the
diagonal band by AM–GM, bound every Whitney block by the bilinear decoupling inequality
rescaled to the coarse interval, and sum using the bounded multiplicity.

Everything is stated with `ℝ≥0∞`-valued `L^p` norms `lpNorm`/`l2Norm` of
`BilinearReduction.lean`; see the header of that module for why.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. Generic extended-`L^p` lemmas -/

/-- The exponent `p_k / 2 = k(k+1)/2` of the bilinear estimates, as a real number. -/
def rExp (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1) / 2

lemma pE_div_two_toReal (k : ℕ) : (pE k / 2).toReal = rExp k := by
  rw [ENNReal.toReal_div, pE_toReal, rExp]
  norm_num

lemma two_le_pE {k : ℕ} (hk : 1 ≤ k) : 2 ≤ pE k := by
  rw [pE]
  have : 2 ≤ k * (k + 1) := by nlinarith
  exact_mod_cast this

lemma one_le_pE_div_two {k : ℕ} (hk : 1 ≤ k) : 1 ≤ pE k / 2 := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  simpa using two_le_pE hk

lemma pE_div_two_ne_zero {k : ℕ} (hk : 1 ≤ k) : pE k / 2 ≠ 0 :=
  (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1) (one_le_pE_div_two hk)).ne'

lemma pE_div_two_ne_top (k : ℕ) : pE k / 2 ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.coe_ne_top : (((k * (k + 1) : ℕ) : ℝ≥0∞)) ≠ ⊤) ?_
  rw [pE, ENNReal.div_eq_inv_mul]
  calc 2⁻¹ * ((k * (k + 1) : ℕ) : ℝ≥0∞) ≤ 1 * ((k * (k + 1) : ℕ) : ℝ≥0∞) :=
        mul_le_mul' (by norm_num) le_rfl
    _ = _ := one_mul _

lemma rExp_pos {k : ℕ} (hk : 1 ≤ k) : 0 < rExp k := by
  have h := (ENNReal.toReal_le_toReal (by norm_num : (1:ℝ≥0∞) ≠ ∞)
    (pE_div_two_ne_top k)).mpr (one_le_pE_div_two hk)
  rw [pE_div_two_toReal] at h
  simp only [ENNReal.toReal_one] at h
  linarith

/-- The square identity: the `L^{p/2}` norm of the pointwise square is the square of the
`L^p` norm. -/
theorem eLpNorm_mul_self (k : ℕ) {p : ℝ≥0∞} {g : E k → ℂ} (hg : AEStronglyMeasurable g volume) :
    lpNorm k (p / 2) (fun x => g x * g x) = (lpNorm k p g) ^ (2:ℝ) := by
  have h2 : (p / 2) * ENNReal.ofReal 2 = p := by
    rw [ENNReal.ofReal_ofNat]
    exact ENNReal.div_mul_cancel (by norm_num) (ENNReal.coe_ne_top)
  have hcongr : eLpNorm (fun x => g x * g x) (p / 2) volume
      = eLpNorm (fun x => ‖g x‖ ^ (2:ℝ)) (p / 2) volume := by
    apply eLpNorm_congr_enorm_ae (f := fun x => g x * g x) (hg.mul hg)
      (hg.norm.aemeasurable.pow_const (2:ℝ)).aestronglyMeasurable
    filter_upwards with x
    simp only [enorm_mul, Real.rpow_two, enorm_norm, pow_two]
  rw [lpNorm, hcongr, eLpNorm_norm_rpow g hg (q := 2) (by norm_num), h2, lpNorm]

theorem eLpNorm_eq_sqrt_mul_self (k : ℕ) {p : ℝ≥0∞} {g : E k → ℂ} (hg : AEStronglyMeasurable g volume) :
    lpNorm k p g = (lpNorm k (p / 2) (fun x => g x * g x)) ^ (1/2:ℝ) := by
  rw [eLpNorm_mul_self k hg, ← ENNReal.rpow_mul]
  norm_num

/-- The Hölder triple `(p, p, p/2)`. -/
theorem holderTriple_half (p : ℝ≥0∞) : ENNReal.HolderTriple p p (p / 2) where
  inv_add_inv_eq_inv := by
    rw [ENNReal.inv_div (by simp) (by norm_num), div_eq_mul_inv]
    ring

/-- Hölder's inequality in the form needed for the diagonal band. -/
theorem eLpNorm_mul_le_lp (k : ℕ) {p : ℝ≥0∞} {g h : E k → ℂ}
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    lpNorm k (p / 2) (fun x => g x * h x) ≤ lpNorm k p g * lpNorm k p h := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := (volume : Measure (E k)))
    (p := p) (q := p) (r := p/2) (fun a b => a * b) 1 continuous_mul hg hh
    (by filter_upwards with x; simp) (hpqr := holderTriple_half p)
  simpa [lpNorm, one_mul] using h

/-- The `L^{p_k/2}` norm of a product expressed as an explicit `ℝ≥0∞` integral; this is the
quantity appearing in Definition 2.1 (`BilinDec`). -/
theorem lpNorm_mul_eq_rpow_lintegral (k : ℕ) (hk : 1 ≤ k) {g h : E k → ℂ}
    (hg : AEStronglyMeasurable g volume) (hh : AEStronglyMeasurable h volume) :
    lpNorm k (pE k / 2) (fun x => g x * h x)
      = (∫⁻ x, ((‖g x‖₊ : ℝ≥0∞) ^ rExp k) * ((‖h x‖₊ : ℝ≥0∞) ^ rExp k))
          ^ (1 / rExp k) := by
  rw [lpNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal (pE_div_two_ne_zero hk)
    (pE_div_two_ne_top k)
    (f := fun x => g x * h x) (hg.mul hh), pE_div_two_toReal]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [enorm_mul, enorm_eq_nnnorm (g x), enorm_eq_nnnorm (h x),
    ENNReal.mul_rpow_of_nonneg _ _ (rExp_pos hk).le]

/-! ## 2. The `ℓ²`-type quantities over finite sets -/

/-- The sum of squares over a finite set. -/
noncomputable def sqSum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i ∈ s, a i ^ (2 : ℝ)

/-- The `ℓ²` quantity attached to a finite set, `(Σ_{i ∈ s} a_i²)^{1/2}`. -/
noncomputable def l2Of {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) : ℝ≥0∞ :=
  (sqSum s a) ^ (1/2 : ℝ)

lemma l2Of_sq {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    (l2Of s a) ^ (2:ℝ) = sqSum s a := by
  rw [l2Of, ← ENNReal.rpow_mul]
  norm_num

lemma l2Of_mono {ι : Type*} {s t : Finset ι} (hst : s ⊆ t) (a : ι → ℝ≥0∞) :
    l2Of s a ≤ l2Of t a := by
  rw [l2Of, l2Of, ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 1/2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => by positivity)

/-! ## 3. Combinatorial and geometric helpers for the Whitney decomposition -/

/-- Truncation is `1`-Lipschitz on naturals: if `|i - j| ≤ 1` then so is `|i/2^m - j/2^m|`. -/
lemma abs_div_pow_two_sub_le_one {i j m : ℕ} (h : |((i:ℤ)) - ((j:ℤ))| ≤ 1) :
    |((i / 2^m : ℕ) : ℤ) - ((j / 2^m : ℕ) : ℤ)| ≤ 1 := by
  have h1 : i ≤ j + 1 := by
    have : ((i:ℤ)) ≤ ((j:ℤ)) + 1 := by
      have := (abs_le.mp h).2; linarith
    exact_mod_cast this
  have h2 : j ≤ i + 1 := by
    have : ((j:ℤ)) ≤ ((i:ℤ)) + 1 := by
      have := (abs_le.mp h).1; linarith
    exact_mod_cast this
  have hdiv : ∀ a : ℕ, (a + 1) / 2^m ≤ a / 2^m + 1 := by
    intro a
    calc (a + 1) / 2^m ≤ (a + 2^m) / 2^m := Nat.div_le_div_right (by
          have : 1 ≤ 2^m := Nat.one_le_two_pow
          omega)
      _ = a / 2^m + 1 := Nat.add_div_right a (pow_pos (by norm_num : (0:ℕ) < 2) m)
  rw [abs_le]
  rcases le_total i j with hle | hle
  · have hA : ((i / 2^m : ℕ) : ℤ) ≤ ((j / 2^m : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_le_div_right hle
    have hB : ((j / 2^m : ℕ) : ℤ) ≤ ((i / 2^m : ℕ) : ℤ) + 1 := by
      exact_mod_cast le_trans (Nat.div_le_div_right h2) (hdiv i)
    constructor <;> omega
  · have hA : ((j / 2^m : ℕ) : ℤ) ≤ ((i / 2^m : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_le_div_right hle
    have hB : ((i / 2^m : ℕ) : ℤ) ≤ ((j / 2^m : ℕ) : ℤ) + 1 := by
      exact_mod_cast le_trans (Nat.div_le_div_right h1) (hdiv j)
    constructor <;> omega

/-- The index of a sub-piece of a dyadic block stays in range. -/
lemma blockIdx_lt {N n q M j : ℕ} (hn : n ≤ N) (hM : M = 2 ^ (N - n)) (hq : q < 2 ^ n)
    (hj : j < M) : q * M + j < 2 ^ N := by
  subst hM
  have h1 : q + 1 ≤ 2 ^ n := hq
  have h2 : (q + 1) * 2 ^ (N - n) ≤ 2 ^ n * 2 ^ (N - n) :=
    Nat.mul_le_mul_right _ h1
  rw [← pow_add, Nat.add_sub_cancel' hn] at h2
  calc q * 2 ^ (N - n) + j < q * 2 ^ (N - n) + 2 ^ (N - n) := by omega
    _ = (q + 1) * 2 ^ (N - n) := by ring
    _ ≤ 2 ^ N := h2

/-- Equality of plates is determined by the width and the centre. -/
lemma plate_congr' {k : ℕ} {δ δ' : ℝ} {c c' : ℝ} (h1 : δ = δ') (h2 : c = c') :
    plate k δ c = plate k δ' c' := by rw [h1, h2]

/-- The plate of a sub-piece of a dyadic block, in the coordinates of the rescaled interval
`[(q/2^n), (q+1)/2^n]`. -/
lemma piecePlate_block (k N n q M : ℕ) (hn : n ≤ N) (hM : M = 2 ^ (N - n)) (hq : q < 2 ^ n)
    (j : Fin M) :
    piecePlate k (2 ^ N) ⟨q * M + (j : ℕ), blockIdx_lt hn hM hq j.2⟩
      = plate k ((1 / (2:ℝ) ^ n) / (2 * (M : ℝ)))
          ((q : ℝ) * (1 / (2:ℝ) ^ n)
            + ((((j : ℕ) : ℝ) + 1 / 2) * (1 / (2:ℝ) ^ n)) / (M : ℝ)) := by
  have h2N : ((2 ^ N : ℕ) : ℝ) = (2:ℝ) ^ N := by push_cast; ring
  have hMM : (M : ℝ) = (2:ℝ) ^ (N - n) := by rw [hM]; push_cast; ring
  have hMN : (2:ℝ) ^ N = (2:ℝ) ^ n * (2:ℝ) ^ (N - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hn]
  rw [piecePlate, pieceCenter]
  apply plate_congr'
  · rw [h2N, hMM, hMN]; field_simp
  · rw [h2N, hMM, hMN]
    have hqM : ((q * M + (j:ℕ) : ℕ) : ℝ) = (q:ℝ) * (2:ℝ)^(N-n) + (j:ℝ) := by
      push_cast [hMM]; ring
    rw [hqM]
    field_simp
    ring

/-! ## 4. The block structure of the dyadic pieces -/

/-- The pair set of the square `[0, 2^N)²`. -/
def pairSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (2 ^ N)).product (Finset.range (2 ^ N))

/-- The block of `2^{N-n}`-th pieces of scale `2^{-N}` whose level-`n` index is `q`. -/
def blk (N n q : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ N)).filter (fun i => i / 2 ^ (N - n) = q)

lemma mem_blk {N n q i : ℕ} : i ∈ blk N n q ↔ i < 2 ^ N ∧ i / 2 ^ (N - n) = q := by
  simp only [blk, Finset.mem_filter, Finset.mem_range]

lemma mem_pairSet {N : ℕ} {q : ℕ × ℕ} : q ∈ pairSet N ↔ q.1 < 2 ^ N ∧ q.2 < 2 ^ N := by
  rw [pairSet, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Finset.mem_range]

lemma blk_le_pow {N n q : ℕ} (hn : n ≤ N) (hq : q < 2 ^ n) :
    (q + 1) * 2 ^ (N - n) ≤ 2 ^ N := by
  have h1 : q + 1 ≤ 2 ^ n := hq
  calc (q + 1) * 2 ^ (N - n) ≤ 2 ^ n * 2 ^ (N - n) := Nat.mul_le_mul_right _ h1
    _ = 2 ^ N := by rw [← pow_add, Nat.add_sub_cancel' hn]

/-- A dyadic block is an interval of consecutive pieces. -/
lemma blk_eq_Ico {N n q : ℕ} (hn : n ≤ N) (hq : q < 2 ^ n) :
    blk N n q = Finset.Ico (q * 2 ^ (N - n)) ((q + 1) * 2 ^ (N - n)) := by
  ext i
  rw [mem_blk, Finset.mem_Ico]
  have hM : 0 < 2 ^ (N - n) := by positivity
  have hMN := blk_le_pow hn hq
  constructor
  · rintro ⟨hi, hdiv⟩
    have h := Nat.div_add_mod i (2 ^ (N - n))
    rw [hdiv, mul_comm] at h
    constructor
    · exact Nat.le.intro h
    · rw [Nat.succ_mul]
      calc i = q * 2 ^ (N - n) + i % 2 ^ (N - n) := h.symm
        _ < q * 2 ^ (N - n) + 2 ^ (N - n) := Nat.add_lt_add_left (Nat.mod_lt i hM) _
  · rintro ⟨h1, h2⟩
    exact ⟨lt_of_lt_of_le h2 hMN, Nat.div_eq_of_lt_le h1 h2⟩

/-- Reindexing a block sum by `Fin (2^{N-n})`. -/
lemma sum_blk_eq {N n q : ℕ} (hn : n ≤ N) (hq : q < 2 ^ n) (f : ℕ → ℂ) :
    ∑ i ∈ blk N n q, f i = ∑ j : Fin (2 ^ (N - n)), f (q * 2 ^ (N - n) + j) := by
  rw [blk_eq_Ico hn hq, Finset.sum_Ico_eq_sum_range]
  have hsub : (q + 1) * 2 ^ (N - n) - q * 2 ^ (N - n) = 2 ^ (N - n) := by
    rw [Nat.succ_mul]; exact Nat.add_sub_cancel_left _ _
  rw [hsub, ← Fin.sum_univ_eq_sum_range]

/-- Reindexing a block sum of extended nonnegative reals by `Fin (2^{N-n})`. -/
lemma sum_blk_eq' {N n q : ℕ} (hn : n ≤ N) (hq : q < 2 ^ n) (f : ℕ → ℝ≥0∞) :
    ∑ i ∈ blk N n q, f i = ∑ j : Fin (2 ^ (N - n)), f (q * 2 ^ (N - n) + j) := by
  rw [blk_eq_Ico hn hq, Finset.sum_Ico_eq_sum_range]
  have hsub : (q + 1) * 2 ^ (N - n) - q * 2 ^ (N - n) = 2 ^ (N - n) := by
    rw [Nat.succ_mul]; exact Nat.add_sub_cancel_left _ _
  rw [hsub, ← Fin.sum_univ_eq_sum_range]

/-- The multiplicity clause of the Whitney decomposition, in the form used here. -/
lemma whitney_multiplicity {N : ℕ} {W : Finset (ℕ × ℕ × ℕ)}
    (hW3 : ∀ n, 2 ≤ n → n ≤ N → ∀ i, i < 2 ^ n →
      (W.filter (fun p => p.1 = n ∧ (p.2.1 = i ∨ p.2.2 = i))).card ≤ 8)
    {n q : ℕ} (hn2 : 2 ≤ n) (hnN : n ≤ N) (hq : q < 2 ^ n) :
    (W.filter (fun p => p.1 = n ∧ p.2.1 = q)).card ≤ 8 := by
  have h := hW3 n hn2 hnN q hq
  refine le_trans (Finset.card_le_card ?_) h
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, ⟨hp.2.1, Or.inl hp.2.2⟩⟩

lemma whitney_multiplicity' {N : ℕ} {W : Finset (ℕ × ℕ × ℕ)}
    (hW3 : ∀ n, 2 ≤ n → n ≤ N → ∀ i, i < 2 ^ n →
      (W.filter (fun p => p.1 = n ∧ (p.2.1 = i ∨ p.2.2 = i))).card ≤ 8)
    {n q : ℕ} (hn2 : 2 ≤ n) (hnN : n ≤ N) (hq : q < 2 ^ n) :
    (W.filter (fun p => p.1 = n ∧ p.2.2 = q)).card ≤ 8 := by
  have h := hW3 n hn2 hnN q hq
  refine le_trans (Finset.card_le_card ?_) h
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, ⟨hp.2.1, Or.inr hp.2.2⟩⟩


/-! ## 5. The bilinear reduction (GLYZ Lemma 2.2) -/

/-- `x * y ≤ x² + y²` in `ℝ≥0∞`. -/
lemma mul_le_sq_add_sq (x y : ℝ≥0∞) : x * y ≤ x ^ (2:ℝ) + y ^ (2:ℝ) := by
  rcases le_total x y with h | h
  · calc x * y ≤ y * y := mul_le_mul' h le_rfl
      _ = y ^ (2:ℝ) := by rw [ENNReal.rpow_two, sq]
      _ ≤ x ^ (2:ℝ) + y ^ (2:ℝ) := by rw [add_comm]; exact le_self_add
  · calc x * y ≤ x * x := mul_le_mul' le_rfl h
      _ = x ^ (2:ℝ) := by rw [ENNReal.rpow_two, sq]
      _ ≤ x ^ (2:ℝ) + y ^ (2:ℝ) := le_self_add

/-- A sum of an indicator times a constant is bounded by the multiplicity times the
constant. -/
lemma sum_ite_const_le {s : Finset ℕ} {p : ℕ → Prop} [DecidablePred p] {m : ℕ}
    (h : (s.filter p).card ≤ m) (c : ℝ≥0∞) :
    ∑ j ∈ s, (if p j then c else 0) ≤ m * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul' (by exact_mod_cast h) le_rfl

/-- Reindexing the square by two blocks. -/
lemma sum_pair_filter {N k : ℕ} {s t : Finset ℕ} (hs : s ⊆ Finset.range (2 ^ N))
    (ht : t ⊆ Finset.range (2 ^ N)) (g : ℕ → E k → ℂ) (x : E k) :
    ∑ q ∈ pairSet N, (if q.1 ∈ s ∧ q.2 ∈ t then g q.1 x * g q.2 x else 0)
      = (∑ i ∈ s, g i x) * (∑ j ∈ t, g j x) := by
  have hfilt : (pairSet N).filter (fun q => q.1 ∈ s ∧ q.2 ∈ t) = s.product t := by
    ext q
    rw [Finset.mem_filter, mem_pairSet, Finset.product_eq_sprod, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h3, h4⟩
    · rintro ⟨h3, h4⟩
      exact ⟨⟨Finset.mem_range.mp (hs h3), Finset.mem_range.mp (ht h4)⟩, h3, h4⟩
  rw [← Finset.sum_filter, hfilt]
  simp only [Finset.product_eq_sprod, Finset.sum_product, ← Finset.sum_mul_sum]

/-- The indices within distance `1` of a fixed index form a set of at most three
elements. -/
lemma card_filter_abs_sub_le_one (N i : ℕ) :
    ((Finset.range (2 ^ N) : Finset ℕ).filter
      (fun j : ℕ => |((i:ℤ)) - ((j:ℤ))| ≤ 1)).card ≤ 3 := by
  have hband : (Finset.range (2 ^ N) : Finset ℕ).filter
      (fun j : ℕ => |((i:ℤ)) - ((j:ℤ))| ≤ 1) ⊆ ({i - 1, i, i + 1} : Finset ℕ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨-, hj⟩ := hj
    have h1 : (j:ℤ) ≤ (i:ℤ) + 1 := by have := (abs_le.mp hj).1; linarith
    have h2 : (i:ℤ) ≤ (j:ℤ) + 1 := by have := (abs_le.mp hj).2; linarith
    have h1' : j ≤ i + 1 := by exact_mod_cast h1
    have h2' : i ≤ j + 1 := by exact_mod_cast h2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact le_trans (Finset.card_le_card hband) Finset.card_le_three

/-- The diagonal band estimate. -/
lemma diagonal_bound {N : ℕ} (a : ℕ → ℝ≥0∞) :
    ∑ q ∈ pairSet N, (if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then a q.1 * a q.2 else 0)
      ≤ 6 * sqSum (Finset.range (2 ^ N)) a := by
  have hsymm : ∀ i j : ℕ, |((i:ℤ)) - ((j:ℤ))| ≤ 1 ↔ |((j:ℤ)) - ((i:ℤ))| ≤ 1 := by
    intro i j; rw [abs_sub_comm]
  simp only [pairSet, Finset.product_eq_sprod, Finset.sum_product]
  calc ∑ i ∈ Finset.range (2 ^ N), ∑ j ∈ Finset.range (2 ^ N),
          (if |((i:ℤ)) - ((j:ℤ))| ≤ 1 then a i * a j else 0)
      ≤ ∑ i ∈ Finset.range (2 ^ N), ∑ j ∈ Finset.range (2 ^ N),
          ((if |((i:ℤ)) - ((j:ℤ))| ≤ 1 then a i ^ (2:ℝ) else 0)
            + (if |((j:ℤ)) - ((i:ℤ))| ≤ 1 then a j ^ (2:ℝ) else 0)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        by_cases h : |((i:ℤ)) - ((j:ℤ))| ≤ 1
        · rw [if_pos h, if_pos h, if_pos ((hsymm i j).mp h)]
          exact mul_le_sq_add_sq (a i) (a j)
        · rw [if_neg h, if_neg h, if_neg (fun hc => h ((hsymm i j).mpr hc)), add_zero]
    _ = (∑ i ∈ Finset.range (2 ^ N), ∑ j ∈ Finset.range (2 ^ N),
            (if |((i:ℤ)) - ((j:ℤ))| ≤ 1 then a i ^ (2:ℝ) else 0))
          + (∑ i ∈ Finset.range (2 ^ N), ∑ j ∈ Finset.range (2 ^ N),
            (if |((j:ℤ)) - ((i:ℤ))| ≤ 1 then a j ^ (2:ℝ) else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ 3 * sqSum (Finset.range (2 ^ N)) a + 3 * sqSum (Finset.range (2 ^ N)) a := by
        refine add_le_add ?_ ?_
        · calc ∑ i ∈ Finset.range (2 ^ N), ∑ j ∈ Finset.range (2 ^ N),
                (if |((i:ℤ)) - ((j:ℤ))| ≤ 1 then a i ^ (2:ℝ) else 0)
              ≤ ∑ i ∈ Finset.range (2 ^ N), 3 * a i ^ (2:ℝ) :=
                Finset.sum_le_sum fun i _ =>
                  sum_ite_const_le (card_filter_abs_sub_le_one N i) _
            _ = 3 * sqSum (Finset.range (2 ^ N)) a := by
                rw [sqSum, Finset.mul_sum]
        · rw [Finset.sum_comm]
          calc ∑ j ∈ Finset.range (2 ^ N), ∑ i ∈ Finset.range (2 ^ N),
                (if |((j:ℤ)) - ((i:ℤ))| ≤ 1 then a j ^ (2:ℝ) else 0)
              ≤ ∑ j ∈ Finset.range (2 ^ N), 3 * a j ^ (2:ℝ) :=
                Finset.sum_le_sum fun j _ =>
                  sum_ite_const_le (card_filter_abs_sub_le_one N j) _
            _ = 3 * sqSum (Finset.range (2 ^ N)) a := by
                rw [sqSum, Finset.mul_sum]
    _ = 6 * sqSum (Finset.range (2 ^ N)) a := by ring

/-- The `ℓ²` quantity of a block is the `ℓ²` norm of the corresponding sub-family. -/
lemma l2Norm_sub_eq {N : ℕ} (a : ℕ → ℝ≥0∞) {n q : ℕ} (hn : n ≤ N) (hq : q < 2 ^ n) :
    l2Norm (fun j : Fin (2 ^ (N - n)) => a (q * 2 ^ (N - n) + j)) = l2Of (blk N n q) a := by
  rw [l2Norm, l2Of, sqSum]
  congr 1
  exact (sum_blk_eq' (N := N) (n := n) (q := q) hn hq (f := fun i => a i ^ (2:ℝ))).symm

/-- Splitting a block sum according to the level-`n` index. -/
lemma sum_blk_fiber {N n : ℕ} (hn : n ≤ N) (f : ℕ → ℝ≥0∞) :
    ∑ q ∈ Finset.range (2 ^ n), ∑ i ∈ blk N n q, f i = ∑ i ∈ Finset.range (2 ^ N), f i := by
  have hmem : ∀ i ∈ Finset.range (2 ^ N), i / 2 ^ (N - n) ∈ Finset.range (2 ^ n) := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    have hMN : 2 ^ (N - n) * 2 ^ n = 2 ^ N := by
      rw [mul_comm, ← pow_add, Nat.add_sub_cancel' hn]
    exact Nat.div_lt_of_lt_mul (by rw [hMN]; exact hi)
  rw [← Finset.sum_fiberwise_of_maps_to hmem f]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => rfl

/-- The per-level multiplicity estimate for the Whitney decomposition. -/
lemma whitney_level_bound {N : ℕ} {W : Finset (ℕ × ℕ × ℕ)}
    (hW1 : ∀ p ∈ W, 2 ≤ p.1 ∧ p.1 ≤ N ∧ p.2.1 < 2 ^ p.1 ∧ p.2.2 < 2 ^ p.1)
    (hW3 : ∀ n, 2 ≤ n → n ≤ N → ∀ i, i < 2 ^ n →
      (W.filter (fun p => p.1 = n ∧ (p.2.1 = i ∨ p.2.2 = i))).card ≤ 8)
    {n : ℕ} (hn2 : 2 ≤ n) (hnN : n ≤ N) (a : ℕ → ℝ≥0∞) :
    ∑ p ∈ W.filter (fun p => p.1 = n),
        l2Of (blk N n p.2.1) a * l2Of (blk N n p.2.2) a
      ≤ 16 * sqSum (Finset.range (2 ^ N)) a := by
  have hmem : ∀ p ∈ W.filter (fun p => p.1 = n), p.2.1 ∈ Finset.range (2 ^ n) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_range, ← hp.2]
    exact (hW1 p hp.1).2.2.1
  have hmem' : ∀ p ∈ W.filter (fun p => p.1 = n), p.2.2 ∈ Finset.range (2 ^ n) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_range, ← hp.2]
    exact (hW1 p hp.1).2.2.2
  have hfirst : ∑ p ∈ W.filter (fun p => p.1 = n), (l2Of (blk N n p.2.1) a) ^ (2:ℝ)
      ≤ 8 * ∑ q ∈ Finset.range (2 ^ n), (l2Of (blk N n q) a) ^ (2:ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmem (fun p => (l2Of (blk N n p.2.1) a) ^ (2:ℝ))]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.filter_filter]
    have hcongr : ∑ p ∈ W.filter (fun p => p.1 = n ∧ p.2.1 = q),
          (l2Of (blk N n p.2.1) a) ^ (2:ℝ)
          = ∑ _p ∈ W.filter (fun p => p.1 = n ∧ p.2.1 = q),
              (l2Of (blk N n q) a) ^ (2:ℝ) :=
      Finset.sum_congr rfl fun p hp => by
        rw [Finset.mem_filter] at hp
        rw [hp.2.2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul' ?_ le_rfl
    exact_mod_cast whitney_multiplicity hW3 hn2 hnN (Finset.mem_range.mp hq)
  have hsecond : ∑ p ∈ W.filter (fun p => p.1 = n), (l2Of (blk N n p.2.2) a) ^ (2:ℝ)
      ≤ 8 * ∑ q ∈ Finset.range (2 ^ n), (l2Of (blk N n q) a) ^ (2:ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmem' (fun p => (l2Of (blk N n p.2.2) a) ^ (2:ℝ))]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    rw [Finset.filter_filter]
    have hcongr : ∑ p ∈ W.filter (fun p => p.1 = n ∧ p.2.2 = q),
          (l2Of (blk N n p.2.2) a) ^ (2:ℝ)
          = ∑ _p ∈ W.filter (fun p => p.1 = n ∧ p.2.2 = q),
              (l2Of (blk N n q) a) ^ (2:ℝ) :=
      Finset.sum_congr rfl fun p hp => by
        rw [Finset.mem_filter] at hp
        rw [hp.2.2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul' ?_ le_rfl
    exact_mod_cast whitney_multiplicity' hW3 hn2 hnN (Finset.mem_range.mp hq)
  have hsplit : ∑ q ∈ Finset.range (2 ^ n), (l2Of (blk N n q) a) ^ (2:ℝ)
      = sqSum (Finset.range (2 ^ N)) a := by
    rw [sqSum]
    rw [← sum_blk_fiber hnN (fun i => a i ^ (2:ℝ))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [l2Of_sq]
    rfl
  calc ∑ p ∈ W.filter (fun p => p.1 = n),
        l2Of (blk N n p.2.1) a * l2Of (blk N n p.2.2) a
      ≤ ∑ p ∈ W.filter (fun p => p.1 = n),
          ((l2Of (blk N n p.2.1) a) ^ (2:ℝ) + (l2Of (blk N n p.2.2) a) ^ (2:ℝ)) :=
        Finset.sum_le_sum fun p _ => mul_le_sq_add_sq _ _
    _ = (∑ p ∈ W.filter (fun p => p.1 = n), (l2Of (blk N n p.2.1) a) ^ (2:ℝ))
        + ∑ p ∈ W.filter (fun p => p.1 = n), (l2Of (blk N n p.2.2) a) ^ (2:ℝ) :=
        Finset.sum_add_distrib
    _ ≤ 8 * ∑ q ∈ Finset.range (2 ^ n), (l2Of (blk N n q) a) ^ (2:ℝ)
        + 8 * ∑ q ∈ Finset.range (2 ^ n), (l2Of (blk N n q) a) ^ (2:ℝ) :=
        add_le_add hfirst hsecond
    _ = 16 * sqSum (Finset.range (2 ^ N)) a := by rw [hsplit]; ring

/-! ## 6. The symmetric bilinear inequality and the reduction -/

/-- The symmetric bilinear decoupling inequality for an *unordered* pair of coarse intervals of
common length `h`; it is the body of `BilinDecOn` with the second interval at `b` (no ordering
requirement). -/
def BilinDecPair (k M : ℕ) (h a b : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ (f f' : Fin M → E k → ℂ),
    (∀ j : Fin M, IsFourierRep k (plate k (h / (2 * M))
      (a + (((j : ℕ) : ℝ) + 1 / 2) * h / M)) (f j)) →
    (∀ j : Fin M, IsFourierRep k (plate k (h / (2 * M))
      (b + (((j : ℕ) : ℝ) + 1 / 2) * h / M)) (f' j)) →
    (∫⁻ x, ((‖(∑ j, f j x)‖₊ : ℝ≥0∞) ^ rExp k)
        * ((‖(∑ j, f' j x)‖₊ : ℝ≥0∞) ^ rExp k))
      ≤ (C ^ ((k : ℝ) * ((k : ℝ) + 1)))
          * (l2Norm fun j => lpNorm k (pE k) (f j)) ^ rExp k
          * (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ rExp k

lemma BilinDecPair.of_bilinDecOn {k M : ℕ} {h a b d : ℝ} {C : ℝ≥0∞}
    (hB : BilinDecOn k M h a d C) (hb : b = a + h + d) : BilinDecPair k M h a b C := by
  subst hb
  intro f f' hf hf'
  exact hB f f' hf hf'

lemma BilinDecPair.comm {k M : ℕ} {h a b : ℝ} {C : ℝ≥0∞} (hB : BilinDecPair k M h a b C) :
    BilinDecPair k M h b a C := by
  intro f f' hf hf'
  have h := hB f' f hf' hf
  have hL : (∫⁻ x, ((‖(∑ j, f j x)‖₊ : ℝ≥0∞) ^ rExp k)
        * ((‖(∑ j, f' j x)‖₊ : ℝ≥0∞) ^ rExp k))
      = (∫⁻ x, ((‖(∑ j, f' j x)‖₊ : ℝ≥0∞) ^ rExp k)
        * ((‖(∑ j, f j x)‖₊ : ℝ≥0∞) ^ rExp k)) :=
    lintegral_congr fun x => mul_comm _ _
  rw [hL]
  refine h.trans (le_of_eq ?_)
  exact mul_right_comm _ _ _

/-- The sum over the square rewritten as a double sum. -/
lemma sum_pairSet_eq {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ × ℕ → M) :
    ∑ q ∈ pairSet N, g q = ∑ i ∈ Finset.range (2 ^ N), ∑ j ∈ Finset.range (2 ^ N), g (i, j) := by
  rw [pairSet, Finset.product_eq_sprod, Finset.sum_product]

/-- **GLYZ Lemma 2.2 (bilinear reduction)**: the linear `ℓ²`-decoupling inequality at
dyadic scale `2^{-N}` follows from the symmetric bilinear inequalities at all the intermediate
dyadic scales. -/
theorem decLin_of_bilinDec (k N : ℕ) (hk : 1 ≤ k) (hN : 2 ≤ N) (C : ℕ → ℝ≥0∞)
    (hC : ∀ n, 2 ≤ n → n ≤ N → BilinDec k (2 ^ (N - n)) (C n)) :
    DecLin k (2 ^ N) ((6 + 16 * ∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ)) ^ (1/2 : ℝ)) := by
  classical
  intro f hf
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := Commons.Combinatorics.Dyadic.whitney_decomposition N hN
  have hW1' : ∀ p ∈ W, 2 ≤ p.1 ∧ p.1 ≤ N ∧ p.2.1 < 2 ^ p.1 ∧ p.2.2 < 2 ^ p.1 :=
    fun p hp => ⟨(hW1 p hp).1, (hW1 p hp).2.1, (hW1 p hp).2.2.1, (hW1 p hp).2.2.2.1⟩
  set F : ℕ → E k → ℂ := fun i => if h : i < 2 ^ N then f ⟨i, h⟩ else 0 with hFdef
  set a : ℕ → ℝ≥0∞ := fun i => lpNorm k (pE k) (F i) with hadef
  have hFa : ∀ i, a i = lpNorm k (pE k) (F i) := fun i => by rw [hadef]
  have hFm : ∀ i (hi : i < 2 ^ N), F i = f ⟨i, hi⟩ := by
    intro i hi
    rw [hFdef]
    simp only [dif_pos hi]
  have hF0 : ∀ i, 2 ^ N ≤ i → F i = 0 := by
    intro i hi
    rw [hFdef]
    simp only [dif_neg (not_lt.mpr hi)]
  have hFmeas : ∀ i, AEStronglyMeasurable (F i) volume := by
    intro i
    by_cases hi : i < 2 ^ N
    · rw [hFm i hi]; exact (hf ⟨i, hi⟩).aestronglyMeasurable
    · rw [hF0 i (by omega)]; exact aestronglyMeasurable_zero
  -- (P1), (P2): transfer the statement to the extended family
  have hgoal1 : (fun x : E k => ∑ j : Fin (2 ^ N), f j x)
      = fun x : E k => ∑ i ∈ Finset.range (2 ^ N), F i x := by
    funext x
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => F i x) (2 ^ N)]
    exact Finset.sum_congr rfl fun i _ => by rw [hFm i i.isLt]
  have hgoal2 : l2Norm (fun j : Fin (2 ^ N) => lpNorm k (pE k) (f j))
      = l2Of (Finset.range (2 ^ N)) a := by
    rw [l2Norm, l2Of, sqSum]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => a i ^ (2:ℝ)) (2 ^ N)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hFa i, hFm i i.isLt]
  rw [hgoal1, hgoal2]
  -- (P3): the Whitney decomposition of the square
  have hpt : ∀ q ∈ pairSet N, ∀ x : E k, F q.1 x * F q.2 x =
      (if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0)
      + ∑ p ∈ W, (if q.1 ∈ blk N p.1 p.2.1 ∧ q.2 ∈ blk N p.1 p.2.2
          then F q.1 x * F q.2 x else 0) := by
    intro q hq x
    rw [mem_pairSet] at hq
    by_cases hD : |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1
    · rw [if_pos hD]
      have hzero : ∑ p ∈ W, (if q.1 ∈ blk N p.1 p.2.1 ∧ q.2 ∈ blk N p.1 p.2.2
          then F q.1 x * F q.2 x else 0) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        rw [if_neg]
        rintro ⟨hm1, hm2⟩
        obtain ⟨hp1, hpN, hpq1, hpq2, hpabs⟩ := hW1 p hp
        rw [mem_blk] at hm1 hm2
        have hle := abs_div_pow_two_sub_le_one (m := N - p.1) hD
        rw [hm1.2, hm2.2] at hle
        rcases hpabs with h | h <;> omega
      rw [hzero, add_zero]
    ·
      have habs : (2:ℤ) ≤ |((q.1:ℤ)) - ((q.2:ℤ))| := by
        have := not_le.mp hD; omega
      obtain ⟨p₀, hp₀, huniq⟩ := hW4 q.1 hq.1 q.2 hq.2 habs
      have hsum : ∑ p ∈ W, (if q.1 ∈ blk N p.1 p.2.1 ∧ q.2 ∈ blk N p.1 p.2.2
          then F q.1 x * F q.2 x else 0) = F q.1 x * F q.2 x := by
        rw [Finset.sum_eq_single p₀ _ _]
        · rw [if_pos ⟨mem_blk.mpr ⟨hq.1, hp₀.2.1⟩, mem_blk.mpr ⟨hq.2, hp₀.2.2⟩⟩]
        · intro p hp hpne
          rw [if_neg]
          rintro ⟨hm1, hm2⟩
          exact hpne (huniq p ⟨hp, (mem_blk.mp hm1).2, (mem_blk.mp hm2).2⟩)
        · intro h
          exact absurd hp₀.1 h
      rw [if_neg hD, zero_add, hsum]
  have hkey : (fun x : E k => (∑ i ∈ Finset.range (2 ^ N), F i x)
        * (∑ j ∈ Finset.range (2 ^ N), F j x))
      = (∑ q ∈ pairSet N, (fun x : E k =>
          if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0))
        + (∑ p ∈ W, (fun x : E k =>
            (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x))) := by
    funext x
    rw [Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
    have hblocks : (∑ p ∈ W, ∑ q ∈ pairSet N,
        (if q.1 ∈ blk N p.1 p.2.1 ∧ q.2 ∈ blk N p.1 p.2.2
          then F q.1 x * F q.2 x else 0))
        = ∑ p ∈ W, (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x) :=
      Finset.sum_congr rfl fun p _ =>
        sum_pair_filter (fun i hi => Finset.mem_range.mpr (mem_blk.mp hi).1)
          (fun i hi => Finset.mem_range.mpr (mem_blk.mp hi).1) F x
    rw [Finset.sum_mul_sum]
    rw [← sum_pairSet_eq N (fun q => F q.1 x * F q.2 x)]
    rw [Finset.sum_congr rfl fun q hq => hpt q hq x]
    rw [Finset.sum_add_distrib, Finset.sum_comm, hblocks]
  -- measurability
  have hterm1 : ∀ q ∈ pairSet N, AEStronglyMeasurable (fun x : E k =>
      if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0) volume := by
    intro q _
    by_cases h : |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1
    · have he : (fun x : E k => if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1
          then F q.1 x * F q.2 x else 0) = fun x : E k => F q.1 x * F q.2 x := by
        funext x; rw [if_pos h]
      rw [he]; exact (hFmeas q.1).mul (hFmeas q.2)
    · have he : (fun x : E k => if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1
          then F q.1 x * F q.2 x else 0) = fun _ : E k => (0:ℂ) := by
        funext x; rw [if_neg h]
      rw [he]; exact aestronglyMeasurable_zero
  have hterm2 : ∀ p ∈ W, AEStronglyMeasurable (fun x : E k =>
      (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x)) volume := by
    intro p _
    have h1 : AEStronglyMeasurable (fun x : E k => ∑ i ∈ blk N p.1 p.2.1, F i x) volume := by
      have h := Finset.aestronglyMeasurable_sum (blk N p.1 p.2.1) fun i _ => hFmeas i
      have he : (∑ i ∈ blk N p.1 p.2.1, F i) = fun x : E k => ∑ i ∈ blk N p.1 p.2.1, F i x := by
        funext x; rw [Finset.sum_apply]
      rwa [he] at h
    have h2 : AEStronglyMeasurable (fun x : E k => ∑ j ∈ blk N p.1 p.2.2, F j x) volume := by
      have h := Finset.aestronglyMeasurable_sum (blk N p.1 p.2.2) fun j _ => hFmeas j
      have he : (∑ j ∈ blk N p.1 p.2.2, F j) = fun x : E k => ∑ j ∈ blk N p.1 p.2.2, F j x := by
        funext x; rw [Finset.sum_apply]
      rwa [he] at h
    exact h1.mul h2
  have hDmeas : AEStronglyMeasurable (∑ q ∈ pairSet N, (fun x : E k =>
      if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0)) volume :=
    Finset.aestronglyMeasurable_sum (pairSet N) hterm1
  have hBmeas : AEStronglyMeasurable (∑ p ∈ W, (fun x : E k =>
      (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x))) volume :=
    Finset.aestronglyMeasurable_sum W hterm2
  -- (P4): the per-block estimate
  have hblock : ∀ p ∈ W, lpNorm k (pE k / 2) (fun x : E k =>
      (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x))
      ≤ (C p.1) ^ (2:ℝ) * l2Of (blk N p.1 p.2.1) a * l2Of (blk N p.1 p.2.2) a := by
    intro p hp
    obtain ⟨hp1, hpN, hpq1, hpq2, hpabs⟩ := hW1 p hp
    have hne : p.2.1 ≠ p.2.2 := by
      intro h
      rw [h] at hpabs
      rcases hpabs with h' | h' <;> simp at h'
    have hMne : (2:ℕ) ^ (N - p.1) ≠ 0 := by positivity
    have hhpos : (0:ℝ) < 1 / (2:ℝ) ^ p.1 := by positivity
    have hsub1 : ∀ x : E k, (∑ i ∈ blk N p.1 p.2.1, F i x)
        = ∑ j : Fin (2 ^ (N - p.1)), F (p.2.1 * 2 ^ (N - p.1) + j) x :=
      fun x => sum_blk_eq (N := N) (n := p.1) (q := p.2.1) hpN hpq1 (f := fun i => F i x)
    have hsub2 : ∀ x : E k, (∑ i ∈ blk N p.1 p.2.2, F i x)
        = ∑ j : Fin (2 ^ (N - p.1)), F (p.2.2 * 2 ^ (N - p.1) + j) x :=
      fun x => sum_blk_eq (N := N) (n := p.1) (q := p.2.2) hpN hpq2 (f := fun i => F i x)
    have hsubF : (fun x : E k => (∑ i ∈ blk N p.1 p.2.1, F i x)
          * (∑ j ∈ blk N p.1 p.2.2, F j x))
        = fun x : E k => (∑ j : Fin (2 ^ (N - p.1)), F (p.2.1 * 2 ^ (N - p.1) + j) x)
            * (∑ j : Fin (2 ^ (N - p.1)), F (p.2.2 * 2 ^ (N - p.1) + j) x) := by
      funext x; rw [hsub1 x, hsub2 x]
    have hplate1 : ∀ j : Fin (2 ^ (N - p.1)), IsFourierRep k
        (plate k ((1 / (2:ℝ) ^ p.1) / (2 * (((2 ^ (N - p.1) : ℕ)) : ℝ)))
          ((p.2.1 : ℝ) * (1 / (2:ℝ) ^ p.1)
            + ((((j : ℕ) : ℝ) + 1 / 2) * (1 / (2:ℝ) ^ p.1))
              / (((2 ^ (N - p.1) : ℕ)) : ℝ)))
        (fun x : E k => F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x) := by
      intro j
      have hlt : p.2.1 * 2 ^ (N - p.1) + (j : ℕ) < 2 ^ N :=
        blockIdx_lt hpN rfl hpq1 j.2
      have hfun : (fun x : E k => F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x)
          = f ⟨p.2.1 * 2 ^ (N - p.1) + (j : ℕ), hlt⟩ := by
        funext x; rw [hFm _ hlt]
      rw [hfun, ← piecePlate_block k N p.1 p.2.1 (2 ^ (N - p.1)) hpN rfl hpq1 j]
      exact hf _
    have hplate2 : ∀ j : Fin (2 ^ (N - p.1)), IsFourierRep k
        (plate k ((1 / (2:ℝ) ^ p.1) / (2 * (((2 ^ (N - p.1) : ℕ)) : ℝ)))
          ((p.2.2 : ℝ) * (1 / (2:ℝ) ^ p.1)
            + ((((j : ℕ) : ℝ) + 1 / 2) * (1 / (2:ℝ) ^ p.1))
              / (((2 ^ (N - p.1) : ℕ)) : ℝ)))
        (fun x : E k => F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x) := by
      intro j
      have hlt : p.2.2 * 2 ^ (N - p.1) + (j : ℕ) < 2 ^ N :=
        blockIdx_lt hpN rfl hpq2 j.2
      have hfun : (fun x : E k => F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x)
          = f ⟨p.2.2 * 2 ^ (N - p.1) + (j : ℕ), hlt⟩ := by
        funext x; rw [hFm _ hlt]
      rw [hfun, ← piecePlate_block k N p.1 p.2.2 (2 ^ (N - p.1)) hpN rfl hpq2 j]
      exact hf _
    have hdist : ((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) = 2 ∨
        ((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) = 3 := by
      rcases hpabs with h | h <;> [left; right] <;> rw [h] <;> norm_num
    rw [hsubF]
    have hd : (((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) - 1) * (1 / (2:ℝ) ^ p.1)
        = 1 / (2:ℝ) ^ p.1 ∨
        (((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) - 1) * (1 / (2:ℝ) ^ p.1)
          = 2 * (1 / (2:ℝ) ^ p.1) := by
      rcases hdist with h | h
      · left; rw [h]; ring
      · right; rw [h]; ring
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hcast : ((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) = (p.2.2:ℝ) - (p.2.1:ℝ) := by
        have hneg : ((p.2.1:ℤ)) - ((p.2.2:ℤ)) < 0 := by
          have : ((p.2.1:ℤ)) < ((p.2.2:ℤ)) := by exact_mod_cast hlt
          omega
        rw [abs_of_neg hneg]; push_cast; ring
      have hcenter : (p.2.2:ℝ) * (1 / (2:ℝ) ^ p.1)
          = (p.2.1:ℝ) * (1 / (2:ℝ) ^ p.1) + 1 / (2:ℝ) ^ p.1
            + (((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) - 1) * (1 / (2:ℝ) ^ p.1) := by
        rw [hcast]; ring
      have hB := BilinDecPair.of_bilinDecOn
        (bilinDecOn_of_bilinDec (k := k) (M := 2 ^ (N - p.1)) hk hMne
          (hC p.1 hp1 hpN) hhpos hd ((p.2.1:ℝ) * (1 / (2:ℝ) ^ p.1))) hcenter
      have hpair := hB _ _ hplate1 hplate2
      have hX1 : (l2Norm fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
          (fun x : E k => F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x))
          = l2Of (blk N p.1 p.2.1) a := by
        rw [show (fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
              (fun x : E k => F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x))
            = fun j : Fin (2 ^ (N - p.1)) => a (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) from
            funext fun j => (hFa _).symm]
        exact l2Norm_sub_eq a hpN hpq1
      have hX2 : (l2Norm fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
          (fun x : E k => F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x))
          = l2Of (blk N p.1 p.2.2) a := by
        rw [show (fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
              (fun x : E k => F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x))
            = fun j : Fin (2 ^ (N - p.1)) => a (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) from
            funext fun j => (hFa _).symm]
        exact l2Norm_sub_eq a hpN hpq2
      have hr : (0:ℝ) ≤ 1 / rExp k := le_of_lt (one_div_pos.mpr (rExp_pos hk))
      have hPR : ((k:ℝ) * ((k:ℝ) + 1)) * (1 / rExp k) = 2 := by
        rw [rExp]; field_simp
      have hRR : rExp k * (1 / rExp k) = 1 := by
        field_simp [(rExp_pos hk).ne']
      refine (lpNorm_mul_eq_rpow_lintegral k hk
        (g := fun x : E k => ∑ j : Fin (2 ^ (N - p.1)),
          F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x)
        (h := fun x : E k => ∑ j : Fin (2 ^ (N - p.1)),
          F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x)
        (Finset.aestronglyMeasurable_fun_sum _ fun j _ => hFmeas _)
        (Finset.aestronglyMeasurable_fun_sum _ fun j _ => hFmeas _)).trans_le ?_
      refine (ENNReal.rpow_le_rpow hpair hr).trans (le_of_eq ?_)
      simp only [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul, hPR, hRR,
        ENNReal.rpow_two, ENNReal.rpow_one, hX1, hX2]
    · have hcast : ((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) = (p.2.1:ℝ) - (p.2.2:ℝ) := by
        have hpos : 0 < ((p.2.1:ℤ)) - ((p.2.2:ℤ)) := by
          have : ((p.2.2:ℤ)) < ((p.2.1:ℤ)) := by exact_mod_cast hgt
          omega
        rw [abs_of_pos hpos]; push_cast; ring
      have hcenter : (p.2.1:ℝ) * (1 / (2:ℝ) ^ p.1)
          = (p.2.2:ℝ) * (1 / (2:ℝ) ^ p.1) + 1 / (2:ℝ) ^ p.1
            + (((|((p.2.1:ℤ)) - ((p.2.2:ℤ))| : ℤ) : ℝ) - 1) * (1 / (2:ℝ) ^ p.1) := by
        rw [hcast]; ring
      have hB := (BilinDecPair.of_bilinDecOn
        (bilinDecOn_of_bilinDec (k := k) (M := 2 ^ (N - p.1)) hk hMne
          (hC p.1 hp1 hpN) hhpos hd ((p.2.2:ℝ) * (1 / (2:ℝ) ^ p.1))) hcenter).comm
      have hpair := hB _ _ hplate1 hplate2
      have hX1 : (l2Norm fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
          (fun x : E k => F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x))
          = l2Of (blk N p.1 p.2.1) a := by
        rw [show (fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
              (fun x : E k => F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x))
            = fun j : Fin (2 ^ (N - p.1)) => a (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) from
            funext fun j => (hFa _).symm]
        exact l2Norm_sub_eq a hpN hpq1
      have hX2 : (l2Norm fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
          (fun x : E k => F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x))
          = l2Of (blk N p.1 p.2.2) a := by
        rw [show (fun j : Fin (2 ^ (N - p.1)) => lpNorm k (pE k)
              (fun x : E k => F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x))
            = fun j : Fin (2 ^ (N - p.1)) => a (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) from
            funext fun j => (hFa _).symm]
        exact l2Norm_sub_eq a hpN hpq2
      have hr : (0:ℝ) ≤ 1 / rExp k := le_of_lt (one_div_pos.mpr (rExp_pos hk))
      have hPR : ((k:ℝ) * ((k:ℝ) + 1)) * (1 / rExp k) = 2 := by
        rw [rExp]; field_simp
      have hRR : rExp k * (1 / rExp k) = 1 := by
        field_simp [(rExp_pos hk).ne']
      refine (lpNorm_mul_eq_rpow_lintegral k hk
        (g := fun x : E k => ∑ j : Fin (2 ^ (N - p.1)),
          F (p.2.1 * 2 ^ (N - p.1) + (j : ℕ)) x)
        (h := fun x : E k => ∑ j : Fin (2 ^ (N - p.1)),
          F (p.2.2 * 2 ^ (N - p.1) + (j : ℕ)) x)
        (Finset.aestronglyMeasurable_fun_sum _ fun j _ => hFmeas _)
        (Finset.aestronglyMeasurable_fun_sum _ fun j _ => hFmeas _)).trans_le ?_
      refine (ENNReal.rpow_le_rpow hpair hr).trans (le_of_eq ?_)
      simp only [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul, hPR, hRR,
        ENNReal.rpow_two, ENNReal.rpow_one, hX1, hX2]
  -- the level splitting
  have hWmem : ∀ p ∈ W, p.1 ∈ Finset.Icc 2 N := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(hW1 p hp).1, (hW1 p hp).2.1⟩
  have hlevel : ∑ p ∈ W, (C p.1) ^ (2:ℝ) * l2Of (blk N p.1 p.2.1) a * l2Of (blk N p.1 p.2.2) a
      ≤ 16 * (∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ)) * sqSum (Finset.range (2 ^ N)) a := by
    have hfib := Finset.sum_fiberwise_of_maps_to hWmem
      (fun p : ℕ × ℕ × ℕ => (C p.1) ^ (2:ℝ) * l2Of (blk N p.1 p.2.1) a
        * l2Of (blk N p.1 p.2.2) a)
    rw [← hfib]
    calc ∑ n ∈ Finset.Icc 2 N, ∑ p ∈ W.filter (fun p => p.1 = n),
          (C p.1) ^ (2:ℝ) * l2Of (blk N p.1 p.2.1) a * l2Of (blk N p.1 p.2.2) a
        = ∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ) * ∑ p ∈ W.filter (fun p => p.1 = n),
            l2Of (blk N p.1 p.2.1) a * l2Of (blk N p.1 p.2.2) a := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mem_filter] at hp
          rw [hp.2, mul_assoc]
      _ ≤ ∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ) * (16 * sqSum (Finset.range (2 ^ N)) a) := by
          refine Finset.sum_le_sum fun n hn => ?_
          refine mul_le_mul' le_rfl ?_
          rw [Finset.mem_Icc] at hn
          refine le_trans (le_of_eq ?_) (whitney_level_bound hW1' hW3 hn.1 hn.2 a)
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mem_filter] at hp
          rw [hp.2]
      _ = 16 * (∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ)) * sqSum (Finset.range (2 ^ N)) a := by
          rw [← Finset.sum_mul]
          ring
  -- assemble
  have hone : (1:ℝ≥0∞) ≤ pE k / 2 := one_le_pE_div_two hk
  have hsplit : lpNorm k (pE k / 2) ((∑ q ∈ pairSet N, (fun x : E k =>
        if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0))
      + (∑ p ∈ W, (fun x : E k =>
          (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x))))
      ≤ (6 * sqSum (Finset.range (2 ^ N)) a)
        + 16 * (∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ)) * sqSum (Finset.range (2 ^ N)) a := by
    calc lpNorm k (pE k / 2) ((∑ q ∈ pairSet N, (fun x : E k =>
          if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0))
        + (∑ p ∈ W, (fun x : E k =>
            (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x))))
        ≤ lpNorm k (pE k / 2) (∑ q ∈ pairSet N, (fun x : E k =>
            if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0))
          + lpNorm k (pE k / 2) (∑ p ∈ W, (fun x : E k =>
            (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x))) :=
          eLpNorm_add_le (μ := volume) hone
      _ ≤ (∑ q ∈ pairSet N, lpNorm k (pE k / 2) (fun x : E k =>
            if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0))
          + (∑ p ∈ W, (C p.1) ^ (2:ℝ) * l2Of (blk N p.1 p.2.1) a
            * l2Of (blk N p.1 p.2.2) a) := by
          refine add_le_add ?_ ?_
          · exact eLpNorm_sum_le (μ := volume) hone
          · refine (eLpNorm_sum_le (μ := volume) hone).trans ?_
            exact Finset.sum_le_sum hblock
      _ ≤ 6 * sqSum (Finset.range (2 ^ N)) a
          + 16 * (∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ)) * sqSum (Finset.range (2 ^ N)) a := by
          refine add_le_add ?_ hlevel
          refine (Finset.sum_le_sum fun q hq => ?_).trans (diagonal_bound a)
          by_cases h : |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1
          · have he : (fun x : E k => (if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1
                then F q.1 x * F q.2 x else 0)) = fun x : E k => F q.1 x * F q.2 x := by
              funext x; rw [if_pos h]
            rw [he, if_pos h]
            exact eLpNorm_mul_le_lp k (hFmeas q.1) (hFmeas q.2)
          · have he : (fun x : E k => (if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1
                then F q.1 x * F q.2 x else 0)) = fun _ : E k => (0:ℂ) := by
              funext x; rw [if_neg h]
            rw [he, if_neg h, lpNorm_zero]
  calc lpNorm k (pE k) (fun x : E k => ∑ i ∈ Finset.range (2 ^ N), F i x)
      = (lpNorm k (pE k / 2) (fun x : E k => (∑ i ∈ Finset.range (2 ^ N), F i x)
          * (∑ j ∈ Finset.range (2 ^ N), F j x))) ^ (1/2:ℝ) :=
        eLpNorm_eq_sqrt_mul_self k (Finset.aestronglyMeasurable_fun_sum _ fun i _ => hFmeas i)
    _ = (lpNorm k (pE k / 2) ((∑ q ∈ pairSet N, (fun x : E k =>
            if |((q.1:ℤ)) - ((q.2:ℤ))| ≤ 1 then F q.1 x * F q.2 x else 0))
          + (∑ p ∈ W, (fun x : E k =>
              (∑ i ∈ blk N p.1 p.2.1, F i x) * (∑ j ∈ blk N p.1 p.2.2, F j x))))) ^ (1/2:ℝ) := by
        rw [hkey]
    _ ≤ ((6 + 16 * (∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ)))
          * sqSum (Finset.range (2 ^ N)) a) ^ (1/2:ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        refine hsplit.trans (le_of_eq ?_)
        ring
    _ = (6 + 16 * (∑ n ∈ Finset.Icc 2 N, (C n) ^ (2:ℝ))) ^ (1/2:ℝ)
          * l2Of (Finset.range (2 ^ N)) a := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
        rfl

end Submission.Vinogradov
