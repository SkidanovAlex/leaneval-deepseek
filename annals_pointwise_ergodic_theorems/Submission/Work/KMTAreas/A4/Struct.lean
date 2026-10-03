/-
# Corollary `struct` of §5: the structure of the dual function

This module sets up the interface of Krause--Mirek--Tao's Corollary `struct` (§5), i.e. the
decomposition of the first dual function `Ã*_N(h,g)` produced by Proposition `lip` (the alternate
inverse theorem) together with the Hahn--Banach Lemma `hahn`.

The content is

* `LipOutput P ρ C K` — the *conclusion* of Proposition `lip` (with explicit constants `C,K`),
  as a predicate, so that the (in-flight) theorem `A4.peluseLipUniform` can be plugged in by
  pure bookkeeping;
* `structPhi P ρ C K δ N` — the family `Φ` of Corollary `struct`: the `ℓ²(ℤ)`-functions that
  Proposition `lip` may return, i.e. those with the `ℓ^∞` and `ℓ¹` bounds, Fourier support in
  `majorArc ρ l k` with `2^l ≤ Cδ^{-K}`, `2^k ≤ Cδ^{-K}/N`;
* `ahalfStarL2` — the dual function `Ã*_N(h,g)` as an element of `ℓ²(ℤ)`;
* `structHahnHyp` — **the content of Corollary `struct`**: under the hypotheses of Proposition
  `lip`, the Hahn--Banach hypothesis of Lemma `hahn` holds for `G = Ã*_N(h,g)` with `A = δN^d`
  and `B = δ^K N^d/2`.  Feeding it to `A4.hahn_decomposition` gives the paper's decomposition
  `Ã*_N(h,g) = ∑_α F_α + E₁ + E₂` with `‖E₁‖_{ℓ¹} ≤ δN^d` and `‖E₂‖_{ℓ²} ≤ δ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.Hahn
import Submission.Work.Analysis.InverseTheory.Transpose

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger (L2Z)
open Work.Analysis.InverseTheory

/-! ## The conclusion of Proposition `lip`, as a predicate -/

/-- **The conclusion of Proposition `lip`** (the alternate inverse theorem for `f`, §5), with
explicit constants `C, K`: for `1`-bounded functions `f,g,h` supported in `[-N₀,N₀]` with
`N₀ ~ N^d` and a large trilinear form, there is `F` with the `ℓ^∞`/`ℓ¹` bounds, Fourier support
in `majorArc ρ l k` with `2^l ≤ Cδ^{-K}`, `2^k ≤ Cδ^{-K}/N`, and the correlation
`δ^K N^d ≤ |⟨f,F⟩|`.

(The `Summable` conjunct makes the `ℓ¹` bound honest: `Mathlib`'s `tsum` is `0` for a
non-summable family.) -/
def LipOutput (P : Polynomial ℤ) (ρ C K : ℝ) : Prop :=
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖F x‖) ∧
      (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      FourierSupportIn F (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖

/-! ## The family `Φ` of Corollary `struct` -/

/-- **The family `Φ` of Corollary `struct`**: the functions that Proposition `lip` may return —
pointwise bounded by `C δ^{-K}`, `ℓ¹`-norm at most `C δ^{-K} N^d`, and Fourier supported in
`majorArc ρ l k` with `2^l ≤ C δ^{-K}`, `2^k ≤ C δ^{-K}/N`. -/
def structPhi (P : Polynomial ℤ) (ρ : ℝ) (C K δ : ℝ) (N : ℕ) : Set L2Z :=
  {ψ | (∀ x : ℤ, ‖ψ x‖ ≤ C * δ⁻¹ ^ K) ∧
       Summable (fun x : ℤ => ‖ψ x‖) ∧
       (∑' x : ℤ, ‖ψ x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
       (∃ l : ℕ, ∃ k : ℤ, FourierSupportIn (fun x : ℤ => ψ x) (majorArc ρ l k) ∧
         (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧ (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ))}

/-! ## The dual function as an element of `ℓ²(ℤ)` -/

theorem supportIn_ahalfTranspose {N N₀ : ℕ} {P : Polynomial ℤ} {h g : ℤ → ℂ}
    (hh : SupportIn h N₀) (hg : SupportIn g N₀) :
    SupportIn (AhalfTranspose N P h g) (N₀ + N) := by
  intro x hx
  rw [AhalfTranspose]
  refine mul_eq_zero_of_right _ ?_
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hhn : h (x - (n : ℤ)) = 0 := by
    apply hh
    have hnN : (n : ℤ).natAbs ≤ N := by
      rw [Int.natAbs_natCast]
      exact hn.2
    have h1 : x.natAbs ≤ (x - (n : ℤ)).natAbs + (n : ℤ).natAbs := by
      have := Int.natAbs_add_le (x - (n : ℤ)) (n : ℤ)
      simpa using this
    omega
  rw [hhn, zero_mul]

/-- The dual function `Ã*_N(h,g)` is in `ℓ²(ℤ)` when `h` is finitely supported. -/
theorem memℓp_ahalfTranspose {N N₀ : ℕ} {P : Polynomial ℤ} {h g : ℤ → ℂ}
    (hh : SupportIn h N₀) (hg : SupportIn g N₀) :
    Memℓp (fun x : ℤ => AhalfTranspose N P h g x) 2 := by
  have hsupp : SupportIn (AhalfTranspose N P h g) (N₀ + N) :=
    supportIn_ahalfTranspose (N := N) (P := P) hh hg
  refine memℓp_gen ?_
  rw [show ((2 : ℝ≥0∞)).toReal = 2 by norm_num]
  refine summable_of_ne_finset_zero
    (s := Finset.Icc (-(((N₀ + N : ℕ) : ℤ))) (((N₀ + N : ℕ) : ℤ))) fun x hx => ?_
  have hx' : N₀ + N < x.natAbs := by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · omega
    · omega
  rw [hsupp x hx']
  simp

/-- The dual function `Ã*_N(h,g)` as an element of `ℓ²(ℤ)`. -/
def ahalfStarL2 (N : ℕ) (P : Polynomial ℤ) (h g : ℤ → ℂ) (N₀ : ℕ)
    (hh : SupportIn h N₀) (hg : SupportIn g N₀) : L2Z :=
  ⟨fun x : ℤ => AhalfTranspose N P h g x, memℓp_ahalfTranspose hh hg⟩

@[simp] theorem ahalfStarL2_apply (N : ℕ) (P : Polynomial ℤ) (h g : ℤ → ℂ) (N₀ : ℕ)
    (hh : SupportIn h N₀) (hg : SupportIn g N₀) (x : ℤ) :
    ahalfStarL2 N P h g N₀ hh hg x = AhalfTranspose N P h g x := rfl


/-! ## The strengthened form of Proposition `lip` needed by Corollary `struct` -/

/-- **Proposition `lip` with the honest `ℓ¹` bound and the spatial tail bound.**  Same as
`LipOutput`, plus the summability of `‖F ·‖` (so that the `ℓ¹` bound is not vacuous) and the
spatial concentration of `F` in `[-2N^d, 2N^d]` (needed to replace the test function `f` by its
truncation in the Hahn--Banach step of Corollary `struct`). -/
def LipOutputTail (P : Polynomial ℤ) (ρ C K : ℝ) : Prop :=
  ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
    (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree →
    SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
    (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
    δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
    ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
      Summable (fun x : ℤ => ‖F x‖) ∧
      (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
      (∑' x : ℤ, (if 2 * N ^ P.natDegree < x.natAbs then ‖F x‖ else 0)
        ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2) ∧
      FourierSupportIn F (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ C * δ⁻¹ ^ K ∧
      (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
      δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖

/-! ## The Hahn--Banach hypothesis of Corollary `struct`

The tail conjunct of `LipOutputTail` is stated with the `ℕ`-valued distance `x.natAbs` (the shape
used by `lipInput` below); a source proving it with the real form `|(x : ℝ)|` only needs the
one-line conversion `((x.natAbs : ℕ) : ℝ) = |(x : ℝ)|` for every `x : ℤ`. -/

/-- The test function fed to Proposition `lip` in the proof of Corollary `struct`: the conjugate
of `f`, truncated to the window `[-2N^d, 2N^d]`. -/
def lipInput (P : Polynomial ℤ) (N : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x : ℤ => if x.natAbs ≤ 2 * N ^ P.natDegree then star (f x) else 0

theorem supportIn_lipInput (P : Polynomial ℤ) (N : ℕ) (f : ℤ → ℂ) :
    SupportIn (lipInput P N f) (2 * N ^ P.natDegree) := by
  intro x hx
  simp only [lipInput]
  exact if_neg (by omega)

theorem norm_lipInput_le_one (P : Polynomial ℤ) (N : ℕ) {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) : ∀ x : ℤ, ‖lipInput P N f x‖ ≤ 1 := by
  intro x
  simp only [lipInput]
  split
  · rw [norm_star]; exact hf x
  · simp

theorem lipInput_eq_star {P : Polynomial ℤ} {N : ℕ} {f : ℤ → ℂ} {x : ℤ}
    (hx : x.natAbs ≤ 2 * N ^ P.natDegree) : lipInput P N f x = star (f x) := by
  simp only [lipInput]
  exact if_pos hx

theorem lipInput_eq_zero {P : Polynomial ℤ} {N : ℕ} {f : ℤ → ℂ} {x : ℤ}
    (hx : 2 * N ^ P.natDegree < x.natAbs) : lipInput P N f x = 0 := by
  simp only [lipInput]
  exact if_neg (by omega)


theorem memℓp_of_l1 {F : ℤ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (h1 : Summable fun x : ℤ => ‖F x‖) (h2 : ∀ x : ℤ, ‖F x‖ ≤ B) : Memℓp F 2 := by
  refine memℓp_gen ?_
  rw [show ((2 : ℝ≥0∞)).toReal = 2 by norm_num]
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) (h1.mul_left B)
  simpa [pow_two] using mul_le_mul_of_nonneg_right (h2 x) (norm_nonneg (F x))

/-- The trilinear form of the truncated conjugate is the inner product with the dual function:
this is the identity on which the Hahn--Banach hypothesis of Corollary `struct` rests. -/
theorem bilinPair_lipInput_eq_inner {P : Polynomial ℤ} (hP : 1 ≤ P.natDegree) {N N₀ : ℕ}
    (hN : 1 ≤ N) (hN0 : N₀ ≤ N ^ P.natDegree) {g h : ℤ → ℂ} {f : L2Z}
    (hgs : SupportIn g N₀) (hhs : SupportIn h N₀) :
    bilinPair (AhalfZ N P (lipInput P N (fun x : ℤ => f x)) g) h
      = inner ℂ f (ahalfStarL2 N P h g N₀ hhs hgs) := by
  have hM : N₀ + N ≤ 2 * N ^ P.natDegree := by
    have h1 : N ≤ N ^ P.natDegree := by
      calc N = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ P.natDegree := Nat.pow_le_pow_right hN hP
    omega
  rw [bilinPair_AhalfZ_eq_transpose (FinSupp.of_supportIn (supportIn_lipInput P N _))
    (FinSupp.of_supportIn hgs) (FinSupp.of_supportIn hhs) N P]
  simp only [bilinPair, lp.inner_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : x.natAbs ≤ 2 * N ^ P.natDegree
  · rw [lipInput_eq_star hx, ahalfStarL2_apply, RCLike.inner_apply]
    simp only [starRingEnd_apply]
  · rw [lipInput_eq_zero (by omega), ahalfStarL2_apply, RCLike.inner_apply,
      supportIn_ahalfTranspose (N := N) (P := P) hhs hgs x (by omega)]
    simp


/-- The tail estimate: pairing `F` against the difference between `star ∘ f` and its truncation
costs at most the mass of `F` outside the window `[-2N^d,2N^d]`. -/
theorem norm_tsum_mul_sub_lipInput_le {P : Polynomial ℤ} {N : ℕ} {F f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hFsum : Summable fun x : ℤ => ‖F x‖) :
    ‖∑' x : ℤ, F x * (star (f x) - lipInput P N f x)‖
      ≤ ∑' x : ℤ, (if 2 * N ^ P.natDegree < x.natAbs then ‖F x‖ else 0) := by
  have hbound : ∀ x : ℤ, ‖F x * (star (f x) - lipInput P N f x)‖
      ≤ if 2 * N ^ P.natDegree < x.natAbs then ‖F x‖ else 0 := by
    intro x
    by_cases hx : x.natAbs ≤ 2 * N ^ P.natDegree
    · rw [lipInput_eq_star hx, sub_self, mul_zero, norm_zero]
      split <;> simp
    · rw [lipInput_eq_zero (by omega), sub_zero, norm_mul, norm_star,
        if_pos (by omega : 2 * N ^ P.natDegree < x.natAbs)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hf x)
  have hsum2 : Summable fun x : ℤ => (if 2 * N ^ P.natDegree < x.natAbs then ‖F x‖ else 0) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) hFsum
    split
    · exact le_rfl
    · exact norm_nonneg _
  have hsum1 : Summable fun x : ℤ => ‖F x * (star (f x) - lipInput P N f x)‖ :=
    Summable.of_nonneg_of_le (fun x => by positivity) hbound hsum2
  calc ‖∑' x : ℤ, F x * (star (f x) - lipInput P N f x)‖
      ≤ ∑' x : ℤ, ‖F x * (star (f x) - lipInput P N f x)‖ := norm_tsum_le_tsum_norm hsum1
    _ ≤ ∑' x : ℤ, (if 2 * N ^ P.natDegree < x.natAbs then ‖F x‖ else 0) :=
        hsum1.tsum_le_tsum hbound hsum2


/-- **The Hahn--Banach hypothesis of Corollary `struct`.**  Under the hypotheses of Proposition
`lip` (in the strengthened form `LipOutputTail`), every `1`-bounded `f` whose pairing with the
dual function `Ã*_N(h,g)` exceeds `δN^d` correlates with an element of `structPhi` beyond
`δ^K N^d/4`.  Feeding this to `hahn_decomposition` produces the paper's decomposition
`Ã*_N(h,g) = ∑_α F_α + E₁ + E₂`. -/
theorem structHahnHyp {P : Polynomial ℤ} (hP : 2 ≤ P.natDegree) {ρ C K : ℝ} (hC : 0 < C)
    (hK : 0 < K) (hLip : LipOutputTail P ρ C K) {N N₀ : ℕ} (hN : 1 ≤ N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN0lo : (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ))
    (hN0hi : (N₀ : ℝ) ≤ (N : ℝ) ^ P.natDegree) {g h : ℤ → ℂ}
    (hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1) (hh1 : ∀ x : ℤ, ‖h x‖ ≤ 1)
    (hgs : SupportIn g N₀) (hhs : SupportIn h N₀) :
    ∀ f : L2Z, (∀ x : ℤ, ‖f x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree < ‖inner ℂ f (ahalfStarL2 N P h g N₀ hhs hgs)‖ →
      ∃ φ ∈ structPhi P ρ C K δ N,
        δ ^ K * (N : ℝ) ^ P.natDegree / 4 < ‖inner ℂ f φ‖ := by
  intro f hf1 hfbig
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hP
  have hN0Nat : N₀ ≤ N ^ P.natDegree := by exact_mod_cast hN0hi
  have hcast : (((N ^ P.natDegree : ℕ)) : ℝ) = (N : ℝ) ^ P.natDegree := by push_cast; ring
  have hMlo : (N : ℝ) ^ P.natDegree / 2 ≤ (((2 * N ^ P.natDegree : ℕ)) : ℝ) := by
    push_cast [hcast]; linarith [hN0lo, hN0hi]
  have hMhi : (((2 * N ^ P.natDegree : ℕ)) : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree := by
    push_cast [hcast]; linarith
  have hN0le : N₀ ≤ 2 * N ^ P.natDegree := by
    have h1 : N ^ P.natDegree ≤ 2 * N ^ P.natDegree := Nat.le_mul_of_pos_left _ (by norm_num)
    omega
  have hkey : δ * (N : ℝ) ^ P.natDegree
      ≤ ‖bilinPair (AhalfZ N P (lipInput P N (fun x : ℤ => f x)) g) h‖ := by
    rw [bilinPair_lipInput_eq_inner hd1 hN hN0Nat hgs hhs]
    exact le_of_lt hfbig
  obtain ⟨F, l, k, hF1, hFsum, hFl1, hFtail, hFsupp, hFl, hFk, hFcorr⟩ :=
    hLip N (2 * N ^ P.natDegree) δ (lipInput P N (fun x : ℤ => f x)) g h hN hδ0 hδ1
      hMlo hMhi (supportIn_lipInput P N _) (hgs.mono hN0le) (hhs.mono hN0le)
      (norm_lipInput_le_one P N hf1) hg1 hh1 hkey
  have hB0 : (0 : ℝ) ≤ C * δ⁻¹ ^ K :=
    le_of_lt (mul_pos hC (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) K))
  set φ : L2Z := ⟨F, memℓp_of_l1 hB0 hFsum hF1⟩ with hφ
  have hφapply : ∀ x : ℤ, φ x = F x := fun x => rfl
  have hδK : 0 < δ ^ K * (N : ℝ) ^ P.natDegree :=
    mul_pos (Real.rpow_pos_of_pos hδ0 K) (pow_pos (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)) _)
  refine ⟨φ, ?_, ?_⟩
  · refine ⟨fun x => ?_, ?_, ?_, ⟨l, k, ?_, hFl, hFk⟩⟩
    · rw [hφapply]; exact hF1 x
    · simpa only [hφapply] using hFsum
    · simpa only [hφapply] using hFl1
    · simpa only [hφapply] using hFsupp
  · -- the correlation
    set S : ℤ → ℂ := fun x => star (f x) - lipInput P N (fun x : ℤ => f x) x with hS
    have hbS : ∀ x : ℤ, ‖S x‖ ≤ 2 := by
      intro x
      rw [hS]
      calc ‖star (f x) - lipInput P N (fun x : ℤ => f x) x‖
          ≤ ‖star (f x)‖ + ‖lipInput P N (fun x : ℤ => f x) x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [norm_star]
            exact add_le_add (hf1 x) (norm_lipInput_le_one P N hf1 x)
        _ = 2 := by norm_num
    have hsumS : Summable fun x : ℤ => F x * S x := by
      refine Summable.of_norm ?_
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hFsum.mul_left 2)
      rw [norm_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right (hbS x) (norm_nonneg (F x))
    have hsumA : Summable fun x : ℤ => F x * lipInput P N (fun x : ℤ => f x) x := by
      refine Summable.of_norm ?_
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hFsum.mul_left 1)
      rw [norm_mul]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right (norm_lipInput_le_one P N hf1 x) (norm_nonneg (F x))
    have hinner : inner ℂ f φ = ∑' x : ℤ, F x * star (f x) := by
      rw [lp.inner_eq_tsum]
      refine tsum_congr fun x => ?_
      rw [RCLike.inner_apply, starRingEnd_apply, hφapply]
    have hpair : bilinPair (lipInput P N (fun x : ℤ => f x)) F
        = ∑' x : ℤ, F x * lipInput P N (fun x : ℤ => f x) x := by
      simp only [bilinPair]
      exact tsum_congr fun x => mul_comm _ _
    have hsplit : (∑' x : ℤ, F x * star (f x))
        = bilinPair (lipInput P N (fun x : ℤ => f x)) F + ∑' x : ℤ, F x * S x := by
      rw [hpair, ← hsumA.tsum_add hsumS]
      refine tsum_congr fun x => ?_
      rw [hS]; ring
    have htailb := norm_tsum_mul_sub_lipInput_le (P := P) (N := N) (F := F) hf1 hFsum
    have htail : ‖∑' x : ℤ, F x * S x‖
        ≤ ∑' x : ℤ, (if 2 * N ^ P.natDegree < x.natAbs then ‖F x‖ else 0) := by
      rw [hS]
      exact htailb
    have hmain : ‖inner ℂ f φ‖
        ≥ ‖bilinPair (lipInput P N (fun x : ℤ => f x)) F‖ - ‖∑' x : ℤ, F x * S x‖ := by
      rw [hinner, hsplit]
      have h2 : ‖bilinPair (lipInput P N (fun x : ℤ => f x)) F‖
          ≤ ‖bilinPair (lipInput P N (fun x : ℤ => f x)) F + ∑' x : ℤ, F x * S x‖
            + ‖∑' x : ℤ, F x * S x‖ := by
        have := norm_add_le (bilinPair (lipInput P N (fun x : ℤ => f x)) F
          + ∑' x : ℤ, F x * S x) (-(∑' x : ℤ, F x * S x))
        simpa using this
      linarith
    have hFtail' : ‖∑' x : ℤ, F x * S x‖ ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2 :=
      htail.trans hFtail
    linarith [hFcorr, hFtail', hmain, hδK]

end Work.KMTAreas.A4
