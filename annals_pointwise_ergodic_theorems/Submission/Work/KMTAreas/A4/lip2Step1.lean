/-
# Step 1 of Proposition `lip-2`: the major-arc correlation with the dual function

The proof of Proposition `lip-2` of Krause--Mirek--Tao, §5.2, starts from the hypothesis
`δ N^d ≤ |⟨Ã_N(f,g), h⟩|` of Theorem `pp`.  Transposing gives `|⟨Ã_N^*(h,g), f⟩| ≥ δ N^d`, and
since `f` is `1`-bounded and supported in `[-N₀,N₀]` with `N₀ ≲ N^d`, Cauchy--Schwarz bounds
`‖Ã_N^*(h,g)‖_{ℓ²}` from below by `δ N^{d/2}`.  The inverse theorem (Proposition `lip`, in the
refined form `Work.KMTAreas.A4.LipL1Fine`) applied to the *truncation of `Ã_N^*(h,g)`* then
produces a function `F` with a large pairing with `Ã_N^*(h,g)`, whose `ℤ`-Fourier transform is
supported in a union of `≤ δ^{-O(1)}` arcs of radius `≤ δ^{-O(1)}/N`.

This module carries out that step, including the reshaping of the returned function into
`lam • conj F` so that the pairing in the *unconjugated* form `⟨Ã_N^*(h,g), lam • conj F⟩` is large
(the bookkeeping of §5.2 needs the un-conjugated pairing, and conjugation is a Fourier-reflection
which preserves the support because the union of arcs is symmetric after adding `-α`).

## Main result

* `lip2_arcCorrelation` — the fine-arc function `F` with `δ^K N^d ≤ ‖⟨Ã_N^*(h,g), F⟩‖`,
  available in the "main case" `N^{d-1} ≳ δ^{-O(1)}` (the complementary case is the trivial
  construction of `lip2.lean`).

## Notation

`Ã_N^*(h,g)` is `AhalfTranspose N P h g` and `⟨·,·⟩` is `bilinPair`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs
import Submission.Work.KMTAreas.A4.Struct
import Submission.Work.KMTAreas.A4.norm_AhalfTranspose_le

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Cauchy--Schwarz on a finite set -/

/-- Cauchy--Schwarz for finite sums of complex numbers, in the form used below:
`‖∑_{x∈s} X x * f x‖ ≤ √(∑_{x∈s}‖X x‖²) * √(∑_{x∈s}‖f x‖²)`. -/
theorem norm_finset_sum_mul_le (s : Finset ℤ) (X f : ℤ → ℂ) :
    ‖∑ x ∈ s, X x * f x‖
      ≤ Real.sqrt (∑ x ∈ s, ‖X x‖ ^ 2) * Real.sqrt (∑ x ∈ s, ‖f x‖ ^ 2) := by
  have h1 : ‖∑ x ∈ s, X x * f x‖ ≤ ∑ x ∈ s, ‖X x‖ * ‖f x‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
  have h2 : (∑ x ∈ s, ‖X x‖ * ‖f x‖) ^ 2
      ≤ (∑ x ∈ s, ‖X x‖ ^ 2) * (∑ x ∈ s, ‖f x‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun x => ‖X x‖) (fun x => ‖f x‖)
  have h3 : 0 ≤ ∑ x ∈ s, ‖X x‖ * ‖f x‖ :=
    Finset.sum_nonneg fun x _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h4 : (∑ x ∈ s, ‖X x‖ * ‖f x‖)
      ≤ Real.sqrt ((∑ x ∈ s, ‖X x‖ ^ 2) * (∑ x ∈ s, ‖f x‖ ^ 2)) := by
    have h := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq h3] at h
  have hsq : (0:ℝ) ≤ (∑ x ∈ s, ‖X x‖ ^ 2) := Finset.sum_nonneg fun x _ => sq_nonneg _
  calc ‖∑ x ∈ s, X x * f x‖ ≤ ∑ x ∈ s, ‖X x‖ * ‖f x‖ := h1
    _ ≤ Real.sqrt ((∑ x ∈ s, ‖X x‖ ^ 2) * (∑ x ∈ s, ‖f x‖ ^ 2)) := h4
    _ = Real.sqrt (∑ x ∈ s, ‖X x‖ ^ 2) * Real.sqrt (∑ x ∈ s, ‖f x‖ ^ 2) :=
        Real.sqrt_mul hsq _

/-! ## Elementary cardinality and summability facts for supported functions -/

/-- Integer membership in `[-D,D]` is membership in the `natAbs` ball. -/
theorem mem_Icc_natAbs {D : ℕ} {x : ℤ} :
    x ∈ Finset.Icc (-(D:ℤ)) (D:ℤ) ↔ x.natAbs ≤ D := by
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (x.natAbs : ℤ) ≤ (D:ℤ) := by
      by_cases hx : 0 ≤ x
      · rw [Int.natAbs_of_nonneg hx]; exact h2
      · rw [← Int.natAbs_neg x, Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ -x)]; omega
    exact_mod_cast h3
  · intro hx
    have h3 : (x.natAbs : ℤ) ≤ (D:ℤ) := by exact_mod_cast hx
    constructor
    · have := Int.le_natAbs (a := -x); omega
    · have := Int.le_natAbs (a := x); omega

/-- A function supported in `[-M,M]` has the whole line as its summability support: `‖f‖²` is
summable. -/
theorem summable_norm_sq_of_supportIn {f : ℤ → ℂ} {M : ℕ} (hf : SupportIn f M) :
    Summable (fun x : ℤ => ‖f x‖ ^ 2) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(M : ℤ)) (M : ℤ)) fun x hx => ?_
  have hx' : M < x.natAbs := by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h <;> omega
  rw [hf x hx']; simp

/-- The `ℓ²` mass of a supported `1`-bounded function is at most `2M+1`. -/
theorem tsum_norm_sq_le_of_supportIn {f : ℤ → ℂ} {M : ℕ} (hf : SupportIn f M)
    (h1 : ∀ x : ℤ, ‖f x‖ ≤ 1) : (∑' x : ℤ, ‖f x‖ ^ 2) ≤ 2 * (M : ℝ) + 1 := by
  rw [tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ)) (fun x hx => by
    have hx' : M < x.natAbs := by
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h <;> omega
    rw [hf x hx']; simp)]
  have hterm : ∀ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ‖f x‖ ^ 2 ≤ 1 := fun x _ => by
    have := h1 x; nlinarith [norm_nonneg (f x)]
  calc ∑ x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ‖f x‖ ^ 2
      ≤ ∑ _x ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), (1 : ℝ) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc (-(M : ℤ)) (M : ℤ)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 2 * (M : ℝ) + 1 := by
        have hc : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card ≤ 2 * M + 1 := by
          rw [Int.card_Icc]; omega
        exact_mod_cast hc

/-- Counting lemma: the integers of `[-M,M]` lying outside `[-W,W]` number at most `2 (M - W)`. -/
theorem card_Icc_diff_Icc_le (M W : ℕ) :
    ((Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(W : ℤ)) (W : ℤ))).card ≤ 2 * (M - W) := by
  have hsub : (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(W : ℤ)) (W : ℤ))
      ⊆ Finset.Icc ((W : ℤ) + 1) (M : ℤ) ∪ Finset.Icc (-(M : ℤ)) (-((W : ℤ) + 1)) := by
    intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hy
    rcases hy with ⟨⟨h1, h2⟩, h3⟩
    simp only [Finset.mem_union, Finset.mem_Icc]
    by_cases h5 : -(W : ℤ) ≤ y
    · left
      constructor <;> omega
    · right
      constructor <;> omega
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 : (Finset.Icc ((W : ℤ) + 1) (M : ℤ)).card ≤ M - W := by
    rw [Int.card_Icc]; omega
  have h2 : (Finset.Icc (-(M : ℤ)) (-((W : ℤ) + 1))).card ≤ M - W := by
    rw [Int.card_Icc]; omega
  omega

/-! ## Conjugation and the `ℤ`-Fourier transform -/

theorem fourierNormOne (n : ℤ) (ξ : FreqCircle) : ‖(fourier n ξ : ℂ)‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- `star (fourier (-x) (-ξ)) = fourier (-x) ξ`. -/
theorem star_fourier (x : ℤ) (ξ : FreqCircle) :
    star (fourier (-x) (-ξ)) = fourier (-x) ξ := by
  have h1 : fourier (-x) (-ξ) = fourier x ξ := by
    rw [fourier_apply, fourier_apply]
    congr 1
    rw [neg_smul, smul_neg, neg_neg]
  rw [h1, @fourier_neg (1:ℝ) (n := x) (x := ξ)]
  rfl

/-- The `ℤ`-Fourier transform of the pointwise conjugate is the conjugate of the transform at the
negated frequency. -/
theorem ZFourier_star {F : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖) (ξ : FreqCircle) :
    ZFourier (fun x => star (F x)) ξ = star (ZFourier F (-ξ)) := by
  have hsum : Summable fun x : ℤ => F x * (fourier (-x) (-ξ) : ℂ) :=
    Summable.of_norm_bounded hF fun x => by
      rw [norm_mul, fourierNormOne, mul_one]
  rw [ZFourier, ZFourier, tsum_star]
  refine tsum_congr fun x => ?_
  rw [star_mul, star_fourier]
  ring

theorem ZFourier_const_mul {F : ℤ → ℂ} (hF : Summable fun x : ℤ => ‖F x‖)
    (c : ℂ) (ξ : FreqCircle) :
    ZFourier (fun x => c * F x) ξ = c * ZFourier F ξ := by
  have hsum : Summable fun x : ℤ => F x * (fourier (-x) ξ : ℂ) :=
    Summable.of_norm_bounded hF fun x => by
      rw [norm_mul, fourierNormOne, mul_one]
  rw [ZFourier, ZFourier, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  ring

theorem FourierSupportIn_star {F : ℤ → ℂ} {S : Set FreqCircle}
    (hF : Summable fun x : ℤ => ‖F x‖) (hs : FourierSupportIn F S)
    (hneg : ∀ ξ : FreqCircle, ξ ∉ S → -ξ ∉ S) :
    FourierSupportIn (fun x => star (F x)) S := by
  intro ξ hξ
  rw [ZFourier_star hF ξ, hs (-ξ) (hneg ξ hξ), star_zero]

theorem FourierSupportIn_const_mul {F : ℤ → ℂ} {S : Set FreqCircle}
    (hF : Summable fun x : ℤ => ‖F x‖) (c : ℂ) (hs : FourierSupportIn F S) :
    FourierSupportIn (fun x => c * F x) S := by
  intro ξ hξ
  rw [ZFourier_const_mul hF c ξ, hs ξ hξ, mul_zero]

/-- Symmetry of the union of arcs around a symmetric set of centres. -/
theorem neg_mem_arcSet_union {A : Finset FreqCircle} {r : ℝ} {ξ : FreqCircle}
    (hA : ∀ α ∈ A, -α ∈ A)
    (hξ : ξ ∈ (⋃ α ∈ (A : Set FreqCircle), arcSet α r)) :
    -ξ ∈ (⋃ α ∈ (A : Set FreqCircle), arcSet α r) := by
  obtain ⟨α, hα, hξ'⟩ := Set.mem_iUnion₂.mp hξ
  obtain ⟨θ, hθ, rfl⟩ := hξ'
  refine Set.mem_biUnion (Finset.mem_coe.mpr (hA α (Finset.mem_coe.mp hα))) ?_
  refine ⟨-θ, by simpa using hθ, ?_⟩
  have hcoeneg : ((-θ : ℝ) : FreqCircle) = -((θ : ℝ) : FreqCircle) :=
    AddCircle.coe_neg (1:ℝ) (x := θ)
  simp only [hcoeneg, neg_add]

/-- The power-function identity for the smoothing scale `δ²/16`. -/
theorem inv_rpow_sq_div_sixteen (δ : ℝ) (hδ : 0 < δ) (r : ℝ) :
    ((δ^2/16 : ℝ))⁻¹ ^ r = (16:ℝ)^r * δ⁻¹^(2*r) := by
  have h1 : ((δ^2/16 : ℝ))⁻¹ = (16:ℝ) * (δ⁻¹)^(2:ℕ) := by
    have h2 : (δ⁻¹)^(2:ℕ) = 1/δ^2 := by rw [inv_pow]; ring
    rw [inv_div, h2]; ring
  rw [h1, Real.mul_rpow (by norm_num) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast δ⁻¹ 2, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ δ⁻¹)]
  norm_num

/-- The key identity balancing the two scales `δ` and `δ²/16`: for `δ > 0` and any real `r`,
`δ^{-2r} · ((δ·δ)/16)^r = 16^{-r}`. -/
theorem rpow_smoothing_mul (δ : ℝ) (hδ : 0 < δ) (r : ℝ) :
    δ⁻¹ ^ (2*r) * (((δ*δ)/16) ^ r) = (16:ℝ)^(-r) := by
  have hB : ((δ*δ)/16) ^ r = δ ^ (2*r) * ((16:ℝ)^r)⁻¹ := by
    have hrr : δ ^ (r + r) = δ ^ (2*r) := by congr 1; ring
    rw [Real.div_rpow (mul_nonneg hδ.le hδ.le) (by norm_num : (0:ℝ) ≤ 16) r, div_eq_mul_inv,
      Real.mul_rpow hδ.le hδ.le, ← Real.rpow_add hδ r r, hrr]
  rw [hB, Real.inv_rpow hδ.le (2*r),
    show (δ ^ (2*r))⁻¹ * (δ ^ (2*r) * ((16:ℝ)^r)⁻¹)
        = ((δ ^ (2*r))⁻¹ * δ ^ (2*r)) * ((16:ℝ)^r)⁻¹ by ring,
    inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hδ (2*r))), one_mul]
  exact (Real.rpow_neg (by norm_num : (0:ℝ) ≤ 16) r).symm

/-! ## Step 1: the fine-arc correlation -/

theorem lip2_arcCorrelation (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (hlip : LipL1Fine P) :
    ∃ C K C₀ K₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < C₀ ∧ 0 < K₀ ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
      ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
        (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ 2 * (N : ℝ) ^ P.natDegree →
        SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
        δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
        C₀ * δ⁻¹ ^ K₀ ≤ (N : ℝ) ^ (P.natDegree - 1) →
        ∃ (k : ℤ) (A : Finset FreqCircle) (F : ℤ → ℂ),
          (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
          Summable (fun x : ℤ => ‖F x‖) ∧
          (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
          FourierSupportIn F (⋃ α ∈ (A : Set FreqCircle), arcSet α ((2 : ℝ) ^ k)) ∧
          (A.card : ℝ) ≤ C * δ⁻¹ ^ K ∧
          (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
          δ ^ K * (N : ℝ) ^ P.natDegree
            ≤ ‖bilinPair (AhalfTranspose N P h g) F‖ := by
  obtain ⟨C₁, K₁, hC₁pos, hK₁pos, hlip⟩ := hlip
  refine ⟨8 * (1 + C₁) * (16:ℝ) ^ (2*K₁) + 8, 2*K₁,
          8 * (1 + C₁) * (16:ℝ) ^ (2*K₁) + 32, 4*K₁ + 2, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · positivity
  · intro ρ hρ hρ1 N N₀ δ f g h hN hδ0 hδ1 hN0lo hN0hi hfs hgs hhs hf1 hg1 hh1 hcorr hmain
    set C : ℝ := 8 * (1 + C₁) * (16:ℝ) ^ (2*K₁) + 8 with hCeq
    set C₀ : ℝ := 8 * (1 + C₁) * (16:ℝ) ^ (2*K₁) + 32 with hC₀eq
    set K : ℝ := 2*K₁ with hKeq
    set K₀ : ℝ := 4*K₁ + 2 with hK₀eq
    have hCpos : 0 < C := by rw [hCeq]; positivity
    have hC₀pos : 0 < C₀ := by rw [hC₀eq]; positivity
    have hKpos : 0 < K := by rw [hKeq]; positivity
    have hK₀pos : 0 < K₀ := by rw [hK₀eq]; positivity
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hNdpos : (0:ℝ) < (N:ℝ)^P.natDegree :=
      pow_pos (by linarith : (0:ℝ) < (N:ℝ)) _
    have hNd1 : (1:ℝ) ≤ (N:ℝ)^P.natDegree := one_le_pow₀ hN1
    have h16pos : (0:ℝ) < 16 := by norm_num
    have hδinv1 : (1:ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
    have hδinvpos : (0:ℝ) < δ⁻¹ := inv_pos.mpr hδ0
    -- the smoothing scale
    set δ' : ℝ := δ^2/16 with hδ'eq
    have hδ'pos : 0 < δ' := by rw [hδ'eq]; positivity
    have hδ'1 : δ' ≤ 1 := by
      rw [hδ'eq, div_le_one (by norm_num : (0:ℝ) < 16)]
      nlinarith [hδ0, hδ1]
    have hδ'id : ∀ r : ℝ, (δ')⁻¹ ^ r = (16:ℝ)^r * δ⁻¹^(2*r) := by
      intro r
      rw [hδ'eq]
      exact inv_rpow_sq_div_sixteen δ hδ0 r
    -- ################################################################
    -- step A: the Cauchy--Schwarz lower bound for `∑ ‖X x‖²`
    -- ################################################################
    set X : ℤ → ℂ := AhalfTranspose N P h g with hXeq
    have hX1 : ∀ x : ℤ, ‖X x‖ ≤ 1 := fun x => lipNormAhalfTranspose hN P hh1 hg1 x
    have hXsupp : SupportIn X (N₀ + N) := supportIn_ahalfTranspose (N := N) (P := P) hhs hgs
    have htrans : bilinPair (AhalfZ N P f g) h = bilinPair X f := by
      rw [hXeq]
      exact bilinPair_AhalfZ_eq_transpose (FinSupp.of_supportIn hfs) (FinSupp.of_supportIn hgs)
        (FinSupp.of_supportIn hhs) N P
    have hcorrX : δ * (N:ℝ)^P.natDegree ≤ ‖bilinPair X f‖ := by
      rw [← htrans]; exact hcorr
    set M : ℕ := N₀ + N with hMeq
    set s : Finset ℤ := Finset.Icc (-(M:ℤ)) (M:ℤ) with hseq
    have hXvan : ∀ x : ℤ, x ∉ s → X x = 0 := by
      intro x hx
      apply hXsupp
      have hx2 : ¬ (x ∈ Finset.Icc (-(M:ℤ)) (M:ℤ)) := by rw [← hseq]; exact hx
      rw [mem_Icc_natAbs] at hx2
      omega
    have hfsum2 : (∑ x ∈ s, ‖f x‖ ^ 2) ≤ 5 * (N:ℝ)^P.natDegree := by
      have h1 : (∑ x ∈ s, ‖f x‖ ^ 2) ≤ ∑' x : ℤ, ‖f x‖ ^ 2 :=
        Summable.sum_le_tsum s (fun x _ => by positivity) (summable_norm_sq_of_supportIn hfs)
      have h2 : (∑' x : ℤ, ‖f x‖ ^ 2) ≤ 2*(N₀:ℝ) + 1 :=
        tsum_norm_sq_le_of_supportIn hfs hf1
      have h3 : 2*(N₀:ℝ) + 1 ≤ 5 * (N:ℝ)^P.natDegree := by linarith [hN0hi, hNd1]
      linarith
    have hCS : ‖bilinPair X f‖
        ≤ Real.sqrt (∑ x ∈ s, ‖X x‖ ^ 2) * Real.sqrt (∑ x ∈ s, ‖f x‖ ^ 2) := by
      rw [bilinPair, tsum_eq_sum (s := s) (fun x hx => by rw [hXvan x hx, zero_mul])]
      exact norm_finset_sum_mul_le s X f
    have hQlower : δ^2 * (N:ℝ)^P.natDegree / 5 ≤ ∑ x ∈ s, ‖X x‖ ^ 2 := by
      set Q : ℝ := ∑ x ∈ s, ‖X x‖ ^ 2 with hQeq
      set R : ℝ := ∑ x ∈ s, ‖f x‖ ^ 2 with hReq
      have hQnn : 0 ≤ Q := by positivity
      have hRnn : 0 ≤ R := by positivity
      have h1 : δ * (N:ℝ)^P.natDegree ≤ Real.sqrt Q * Real.sqrt R := hcorrX.trans hCS
      have h2 : (δ * (N:ℝ)^P.natDegree) * (δ * (N:ℝ)^P.natDegree)
          ≤ (Real.sqrt Q * Real.sqrt R) * (Real.sqrt Q * Real.sqrt R) :=
        mul_self_le_mul_self (by positivity) h1
      have h3 : (Real.sqrt Q * Real.sqrt R) * (Real.sqrt Q * Real.sqrt R) = Q * R := by
        rw [show (Real.sqrt Q * Real.sqrt R) * (Real.sqrt Q * Real.sqrt R)
              = (Real.sqrt Q)^2 * (Real.sqrt R)^2 by ring,
          Real.sq_sqrt hQnn, Real.sq_sqrt hRnn]
      have h4 : δ^2 * (N:ℝ)^P.natDegree * (N:ℝ)^P.natDegree
          ≤ Q * (5*(N:ℝ)^P.natDegree) := by
        calc δ^2 * (N:ℝ)^P.natDegree * (N:ℝ)^P.natDegree
            = (δ * (N:ℝ)^P.natDegree) * (δ * (N:ℝ)^P.natDegree) := by ring
          _ ≤ (Real.sqrt Q * Real.sqrt R) * (Real.sqrt Q * Real.sqrt R) := h2
          _ = Q * R := h3
          _ ≤ Q * (5*(N:ℝ)^P.natDegree) :=
              mul_le_mul_of_nonneg_left hfsum2 hQnn
      have hNd2 : (0:ℝ) < (N:ℝ)^P.natDegree * (N:ℝ)^P.natDegree := mul_pos hNdpos hNdpos
      have h5 : δ^2 * (N:ℝ)^P.natDegree ≤ 5 * Q := by
        have h6 : (δ^2 * (N:ℝ)^P.natDegree * (N:ℝ)^P.natDegree)
            * ((N:ℝ)^P.natDegree)⁻¹ = δ^2 * (N:ℝ)^P.natDegree := by field_simp
        have h7 : (Q * (5*(N:ℝ)^P.natDegree)) * ((N:ℝ)^P.natDegree)⁻¹ = 5 * Q := by
          field_simp
        have h8 := mul_le_mul_of_nonneg_right h4 (le_of_lt (inv_pos.mpr hNdpos))
        rwa [h6, h7] at h8
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 5)]
      linarith
    -- ################################################################
    -- step B: the truncation to `[-2N^d, 2N^d]`
    -- ################################################################
    set D : ℕ := 2 * N ^ P.natDegree with hDeq
    have hDcast : (D:ℝ) = 2 * (N:ℝ)^P.natDegree := by rw [hDeq]; push_cast; ring
    set s2 : Finset ℤ := Finset.Icc (-(D:ℤ)) (D:ℤ) with hs2eq
    have hDlt : ∀ x : ℤ, x ∉ s2 → D < x.natAbs := by
      intro x hx
      have hx2 : ¬ (x ∈ Finset.Icc (-(D:ℤ)) (D:ℤ)) := by rw [← hs2eq]; exact hx
      rw [mem_Icc_natAbs] at hx2
      omega
    have hsplit3 : (∑ x ∈ s, ‖X x‖ ^ 2)
        = (∑ x ∈ s ∩ s2, ‖X x‖ ^ 2) + (∑ x ∈ s \ s2, ‖X x‖ ^ 2) := by
      rw [← Finset.sum_inter_add_sum_sdiff]
    have htarget : ∑ x ∈ s ∩ s2, ‖X x‖ ^ 2 ≤ ∑ x ∈ s2, ‖X x‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun x _ _ => by positivity)
    have hN0D : N₀ ≤ D := by
      have h : (N₀:ℝ) ≤ (D:ℝ) := by rw [hDcast]; exact hN0hi
      exact_mod_cast h
    have htailcard : ((s \ s2).card : ℝ) ≤ 2*(N:ℝ) := by
      have h1 := card_Icc_diff_Icc_le M D
      have h1' : (s \ s2).card ≤ 2 * (M - D) := by
        rw [hseq, hs2eq]; exact h1
      have h2 : M - D ≤ N := by rw [hMeq, hDeq]; omega
      calc ((s \ s2).card : ℝ) ≤ ((2 * (M - D) : ℕ) : ℝ) := by exact_mod_cast h1'
        _ ≤ 2*(N:ℝ) := by
            have h3 : (2 * (M - D) : ℕ) ≤ 2 * N := Nat.mul_le_mul_left 2 h2
            exact_mod_cast h3
    have htail : ∑ x ∈ s \ s2, ‖X x‖ ^ 2 ≤ 2*(N:ℝ) := by
      calc ∑ x ∈ s \ s2, ‖X x‖ ^ 2 ≤ ∑ _x ∈ s \ s2, (1:ℝ) :=
            Finset.sum_le_sum fun x _ => by
              have := hX1 x; nlinarith [norm_nonneg (X x)]
        _ = ((s \ s2).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 2*(N:ℝ) := htailcard
    -- the two main-case inequalities
    have hmain1 : 32 * δ⁻¹^(2:ℝ) ≤ (N:ℝ)^(P.natDegree - 1) := by
      have hU : (0:ℝ) < (16:ℝ)^(2*K₁) := Real.rpow_pos_of_pos h16pos (2*K₁)
      have h4 : (32:ℝ) ≤ C₀ := by
        rw [hC₀eq]
        nlinarith [hC₁pos, hU, mul_nonneg hC₁pos.le hU.le]
      have hK₀2 : (2:ℝ) ≤ K₀ := by rw [hK₀eq]; linarith [hK₁pos]
      have hle : δ⁻¹^(2:ℝ) ≤ δ⁻¹^K₀ := Real.rpow_le_rpow_of_exponent_le hδinv1 hK₀2
      have hδ2nn : (0:ℝ) ≤ δ⁻¹^(2:ℝ) := Real.rpow_nonneg hδinvpos.le 2
      have h5 : 32 * δ⁻¹^(2:ℝ) ≤ C₀ * δ⁻¹^K₀ :=
        calc 32 * δ⁻¹^(2:ℝ) ≤ C₀ * δ⁻¹^(2:ℝ) := mul_le_mul_of_nonneg_right h4 hδ2nn
          _ ≤ C₀ * δ⁻¹^K₀ := mul_le_mul_of_nonneg_left hle hC₀pos.le
      linarith [h5, hmain]
    have hmain2 : 4 * C₁ * ((16:ℝ)^(2*K₁) * δ⁻¹^(4*K₁)) ≤ (N:ℝ)^(P.natDegree - 1) := by
      have hU : (0:ℝ) < (16:ℝ)^(2*K₁) := Real.rpow_pos_of_pos h16pos (2*K₁)
      have h4 : 4 * C₁ * (16:ℝ)^(2*K₁) ≤ C₀ := by
        rw [hC₀eq]
        nlinarith [hC₁pos, hU, mul_nonneg hC₁pos.le hU.le]
      have h4K₁ : (4*K₁ : ℝ) ≤ K₀ := by rw [hK₀eq]; linarith
      have hle : δ⁻¹^(4*K₁) ≤ δ⁻¹^K₀ := Real.rpow_le_rpow_of_exponent_le hδinv1 h4K₁
      have hnn : (0:ℝ) ≤ δ⁻¹^(4*K₁) := Real.rpow_nonneg hδinvpos.le _
      have h5 : 4 * C₁ * ((16:ℝ)^(2*K₁) * δ⁻¹^(4*K₁)) ≤ C₀ * δ⁻¹^K₀ :=
        calc 4 * C₁ * ((16:ℝ)^(2*K₁) * δ⁻¹^(4*K₁))
              = (4 * C₁ * (16:ℝ)^(2*K₁)) * δ⁻¹^(4*K₁) := by ring
          _ ≤ C₀ * δ⁻¹^(4*K₁) := mul_le_mul_of_nonneg_right h4 hnn
          _ ≤ C₀ * δ⁻¹^K₀ := mul_le_mul_of_nonneg_left hle hC₀pos.le
      linarith [h5, hmain]
    have hNdecomp : (N:ℝ)^P.natDegree = (N:ℝ) * (N:ℝ)^(P.natDegree - 1) := by
      have hPd : P.natDegree - 1 + 1 = P.natDegree :=
        Nat.sub_add_cancel (le_trans (by norm_num : 1 ≤ 2) hP)
      rw [← pow_succ' (N:ℝ) (P.natDegree - 1), hPd]
    have hδinv2 : δ⁻¹^(2:ℝ) = (δ^2)⁻¹ := by
      rw [Real.inv_rpow hδ0.le (2:ℝ), Real.rpow_ofNat δ 2]
    have htailsmall : 2*(N:ℝ) ≤ δ^2 * (N:ℝ)^P.natDegree / 16 := by
      rw [hNdecomp, le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
      have h1 : 32 * (δ^2)⁻¹ ≤ (N:ℝ)^(P.natDegree - 1) := by
        rw [← hδinv2]; exact hmain1
      have h9 : (N:ℝ) * δ^2 * (32 * (δ^2)⁻¹) ≤ (N:ℝ) * δ^2 * (N:ℝ)^(P.natDegree - 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have hne : δ^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hδ0)
      have h8 : (N:ℝ) * δ^2 * (32 * (δ^2)⁻¹) = 32 * (N:ℝ) := by
        calc (N:ℝ) * δ^2 * (32 * (δ^2)⁻¹) = 32 * ((N:ℝ) * (δ^2 * (δ^2)⁻¹)) := by ring
          _ = 32 * (N:ℝ) := by rw [mul_inv_cancel₀ hne]; ring
      rw [h8] at h9
      linarith [h9]
    have hQ2 : δ^2 * (N:ℝ)^P.natDegree / 8 ≤ ∑ x ∈ s2, ‖X x‖ ^ 2 := by
      have h8 : δ^2 * (N:ℝ)^P.natDegree / 5 - 2*(N:ℝ)
          ≥ δ^2 * (N:ℝ)^P.natDegree / 8 := by linarith [htailsmall]
      linarith [hQlower, hsplit3, htarget, htail, h8]
    -- ################################################################
    -- step C: the input of the refined inverse theorem
    -- ################################################################
    set fin : ℤ → ℂ := fun x => if x.natAbs ≤ D then star (X x) else 0 with hfineq
    have hfin_supp : SupportIn fin D := by
      intro x hx
      rw [hfineq]
      exact if_neg (not_le.mpr hx)
    have hfin1 : ∀ x : ℤ, ‖fin x‖ ≤ 1 := by
      intro x
      change ‖(if x.natAbs ≤ D then star (X x) else 0 : ℂ)‖ ≤ 1
      by_cases hx : x.natAbs ≤ D
      · rw [if_pos hx, norm_star]; exact hX1 x
      · rw [if_neg hx]; simp
    have hstarfin : ∀ x : ℤ, star (fin x) = if x.natAbs ≤ D then X x else 0 := by
      intro x
      change star (if x.natAbs ≤ D then star (X x) else 0) = (if x.natAbs ≤ D then X x else 0)
      by_cases hx : x.natAbs ≤ D
      · rw [if_pos hx, if_pos hx]; simp
      · rw [if_neg hx, if_neg hx]; simp
    have hfinvan : ∀ x : ℤ, x ∉ s2 → fin x = 0 := fun x hx =>
      if_neg (not_le.mpr (hDlt x hx))
    have hpair_fin : bilinPair (AhalfZ N P fin g) h = ∑ x ∈ s2, ((‖X x‖^2 : ℝ) : ℂ) := by
      have h1 : bilinPair (AhalfZ N P fin g) h = bilinPair X fin :=
        bilinPair_AhalfZ_eq_transpose (FinSupp.of_supportIn hfin_supp)
          (FinSupp.of_supportIn hgs) (FinSupp.of_supportIn hhs) N P
      rw [h1, bilinPair, tsum_eq_sum (s := s2) (fun x hx => by rw [hfinvan x hx, mul_zero])]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' : x.natAbs ≤ D := (mem_Icc_natAbs.mp hx)
      have hfinx : fin x = star (X x) := by
        change (if x.natAbs ≤ D then star (X x) else 0) = star (X x)
        exact if_pos hx'
      rw [hfinx, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hpair_norm : ‖bilinPair (AhalfZ N P fin g) h‖ = ∑ x ∈ s2, ‖X x‖ ^ 2 := by
      rw [hpair_fin]
      have h1 : (∑ x ∈ s2, ((‖X x‖ ^ 2 : ℝ) : ℂ))
          = (((∑ x ∈ s2, ‖X x‖ ^ 2) : ℝ) : ℂ) := by push_cast; rfl
      rw [h1]
      have hnn : (0:ℝ) ≤ ∑ x ∈ s2, ‖X x‖ ^ 2 := Finset.sum_nonneg fun x _ => by positivity
      exact RCLike.norm_of_nonneg hnn
    -- ################################################################
    -- step D: apply the refined inverse theorem
    -- ################################################################

    have hgD : SupportIn g D := hgs.mono hN0D
    have hhD : SupportIn h D := hhs.mono hN0D
    have hDlo : (N:ℝ)^P.natDegree / 2 ≤ (D:ℝ) := by rw [hDcast]; linarith [hNdpos]
    have hDhi : (D:ℝ) ≤ 2 * (N:ℝ)^P.natDegree := by rw [hDcast]
    have hcorr2 : δ' * (N:ℝ)^P.natDegree ≤ ‖bilinPair (AhalfZ N P fin g) h‖ := by
      rw [hpair_norm]
      have hδ'e : δ' * (N:ℝ)^P.natDegree = δ^2 * (N:ℝ)^P.natDegree / 16 := by
        rw [hδ'eq]; ring
      rw [hδ'e]
      linarith [hQ2]
    obtain ⟨F, k, A, hF1, hFsum, hFl1, hFsupp, hAcard, hFk, hFcorr⟩ :=
      hlip ρ hρ hρ1 N D δ' fin g h hN (by rw [hδ'eq]; positivity) hδ'1
        hDlo hDhi hfin_supp hgD hhD hfin1 hg1 hh1 hcorr2
    -- ################################################################
    -- step E: conjugation, the comparison, and the rescaling
    -- ################################################################
    set T : ℝ := (δ')⁻¹ ^ K₁ with hTeq
    have hTpos : 0 < T := by rw [hTeq]; exact Real.rpow_pos_of_pos (inv_pos.mpr hδ'pos) K₁
    have hTid : T = (16:ℝ)^K₁ * δ⁻¹^(2*K₁) := by rw [hTeq]; exact hδ'id K₁
    have h16K1pos : (0:ℝ) < (16:ℝ)^K₁ := Real.rpow_pos_of_pos h16pos K₁
    have hu16 : (16:ℝ)^K₁ * (16:ℝ)^K₁ = (16:ℝ)^(2*K₁) := by
      rw [← Real.rpow_add h16pos K₁ K₁]; congr 1; ring
    have hdd : δ⁻¹^(2*K₁) * δ⁻¹^(2*K₁) = δ⁻¹^(4*K₁) := by
      rw [← Real.rpow_add hδinvpos (2*K₁) (2*K₁)]; congr 1; ring
    have hTT : T * T = (16:ℝ)^(2*K₁) * δ⁻¹^(4*K₁) := by
      rw [hTid,
        show ((16:ℝ)^K₁ * δ⁻¹^(2*K₁)) * ((16:ℝ)^K₁ * δ⁻¹^(2*K₁))
          = ((16:ℝ)^K₁ * (16:ℝ)^K₁) * (δ⁻¹^(2*K₁) * δ⁻¹^(2*K₁)) by ring,
        hu16, hdd]
    have hmain2' : 4 * C₁ * (T * T) ≤ (N:ℝ)^(P.natDegree - 1) := by
      rw [hTT]; exact hmain2
    have hTinv : δ' ^ K₁ = T⁻¹ := by
      rw [hTeq, Real.inv_rpow hδ'pos.le K₁]
      exact (inv_inv _).symm
    -- the symmetrised arc set
    set A' : Finset FreqCircle := A ∪ A.image (fun α => -α) with hA'eq
    have hA'card : (A'.card : ℝ) ≤ 2 * (C₁ * T) := by
      have h1 : A'.card ≤ 2 * A.card := by
        rw [hA'eq]
        calc (A ∪ A.image (fun α : FreqCircle => -α)).card
            ≤ A.card + (A.image (fun α : FreqCircle => -α)).card := Finset.card_union_le _ _
          _ ≤ A.card + A.card := Nat.add_le_add_left Finset.card_image_le _
          _ = 2 * A.card := by ring
      have h2 : ((2 * A.card : ℕ) : ℝ) ≤ 2 * (C₁ * T) := by
        push_cast; linarith [hAcard]
      calc (A'.card : ℝ) ≤ ((2 * A.card : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ 2 * (C₁ * T) := h2
    have hA'mono : (⋃ α ∈ (A : Set FreqCircle), arcSet α ((2:ℝ)^k))
        ⊆ (⋃ α ∈ (A' : Set FreqCircle), arcSet α ((2:ℝ)^k)) := by
      intro ξ hξ
      obtain ⟨α, hα, harc⟩ := Set.mem_iUnion₂.mp hξ
      refine Set.mem_biUnion ?_ harc
      rw [hA'eq, Finset.mem_coe]
      exact Finset.mem_union_left _ (Finset.mem_coe.mp hα)
    have hA'sym : ∀ α ∈ A', -α ∈ A' := by
      intro α hα
      rw [hA'eq] at hα ⊢
      rcases (Finset.mem_union.mp hα) with hα | hα
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨α, hα, rfl⟩)
      · obtain ⟨β, hβ, hβα⟩ := Finset.mem_image.mp hα
        rw [← hβα, neg_neg]
        exact Finset.mem_union_left _ hβ
    have hFsupp' : FourierSupportIn (fun x => star (F x))
        (⋃ α ∈ (A' : Set FreqCircle), arcSet α ((2:ℝ)^k)) :=
      FourierSupportIn_star hFsum (FourierSupportIn.mono hA'mono hFsupp)
        (fun ξ hξ h2 => hξ (by
          have h3 := neg_mem_arcSet_union hA'sym h2
          rwa [neg_neg] at h3))
    have hF1T : ∀ x : ℤ, ‖F x‖ ≤ C₁ * T := fun x => hF1 x
    have hC₁Tnn : 0 ≤ C₁ * T := mul_nonneg hC₁pos.le hTpos.le
    -- the summable families
    have hsumA : Summable (fun x : ℤ => X x * star (F x)) :=
      Summable.of_norm_bounded hFsum fun x => by
        rw [norm_mul, norm_star]
        exact mul_le_of_le_one_left (norm_nonneg _) (hX1 x)
    have hsumB : Summable (fun x : ℤ => star (fin x) * star (F x)) :=
      Summable.of_norm_bounded hFsum fun x => by
        rw [norm_mul, norm_star, norm_star]
        exact mul_le_of_le_one_left (norm_nonneg _) (hfin1 x)
    have hstarB : star (bilinPair fin F) = ∑' x : ℤ, star (fin x) * star (F x) := by
      rw [bilinPair, tsum_star]
      exact tsum_congr fun x => star_mul' (fin x) (F x)
    have hzeroterm : ∀ x : ℤ, x ∉ s \ s2 →
        X x * star (F x) - star (fin x) * star (F x) = 0 := by
      intro x hx
      by_cases hxs : x ∈ s
      · have hx2 : x ∈ s2 := by
          by_contra hx2
          exact hx (Finset.mem_sdiff.mpr ⟨hxs, hx2⟩)
        have hz : star (fin x) = X x := by
          rw [hstarfin, if_pos (mem_Icc_natAbs.mp hx2)]
        rw [hz, sub_self]
      · have hz1 : X x = 0 := hXvan x hxs
        have hz2 : fin x = 0 := by
          change (if x.natAbs ≤ D then star (X x) else 0) = 0
          by_cases hh : x.natAbs ≤ D
          · rw [if_pos hh]; simp [hz1]
          · exact if_neg hh
        rw [hz1, hz2, star_zero, zero_mul, sub_zero]
    have hdiff : bilinPair X (fun x => star (F x)) - star (bilinPair fin F)
        = ∑ x ∈ s \ s2, X x * star (F x) := by
      rw [hstarB, bilinPair, ← hsumA.tsum_sub hsumB,
        tsum_eq_sum (s := s \ s2) hzeroterm]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxn : x ∉ s2 := (Finset.mem_sdiff.mp hx).2
      have hz : star (fin x) = 0 := by
        rw [hstarfin]
        exact if_neg (not_le.mpr (hDlt x hxn))
      rw [hz, zero_mul, sub_zero]
    have htailbound : ‖∑ x ∈ s \ s2, X x * star (F x)‖ ≤ C₁ * T * (2*(N:ℝ)) := by
      calc ‖∑ x ∈ s \ s2, X x * star (F x)‖ ≤ ∑ x ∈ s \ s2, ‖X x * star (F x)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _x ∈ s \ s2, (C₁ * T) := Finset.sum_le_sum fun x _ => by
              have h1 : ‖X x‖ * ‖F x‖ ≤ 1 * (C₁ * T) :=
                mul_le_mul (hX1 x) (hF1T x) (norm_nonneg _) (by norm_num)
              simpa using h1
        _ = ((s \ s2).card : ℝ) * (C₁ * T) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2*(N:ℝ)) * (C₁ * T) := mul_le_mul_of_nonneg_right htailcard hC₁Tnn
        _ = C₁ * T * (2*(N:ℝ)) := by ring
    have hcorrstar : δ' ^ K₁ * (N:ℝ)^P.natDegree / 2
        ≤ ‖bilinPair X (fun x => star (F x))‖ := by
      have htailsmall' : C₁ * T * (2*(N:ℝ)) ≤ δ' ^ K₁ * (N:ℝ)^P.natDegree / 2 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), hTinv]
        have hcross : (C₁ * T * (2*(N:ℝ))) * 2 * T ≤ (N:ℝ)^P.natDegree := by
          rw [hNdecomp]
          have hNnn : (0:ℝ) ≤ (N:ℝ) := by linarith
          have hm : (4 * C₁ * (T*T)) * (N:ℝ) ≤ (N:ℝ)^(P.natDegree - 1) * (N:ℝ) :=
            mul_le_mul_of_nonneg_right hmain2' hNnn
          calc (C₁ * T * (2*(N:ℝ))) * 2 * T = (4 * C₁ * (T*T)) * (N:ℝ) := by ring
            _ ≤ (N:ℝ)^(P.natDegree - 1) * (N:ℝ) := hm
            _ = (N:ℝ) * (N:ℝ)^(P.natDegree - 1) := by ring
        calc (C₁ * T * (2*(N:ℝ))) * 2
            ≤ (N:ℝ)^P.natDegree / T := by rw [le_div_iff₀ hTpos]; exact hcross
          _ = T⁻¹ * (N:ℝ)^P.natDegree := by rw [div_eq_mul_inv]; ring
      have h1 : ‖bilinPair X (fun x => star (F x))‖
          ≥ δ' ^ K₁ * (N:ℝ)^P.natDegree - C₁ * T * (2*(N:ℝ)) := by
        have h2 : bilinPair X (fun x => star (F x))
            = star (bilinPair fin F) + ∑ x ∈ s \ s2, X x * star (F x) := by
          rw [add_comm]
          exact eq_add_of_sub_eq hdiff
        rw [h2]
        have h4 := norm_sub_norm_le (star (bilinPair fin F))
          (-(∑ x ∈ s \ s2, X x * star (F x)))
        rw [norm_star, norm_neg, sub_neg_eq_add] at h4
        linarith [h4, hFcorr, htailbound]
      linarith [h1, htailsmall']
    set lam : ℝ := C * δ⁻¹^K / (1 + C₁ * T) with hlameq
    have hlampos : 0 < lam := by rw [hlameq]; positivity
    have hlamden : 0 < 1 + C₁ * T := by positivity
    have huv : (16:ℝ)^K₁ ≤ (16:ℝ)^(2*K₁) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 16) (by linarith [hK₁pos])
    have hC₁T_le : C₁ * T ≤ C * δ⁻¹^K := by
      rw [hTid, hKeq]
      have hC1u : C₁ * (16:ℝ)^K₁ ≤ C := by
        rw [hCeq]
        have hU : (0:ℝ) ≤ (16:ℝ)^(2*K₁) := (Real.rpow_pos_of_pos h16pos (2*K₁)).le
        have hm : 0 ≤ C₁ * (16:ℝ)^(2*K₁) := mul_nonneg hC₁pos.le hU
        have hm2 : C₁ * (16:ℝ)^K₁ ≤ C₁ * (16:ℝ)^(2*K₁) :=
          mul_le_mul_of_nonneg_left huv hC₁pos.le
        nlinarith [hm, hm2, Real.rpow_pos_of_pos h16pos (2*K₁)]
      have hstep : (C₁ * (16:ℝ)^K₁) * δ⁻¹^(2*K₁) ≤ C * δ⁻¹^(2*K₁) :=
        mul_le_mul_of_nonneg_right hC1u (Real.rpow_nonneg hδinvpos.le _)
      calc C₁ * ((16:ℝ)^K₁ * δ⁻¹^(2*K₁)) = (C₁ * (16:ℝ)^K₁) * δ⁻¹^(2*K₁) := by ring
        _ ≤ C * δ⁻¹^(2*K₁) := hstep
    have h2C₁T_le : 2 * (C₁ * T) ≤ C * δ⁻¹^K := by
      rw [hTid, hKeq]
      have hU : (0:ℝ) < (16:ℝ)^(2*K₁) := Real.rpow_pos_of_pos h16pos (2*K₁)
      have hC1 : 2 * C₁ * (16:ℝ)^K₁ ≤ 2 * C₁ * (16:ℝ)^(2*K₁) :=
        mul_le_mul_of_nonneg_left huv (by positivity)
      have hC2 : 2 * C₁ * (16:ℝ)^(2*K₁) ≤ C := by
        rw [hCeq]
        have h4 : (0:ℝ) ≤ C₁ * (16:ℝ)^(2*K₁) := mul_nonneg hC₁pos.le hU.le
        have h3 : 2 * C₁ * (16:ℝ)^(2*K₁) ≤ 8 * C₁ * (16:ℝ)^(2*K₁) := by
          linarith only [h4]
        have h5 : 8 * C₁ * (16:ℝ)^(2*K₁)
            ≤ 8 * (1 + C₁) * (16:ℝ)^(2*K₁) + 8 := by
          have h6 : (0:ℝ) ≤ 8 * (16:ℝ)^(2*K₁) := by linarith only [hU]
          linarith only [h6]
        linarith only [h3, h5]
      have hstep : (2 * C₁ * (16:ℝ)^(2*K₁)) * δ⁻¹^(2*K₁) ≤ C * δ⁻¹^(2*K₁) :=
        mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hδinvpos.le _)
      calc 2 * (C₁ * ((16:ℝ)^K₁ * δ⁻¹^(2*K₁)))
            = (2 * C₁ * (16:ℝ)^K₁) * δ⁻¹^(2*K₁) := by ring
        _ ≤ (2 * C₁ * (16:ℝ)^(2*K₁)) * δ⁻¹^(2*K₁) :=
            mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg hδinvpos.le _)
        _ ≤ C * δ⁻¹^(2*K₁) := hstep
    have hlamC₁T : lam * (C₁ * T) ≤ C * δ⁻¹^K := by
      have h : lam * (C₁ * T) = C * δ⁻¹^K * (C₁ * T) / (1 + C₁ * T) := by
        rw [hlameq]; ring
      rw [h, div_le_iff₀ hlamden]
      exact mul_le_mul_of_nonneg_left (by linarith [hC₁Tnn])
        (mul_nonneg hCpos.le (Real.rpow_nonneg hδinvpos.le K))
    have hrescale : δ^K ≤ lam * δ'^K₁ / 2 := by
      have hid2 : δ⁻¹^K * δ'^K₁ = (16:ℝ)^(-K₁) := by
        rw [hKeq, hδ'eq, pow_two]
        exact rpow_smoothing_mul δ hδ0 K₁
      have hid3 : C * δ⁻¹^K * δ'^K₁ = C * (16:ℝ)^(-K₁) := by
        rw [mul_assoc, hid2]
      have hδK1 : δ^K ≤ 1 := Real.rpow_le_one hδ0.le hδ1 hKpos.le
      have hidT : δ^K * (16:ℝ)^K₁ * T = (16:ℝ)^(2*K₁) := by
        rw [hKeq, hTid]
        have hδs : δ^(2*K₁) * δ⁻¹^(2*K₁) = 1 := by
          rw [Real.inv_rpow hδ0.le (2*K₁)]
          exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hδ0 (2*K₁)))
        calc δ^(2*K₁) * (16:ℝ)^K₁ * ((16:ℝ)^K₁ * δ⁻¹^(2*K₁))
            = ((16:ℝ)^K₁ * (16:ℝ)^K₁) * (δ^(2*K₁) * δ⁻¹^(2*K₁)) := by ring
          _ = (16:ℝ)^(2*K₁) := by rw [hu16, hδs, mul_one]
      have hCbig : 2 * (16:ℝ)^K₁ + 2 * C₁ * (16:ℝ)^(2*K₁) ≤ C := by
        rw [hCeq]
        have hU : (0:ℝ) < (16:ℝ)^(2*K₁) := Real.rpow_pos_of_pos h16pos (2*K₁)
        have h1 : 2 * (16:ℝ)^K₁ ≤ 2 * (16:ℝ)^(2*K₁) :=
          mul_le_mul_of_nonneg_left huv (by norm_num)
        have h2 : 2 * C₁ * (16:ℝ)^(2*K₁) ≤ 8 * C₁ * (16:ℝ)^(2*K₁) := by
          have h4 : (0:ℝ) ≤ C₁ * (16:ℝ)^(2*K₁) := mul_nonneg hC₁pos.le hU.le
          linarith only [h4]
        have h3 : 2 * (16:ℝ)^(2*K₁) + 8 * C₁ * (16:ℝ)^(2*K₁)
            ≤ 8 * (1 + C₁) * (16:ℝ)^(2*K₁) + 8 := by
          have h5 : (0:ℝ) ≤ 6 * (16:ℝ)^(2*K₁) := by linarith only [hU]
          linarith only [h5]
        linarith only [h1, h2, h3]
      have hkey2 : δ^K * 2 * (1 + C₁ * T) * (16:ℝ)^K₁ ≤ C := by
        have hsplit : δ^K * 2 * (1 + C₁ * T) * (16:ℝ)^K₁
            = 2 * (δ^K * (16:ℝ)^K₁) + 2 * C₁ * (δ^K * (16:ℝ)^K₁ * T) := by ring
        rw [hsplit, hidT]
        have hle : δ^K * (16:ℝ)^K₁ ≤ (16:ℝ)^K₁ := by
          simpa using mul_le_mul_of_nonneg_right hδK1
            (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 16) K₁)
        linarith [hCbig, hle]
      have hkey : δ^K * 2 * (1 + C₁ * T) ≤ C * (16:ℝ)^(-K₁) := by
        rw [show C * (16:ℝ)^(-K₁) = C / (16:ℝ)^K₁ by
              rw [div_eq_mul_inv, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 16)],
            le_div_iff₀ (Real.rpow_pos_of_pos h16pos K₁)]
        exact hkey2
      rw [hlameq, le_div_iff₀ (by norm_num : (0:ℝ) < 2), div_mul_eq_mul_div,
        le_div_iff₀ (by positivity : (0:ℝ) < 1 + C₁ * T), hid3]
      exact hkey
    have hnormlam : ‖((lam : ℝ) : ℂ)‖ = lam := by
      have h1 : ‖((lam : ℝ) : ℂ)‖ = |lam| := by simp
      rw [h1, abs_of_nonneg hlampos.le]
    refine ⟨k, A', fun x => lam * star (F x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [norm_mul, norm_star, hnormlam]
      have h1 : lam * ‖F x‖ ≤ lam * (C₁ * T) := mul_le_mul_of_nonneg_left (hF1T x) hlampos.le
      linarith [h1, hlamC₁T]
    · have : (fun x : ℤ => ‖lam * star (F x)‖) = fun x => lam * ‖F x‖ := by
        funext x; rw [norm_mul, norm_star, hnormlam]
      rw [this]
      exact hFsum.mul_left lam
    · have hpt : ∀ x : ℤ, ‖lam * star (F x)‖ = lam * ‖F x‖ :=
        fun x => by rw [norm_mul, norm_star, hnormlam]
      rw [tsum_congr hpt, tsum_mul_left]
      calc lam * (∑' x : ℤ, ‖F x‖) ≤ lam * (C₁ * T * (N:ℝ)^P.natDegree) :=
            mul_le_mul_of_nonneg_left hFl1 hlampos.le
        _ = (lam * (C₁ * T)) * (N:ℝ)^P.natDegree := by ring
        _ ≤ C * δ⁻¹^K * (N:ℝ)^P.natDegree :=
            mul_le_mul_of_nonneg_right hlamC₁T (le_of_lt hNdpos)
    · refine FourierSupportIn_const_mul (F := fun x => star (F x)) ?_ lam hFsupp'
      simpa using hFsum
    · exact le_trans hA'card h2C₁T_le
    · calc (2:ℝ)^k ≤ C₁ * T / (N:ℝ) := hFk
        _ ≤ (C * δ⁻¹^K) / (N:ℝ) := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hC₁T_le (by positivity)
    · have hbilin : bilinPair X (fun x => lam * star (F x))
          = lam * bilinPair X (fun x => star (F x)) := by
        rw [bilinPair, bilinPair, ← tsum_mul_left]
        refine tsum_congr fun x => by ring
      rw [hbilin]
      calc δ^K * (N:ℝ)^P.natDegree
          ≤ (lam * δ'^K₁ / 2) * (N:ℝ)^P.natDegree :=
            mul_le_mul_of_nonneg_right hrescale (le_of_lt hNdpos)
        _ = lam * (δ'^K₁ * (N:ℝ)^P.natDegree / 2) := by ring
        _ ≤ lam * ‖bilinPair X (fun x => star (F x))‖ :=
            mul_le_mul_of_nonneg_left hcorrstar hlampos.le
        _ = ‖(lam : ℂ) * bilinPair X (fun x => star (F x))‖ := by
            rw [norm_mul, hnormlam]
