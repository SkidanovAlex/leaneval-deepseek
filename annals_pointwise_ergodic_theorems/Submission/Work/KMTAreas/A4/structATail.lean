/-
# Corollary `struct` with a free support window `A N^d`

Krause--Mirek--Tao, §5, Corollary `struct`, in the *window-parameterised* form needed by the
second half of Theorem `improv`: under Proposition `lip` with a free support window `A N^d`
(`A4/LipOutputTailA`), the dual function `A*_N(h,g)` of the halved bilinear average decomposes as

`A*_N(h,g) = sum_i w_i . lam_i . phi_i + E1 + E2`,

with each `phi_i` in the family `structPhi` (pointwise `<< delta^{-O(1)}`, `l^1`-norm
`<< delta^{-O(1)} N^d`, Fourier support in a major arc of scales `2^l << delta^{-O(1)}`,
`2^k << delta^{-O(1)}/N`), non-negative weights with `sum w_i <= 1`, coefficients bounded by
`4 delta^{1-K}`, `‖E1‖_{l^1} <= delta N^d` and `‖E2‖_{l^2} <= delta`.

This is `A4/StructCor.lean`'s `structDecomp_of_lip` with the pinned window `2 N^d` replaced by the
free parameter: the hypothesis is `LipOutputTailA P rho (A + 1) C K` (input supported in
`[-A' N^d, A' N^d]`, tail measured outside `A' N^d`, with `A' = A + 1`) and the input data `g, h`
are supported in `[-N0, N0]` with `N^d / 2 <= N0 <= A N^d`.

The proof is the pinned one with the Hahn--Banach test function truncated to the window
`B = (A+1) N^d` (the tail window of `LipOutputTailA`) instead of `2 N^d`: the truncation radius is
`Nat.floor B` -- large enough to contain `supp A*_N(h,g) + supp h` up to `N0 + N`, small enough
to satisfy the support hypothesis of `lip`, and its truncation error is supported exactly where
the tail clause of `LipOutputTailA` lives.

## Main results

* `Work.KMTAreas.A4.lipInputW` and the lemmas about it -- the truncated test function;
* `Work.KMTAreas.A4.structHahnHypA` -- the Hahn--Banach hypothesis of Corollary `struct`, windowed;
* `Work.KMTAreas.A4.structATail` -- Corollary `struct` from `LipOutputTailA`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.LipOutputTailA

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger (L2Z)
open Work.Analysis.InverseTheory

/-! ## The Hahn--Banach test function truncated to a free window -/

/-- The test function fed to Proposition `lip` in the proof of Corollary `struct`: the conjugate
of `f`, truncated to the window `[-B, B]`.  Unlike `Struct.lipInput` (pinned to `2 N^d`), the
radius `B` is an arbitrary real, so that the truncation error lives exactly where the tail clause
of `LipOutputTailA` is measured. -/
def lipInputW (P : Polynomial ℤ) (B : ℝ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x : ℤ => if (x.natAbs : ℝ) ≤ B then star (f x) else 0

/-- `lipInputW` is supported in `[-floor B, floor B]`. -/
theorem supportIn_lipInputW (P : Polynomial ℤ) (B : ℝ) (f : ℤ → ℂ) :
    SupportIn (lipInputW P B f) (Nat.floor B) := by
  intro x hx
  simp only [lipInputW]
  refine if_neg ?_
  intro hcon
  have hcast : ((Nat.floor B : ℕ) : ℝ) + 1 ≤ (x.natAbs : ℝ) := by
    have h : Nat.floor B + 1 ≤ x.natAbs := Nat.succ_le_of_lt hx
    exact_mod_cast h
  have hlt : B < ((Nat.floor B : ℕ) : ℝ) + 1 := by simpa using Nat.lt_floor_add_one B
  linarith

theorem norm_lipInputW_le_one (P : Polynomial ℤ) (B : ℝ) {f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) : ∀ x : ℤ, ‖lipInputW P B f x‖ ≤ 1 := by
  intro x
  simp only [lipInputW]
  split
  · rw [norm_star]; exact hf x
  · simp

theorem lipInputW_eq_star {P : Polynomial ℤ} {B : ℝ} {f : ℤ → ℂ} {x : ℤ}
    (hx : (x.natAbs : ℝ) ≤ B) : lipInputW P B f x = star (f x) := by
  simp only [lipInputW]
  exact if_pos hx

theorem lipInputW_eq_zero {P : Polynomial ℤ} {B : ℝ} {f : ℤ → ℂ} {x : ℤ}
    (hx : B < (x.natAbs : ℝ)) : lipInputW P B f x = 0 := by
  simp only [lipInputW]
  exact if_neg (by linarith)

/-- The trilinear form of the truncated conjugate is the inner product with the dual function:
the identity on which the Hahn--Banach hypothesis of Corollary `struct` rests.  It needs the
truncation radius `floor B` to contain the support `[-N0 - N, N0 + N]` of `A*_N(h,g)`. -/
theorem bilinPair_lipInputW_eq_inner {P : Polynomial ℤ} {N N₀ : ℕ}
    {B : ℝ} (hB0 : 0 ≤ B) (hN0 : N₀ + N ≤ Nat.floor B) {g h : ℤ → ℂ} {f : L2Z}
    (hgs : SupportIn g N₀) (hhs : SupportIn h N₀) :
    bilinPair (AhalfZ N P (lipInputW P B (fun x : ℤ => f x)) g) h
      = inner ℂ f (ahalfStarL2 N P h g N₀ hhs hgs) := by
  rw [bilinPair_AhalfZ_eq_transpose (FinSupp.of_supportIn (supportIn_lipInputW P B _))
    (FinSupp.of_supportIn hgs) (FinSupp.of_supportIn hhs) N P]
  simp only [bilinPair, lp.inner_eq_tsum]
  refine tsum_congr fun x => ?_
  by_cases hx : (x.natAbs : ℝ) ≤ B
  · rw [lipInputW_eq_star hx, ahalfStarL2_apply, RCLike.inner_apply]
    simp only [starRingEnd_apply]
  · have hxB : B < (x.natAbs : ℝ) := lt_of_not_ge hx
    have hlt : Nat.floor B < x.natAbs := (Nat.floor_lt hB0).mpr hxB
    rw [lipInputW_eq_zero hxB, ahalfStarL2_apply, RCLike.inner_apply,
      supportIn_ahalfTranspose (N := N) (P := P) hhs hgs x (by omega)]
    simp

/-- The tail estimate: pairing `F` against the difference between `star o f` and its truncation
costs at most the mass of `F` outside the window `[-B, B]`. -/
theorem norm_tsum_mul_sub_lipInputW_le {P : Polynomial ℤ} {B : ℝ} {F f : ℤ → ℂ}
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hFsum : Summable fun x : ℤ => ‖F x‖) :
    ‖∑' x : ℤ, F x * (star (f x) - lipInputW P B f x)‖
      ≤ ∑' x : ℤ, (if B < (x.natAbs : ℝ) then ‖F x‖ else 0) := by
  have hbound : ∀ x : ℤ, ‖F x * (star (f x) - lipInputW P B f x)‖
      ≤ if B < (x.natAbs : ℝ) then ‖F x‖ else 0 := by
    intro x
    by_cases hx : (x.natAbs : ℝ) ≤ B
    · rw [lipInputW_eq_star hx, sub_self, mul_zero, norm_zero]
      split <;> simp
    · rw [lipInputW_eq_zero (lt_of_not_ge hx), sub_zero, norm_mul, norm_star,
        if_pos (lt_of_not_ge hx)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hf x)
  have hsum2 : Summable fun x : ℤ => (if B < (x.natAbs : ℝ) then ‖F x‖ else 0) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) hFsum
    split
    · exact le_rfl
    · exact norm_nonneg _
  have hsum1 : Summable fun x : ℤ => ‖F x * (star (f x) - lipInputW P B f x)‖ :=
    Summable.of_nonneg_of_le (fun x => by positivity) hbound hsum2
  calc ‖∑' x : ℤ, F x * (star (f x) - lipInputW P B f x)‖
      ≤ ∑' x : ℤ, ‖F x * (star (f x) - lipInputW P B f x)‖ := norm_tsum_le_tsum_norm hsum1
    _ ≤ ∑' x : ℤ, (if B < (x.natAbs : ℝ) then ‖F x‖ else 0) :=
        hsum1.tsum_le_tsum hbound hsum2

/-! ## The Hahn--Banach hypothesis of Corollary `struct`, windowed -/

/-- **The Hahn--Banach hypothesis of Corollary `struct`** in the window-parameterised form: under
`LipOutputTailA P rho (A+1) C K` (input supported in `(A+1) N^d`, tail measured outside
`(A+1) N^d`) and `g, h` supported in `N0` with `N^d/2 <= N0 <= A N^d`, every `1`-bounded `f` whose
pairing with the dual function `A*_N(h,g)` exceeds `delta N^d` correlates with an element of
`structPhi P rho C K delta N` beyond `delta^K N^d/4`.

The truncation radius is `floor ((A+1) N^d)`, which lies between `N0 + N` (the support of the dual
function) and `(A+1) N^d` (the support window of `lip`); the truncation error is therefore
invisible to the pairing with `F` outside the tail window of `LipOutputTailA`. -/
theorem structHahnHypA {P : Polynomial ℤ} (hP : 2 ≤ P.natDegree) {ρ C K A : ℝ} (hA : 1 ≤ A)
    (hC : 0 < C) (hK : 0 < K) (hLip : LipOutputTailA P ρ (A + 1) C K) {N N₀ : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hN0lo : (N : ℝ) ^ P.natDegree / 2 ≤ (N₀ : ℝ))
    (hN0hi : (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree) {g h : ℤ → ℂ}
    (hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1) (hh1 : ∀ x : ℤ, ‖h x‖ ≤ 1)
    (hgs : SupportIn g N₀) (hhs : SupportIn h N₀) :
    ∀ f : L2Z, (∀ x : ℤ, ‖f x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree < ‖inner ℂ f (ahalfStarL2 N P h g N₀ hhs hgs)‖ →
      ∃ φ ∈ structPhi P ρ C K δ N,
        δ ^ K * (N : ℝ) ^ P.natDegree / 4 < ‖inner ℂ f φ‖ := by
  intro f hf1 hfbig
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hP
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNNd : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ hN1 hd1
  -- the free window `B = (A+1) N^d` and its integral part
  set B : ℝ := (A + 1) * (N : ℝ) ^ P.natDegree with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hN0leM : N₀ ≤ Nat.floor B := by
    apply Nat.le_floor
    rw [hBdef]
    calc (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := hN0hi
      _ ≤ (A + 1) * (N : ℝ) ^ P.natDegree := by nlinarith [hNdpos]
  have hN0NleM : N₀ + N ≤ Nat.floor B := by
    apply Nat.le_floor
    rw [hBdef, Nat.cast_add]
    calc (N₀ : ℝ) + (N : ℝ) ≤ A * (N : ℝ) ^ P.natDegree + (N : ℝ) ^ P.natDegree :=
          add_le_add hN0hi hNNd
      _ = (A + 1) * (N : ℝ) ^ P.natDegree := by ring
  have hMlo : (N : ℝ) ^ P.natDegree / (A + 1) ≤ ((Nat.floor B : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < A + 1)]
    have hN0leR : (N₀ : ℝ) ≤ ((Nat.floor B : ℕ) : ℝ) := by exact_mod_cast hN0leM
    nlinarith [hN0lo, hN0leR, hA, hNdpos]
  have hMhi : ((Nat.floor B : ℕ) : ℝ) ≤ (A + 1) * (N : ℝ) ^ P.natDegree := by
    rw [← hBdef]; exact Nat.floor_le hBpos.le
  -- the correlation hypothesis for `lip`
  have hkey : δ * (N : ℝ) ^ P.natDegree
      ≤ ‖bilinPair (AhalfZ N P (lipInputW P B (fun x : ℤ => f x)) g) h‖ := by
    rw [bilinPair_lipInputW_eq_inner hBpos.le hN0NleM hgs hhs]
    exact le_of_lt hfbig
  obtain ⟨F, l, k, hF1, hFsum, hFl1, hFtail, hFsupp, hFl, hFk, hFcorr⟩ :=
    hLip N (Nat.floor B) δ (lipInputW P B (fun x : ℤ => f x)) g h hN hδ0 hδ1
      hMlo hMhi (supportIn_lipInputW P B _) (hgs.mono hN0leM) (hhs.mono hN0leM)
      (norm_lipInputW_le_one P B hf1) hg1 hh1 hkey
  have hB0 : (0 : ℝ) ≤ C * δ⁻¹ ^ K :=
    le_of_lt (mul_pos hC (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) K))
  set φ : L2Z := ⟨F, memℓp_of_l1 hB0 hFsum hF1⟩ with hφ
  have hφapply : ∀ x : ℤ, φ x = F x := fun x => rfl
  have hδK : 0 < δ ^ K * (N : ℝ) ^ P.natDegree :=
    mul_pos (Real.rpow_pos_of_pos hδ0 K) (pow_pos hNpos _)
  refine ⟨φ, ?_, ?_⟩
  · refine ⟨fun x => ?_, ?_, ?_, ⟨l, k, ?_, hFl, hFk⟩⟩
    · rw [hφapply]; exact hF1 x
    · simpa only [hφapply] using hFsum
    · simpa only [hφapply] using hFl1
    · simpa only [hφapply] using hFsupp
  · -- the correlation
    set S : ℤ → ℂ := fun x => star (f x) - lipInputW P B (fun x : ℤ => f x) x with hS
    have hbS : ∀ x : ℤ, ‖S x‖ ≤ 2 := by
      intro x
      rw [hS]
      calc ‖star (f x) - lipInputW P B (fun x : ℤ => f x) x‖
          ≤ ‖star (f x)‖ + ‖lipInputW P B (fun x : ℤ => f x) x‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            rw [norm_star]
            exact add_le_add (hf1 x) (norm_lipInputW_le_one P B hf1 x)
        _ = 2 := by norm_num
    have hsumS : Summable fun x : ℤ => F x * S x := by
      refine Summable.of_norm ?_
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hFsum.mul_left 2)
      rw [norm_mul]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right (hbS x) (norm_nonneg (F x))
    have hsumA : Summable fun x : ℤ => F x * lipInputW P B (fun x : ℤ => f x) x := by
      refine Summable.of_norm ?_
      refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hFsum.mul_left 1)
      rw [norm_mul]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_right (norm_lipInputW_le_one P B hf1 x) (norm_nonneg (F x))
    have hinner : inner ℂ f φ = ∑' x : ℤ, F x * star (f x) := by
      rw [lp.inner_eq_tsum]
      refine tsum_congr fun x => ?_
      rw [RCLike.inner_apply, starRingEnd_apply, hφapply]
    have hpair : bilinPair (lipInputW P B (fun x : ℤ => f x)) F
        = ∑' x : ℤ, F x * lipInputW P B (fun x : ℤ => f x) x := by
      simp only [bilinPair]
      exact tsum_congr fun x => mul_comm _ _
    have hsplit : (∑' x : ℤ, F x * star (f x))
        = bilinPair (lipInputW P B (fun x : ℤ => f x)) F + ∑' x : ℤ, F x * S x := by
      rw [hpair, ← hsumA.tsum_add hsumS]
      refine tsum_congr fun x => ?_
      rw [hS]; ring
    have htailb := norm_tsum_mul_sub_lipInputW_le (P := P) (B := B) (F := F) hf1 hFsum
    have htail : ‖∑' x : ℤ, F x * S x‖
        ≤ ∑' x : ℤ, (if B < (x.natAbs : ℝ) then ‖F x‖ else 0) := by
      rw [hS]; exact htailb
    have hmain : ‖inner ℂ f φ‖
        ≥ ‖bilinPair (lipInputW P B (fun x : ℤ => f x)) F‖ - ‖∑' x : ℤ, F x * S x‖ := by
      rw [hinner, hsplit]
      have h2 : ‖bilinPair (lipInputW P B (fun x : ℤ => f x)) F‖
          ≤ ‖bilinPair (lipInputW P B (fun x : ℤ => f x)) F + ∑' x : ℤ, F x * S x‖
            + ‖∑' x : ℤ, F x * S x‖ := by
        have := norm_add_le (bilinPair (lipInputW P B (fun x : ℤ => f x)) F
          + ∑' x : ℤ, F x * S x) (-(∑' x : ℤ, F x * S x))
        simpa using this
      linarith
    have hFtail' : ‖∑' x : ℤ, F x * S x‖ ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2 :=
      htail.trans hFtail
    linarith [hFcorr, hFtail', hmain, hδK]

end Work.KMTAreas.A4
