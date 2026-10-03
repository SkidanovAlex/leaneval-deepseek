import Mathlib
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## The Chebyshev radius of a Gaussian integer -/

/-- `‖z‖ = max(|Re z|, |Im z|)`, the radius of the smallest axis-parallel square box
centred at the origin that contains `z`. -/
def gRadius (z : GaussianInt) : ℕ := max z.re.natAbs z.im.natAbs

lemma gRadius_eq_zero_iff {z : GaussianInt} : gRadius z = 0 ↔ z = 0 := by
  rw [gRadius]
  constructor
  · intro h
    exact Zsqrtd.ext (Int.natAbs_eq_zero.mp (by omega)) (Int.natAbs_eq_zero.mp (by omega))
  · rintro rfl; simp

lemma one_le_gRadius_of_ne_zero {z : GaussianInt} (hz : z ≠ 0) : 1 ≤ gRadius z := by
  rcases Nat.eq_zero_or_pos (gRadius z) with h | h
  · exact absurd (gRadius_eq_zero_iff.mp h) hz
  · exact h

/-- `gRadius z ≤ k` unfolds into the four coordinate inequalities. -/
lemma gRadius_le_iff (z : GaussianInt) (k : ℕ) :
    gRadius z ≤ k ↔ -(k : ℤ) ≤ z.re ∧ z.re ≤ (k : ℤ)
      ∧ -(k : ℤ) ≤ z.im ∧ z.im ≤ (k : ℤ) := by
  rw [gRadius, max_le_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega⟩

/-- Membership in the box `gBox R` in terms of `gRadius`, for `R ≥ 0`. -/
lemma mem_gBox_iff_gRadius {R : ℤ} (hR : 0 ≤ R) {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ gRadius z ≤ R.natAbs := by
  rw [cf_mem_gBox_iff, gRadius, max_le_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega, by omega, by omega⟩

/-- **The box of radius `k` inside the box of radius `n`.**  For `k ≤ n` the points of
`gBox n` of Chebyshev radius at most `k` are exactly the points of `gBox k`. -/
lemma filter_gRadius_le_eq_gBox (n k : ℕ) (hk : k ≤ n) :
    (Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k)
      = Work.FIPlan.gBox ((k : ℤ)) := by
  ext z
  simp only [Finset.mem_filter, cf_mem_gBox_iff, gRadius_le_iff]
  constructor
  · rintro ⟨_, h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, h1, h2, h3, h4⟩

/-- The cardinality of the integer interval `[−R,R]`. -/
lemma card_Icc_int (R : ℤ) : (Finset.Icc (-R) R).card = (2 * R + 1).toNat := by
  rw [Int.card_Icc]
  congr 1
  ring

/-- The cardinality of the box `gBox R` is the square of the number of integers in `[−R,R]`. -/
lemma card_gBox_eq (R : ℤ) :
    (Work.FIPlan.gBox R).card = (2 * R + 1).toNat ^ 2 := by
  rw [Work.FIPlan.gBox, Finset.card_image_of_injective _ Work.FIPlan.gaussMk_injective,
    Finset.product_eq_sprod, Finset.card_product, card_Icc_int]
  ring

/-! ## The one-dimensional counting bound -/

/-- A set of integers `t` with `|a·t − K| < M`, for a **positive** integer `a`, has at most
`2M/a + 1` elements. -/
private lemma card_le_div_of_pos_abs_lt (a : ℤ) (ha : 0 < a) (K : ℤ) (M : ℕ) (U : Finset ℤ)
    (h : ∀ t ∈ U, (a * t - K).natAbs < M) :
    U.card ≤ 2 * M / a.natAbs + 1 := by
  rcases U.eq_empty_or_nonempty with hem | hne
  · rw [hem]; simp
  · set t0 := U.min' hne
    have ht0U : t0 ∈ U := U.min'_mem hne
    have hle : ∀ t ∈ U, t0 ≤ t := fun t ht => U.min'_le t ht
    have hmaps : Set.MapsTo (fun t : ℤ => (t - t0).toNat) (↑U : Set ℤ)
        (↑(Finset.range (2 * M / a.natAbs + 1)) : Set ℕ) := by
      intro t ht
      simp only [Finset.mem_coe, Finset.mem_range]
      have hbt : (a * t - K).natAbs < M := h t ht
      have hb0 : (a * t0 - K).natAbs < M := h t0 ht0U
      have ht0t : t0 ≤ t := hle t ht
      have h1 : a * t - K ≤ (M:ℤ) - 1 := by omega
      have h2 : -((M:ℤ) - 1) ≤ a * t0 - K := by omega
      have h3 : a * (t - t0) ≤ 2 * (M:ℤ) - 2 := by
        have : a * (t - t0) = (a*t - K) - (a*t0 - K) := by ring
        omega
      have hd0 : (0:ℤ) ≤ t - t0 := by omega
      have haeq : a = (a.natAbs : ℤ) := by omega
      rw [haeq] at h3
      have ht' : t - t0 = (((t - t0).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hd0).symm
      rw [ht'] at h3
      rw [← Nat.cast_mul] at h3
      have h5 : a.natAbs * (t - t0).toNat < 2 * M := by
        have key : ((a.natAbs * (t - t0).toNat : ℕ) : ℤ) < ((2*M : ℕ) : ℤ) := by
          have h2M : ((2*M : ℕ) : ℤ) = 2 * (M:ℤ) := by push_cast; ring
          rw [h2M]; omega
        exact_mod_cast key
      have hc : 0 < a.natAbs := Int.natAbs_pos.mpr (ne_of_gt ha)
      have h6 : (t - t0).toNat ≤ 2 * M / a.natAbs := by
        rw [Nat.le_div_iff_mul_le hc, Nat.mul_comm]
        omega
      omega
    have hinj : Set.InjOn (fun t : ℤ => (t - t0).toNat) (↑U : Set ℤ) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe] at hx hy
      have hx0 : t0 ≤ x := hle x hx
      have hy0 : t0 ≤ y := hle y hy
      have e1 : (0:ℤ) ≤ x - t0 := by omega
      have e2 : (0:ℤ) ≤ y - t0 := by omega
      have h1 : x - t0 = y - t0 := by
        have := congrArg (fun n : ℕ => (n:ℤ)) hxy
        rw [Int.toNat_of_nonneg e1, Int.toNat_of_nonneg e2] at this
        exact this
      omega
    have := Finset.card_le_card_of_injOn (fun t : ℤ => (t - t0).toNat) hmaps hinj
    simpa using this

/-- A set of integers `t` with `|a·t − K| < M`, for a **nonzero** integer `a`, has at most
`2M/|a| + 1` elements. -/
private lemma card_le_div_of_abs_lt (a : ℤ) (ha : a ≠ 0) (K : ℤ) (M : ℕ) (U : Finset ℤ)
    (h : ∀ t ∈ U, (a * t - K).natAbs < M) :
    U.card ≤ 2 * M / a.natAbs + 1 := by
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · have ha' : 0 < -a := by omega
    have hres := card_le_div_of_pos_abs_lt (-a) ha' (-K) M U (by
      intro t ht
      have h' := h t ht
      have heq : ((-a) * t - (-K)) = -(a * t - K) := by ring
      rwa [heq, Int.natAbs_neg])
    rwa [Int.natAbs_neg] at hres
  · exact card_le_div_of_pos_abs_lt a hgt K M U h

/-- **One-dimensional count.**  For a nonzero coefficient `c`, the integers `t` of `[−R,R]`
with `|c·t − K| < M` number at most `2M/|c| + 1`. -/
lemma card_Icc_lin_le (R : ℤ) (c : ℤ) (hc : c ≠ 0) (K : ℤ) (M : ℕ) :
    ((Finset.Icc (-R) R).filter (fun t => (c * t - K).natAbs < M)).card
      ≤ 2 * M / c.natAbs + 1 :=
  card_le_div_of_abs_lt c hc K M _
    (fun _t ht => (Finset.mem_filter.mp ht).2)

/-- `(a / b : ℕ)` cast to `ℝ` is at most `a / b`. -/
lemma natCast_div_le (a b : ℕ) : (((a / b : ℕ)) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp
  · have hb : (0:ℝ) < (b : ℝ) := by exact_mod_cast h
    rw [le_div_iff₀ hb]
    have h1 : (a / b) * b ≤ a := Nat.div_mul_le_self a b
    calc (((a / b : ℕ)) : ℝ) * (b : ℝ) = (((a / b) * b : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (a : ℝ) := by exact_mod_cast h1

/-! ## Counting the shell `gRadius = k` -/

/-- For `1 ≤ k ≤ n` the box `gBox n` contains exactly `8k` points of Chebyshev radius `k`. -/
lemma card_filter_gRadius_eq_le (n k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ n) :
    ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z = k)).card ≤ 8 * k := by
  have hA : (Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k)
      = Work.FIPlan.gBox ((k : ℤ)) := filter_gRadius_le_eq_gBox n k hk
  have hB : (Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k - 1)
      = Work.FIPlan.gBox (((k - 1 : ℕ) : ℤ)) := filter_gRadius_le_eq_gBox n (k - 1) (by omega)
  have hdisj : Disjoint ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k - 1))
      ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z = k)) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rw [Finset.mem_filter] at hz1 hz2
    omega
  have hpart : (Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k)
      = (Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k - 1)
        ∪ (Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z = k) := by
    ext z
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hz, h⟩
      by_cases h' : gRadius z ≤ k - 1
      · exact Or.inl ⟨hz, h'⟩
      · exact Or.inr ⟨hz, by omega⟩
    · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
      · exact ⟨hz, by omega⟩
      · exact ⟨hz, by omega⟩
  have hcard : ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k)).card
      = ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k - 1)).card
        + ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z = k)).card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have hAk : ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k)).card
      = (2 * k + 1) ^ 2 := by
    rw [hA, card_gBox_eq]
    have h : 2 * (k : ℤ) + 1 = (((2 * k + 1 : ℕ)) : ℤ) := by omega
    rw [h, Int.toNat_natCast]
  have hBk : ((Work.FIPlan.gBox ((n : ℤ))).filter (fun z => gRadius z ≤ k - 1)).card
      = (2 * k - 1) ^ 2 := by
    rw [hB, card_gBox_eq]
    have h : 2 * (((k - 1 : ℕ)) : ℤ) + 1 = (((2 * k - 1 : ℕ)) : ℤ) := by omega
    rw [h, Int.toNat_natCast]
  rw [hAk, hBk] at hcard
  have key : (2 * k + 1) ^ 2 = (2 * k - 1) ^ 2 + 8 * k := by
    have h1 : 2 * k + 1 = (2 * k - 1) + 2 := by omega
    have h2 : 8 * k = 4 * (2 * k - 1) + 4 := by omega
    rw [h1, h2]; ring
  omega

/-! ## The two-dimensional harmonic sum -/

/-- **The `2`-dimensional harmonic bound.**  `Σ_{0 ≠ z ∈ gBox n} 1/‖z‖ ≤ 8n`, where `‖z‖` is the
Chebyshev radius: fibre over `‖z‖ = k`, which contains `8k` points and contributes `8k/k = 8`. -/
lemma sum_gRadius_inv_le (n : ℕ) :
    ∑ z ∈ (Work.FIPlan.gBox ((n : ℤ))).erase 0, (1 : ℝ) / (gRadius z : ℝ) ≤ 8 * (n : ℝ) := by
  have hmaps : ∀ z ∈ (Work.FIPlan.gBox ((n : ℤ))).erase 0, gRadius z ∈ Finset.Icc 1 n := by
    intro z hz
    rw [Finset.mem_erase] at hz
    have hb := cf_mem_gBox_iff.mp hz.2
    refine Finset.mem_Icc.mpr ⟨one_le_gRadius_of_ne_zero hz.1, ?_⟩
    rw [gRadius, max_le_iff]
    constructor <;> omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun z => (1 : ℝ) / (gRadius z : ℝ))]
  have hinner : ∀ j ∈ Finset.Icc 1 n,
      ∑ z ∈ ((Work.FIPlan.gBox ((n : ℤ))).erase 0).filter (fun z => gRadius z = j),
          (1 : ℝ) / (gRadius z : ℝ) ≤ 8 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hcard : (((Work.FIPlan.gBox ((n : ℤ))).erase 0).filter
        (fun z => gRadius z = j)).card ≤ 8 * j := by
      refine le_trans (Finset.card_le_card ?_) (card_filter_gRadius_eq_le n j hj.1 hj.2)
      intro z hz
      rw [Finset.mem_filter, Finset.mem_erase] at hz
      rw [Finset.mem_filter]
      exact ⟨hz.1.2, hz.2⟩
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    calc ∑ z ∈ ((Work.FIPlan.gBox ((n : ℤ))).erase 0).filter (fun z => gRadius z = j),
            (1 : ℝ) / (gRadius z : ℝ)
        = ∑ z ∈ ((Work.FIPlan.gBox ((n : ℤ))).erase 0).filter (fun z => gRadius z = j),
            (1 : ℝ) / (j : ℝ) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [Finset.mem_filter] at hz
          rw [hz.2]
      _ = (((((Work.FIPlan.gBox ((n : ℤ))).erase 0).filter
              (fun z => gRadius z = j)).card : ℕ) : ℝ) * (1 / (j : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((8 * j : ℕ) : ℝ) * (1 / (j : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
      _ = 8 := by
          push_cast
          field_simp
  calc ∑ j ∈ Finset.Icc 1 n,
        ∑ z ∈ ((Work.FIPlan.gBox ((n : ℤ))).erase 0).filter (fun z => gRadius z = j),
          (1 : ℝ) / (gRadius z : ℝ)
      ≤ ∑ _j ∈ Finset.Icc 1 n, (8 : ℝ) := Finset.sum_le_sum hinner
    _ = 8 * (n : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        have : n + 1 - 1 = n := by omega
        rw [this]; ring

/-! ## The `z₁`-count for a fixed `z₂ ≠ 0` -/

/-- **Fibre count over `z₁`.**  For `z₂ ≠ 0`, the number of `z₁` in the box `gBox R` with
`|Δ(z₁,z₂)| < M` is at most `(2R+1)·(2M/‖z₂‖ + 1)`, where `‖z₂‖` is the Chebyshev radius.
Fibre over the coordinate of `z₁` whose coefficient in `Δ` is the larger of `|Re z₂|`, `|Im z₂|`;
in each fibre one coordinate of `z₁` ranges in an interval of length `2M/‖z₂‖`. -/
lemma card_z1_absDelta_le (R : ℤ) (M : ℕ) (z2 : GaussianInt) (hz : z2 ≠ 0) :
    ((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card
      ≤ (2 * R + 1).toNat * (2 * M / gRadius z2 + 1) := by
  rcases le_total z2.im.natAbs z2.re.natAbs with hle | hlt
  · have hA : gRadius z2 = z2.re.natAbs := by rw [gRadius, max_eq_left hle]
    have hre : z2.re ≠ 0 := by
      intro h
      have hz0 : gRadius z2 = 0 := by rw [hA, h]; rfl
      exact hz (gRadius_eq_zero_iff.mp hz0)
    set S := (Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M) with hS
    have hmaps : Set.MapsTo (fun z : GaussianInt => z.re) (↑S : Set GaussianInt)
        (↑(Finset.Icc (-R) R) : Set ℤ) := by
      intro z hzS
      have hz' : z ∈ S := hzS
      rw [hS, Finset.mem_filter] at hz'
      have h := cf_mem_gBox_iff.mp hz'.1
      exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
    have hcard := Finset.card_eq_sum_card_fiberwise hmaps
    have hfiber : ∀ a ∈ Finset.Icc (-R) R,
        (S.filter (fun z => z.re = a)).card ≤ 2 * M / z2.re.natAbs + 1 := by
      intro a _ha
      set F := S.filter (fun z => z.re = a) with hF
      have hFU : (F.image (fun z => z.im)).card = F.card := by
        refine Finset.card_image_of_injOn ?_
        intro x hx y hy hxy
        have hx' : x.re = a := (Finset.mem_filter.mp hx).2
        have hy' : y.re = a := (Finset.mem_filter.mp hy).2
        exact Zsqrtd.ext (by rw [hx', hy']) hxy
      rw [← hFU]
      refine le_trans (Finset.card_le_card ?_) (card_Icc_lin_le R z2.re hre (a * z2.im) M)
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨z, hzF, rfl⟩ := ht
      rw [Finset.mem_filter]
      have hzF' := Finset.mem_filter.mp hzF
      have hzS' := Finset.mem_filter.mp hzF'.1
      refine ⟨?_, ?_⟩
      · have h := cf_mem_gBox_iff.mp hzS'.1
        exact Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2⟩
      · have hΔ : Work.FIPlan.absDelta z z2 < M := hzS'.2
        rw [Work.FIPlan.absDelta, Delta_eq z z2] at hΔ
        rw [hzF'.2] at hΔ
        have heq : z2.re * z.im - a * z2.im = -(a * z2.im - z.im * z2.re) := by ring
        rw [heq, Int.natAbs_neg]
        exact hΔ
    calc S.card = ∑ a ∈ Finset.Icc (-R) R, (S.filter (fun z => z.re = a)).card := hcard
      _ ≤ ∑ _a ∈ Finset.Icc (-R) R, (2 * M / z2.re.natAbs + 1) := Finset.sum_le_sum hfiber
      _ = (Finset.Icc (-R) R).card * (2 * M / z2.re.natAbs + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
      _ = (2 * R + 1).toNat * (2 * M / z2.re.natAbs + 1) := by rw [card_Icc_int R]
      _ = (2 * R + 1).toNat * (2 * M / gRadius z2 + 1) := by rw [hA]
  · have hA : gRadius z2 = z2.im.natAbs := by rw [gRadius, max_eq_right hlt]
    have him : z2.im ≠ 0 := by
      intro h
      have hz0 : gRadius z2 = 0 := by rw [hA, h]; rfl
      exact hz (gRadius_eq_zero_iff.mp hz0)
    set S := (Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M) with hS
    have hmaps : Set.MapsTo (fun z : GaussianInt => z.im) (↑S : Set GaussianInt)
        (↑(Finset.Icc (-R) R) : Set ℤ) := by
      intro z hzS
      have hz' : z ∈ S := hzS
      rw [hS, Finset.mem_filter] at hz'
      have h := cf_mem_gBox_iff.mp hz'.1
      exact Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2⟩
    have hcard := Finset.card_eq_sum_card_fiberwise hmaps
    have hfiber : ∀ b ∈ Finset.Icc (-R) R,
        (S.filter (fun z => z.im = b)).card ≤ 2 * M / z2.im.natAbs + 1 := by
      intro b _hb
      set F := S.filter (fun z => z.im = b) with hF
      have hFU : (F.image (fun z => z.re)).card = F.card := by
        refine Finset.card_image_of_injOn ?_
        intro x hx y hy hxy
        have hx' : x.im = b := (Finset.mem_filter.mp hx).2
        have hy' : y.im = b := (Finset.mem_filter.mp hy).2
        exact Zsqrtd.ext hxy (by rw [hx', hy'])
      rw [← hFU]
      refine le_trans (Finset.card_le_card ?_) (card_Icc_lin_le R z2.im him (b * z2.re) M)
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨z, hzF, rfl⟩ := ht
      rw [Finset.mem_filter]
      have hzF' := Finset.mem_filter.mp hzF
      have hzS' := Finset.mem_filter.mp hzF'.1
      refine ⟨?_, ?_⟩
      · have h := cf_mem_gBox_iff.mp hzS'.1
        exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
      · have hΔ : Work.FIPlan.absDelta z z2 < M := hzS'.2
        rw [Work.FIPlan.absDelta, Delta_eq z z2] at hΔ
        rw [hzF'.2] at hΔ
        have heq : z2.im * z.re - b * z2.re = z.re * z2.im - b * z2.re := by ring
        rw [heq]
        exact hΔ
    calc S.card = ∑ b ∈ Finset.Icc (-R) R, (S.filter (fun z => z.im = b)).card := hcard
      _ ≤ ∑ _b ∈ Finset.Icc (-R) R, (2 * M / z2.im.natAbs + 1) := Finset.sum_le_sum hfiber
      _ = (Finset.Icc (-R) R).card * (2 * M / z2.im.natAbs + 1) := by
            rw [Finset.sum_const, smul_eq_mul]
      _ = (2 * R + 1).toNat * (2 * M / z2.im.natAbs + 1) := by rw [card_Icc_int R]
      _ = (2 * R + 1).toNat * (2 * M / gRadius z2 + 1) := by rw [hA]

/-! ## The near-diagonal pair count -/

/-- **The near-diagonal count.**  The number of pairs `(z₁, z₂)` in the box `gBox R` with
`|Δ(z₁,z₂)| < M` is `≪ M·R² + R³`, i.e. (with `R² ≍ N`, `M ≍ N/H`) `≪ H⁻¹N² + N^{3/2}`.  This is
the elementary estimate behind the removal of the *near-diagonal* pairs in *FI* (16.6) and in the
passage (17.9) ⇒ (17.10): the Fourier expansion of `logFac` has remainder `≪ 1/(K|sin t|)`
(`Work.FIArea7.logFac_eq_sum_powers`), i.e. `≪ |z₁z₂|/(K|Δ|)`, so only the pairs with
`|Δ| ≳ |z₁z₂|/H` can be kept, and the discarded diagonal set costs one factor `H⁻¹`.

Proof sketch: fix `z₂ ≠ 0` and count `z₁`.  The set `{|r₁s₂ − r₂s₁| < M}` is a strip of width
`2M/|z₂|` in the `(r₁,s₁)`-plane (`(s₂,−r₂)` is primitive when `z₂` is), so it meets the box
`[−R,R]²` of side `2R` in `≪ (2R+1) + 4RM/|z₂|` lattice points; summing the two terms over
`z₂ ∈ gBox R`, `z₂ ≠ 0`, uses the two-dimensional harmonic bound
`Σ_{z₂ ∈ gBox R, z₂ ≠ 0} 1/|z₂| ≪ log(2R+1)`, and the `z₂ = 0` fibre is absorbed by the `R³` term.
NOTE (for the prover): summing the one-dimensional bound `Work.FIArea7.card_gBox_absDelta_lt` over
`z₁` is **not** enough — it produces a spurious factor `log R`. -/
theorem card_pairs_gBox_absDelta_lt :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (M : ℕ),
      ((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
        ≤ C * ((M : ℝ) + 1) * (((2 * R + 1).toNat : ℝ) ^ 2)
          + C * (((2 * R + 1).toNat : ℝ) ^ 3) := by
  refine ⟨40, by norm_num, ?_⟩
  intro R M
  rcases lt_or_ge R 0 with hneg | hR
  · have hIcc : Finset.Icc (-R) R = (∅ : Finset ℤ) := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    have hempty : Work.FIPlan.gBox R = ∅ := by
      rw [Work.FIPlan.gBox, hIcc]; simp
    have hN0 : (2 * R + 1).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hempty, hN0]
    simp
  · set n : ℕ := R.toNat with hn
    set N : ℝ := ((2 * R + 1).toNat : ℝ) with hNdef
    have hRn : ((n : ℕ) : ℤ) = R := Int.toNat_of_nonneg hR
    have hNR : (2 * R + 1).toNat = 2 * n + 1 := by
      have h : 2 * R + 1 = (((2 * n + 1 : ℕ)) : ℤ) := by rw [← hRn]; omega
      rw [h, Int.toNat_natCast]
    have hNval : N = (((2 * n + 1 : ℕ)) : ℝ) := by rw [hNdef, hNR]
    have hNnn : (0 : ℝ) ≤ N := by rw [hNval]; positivity
    have hNR2 : (((2 * R + 1).toNat : ℕ) : ℝ) = N := hNdef.symm
    -- decomposition of the pair count as a sum over `z₂`
    have hdecompN : ((Work.FIPlan.gBox R ×ˢ Work.FIPlan.gBox R).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card
        = ∑ z2 ∈ Work.FIPlan.gBox R,
            ((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card := by
      rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z2 _ => ?_)
      rw [Finset.card_filter]
    have hdecomp : (((Work.FIPlan.gBox R ×ˢ Work.FIPlan.gBox R).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
        = ∑ z2 ∈ Work.FIPlan.gBox R,
            (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ) := by
      rw [hdecompN, Nat.cast_sum]
    -- split off the `z₂ = 0` fibre
    have h0mem : (0 : GaussianInt) ∈ Work.FIPlan.gBox R := by
      rw [mem_gBox_iff_gRadius hR]
      simp [gRadius]
    have hsplit : ∑ z2 ∈ Work.FIPlan.gBox R,
            (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
        = (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
          + ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
              (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ) := by
      have hs := Finset.sum_erase_add (Work.FIPlan.gBox R)
        (fun z2 => (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ))
        h0mem
      rw [add_comm] at hs
      exact hs.symm
    -- the `z₂ = 0` fibre costs at most `N²`
    have hC0 : (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
        ≤ N ^ 2 := by
      have hcf : ((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card
          ≤ (Work.FIPlan.gBox R).card := Finset.card_filter_le _ _
      have h2 : ((Work.FIPlan.gBox R).card : ℝ) = N ^ 2 := by
        rw [card_gBox_eq, hNdef]
        push_cast
        ring
      calc (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
          ≤ ((Work.FIPlan.gBox R).card : ℝ) := by exact_mod_cast hcf
        _ = N ^ 2 := h2
    -- every nonzero `z₂` contributes at most `N·(2M/‖z₂‖ + 1)`
    have hCne : ∀ z2 ∈ (Work.FIPlan.gBox R).erase 0,
        (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
          ≤ N * (2 * (M : ℝ) / (gRadius z2 : ℝ) + 1) := by
      intro z2 hz2
      rw [Finset.mem_erase] at hz2
      have h := card_z1_absDelta_le R M z2 hz2.1
      have step : (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
          ≤ (((2 * R + 1).toNat * (2 * M / gRadius z2 + 1) : ℕ) : ℝ) := by exact_mod_cast h
      refine step.trans ?_
      push_cast
      rw [hNR2]
      apply mul_le_mul_of_nonneg_left _ hNnn
      have hdiv : (((2 * M / gRadius z2 : ℕ)) : ℝ) ≤ 2 * (M : ℝ) / (gRadius z2 : ℝ) := by
        have h0 := natCast_div_le (2 * M) (gRadius z2)
        simpa using h0
      linarith
    -- the harmonic sum and the cardinality of the punctured box
    have hsumS : ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0, (1 : ℝ) / (gRadius z2 : ℝ)
        ≤ 8 * (n : ℝ) := by
      rw [show Work.FIPlan.gBox R = Work.FIPlan.gBox ((n : ℤ)) from by rw [← hRn]]
      exact sum_gRadius_inv_le n
    have herasecard : (((Work.FIPlan.gBox R).erase 0).card : ℝ) ≤ N ^ 2 := by
      have h1 : ((Work.FIPlan.gBox R).erase 0).card ≤ (Work.FIPlan.gBox R).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      calc (((Work.FIPlan.gBox R).erase 0).card : ℝ) ≤ ((Work.FIPlan.gBox R).card : ℝ) := by
            exact_mod_cast h1
        _ = N ^ 2 := by rw [card_gBox_eq, hNdef]; push_cast; ring
    have hSbound : ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
            (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
        ≤ N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := by
      have h1 : ∀ z2 ∈ (Work.FIPlan.gBox R).erase 0,
          (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
            ≤ N * (2 * (M : ℝ) * (1 / (gRadius z2 : ℝ)) + 1) := by
        intro z2 hz2
        refine (hCne z2 hz2).trans (le_of_eq ?_)
        ring
      calc ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
              (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
          ≤ ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
              N * (2 * (M : ℝ) * (1 / (gRadius z2 : ℝ)) + 1) := Finset.sum_le_sum h1
        _ = N * (2 * (M : ℝ) * (∑ z2 ∈ (Work.FIPlan.gBox R).erase 0, 1 / (gRadius z2 : ℝ))
              + (((Work.FIPlan.gBox R).erase 0).card : ℝ)) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              nsmul_eq_mul, mul_one]
        _ ≤ N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hNnn
            have hSnn : (0 : ℝ) ≤ ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
                1 / (gRadius z2 : ℝ) := by positivity
            nlinarith [hsumS, herasecard, hSnn, show (0 : ℝ) ≤ (M : ℝ) by positivity,
              show (0 : ℝ) ≤ (n : ℝ) by positivity]
    -- assemble
    have hfinal : ((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
        ≤ N ^ 2 + N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := by
      rw [hdecomp, hsplit]
      linarith [hC0, hSbound]
    have hnle : (n : ℝ) ≤ N := by
      rw [hNval]
      push_cast
      linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
    have hN1 : (1 : ℝ) ≤ N := by
      rw [hNval]
      push_cast
      linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
    calc ((((Work.FIPlan.gBox R) ×ˢ Work.FIPlan.gBox R).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
        ≤ N ^ 2 + N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := hfinal
      _ = N ^ 2 + 16 * (M : ℝ) * (n : ℝ) * N + N ^ 3 := by ring
      _ ≤ 40 * ((M : ℝ) + 1) * N ^ 2 + 40 * N ^ 3 := by
          have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
          have key : 16 * (M : ℝ) * (n : ℝ) * N ≤ 16 * (M : ℝ) * N ^ 2 := by
            have hb : (0 : ℝ) ≤ 16 * (M : ℝ) * N := by positivity
            calc 16 * (M : ℝ) * (n : ℝ) * N = (16 * (M : ℝ) * N) * (n : ℝ) := by ring
              _ ≤ (16 * (M : ℝ) * N) * N := mul_le_mul_of_nonneg_left hnle hb
              _ = 16 * (M : ℝ) * N ^ 2 := by ring
          nlinarith [key, hN1, hM0, sq_nonneg N, mul_nonneg hM0 (sq_nonneg N)]

end

end Work.FIArea7
