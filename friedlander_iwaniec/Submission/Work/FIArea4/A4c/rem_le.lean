import Mathlib
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A4c.rem_le_arith_self
import Submission.Work.FITop4.Areas6c

set_option maxHeartbeats 1600000

namespace Work.FIArea4.A4c

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary triangle-inequality lemmas for the weighted sum

The remainder is `(W+B)(X)` minus the convex combination
`Σ_{m<X} wA X m·((W+B)(m) − junk_m)`; the weights `wA X ·` are nonnegative and sum to `1`
(`wA_nonneg`, `sum_wA_eq_one`), so the two weighted sums are bounded by their entries'
pointwise maxima.  These two lemmas isolate that step. -/

/-- A weighted sum of vectors is bounded by `M` as soon as every weight is nonnegative, the weights
sum to `1`, and each entry weighted by its weight is bounded by the weight times `M` (the product
form is chosen so that the bound may fail where the weight vanishes). -/
private lemma sum_norm_le_of_bound {ι : Type*} (s : Finset ι) (w : ι → ℝ) (v : ι → ℂ) (M : ℝ)
    (hw : ∀ m ∈ s, 0 ≤ w m) (hv : ∀ m ∈ s, w m * ‖v m‖ ≤ w m * M)
    (hsum : ∑ m ∈ s, w m = 1) :
    ‖∑ m ∈ s, ((w m : ℝ) : ℂ) * v m‖ ≤ M := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ s, ‖((w m : ℝ) : ℂ) * v m‖ ≤ w m * M := by
    intro m hm
    have h1 : ‖((w m : ℝ) : ℂ) * v m‖ = w m * ‖v m‖ := by
      rw [norm_mul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
        abs_of_nonneg (hw m hm)]
    rw [h1]; exact hv m hm
  calc ∑ m ∈ s, ‖((w m : ℝ) : ℂ) * v m‖ ≤ ∑ m ∈ s, w m * M := Finset.sum_le_sum hterm
    _ = (∑ m ∈ s, w m) * M := by rw [Finset.sum_mul]
    _ = M := by rw [hsum, one_mul]

/-- The triangle inequality behind the remainder: `A` minus the convex combination of the
`v m − j m` is bounded by `‖A‖` plus the two maxima. -/
private lemma norm_sub_sum_sub_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (v j : ι → ℂ) (A : ℂ)
    (Mv Mj : ℝ) (hw : ∀ m ∈ s, 0 ≤ w m) (hsum : ∑ m ∈ s, w m = 1)
    (hv : ∀ m ∈ s, w m * ‖v m‖ ≤ w m * Mv) (hj : ∀ m ∈ s, w m * ‖j m‖ ≤ w m * Mj) :
    ‖A - ∑ m ∈ s, ((w m : ℝ) : ℂ) * (v m - j m)‖ ≤ ‖A‖ + Mv + Mj := by
  have hsplit : ∑ m ∈ s, ((w m : ℝ) : ℂ) * (v m - j m)
      = (∑ m ∈ s, ((w m : ℝ) : ℂ) * v m) - (∑ m ∈ s, ((w m : ℝ) : ℂ) * j m) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun m _ => by rw [mul_sub])
  rw [hsplit]
  have h1 : A - ((∑ m ∈ s, ((w m : ℝ) : ℂ) * v m) - (∑ m ∈ s, ((w m : ℝ) : ℂ) * j m))
      = (A - ∑ m ∈ s, ((w m : ℝ) : ℂ) * v m) + ∑ m ∈ s, ((w m : ℝ) : ℂ) * j m := by ring
  rw [h1]
  have h2 := norm_sub_le A (∑ m ∈ s, ((w m : ℝ) : ℂ) * v m)
  have h3 := norm_add_le (A - ∑ m ∈ s, ((w m : ℝ) : ℂ) * v m)
      (∑ m ∈ s, ((w m : ℝ) : ℂ) * j m)
  have h4 := sum_norm_le_of_bound s w v Mv hw hv hsum
  have h5 := sum_norm_le_of_bound s w j Mj hw hj hsum
  linarith

/-- The assembly of the remainder bound (design `AREA4_ENGINES_LEAD.md` §3.3, node N8), with the
real-variable absorption supplied by the explicit hypothesis `harith`
(the sibling lemma `Work.FIArea4.A4c.rem_le_arith`).

1. `obtain ⟨δ, c₇, x₇, hδ, hc₇, h7⟩ := h7 η hη0 hη3`; `hjunk` gives `C, hC, Hj`.
2. Apply `h7` at `X` (`1 ≤ X`, `X < N^δ`, `X ≤ (log N)^{nuU}` are supplied by `harith`).
3. For `m ∈ Ico 1 X` with `wA X m ≠ 0`, `wA_support` gives `X/3 ≤ m`, so the same application at
   `m` gives `‖(W+B)(m)‖ ≤ c₇(P⁻¹ + 3X⁻¹)N²log N`.
4. Triangle inequality (`norm_sub_sum_sub_le`) plus `∑ wA = 1`, `wA ≥ 0` and `Hj`.
5. `harith` absorbs into `6c₇·X^{-1/3}N² + X^{-1/3}N²`, i.e. `c = 6c₇ + 1`. -/
private theorem rem_le_of_arith
    (harith : ∀ (η : ℝ) (hη0 : 0 < η) (hη3 : η < 3 / 32)
        (δ c7 Cj : ℝ) (hδ : 0 < δ) (hc7 : 0 < c7) (hCj : 0 < Cj),
        ∃ x0 : ℝ, ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
          Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
        ∀ (X : ℕ), (Real.log Pa.N) ^ (2 : ℕ) ≤ (X : ℝ) →
          (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
            (Real.log Pa.N) ^ Work.FITop4.nuU < Pa.N ^ δ ∧
            (2 : ℝ) ≤ Real.log Pa.N ∧
            (3 : ℝ) ≤ (X : ℝ) ∧
            c7 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
              ≤ 2 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 ∧
            c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
              ≤ 4 * c7 * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 ∧
            Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1)
              ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2)
    (h7 : Work.FITop4.Area7_6b) (hjunk : Work.FIArea4.A4c.JunkBound) :
    ∀ η : ℝ, 0 < η → η < 3 / 32 → ∃ c x0 : ℝ, 0 < c ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
      Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
    ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
      (Real.log Pa.N) ^ (2 : ℕ) ≤ (X : ℝ) → (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
      ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)
        - ∑ m ∈ Finset.Ico 1 X, ((Work.FIArea4.A4c.wA X m : ℝ) : ℂ) *
            (Work.FITop4.Wcut (Work.FITop.radN Pa) m β
              + Work.FITop4.Bcut (Work.FITop.radN Pa) m β
              - Work.FITop4.Tcut (Work.FITop.radN Pa) (Work.FIArea4.A4c.junkCut X m) β)‖
        ≤ c * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
  intro η hη0 hη3
  obtain ⟨δ, c7, x7, hδ, hc7, H7⟩ := h7 η hη0 hη3
  obtain ⟨Cj, hCj, Hj⟩ := hjunk
  obtain ⟨xa, Harith⟩ := harith η hη0 hη3 δ c7 Cj hδ hc7 hCj
  refine ⟨6 * c7 + 1, max x7 (max xa 4096), by linarith, ?_⟩
  intro Pa hx hPaη hPaτ X φ z0 β hβ haxis hlog2 hXmax
  have hx7 : x7 ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hxa : xa ≤ (Pa.x : ℝ) :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  obtain ⟨hlogdom, hL2, hX3, habs1, habs2, habs3⟩ :=
    Harith Pa hxa hPaη hPaτ X hlog2 hXmax
  have hLpos : 0 < Real.log Pa.N := by linarith
  have hNδ : (X : ℝ) < Pa.N ^ δ := lt_of_le_of_lt hXmax hlogdom
  have hXge1 : 1 ≤ X := by
    have h : (1 : ℝ) ≤ (X : ℝ) := by linarith
    exact_mod_cast h
  have hXge2 : 2 ≤ X := by
    have h : (2 : ℝ) ≤ (X : ℝ) := by linarith
    exact_mod_cast h
  have hsumw : ∑ m ∈ Finset.Ico 1 X, wA X m = 1 := sum_wA_eq_one X hXge2
  -- the `X`-term (step 2)
  have hboundX : ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β
      + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      ≤ c7 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
    H7 Pa hx7 hPaη hPaτ X φ z0 β hβ haxis hXge1 hNδ hXmax
  -- step 3: the pointwise bound for the weighted `(W+B)(m)`
  have hvbound : ∀ m ∈ Finset.Ico 1 X, wA X m *
        ‖Work.FITop4.Wcut (Work.FITop.radN Pa) m β + Work.FITop4.Bcut (Work.FITop.radN Pa) m β‖
      ≤ wA X m * (c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    obtain ⟨hm1, hmX⟩ := hm
    rcases eq_or_ne (wA X m) 0 with h0 | hne
    · rw [h0, zero_mul, zero_mul]
    · have hsupp := wA_support hne
      have hmge : (X : ℝ) / 3 ≤ (m : ℝ) := by linarith
      have hmXlt : (m : ℝ) < (X : ℝ) := by exact_mod_cast hmX
      have hmNδ : (m : ℝ) < Pa.N ^ δ := lt_trans hmXlt hNδ
      have hmLn : (m : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU :=
        le_of_lt (lt_of_lt_of_le hmXlt hXmax)
      have hb := H7 Pa hx7 hPaη hPaτ m φ z0 β hβ haxis hm1 hmNδ hmLn
      have hinv : (m : ℝ)⁻¹ ≤ 3 * (X : ℝ)⁻¹ := by
        have hXpos : (0 : ℝ) < (X : ℝ) / 3 := by linarith
        have h1 : ((m : ℝ))⁻¹ ≤ ((X : ℝ) / 3)⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hXpos hmge
        have h2 : ((X : ℝ) / 3)⁻¹ = 3 * (X : ℝ)⁻¹ := by
          rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
        linarith [h1, h2]
      have hstep : c7 * ((Pa.Pz : ℝ)⁻¹ + (m : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
          ≤ c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
        have hle : (Pa.Pz : ℝ)⁻¹ + (m : ℝ)⁻¹
            ≤ (Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹ := by linarith [hinv]
        have h1 : c7 * ((Pa.Pz : ℝ)⁻¹ + (m : ℝ)⁻¹)
            ≤ c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hle hc7.le
        have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg Pa.N)
        exact mul_le_mul_of_nonneg_right h2 hLpos.le
      calc wA X m * ‖Work.FITop4.Wcut (Work.FITop.radN Pa) m β
              + Work.FITop4.Bcut (Work.FITop.radN Pa) m β‖
          ≤ wA X m * (c7 * ((Pa.Pz : ℝ)⁻¹ + (m : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N) :=
            mul_le_mul_of_nonneg_left hb (wA_nonneg X m)
        _ ≤ wA X m * (c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N) :=
            mul_le_mul_of_nonneg_left hstep (wA_nonneg X m)
  -- step 4: the pointwise bound for the junk
  have hjbound : ∀ m ∈ Finset.Ico 1 X, wA X m *
        ‖Work.FITop4.Tcut (Work.FITop.radN Pa) (junkCut X m) β‖
      ≤ wA X m * (Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2)
          * (Real.log Pa.N + 1)) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    obtain ⟨hm1, hmX⟩ := hm
    exact mul_le_mul_of_nonneg_left (Hj Pa φ z0 β X m hβ hm1 hmX) (wA_nonneg X m)
  -- step 4: the triangle inequality
  have hmain : ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β
          + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)
        - ∑ m ∈ Finset.Ico 1 X, ((wA X m : ℝ) : ℂ) *
            (Work.FITop4.Wcut (Work.FITop.radN Pa) m β
              + Work.FITop4.Bcut (Work.FITop.radN Pa) m β
              - Work.FITop4.Tcut (Work.FITop.radN Pa) (junkCut X m) β)‖
      ≤ ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β
            + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)‖
        + (c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)
        + (Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N + 1)) :=
    norm_sub_sum_sub_le (Finset.Ico 1 X) (fun m => wA X m)
      (fun m => Work.FITop4.Wcut (Work.FITop.radN Pa) m β
        + Work.FITop4.Bcut (Work.FITop.radN Pa) m β)
      (fun m => Work.FITop4.Tcut (Work.FITop.radN Pa) (junkCut X m) β)
      (Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)
      (c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)
      (Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1))
      (fun m _ => wA_nonneg X m) hsumw hvbound hjbound
  -- step 5: absorb (the sibling lemma `rem_le_arith`)
  have h1 : ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β
        + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)‖
      ≤ 2 * c7 * ((X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2) :=
    le_trans hboundX (le_trans habs1 (le_of_eq (by ring)))
  have h2 : c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
      ≤ 4 * c7 * ((X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2) :=
    le_trans habs2 (le_of_eq (by ring))
  have h3 : Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N + 1)
      ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := habs3
  calc ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β
          + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)
        - ∑ m ∈ Finset.Ico 1 X, ((wA X m : ℝ) : ℂ) *
            (Work.FITop4.Wcut (Work.FITop.radN Pa) m β
              + Work.FITop4.Bcut (Work.FITop.radN Pa) m β
              - Work.FITop4.Tcut (Work.FITop.radN Pa) (junkCut X m) β)‖
      ≤ ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β
            + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)‖
        + (c7 * ((Pa.Pz : ℝ)⁻¹ + 3 * (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)
        + (Cj * Pa.τ ^ 2 * (X : ℝ) ^ 3 * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N + 1)) := hmain
    _ ≤ 2 * c7 * ((X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2)
        + 4 * c7 * ((X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2)
        + ((X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2) := add_le_add (add_le_add h1 h2) h3
    _ = (6 * c7 + 1) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by ring

/-- **The remainder** (design `AREA4_ENGINES_LEAD.md` §3.3, node N8).

Inputs as explicit hypotheses (so that this node is independent of the nodes proving them):
`h7 : Work.FITop4.Area7_6b` (PROVED in `Submission/Work/FIArea7/area7_6b.lean`, axiom-clean) and
`hjunk : JunkBound` (the crude junk bound of `A4c/junk_le.lean`).

Proof route:
1. `obtain ⟨δ, c₇, x₇, hδ, hc₇, h7⟩ := h7 η hη0 hη3`.  For `x ≥ x0` large enough,
   `(log N)^{nuU} < N^δ` (log dominance: use `Real.log_le_rpow_div`, `nuU = 3·sigmaChoice Asave + 4`)
   and `Pa.τ = tauOf Pa.x Asave > 0`.
2. Apply `h7` at `X`: hypotheses `1 ≤ X`, `X < N^δ`, `X ≤ (log N)^{nuU}`, the τ-pin and the
   axis-free box are all available → `‖(W+B)(X)‖ ≤ c₇ (P⁻¹ + X⁻¹) N² log N`.
3. For `m ∈ Finset.Ico 1 X` with `wA X m ≠ 0`: `Work.FIArea4.A4c.wA_support` gives
   `2X < 3(m+1)`, hence `X/3 ≤ m` for `3 ≤ X`; so the same application at `m` gives
   `‖(W+B)(m)‖ ≤ c₇ (P⁻¹ + m⁻¹) N² log N ≤ c₇ (P⁻¹ + 3X⁻¹) N² log N`.
4. `‖(W+B)(X) - ∑_m wA(m)((W+B)(m) - junk_m)‖ ≤ ‖(W+B)(X)‖ + ∑_m wA(m)‖(W+B)(m)‖ + ∑_m wA(m)‖junk_m‖`
   (triangle inequality, `norm_sum_le`, `norm_mul`), then
   `∑_m wA(m) = 1` and `wA ≥ 0` (`Work.FIArea4.A4c.sum_wA_eq_one`, `wA_nonneg`) bound the first two
   weighted sums by the maximum, and `hjunk` bounds the third by `C τ² X³ N^{3/2}(log N+1)`
   since `∑_m wA(m) = 1`.
   Total `≤ c₇(2P⁻¹ + 4X⁻¹)N²log N + C τ²X³N^{3/2}(log N+1)`.
5. Absorb into `(X^{-1/3})N²`, with the constant `c = 6c₇ + 1` (say):
   * `X⁻¹ log N ≤ X^{-1/3}`: `(log N)^2 ≤ X` gives `X^{1/3} ≥ (log N)^{2/3}` and
     `X^{2/3} log N ≤ X^{2/3}·X^{1/3}` hmm — simply `log N ≤ X^{2/3}` since
     `X^{2/3} ≥ (log N)^{4/3} ≥ log N` for `log N ≥ 1`.
   * `P⁻¹ log N ≤ X^{-1/3}`: `X^{1/3} log N ≤ (log N)^{nuU/3+1}` and `Pa.hPlo`
     (`(loglog x)² ≤ log Pz`) beats `(log x)^{nuU/3+1}` once `loglog x ≥ nuU/3 + 1`.
   * junk: `C τ² X^{10/3} (log N+1) ≤ N^{1/2}`.  With `τ = (log x)^{2Asave+2^20}` and
     `X ≤ (log N)^{nuU}`, the left side is `≤ C (log x)^{2Asave+2^20} (log N)^{(10/3)nuU+1}`, and
     `Pa.hNlo` (`x^{1/4+η} < N`) gives `N^{1/2} ≥ x^{1/8}`, so it suffices that
     `x^{1/8} ≥ C (log x)^{K}` with `K = 2Asave + 2^20 + (10/3)nuU + 1` — true for `x ≥ x0(K)`
     (raise `Real.log_le_rpow_div` to the `K`-th power with the exponent `η/4`).
   These produce the `x0` of the statement as the max of the finitely many thresholds (they may
   depend on `δ`, hence on `η` through `h7`).  This real-variable absorption is proved in the
   sibling module `A4c/rem_le_arith_self.lean` (`Work.FIArea4.A4c.RemSelfArith.rem_le_arith_self`)
   and enters the assembly above as the explicit hypothesis `harith` of `rem_le_of_arith`.
Use `set`/`clear_value` to keep `(log x)^{2Asave+2^20}`, `(log N)^{nuU}` and `2^{2^20}` opaque
inside the arithmetic (project build rule). -/
theorem rem_le (h7 : Work.FITop4.Area7_6b) (hjunk : Work.FIArea4.A4c.JunkBound) :
    ∀ η : ℝ, 0 < η → η < 3 / 32 → ∃ c x0 : ℝ, 0 < c ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
      Pa.τ = Work.FITop4.tauOf Pa.x Work.FITop4.Asave →
    ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
      (Real.log Pa.N) ^ (2 : ℕ) ≤ (X : ℝ) → (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
      ‖(Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β)
        - ∑ m ∈ Finset.Ico 1 X, ((Work.FIArea4.A4c.wA X m : ℝ) : ℂ) *
            (Work.FITop4.Wcut (Work.FITop.radN Pa) m β
              + Work.FITop4.Bcut (Work.FITop.radN Pa) m β
              - Work.FITop4.Tcut (Work.FITop.radN Pa) (Work.FIArea4.A4c.junkCut X m) β)‖
        ≤ c * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 :=
  rem_le_of_arith RemSelfArith.rem_le_arith_self h7 hjunk

end

end Work.FIArea4.A4c
