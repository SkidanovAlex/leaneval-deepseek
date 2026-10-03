/-
# `Work.FIArea7.P231.card_strip_le`

The count of Gaussian integers in the *strip* `|Re(W z)| < |W| √N / R` intersected with the disc
`|z|² ≤ N`:  `#{z : |z|² ≤ N, (Re (W z))² R² < |W|² N} ≤ C (√N + N/R)`.

Geometrically the strip has width `2√N/R` while the disc has radius `√N`, so the count is
`area + boundary = 4N/R + O(√N)`.  The proof is the elementary slicing argument: slice the rotated
lattice `ℤ[i]` into rows (or columns) along the strip; each non-empty row carries at most
`2K/|β| + 1` points (`card_le_of_dvd_of_interval`, via `card_rows_le`) and there are at most
`2√N + 1` rows inside the disc.  The symmetric column count has `|α|` in the denominator,
obtained by transposing the set and reusing the row count; choosing the slicing with the larger of `|Re W|, |Im W|` in the denominator and using
`|W|² = a² + b² ≤ 2 max(a,b)²` gives the bound `(2√N + 1)(2√2 √N/R + 1) ≤ 30 (√N + N/R)`.
-/
import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231.card_rows_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7.P231

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma gnorm_cast_eq (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]
  push_cast
  simp only [Nat.cast_natAbs, Int.cast_abs]
  rw [← sq, ← sq, sq_abs, sq_abs]

/-- **The counted strip, in coordinates.**  Every pair `(x, y)` coming from a Gaussian integer `z`
of the box with `|z|² ≤ N` and `(Re(W z))² R² < |W|² N` satisfies the disc condition `x² + y² ≤ N`
and the strip condition `|Re W · x - Im W · y| < √(|W|² N)/R`. -/
private lemma strip_image_conds' (N R : ℕ) (W : GaussianInt) (hR : 1 ≤ R) :
    ∀ (p : ℤ × ℤ), p ∈ (((Work.FIPlan.gBox (N : ℤ)).filter
        (fun z => Work.FIPlan.gnorm z ≤ N ∧
          ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N : ℤ))).image
        (fun z => (z.re, z.im))) →
      ((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2 ≤ (N : ℝ) ∧
      |((W.re * p.1 - W.im * p.2 : ℤ) : ℝ)|
        < Real.sqrt ((Work.FIPlan.gnorm W : ℝ) * (N : ℝ)) / (R : ℝ) := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
  rw [Finset.mem_filter] at hz
  obtain ⟨-, hgn, hstrip⟩ := hz
  constructor
  · have h1 : (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) := by exact_mod_cast hgn
    rwa [gnorm_cast_eq z] at h1
  · have h2 : ((W * z).re : ℝ) ^ 2 * (R : ℝ) ^ 2
        < (Work.FIPlan.gnorm W : ℝ) * (N : ℝ) := by
      exact_mod_cast hstrip
    have hRpos : (0 : ℝ) < (R : ℝ) ^ 2 := by positivity
    have h3 : ((W * z).re : ℝ) ^ 2
        < ((Work.FIPlan.gnorm W : ℝ) * (N : ℝ)) / (R : ℝ) ^ 2 := by
      rw [lt_div_iff₀ hRpos]
      exact h2
    have h4 : ((W * z).re : ℝ) ^ 2
        < (Real.sqrt ((Work.FIPlan.gnorm W : ℝ) * (N : ℝ)) / (R : ℝ)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]
      exact h3
    have h5 : |((W * z).re : ℝ)|
        < Real.sqrt ((Work.FIPlan.gnorm W : ℝ) * (N : ℝ)) / (R : ℝ) := by
      have h6 := sq_lt_sq.mp h4
      have hnn : (0 : ℝ) ≤ Real.sqrt ((Work.FIPlan.gnorm W : ℝ) * (N : ℝ)) / (R : ℝ) :=
        div_nonneg (Real.sqrt_nonneg _) (by positivity)
      rwa [abs_of_nonneg hnn] at h6
    have h7 : ((W * z).re : ℝ) = ((W.re * z.re - W.im * z.im : ℤ) : ℝ) := by
      have hz : (W * z).re = W.re * z.re - W.im * z.im := by
        simp only [Zsqrtd.re_mul]
        ring
      exact_mod_cast hz
    rwa [h7] at h5

private lemma final_arith (N R : ℕ) (hN : 1 ≤ N) (hR : 1 ≤ R) :
    (2 * Real.sqrt (N:ℝ) + 1) * (2 * Real.sqrt 2 * Real.sqrt (N:ℝ) / (R:ℝ) + 1)
      ≤ 30 * (Real.sqrt (N:ℝ) + (N:ℝ)/(R:ℝ)) := by
  set s := Real.sqrt (N:ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr (by exact_mod_cast hN)
  have hsq : s^2 = (N:ℝ) := Real.sq_sqrt (by positivity)
  have hR0 : (0:ℝ) < R := by exact_mod_cast hR
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
  have h2 : Real.sqrt 2 ≤ 3/2 := by
    have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hexp : (2*s+1)*(2*Real.sqrt 2*s/(R:ℝ)+1)
      = 4*Real.sqrt 2*s^2/(R:ℝ) + 2*Real.sqrt 2*s/(R:ℝ) + 2*s + 1 := by ring
  rw [hexp, hsq]
  have hA : 4 * Real.sqrt 2 * (N:ℝ) / (R:ℝ) ≤ 6 * (N:ℝ) / (R:ℝ) := by
    apply div_le_div_of_nonneg_right
    · nlinarith
    · linarith
  have hB : 2 * Real.sqrt 2 * s / (R:ℝ) ≤ 3 * s := by
    have h1 : 2 * Real.sqrt 2 * s / (R:ℝ) ≤ 2 * Real.sqrt 2 * s := by
      rw [div_le_iff₀ hR0]
      nlinarith [mul_le_mul_of_nonneg_left hR1 (by positivity : (0:ℝ) ≤ 2 * Real.sqrt 2 * s)]
    nlinarith [h2, hs0]
  have hC : 6 * (N:ℝ) / (R:ℝ) ≤ 30 * ((N:ℝ)/(R:ℝ)) := by
    have hCeq : 6 * (N:ℝ) / (R:ℝ) = 6 * ((N:ℝ)/(R:ℝ)) := by ring
    rw [hCeq]
    nlinarith [div_nonneg hN0 hR0.le]
  have hD : 3 * s + 2 * s + 1 ≤ 30 * s := by linarith
  linarith [hA, hB, hC, hD]

/-- The strip half-width bound: with `q = a² + b² ≤ 2b²`, the quantity `2K/|b|` is at most
`2√2 √N / R` when `K = √(qN)/R`. -/
private lemma K_bound (a b N R : ℝ) (_hN : 0 ≤ N) (hR : 0 < R) (hb : 0 < |b|)
    (hab : a^2 ≤ b^2) :
    2 * (Real.sqrt ((a^2+b^2) * N) / R) / |b| ≤ 2 * Real.sqrt 2 * Real.sqrt N / R := by
  have hq0 : (0:ℝ) ≤ a^2 + b^2 := by positivity
  have hsq : Real.sqrt ((a^2+b^2) * N) = Real.sqrt (a^2+b^2) * Real.sqrt N :=
    Real.sqrt_mul hq0 N
  have hb2 : Real.sqrt (a^2+b^2) ≤ Real.sqrt 2 * |b| := by
    have h1 : Real.sqrt (a^2+b^2) ≤ Real.sqrt (2*b^2) := Real.sqrt_le_sqrt (by nlinarith)
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq_eq_abs] at h1
    exact h1
  rw [hsq]
  have hL : 2 * (Real.sqrt (a^2+b^2) * Real.sqrt N / R) / |b|
      = 2 * Real.sqrt (a^2+b^2) * Real.sqrt N / (R * |b|) := by
    field_simp
  rw [hL, div_le_iff₀ (by positivity : (0:ℝ) < R * |b|)]
  have hrhs : (2 * Real.sqrt 2 * Real.sqrt N / R) * (R * |b|)
      = 2 * Real.sqrt 2 * Real.sqrt N * |b| := by field_simp
  rw [hrhs]
  nlinarith [mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg N), Real.sqrt_nonneg N,
    Real.sqrt_nonneg 2, abs_nonneg b]

theorem card_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (W : GaussianInt), 1 ≤ R → 1 ≤ N → W ≠ 0 →
      (((Work.FIPlan.gBox (N : ℤ)).filter
          (fun z => Work.FIPlan.gnorm z ≤ N ∧
            ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N : ℤ))).card : ℝ)
        ≤ C * (Real.sqrt (N : ℝ) + (N : ℝ) / (R : ℝ)) := by
  classical
  refine ⟨30, by norm_num, ?_⟩
  intro N R W hR hN hW
  set A : Finset GaussianInt := (Work.FIPlan.gBox (N : ℤ)).filter
      (fun z => Work.FIPlan.gnorm z ≤ N ∧
        ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N : ℤ)) with hA
  set S : Finset (ℤ × ℤ) := A.image (fun z => (z.re, z.im)) with hS
  have hcoord_inj : Function.Injective (fun z : GaussianInt => (z.re, z.im)) :=
    fun x y h => Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hcard : (A.card : ℝ) = (S.card : ℝ) := by
    rw [hS, Finset.card_image_of_injective _ hcoord_inj]
  rw [hcard]
  set K : ℝ := Real.sqrt ((Work.FIPlan.gnorm W : ℝ) * (N : ℝ)) / (R : ℝ) with hK
  have hconds : ∀ p : ℤ × ℤ, p ∈ S →
      ((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2 ≤ (N : ℝ) ∧
      |((W.re * p.1 - W.im * p.2 : ℤ) : ℝ)| < K := by
    intro p hp
    have hp' : p ∈ (((Work.FIPlan.gBox (N : ℤ)).filter
        (fun z => Work.FIPlan.gnorm z ≤ N ∧
          ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N : ℤ))).image
        (fun z => (z.re, z.im))) := by
      rw [hS, hA] at hp
      exact hp
    have h := strip_image_conds' N R W hR p hp'
    exact ⟨h.1, by rw [hK]; exact h.2⟩
  have hnorm : ∀ p ∈ S, ((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2 ≤ (N : ℝ) :=
    fun p hp => (hconds p hp).1
  have hstrip : ∀ p ∈ S, |((W.re * p.1 - W.im * p.2 : ℤ) : ℝ)| < K :=
    fun p hp => (hconds p hp).2
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast hR
  have hgnorm : (Work.FIPlan.gnorm W : ℝ) = (W.re : ℝ) ^ 2 + (W.im : ℝ) ^ 2 :=
    gnorm_cast_eq W
  rcases le_or_gt ((W.re : ℝ) ^ 2) ((W.im : ℝ) ^ 2) with hab | hab
  · have hb0 : W.im ≠ 0 := by
      intro h
      have hbR : (W.im : ℝ) = 0 := by exact_mod_cast h
      have hre : (W.re : ℝ) = 0 := by
        nlinarith [hab, sq_nonneg (W.re : ℝ), hbR]
      exact hW (Zsqrtd.ext (by exact_mod_cast hre) h)
    have hb0R : (W.im : ℝ) ≠ 0 := by exact_mod_cast hb0
    have hrows := card_rows_le W.re W.im hb0 K (N:ℝ) hK0 hN0 S hnorm hstrip
    have hKb : 2 * K / |(W.im : ℝ)| ≤ 2 * Real.sqrt 2 * Real.sqrt (N : ℝ) / (R : ℝ) := by
      rw [hK, hgnorm]
      exact K_bound (W.re : ℝ) (W.im : ℝ) (N : ℝ) (R : ℝ) hN0 hR0 (abs_pos.mpr hb0R) hab
    calc (S.card : ℝ) ≤ (2 * Real.sqrt (N:ℝ) + 1) * (2 * K / |(W.im : ℝ)| + 1) := hrows
      _ ≤ (2 * Real.sqrt (N:ℝ) + 1) * (2 * Real.sqrt 2 * Real.sqrt (N:ℝ) / (R:ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ 30 * (Real.sqrt (N:ℝ) + (N:ℝ)/(R:ℝ)) := final_arith N R hN hR
  · have ha0 : W.re ≠ 0 := by
      intro h
      have haR : (W.re : ℝ) = 0 := by exact_mod_cast h
      have him : (W.im : ℝ) = 0 := by
        nlinarith [hab, sq_nonneg (W.im : ℝ), haR]
      exact hW (Zsqrtd.ext h (by exact_mod_cast him))
    have ha0R : (W.re : ℝ) ≠ 0 := by exact_mod_cast ha0
    -- the column count: transpose the set and apply the *row* count with the roles of
    -- `W.re` and `W.im` exchanged (the strip condition `|W.re x - W.im y| < K` becomes
    -- `|W.im x - W.re y| < K` under `(x,y) ↦ (y,x)`).
    set S' : Finset (ℤ × ℤ) := S.image (fun q => (q.2, q.1)) with hS'
    have hswap_inj : Function.Injective (fun q : ℤ × ℤ => (q.2, q.1)) :=
      fun a b h => Prod.ext (by simpa using congrArg Prod.snd h)
        (by simpa using congrArg Prod.fst h)
    have hcard' : (S'.card : ℝ) = (S.card : ℝ) := by
      rw [hS', Finset.card_image_of_injective _ hswap_inj]
    have hnorm' : ∀ p ∈ S', ((p.1 : ℝ)) ^ 2 + ((p.2 : ℝ)) ^ 2 ≤ (N : ℝ) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have h := hnorm q hq
      linarith
    have hstrip' : ∀ p ∈ S', |((W.im * p.1 - W.re * p.2 : ℤ) : ℝ)| < K := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have h := hstrip q hq
      have heq : ((W.im * q.2 - W.re * q.1 : ℤ) : ℝ)
          = -((W.re * q.1 - W.im * q.2 : ℤ) : ℝ) := by
        push_cast; ring
      rw [heq, abs_neg]
      exact h
    have hcols : (S.card : ℝ) ≤ (2 * Real.sqrt (N : ℝ) + 1) * (2 * K / |(W.re : ℝ)| + 1) := by
      rw [← hcard']
      exact card_rows_le W.im W.re ha0 K (N : ℝ) hK0 hN0 S' hnorm' hstrip'
    have hKa : 2 * K / |(W.re : ℝ)| ≤ 2 * Real.sqrt 2 * Real.sqrt (N : ℝ) / (R : ℝ) := by
      rw [hK, hgnorm]
      rw [show (W.re : ℝ) ^ 2 + (W.im : ℝ) ^ 2 = (W.im : ℝ) ^ 2 + (W.re : ℝ) ^ 2 from by ring]
      exact K_bound (W.im : ℝ) (W.re : ℝ) (N : ℝ) (R : ℝ) hN0 hR0 (abs_pos.mpr ha0R) (le_of_lt hab)
    calc (S.card : ℝ) ≤ (2 * Real.sqrt (N:ℝ) + 1) * (2 * K / |(W.re : ℝ)| + 1) := hcols
      _ ≤ (2 * Real.sqrt (N:ℝ) + 1) * (2 * Real.sqrt 2 * Real.sqrt (N:ℝ) / (R:ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ 30 * (Real.sqrt (N:ℝ) + (N:ℝ)/(R:ℝ)) := final_arith N R hN hR

end

end Work.FIArea7.P231
