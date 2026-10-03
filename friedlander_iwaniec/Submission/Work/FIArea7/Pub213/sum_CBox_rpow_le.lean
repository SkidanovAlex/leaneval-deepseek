/-
# `Work.FIArea7.Pub213.sum_CBox_rpow_le`

The class-`C` series `∑_{c ∈ C, |c|² ≤ X} |c|^{-s}` is bounded uniformly in `X`, for every
`s > 1` (here `|c|^{-s} = (|c|²)^{-s/2}`).

*FI* need this for the arrangement `z = c·z∗` of p. 1027: the classes `c ∈ C` carry the weight
`|c|^{-s}`, and the two exponents used are `s = 2` and `s = 11/6` (i.e. `|c|^{-2}` and
`|c|^{-11/6}`).

Every `c ∈ C` can be written `c = u·(1+i)^b·n` with `u` a unit and `n` odd, hence
`|c|² = 2^b n²` and `|c|^{-s} = 2^{-bs/2} n^{-s}`.  For fixed `(b,n)` the unit `u` — and hence
`c` — is determined up to the `9` elements of the box `gBox 1` (`4` units, but `9` is all we
use).  The two series `∑_b 2^{-bs/2} = (1 - 2^{-s/2})^{-1}` and `∑_n n^{-s}` converge for `s > 1`,
giving a constant independent of `X`.

The only `X`-dependence enters through `2^b n² = |c|² ≤ 2R²` with `R = ⌈√X⌉`, which confines
`(b,n)` to the rectangle `[0, 2R²+1)²`; both partial sums are then bounded by the corresponding
`tsum`s.
-/
import Mathlib
import Submission.Work.FIArea7.Pub213.Defs
import Submission.Work.FIArea7.Prop213Aux.Defs

set_option autoImplicit false

namespace Work.FIArea7.Pub213

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The two convergent majorants -/

/-- The geometric majorant `2^{-sb/2}`. -/
def fMaj (s : ℝ) (b : ℕ) : ℝ := (2 : ℝ) ^ (-(s / 2) * b)

/-- The `ζ`-majorant `n^{-s}`. -/
def gMaj (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-s)

/-- The weight of a pair `(b,n)`: `2^{-sb/2} n^{-s} = (2^b n²)^{-s/2}`. -/
def wMaj (s : ℝ) (q : ℕ × ℕ) : ℝ := fMaj s q.1 * gMaj s q.2

lemma fMaj_nonneg (s : ℝ) (b : ℕ) : 0 ≤ fMaj s b := Real.rpow_nonneg (by norm_num) _

lemma gMaj_nonneg (s : ℝ) (n : ℕ) : 0 ≤ gMaj s n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

lemma wMaj_nonneg (s : ℝ) (q : ℕ × ℕ) : 0 ≤ wMaj s q :=
  mul_nonneg (fMaj_nonneg s q.1) (gMaj_nonneg s q.2)

/-- `∑_b 2^{-sb/2}` is a geometric series of ratio `2^{-s/2} ∈ (0,1)` for `s > 0`. -/
lemma fMaj_summable {s : ℝ} (hs : 0 < s) : Summable (fMaj s) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(s / 2)) := Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (2 : ℝ) ^ (-(s / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeo : Summable (fun b : ℕ => ((2 : ℝ) ^ (-(s / 2))) ^ b) :=
    (summable_geometric_iff_norm_lt_one (ξ := (2 : ℝ) ^ (-(s / 2)))).mpr
      (by rw [Real.norm_eq_abs, abs_of_pos hpos]; exact hlt)
  refine hgeo.congr (fun b => ?_)
  show ((2 : ℝ) ^ (-(s / 2))) ^ b = (2 : ℝ) ^ (-(s / 2) * b)
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(s / 2))) b,
    ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]

/-- `∑_n n^{-s}` converges for `s > 1`. -/
lemma gMaj_summable {s : ℝ} (hs : 1 < s) : Summable (gMaj s) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) := (Real.summable_nat_rpow_inv (p := s)).mpr hs
  refine h.congr (fun n => ?_)
  show ((n : ℝ) ^ s)⁻¹ = (n : ℝ) ^ (-s)
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

/-! ## 2. The arithmetic of `gnorm` and `IsC` -/

/-- `gnorm` of a unit is `1`. -/
lemma gnorm_eq_one_of_isUnit {u : GaussianInt} (hu : IsUnit u) : Work.FIPlan.gnorm u = 1 := by
  show u.norm.natAbs = 1
  exact (Zsqrtd.norm_eq_one_iff).mpr hu

/-- `gnorm ((1+i)^b) = 2^b`. -/
lemma gnorm_onePlusI_pow (b : ℕ) : Work.FIPlan.gnorm (Prop213Aux.onePlusI ^ b) = 2 ^ b := by
  induction b with
  | zero => simpa using gnorm_eq_one_of_isUnit (u := 1) isUnit_one
  | succ b ih =>
      rw [pow_succ, Work.FIArea7.gnorm_mul, ih, Prop213Aux.gnorm_onePlusI, pow_succ]

/-- `gnorm` of a natural number is its square. -/
lemma gnorm_natCast (n : ℕ) : Work.FIPlan.gnorm ((n : ℕ) : GaussianInt) = n ^ 2 := by
  have h := Work.FIArea7.norm_eq ((n : ℕ) : GaussianInt)
  have hn : ((Work.FIPlan.gnorm ((n : ℕ) : GaussianInt) : ℕ) : ℤ) = (n : ℤ) ^ 2 := by
    rw [h]; simp
  exact_mod_cast hn

/-- If `c = u·(1+i)^b·n` with `u` a unit then `|c|² = 2^b n²`. -/
lemma gnorm_eq_of_repr {c u : GaussianInt} {b n : ℕ} (hu : IsUnit u)
    (hc : c = u * Prop213Aux.onePlusI ^ b * (n : GaussianInt)) :
    Work.FIPlan.gnorm c = 2 ^ b * n ^ 2 := by
  rw [hc, Work.FIArea7.gnorm_mul, Work.FIArea7.gnorm_mul, gnorm_eq_one_of_isUnit hu,
    gnorm_onePlusI_pow, gnorm_natCast]
  ring

/-- An element of the coordinate box `gBox R` has `|z|² ≤ 2R²`. -/
lemma gnorm_le_two_mul_sq_of_mem_gBox {R : ℕ} {c : GaussianInt}
    (h : c ∈ Work.FIPlan.gBox (R : ℤ)) : Work.FIPlan.gnorm c ≤ 2 * R ^ 2 := by
  rw [Work.FIPlan.gBox, Finset.mem_image] at h
  obtain ⟨p, hp, rfl⟩ := h
  rw [show (Finset.Icc (-(R : ℤ)) (R : ℤ)).product (Finset.Icc (-(R : ℤ)) (R : ℤ))
      = (Finset.Icc (-(R : ℤ)) (R : ℤ) ×ˢ Finset.Icc (-(R : ℤ)) (R : ℤ)) from rfl] at hp
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
  have hsq : ((Work.FIPlan.gnorm (⟨p.1, p.2⟩ : GaussianInt) : ℕ) : ℤ)
      ≤ ((2 * R ^ 2 : ℕ) : ℤ) := by
    have hnorm := Work.FIArea7.norm_eq (⟨p.1, p.2⟩ : GaussianInt)
    have hp1 : p.1 ^ 2 ≤ (R : ℤ) ^ 2 := by
      have ha : 0 ≤ (R : ℤ) + p.1 := by linarith
      have hb : 0 ≤ (R : ℤ) - p.1 := by linarith
      nlinarith [mul_nonneg ha hb]
    have hp2 : p.2 ^ 2 ≤ (R : ℤ) ^ 2 := by
      have ha : 0 ≤ (R : ℤ) + p.2 := by linarith
      have hb : 0 ≤ (R : ℤ) - p.2 := by linarith
      nlinarith [mul_nonneg ha hb]
    rw [hnorm]
    push_cast
    linarith
  exact_mod_cast hsq

/-- The real power of `2^b n²` splits as `2^{-bs/2} n^{-s}`. -/
lemma rpow_two_pow_mul_sq (s : ℝ) (b n : ℕ) :
    ((2 ^ b * n ^ 2 : ℕ) : ℝ) ^ (-(s / 2))
      = (2 : ℝ) ^ (-(s / 2) * b) * (n : ℝ) ^ (-s) := by
  push_cast
  rw [Real.mul_rpow (x := (2 : ℝ) ^ b) (y := (n : ℝ) ^ 2) (z := -(s / 2))
    (by positivity) (by positivity)]
  congr 1
  · rw [← Real.rpow_natCast (2 : ℝ) b, ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    congr 1
    ring
  · rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    ring

/-! ## 3. The chosen `IsC`-representation and the counting bound -/

/-- Rearranged form of `IsC`: the representation `c = u·(1+i)^b·n` bundled as one tuple. -/
lemma isC_exists_repr {c : GaussianInt} (h : Prop213Aux.IsC c) :
    ∃ r : GaussianInt × ℕ × ℕ, IsUnit r.1 ∧ Odd r.2.2 ∧
      c = r.1 * Prop213Aux.onePlusI ^ r.2.1 * ((r.2.2 : ℕ) : GaussianInt) := by
  obtain ⟨u, hu, b, n, hn, hc⟩ := h
  exact ⟨(u, b, n), hu, hn, hc⟩

/-- The chosen representation `(u,b,n)` of `c` when `c ∈ C` (junk otherwise). -/
def reprOf (c : GaussianInt) : GaussianInt × ℕ × ℕ :=
  if h : Prop213Aux.IsC c then Classical.choose (isC_exists_repr h) else (1, 0, 1)

lemma reprOf_spec {c : GaussianInt} (h : Prop213Aux.IsC c) :
    IsUnit (reprOf c).1 ∧ Odd (reprOf c).2.2 ∧
      c = (reprOf c).1 * Prop213Aux.onePlusI ^ (reprOf c).2.1
            * ((reprOf c).2.2 : GaussianInt) := by
  rw [reprOf, dif_pos h]
  exact Classical.choose_spec (isC_exists_repr h)

/-- For fixed `(b,n)` there are at most `9` Gaussian integers of the form `u·(1+i)^b·n` with `u`
a unit: the unit is determined by the integer, and the units sit in the `9`-element box
`gBox 1`. -/
lemma card_filter_repr_le_nine (S : Finset GaussianInt) (b n : ℕ) :
    (S.filter (fun c => ∃ u : GaussianInt, IsUnit u ∧
      c = u * Prop213Aux.onePlusI ^ b * (n : GaussianInt))).card ≤ 9 := by
  set T : Finset GaussianInt := S.filter (fun c => ∃ u : GaussianInt, IsUnit u ∧
    c = u * Prop213Aux.onePlusI ^ b * (n : GaussianInt)) with hT
  let un : GaussianInt → GaussianInt := fun c =>
    if h : ∃ u : GaussianInt, IsUnit u ∧ c = u * Prop213Aux.onePlusI ^ b * (n : GaussianInt)
      then Classical.choose h else 1
  have hun_mem : ∀ c ∈ T, ∃ u : GaussianInt, IsUnit u ∧
      c = u * Prop213Aux.onePlusI ^ b * (n : GaussianInt) := by
    intro c hc
    have hc' := hc
    rw [hT] at hc'
    exact (Finset.mem_filter.mp hc').2
  have hun_unit : ∀ c ∈ T, IsUnit (un c) := by
    intro c hc
    have h := hun_mem c hc
    simp only [un, dif_pos h]
    exact (Classical.choose_spec h).1
  have hun_eq : ∀ c ∈ T, c = un c * Prop213Aux.onePlusI ^ b * (n : GaussianInt) := by
    intro c hc
    have h := hun_mem c hc
    simp only [un, dif_pos h]
    exact (Classical.choose_spec h).2
  have hun_gbox : ∀ c ∈ T, un c ∈ Work.FIPlan.gBox (1 : ℤ) := by
    intro c hc
    have hu := hun_unit c hc
    have hgn : Work.FIPlan.gnorm (un c) = 1 := gnorm_eq_one_of_isUnit hu
    have hc1 : (un c).re ^ 2 + (un c).im ^ 2 = (1 : ℤ) := by
      have hh := Work.FIArea7.norm_eq (un c)
      rw [hgn] at hh
      exact hh.symm
    have hre : -1 ≤ (un c).re ∧ (un c).re ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (un c).re, sq_nonneg (un c).im]
    have him : -1 ≤ (un c).im ∧ (un c).im ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (un c).re, sq_nonneg (un c).im]
    rw [Work.FIPlan.gBox, Finset.mem_image]
    refine ⟨((un c).re, (un c).im), ?_, rfl⟩
    rw [show (Finset.Icc (-1 : ℤ) 1).product (Finset.Icc (-1 : ℤ) 1)
        = (Finset.Icc (-1 : ℤ) 1 ×ˢ Finset.Icc (-1 : ℤ) 1) from rfl]
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨hre.1, hre.2⟩, ⟨him.1, him.2⟩⟩
  have hinj : Set.InjOn un ↑T := by
    intro c hc c' hc' heq
    rw [hun_eq c hc, hun_eq c' hc', heq]
  have hcard : T.card ≤ (Work.FIPlan.gBox (1 : ℤ)).card :=
    Finset.card_le_card_of_injOn un (fun c hc => hun_gbox c hc) hinj
  have h9 : (Work.FIPlan.gBox (1 : ℤ)).card = 9 := by decide
  calc T.card ≤ (Work.FIPlan.gBox (1 : ℤ)).card := hcard
    _ = 9 := h9

/-! ## 4. The box sum -/

/-- **The box sum is bounded by a constant independent of `R`.** -/
lemma sum_gBox_filter_le {s : ℝ} (hs : 1 < s) (R : ℕ) :
    ∑ c ∈ (Work.FIPlan.gBox (R : ℤ)).filter Prop213Aux.IsC,
        ((Work.FIPlan.gnorm c : ℝ)) ^ (-(s / 2))
      ≤ 9 * ((∑' b : ℕ, fMaj s b) * (∑' n : ℕ, gMaj s n)) := by
  classical
  have hs0 : (0 : ℝ) < s := by linarith
  have hBsum : Summable (fMaj s) := fMaj_summable hs0
  have hNsum : Summable (gMaj s) := gMaj_summable hs
  set B0 : ℕ := 2 * R ^ 2 + 1 with hB0
  set Rect : Finset (ℕ × ℕ) := (Finset.range B0) ×ˢ (Finset.range B0) with hRect
  set Φ : GaussianInt → ℕ × ℕ := fun c => ((reprOf c).2.1, (reprOf c).2.2) with hΦ
  set S : Finset GaussianInt := (Work.FIPlan.gBox (R : ℤ)).filter Prop213Aux.IsC with hS
  have hIsC : ∀ c ∈ S, Prop213Aux.IsC c := by
    intro c hc
    rw [hS] at hc
    exact (Finset.mem_filter.mp hc).2
  -- `Φ` maps `S` into the rectangle
  have hΦmem : ∀ c ∈ S, Φ c ∈ Rect := by
    intro c hc
    have hcbox : c ∈ Work.FIPlan.gBox (R : ℤ) := by
      have hc' := hc
      rw [hS] at hc'
      exact (Finset.mem_filter.mp hc').1
    have hgn : Work.FIPlan.gnorm c ≤ 2 * R ^ 2 := gnorm_le_two_mul_sq_of_mem_gBox hcbox
    obtain ⟨hu, hodd, hrepr⟩ := reprOf_spec (hIsC c hc)
    have hgn_eq : Work.FIPlan.gnorm c = 2 ^ (reprOf c).2.1 * (reprOf c).2.2 ^ 2 :=
      gnorm_eq_of_repr hu hrepr
    have hn1 : 1 ≤ (reprOf c).2.2 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hpow : 1 ≤ 2 ^ (reprOf c).2.1 := Nat.one_le_pow _ 2 (by norm_num)
    have hsq1 : 1 ≤ (reprOf c).2.2 ^ 2 := one_le_pow₀ hn1
    have hb_le : (reprOf c).2.1 ≤ 2 * R ^ 2 := by
      calc (reprOf c).2.1 ≤ 2 ^ (reprOf c).2.1 := le_of_lt Nat.lt_two_pow_self
        _ = 2 ^ (reprOf c).2.1 * 1 := (mul_one _).symm
        _ ≤ 2 ^ (reprOf c).2.1 * (reprOf c).2.2 ^ 2 := Nat.mul_le_mul_left _ hsq1
        _ = Work.FIPlan.gnorm c := hgn_eq.symm
        _ ≤ 2 * R ^ 2 := hgn
    have hn_le : (reprOf c).2.2 ≤ 2 * R ^ 2 := by
      calc (reprOf c).2.2 ≤ (reprOf c).2.2 ^ 2 := Nat.le_self_pow (by norm_num) _
        _ = 2 ^ 0 * (reprOf c).2.2 ^ 2 := by norm_num
        _ ≤ 2 ^ (reprOf c).2.1 * (reprOf c).2.2 ^ 2 :=
            Nat.mul_le_mul_right _ hpow
        _ = Work.FIPlan.gnorm c := hgn_eq.symm
        _ ≤ 2 * R ^ 2 := hgn
    simp only [hΦ, hRect, hB0, Finset.mem_product, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hb_le, Nat.lt_succ_of_le hn_le⟩
  -- each fibre has at most `9` elements
  have hfib : ∀ q ∈ Rect, (S.filter (fun c => Φ c = q)).card ≤ 9 := by
    intro q hq
    have hsub : S.filter (fun c => Φ c = q) ⊆ S.filter (fun c => ∃ u : GaussianInt,
        IsUnit u ∧ c = u * Prop213Aux.onePlusI ^ q.1 * ((q.2 : ℕ) : GaussianInt)) := by
      intro c hc
      rw [Finset.mem_filter] at hc ⊢
      obtain ⟨hcS, hcq⟩ := hc
      obtain ⟨hu, hodd, hrepr⟩ := reprOf_spec (hIsC c hcS)
      have hcq' := hcq
      rw [hΦ] at hcq'
      have hb : (reprOf c).2.1 = q.1 := by simpa using congrArg Prod.fst hcq'
      have hn : (reprOf c).2.2 = q.2 := by simpa using congrArg Prod.snd hcq'
      exact ⟨hcS, (reprOf c).1, hu, by simpa only [hb, hn] using hrepr⟩
    calc (S.filter (fun c => Φ c = q)).card
        ≤ (S.filter (fun c => ∃ u : GaussianInt, IsUnit u ∧
            c = u * Prop213Aux.onePlusI ^ q.1 * ((q.2 : ℕ) : GaussianInt))).card :=
          Finset.card_le_card hsub
      _ ≤ 9 := card_filter_repr_le_nine S q.1 q.2
  -- on each fibre the summand is constant
  have hpt : ∀ q ∈ Rect, ∀ c ∈ S.filter (fun c => Φ c = q),
      ((Work.FIPlan.gnorm c : ℝ)) ^ (-(s / 2)) = wMaj s q := by
    intro q hq c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨hcS, hcq⟩ := hc
    obtain ⟨hu, hodd, hrepr⟩ := reprOf_spec (hIsC c hcS)
    have hcq' := hcq
    rw [hΦ] at hcq'
    have hb : (reprOf c).2.1 = q.1 := by simpa using congrArg Prod.fst hcq'
    have hn : (reprOf c).2.2 = q.2 := by simpa using congrArg Prod.snd hcq'
    rw [gnorm_eq_of_repr hu hrepr, hb, hn]
    show ((2 ^ q.1 * q.2 ^ 2 : ℕ) : ℝ) ^ (-(s / 2))
        = (2 : ℝ) ^ (-(s / 2) * q.1) * (q.2 : ℝ) ^ (-s)
    exact rpow_two_pow_mul_sq s q.1 q.2
  -- the arithmetic of the rectangle sum
  have hwRect : ∑ q ∈ Rect, wMaj s q
      = (∑ b ∈ Finset.range B0, fMaj s b) * (∑ n ∈ Finset.range B0, gMaj s n) := by
    rw [hRect, Finset.sum_product]
    exact (Finset.sum_mul_sum (Finset.range B0) (Finset.range B0) (fMaj s) (gMaj s)).symm
  have hrect9 : ∑ q ∈ Rect, 9 * wMaj s q
      = 9 * ((∑ b ∈ Finset.range B0, fMaj s b) * (∑ n ∈ Finset.range B0, gMaj s n)) := by
    rw [← Finset.mul_sum Rect (wMaj s) 9, hwRect]
  -- partial sums are dominated by the `tsum`s
  have hBle : ∑ b ∈ Finset.range B0, fMaj s b ≤ ∑' b : ℕ, fMaj s b :=
    Summable.sum_le_tsum (Finset.range B0) (fun b _ => fMaj_nonneg s b) hBsum
  have hNle : ∑ n ∈ Finset.range B0, gMaj s n ≤ ∑' n : ℕ, gMaj s n :=
    Summable.sum_le_tsum (Finset.range B0) (fun n _ => gMaj_nonneg s n) hNsum
  have hBN : (∑ b ∈ Finset.range B0, fMaj s b) * (∑ n ∈ Finset.range B0, gMaj s n)
      ≤ (∑' b : ℕ, fMaj s b) * (∑' n : ℕ, gMaj s n) :=
    mul_le_mul hBle hNle (Finset.sum_nonneg (fun n _ => gMaj_nonneg s n))
      (tsum_nonneg (fun b => fMaj_nonneg s b))
  calc ∑ c ∈ S, ((Work.FIPlan.gnorm c : ℝ)) ^ (-(s / 2))
      = ∑ q ∈ Rect, ∑ c ∈ S.filter (fun c => Φ c = q), ((Work.FIPlan.gnorm c : ℝ)) ^ (-(s / 2)) :=
        (Finset.sum_fiberwise_of_maps_to hΦmem
          (fun c => ((Work.FIPlan.gnorm c : ℝ)) ^ (-(s / 2)))).symm
    _ ≤ ∑ q ∈ Rect, 9 * wMaj s q := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        rw [Finset.sum_congr rfl (fun c hc => hpt q hq c hc), Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib q hq) (wMaj_nonneg s q)
    _ = 9 * ((∑ b ∈ Finset.range B0, fMaj s b) * (∑ n ∈ Finset.range B0, gMaj s n)) := hrect9
    _ ≤ 9 * ((∑' b : ℕ, fMaj s b) * (∑' n : ℕ, gMaj s n)) :=
        mul_le_mul_of_nonneg_left hBN (by norm_num)

/-! ## 5. The theorem -/

theorem sum_CBox_rpow_le {s : ℝ} (hs : 1 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ∑ c ∈ Pub213.CBox X, ((Work.FIPlan.gnorm c : ℝ)) ^ (-(s / 2)) ≤ K := by
  refine ⟨9 * ((∑' b : ℕ, fMaj s b) * (∑' n : ℕ, gMaj s n)), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑' b : ℕ, fMaj s b := tsum_nonneg (fun b => fMaj_nonneg s b)
    have h2 : (0 : ℝ) ≤ ∑' n : ℕ, gMaj s n := tsum_nonneg (fun n => gMaj_nonneg s n)
    exact mul_nonneg (by norm_num) (mul_nonneg h1 h2)
  · intro X hX
    show ∑ c ∈ (Work.FIPlan.gBox (⌈Real.sqrt X⌉₊ : ℤ)).filter Prop213Aux.IsC,
        ((Work.FIPlan.gnorm c : ℝ)) ^ (-(s / 2))
      ≤ 9 * ((∑' b : ℕ, fMaj s b) * (∑' n : ℕ, gMaj s n))
    exact sum_gBox_filter_le hs _

end

end Work.FIArea7.Pub213
