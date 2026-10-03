/-
# `Work.FITop4.Red5.window_sharp_count` — the sharp dyadic window count

For a primitive Gaussian integer `z` with `N = |z|² ≥ 1` and `M ≥ 1`, the dyadic window sum

  `Σ_{M < |w|² ≤ 2M} Z(Re w z)`

is `≪ M^{3/4} N^{-1/4} + (M N)^{1/4}`.

This is the `Finset.Icc (Mn+1) (2Mn)`-window form of `sum_Zint_annM_prim_le`, proved directly for
the window (without going through `Work.FITop.Params`, which cannot realise an arbitrary `Mn` as its
outer scale `M`).  The three ingredients are the same:

* `window_eq_winAnn` — the `m`-fibration of the window equals the Gaussian annulus `winAnn Mn`;
* `winAnn_sum_eq_fiber_sum` — the `Z`-weighted sum is the sum over `c` of the `c`-fibres
  (`Re(wz) = c²`);
* `winAnn_per_c_bound` — each `c`-fibre has at most `2√(2M/N) + 1` points.

The closing real inequality is `arith_bound` of `sum_Zint_annM_prim_le`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.sum_Zint_annM_prim_le
import Submission.Work.FIArea1.count_annulus
import Submission.Work.FIArea2.hits_card_le
import Submission.Work.FIArea2.sum_gBox_eq_sum_congruences

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The dyadic Gaussian annulus -/

/-- The dyadic annulus `A < |w|² ≤ 2A`, cut out of the box `gBox (2A)`. -/
def winAnn (A : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (((2 * A : ℕ) : ℤ))).filter
    (fun w => A < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ 2 * A)

lemma mem_winAnn {A : ℕ} {w : GaussianInt} :
    w ∈ winAnn A ↔ w ∈ Work.FIPlan.gBox (((2 * A : ℕ) : ℤ)) ∧
      A < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ 2 * A :=
  Finset.mem_filter

/-- The `m`-fibre of the window annulus `winAnn A` is the sphere `wSph m`. -/
lemma winAnn_filter_gnorm_eq {A m : ℕ} (hm1 : A + 1 ≤ m) (hm2 : m ≤ 2 * A) :
    (winAnn A).filter (fun w => Work.FIPlan.gnorm w = m) = wSph m := by
  have hm1' : 1 ≤ m := by omega
  have h2A1 : 1 ≤ 2 * A := by omega
  have hmsq : m ≤ m ^ 2 :=
    calc m = m * 1 := (mul_one m).symm
      _ ≤ m * m := Nat.mul_le_mul_left m hm1'
      _ = m ^ 2 := (pow_two m).symm
  have hm2sq : m ≤ (2 * A) ^ 2 :=
    calc m ≤ 2 * A := hm2
      _ = (2 * A) * 1 := (mul_one (2 * A)).symm
      _ ≤ (2 * A) * (2 * A) := Nat.mul_le_mul_left (2 * A) h2A1
      _ = (2 * A) ^ 2 := (pow_two (2 * A)).symm
  ext w
  rw [Finset.mem_filter, mem_winAnn, wSph, Finset.mem_filter]
  constructor
  · rintro ⟨⟨-, -, -⟩, hgn⟩
    exact ⟨mem_gBox_of_norm_sq hgn hmsq, hgn⟩
  · rintro ⟨-, hgn⟩
    refine ⟨⟨mem_gBox_of_norm_sq hgn hm2sq, ?_, ?_⟩, hgn⟩
    · rw [hgn]; omega
    · rw [hgn]; omega

/-- **The `m`-fibration of the window.**  The window annulus sum is the dyadic `m`-window of the
sphere sums. -/
lemma window_eq_winAnn {A : ℕ} (F : GaussianInt → ℝ) :
    (∑ w ∈ winAnn A, F w) = ∑ m ∈ Finset.Icc (A + 1) (2 * A), ∑ w ∈ wSph m, F w := by
  have hmaps : ∀ w ∈ winAnn A, Work.FIPlan.gnorm w ∈ Finset.Icc (A + 1) (2 * A) := by
    intro w hw
    obtain ⟨-, hlt, hle⟩ := mem_winAnn.mp hw
    rw [Finset.mem_Icc]
    exact ⟨by omega, hle⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_Icc] at hm
  rw [winAnn_filter_gnorm_eq hm.1 hm.2]

/-! ## 1. The `c`-fibre decomposition -/

/-- **Fibre decomposition of the `Z`-weighted window sum.**  Writing `Z(Re wz)` as the number of
roots `c` of `c² = Re(wz)` turns the sum into the sum over `c` of the cardinalities of the fibres
`{w ∈ winAnn A : Re(wz) = c²}`. -/
lemma winAnn_sum_eq_fiber_sum (A : ℕ) (z : GaussianInt) (K : ℕ)
    (hroot : ∀ w ∈ winAnn A, ∀ c : ℤ, c ^ 2 = Work.FIPlan.cForm w z →
      c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)) :
    (∑ w ∈ winAnn A, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      = ∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (((winAnn A).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℝ) := by
  classical
  have h1 : ∀ w ∈ winAnn A,
      (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
        = ∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (if c ^ 2 = Work.FIPlan.cForm w z then (1 : ℝ) else 0) :=
    fun w hw => Work.FIArea2.Zint_eq_Cnt K (Work.FIPlan.cForm w z) (hroot w hw)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_boole _ _

/-! ## 2. The per-`c` fibre bound -/

/-- **The per-line bound for the window.**  On a coset of `ker (cForm · z)` inside the annulus
`A < |w|² ≤ 2A`, the `psi`-coordinate takes at most `2√(2A/N) + 1` values (`N = |z|²`).

This is `per_c_gen_bound_prim` with `Pa.M` replaced by the window scale `A` and the annulus
hypothesis by the raw norm bound, so that no `Work.FITop.Params` is needed. -/
lemma winAnn_per_c_bound {A : ℕ} {z : GaussianInt} {T : Finset GaussianInt} {v : ℤ}
    (hcop : IsCoprime z.re z.im) (hnz : (Work.FIPlan.gnorm z : ℤ) ≠ 0)
    (hT : ∀ w ∈ T, w ∈ winAnn A ∧ Work.FIPlan.cForm w z = v) :
    (T.card : ℝ) ≤ 2 * Real.sqrt (2 * (A : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1 := by
  have hnz0 : Work.FIPlan.gnorm z ≠ 0 := by
    intro h0
    exact hnz (by rw [h0]; norm_num)
  have hnzR : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hnz0
  by_cases hne : T.Nonempty
  · obtain ⟨w₀, hw₀⟩ := hne
    set B : Finset ℤ := T.image (Work.FIArea1.psi z) with hB
    have hinj : Set.InjOn (Work.FIArea1.psi z) (T : Set GaussianInt) := by
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      exact Work.FIArea1.psi_eq_of_cForm_eq hcop hnz (by rw [(hT a ha).2, (hT b hb).2]) hab
    have hBcard : B.card = T.card := by rw [hB]; exact Finset.card_image_of_injOn hinj
    set R : ℝ := Real.sqrt (2 * (A : ℝ) * (Work.FIPlan.gnorm z : ℝ)) with hR
    have hRnn : 0 ≤ R := Real.sqrt_nonneg _
    have hdiv : ∀ t ∈ B, ((Work.FIPlan.gnorm z) : ℤ) ∣ (t - Work.FIArea1.psi z w₀) := by
      intro t ht
      rw [hB, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      have hcw : Work.FIPlan.cForm w z = Work.FIPlan.cForm w₀ z := by
        rw [(hT w hw).2, (hT w₀ hw₀).2]
      exact Work.FIArea1.nz_dvd_psi_sub hcop hcw
    have hint : ∀ t ∈ B, |(t : ℝ)| ≤ R := by
      intro t ht
      rw [hB, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      have hgt : (Work.FIPlan.gnorm w : ℝ) ≤ 2 * (A : ℝ) := by
        have h := (mem_winAnn.mp (hT w hw).1).2.2
        exact_mod_cast h
      have hgz0 : (0 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := le_of_lt hnzR
      have hsq : (((Work.FIArea1.psi z w : ℤ) : ℝ)) ^ 2
          ≤ 2 * (A : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
        have h1 := Work.FIArea1.psi_sq_le w z
        have h2 : (((Work.FIArea1.psi z w : ℤ) : ℝ)) ^ 2
            ≤ (((Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h2
        calc (((Work.FIArea1.psi z w : ℤ) : ℝ)) ^ 2
              ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := h2
          _ ≤ (2 * (A : ℝ)) * (Work.FIPlan.gnorm z : ℝ) :=
              mul_le_mul_of_nonneg_right hgt hgz0
      rw [hR]
      exact Real.abs_le_sqrt hsq
    have hmain := Work.FIArea1.card_int_le_shifted_ap (U := B)
        (t0 := Work.FIArea1.psi z w₀) (m := Work.FIPlan.gnorm z)
        (Nat.pos_of_ne_zero hnz0) hRnn hdiv hint
    rw [hBcard] at hmain
    have hstep : 2 * R / (Work.FIPlan.gnorm z : ℝ)
        ≤ 2 * Real.sqrt (2 * (A : ℝ) / (Work.FIPlan.gnorm z : ℝ)) := by
      have hsqeq : (R / (Work.FIPlan.gnorm z : ℝ)) ^ 2
          = 2 * (A : ℝ) / (Work.FIPlan.gnorm z : ℝ) := by
        rw [hR, div_pow, Real.sq_sqrt (by positivity)]
        field_simp
      have hnn : 0 ≤ R / (Work.FIPlan.gnorm z : ℝ) := by positivity
      have heq : R / (Work.FIPlan.gnorm z : ℝ)
          = Real.sqrt (2 * (A : ℝ) / (Work.FIPlan.gnorm z : ℝ)) := by
        rw [← Real.sqrt_sq hnn, hsqeq]
      rw [show 2 * R / (Work.FIPlan.gnorm z : ℝ)
            = 2 * (R / (Work.FIPlan.gnorm z : ℝ)) by ring, heq]
    linarith [hmain, hstep]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ 2 * Real.sqrt (2 * (A : ℝ) / (Work.FIPlan.gnorm z : ℝ)) := by positivity
    linarith

/-! ## 3. The window count -/

/-- **The sharp dyadic window count.**  For `M = Mn` and `N = |z|²` (primitive `z`, `N ≥ 1`),

  `Σ_{M < |w|² ≤ 2M} Z(Re w z) ≤ 64 (M^{3/4} N^{-1/4} + (M N)^{1/4})`. -/
theorem window_sharp_count :
    ∃ c : ℝ, 0 < c ∧ ∀ (Mn : ℕ) (z : GaussianInt), 1 ≤ Mn → Work.FIPlan.IsPrimitive z →
    1 ≤ Work.FIPlan.gnorm z →
    (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
        (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ c * ((Mn : ℝ) ^ ((3:ℝ)/4) * ((Work.FIPlan.gnorm z : ℝ)) ^ (-(1:ℝ)/4)
          + ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4)) := by
  refine ⟨64, by norm_num, ?_⟩
  intro Mn z hMn hprim hz1
  rw [← window_eq_winAnn (A := Mn) (fun w => (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))]
  have hN1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hz1
  have hnz : (Work.FIPlan.gnorm z : ℤ) ≠ 0 := by
    have h : Work.FIPlan.gnorm z ≠ 0 := Nat.one_le_iff_ne_zero.mp hz1
    exact_mod_cast h
  have hcop : IsCoprime z.re z.im := Work.FIArea2.isCoprime_re_im_of_isCoprime_star hprim
  set B : ℝ := (2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) with hBdef
  set K : ℕ := ⌈B⌉₊ with hKdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hKle : (K : ℝ) ≤ B + 1 := by rw [hKdef]; exact le_of_lt (Nat.ceil_lt_add_one hBnn)
  -- every integer root `c` of `Re(wz) = c²` lies in `[-K,K]`
  have hroot : ∀ w ∈ winAnn Mn, ∀ c : ℤ, c ^ 2 = Work.FIPlan.cForm w z →
      c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro w hw c hc
    obtain ⟨-, -, hle⟩ := mem_winAnn.mp hw
    have hgnw : (Work.FIPlan.gnorm w : ℝ) ≤ 2 * (Mn : ℝ) := by exact_mod_cast hle
    have hprod : (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ)
        = ((w * z).re : ℝ) ^ 2 + ((w * z).im : ℝ) ^ 2 := by
      rw [← annM_prim_gnorm_mul_real w z, annM_prim_gnorm_eq_coords]
    have hre : ((w * z).re : ℝ) = (c : ℝ) ^ 2 := by
      have h : ((Work.FIPlan.cForm w z : ℤ) : ℝ) = (c : ℝ) ^ 2 := by
        rw [← hc]; push_cast; ring
      simpa only [Work.FIPlan.cForm] using h
    have hc4 : ((c : ℝ)) ^ 4 ≤ 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
      have hstep : ((c : ℝ) ^ 2) ^ 2
          ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
        rw [← hre, hprod]
        nlinarith [sq_nonneg ((w * z).im : ℝ)]
      have hstep2 : (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ)
          ≤ (2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ) :=
        mul_le_mul_of_nonneg_right hgnw (by positivity)
      calc ((c : ℝ)) ^ 4 = ((c : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := hstep
        _ ≤ (2 * (Mn : ℝ)) * (Work.FIPlan.gnorm z : ℝ) := hstep2
        _ = 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by ring
    have hB4 : B ^ 4 = 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
      rw [hBdef,
        ← Real.rpow_natCast ((2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) 4,
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ))]
      norm_num
    have hcabs : |(c : ℝ)| ≤ B := by
      refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hBnn ?_
      rw [hB4]
      calc |(c : ℝ)| ^ 4 = ((c : ℝ)) ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
        _ ≤ 2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ) := hc4
    have hcK : |(c : ℝ)| ≤ (K : ℝ) := le_trans hcabs (by rw [hKdef]; exact Nat.le_ceil B)
    rw [Finset.mem_Icc]
    constructor
    · have h := (abs_le.mp hcK).1
      have h' : ((-(K : ℤ)) : ℝ) ≤ (c : ℝ) := by push_cast; linarith
      exact_mod_cast h'
    · have h := (abs_le.mp hcK).2
      have h' : (c : ℝ) ≤ ((K : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h'
  rw [winAnn_sum_eq_fiber_sum Mn z K hroot]
  have hfib : ∀ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ((((winAnn Mn).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ)
        ≤ 2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1 := by
    intro c _
    refine winAnn_per_c_bound (A := Mn) (z := z)
      (T := (winAnn Mn).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z))
      (v := c ^ 2) hcop hnz ?_
    intro w hw
    rw [Finset.mem_filter] at hw
    exact ⟨hw.1, hw.2.symm⟩
  have hcardI : (((Finset.Icc (-(K : ℤ)) (K : ℤ))).card : ℝ) = 2 * (K : ℝ) + 1 := by
    rw [Int.card_Icc]
    have htoNat : ((K : ℤ) + 1 - (-(K : ℤ))).toNat = 2 * K + 1 := by
      have h : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h, Int.toNat_natCast]
    rw [htoNat]
    push_cast
    ring
  have h1 : (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        ((((winAnn Mn).filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ))
      ≤ (2 * (K : ℝ) + 1)
          * (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) := by
    calc _ ≤ ∑ _c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) :=
          Finset.sum_le_sum hfib
      _ = (((Finset.Icc (-(K : ℤ)) (K : ℤ))).card : ℝ)
            * (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (K : ℝ) + 1)
            * (2 * Real.sqrt (2 * (Mn : ℝ) / (Work.FIPlan.gnorm z : ℝ)) + 1) := by rw [hcardI]
  have hKle' : (K : ℝ) ≤ (2 * (Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4) + 1 := by
    rw [← hBdef]; exact hKle
  exact h1.trans (arith_bound (M := (Mn : ℝ)) (N := (Work.FIPlan.gnorm z : ℝ)) (K := (K : ℝ))
    (by exact_mod_cast hMn) hN1 hKle')

end

end Work.FITop4.Red5
