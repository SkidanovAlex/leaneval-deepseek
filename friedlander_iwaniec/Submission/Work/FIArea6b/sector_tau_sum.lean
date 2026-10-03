/-
# `Work.FIArea6b.sector_tau_sum`

The sector divisor sum: for `N ≥ 1` and `0 ≤ θ ≤ 1`, the sum of `τ(|z|²)` over the Gaussian
integers `z` with norm in the annulus `(N, (1+θ)N]`, argument in a sector of width `2πθ` and
*squarefree* norm is `O((√N + θN) log^9(2+N))`.

The proof is elementary and goes through the divisor pairing `τ(|z|²) ≤ #{w : w ∣ z}` (valid
because `|z|²` is squarefree, `Work.FIArea6b.gaussian_divisor_count`): the pairs `(w, z = w·u)`
are counted by grouping according to the smaller of `|w|`, `|u|`.  For a fixed factor the other
one lies in a *sector annulus*, which is contained in a disc of radius `≲ θ√N/|u|` (a
"chord ≤ arc" + radial width estimate); a disc of radius `ρ` contains at most `(2ρ+1)²`
Gaussian integers.  Summing `(2·10θ√(N/k)+1)²` over the possible `k = |u|² ≤ √((1+θ)N)`
requires the two elementary lattice sums `Σ 1/|u|² = O(log)` and `Σ 1/|u| = O(N^{1/4} log)`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6b.gaussian_divisor_count

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6b

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Arithmetic of `gnorm` -/

/-- `gnorm` is multiplicative. -/
lemma gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  rw [Work.FIPlan.gnorm, Work.FIPlan.gnorm, Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- A Gaussian integer of norm `0` is `0`. -/
lemma eq_zero_of_gnorm_eq_zero (z : GaussianInt) (h : Work.FIPlan.gnorm z = 0) : z = 0 := by
  have hnorm : z.norm = z.re * z.re + z.im * z.im := by rw [Zsqrtd.norm]; ring
  have hz : z.norm = 0 := by
    rw [Work.FIPlan.gnorm] at h
    exact Int.natAbs_eq_zero.mp h
  have h2 : z.re * z.re + z.im * z.im = 0 := by rw [← hnorm]; exact hz
  have hr : z.re = 0 := by nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]
  have hi : z.im = 0 := by nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]
  exact Zsqrtd.ext hr hi

/-- A Gaussian integer of norm `0` is `0`. -/
lemma gnorm_eq_zero_iff (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 :=
  ⟨eq_zero_of_gnorm_eq_zero z, by rintro rfl; simp [Work.FIPlan.gnorm]⟩

/-- Norms are positive on nonzero Gaussian integers. -/
lemma one_le_gnorm_of_ne_zero (z : GaussianInt) (h : z ≠ 0) : 1 ≤ Work.FIPlan.gnorm z :=
  Nat.one_le_iff_ne_zero.mpr fun hz => h ((gnorm_eq_zero_iff z).mp hz)

/-- Multiplicativity of `gnorm` combined with positivity: a product is nonzero iff both factors
are. -/
lemma gnorm_mul_pos {z w : GaussianInt} (h : 0 < Work.FIPlan.gnorm (z * w)) :
    0 < Work.FIPlan.gnorm z ∧ 0 < Work.FIPlan.gnorm w := by
  rw [gnorm_mul] at h
  exact ⟨Nat.pos_of_ne_zero fun hz => by simp [hz] at h, Nat.pos_of_ne_zero fun hw => by simp [hw] at h⟩

/-! ## 1. The sector annulus is contained in a disc -/

/-- **A sector annulus lies in a disc.**  If `z` has norm in `(N, (1+θ)N]` and argument in
`(φ, φ+2πθ]`, then `z` is within `10θ√N` of the point of modulus `√((1+θ)N)` at the mid-angle
`φ + πθ` of the sector.  Radially the annulus is `θ√N` thick (`√(1+θ) ≤ 1+θ`) and angularly the
chord is at most the arc, `√((1+θ)N)·πθ ≤ √2 π θ√N`. -/
lemma sector_annulus_disc (N θ φ : ℝ) (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (z : GaussianInt)
    (hlo : N < ((Work.FIPlan.gnorm z : ℕ) : ℝ))
    (hhi : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + θ) * N)
    (harglo : φ < Complex.arg z.toComplex)
    (hargle : Complex.arg z.toComplex ≤ φ + 2 * Real.pi * θ) :
    ‖z.toComplex - (Real.sqrt ((1 + θ) * N) : ℂ)
        * Complex.exp (((φ + Real.pi * θ : ℝ) : ℂ) * Complex.I)‖
      ≤ 10 * θ * Real.sqrt N := by
  set r : ℝ := ‖z.toComplex‖ with hr
  set s : ℝ := Real.sqrt ((1 + θ) * N) with hs
  set ψ : ℝ := Complex.arg z.toComplex with hψ
  set ψc : ℝ := φ + Real.pi * θ with hψc
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr_eq : r = Real.sqrt (((Work.FIPlan.gnorm z : ℕ) : ℝ)) := by
    rw [hr]; exact Work.FIArea4.norm_toComplex_eq_sqrt_gnorm z
  have hz_eq : z.toComplex = (r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I z.toComplex
    rw [← hr, ← hψ] at h
    exact h.symm
  have hr_ge : Real.sqrt N ≤ r := by
    rw [hr_eq]; exact Real.sqrt_le_sqrt (by linarith)
  have hr_le : r ≤ s := by
    rw [hr_eq, hs]; exact Real.sqrt_le_sqrt hhi
  have hsqrt1 : Real.sqrt (1 + θ) ≤ 1 + θ := by
    have h1 : (0 : ℝ) ≤ 1 + θ := by linarith
    calc Real.sqrt (1 + θ) ≤ Real.sqrt ((1 + θ) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 1 + θ := Real.sqrt_sq h1
  have hs_eq : s = Real.sqrt (1 + θ) * Real.sqrt N := by
    rw [hs, Real.sqrt_mul (by linarith)]
  have hsr : s - r ≤ θ * Real.sqrt N := by
    calc s - r ≤ s - Real.sqrt N := by linarith
      _ = (Real.sqrt (1 + θ) - 1) * Real.sqrt N := by rw [hs_eq]; ring
      _ ≤ θ * Real.sqrt N := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg N)
          linarith
  have hrad : |r - s| ≤ θ * Real.sqrt N := by
    rw [abs_of_nonpos (by linarith : r - s ≤ 0)]
    linarith
  have hang : |ψ - ψc| ≤ Real.pi * θ := by
    rw [abs_le, hψ, hψc]
    constructor <;> linarith
  have hexp : ‖Complex.exp ((ψ : ℂ) * Complex.I) - Complex.exp ((ψc : ℂ) * Complex.I)‖
      ≤ |ψ - ψc| := Work.FIArea4.norm_exp_sub_exp_le ψ ψc
  have hs_le : s ≤ Real.sqrt 2 * Real.sqrt N := by
    rw [hs_eq]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg N)
  have hsqrt2 : Real.sqrt 2 < 1.5 := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have hmain : ‖z.toComplex - (s : ℂ) * Complex.exp ((ψc : ℂ) * Complex.I)‖
      = ‖(r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)
          - (s : ℂ) * Complex.exp ((ψc : ℂ) * Complex.I)‖ := by
    rw [hz_eq]
  rw [hmain]
  calc ‖(r : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)
          - (s : ℂ) * Complex.exp ((ψc : ℂ) * Complex.I)‖
      = ‖(((r - s : ℝ)) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)
          + (s : ℂ) * (Complex.exp ((ψ : ℂ) * Complex.I)
              - Complex.exp ((ψc : ℂ) * Complex.I))‖ := by
        congr 1
        push_cast
        ring
    _ ≤ ‖(((r - s : ℝ)) : ℂ) * Complex.exp ((ψ : ℂ) * Complex.I)‖
          + ‖(s : ℂ) * (Complex.exp ((ψ : ℂ) * Complex.I)
              - Complex.exp ((ψc : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ = |r - s| + s * ‖Complex.exp ((ψ : ℂ) * Complex.I)
            - Complex.exp ((ψc : ℂ) * Complex.I)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Work.FIArea4.norm_ofReal_abs, Work.FIArea4.norm_ofReal_abs, abs_of_nonneg hs0]
    _ ≤ θ * Real.sqrt N + s * |ψ - ψc| := by
        have h2 : s * ‖Complex.exp ((ψ : ℂ) * Complex.I) - Complex.exp ((ψc : ℂ) * Complex.I)‖
            ≤ s * |ψ - ψc| := mul_le_mul_of_nonneg_left hexp hs0
        linarith
    _ ≤ θ * Real.sqrt N + (Real.sqrt 2 * Real.sqrt N) * (Real.pi * θ) := by
        have h3 : s * |ψ - ψc| ≤ (Real.sqrt 2 * Real.sqrt N) * (Real.pi * θ) :=
          mul_le_mul hs_le hang (abs_nonneg _) (by positivity)
        linarith
    _ = θ * Real.sqrt N * (1 + Real.sqrt 2 * Real.pi) := by ring
    _ ≤ 10 * θ * Real.sqrt N := by
        have hpi : Real.pi < 4 := Real.pi_lt_four
        have h6 : Real.sqrt 2 * Real.pi < 6 := by
          nlinarith [hsqrt2, hpi, Real.pi_pos.le, Real.sqrt_nonneg 2]
        have ht : 0 ≤ θ * Real.sqrt N := mul_nonneg hθ (Real.sqrt_nonneg N)
        nlinarith [h6, ht]



/-! ## 2. Counting a disc, and two elementary lattice sums -/

/-- **Disc bound**: a finite set of Gaussian integers contained in a disc of radius `ρ` has at
most `(2ρ+1)²` elements (real and imaginary parts lie in intervals of length `2ρ`). -/
theorem card_le_disc (A : Finset GaussianInt) (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ z ∈ A, ‖z.toComplex - c‖ ≤ ρ) : (A.card : ℝ) ≤ (2 * ρ + 1) ^ 2 :=
  Work.FIArea4.card_le_of_dist_le A c hρ h

/-- Cardinality of a set of Gaussian integers of norm `≤ X`. -/
theorem card_of_gnorm_le (A : Finset GaussianInt) {X : ℝ} (_hX : 0 ≤ X)
    (h : ∀ z ∈ A, ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ X) :
    (A.card : ℝ) ≤ (2 * Real.sqrt X + 1) ^ 2 := by
  refine card_le_disc A 0 (Real.sqrt_nonneg X) ?_
  intro z hz
  rw [sub_zero, Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
  exact Real.sqrt_le_sqrt (h z hz)

/-- The telescoping summand `1/(m(m+1))`. -/
def telSummand (m : ℕ) : ℝ := (1 : ℝ) / ((m : ℝ) * ((m : ℝ) + 1))

/-- Telescoping identity: `∑_{m = k}^{M} 1/(m(m+1)) = 1/k - 1/(M+1)`. -/
theorem sum_Icc_tel (k M : ℕ) (hk : 1 ≤ k) (hkM : k ≤ M) :
    ∑ m ∈ Finset.Icc k M, telSummand m = 1 / (k : ℝ) - 1 / ((M : ℝ) + 1) := by
  simp only [telSummand]
  induction M, hkM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
  | succ M hkM ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      have hstep : (1 : ℝ) / (((M : ℝ) + 1) * (((M : ℝ) + 1) + 1))
          = 1 / ((M : ℝ) + 1) - 1 / (((M : ℝ) + 1) + 1) := by
        have h1 : ((M : ℝ) + 1) ≠ 0 := by positivity
        have h2 : ((M : ℝ) + 1 + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [hstep]
      ring

/-- The harmonic sum bound `∑_{m=1}^{M} 1/(m+1) ≤ log(1+M)`, by comparison with `∫ x⁻¹`. -/
theorem sum_inv_succ_le_log (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((m : ℝ) + 1) ≤ Real.log (1 + (M : ℝ)) := by
  rw [show Finset.Icc 1 M = Finset.Ico 1 (M + 1) by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  rw [Finset.sum_Ico_eq_sum_range, show M + 1 - 1 = M by omega]
  have hcongr : ∀ i ∈ Finset.range M,
      (1 : ℝ) / (((1 + i : ℕ) : ℝ) + 1) = 1 / (1 + ((i : ℝ) + 1)) := by
    intro i _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcongr]
  have hanti : AntitoneOn (fun x : ℝ => 1 / x) (Set.Icc (1 : ℝ) (1 + (M : ℝ))) := by
    intro x hx y hy hxy
    rw [Set.mem_Icc] at hx hy
    exact one_div_le_one_div_of_le (by linarith : (0 : ℝ) < x) hxy
  have h := AntitoneOn.sum_le_integral hanti
  simp only [Nat.cast_add, Nat.cast_one] at h
  have hint : ∫ x in (1 : ℝ)..(1 + (M : ℝ)), 1 / x = Real.log (1 + (M : ℝ)) := by
    have h' : (∫ x in (1 : ℝ)..(1 + (M : ℝ)), 1 / x)
        = ∫ x in (1 : ℝ)..(1 + (M : ℝ)), x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x _
      rw [one_div]
    have hle : (1 : ℝ) ≤ 1 + (M : ℝ) := by
      linarith [show (0 : ℝ) ≤ (M : ℝ) from Nat.cast_nonneg M]
    have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + (M : ℝ)) := by
      rw [Set.uIcc_of_le hle, Set.mem_Icc]
      rintro ⟨h1, h2⟩
      linarith
    rw [h', integral_inv h0, div_one]
  rw [hint] at h
  exact h

/-- **The elementary lattice sum** `∑ 1/|u|² = O(log)`: for a finite set of nonzero Gaussian
integers of norm `≤ X`, the sum of `1/|u|²` is at most `100 log(2+X)`.

The pointwise bound `1/k ≤ ∑_{m=k}^{M} telSummand m + 1/(M+1)` (telescoping, `M = ⌈X⌉`) is summed
and the order of summation exchanged; the inner count `#{u ∈ A : |u|² ≤ m}` is a disc count
`≤ (2√m+1)²`, and `(2√m+1)²/(m(m+1)) ≤ 9/(m+1)`. -/
theorem sum_inv_gnorm_le (A : Finset GaussianInt) (X : ℝ) (hX : 1 ≤ X)
    (hpos : ∀ u ∈ A, 1 ≤ Work.FIPlan.gnorm u)
    (hle : ∀ u ∈ A, ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ X) :
    ∑ u ∈ A, (1 : ℝ) / ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ 100 * Real.log (2 + X) := by
  set M : ℕ := ⌈X⌉₊ with hM
  have hXM : X ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil X
  have hkey : ∀ u ∈ A, (1 : ℝ) / ((Work.FIPlan.gnorm u : ℕ) : ℝ)
      ≤ (∑ m ∈ Finset.Icc (Work.FIPlan.gnorm u) M, telSummand m) + 1 / ((M : ℝ) + 1) := by
    intro u hu
    have hk : 1 ≤ Work.FIPlan.gnorm u := hpos u hu
    have hkM : Work.FIPlan.gnorm u ≤ M := by
      have h2 : ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := le_trans (hle u hu) hXM
      exact_mod_cast h2
    rw [sum_Icc_tel (Work.FIPlan.gnorm u) M hk hkM, sub_add_cancel]
  have hsum1 : ∑ u ∈ A, (1 : ℝ) / ((Work.FIPlan.gnorm u : ℕ) : ℝ)
      ≤ (∑ u ∈ A, ∑ m ∈ Finset.Icc (Work.FIPlan.gnorm u) M, telSummand m)
        + (A.card : ℝ) * (1 / ((M : ℝ) + 1)) := by
    calc ∑ u ∈ A, (1 : ℝ) / ((Work.FIPlan.gnorm u : ℕ) : ℝ)
        ≤ ∑ u ∈ A, ((∑ m ∈ Finset.Icc (Work.FIPlan.gnorm u) M, telSummand m)
            + 1 / ((M : ℝ) + 1)) := Finset.sum_le_sum hkey
      _ = (∑ u ∈ A, ∑ m ∈ Finset.Icc (Work.FIPlan.gnorm u) M, telSummand m)
            + (A.card : ℝ) * (1 / ((M : ℝ) + 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hswap : (∑ u ∈ A, ∑ m ∈ Finset.Icc (Work.FIPlan.gnorm u) M, telSummand m)
      = ∑ m ∈ Finset.Icc 1 M,
          ∑ u ∈ A, (if Work.FIPlan.gnorm u ≤ m then telSummand m else 0) := by
    have h1 : ∀ u ∈ A, (∑ m ∈ Finset.Icc (Work.FIPlan.gnorm u) M, telSummand m)
        = ∑ m ∈ Finset.Icc 1 M,
            (if Work.FIPlan.gnorm u ≤ m then telSummand m else 0) := by
      intro u hu
      have hk : 1 ≤ Work.FIPlan.gnorm u := hpos u hu
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have hcount : ∀ m ∈ Finset.Icc 1 M,
      (∑ u ∈ A, (if Work.FIPlan.gnorm u ≤ m then telSummand m else 0))
        ≤ telSummand m * (2 * Real.sqrt (m : ℝ) + 1) ^ 2 := by
    intro m _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (((A.filter (fun u => Work.FIPlan.gnorm u ≤ m)).card : ℕ) : ℝ)
        ≤ (2 * Real.sqrt (m : ℝ) + 1) ^ 2 := by
      refine card_of_gnorm_le _ (by positivity) ?_
      intro z hz
      rw [Finset.mem_filter] at hz
      exact_mod_cast hz.2
    have hnn : 0 ≤ telSummand m := by
      rw [telSummand]
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp
      · exact div_nonneg zero_le_one (by positivity : (0 : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 1))
    calc ((A.filter (fun u => Work.FIPlan.gnorm u ≤ m)).card : ℕ) * telSummand m
        ≤ (2 * Real.sqrt (m : ℝ) + 1) ^ 2 * telSummand m :=
          mul_le_mul_of_nonneg_right hcard hnn
      _ = telSummand m * (2 * Real.sqrt (m : ℝ) + 1) ^ 2 := by ring
  have hpoint : ∀ m ∈ Finset.Icc 1 M,
      telSummand m * (2 * Real.sqrt (m : ℝ) + 1) ^ 2 ≤ 9 * (1 / ((m : ℝ) + 1)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
    have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
    have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt hmpos.le
    have hexp : (2 * Real.sqrt (m : ℝ) + 1) ^ 2
        = 4 * (m : ℝ) + 4 * Real.sqrt (m : ℝ) + 1 := by
      rw [show (2 * Real.sqrt (m : ℝ) + 1) ^ 2
          = 4 * Real.sqrt (m : ℝ) ^ 2 + 4 * Real.sqrt (m : ℝ) + 1 by ring, hsq]
    have h5 : 4 * Real.sqrt (m : ℝ) + 1 ≤ 5 * (m : ℝ) := by
      nlinarith [Real.sqrt_nonneg (m : ℝ), hsq, hm1]
    rw [telSummand, hexp]
    rw [show (1 : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) * (4 * (m : ℝ) + 4 * Real.sqrt (m : ℝ) + 1)
        = (4 * (m : ℝ) + 4 * Real.sqrt (m : ℝ) + 1) / ((m : ℝ) * ((m : ℝ) + 1)) from by ring]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1))]
    rw [show 9 * (1 / ((m : ℝ) + 1)) * ((m : ℝ) * ((m : ℝ) + 1)) = 9 * (m : ℝ) from by
      field_simp]
    linarith
  have hmain : (∑ m ∈ Finset.Icc 1 M,
        ∑ u ∈ A, (if Work.FIPlan.gnorm u ≤ m then telSummand m else 0))
      ≤ 9 * Real.log (1 + (M : ℝ)) := by
    calc (∑ m ∈ Finset.Icc 1 M,
          ∑ u ∈ A, (if Work.FIPlan.gnorm u ≤ m then telSummand m else 0))
        ≤ ∑ m ∈ Finset.Icc 1 M, telSummand m * (2 * Real.sqrt (m : ℝ) + 1) ^ 2 :=
          Finset.sum_le_sum hcount
      _ ≤ ∑ m ∈ Finset.Icc 1 M, 9 * (1 / ((m : ℝ) + 1)) := Finset.sum_le_sum hpoint
      _ = 9 * ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / ((m : ℝ) + 1) := by rw [Finset.mul_sum]
      _ ≤ 9 * Real.log (1 + (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_succ_le_log M) (by norm_num)
  have hcardA : (A.card : ℝ) ≤ (2 * Real.sqrt X + 1) ^ 2 := card_of_gnorm_le A (by linarith) hle
  have hextra : (A.card : ℝ) * (1 / ((M : ℝ) + 1)) ≤ 8 := by
    have hXM1 : X + 1 ≤ (M : ℝ) + 1 := by linarith
    have hA1 : (1 / ((M : ℝ) + 1)) ≤ 1 / (X + 1) :=
      one_div_le_one_div_of_le (by linarith : (0 : ℝ) < X + 1) hXM1
    have hb : (2 * Real.sqrt X + 1) ^ 2 * (1 / (X + 1)) ≤ 8 := by
      have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt (by linarith)
      have hexp : (2 * Real.sqrt X + 1) ^ 2 = 4 * X + 4 * Real.sqrt X + 1 := by
        rw [show (2 * Real.sqrt X + 1) ^ 2 = 4 * Real.sqrt X ^ 2 + 4 * Real.sqrt X + 1 by ring,
          hsq]
      rw [one_div, ← div_eq_mul_inv, div_le_iff₀ (by linarith : (0 : ℝ) < X + 1), hexp]
      nlinarith [Real.sqrt_nonneg X, hsq, hX]
    calc (A.card : ℝ) * (1 / ((M : ℝ) + 1))
        ≤ (2 * Real.sqrt X + 1) ^ 2 * (1 / ((M : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hcardA (by positivity)
      _ ≤ (2 * Real.sqrt X + 1) ^ 2 * (1 / (X + 1)) :=
          mul_le_mul_of_nonneg_left hA1 (by positivity)
      _ ≤ 8 := hb
  have hlog1 : Real.log (1 + (M : ℝ)) ≤ Real.log (2 + X) := by
    apply Real.log_le_log (by linarith)
    have : (M : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hlog2 : (1 : ℝ) ≤ Real.log (2 + X) := by
    have h1 : Real.exp 1 ≤ 2 + X := by
      have := Real.exp_one_lt_three
      linarith
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  rw [hswap] at hsum1
  nlinarith [hsum1, hmain, hextra, hlog1, hlog2]

/-! ## 3. The pair count -/

/-- The box `{|re| ≤ R, |im| ≤ R}` of Gaussian integers (the same set as
`Work.FIPlan.gBox`, written with the finitary product so that `Finset.mem_product` applies). -/
def gBoxI (R : ℤ) : Finset GaussianInt :=
  ((Finset.Icc (-R) R) ×ˢ (Finset.Icc (-R) R)).image (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))

lemma gBoxI_eq_gBox (R : ℤ) : gBoxI R = Work.FIPlan.gBox R := rfl

/-- The box of the statement. -/
def tauBox (N θ : ℝ) : Finset GaussianInt :=
  gBoxI (⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ)

lemma mem_tauBox_iff {N θ : ℝ} {z : GaussianInt} :
    z ∈ tauBox N θ ↔ -((⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ)) ≤ z.re ∧
      z.re ≤ (⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ) ∧
      -((⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ)) ≤ z.im ∧
      z.im ≤ (⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ) := by
  rw [tauBox, gBoxI, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [← hpe]
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(z.re, z.im), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    · exact Zsqrtd.ext rfl rfl

/-- `gnorm` of zero. -/
lemma gnorm_zero : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := rfl

/-- `gnorm` in terms of the real and imaginary parts. -/
lemma gnorm_cast_real (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  have h1 := Work.FIArea4.normSq_toComplex_gnorm z
  rw [← h1, Complex.sq_norm, Complex.normSq_apply, ← GaussianInt.intCast_re,
    ← GaussianInt.intCast_im]
  ring

/-- Membership in the box from the norm bound. -/
lemma mem_tauBox_of_gnorm_le (N θ : ℝ) (hN : 0 ≤ N) {z : GaussianInt}
    (h : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + θ) * N) : z ∈ tauBox N θ := by
  rw [mem_tauBox_iff]
  set R : ℤ := (⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ) with hR
  have hgn := gnorm_cast_real z
  have hceil : Real.sqrt (4 * N * (1 + θ)) ≤ (R : ℝ) := by
    rw [hR]
    push_cast
    exact Nat.le_ceil _
  have hsq_le : (z.re : ℝ) ^ 2 ≤ 4 * N * (1 + θ) := by
    have h3 : (z.re : ℝ) ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
      rw [hgn]; nlinarith [sq_nonneg (z.im : ℝ)]
    nlinarith [h3, h, hN, sq_nonneg θ, sq_nonneg N]
  have hsq_le' : (z.im : ℝ) ^ 2 ≤ 4 * N * (1 + θ) := by
    have h3 : (z.im : ℝ) ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
      rw [hgn]; nlinarith [sq_nonneg (z.re : ℝ)]
    nlinarith [h3, h, hN, sq_nonneg θ, sq_nonneg N]
  have hre : (z.re : ℝ) ≤ (R : ℝ) := by
    calc (z.re : ℝ) ≤ Real.sqrt ((z.re : ℝ) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
      _ ≤ Real.sqrt (4 * N * (1 + θ)) := Real.sqrt_le_sqrt hsq_le
      _ ≤ (R : ℝ) := hceil
  have him : (z.im : ℝ) ≤ (R : ℝ) := by
    calc (z.im : ℝ) ≤ Real.sqrt ((z.im : ℝ) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
      _ ≤ Real.sqrt (4 * N * (1 + θ)) := Real.sqrt_le_sqrt hsq_le'
      _ ≤ (R : ℝ) := hceil
  have hnegre : (z.re : ℝ) ≥ -(R : ℝ) := by
    have habs : |(z.re : ℝ)| ≤ Real.sqrt (4 * N * (1 + θ)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq_le
    have := (abs_le.mp habs).1
    linarith
  have hnegim : (z.im : ℝ) ≥ -(R : ℝ) := by
    have habs : |(z.im : ℝ)| ≤ Real.sqrt (4 * N * (1 + θ)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hsq_le'
    have := (abs_le.mp habs).1
    linarith
  exact ⟨by exact_mod_cast hnegre, by exact_mod_cast hre,
    by exact_mod_cast hnegim, by exact_mod_cast him⟩

/-- The sector-annulus predicate. -/
def sectAnn (N θ φ : ℝ) (z : GaussianInt) : Prop :=
  N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧ ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + θ) * N ∧
    φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * θ

lemma ne_zero_of_sectAnn {N θ φ : ℝ} (hN : 0 ≤ N) {z : GaussianInt} (hz : sectAnn N θ φ z) :
    z ≠ 0 := by
  intro h
  subst h
  simp only [sectAnn, gnorm_zero, Nat.cast_zero] at hz
  linarith [hz.1, hN]

lemma one_le_gnorm_of_sectAnn {N θ φ : ℝ} (hN : 0 ≤ N) {z : GaussianInt}
    (hz : sectAnn N θ φ z) : 1 ≤ Work.FIPlan.gnorm z :=
  one_le_gnorm_of_ne_zero z (ne_zero_of_sectAnn hN hz)

lemma le_gnorm_of_mul {a b : GaussianInt} (h : 1 ≤ Work.FIPlan.gnorm (a * b)) :
    1 ≤ Work.FIPlan.gnorm a ∧ 1 ≤ Work.FIPlan.gnorm b := by
  rw [gnorm_mul] at h
  exact ⟨Nat.one_le_iff_ne_zero.mpr fun ha => by simp [ha] at h,
    Nat.one_le_iff_ne_zero.mpr fun hb => by simp [hb] at h⟩

/-- The set of Gaussian integers whose norm is in the sector annulus and squarefree. -/
def zSet (N θ φ : ℝ) : Finset GaussianInt :=
  (tauBox N θ).filter (fun z => sectAnn N θ φ z ∧ Squarefree (Work.FIPlan.gnorm z))

/-- The set of candidate "small" norms of a factor of an element of the sector annulus. -/
def smallSet (N θ : ℝ) : Finset GaussianInt :=
  (tauBox N θ).filter (fun u => 1 ≤ Work.FIPlan.gnorm u ∧
    (((Work.FIPlan.gnorm u : ℕ) : ℝ)) ^ 2 ≤ (1 + θ) * N)

/-- The radius of the disc containing the cofactor of a fixed factor `v`. -/
def cofactorRadius (N θ : ℝ) (v : GaussianInt) : ℝ :=
  10 * θ * Real.sqrt N / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ))

/-- All pairs `(w, u)` of box elements with `w·u` in the sector annulus. -/
def pairSet (N θ φ : ℝ) : Finset (GaussianInt × GaussianInt) :=
  ((tauBox N θ) ×ˢ (tauBox N θ)).filter (fun p => sectAnn N θ φ (p.1 * p.2))

/-- The pairs grouped by the "fixed" factor. -/
def sigmaSet (N θ φ : ℝ) : Finset (Σ _ : GaussianInt, GaussianInt) :=
  (smallSet N θ).sigma (fun v => (tauBox N θ).filter (fun t => sectAnn N θ φ (t * v)))

lemma pairSet_mem {N θ φ : ℝ} {p : GaussianInt × GaussianInt} (hp : p ∈ pairSet N θ φ) :
    p.1 ∈ tauBox N θ ∧ p.2 ∈ tauBox N θ ∧ sectAnn N θ φ (p.1 * p.2) := by
  rw [pairSet, Finset.mem_filter] at hp
  rw [Finset.mem_product] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

lemma smallSet_mem {N θ : ℝ} {u : GaussianInt} (hu : u ∈ smallSet N θ) :
    1 ≤ Work.FIPlan.gnorm u ∧ (((Work.FIPlan.gnorm u : ℕ) : ℝ)) ^ 2 ≤ (1 + θ) * N := by
  rw [smallSet, Finset.mem_filter] at hu
  exact hu.2

/-- **The cofactor of a fixed factor lies in a disc of radius `cofactorRadius`.** -/
theorem fiber_card_le (N θ φ : ℝ) (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (v : GaussianInt) :
    (((tauBox N θ).filter (fun t => sectAnn N θ φ (t * v))).card : ℝ)
      ≤ (2 * cofactorRadius N θ v + 1) ^ 2 := by
  by_cases hv : v = 0
  · subst hv
    have hempty : (tauBox N θ).filter (fun t => sectAnn N θ φ (t * 0)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro t _ hs
      have h1 : N < (0 : ℝ) := by
        have h2 := hs.1
        rw [mul_zero, gnorm_zero] at h2
        simpa using h2
      linarith
    rw [hempty, Finset.card_empty]
    push_cast
    rw [cofactorRadius]
    positivity
  · have hvpos : 0 < Work.FIPlan.gnorm v :=
      Nat.pos_of_ne_zero fun h => hv ((gnorm_eq_zero_iff v).mp h)
    have hvn : 0 < Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)) := by
      rw [Real.sqrt_pos]
      exact_mod_cast hvpos
    set c : ℂ := (Real.sqrt ((1 + θ) * N) : ℂ)
      * Complex.exp (((φ + Real.pi * θ : ℝ) : ℂ) * Complex.I) with hc
    refine card_le_disc _ (c / v.toComplex) ?_ ?_
    · rw [cofactorRadius]
      positivity
    · intro t ht
      rw [Finset.mem_filter] at ht
      have hs := ht.2
      have h1 : ‖(t * v).toComplex - c‖ ≤ 10 * θ * Real.sqrt N := by
        rw [hc]
        exact sector_annulus_disc N θ φ hN hθ hθ1 (t * v) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
      have h1' : ‖t.toComplex * v.toComplex - c‖ ≤ 10 * θ * Real.sqrt N := by
        simpa [map_mul] using h1
      have hvz : v.toComplex ≠ 0 := by
        intro h0
        have hnm : ‖v.toComplex‖ = 0 := by rw [h0]; simp
        rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm] at hnm
        linarith
      have hkey : t.toComplex - c / v.toComplex
          = (t.toComplex * v.toComplex - c) / v.toComplex := by
        field_simp
      rw [hkey, norm_div, Work.FIArea4.norm_toComplex_eq_sqrt_gnorm, cofactorRadius]
      exact div_le_div_of_nonneg_right h1' (Real.sqrt_nonneg _)

/-- The pairs whose second factor is the smaller one are counted by the grouped set. -/
theorem pairA_le (N θ φ : ℝ) (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ((pairSet N θ φ).filter (fun p => Work.FIPlan.gnorm p.2 ≤ Work.FIPlan.gnorm p.1)).card
      ≤ (sigmaSet N θ φ).card := by
  refine Finset.card_le_card_of_injOn
    (fun p : GaussianInt × GaussianInt => (⟨p.2, p.1⟩ : Σ _ : GaussianInt, GaussianInt)) ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨hpair, hle⟩ := hp
    obtain ⟨h1, h2, hsect⟩ := pairSet_mem hpair
    have hk2 := (le_gnorm_of_mul (one_le_gnorm_of_sectAnn (by linarith) hsect)).2
    rw [Finset.mem_coe, sigmaSet, Finset.mem_sigma]
    constructor
    · rw [smallSet, Finset.mem_filter]
      refine ⟨h2, hk2, ?_⟩
      have hg : ((Work.FIPlan.gnorm (p.1 * p.2) : ℕ) : ℝ)
          = ((Work.FIPlan.gnorm p.1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm p.2 : ℕ) : ℝ) := by
        rw [gnorm_mul]; push_cast; ring
      have hleR : ((Work.FIPlan.gnorm p.2 : ℕ) : ℝ) ≤ ((Work.FIPlan.gnorm p.1 : ℕ) : ℝ) := by
        exact_mod_cast hle
      have hnn : (0 : ℝ) ≤ ((Work.FIPlan.gnorm p.2 : ℕ) : ℝ) := by positivity
      nlinarith [hsect.2.1, hg, hleR, hnn]
    · rw [Finset.mem_filter]
      exact ⟨h1, hsect⟩
  · intro p hp q hq heq
    simp only [Finset.mem_coe] at hp hq
    have h2 : (p.2, p.1) = (q.2, q.1) := by
      simpa only [Sigma.fst, Sigma.snd] using
        congrArg (fun s : Σ _ : GaussianInt, GaussianInt => (s.1, s.2)) heq
    exact Prod.ext (Prod.ext_iff.mp h2).2 (Prod.ext_iff.mp h2).1

/-- The pairs whose first factor is the smaller one are counted by the grouped set. -/
theorem pairB_le (N θ φ : ℝ) (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ((pairSet N θ φ).filter (fun p => ¬ (Work.FIPlan.gnorm p.2 ≤ Work.FIPlan.gnorm p.1))).card
      ≤ (sigmaSet N θ φ).card := by
  refine Finset.card_le_card_of_injOn
    (fun p : GaussianInt × GaussianInt => (⟨p.1, p.2⟩ : Σ _ : GaussianInt, GaussianInt)) ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨hpair, hle⟩ := hp
    obtain ⟨h1, h2, hsect⟩ := pairSet_mem hpair
    have hlt : Work.FIPlan.gnorm p.1 < Work.FIPlan.gnorm p.2 := not_le.mp hle
    have hk1 := (le_gnorm_of_mul (one_le_gnorm_of_sectAnn (by linarith) hsect)).1
    rw [Finset.mem_coe, sigmaSet, Finset.mem_sigma]
    constructor
    · rw [smallSet, Finset.mem_filter]
      refine ⟨h1, hk1, ?_⟩
      have hg : ((Work.FIPlan.gnorm (p.1 * p.2) : ℕ) : ℝ)
          = ((Work.FIPlan.gnorm p.1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm p.2 : ℕ) : ℝ) := by
        rw [gnorm_mul]; push_cast; ring
      have hltR : ((Work.FIPlan.gnorm p.1 : ℕ) : ℝ) < ((Work.FIPlan.gnorm p.2 : ℕ) : ℝ) := by
        exact_mod_cast hlt
      have hnn : (0 : ℝ) ≤ ((Work.FIPlan.gnorm p.1 : ℕ) : ℝ) := by positivity
      nlinarith [hsect.2.1, hg, hltR, hnn]
    · rw [Finset.mem_filter]
      refine ⟨h2, ?_⟩
      rw [mul_comm]
      exact hsect
  · intro p hp q hq heq
    simp only [Finset.mem_coe] at hp hq
    have h2 : (p.1, p.2) = (q.1, q.2) := by
      simpa only [Sigma.fst, Sigma.snd] using
        congrArg (fun s : Σ _ : GaussianInt, GaussianInt => (s.1, s.2)) heq
    exact Prod.ext (Prod.ext_iff.mp h2).1 (Prod.ext_iff.mp h2).2

/-- **The pair count.** -/
theorem pair_card_le (N θ φ : ℝ) (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ((pairSet N θ φ).card : ℝ)
      ≤ 2 * ∑ v ∈ smallSet N θ, (2 * cofactorRadius N θ v + 1) ^ 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := pairSet N θ φ) (p := fun p : GaussianInt × GaussianInt =>
      Work.FIPlan.gnorm p.2 ≤ Work.FIPlan.gnorm p.1)
  have hA := pairA_le N θ φ hN hθ hθ1
  have hB := pairB_le N θ φ hN hθ hθ1
  have hsigma : ((sigmaSet N θ φ).card : ℝ) = ∑ v ∈ smallSet N θ,
      (((tauBox N θ).filter (fun t => sectAnn N θ φ (t * v))).card : ℝ) := by
    rw [sigmaSet, Finset.card_sigma]
    push_cast
    rfl
  have hbound : ((sigmaSet N θ φ).card : ℝ)
      ≤ ∑ v ∈ smallSet N θ, (2 * cofactorRadius N θ v + 1) ^ 2 := by
    rw [hsigma]
    exact Finset.sum_le_sum (fun v _ => fiber_card_le N θ φ hN hθ hθ1 v)
  have hcard : ((pairSet N θ φ).card : ℝ) = (((pairSet N θ φ).filter
        (fun p => Work.FIPlan.gnorm p.2 ≤ Work.FIPlan.gnorm p.1)).card : ℝ)
      + (((pairSet N θ φ).filter
        (fun p => ¬ (Work.FIPlan.gnorm p.2 ≤ Work.FIPlan.gnorm p.1))).card : ℝ) := by
    rw [← hsplit]; push_cast; ring
  have hA' : (((pairSet N θ φ).filter
      (fun p => Work.FIPlan.gnorm p.2 ≤ Work.FIPlan.gnorm p.1)).card : ℝ)
      ≤ ((sigmaSet N θ φ).card : ℝ) := by exact_mod_cast hA
  have hB' : (((pairSet N θ φ).filter
      (fun p => ¬ (Work.FIPlan.gnorm p.2 ≤ Work.FIPlan.gnorm p.1))).card : ℝ)
      ≤ ((sigmaSet N θ φ).card : ℝ) := by exact_mod_cast hB
  rw [hcard]
  linarith [hA', hB', hbound]

/-! ## 4. The estimate for the grouped sum -/

lemma cofactorRadius_expand (N θ : ℝ) (hN : 0 < N) {v : GaussianInt}
    (hv : 1 ≤ Work.FIPlan.gnorm v) :
    (2 * cofactorRadius N θ v + 1) ^ 2
      = 400 * θ ^ 2 * N / (((Work.FIPlan.gnorm v : ℕ) : ℝ))
        + 40 * θ * Real.sqrt N / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)) + 1 := by
  set k : ℝ := ((Work.FIPlan.gnorm v : ℕ) : ℝ) with hkdef
  have hk : 0 < k := by rw [hkdef]; exact_mod_cast hv
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  have hsk : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
  have hsq : (Real.sqrt N / Real.sqrt k) ^ 2 = N / k := by
    rw [div_pow, hsN, hsk]
  rw [cofactorRadius]
  rw [show (2 * (10 * θ * Real.sqrt N / Real.sqrt k) + 1) ^ 2
      = 400 * θ ^ 2 * (Real.sqrt N / Real.sqrt k) ^ 2
        + 40 * θ * (Real.sqrt N / Real.sqrt k) + 1 from by ring, hsq]
  ring

/-- **The estimate for the grouped sum**: `∑ (2ρ_v+1)² ≪ (√N + θN) log(2+N)`. -/
theorem smallSet_sum_bound (N θ : ℝ) (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∑ v ∈ smallSet N θ, (2 * cofactorRadius N θ v + 1) ^ 2
      ≤ 200000 * (Real.sqrt N + θ * N) * Real.log (2 + N) := by
  set Y : ℝ := Real.sqrt ((1 + θ) * N) with hY
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hY1 : 1 ≤ Y := by
    rw [hY]
    apply Real.one_le_sqrt.mpr
    nlinarith
  have hmem : ∀ v ∈ smallSet N θ, 1 ≤ Work.FIPlan.gnorm v ∧ ((Work.FIPlan.gnorm v : ℕ) : ℝ) ≤ Y := by
    intro v hv
    have h := smallSet_mem hv
    refine ⟨h.1, ?_⟩
    rw [hY]
    calc ((Work.FIPlan.gnorm v : ℕ) : ℝ) = Real.sqrt ((((Work.FIPlan.gnorm v : ℕ) : ℝ)) ^ 2) := by
          rw [Real.sqrt_sq (by positivity)]
      _ ≤ Real.sqrt ((1 + θ) * N) := Real.sqrt_le_sqrt h.2
  have hS1 : ∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ)
      ≤ 100 * Real.log (2 + Y) :=
    sum_inv_gnorm_le _ Y hY1 (fun v hv => (hmem v hv).1) (fun v hv => (hmem v hv).2)
  have hS1nn : 0 ≤ ∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ) :=
    Finset.sum_nonneg (fun v hv => by
      have hk : (0 : ℝ) < ((Work.FIPlan.gnorm v : ℕ) : ℝ) := by exact_mod_cast (hmem v hv).1
      positivity)
  have hcard : (((smallSet N θ).card : ℕ) : ℝ) ≤ (2 * Real.sqrt Y + 1) ^ 2 :=
    card_of_gnorm_le _ hY0 (fun v hv => (hmem v hv).2)
  have hcardN : (((smallSet N θ).card : ℕ) : ℝ) ≤ 20 * Real.sqrt N := by
    refine le_trans hcard ?_
    have hYN : Y ≤ Real.sqrt 2 * Real.sqrt N := by
      rw [hY]
      calc Real.sqrt ((1 + θ) * N) ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt (by nlinarith)
        _ = Real.sqrt 2 * Real.sqrt N := Real.sqrt_mul (by norm_num) N
    have hYN2 : Y ≤ 2 * Real.sqrt N := by
      have h2 : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      nlinarith [hYN, h2, Real.sqrt_nonneg N]
    have hsY : Real.sqrt Y ≤ 2 * Real.sqrt N := by
      rw [← Real.sqrt_sq (show (0:ℝ) ≤ 2 * Real.sqrt N by positivity)]
      apply Real.sqrt_le_sqrt
      nlinarith [hYN2, Real.sq_sqrt (show (0:ℝ) ≤ N by linarith), Real.sqrt_nonneg N]
    have hexp : (2 * Real.sqrt Y + 1) ^ 2 = 4 * Y + 4 * Real.sqrt Y + 1 := by
      rw [show (2 * Real.sqrt Y + 1) ^ 2 = 4 * Real.sqrt Y ^ 2 + 4 * Real.sqrt Y + 1 by ring,
        Real.sq_sqrt hY0]
    rw [hexp]
    have hsN1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
    nlinarith [hYN2, hsY, Real.sqrt_nonneg N]
  have hS2 : ∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ))
      ≤ Real.sqrt ((∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
          * ((smallSet N θ).card : ℝ)) := by
    have hsq2 : ∀ v ∈ smallSet N θ,
        ((1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ))) ^ 2
          = (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ) := by
      intro v hv
      have hk : (0 : ℝ) < ((Work.FIPlan.gnorm v : ℕ) : ℝ) := by exact_mod_cast (hmem v hv).1
      rw [div_pow, one_pow, Real.sq_sqrt hk.le]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (smallSet N θ)
      (fun v => (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ))) (fun _ => (1 : ℝ))
    have hL : (∑ v ∈ smallSet N θ,
          (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)) * 1)
        = ∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)) :=
      Finset.sum_congr rfl (fun v _ => mul_one _)
    have hR1 : (∑ v ∈ smallSet N θ, ((1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ))) ^ 2)
        = ∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ) :=
      Finset.sum_congr rfl hsq2
    have hR2 : (∑ v ∈ smallSet N θ, (1 : ℝ) ^ 2) = ((smallSet N θ).card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]; simp
    rw [hL, hR1, hR2] at hcs
    have hnn : 0 ≤ ∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)) :=
      Finset.sum_nonneg (fun v hv => by
        have hk : (0 : ℝ) < ((Work.FIPlan.gnorm v : ℕ) : ℝ) := by exact_mod_cast (hmem v hv).1
        positivity)
    calc (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
        = Real.sqrt ((∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ))) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
            * ((smallSet N θ).card : ℝ)) := Real.sqrt_le_sqrt hcs
  -- assemble
  have hlogY : Real.log (2 + Y) ≤ 2 * Real.log (2 + N) := by
    have h1 : (2:ℝ) + Y ≤ 2 * (2 + N) := by
      have : Y ≤ 2 * N := by
        rw [hY]
        calc Real.sqrt ((1 + θ) * N) ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt (by nlinarith)
          _ ≤ 2 * N := by
              rw [Real.sqrt_le_iff]
              constructor <;> nlinarith
      linarith
    have h2 : Real.log (2 + Y) ≤ Real.log (2 * (2 + N)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    have h3 : Real.log 2 ≤ Real.log (2 + N) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlog1 : (1:ℝ) ≤ Real.log (2 + N) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hstep : ∑ v ∈ smallSet N θ, (400 * θ ^ 2 * N / (((Work.FIPlan.gnorm v : ℕ) : ℝ))
        + 40 * θ * Real.sqrt N / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)) + 1)
      = 400 * θ ^ 2 * N * (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
        + 40 * θ * Real.sqrt N
            * (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
        + ((smallSet N θ).card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.mul_sum, Finset.mul_sum]
    ring
  have hsum_eq : ∑ v ∈ smallSet N θ, (2 * cofactorRadius N θ v + 1) ^ 2
      = ∑ v ∈ smallSet N θ, (400 * θ ^ 2 * N / (((Work.FIPlan.gnorm v : ℕ) : ℝ))
        + 40 * θ * Real.sqrt N / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)) + 1) :=
    Finset.sum_congr rfl (fun v hv => cofactorRadius_expand N θ (by linarith) (hmem v hv).1)
  rw [hsum_eq, hstep]
  -- numeric combination
  have hL0 : 0 ≤ Real.log (2 + N) := le_trans (by norm_num) hlog1
  have hsN0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hsN1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hN0 : 0 ≤ N := by linarith
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith [hθ, hθ1]
  have hsNsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
  have hN14 : Real.sqrt (Real.sqrt N) ≤ Real.sqrt N := by
    calc Real.sqrt (Real.sqrt N) ≤ Real.sqrt (Real.sqrt N * Real.sqrt N) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hsN1]
      _ = Real.sqrt N := Real.sqrt_mul_self hsN0
  have hsqrtlog : Real.sqrt (Real.log (2 + N)) ≤ Real.log (2 + N) := by
    nlinarith [Real.sq_sqrt hL0, Real.sqrt_nonneg (Real.log (2 + N)), hlog1]
  have hS1' : (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
      ≤ 200 * Real.log (2 + N) := by linarith [hS1, hlogY]
  have hS2'' : (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
      ≤ 100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N) := by
    have hsqid : (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2
        = 10000 * Real.log (2 + N) * Real.sqrt N := by
      have h1 : Real.sqrt (Real.sqrt N) ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg N)
      have h2 : Real.sqrt (Real.log (2 + N)) ^ 2 = Real.log (2 + N) := Real.sq_sqrt hL0
      rw [show (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2
          = 10000 * Real.sqrt (Real.log (2 + N)) ^ 2 * (Real.sqrt (Real.sqrt N)) ^ 2 by ring,
        h1, h2]
    have hprod : (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
        * ((smallSet N θ).card : ℝ)
        ≤ (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2 := by
      rw [hsqid]
      have h1 : (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
          * ((smallSet N θ).card : ℝ)
          ≤ (200 * Real.log (2 + N)) * (20 * Real.sqrt N) :=
        mul_le_mul hS1' hcardN (by positivity) (by positivity)
      nlinarith [h1, hL0, hsN0]
    calc (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
        ≤ Real.sqrt ((∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
            * ((smallSet N θ).card : ℝ)) := hS2
      _ ≤ Real.sqrt ((100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = 100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N) :=
          Real.sqrt_sq (by positivity)
  have hsNsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
  have hS1' : (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
      ≤ 200 * Real.log (2 + N) := by linarith [hS1, hlogY]
  have hS2'' : (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
      ≤ 100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N) := by
    have hsqid : (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2
        = 10000 * Real.log (2 + N) * Real.sqrt N := by
      have h1 : Real.sqrt (Real.sqrt N) ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg N)
      have h2 : Real.sqrt (Real.log (2 + N)) ^ 2 = Real.log (2 + N) := Real.sq_sqrt hL0
      rw [show (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2
          = 10000 * Real.sqrt (Real.log (2 + N)) ^ 2 * (Real.sqrt (Real.sqrt N)) ^ 2 by ring,
        h1, h2]
    have hprod : (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
        * ((smallSet N θ).card : ℝ)
        ≤ (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2 := by
      rw [hsqid]
      have h1 : (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
          * ((smallSet N θ).card : ℝ)
          ≤ (200 * Real.log (2 + N)) * (20 * Real.sqrt N) :=
        mul_le_mul hS1' hcardN (by positivity) (by positivity)
      have hp : 0 ≤ Real.log (2 + N) * Real.sqrt N := mul_nonneg hL0 hsN0
      nlinarith [h1, hp]
    calc (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
        ≤ Real.sqrt ((∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
            * ((smallSet N θ).card : ℝ)) := hS2
      _ ≤ Real.sqrt ((100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = 100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N) :=
          Real.sqrt_sq (by positivity)
  have hA : 400 * θ ^ 2 * N * (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
      ≤ 80000 * θ * N * Real.log (2 + N) := by
    have h1 : 400 * θ ^ 2 * N * (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
        ≤ 400 * θ ^ 2 * N * (200 * Real.log (2 + N)) :=
      mul_le_mul_of_nonneg_left hS1' (by positivity)
    have he : 400 * θ ^ 2 * N * (200 * Real.log (2 + N)) = 80000 * θ ^ 2 * N * Real.log (2 + N) := by
      ring
    have hp : 0 ≤ 80000 * N * Real.log (2 + N) := by positivity
    have h2 : 80000 * θ ^ 2 * N * Real.log (2 + N) ≤ 80000 * θ * N * Real.log (2 + N) := by
      nlinarith [hθ2, hp]
    linarith [h1, he.le, h2]
  have hB : 40 * θ * Real.sqrt N
        * (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
      ≤ 4000 * θ * N * Real.log (2 + N) := by
    have h1 : 40 * θ * Real.sqrt N
          * (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
        ≤ 40 * θ * Real.sqrt N
            * (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)) :=
      mul_le_mul_of_nonneg_left hS2'' (by positivity)
    have hsl : 100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N)
        ≤ 100 * Real.log (2 + N) * Real.sqrt N := by
      have h0 : 0 ≤ Real.sqrt (Real.log (2 + N)) := Real.sqrt_nonneg _
      have h0' : 0 ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_nonneg _
      nlinarith [hsqrtlog, hN14, h0, h0']
    have h2 : 40 * θ * Real.sqrt N * (100 * Real.sqrt (Real.log (2 + N)) * Real.sqrt (Real.sqrt N))
        ≤ 40 * θ * Real.sqrt N * (100 * Real.log (2 + N) * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hsl (by positivity)
    have he : 40 * θ * Real.sqrt N * (100 * Real.log (2 + N) * Real.sqrt N)
        = 4000 * θ * Real.log (2 + N) * (Real.sqrt N ^ 2) := by ring
    have h3 : 40 * θ * Real.sqrt N * (100 * Real.log (2 + N) * Real.sqrt N)
        ≤ 4000 * θ * N * Real.log (2 + N) := by
      rw [he, hsNsq]
      have hp : 0 ≤ 4000 * θ * Real.log (2 + N) := by positivity
      nlinarith [hp]
    linarith [h1, h2, h3]
  have hC : ((smallSet N θ).card : ℝ) ≤ 20 * Real.sqrt N * Real.log (2 + N) := by
    nlinarith [hcardN, hsN0, hlog1]
  have hfinal : 400 * θ ^ 2 * N * (∑ v ∈ smallSet N θ, (1 : ℝ) / ((Work.FIPlan.gnorm v : ℕ) : ℝ))
        + 40 * θ * Real.sqrt N
            * (∑ v ∈ smallSet N θ, (1 : ℝ) / Real.sqrt (((Work.FIPlan.gnorm v : ℕ) : ℝ)))
        + ((smallSet N θ).card : ℝ)
      ≤ 80000 * θ * N * Real.log (2 + N) + 4000 * θ * N * Real.log (2 + N)
        + 20 * Real.sqrt N * Real.log (2 + N) := by
    linarith [hA, hB, hC]
  have htail : 80000 * θ * N * Real.log (2 + N) + 4000 * θ * N * Real.log (2 + N)
        + 20 * Real.sqrt N * Real.log (2 + N)
      ≤ 200000 * (Real.sqrt N + θ * N) * Real.log (2 + N) := by
    have hp : 0 ≤ 200000 * θ * N * Real.log (2 + N) := by positivity
    have hq : 0 ≤ 200000 * Real.sqrt N * Real.log (2 + N) := by positivity
    nlinarith [hsN0, hL0, hθ, hN0, hp, hq]
  linarith [hfinal, htail]

/-! ## 5. The divisor reduction and the main theorem -/

/-- **The divisor reduction.**  Summing `τ(|z|²)` over the sector annulus (with squarefree norm)
and pairing each divisor with its Gaussian cofactor bounds the sum by the number of pairs
`(w, u)` of box elements with `w·u` in the sector annulus. -/
theorem sum_le_pairSet (N θ φ : ℝ) (hN : 1 ≤ N) :
    ∑ z ∈ zSet N θ φ, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ ((pairSet N θ φ).card : ℝ) := by
  have h1 : ∀ z ∈ zSet N θ φ, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ (((tauBox N θ).filter (fun w => w ∣ z)).card : ℝ) := by
    intro z hz
    rw [zSet, Finset.mem_filter] at hz
    obtain ⟨_, hzsect, hzsf⟩ := hz
    have hz0 : z ≠ 0 := ne_zero_of_sectAnn (by linarith) hzsect
    obtain ⟨f, hinj, hf⟩ := gaussian_divisor_count z hz0 hzsf
    have hcard : (Work.FIPlan.gnorm z).divisors.card
        ≤ ((tauBox N θ).filter (fun w => w ∣ z)).card := by
      have huniv : (Finset.univ : Finset (Work.FIPlan.gnorm z).divisors).card
          = (Work.FIPlan.gnorm z).divisors.card := by
        rw [Finset.card_univ, Fintype.card_coe]
      rw [← huniv]
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro d _
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨?_, (hf d).1⟩
        have hn : ((Work.FIPlan.gnorm (f d) : ℕ) : ℝ) ≤ (1 + θ) * N := by
          rw [(hf d).2]
          have hdvd : (d : ℕ) ∣ Work.FIPlan.gnorm z := (Nat.mem_divisors.mp d.2).1
          have hpos : 0 < Work.FIPlan.gnorm z := by
            have h2 : (0:ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by linarith [hzsect.1]
            exact_mod_cast h2
          have h3 := Nat.le_of_dvd hpos hdvd
          have h4 : ((d : ℕ) : ℝ) ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by exact_mod_cast h3
          linarith [h4, hzsect.2.1]
        exact mem_tauBox_of_gnorm_le N θ (by linarith) hn
      · intro d _ d' _ heq
        exact hinj heq
    exact_mod_cast hcard
  calc ∑ z ∈ zSet N θ φ, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ ∑ z ∈ zSet N θ φ, (((tauBox N θ).filter (fun w => w ∣ z)).card : ℝ) :=
        Finset.sum_le_sum h1
    _ = ∑ z ∈ zSet N θ φ, ∑ w ∈ tauBox N θ, (if w ∣ z then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.card_filter]
        push_cast
        rfl
    _ = ∑ w ∈ tauBox N θ, ∑ z ∈ zSet N θ φ, (if w ∣ z then (1 : ℝ) else 0) := Finset.sum_comm
    _ = (((tauBox N θ) ×ˢ (zSet N θ φ)).filter (fun p => p.1 ∣ p.2)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        push_cast
        rfl
    _ ≤ ((pairSet N θ φ).card : ℝ) := by
      have hstep : (((tauBox N θ) ×ˢ (zSet N θ φ)).filter (fun p => p.1 ∣ p.2)).card
          ≤ (pairSet N θ φ).card := by
        refine Finset.card_le_card_of_injOn
          (fun p : GaussianInt × GaussianInt =>
            (p.1, if h : p.1 ∣ p.2 then Classical.choose h else 0)) ?_ ?_
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_filter] at hp
          obtain ⟨hpmem, hdvd⟩ := hp
          rw [Finset.mem_product] at hpmem
          obtain ⟨hw, hz⟩ := hpmem
          rw [zSet, Finset.mem_filter] at hz
          obtain ⟨_, hzsect, _⟩ := hz
          set u : GaussianInt := Classical.choose hdvd with hu_def
          have hu : p.2 = p.1 * u := Classical.choose_spec hdvd
          have hif : (if h : p.1 ∣ p.2 then Classical.choose h else 0) = u := by
            rw [dif_pos hdvd, hu_def]
          change (p.1, (if h : p.1 ∣ p.2 then Classical.choose h else 0)) ∈ pairSet N θ φ
          rw [hif, pairSet, Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨hw, ?_⟩, ?_⟩
          · have hp1ne : p.1 ≠ 0 := by
              intro h0
              rw [h0, zero_mul] at hu
              exact ne_zero_of_sectAnn (by linarith) hzsect hu
            have hk1 : 1 ≤ Work.FIPlan.gnorm p.1 := one_le_gnorm_of_ne_zero p.1 hp1ne
            have hgn : Work.FIPlan.gnorm p.2 = Work.FIPlan.gnorm p.1 * Work.FIPlan.gnorm u := by
              rw [hu, gnorm_mul]
            have hle : ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ (1 + θ) * N := by
              have h1' : ((Work.FIPlan.gnorm p.2 : ℕ) : ℝ) ≤ (1 + θ) * N := hzsect.2.1
              rw [hgn, Nat.cast_mul] at h1'
              have h2 : ((Work.FIPlan.gnorm u : ℕ) : ℝ)
                  ≤ ((Work.FIPlan.gnorm p.1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm u : ℕ) : ℝ) := by
                have h3 : (1:ℝ) ≤ ((Work.FIPlan.gnorm p.1 : ℕ) : ℝ) := by exact_mod_cast hk1
                have h4 : (0:ℝ) ≤ ((Work.FIPlan.gnorm u : ℕ) : ℝ) := by positivity
                nlinarith
              linarith
            exact mem_tauBox_of_gnorm_le N θ (by linarith) hle
          · rw [← hu]
            exact hzsect
        · intro p hp q hq heq
          have hpd : p.1 ∣ p.2 := (Finset.mem_filter.mp hp).2
          have hqd : q.1 ∣ q.2 := (Finset.mem_filter.mp hq).2
          set u : GaussianInt := Classical.choose hpd with hu_def
          set uq : GaussianInt := Classical.choose hqd with huq_def
          have hu : p.2 = p.1 * u := by
            rw [hu_def]
            exact Classical.choose_spec hpd
          have huq : q.2 = q.1 * uq := by
            rw [huq_def]
            exact Classical.choose_spec hqd
          have heq' : (p.1, u) = (q.1, uq) := by
            have h1 : (if h : p.1 ∣ p.2 then Classical.choose h else 0) = u := by
              rw [dif_pos hpd, hu_def]
            have h2 : (if h : q.1 ∣ q.2 then Classical.choose h else 0) = uq := by
              rw [dif_pos hqd, huq_def]
            have heq'' : (p.1, (if h : p.1 ∣ p.2 then Classical.choose h else 0))
                = (q.1, (if h : q.1 ∣ q.2 then Classical.choose h else 0)) := heq
            rw [h1, h2] at heq''
            exact heq''
          obtain ⟨hpe, hue⟩ := Prod.ext_iff.mp heq'
          have hpe' : p.1 = q.1 := hpe
          have hue' : u = uq := hue
          have h2 : p.2 = q.2 := by
            rw [hu, huq, hpe', hue']
          exact Prod.ext hpe' h2
      exact_mod_cast hstep

/-- The filter of the statement is the sector annulus with squarefree norm. -/
theorem tau_filter_eq_zSet (N θ φ : ℝ) :
    (Work.FIPlan.gBox (⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ)).filter
        (fun z => N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
                  ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + θ) * N ∧
                  φ < Complex.arg z.toComplex ∧
                  Complex.arg z.toComplex ≤ φ + 2 * Real.pi * θ ∧
                  Squarefree (Work.FIPlan.gnorm z))
      = zSet N θ φ := by
  rw [zSet, tauBox, gBoxI_eq_gBox]
  apply Finset.filter_congr
  intro z _
  simp only [sectAnn]
  tauto

theorem sector_tau_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (N θ : ℝ) (φ : ℝ), 1 ≤ N → 0 ≤ θ → θ ≤ 1 →
      ∑ z ∈ (Work.FIPlan.gBox (⌈Real.sqrt (4 * N * (1 + θ))⌉₊ : ℤ)).filter
          (fun z => N < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
                    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + θ) * N ∧
                    φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * θ ∧
                    Squarefree (Work.FIPlan.gnorm z)),
        (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ C * (Real.sqrt N + θ * N) * (Real.log (2 + N)) ^ 9 := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro N θ φ hN hθ hθ1
  rw [tau_filter_eq_zSet N θ φ]
  have h1 := sum_le_pairSet N θ φ hN
  have h2 := pair_card_le N θ φ hN hθ hθ1
  have h3 := smallSet_sum_bound N θ hN hθ hθ1
  have hL1 : (1:ℝ) ≤ Real.log (2 + N) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_three
    linarith
  have hL9 : Real.log (2 + N) ≤ (Real.log (2 + N)) ^ 9 := by
    have hp : (1:ℝ) ≤ (Real.log (2 + N)) ^ 8 := one_le_pow₀ hL1
    nlinarith [hL1, hp]
  have hbase : 0 ≤ Real.sqrt N + θ * N := by positivity
  have hbase2 : 0 ≤ 400000 * (Real.sqrt N + θ * N) := by positivity
  have hmid : 400000 * (Real.sqrt N + θ * N) * Real.log (2 + N)
      ≤ 400000 * (Real.sqrt N + θ * N) * (Real.log (2 + N)) ^ 9 :=
    mul_le_mul_of_nonneg_left hL9 hbase2
  nlinarith [h1, h2, h3, hmid, hbase, hbase2]

end

end Work.FIArea6b
