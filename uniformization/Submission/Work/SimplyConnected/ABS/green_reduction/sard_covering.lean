import Mathlib

/-!
# Sard-lite, step 1: the covering lemma

The quantitative core of Sard's lemma for a `C³` function `f : ℂ → ℝ`: **if the values of `f` at
two nearby critical points differ cubically in the distance of the points**, then the critical
values of `f` on a disc are covered by finitely many intervals of arbitrarily small total length.

The estimate `|f p - f x| ≤ C * ‖p - x‖ ^ 3` for critical `x, p` is the whole analytic content of
Sard's lemma in dimension two (it follows from the second-order Taylor expansion of `f` and the
first-order expansion of `Df`: both `Df x` and `Df p` vanish, whence `D²f x (p - x) = O(‖p-x‖²)` and
`f p - f x = (1/2) D²f x (p - x, p - x) + O(‖p-x‖³) = O(‖p-x‖³)`).

Here we prove the *elementary* consequence, with no analysis at all: cover the disc of radius `R` by
the points of a grid of mesh `R/(2(n+1))`, pick, for each grid cell meeting the critical set, one
critical point in it, and use the interval of radius `8 * C * (R/(n+1))³` around its value; the
total length is `≤ 1296 * C * R³ / (n+1)`, which tends to `0`.
-/

open Set Metric Filter
open scoped Topology

namespace Work.SimplyConnected.ABS.green_reduction

/-- One-dimensional grid step. -/
lemma exists_nat_sub_close {h : ℝ} (hh : 0 < h) {K : ℕ} {x : ℝ} (hx : |x| ≤ (K : ℝ) * h) :
    ∃ i : ℕ, i ≤ 2 * K ∧ |x - h * ((i : ℝ) - K)| ≤ h := by
  have hdiv_le : x / h ≤ (K : ℝ) := by
    rw [div_le_iff₀ hh]; linarith [le_abs_self x, hx]
  have hdiv_ge : -(K : ℝ) ≤ x / h := by
    rw [le_div_iff₀ hh]; linarith [neg_abs_le x, hx]
  have hfl : ⌊x / h⌋ ≤ (K : ℤ) := by
    have h1 : (⌊x / h⌋ : ℝ) ≤ (K : ℝ) := le_trans (Int.floor_le _) hdiv_le
    exact_mod_cast h1
  have hfg : -(K : ℤ) ≤ ⌊x / h⌋ := by
    have h1 : (-(K : ℝ) - 1) < (⌊x / h⌋ : ℝ) := by
      have h2 := Int.lt_floor_add_one (x / h); linarith
    have h2 : ((-(K : ℤ) - 1 : ℤ) : ℝ) < (⌊x / h⌋ : ℝ) := by push_cast; linarith
    have h3 : (-(K : ℤ) - 1) < ⌊x / h⌋ := Int.cast_lt.mp h2
    omega
  have hnn : 0 ≤ ⌊x / h⌋ + (K : ℤ) := by omega
  refine ⟨(⌊x / h⌋ + (K : ℤ)).toNat, ?_, ?_⟩
  · have h2 : (((⌊x / h⌋ + (K : ℤ)).toNat : ℕ) : ℤ) ≤ 2 * (K : ℤ) := by
      rw [Int.toNat_of_nonneg hnn]; omega
    exact_mod_cast h2
  · have hkey : (((⌊x / h⌋ + (K : ℤ)).toNat : ℕ) : ℝ) - K = ((⌊x / h⌋ : ℤ) : ℝ) := by
      have hcast : (((⌊x / h⌋ + (K : ℤ)).toNat : ℕ) : ℝ) = ((⌊x / h⌋ + (K : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hnn :
          (((⌊x / h⌋ + (K : ℤ)).toNat : ℕ) : ℤ) = ⌊x / h⌋ + (K : ℤ))
      rw [hcast]; push_cast; ring
    rw [hkey, abs_le]
    have h1 := Int.floor_le (x / h); have h2 := Int.lt_floor_add_one (x / h)
    rw [le_div_iff₀ hh] at h1
    rw [div_lt_iff₀ hh] at h2
    constructor <;> linarith

/-- **The grid cover of a disc.** -/
lemma exists_grid_cover (R : ℝ) (n : ℕ) (hR : 0 < R) :
    ∃ a : Fin (4 * n + 5) × Fin (4 * n + 5) → ℂ,
      ∀ z : ℂ, ‖z‖ ≤ R → ∃ ij, ‖z - a ij‖ ≤ R / (n + 1) := by
  set K : ℕ := 2 * (n + 1) with hK
  set h : ℝ := R / (2 * ((n : ℝ) + 1)) with hh
  have hKreal : ((K : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by rw [hK]; push_cast; ring
  have hcard : 4 * n + 5 = 2 * K + 1 := by rw [hK]; omega
  have hhpos : 0 < h := by rw [hh]; positivity
  refine ⟨fun ij => ((h * (((ij.1 : ℕ) : ℝ) - (K : ℕ))) : ℂ) +
    ((h * (((ij.2 : ℕ) : ℝ) - (K : ℕ))) : ℂ) * Complex.I, ?_⟩
  intro z hz
  have hKh : (K : ℝ) * h = R := by
    rw [hh, hKreal, mul_div_assoc']
    rw [mul_div_cancel_left₀ R (by positivity : (2 * ((n : ℝ) + 1)) ≠ 0)]
  have hzre : |z.re| ≤ R := by
    have h1 := Complex.abs_re_le_norm z
    rw [abs_le] at h1 ⊢
    exact ⟨by linarith [h1.1, hz], by linarith [h1.2, hz]⟩
  have hzim : |z.im| ≤ R := by
    have h1 := Complex.abs_im_le_norm z
    rw [abs_le] at h1 ⊢
    exact ⟨by linarith [h1.1, hz], by linarith [h1.2, hz]⟩
  obtain ⟨i, hi2K, hi⟩ := exists_nat_sub_close hhpos (K := K) (x := z.re)
    (by rw [hKh]; linarith [le_abs_self z.re, hzre])
  obtain ⟨j, hj2K, hj⟩ := exists_nat_sub_close hhpos (K := K) (x := z.im)
    (by rw [hKh]; linarith [le_abs_self z.im, hzim])
  refine ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), ?_⟩
  have hsub : z - ((h * ((i : ℝ) - (K : ℕ)) : ℂ) + ((h * ((j : ℝ) - (K : ℕ))) : ℂ) * Complex.I)
      = (((z.re - h * ((i : ℝ) - (K : ℕ))) : ℝ) : ℂ) +
        (((z.im - h * ((j : ℝ) - (K : ℕ))) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [hsub, Complex.norm_add_mul_I]
  have hle1 : (z.re - h * ((i : ℝ) - (K : ℕ))) ^ 2 ≤ h ^ 2 := by
    have := abs_le.mp hi; nlinarith
  have hle2 : (z.im - h * ((j : ℝ) - (K : ℕ))) ^ 2 ≤ h ^ 2 := by
    have := abs_le.mp hj; nlinarith
  have hsum : (z.re - h * ((i : ℝ) - (K : ℕ))) ^ 2 +
      (z.im - h * ((j : ℝ) - (K : ℕ))) ^ 2 ≤ 2 * h ^ 2 := by linarith
  refine le_trans (Real.sqrt_le_sqrt hsum) ?_
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (h ^ 2), Real.sqrt_sq hhpos.le, hh]
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hmul : Real.sqrt 2 * (R / (2 * ((n : ℝ) + 1))) ≤ 2 * (R / (2 * ((n : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right hs (by positivity)
  refine le_trans hmul ?_
  rw [mul_div_assoc']
  rw [mul_div_mul_left R ((n : ℝ) + 1) (by norm_num : (2:ℝ) ≠ 0)]



/-- Auxiliary form of the covering lemma, with the product index. -/
lemma exists_intervals_cover_criticalValues_aux {f : ℂ → ℝ} {R C ε : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hε : 0 < ε)
    (hcub : ∀ x : ℂ, ‖x‖ ≤ R → fderiv ℝ f x = 0 → ∀ p : ℂ, ‖p‖ ≤ R → fderiv ℝ f p = 0 →
      |f p - f x| ≤ C * ‖p - x‖ ^ 3) :
    ∃ (A : ℕ) (l u : Fin A × Fin A → ℝ), (∀ i, l i ≤ u i) ∧
      (∑ i, (u i - l i)) < ε ∧
      ∀ z : ℂ, ‖z‖ ≤ R → fderiv ℝ f z = 0 → ∃ i, f z ∈ Set.Icc (l i) (u i) := by
  classical
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · refine ⟨1, fun _ => f 0, fun _ => f 0, fun i => le_refl _, ?_, ?_⟩
    · have hzero : (∑ i : Fin 1 × Fin 1, ((fun _ : Fin 1 × Fin 1 => f 0) i -
          (fun _ : Fin 1 × Fin 1 => f 0) i)) = 0 := by simp
      rw [hzero]; exact hε
    · intro z hz _
      have hz0 : z = 0 := by
        have h1 : ‖z‖ = 0 := le_antisymm (hR0 ▸ hz) (norm_nonneg z)
        exact norm_eq_zero.mp h1
      exact ⟨(0, 0), by simp [hz0]⟩
  · -- the threshold `n`
    obtain ⟨M, hM⟩ := exists_nat_gt (1296 * C * R ^ 3 / ε)
    set n : ℕ := M with hn
    have hn1 : 1296 * C * R ^ 3 / ((n : ℝ) + 1) < ε := by
      have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hpos]
      have h2 : ε * (n : ℝ) > 1296 * C * R ^ 3 := by
        have h3 := (div_lt_iff₀ hε).mp hM
        linarith [h3]
      have hn0 : (0:ℝ) ≤ (n : ℝ) := by positivity
      linarith [h2, hε, hn0]
    obtain ⟨a, ha⟩ := exists_grid_cover R n hRpos
    set ρ : ℝ := R / ((n : ℝ) + 1) with hρ
    have hρpos : 0 < ρ := by rw [hρ]; positivity
    let P : Fin (4 * n + 5) × Fin (4 * n + 5) → Prop := fun ij =>
      ∃ z : ℂ, ‖z‖ ≤ R ∧ fderiv ℝ f z = 0 ∧ ‖z - a ij‖ ≤ ρ
    let zof : Fin (4 * n + 5) × Fin (4 * n + 5) → ℂ := fun ij =>
      if h : P ij then Classical.choose h else 0
    have hzof : ∀ ij, P ij → ‖zof ij‖ ≤ R ∧ fderiv ℝ f (zof ij) = 0 ∧ ‖zof ij - a ij‖ ≤ ρ := by
      intro ij h
      simp only [zof, dif_pos h]
      exact Classical.choose_spec h
    let l : Fin (4 * n + 5) × Fin (4 * n + 5) → ℝ := fun ij =>
      if h : P ij then f (zof ij) - 8 * C * ρ ^ 3 else 0
    let u : Fin (4 * n + 5) × Fin (4 * n + 5) → ℝ := fun ij =>
      if h : P ij then f (zof ij) + 8 * C * ρ ^ 3 else 0
    refine ⟨4 * n + 5, l, u, ?_, ?_, ?_⟩
    · intro ij
      by_cases h : P ij
      · simp only [l, u, dif_pos h]; nlinarith [pow_nonneg hρpos.le 3, hC]
      · simp only [l, u, dif_neg h]; exact le_refl 0
    · have hstep : ∀ ij, u ij - l ij ≤ 16 * C * ρ ^ 3 := by
        intro ij
        by_cases h : P ij
        · simp only [l, u, dif_pos h]
          nlinarith [pow_nonneg hρpos.le 3, hC]
        · simp only [l, u, dif_neg h, sub_self]
          positivity
      have hsmall : ((4 * n + 5) * (4 * n + 5) : ℝ) * (16 * C * ρ ^ 3) < ε := by
        have h4n : ((4 * n + 5 : ℕ) : ℝ) ≤ 9 * ((n : ℝ) + 1) := by push_cast; linarith
        have hsq : ((4 * n + 5 : ℕ) : ℝ) ^ 2 ≤ (9 * ((n : ℝ) + 1)) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) h4n
        have hb2 : ((4 * n + 5 : ℕ) : ℝ) ^ 2 * (16 * C * ρ ^ 3) ≤
            (9 * ((n : ℝ) + 1)) ^ 2 * (16 * C * ρ ^ 3) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
        have hρ3 : ρ ^ 3 = R ^ 3 / ((n : ℝ) + 1) ^ 3 := by
          rw [hρ, div_pow]
        have hkey : (9 * ((n : ℝ) + 1)) ^ 2 * (16 * C * ρ ^ 3) =
            1296 * C * R ^ 3 / ((n : ℝ) + 1) := by
          rw [hρ3]; field_simp; ring
        calc ((4 * n + 5) * (4 * n + 5) : ℝ) * (16 * C * ρ ^ 3)
            = ((4 * n + 5 : ℕ) : ℝ) ^ 2 * (16 * C * ρ ^ 3) := by push_cast; ring
          _ ≤ (9 * ((n : ℝ) + 1)) ^ 2 * (16 * C * ρ ^ 3) := hb2
          _ = 1296 * C * R ^ 3 / ((n : ℝ) + 1) := hkey
          _ < ε := hn1
      calc ∑ ij, (u ij - l ij)
          ≤ ∑ _ij : Fin (4 * n + 5) × Fin (4 * n + 5), (16 * C * ρ ^ 3) :=
            Finset.sum_le_sum (fun ij _ => hstep ij)
        _ = ((4 * n + 5) * (4 * n + 5)) * (16 * C * ρ ^ 3) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              nsmul_eq_mul]
        _ < ε := hsmall
    · intro z hz hcrit
      obtain ⟨ij, hij⟩ := ha z hz
      have hP : P ij := ⟨z, hz, hcrit, hij⟩
      obtain ⟨hzR, hzc, hzdist⟩ := hzof ij hP
      have hdist : ‖z - zof ij‖ ≤ 2 * ρ := by
        calc ‖z - zof ij‖ = ‖(z - a ij) + (a ij - zof ij)‖ := by ring_nf
          _ ≤ ‖z - a ij‖ + ‖a ij - zof ij‖ := norm_add_le _ _
          _ ≤ ρ + ρ := add_le_add hij (by rwa [norm_sub_rev] at hzdist)
          _ = 2 * ρ := by ring
      have hc := hcub z hz hcrit (zof ij) hzR hzc
      have hc' : |f (zof ij) - f z| ≤ C * ‖z - zof ij‖ ^ 3 := by
        rw [norm_sub_rev] at hc
        exact hc
      refine ⟨ij, ?_⟩
      simp only [l, u, dif_pos hP, Set.mem_Icc]
      have h3 : C * ‖z - zof ij‖ ^ 3 ≤ C * (2 * ρ) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact pow_le_pow_left₀ (norm_nonneg _) hdist 3
      have h4 : |f (zof ij) - f z| ≤ C * (2 * ρ) ^ 3 := le_trans hc' h3
      have h8 : C * (2 * ρ) ^ 3 = 8 * C * ρ ^ 3 := by ring
      have hb := abs_le.mp h4
      rw [h8] at hb
      constructor <;> linarith [hb.1, hb.2]



/-- **Sard-lite, covering form** (the `Fin n`-indexed statement). -/
theorem exists_intervals_cover_criticalValues {f : ℂ → ℝ} {R C ε : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hε : 0 < ε)
    (hcub : ∀ x : ℂ, ‖x‖ ≤ R → fderiv ℝ f x = 0 → ∀ p : ℂ, ‖p‖ ≤ R → fderiv ℝ f p = 0 →
      |f p - f x| ≤ C * ‖p - x‖ ^ 3) :
    ∃ (n : ℕ) (l u : Fin n → ℝ), (∀ i, l i ≤ u i) ∧ (∑ i, (u i - l i)) < ε ∧
      ∀ z : ℂ, ‖z‖ ≤ R → fderiv ℝ f z = 0 → ∃ i, f z ∈ Set.Icc (l i) (u i) := by
  classical
  obtain ⟨A, l, u, hlu, hsum, hcov⟩ := exists_intervals_cover_criticalValues_aux hR hC hε hcub
  let e : Fin A × Fin A ≃ Fin (Fintype.card (Fin A × Fin A)) := Fintype.equivFin _
  refine ⟨Fintype.card (Fin A × Fin A), fun k => l (e.symm k), fun k => u (e.symm k),
    fun k => hlu (e.symm k), ?_, ?_⟩
  · rw [← Fintype.sum_equiv e (fun x => u x - l x) (fun k => u (e.symm k) - l (e.symm k))
      (fun x => by simp)]
    exact hsum
  · intro z hz hcrit
    obtain ⟨x, hx⟩ := hcov z hz hcrit
    exact ⟨e x, by simpa using hx⟩

end Work.SimplyConnected.ABS.green_reduction
