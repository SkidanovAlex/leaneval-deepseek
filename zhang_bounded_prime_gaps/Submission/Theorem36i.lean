import Mathlib
import Submission.GoodMainSumAsymptotic
import Submission.SieveSupport
import Submission.Commons.Analysis.Asymptotics.tendsto_mul_rpow_mul_log_pow_zero

open scoped BigOperators Topology
open Filter MeasureTheory

set_option maxHeartbeats 1000000

/-!
# Polymath8a Theorem 3.6(i): the `S₁` window sum

This module assembles the *unconditional* case (i) of Polymath8a Theorem 3.6:
for smooth compactly supported `Fᵢ, Gᵢ : ℝ → ℝ` whose supports satisfy
`Σᵢ (S(Fᵢ) + S(Gᵢ)) < 1`, and for a modulus family `W = W(x)` (all primes
`≤ w(x)` divide `W(x)`, `log W(x) = o(√(log x))`, `w(x) → ∞`),

    Σ_{x ≤ n ≤ 2x, n ≡ b (W)} ∏ᵢ λ_{Fᵢ}(n+hᵢ) λ_{Gᵢ}(n+hᵢ)
      = (c + o(1))·B^{-k}·x/W ,     c = ∏ᵢ ∫₀^∞ Fᵢ′(t)Gᵢ′(t) dt,

where `B = φ(W)/W · log x` and `W` is `W(x)` — this is (29) of the paper in
the case (27).

The proof combines the window expansion (`windowLambdaProduct_eq_main_add_error`),
the evaluation of the main term (`goodMainSum_asymptotic`, i.e. the pairwise
Lemma 4.1) and the `O(x^{σ})` bound for the collected `S`-counting errors
(`goodErrSum_le_rpow`).
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The residue-window sum of a product of two Maynard divisor sums per
coordinate, truncated at divisors `≤ D`. -/
noncomputable def windowDivisorProduct {k : ℕ} (F G : Fin k → ℝ → ℝ) (H : Fin k → ℕ)
    (W b D x : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => n % W = b % W),
    ∏ i : Fin k,
      (∑ d : Fin (D + 1),
        lamDivWeight (F i) x d * (if (d : ℕ) ∣ n + H i then (1 : ℝ) else 0)) *
      (∑ e : Fin (D + 1),
        lamDivWeight (G i) x e * (if (e : ℕ) ∣ n + H i then (1 : ℝ) else 0))

/-- The main term of the `S₁` sum, `x·B^{-k}·∏ᵢ ∫₀^∞ Fᵢ′Gᵢ′` (with `B` encoded
through `prefactor`), written at the Mathlib (complex) Fourier normalization:
the `deriv` factors are cast to `ℂ`. -/
noncomputable def mainTarget {k : ℕ} (F G : Fin k → ℝ → ℝ) (W : ℕ → ℕ) (x : ℕ) : ℂ :=
  ((((x : ℝ) / (W x : ℝ)) * (prefactor W (fun _ => 1) x) ^ k : ℝ) : ℂ) *
    ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
      ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))

/-- The real prefactor of the main term, `x/W · B^{-k}`. -/
noncomputable def mainScale (k : ℕ) (W : ℕ → ℕ) (x : ℕ) : ℝ :=
  ((x : ℝ) / (W x : ℝ)) * (prefactor W (fun _ => 1) x) ^ k

/-- `mainTerm` is linear in the window scale. -/
lemma mainTerm_eq_mul_mainTerm_one {k : ℕ} (N W : ℕ) (m : Fin k → ℕ) :
    mainTerm N W m = (N : ℝ) * mainTerm 1 W m := by
  unfold mainTerm
  push_cast
  ring

/-- The `lcmGood` main sum is linear in the window scale. -/
lemma goodMainSum_eq_mul_goodMainSum_one {k D W N : ℕ} (α β : Fin k → ℕ → ℝ) :
    goodMainSum (k := k) (D := D) (N := N) (W := W) α β =
      (N : ℝ) * goodMainSum (k := k) (D := D) (N := 1) (W := W) α β := by
  unfold goodMainSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mainTerm_eq_mul_mainTerm_one]
  ring

/-! ## Elementary bounds on the main scale `x/W · B^{-k}`

`prefactor W (fun _ => 1) x = (W/φ(W))·(log x)^{-1} ≥ (log x)^{-1}` since
`W/φ(W) ≥ 1`, so the main scale dominates `x/(W·(log x)^k)`. -/

/-- `(log x)^{-1} ≤ prefactor W 1 x` (for `2 ≤ x`, `W x ≠ 0`). -/
lemma inv_log_le_prefactor_one {W : ℕ → ℕ} {x : ℕ} (hW : W x ≠ 0) (hx : 2 ≤ x) :
    (Real.log (x : ℝ))⁻¹ ≤ prefactor W (fun _ => 1) x := by
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hφpos : 0 < (W x).totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)
  have hφr : (0:ℝ) < ((W x).totient : ℝ) := by exact_mod_cast hφpos
  have hquot : 1 ≤ (W x : ℝ) / ((W x).totient : ℝ) := by
    rw [le_div_iff₀ hφr, one_mul]
    exact_mod_cast Nat.totient_le (W x)
  have hinv : 0 ≤ (Real.log (x:ℝ))⁻¹ := by positivity
  rw [prefactor]
  simp only [Nat.totient_one]
  norm_num
  calc (Real.log (x:ℝ))⁻¹ = 1 * (Real.log (x:ℝ))⁻¹ := (one_mul _).symm
    _ ≤ ((W x : ℝ) / ((W x).totient : ℝ)) * (Real.log (x:ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hquot hinv

/-- The main scale dominates `x/(W·(log x)^k)`. -/
lemma mainScale_ge {W : ℕ → ℕ} {x : ℕ} (hW : W x ≠ 0) (hx : 2 ≤ x) (k : ℕ) :
    (x : ℝ) / (W x : ℝ) * ((Real.log (x : ℝ)) ^ k)⁻¹ ≤ mainScale k W x := by
  have h1 := inv_log_le_prefactor_one (W := W) hW hx
  have hinvnn : 0 ≤ (Real.log (x:ℝ))⁻¹ := by
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    positivity
  have hpow : ((Real.log (x:ℝ))⁻¹) ^ k ≤ (prefactor W (fun _ => 1) x) ^ k :=
    pow_le_pow_left₀ hinvnn h1 k
  have hxW : 0 ≤ (x : ℝ) / (W x : ℝ) := by positivity
  calc (x : ℝ) / (W x : ℝ) * ((Real.log (x : ℝ)) ^ k)⁻¹
      = (x : ℝ) / (W x : ℝ) * ((Real.log (x:ℝ))⁻¹) ^ k := by rw [inv_pow]
    _ ≤ (x : ℝ) / (W x : ℝ) * (prefactor W (fun _ => 1) x) ^ k :=
        mul_le_mul_of_nonneg_left hpow hxW
    _ = mainScale k W x := by rw [mainScale]

/-- The main scale is positive. -/
lemma mainScale_pos {W : ℕ → ℕ} {x : ℕ} (hW : W x ≠ 0) (hx : 2 ≤ x) (k : ℕ) :
    0 < mainScale k W x :=
  lt_of_lt_of_le (by
    have hWpos : (0:ℝ) < (W x : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hW
    have hlog : 0 < Real.log (x:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hk : 0 < (Real.log (x:ℝ))^k := pow_pos hlog k
    positivity) (mainScale_ge hW hx k)

/-- The `O(x^σ)` sieve error is `o(x/W · B^{-k})`. -/
lemma errRatio_le {W : ℕ → ℕ} {x : ℕ} (hW : W x ≠ 0) (hx : 2 ≤ x) (k : ℕ) {C σ : ℝ}
    (hC : 0 ≤ C) :
    C * (x : ℝ) ^ σ / mainScale k W x ≤
      C * ((W x : ℝ) * (x : ℝ) ^ (σ - 1) * (Real.log (x : ℝ)) ^ k) := by
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hxr : (0:ℝ) < (x : ℝ) := by positivity
  have hWr : (0:ℝ) < (W x : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hW
  have hlow : (0:ℝ) < (x : ℝ) / (W x : ℝ) * ((Real.log (x : ℝ)) ^ k)⁻¹ := by positivity
  have hge := mainScale_ge (W := W) hW hx k
  have hpos : 0 < mainScale k W x := lt_of_lt_of_le hlow hge
  have hinv : (mainScale k W x)⁻¹ ≤ ((x : ℝ) / (W x : ℝ) * ((Real.log (x : ℝ)) ^ k)⁻¹)⁻¹ :=
    (inv_le_inv₀ hpos hlow).mpr hge
  have hhigh : ((x : ℝ) / (W x : ℝ) * ((Real.log (x : ℝ)) ^ k)⁻¹)⁻¹ =
      (W x : ℝ) * (Real.log (x : ℝ)) ^ k / (x : ℝ) := by
    have hxne : (x : ℝ) ≠ 0 := hxr.ne'
    have hlne : (Real.log (x : ℝ)) ^ k ≠ 0 := pow_ne_zero k hlog.ne'
    field_simp
  have hCs : 0 ≤ C * (x : ℝ) ^ σ := mul_nonneg hC (Real.rpow_nonneg hxr.le σ)
  calc C * (x : ℝ) ^ σ / mainScale k W x
      = C * (x : ℝ) ^ σ * (mainScale k W x)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ C * (x : ℝ) ^ σ * ((x : ℝ) / (W x : ℝ) * ((Real.log (x : ℝ)) ^ k)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hCs
    _ = C * (x : ℝ) ^ σ * ((W x : ℝ) * (Real.log (x : ℝ)) ^ k / (x : ℝ)) := by rw [hhigh]
    _ = C * ((W x : ℝ) * ((x : ℝ) ^ σ / (x : ℝ)) * (Real.log (x : ℝ)) ^ k) := by ring
    _ = C * ((W x : ℝ) * (x : ℝ) ^ (σ - 1) * (Real.log (x : ℝ)) ^ k) := by
        rw [← Real.rpow_sub_one hxr.ne' σ]



/-! ## Theorem 3.6(i) (Polymath8a), assembled -/

/-- **Polymath8a Theorem 3.6(i)** (case (27)), in the form used below: the
residue-window sum of the product of the Maynard divisor sums `λ_{Fᵢ}λ_{Gᵢ}` is
`(1 + o(1)) · x/W · B^{-k} · ∏ᵢ ∫₀^∞ Fᵢ′Gᵢ′`, where `B^{-1} = prefactor W 1 x`.

The extra hypothesis `hvan` is the (fully explicit) information that
`W(x)·x^{2ΣM-1}·(log x)^k → 0`, which is what the `O(x^{2ΣM})` error bound
requires; in applications it is derived from `log W(x) = o(√(log x))` and
`2 Σ M < 1` (see `theorem36_i`). -/
theorem theorem36_i_of_small {k : ℕ} (hk : 1 ≤ k) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (M : Fin k → ℝ) (hMnn : ∀ i, 0 ≤ M i)
    (hsupp : ∀ i t, M i < |t| → F i t = 0 ∧ G i t = 0)
    (hσ1 : 2 * (∑ i, M i) < 1)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (∑ i, M i) ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x))
    (hvan : Tendsto (fun x : ℕ => (W x : ℝ) * (x : ℝ) ^ (2 * (∑ i, M i) - 1) *
      (Real.log (x : ℝ)) ^ k) atTop (𝓝 0)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      ‖(((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x‖
        ≤ ε x * mainScale k W x := by
  classical
  set M0 : ℝ := ∑ i, M i with hM0
  have hM0nn : 0 ≤ M0 := by rw [hM0]; exact Finset.sum_nonneg fun i _ => hMnn i
  have hMile : ∀ i, M i ≤ M0 := by
    intro i
    rw [hM0]
    exact Finset.single_le_sum (fun j _ => hMnn j) (Finset.mem_univ i)
  obtain ⟨x₀s, εs, hεs, hbd⟩ := goodMainSum_asymptotic (k := k) hk F G hcsF hsmF hcsG hsmG
    W hW w hw hsmall hlq
    (M := M0) (fun i t ht => hsupp i t (lt_of_le_of_lt (hMile i) ht)) D (by simpa [hM0] using hD)
  have hvan' : Tendsto (fun x : ℕ => (W x : ℝ) * (x : ℝ) ^ (2 * M0 - 1) *
      (Real.log (x : ℝ)) ^ k) atTop (𝓝 0) := by simpa [hM0] using hvan
  have hBFex : ∀ i, ∃ C, 0 ≤ C ∧ ∀ t, |F i t| ≤ C := fun i =>
    exists_abs_bound_of_hasCompactSupport (F i) (hcsF i) (hsmF i).continuous
  have hBGex : ∀ i, ∃ C, 0 ≤ C ∧ ∀ t, |G i t| ≤ C := fun i =>
    exists_abs_bound_of_hasCompactSupport (G i) (hcsG i) (hsmG i).continuous
  choose BF hBF0 hBF using hBFex
  choose BG hBG0 hBG using hBGex
  set C₀ : ℝ := 2 * 4 ^ (2 * k) * (∏ i, BF i) * (∏ i, BG i) with hC₀
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀]
    have h1 : (0:ℝ) ≤ (∏ i, BF i) := Finset.prod_nonneg fun i _ => hBF0 i
    have h2 : (0:ℝ) ≤ (∏ i, BG i) := Finset.prod_nonneg fun i _ => hBG0 i
    have h3 : (0:ℝ) ≤ 4 ^ (2 * k) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h3) h1) h2
  obtain ⟨x₀w, hx₀w⟩ := Filter.eventually_atTop.mp
    ((hw.eventually_ge_atTop (2 : ℕ)).and (hw.eventually_gt_atTop (∑ i, H i)))
  have hD' : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ M0 ≤ (D x : ℝ) := by simpa only [hM0] using hD
  obtain ⟨x₀D, hx₀D⟩ := Filter.eventually_atTop.mp hD'
  refine ⟨max (max (max x₀s x₀D) x₀w) 2,
    fun x => εs x + C₀ * (x : ℝ) ^ (2 * M0) / mainScale k W x, ?_, ?_⟩
  · have hg : Tendsto (fun x : ℕ => C₀ * (x : ℝ) ^ (2 * M0) / mainScale k W x)
        atTop (𝓝 0) := by
      refine squeeze_zero' (g := fun x : ℕ => C₀ * ((W x : ℝ) * (x : ℝ) ^ (2 * M0 - 1) *
        (Real.log (x : ℝ)) ^ k)) ?_ ?_ ?_
      · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx2
        have hms : 0 < mainScale k W x := mainScale_pos (W := W) (x := x) (hW x) hx2 k
        exact div_nonneg (mul_nonneg hC₀nn (Real.rpow_nonneg (by positivity) _)) hms.le
      · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx2
        exact errRatio_le (W := W) (x := x) (hW x) hx2 k (C := C₀) (σ := 2 * M0) hC₀nn
      · have h1 : Tendsto (fun x : ℕ => C₀ * ((W x : ℝ) * (x : ℝ) ^ (2 * M0 - 1) *
            (Real.log (x : ℝ)) ^ k)) atTop (𝓝 (C₀ * 0)) := hvan'.const_mul C₀
        simpa using h1
    simpa using hεs.add hg
  · intro x hx
    have hx2 : 2 ≤ x := le_trans (le_max_right (max (max x₀s x₀D) x₀w) 2) hx
    have hx1 : 1 < x := by omega
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx1)
    have hxs : x₀s ≤ x :=
      le_trans (le_max_left x₀s x₀D)
        (le_trans (le_max_left (max x₀s x₀D) x₀w)
          (le_trans (le_max_left (max (max x₀s x₀D) x₀w) 2) hx))
    have hxD : x₀D ≤ x :=
      le_trans (le_max_right x₀s x₀D)
        (le_trans (le_max_left (max x₀s x₀D) x₀w)
          (le_trans (le_max_left (max (max x₀s x₀D) x₀w) 2) hx))
    have hxw : x₀w ≤ x :=
      le_trans (le_max_right (max x₀s x₀D) x₀w)
        (le_trans (le_max_left (max (max x₀s x₀D) x₀w) 2) hx)
    obtain ⟨hw2, hwd⟩ := hx₀w x hxw
    have hWdiv : ∀ p : ℕ, p.Prime → p ≤ w x → p ∣ W x := fun p hp hle => hsmall x p hp hle
    have hsep : ∀ i j : Fin k, i ≠ j → H j - H i < w x := by
      intro i j hij
      have h1 : H j - H i ≤ H j := Nat.sub_le _ _
      have h2 : H j ≤ ∑ i, H i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hWx2 : 2 ≤ W x := by
      have h2dvd : 2 ∣ W x := hsmall x 2 Nat.prime_two hw2
      rcases h2dvd with ⟨m, hm⟩
      have : W x ≠ 0 := hW x
      omega
    have hms : 0 < mainScale k W x := mainScale_pos (W := W) (x := x) (hW x) hx2 k
    set gm : ℝ := goodMainSum (k := k) (D := D x) (N := x) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) with hgm
    set ge : ℝ := goodErrSum (k := k) (D := D x) (N := x) (W := W x) (b := b x) (H := H)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) with hge
    set g1 : ℝ := goodMainSum (k := k) (D := D x) (N := 1) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) with hg1
    set MS1 : ℂ := (((1 : ℝ) / (W x : ℝ) : ℝ) : ℂ) *
      (((prefactor W (fun _ => 1) x : ℝ) : ℂ) ^ k *
        ∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ))) with hMS1
    -- the window expansion
    have hwin : windowDivisorProduct F G H (W x) (b x) (D x) x = gm + ge := by
      rw [hgm, hge]
      exact windowLambdaProduct_eq_main_add_error (k := k) (D := D x) (N := x) (W := W x)
        (b := b x) (wd := w x) (R := x) (H := H) (F := F) (G := G) hWdiv hHinj (hbW x) hsep
    -- the main target in terms of `MS1`
    have key : ∀ (r a p : ℝ) (Z : ℂ),
        (r : ℂ) * ((a : ℂ) * ((p : ℂ) ^ k * Z)) = (((r * a * p ^ k : ℝ)) : ℂ) * Z := by
      intro r a p Z
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    have hMT1 : ((x : ℝ) : ℂ) * MS1 = mainTarget F G W x := by
      rw [hMS1]
      rw [key x ((1 : ℝ) / (W x : ℝ)) (prefactor W (fun _ => 1) x)
        (∏ j : Fin k, (∫ t : ℝ in Set.Ioi 0,
          ((deriv (F j) t : ℝ) : ℂ) * ((deriv (G j) t : ℝ) : ℂ)))]
      rw [mainTarget]
      congr 1
      push_cast
      ring
    -- the main term, scaled by the window length
    have hscaled : ‖(((gm : ℝ) : ℂ) - mainTarget F G W x)‖ ≤ εs x * mainScale k W x := by
      rw [hgm]
      have hs := hbd x hxs
      rw [← hMS1, ← hg1] at hs
      have hgx : ((goodMainSum (k := k) (D := D x) (N := x) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) : ℝ) : ℂ) =
          ((x : ℝ) : ℂ) * ((g1 : ℝ) : ℂ) := by
        rw [hg1, goodMainSum_eq_mul_goodMainSum_one]
        push_cast
        ring
      have hstep : ((goodMainSum (k := k) (D := D x) (N := x) (W := W x)
            (fun i d => lamDivWeight (F i) x d) (fun i d => lamDivWeight (G i) x d) : ℝ) : ℂ) -
            mainTarget F G W x = ((x : ℝ) : ℂ) * (((g1 : ℝ) : ℂ) - MS1) := by
        rw [hgx, ← hMT1]
        ring
      rw [hstep, norm_mul, norm_ofReal_complex, abs_of_nonneg (by positivity : (0:ℝ) ≤ (x:ℝ))]
      calc (x : ℝ) * ‖((g1 : ℝ) : ℂ) - MS1‖
            ≤ (x : ℝ) * (εs x * ((1 : ℝ) / (W x : ℝ)) * (prefactor W (fun _ => 1) x) ^ k) :=
              mul_le_mul_of_nonneg_left hs (by positivity)
        _ = εs x * mainScale k W x := by rw [mainScale]; ring
    -- the error term
    have herr := goodErrSum_le_rpow (k := k) (D := D x) (N := x) (W := W x) (b := b x)
      (H := H) (R := x) (F := F) (G := G) (MF := M) (MG := M) (BF := BF) (BG := BG)
      hWx2 hx1 hMnn hMnn hBF0 hBG0 hBF hBG
      (fun i t ht => (hsupp i t ht).1) (fun i t ht => (hsupp i t ht).2)
    have h2M : (∑ i : Fin k, (M i + M i)) = 2 * M0 := by
      rw [hM0, Finset.sum_add_distrib, two_mul]
    have herrC : ‖(((ge : ℝ) : ℂ))‖ ≤ C₀ * (x : ℝ) ^ (2 * M0) := by
      rw [hge, norm_ofReal_complex]
      refine herr.trans (le_of_eq ?_)
      rw [h2M, hC₀]
    -- assemble
    calc ‖(((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x‖
        = ‖(((gm : ℝ) : ℂ) + ((ge : ℝ) : ℂ) - mainTarget F G W x)‖ := by
            rw [hwin]; push_cast; ring_nf
      _ = ‖(((gm : ℝ) : ℂ) - mainTarget F G W x) + ((ge : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ ‖(((gm : ℝ) : ℂ) - mainTarget F G W x)‖ + ‖((ge : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ εs x * mainScale k W x + C₀ * (x : ℝ) ^ (2 * M0) := add_le_add hscaled herrC
      _ = (εs x + C₀ * (x : ℝ) ^ (2 * M0) / mainScale k W x) * mainScale k W x := by
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hms)]

/-- **Polymath8a Theorem 3.6(i)**, unconditional form (case (27) of the paper):
for smooth compactly supported `Fᵢ, Gᵢ` with `2 Σᵢ Mᵢ < 1` on their supports, the
residue-window sum of `∏ᵢ λ_{Fᵢ}(n+hᵢ) λ_{Gᵢ}(n+hᵢ)` is
`(1 + o(1))·x/W·B^{-k}·∏ᵢ ∫₀^∞ Fᵢ′Gᵢ′`.  The vanishing of the `O(x^{2ΣM})` error
against the main term follows from `log W(x) = o(√(log x))` and `2 Σ M < 1`
(the fleet lemma `tendsto_mul_rpow_mul_log_pow_zero`). -/
theorem theorem36_i {k : ℕ} (hk : 1 ≤ k) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (M : Fin k → ℝ) (hMnn : ∀ i, 0 ≤ M i)
    (hsupp : ∀ i t, M i < |t| → F i t = 0 ∧ G i t = 0)
    (hσ1 : 2 * (∑ i, M i) < 1)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ (∑ i, M i) ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      ‖(((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x‖
        ≤ ε x * mainScale k W x :=
  theorem36_i_of_small hk H hHinj F G hcsF hsmF hcsG hsmG M hMnn hsupp hσ1 W hW w hw
    hsmall hlq D hD b hbW
    (Commons.Analysis.Asymptotics.tendsto_mul_rpow_mul_log_pow_zero hσ1 k hlq)

end Commons.NumberTheory.MaynardSieve
