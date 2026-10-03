import Mathlib
import Submission.Work.Peluse.Track.boxNormPow_one_arithIcc_window
import Submission.Work.Peluse.Track.windowSum_block_transfer_complex_step
import Submission.Work.Peluse.PET.tsum_cubeShiftSum_norm_sq_le

/-!
# The `m = 1` case of Peluse's Lemma 4.10

This file proves the `m = 1` instance of the PET-induction target
`Work.Peluse.PET.boxNormPow_control_linear_v2` — Peluse's Lemma 4.10 for the *linear*
configuration `(x, x + c₁ y)` (zero constant term, `c 0 = 0`).

For `m = 1` the hypothesis of the target is a *linear* average: with
`W_M(x) = ∑_{y ∈ [M]} F₁ (x + c₁ y)` one has
`‖Λ‖ = (N M)⁻¹ ‖∑_x F₀(x) W_M(x)‖` (no product of more than one factor).  Hence
Cauchy–Schwarz in `x` *directly* controls `∑_{x ∈ [-N,N]} ‖W_M(x)‖²` by `γ N² M² / (2N+1)`,
with no "modulus" loss: the box norm at level one is exactly the `ℓ²` mass of the window sums, for
the *complex* function `F 1`.

The scale reduction `M → L = ⌊γ' M⌋` is the block decomposition of the window sums
(`Work.Peluse.Track.windowSum_block_transfer_complex_step`), whose error term `2 L² (2N+1)` is
absorbed by the main term because `L ≤ γ M / 2000` and `γ ≤ 1`.  The two elementary facts
`L ≤ γ M/2000` and `⌊M/L⌋ L ≤ M` then yield

`boxNormPow 1 (c₁[L]) ([-N,N]) (F 1) ≥ γ N²/(16 (2N+1)²) ≥ γ/144 ≥ (γ/1000)³`.

The degenerate case `c 1 = 0` is even easier: then `c₁[L] = {0}` and the box norm is the
normalised `ℓ²` mass of `F 1`, bounded below by `γ/9`.

## Reference

S. Peluse, *Bounds for sets with no polynomial progressions*, Forum of Mathematics, Pi **8** (2020),
e16, Lemma 4.10 (and Lemma 4.2); B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for
non-conventional bilinear polynomial averages*, Ann. of Math. **195** (2022), §5.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.PET

noncomputable section

/-! ## Elementary auxiliary lemmas -/

/-- Powers of a number in `(0,1]` are decreasing: `(γ/1000)^K ≤ γ/1000` for `K ≥ 1`. -/
private lemma pow_gamma_div_le {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) {K : ℕ} (hK : 1 ≤ K) :
    (γ / 1000) ^ K ≤ γ / 1000 := by
  have h0 : (0 : ℝ) ≤ γ / 1000 := by positivity
  have h1 : γ / 1000 ≤ 1 := by linarith
  calc (γ / 1000) ^ K ≤ (γ / 1000) ^ 1 := pow_le_pow_of_le_one h0 h1 hK
    _ = γ / 1000 := pow_one _

/-- The single factor of the product over `Fin 1`: for `i : Fin 1` the index `i.succ` is `1`. -/
private lemma prod_univ_one_eq (F : Fin 2 → ℤ → ℂ) (c : Fin 2 → ℤ) (x y : ℤ) :
    (∏ i : Fin 1, F i.succ (x + c i.succ * y)) = F 1 (x + c 1 * y) := by
  rw [Fin.prod_univ_one]
  simp

/-- `symIcc N = [-N,N]` has `2N+1` elements. -/
private lemma symIcc_card_eq (N : ℕ) : (Work.Peluse.symIcc N).card = 2 * N + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The degenerate direction set: `c[H] = {0}` when `c = 0` and `H ≥ 1`. -/
private lemma arithIcc_zero_eq {L : ℕ} (hL : 1 ≤ L) :
    Work.Peluse.arithIcc (0 : ℤ) L = ({0} : Finset ℤ) := by
  ext x
  simp only [Work.Peluse.arithIcc, Finset.mem_image, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨y, _, rfl⟩
    ring
  · intro hx
    exact ⟨1, ⟨le_refl 1, hL⟩, by rw [hx]; ring⟩

/-- **The first box-norm power for a degenerate (`{0}`) direction set.**  For `f` supported in
`[-N,N]`, the level-one box-norm power of `f` with direction set `{0}` is the normalised `ℓ²` mass
of `f`:
`‖f‖²_{□¹_{ {0} }([-N,N])} = (2N+1)⁻¹ ∑_{x ∈ [-N,N]} ‖f x‖²`. -/
private lemma boxNormPow_one_singleton {N : ℕ} (f : ℤ → ℂ) (hsup : Work.Peluse.SupportIn f N) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => ({0} : Finset ℤ)) (Work.Peluse.symIcc N) f
      = ((2 * (N : ℝ) + 1))⁻¹ * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ 2 := by
  rw [Work.Peluse.Peel.boxNormPow_one_tsum (N := N) ({0} : Finset ℤ) (Work.Peluse.symIcc N) hsup]
  have hcard : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [symIcc_card_eq]; push_cast; ring
  have htsum : (∑' x : ℤ, ‖∑ a ∈ ({0} : Finset ℤ), f (x + a)‖ ^ 2)
      = ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ 2 := by
    have hstep : ∀ x : ℤ, ‖∑ a ∈ ({0} : Finset ℤ), f (x + a)‖ ^ 2 = ‖f x‖ ^ 2 := by
      intro x
      rw [Finset.sum_singleton, add_zero]
    rw [tsum_congr hstep]
    rw [tsum_eq_sum (s := Work.Peluse.symIcc N)]
    intro x hx
    have hx' : ¬ (x.natAbs ≤ N) := fun h => hx (Work.Peluse.Track.mem_symIcc_iff_natAbs.mpr h)
    have hxN : N < x.natAbs := by omega
    rw [hsup x hxN, norm_zero]
    norm_num
  rw [htsum]
  simp only [Finset.card_singleton, Nat.cast_one, inv_one, one_pow, mul_one]
  rw [hcard]

/-! ## The Cauchy–Schwarz consequence of the hypothesis -/

/-- **Cauchy–Schwarz in `x`.**  If the normalised linear average along `(x, x + c₁ y)` is at least
`γ` in modulus and `F 0`, `F 1` are `1`-bounded and supported in `[-N,N]`, then the `ℓ²` mass of the
window sums `W(x) = ∑_{y ∈ [M]} F 1 (x + c₁ y)` over the *support window* `[-N,N]` dominates
`γ N² M² / (2N+1)`. -/
private lemma cs_le_windowSum_sq {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (c : Fin 2 → ℤ) (F : Fin 2 → ℤ → ℂ) {γ : ℝ} (hγ : 0 < γ)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hLam : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, F 1 (x + c 1 * (y : ℤ))‖ ^ 2) :
    γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ (2 * (N : ℝ) + 1) *
      ∑ x ∈ Work.Peluse.symIcc N,
        ‖∑ y ∈ Finset.Icc 1 M, F 1 (x + c 1 * (y : ℤ))‖ ^ 2 := by
  classical
  set S : ℤ → ℂ := fun x => ∑ y ∈ Finset.Icc 1 M, F 1 (x + c 1 * (y : ℤ)) with hS
  set T : ℂ := ∑' x : ℤ, F 0 x * S x with hT
  have hTsum : T = ∑ x ∈ Work.Peluse.symIcc N, F 0 x * S x := by
    rw [hT, tsum_eq_sum (s := Work.Peluse.symIcc N)]
    intro x hx
    have hx' : ¬ (x.natAbs ≤ N) := fun h => hx (Work.Peluse.Track.mem_symIcc_iff_natAbs.mpr h)
    have hxN : N < x.natAbs := by omega
    rw [hFs 0 x hxN, zero_mul]
  have hCS : ‖T‖ ^ 2 ≤ (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖S x‖ ^ 2 := by
    have hcard : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      rw [symIcc_card_eq]; push_cast; ring
    have h1 : ‖∑ x ∈ Work.Peluse.symIcc N, F 0 x * S x‖ ^ 2
        ≤ (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖F 0 x * S x‖ ^ 2 := by
      have h2 := Work.Peluse.PET.norm_sum_sq_le_card_mul_sum_norm_sq (Work.Peluse.symIcc N)
        (fun x => F 0 x * S x)
      rwa [hcard] at h2
    rw [hTsum]
    refine le_trans h1 ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro x _
    rw [norm_mul, mul_pow]
    have hx1 : ‖F 0 x‖ ^ 2 ≤ 1 := by
      have h := hF 0 x
      nlinarith [norm_nonneg (F 0 x)]
    calc ‖F 0 x‖ ^ 2 * ‖S x‖ ^ 2 = ‖S x‖ ^ 2 * ‖F 0 x‖ ^ 2 := by ring
      _ ≤ ‖S x‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ = ‖S x‖ ^ 2 := by ring
  have hnorm : ‖((N : ℂ) * (M : ℂ))⁻¹ * T‖ ^ 2
      = (((N : ℝ) * (M : ℝ))⁻¹) ^ 2 * ‖T‖ ^ 2 := by
    rw [norm_mul, mul_pow, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hkey : γ ≤ (((N : ℝ) * (M : ℝ))⁻¹) ^ 2 * ‖T‖ ^ 2 := by
    rw [← hnorm]; exact hLam
  have ha2pos : (0 : ℝ) < ((N : ℝ) * (M : ℝ)) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hkey (le_of_lt ha2pos)
  have hsimp : (((N : ℝ) * (M : ℝ))⁻¹) ^ 2 * ‖T‖ ^ 2 * ((N : ℝ) * (M : ℝ)) ^ 2
      = ‖T‖ ^ 2 := by
    have hne : (N : ℝ) * (M : ℝ) ≠ 0 := by positivity
    rw [mul_assoc, mul_comm (‖T‖ ^ 2) (((N : ℝ) * (M : ℝ)) ^ 2), ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hne, one_pow, one_mul]
  rw [hsimp] at hmul
  calc γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
      = γ * ((N : ℝ) * (M : ℝ)) ^ 2 := by ring
    _ ≤ ‖T‖ ^ 2 := hmul
    _ ≤ (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖S x‖ ^ 2 := hCS
    _ = (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N,
          ‖∑ y ∈ Finset.Icc 1 M, F 1 (x + c 1 * (y : ℤ))‖ ^ 2 := by
        simp only [hS]

/-! ## The two arithmetic lemmas -/

/-- **The arithmetic of the non-degenerate case.**  From the two ingredients

* `γ N² M² ≤ (2N+1) · AM` (the Cauchy–Schwarz bound at the scale `M`),
* `AM ≤ 2 ⌊M/L⌋² · AL + 2 L² (2N+1)` (the block transfer `M → L`, `L` a multiple scale with
  `L ≤ γ M/2000`),

one gets `(γ/1000)³ ≤ ((2N+1) L²)⁻¹ AL`:  the transfer error is absorbed by the main term because
`4 L² (2N+1)² ≤ γ N² M²` (from `L ≤ γM/2000`, `γ ≤ 1` and `2N+1 ≤ 3N`), and `⌊M/L⌋ L ≤ M`
converts the `⌊M/L⌋²` loss into the `L²` that the box norm normalises away. -/
private lemma arith_one_aux {N M L : ℕ} {γ AM AL : ℝ} (hN : 0 < N) (hM : 0 < M) (hL1 : 1 ≤ L)
    (hLM : L ≤ M) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hL2000 : (L : ℝ) ≤ γ * (M : ℝ) / 2000)
    (hAM : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ (2 * (N : ℝ) + 1) * AM)
    (hT : AM ≤ 2 * ((M / L : ℕ) : ℝ) ^ 2 * AL + 2 * (L : ℝ) ^ 2 * (2 * (N : ℝ) + 1)) :
    (γ / 1000) ^ 3 ≤ ((2 * (N : ℝ) + 1) * (L : ℝ) ^ 2)⁻¹ * AL := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hb : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  have hbsq : (2 * (N : ℝ) + 1) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by nlinarith
  have hLsq : (L : ℝ) ^ 2 ≤ γ ^ 2 * (M : ℝ) ^ 2 / 4000000 := by
    have h1 : (L : ℝ) ^ 2 ≤ (γ * (M : ℝ) / 2000) ^ 2 := pow_le_pow_left₀ hLpos.le hL2000 2
    have h2 : (γ * (M : ℝ) / 2000) ^ 2 = γ ^ 2 * (M : ℝ) ^ 2 / 4000000 := by ring
    linarith [h1, h2]
  have hgb : γ * (2 * (N : ℝ) + 1) ^ 2 ≤ 10 ^ 6 * (N : ℝ) ^ 2 := by
    have h2 : γ * (2 * (N : ℝ) + 1) ^ 2 ≤ 1 * (9 * (N : ℝ) ^ 2) :=
      mul_le_mul hγ1 hbsq (by positivity) (by norm_num)
    have h3 : (9 : ℝ) * (N : ℝ) ^ 2 ≤ 10 ^ 6 * (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (N : ℝ)]
    linarith [h2, h3]
  have hkey1 : 4 * (L : ℝ) ^ 2 * (2 * (N : ℝ) + 1) ^ 2 ≤ γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 := by
    have h1 : 4 * (L : ℝ) ^ 2 ≤ γ ^ 2 * (M : ℝ) ^ 2 / 10 ^ 6 := by nlinarith [hLsq]
    have h2 : 4 * (L : ℝ) ^ 2 * (2 * (N : ℝ) + 1) ^ 2
        ≤ (γ ^ 2 * (M : ℝ) ^ 2 / 10 ^ 6) * (2 * (N : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have h3 : (γ * (M : ℝ) ^ 2 / 10 ^ 6) * (γ * (2 * (N : ℝ) + 1) ^ 2)
        ≤ (γ * (M : ℝ) ^ 2 / 10 ^ 6) * (10 ^ 6 * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hgb (by positivity)
    nlinarith [h2, h3]
  have hK : ((M / L : ℕ) : ℝ) * (L : ℝ) ≤ (M : ℝ) := by
    have h1 : ((M / L : ℕ) : ℝ) * (L : ℝ) = ((M / L * L : ℕ) : ℝ) := by push_cast; ring
    rw [h1]
    exact_mod_cast Nat.div_mul_le_self M L
  have hK1 : (1 : ℝ) ≤ ((M / L : ℕ) : ℝ) := by
    have h1 : 1 ≤ M / L := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < L)]
      simpa using hLM
    exact_mod_cast h1
  have hkey2 : ((M / L : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hK 2
    nlinarith [h]
  have hstep1 : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
      ≤ 2 * ((M / L : ℕ) : ℝ) ^ 2 * AL * (2 * (N : ℝ) + 1)
        + 2 * (L : ℝ) ^ 2 * (2 * (N : ℝ) + 1) ^ 2 := by
    have hbT := mul_le_mul_of_nonneg_left hT hb.le
    nlinarith [hAM, hbT]
  have hstep2 : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 / 2
      ≤ 2 * ((M / L : ℕ) : ℝ) ^ 2 * AL * (2 * (N : ℝ) + 1) := by
    nlinarith [hstep1, hkey1]
  have hstep3 : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 * (L : ℝ) ^ 2 / 2
      ≤ 2 * ((M / L : ℕ) : ℝ) ^ 2 * AL * (2 * (N : ℝ) + 1) * (L : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hstep2 (sq_nonneg (L : ℝ))
    nlinarith [h]
  have hKpos : (0 : ℝ) < ((M / L : ℕ) : ℝ) := by linarith
  have hKLpos : (0 : ℝ) < ((M / L : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2 :=
    mul_pos (pow_pos hKpos 2) (pow_pos hLpos 2)
  have hstep4 : (γ * (N : ℝ) ^ 2 * (L : ℝ) ^ 2 / 2) * (((M / L : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2)
      ≤ (2 * (2 * (N : ℝ) + 1) * AL) * (((M / L : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2) := by
    have hg : (0 : ℝ) ≤ γ * (N : ℝ) ^ 2 * (L : ℝ) ^ 2 / 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hkey2 hg
    nlinarith [h, hstep3]
  have hmain : γ * (N : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ AL * (4 * (2 * (N : ℝ) + 1)) := by
    have h := le_of_mul_le_mul_right hstep4 hKLpos
    nlinarith [h]
  have hratio : γ * (2 * (N : ℝ) + 1) * (L : ℝ) ^ 2 / 36
      ≤ γ * (N : ℝ) ^ 2 * (L : ℝ) ^ 2 / (4 * (2 * (N : ℝ) + 1)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have hmul : γ * (L : ℝ) ^ 2 * (2 * (N : ℝ) + 1) ^ 2
        ≤ γ * (L : ℝ) ^ 2 * (9 * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hbsq (by positivity)
    nlinarith [hmul]
  have hAL : γ / 36 ≤ ((2 * (N : ℝ) + 1) * (L : ℝ) ^ 2)⁻¹ * AL := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    have h2 : γ * (N : ℝ) ^ 2 * (L : ℝ) ^ 2 / (4 * (2 * (N : ℝ) + 1)) ≤ AL :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (2 * (N : ℝ) + 1))).mpr hmain
    have h3 : γ / 36 * ((2 * (N : ℝ) + 1) * (L : ℝ) ^ 2)
        = γ * (2 * (N : ℝ) + 1) * (L : ℝ) ^ 2 / 36 := by ring
    rw [h3]
    linarith [hratio, h2]
  have hpow : (γ / 1000) ^ 3 ≤ γ / 1000 := by
    simpa using pow_le_pow_of_le_one (show (0 : ℝ) ≤ γ / 1000 by positivity)
      (show γ / 1000 ≤ 1 by linarith) (show 1 ≤ 3 by norm_num)
  have hcmp : γ / 1000 ≤ γ / 36 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith [hγ.le]
  linarith [hpow, hcmp, hAL]

/-- **The arithmetic of the degenerate case.**  Here the hypothesis controls the normalised `ℓ²`
mass of `F 1` directly: `γ N² ≤ (2N+1) AL` gives `(γ/1000)³ ≤ (2N+1)⁻¹ AL` because
`(2N+1)² ≤ 9N²`. -/
private lemma arith_zero {N : ℕ} {γ AL : ℝ} (hN : 0 < N) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hAM : γ * (N : ℝ) ^ 2 ≤ (2 * (N : ℝ) + 1) * AL) :
    (γ / 1000) ^ 3 ≤ ((2 * (N : ℝ) + 1))⁻¹ * AL := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hb : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  have hbsq : (2 * (N : ℝ) + 1) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by nlinarith
  have hAL : γ / 9 ≤ ((2 * (N : ℝ) + 1))⁻¹ * AL := by
    rw [inv_mul_eq_div, le_div_iff₀ hb]
    have h2 : γ * (N : ℝ) ^ 2 / (2 * (N : ℝ) + 1) ≤ AL :=
      (div_le_iff₀ hb).mpr (by linarith [hAM])
    have hratio : γ * (2 * (N : ℝ) + 1) / 9 ≤ γ * (N : ℝ) ^ 2 / (2 * (N : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by norm_num) hb]
      nlinarith [hbsq, hγ.le]
    have h3 : γ / 9 * (2 * (N : ℝ) + 1) = γ * (2 * (N : ℝ) + 1) / 9 := by ring
    rw [h3]
    linarith [hratio, h2]
  have hpow : (γ / 1000) ^ 3 ≤ γ / 1000 := by
    simpa using pow_le_pow_of_le_one (show (0 : ℝ) ≤ γ / 1000 by positivity)
      (show γ / 1000 ≤ 1 by linarith) (show 1 ≤ 3 by norm_num)
  have hcmp : γ / 1000 ≤ γ / 9 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    linarith [hγ.le]
  linarith [hpow, hcmp, hAL]

/-! ## The target -/

theorem boxNormPow_control_linear_v2_one :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (c : Fin 2 → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin 2 → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin 2, |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ / (1000 * (1 + 1)) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin 1, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / 1000) ^ K ≤ Work.Peluse.boxNormPow 1
        (fun i : Fin 1 => Work.Peluse.arithIcc (c 1 - c i.castSucc) (⌊γ' * (M : ℝ)⌋).toNat)
        (Work.Peluse.symIcc N) (F 1) := by
  refine ⟨3, by norm_num, ?_⟩
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hγ'le hLge hLam
  -- normalise the scale and the hypothesis
  set L : ℕ := ⌊γ' * (M : ℝ)⌋.toNat with hLdef
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hL1 : 1 ≤ L := by rw [hLdef]; exact hLge
  have hLam' : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
      ∑ y ∈ Finset.Icc 1 M, F 1 (x + c 1 * (y : ℤ))‖ ^ 2 := by
    simpa only [prod_univ_one_eq] using hLam
  have hγ'2000 : γ' ≤ γ / 2000 := by
    have h : (1000 : ℝ) * (1 + 1) = 2000 := by norm_num
    rw [h] at hγ'le
    exact hγ'le
  have hγ'1 : γ' ≤ 1 := by
    have h2 : γ / 2000 ≤ 1 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2000)]
      linarith
    linarith
  have hLle : (L : ℝ) ≤ γ' * (M : ℝ) := by
    rw [hLdef, Int.floor_toNat]
    exact Nat.floor_le (le_of_lt (mul_pos hγ' hMpos))
  have hL2000 : (L : ℝ) ≤ γ * (M : ℝ) / 2000 := by
    calc (L : ℝ) ≤ γ' * (M : ℝ) := hLle
      _ ≤ (γ / 2000) * (M : ℝ) := mul_le_mul_of_nonneg_right hγ'2000 hMpos.le
      _ = γ * (M : ℝ) / 2000 := by ring
  have hLMe : (L : ℝ) ≤ (M : ℝ) := by
    calc (L : ℝ) ≤ γ' * (M : ℝ) := hLle
      _ ≤ 1 * (M : ℝ) := mul_le_mul_of_nonneg_right hγ'1 hMpos.le
      _ = (M : ℝ) := one_mul _
  have hLM : L ≤ M := by exact_mod_cast hLMe
  have hcard : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [symIcc_card_eq]; push_cast; ring
  by_cases hc1 : c 1 = 0
  · -- ## degenerate case `c 1 = 0`
    have hAM0 := cs_le_windowSum_sq hN hM c F hγ hF hFs hLam'
    rw [hc1] at hAM0
    simp only [zero_mul, add_zero] at hAM0
    have hsum : ∀ x : ℤ, ‖∑ y ∈ Finset.Icc 1 M, F 1 x‖ ^ 2 = (M : ℝ) ^ 2 * ‖F 1 x‖ ^ 2 := by
      intro x
      have hcardM : (Finset.Icc 1 M).card = M := by
        rw [Nat.card_Icc]; omega
      have h1 : (∑ y ∈ Finset.Icc 1 M, F 1 x) = (M : ℂ) * F 1 x := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardM]
      rw [h1, norm_mul, Complex.norm_natCast]
      ring
    have hsum_eq : (∑ x ∈ Work.Peluse.symIcc N, ‖∑ y ∈ Finset.Icc 1 M, F 1 x‖ ^ 2)
        = (M : ℝ) ^ 2 * ∑ x ∈ Work.Peluse.symIcc N, ‖F 1 x‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => hsum x)
    rw [hsum_eq] at hAM0
    have hAM2 : γ * (N : ℝ) ^ 2
        ≤ (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖F 1 x‖ ^ 2 := by
      have h2 : (γ * (N : ℝ) ^ 2) * (M : ℝ) ^ 2
          ≤ ((2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖F 1 x‖ ^ 2)
            * (M : ℝ) ^ 2 := by nlinarith [hAM0]
      exact le_of_mul_le_mul_right h2 (by positivity)
    have hbox := boxNormPow_one_singleton (N := N) (F 1) (hFs 1)
    have hdir : (fun i : Fin 1 => Work.Peluse.arithIcc (c 1 - c i.castSucc) L)
        = fun _ : Fin 1 => ({0} : Finset ℤ) := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have hcs : (0 : Fin 1).castSucc = (0 : Fin 2) := Fin.ext rfl
      rw [hcs, hc0, hc1, sub_zero, arithIcc_zero_eq hL1]
    rw [hdir, hbox]
    exact arith_zero hN hγ hγ1 hAM2
  · -- ## non-degenerate case `c 1 ≠ 0`
    have hAM := cs_le_windowSum_sq hN hM c F hγ hF hFs hLam'
    set AM : ℝ := ∑ x ∈ Work.Peluse.symIcc N,
      ‖∑ y ∈ Finset.Icc 1 M, F 1 (x + c 1 * (y : ℤ))‖ ^ 2 with hAMdef
    set AL : ℝ := ∑ x ∈ Work.Peluse.symIcc (N + L * (c 1).natAbs),
      ‖∑ y ∈ Finset.Icc 1 L, F 1 (x + c 1 * (y : ℤ))‖ ^ 2 with hALdef
    have hAM' : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ (2 * (N : ℝ) + 1) * AM := by
      rw [hAMdef]; exact hAM
    have hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → F 1 x = 0 := by
      intro x hx
      have hx' : ¬ (x.natAbs ≤ N) := fun h => hx (Work.Peluse.Track.mem_symIcc_iff_natAbs.mpr h)
      exact hFs 1 x (by omega)
    have hT0 := Work.Peluse.Track.windowSum_block_transfer_complex_step
      (N := N) (M := M) (L := L) hL1 hLM (c 1) (F 1) hsup (fun x => hF 1 x)
    have hT : AM ≤ 2 * ((M / L : ℕ) : ℝ) ^ 2 * AL + 2 * (L : ℝ) ^ 2 * (2 * (N : ℝ) + 1) := by
      rw [hAMdef, hALdef]
      rw [hcard] at hT0
      exact hT0
    have hbox0 := Work.Peluse.Track.boxNormPow_one_arithIcc_window (d := c 1) hc1 (H := L)
      hL1 (N := N) (F 1) (hFs 1)
    have hdir : (fun i : Fin 1 => Work.Peluse.arithIcc (c 1 - c i.castSucc) L)
        = fun _ : Fin 1 => Work.Peluse.arithIcc (c 1) L := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have hcs : (0 : Fin 1).castSucc = (0 : Fin 2) := Fin.ext rfl
      rw [hcs, hc0, sub_zero]
    have hgoal : Work.Peluse.boxNormPow 1
          (fun i : Fin 1 => Work.Peluse.arithIcc (c 1 - c i.castSucc) L)
          (Work.Peluse.symIcc N) (F 1) = ((2 * (N : ℝ) + 1) * (L : ℝ) ^ 2)⁻¹ * AL := by
      rw [hdir, hbox0, hcard, mul_inv, inv_pow]
    rw [hgoal]
    exact arith_one_aux hN hM hL1 hLM hγ hγ1 hL2000 hAM' hT

end

end Work.Peluse.PET
