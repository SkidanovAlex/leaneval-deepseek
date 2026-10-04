import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.CSq_comp_vecarg_le
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.flat.Sobolev
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.flat.det_cutoff
import Submission.Work.Diff.STE.flat.cutoff_mul_contDiff
import Submission.Work.Diff.STE.flat.sobolev_uniform
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.CSq_symInvC_le
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.fill.symInv_garding_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `L^{2p}` bounds for the derivatives of the symmetrised inverse metric

The target `Work.Diff.STE.fill.symInv_deriv_Lp_bound` is the coefficient-side input of the
Leibniz/Hölder step of the sharp level-`k` Gårding estimate of the flat DeTurck system
(`Submission/Work/Diff/STE/flat/pairing_sharp.lean`): under the level-`k` energy bound
`ENormSqFull k (seriesFunM c) ≤ B²` and uniform ellipticity of `reMat (seriesFunM c ·)` with
constant `lam > 0`, every partial derivative `∂^q (symInvC c a b)` of order `j = q.length` is
bounded in `L^{2p}` by a constant depending only on `n`, `k`, `lam`, `B` — *uniformly* in the
truncation order `N`, in the coefficient family `c`, in the index pair `(a,b)`, in the list `q`
and in the exponent `p ≥ 1`, as long as the "price" `j + n/2 - n/(2p) + 1` of the derivative does
not exceed the level `k` at which the energy is controlled.

## Route

1. `symInv_garding_bounds` bounds the level-`k` Fourier mass of `symInvC c a b`, and gives its
   smoothness and `1`-periodicity.
2. `seriesFun_fourierCoeff` writes `symInvC c a b = seriesFun γ` with `γ` its own coefficient
   family; `pdList_seriesFun` then computes `∂^q (seriesFun γ) = seriesFun (dmulV q γ)`, with
   `dmulV q γ` the family `m ↦ ∏_{i ∈ q} (2πi m_i) · γ m`.  The weighted `ℓ¹` moments of `γ`
   required by `pdList_seriesFun` come from the weighted `ℓ²` moments
   (`invJet_summable_moment_of_wt_sq`), which are supplied at every level by the smoothness of
   `symInvC c a b` (`summable_weighted_fourierCoeff_of_contDiff`).
3. The sharp Sobolev embedding *with a constant uniform in the exponent*
   (`Work.Diff.STE.flat.rnorm_seriesFun_uniform`) bounds `rnorm (2p) (seriesFun (dmulV q γ))` by
   `C · (Σ_m ⟨m⟩^{2j₀} ‖dmulV q γ m‖²)^{1/2}` for any real level `j₀ ≥ n(1/2 - 1/(2p)) + 1/2`.
4. The weight trade `(wt m)^{j₀} ‖dmulV q γ m‖² ≤ (2π)^{2|q|} (wt m)^{|q| + j₀} ‖γ m‖²` and the
   choice `j₀ := n(1/2 - 1/(2p)) + 1/2`, whose "price" `|q| + j₀ = |q| + n/2 - n/(2p) + 1/2 ≤
   k - 1/2` is below the energy level `k`, close the argument: all remaining constants are
   `√(CSq k γ) ≤ √Cinv` and `(2π)^{|q|} ≤ (2π)^k` (and `|q| ≤ k` follows from the price bound).
-/

namespace Work.Diff.STE.fill

open Work.Diff.STE

theorem symInv_deriv_Lp_bound {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        ∀ (a b : Fin n) (q : List (Fin n)) (p : ℝ), 1 ≤ p →
          (q.length : ℝ) + (n : ℝ) / 2 - (n : ℝ) / (2 * p) + 1 ≤ (k : ℝ) →
          (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.flat.symInvC c a b y) x‖ ^ (2 * p))
            ^ (1 / (2 * p)) ≤ C := by
  classical
  -- the three uniform constants: the Sobolev constant, the level-`k` mass of `symInvC`, and the
  -- Gårding bounds (smoothness/periodicity of `symInvC` in particular)
  obtain ⟨Csob, hCsob0, hCsob⟩ := Work.Diff.STE.flat.rnorm_seriesFun_uniform (ι := Fin n)
  obtain ⟨Cinv, hCinv0, hCinv⟩ :=
    Work.Diff.STE.flat.CSq_symInvC_le hn k (sob_le_of_card hk) lam hlam B hB
  obtain ⟨_lam', _hlam', _Kg, _hKg, hgb⟩ := symInv_garding_bounds hn k hk lam hlam B hB
  refine ⟨Csob * (2 * Real.pi) ^ k * Real.sqrt Cinv, by positivity, ?_⟩
  intro N c hc hE hell a b q p hp hkq
  obtain ⟨_hsmR, hsmC, _hperR, hperC, _hpdr, _hgard⟩ := hgb N c hc hE hell
  -- the coefficient family of the symmetrised inverse metric
  set γ : (Fin n → ℤ) → ℂ :=
    Work.Diff.STE.fourierCoeff (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) with hγ
  have hsmF : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) :=
    hsmC a b
  have hperF : Work.Diff.STE.Periodic1 (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y) :=
    hperC a b
  have hFeq : Work.Diff.STE.seriesFun γ
      = fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y :=
    funext (Work.Diff.STE.flat.seriesFun_fourierCoeff _ hsmF hperF)
  -- weighted `ℓ²` and `ℓ¹` moment summability of `γ`
  have hmom2 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ K * ‖γ m‖ ^ 2) :=
    fun K => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ hsmF hperF K
  have hmom1 : ∀ K : ℕ, Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ K * ‖γ m‖) :=
    fun K => Work.Diff.STE.flat.invJet_summable_moment_of_wt_sq γ hmom2 K
  -- the derivative identity
  have hpd : ∀ x : Fin n → ℝ,
      Work.Diff.STE.pdList q (Work.Diff.STE.seriesFun γ) x
        = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q γ) x :=
    Work.Diff.STE.pdList_seriesFun q γ hmom1
  have hpdall : Work.Diff.STE.pdList q (fun y : Fin n → ℝ => Work.Diff.STE.flat.symInvC c a b y)
      = Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q γ) := by
    rw [← hFeq]
    exact funext hpd
  -- the level at which the Sobolev embedding is applied
  set j₀ : ℝ := (n : ℝ) * (1 / 2 - 1 / (2 * p)) + 1 / 2 with hj₀
  have hj₀card : (Fintype.card (Fin n) : ℝ) * (1 / 2 - 1 / (2 * p)) + 1 / 2 ≤ j₀ := by
    rw [hj₀, Fintype.card_fin]
  have hj₀j : j₀ + (q.length : ℝ) ≤ (k : ℝ) := by
    have h1 : j₀ = (n : ℝ) / 2 - (n : ℝ) / (2 * p) + 1 / 2 := by rw [hj₀]; ring
    rw [h1]; linarith
  -- the pointwise weight trade
  have hkey : ∀ m : Fin n → ℤ,
      (Work.Diff.STE.wt m) ^ j₀ * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2
        ≤ (2 * Real.pi) ^ (2 * q.length) * ((Work.Diff.STE.wt m) ^ k * ‖γ m‖ ^ 2) := by
    intro m
    have hwpos : 0 < Work.Diff.STE.wt m := Work.Diff.STE.wt_pos m
    have hw1 : 1 ≤ Work.Diff.STE.wt m := Work.Diff.STE.wt_one_le m
    have hstep : (Work.Diff.STE.wt m) ^ j₀ * (Work.Diff.STE.wt m) ^ q.length
        = (Work.Diff.STE.wt m) ^ (j₀ + (q.length : ℝ)) := by
      rw [← Real.rpow_natCast (Work.Diff.STE.wt m) q.length, ← Real.rpow_add hwpos]
    have hA : ((2 * Real.pi) ^ 2 * Work.Diff.STE.wt m) ^ q.length
        = (2 * Real.pi) ^ (2 * q.length) * (Work.Diff.STE.wt m) ^ q.length := by
      rw [mul_pow, ← pow_mul]
    calc (Work.Diff.STE.wt m) ^ j₀ * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2
        ≤ (Work.Diff.STE.wt m) ^ j₀
            * (((2 * Real.pi) ^ 2 * Work.Diff.STE.wt m) ^ q.length * ‖γ m‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Work.Diff.STE.norm_sq_dmulV_le q γ m)
            (Real.rpow_nonneg hwpos.le j₀)
      _ = (Work.Diff.STE.wt m) ^ j₀
            * ((2 * Real.pi) ^ (2 * q.length) * (Work.Diff.STE.wt m) ^ q.length
              * ‖γ m‖ ^ 2) := by
          rw [hA]
      _ = (2 * Real.pi) ^ (2 * q.length)
            * ((Work.Diff.STE.wt m) ^ j₀ * (Work.Diff.STE.wt m) ^ q.length * ‖γ m‖ ^ 2) := by
          ring
      _ = (2 * Real.pi) ^ (2 * q.length)
            * ((Work.Diff.STE.wt m) ^ (j₀ + (q.length : ℝ)) * ‖γ m‖ ^ 2) := by
          rw [hstep]
      _ ≤ (2 * Real.pi) ^ (2 * q.length)
            * ((Work.Diff.STE.wt m) ^ (k : ℝ) * ‖γ m‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
            (pow_nonneg (by positivity) _)
          exact Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
      _ = (2 * Real.pi) ^ (2 * q.length) * ((Work.Diff.STE.wt m) ^ k * ‖γ m‖ ^ 2) := by
          rw [Real.rpow_natCast]
  -- the weighted mass of `dmulV q γ` at level `j₀`
  have hSsumm : Summable (fun m : Fin n → ℤ =>
      (Work.Diff.STE.wt m) ^ j₀ * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (Real.rpow_nonneg (Work.Diff.STE.wt_pos m).le j₀) (sq_nonneg _))
      hkey ((hmom2 k).mul_left ((2 * Real.pi) ^ (2 * q.length)))
  have hSnn : 0 ≤ ∑' m : Fin n → ℤ,
      (Work.Diff.STE.wt m) ^ j₀ * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2 :=
    tsum_nonneg fun m =>
      mul_nonneg (Real.rpow_nonneg (Work.Diff.STE.wt_pos m).le j₀) (sq_nonneg _)
  have hSle : (∑' m : Fin n → ℤ,
        (Work.Diff.STE.wt m) ^ j₀ * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2)
      ≤ (2 * Real.pi) ^ (2 * q.length) * Work.Diff.STE.CSq k γ := by
    have hmaj : Summable (fun m : Fin n → ℤ => (2 * Real.pi) ^ (2 * q.length)
        * ((Work.Diff.STE.wt m) ^ k * ‖γ m‖ ^ 2)) :=
      (hmom2 k).mul_left _
    have h := Summable.tsum_le_tsum hkey hSsumm hmaj
    rw [tsum_mul_left] at h
    simpa only [Work.Diff.STE.CSq] using h
  have hCinv' : Work.Diff.STE.CSq k γ ≤ Cinv := hCinv N c hc hE hell a b
  -- the Sobolev bound
  have hsob := hCsob p hp j₀ hj₀card (Work.Diff.STE.dmulV q γ) hSsumm
  have hsq : ((2 * Real.pi) ^ (2 * q.length) : ℝ) ^ (1 / 2 : ℝ) = (2 * Real.pi) ^ q.length := by
    rw [← Real.sqrt_eq_rpow,
      show (2 * Real.pi) ^ (2 * q.length) = ((2 * Real.pi) ^ q.length) ^ 2 from by
        rw [← pow_mul, Nat.mul_comm],
      Real.sqrt_sq (pow_nonneg (by positivity) _)]
  have hsqrt : (∑' m : Fin n → ℤ,
        (Work.Diff.STE.wt m) ^ j₀ * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (2 * Real.pi) ^ q.length * Real.sqrt Cinv := by
    calc (∑' m : Fin n → ℤ,
          (Work.Diff.STE.wt m) ^ j₀ * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2) ^ (1 / 2 : ℝ)
        ≤ ((2 * Real.pi) ^ (2 * q.length) * Work.Diff.STE.CSq k γ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hSnn hSle (by norm_num)
      _ = (2 * Real.pi) ^ q.length * (Work.Diff.STE.CSq k γ) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (pow_nonneg (by positivity) _) (CSq_nonneg k γ), hsq]
      _ ≤ (2 * Real.pi) ^ q.length * Real.sqrt Cinv := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) q.length)
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_le_sqrt hCinv'
  -- exponent bookkeeping
  have hlen : q.length ≤ k := by
    have hpn : (n : ℝ) / (2 * p) ≤ (n : ℝ) / 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    have h1 : (q.length : ℝ) + 1 ≤ (k : ℝ) := by linarith
    have h2 : (q.length : ℝ) < (k : ℝ) := by linarith
    exact le_of_lt (by exact_mod_cast h2)
  have hpi : (2 * Real.pi) ^ q.length ≤ (2 * Real.pi) ^ k :=
    pow_le_pow_right₀ (by nlinarith [Real.pi_gt_three]) hlen
  -- assembly
  calc (∫ x in Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pdList q (fun y => Work.Diff.STE.flat.symInvC c a b y) x‖ ^ (2 * p))
        ^ (1 / (2 * p))
      = Work.Diff.STE.flat.rnorm (2 * p) (Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV q γ)) := by
        rw [hpdall]; rfl
    _ ≤ Csob * ((2 * Real.pi) ^ q.length * Real.sqrt Cinv) :=
        hsob.trans (mul_le_mul_of_nonneg_left hsqrt hCsob0)
    _ ≤ Csob * ((2 * Real.pi) ^ k * Real.sqrt Cinv) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpi (Real.sqrt_nonneg _)) hCsob0
    _ = Csob * (2 * Real.pi) ^ k * Real.sqrt Cinv := by ring

end Work.Diff.STE.fill
