import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.leftCoord.wMap_large_estimates
import Submission.Work.Parab.leftCoord.wMap_orbit_estimates

/-!
# The `wMap`-orbit reaches every level to the right, keeping its imaginary part

For the chart dynamics `wMap f w = -1 / f (-1/w)` of a parabolic germ `f z = z + z^2 h z`
(`ParabolicBounds f h a r A A'`) every point `x` in the far wedge
`{M < |Im x|, Re x > -3 |Im x|}`, with `M = M(N)` large, has an orbit whose real part crosses
the level `N`:

* `n` is the first index with `Re (wMap f)^[n] x > N` (and `Re (wMap f)^[k] x ≤ N` for `k < n`);
* on the way (`k ≤ n`) the orbit keeps `|Im x| / 4 ≤ ‖wMap^k x‖`, so it never comes near the
  origin where the estimates degenerate;
* its imaginary part drifts only by `C (1 + log (k+1))` (`C` a constant depending on `f` and `N`),
* and the quadratic tail `∑_{k<n} 1/‖wMap^k x‖²` is `≤ C / |Im x|`.

The proof is a one-dimensional induction.  Writing `w _ k := (wMap f)^[k] x`, the invariant
`|Im x|/2 ≤ ‖w k‖ ∧ Re x + k/2 ≤ Re (w k) ∧ |Im (w k) - Im x| ≤ 2K k / |Im x|` is preserved as
long as `k ≤ k₀ := ⌈2N + 6|Im x|⌉₊ + 3`, because the one-step expansion
`‖wMap f ζ - (ζ+1)‖ ≤ K/‖ζ‖` (valid for `R < ‖ζ‖`) gives `Re (wMap f ζ) ≥ Re ζ + 1/2` and
`|Im (wMap f ζ) - Im ζ| ≤ K/‖ζ‖`; the hypothesis `Re x > -3 |Im x|` is exactly what makes `k₀`
steps enough to push the real part past `N` (each step gains `1/2`, and `Re x` is at worst
`-3|Im x| ≈ -k₀/2`).
-/

namespace Work.Parab.leftCoordData

open Finset

/-- The arithmetic bookkeeping of the induction: for `100 K ≤ |im0|`, `100 N ≤ |im0|` and
`1 ≤ |im0|`, the exit index `k₀ ≈ 2N + 6|im0|` satisfies the three numerical bounds used below
(the norm is kept, the imaginary drift is bounded, and the sum of the `1/‖w k‖²` is `≤ C/|im0|`). -/
private theorem orbit_arith {K N im0 : ℝ} (hK : 0 ≤ K) (hN : 0 < N) (h1 : 1 ≤ |im0|)
    (hN2 : 100 * N ≤ |im0|) (hK2 : 100 * K ≤ |im0|) {k₀ : ℕ}
    (hk₀ : (k₀ : ℝ) ≤ 2 * N + 6 * |im0| + 4) :
    4 * K * (k₀ : ℝ) ≤ |im0| ^ 2 / 2 ∧
    4 * (k₀ : ℝ) ≤ (4 * K * N + 20 * K + 98) * |im0| ∧
    2 * K * (k₀ : ℝ) ≤ (4 * K * N + 20 * K) * |im0| := by
  have hA0 : (0:ℝ) < |im0| := lt_of_lt_of_le (by norm_num) h1
  have hA : (0:ℝ) ≤ |im0| := le_of_lt hA0
  have hk0nn : (0:ℝ) ≤ (k₀ : ℝ) := Nat.cast_nonneg k₀
  have hNK : N ≤ |im0| := by linarith
  have hKN : K * N ≤ K * |im0| := mul_le_mul_of_nonneg_left hNK hK
  have hKA : 100 * K * |im0| ≤ |im0| * |im0| := mul_le_mul_of_nonneg_right hK2 hA
  have hK1 : K * 1 ≤ K * |im0| := mul_le_mul_of_nonneg_left h1 hK
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hk₀, hK, hKN, hKA, hK1, hk0nn, hA0]
  · nlinarith [hk₀, hK, hNK, hN2, hK2, hA0]
  · nlinarith [hk₀, hK, hKN, hK1, hKA, hk0nn, hA0]

/-- Summing the per-term bound `1/‖u k‖² ≤ 1/c²` over `k < n`. -/
private theorem sum_inv_sq_le {u : ℕ → ℂ} {c : ℝ} (hc : 0 < c) (n : ℕ)
    (h : ∀ k < n, c ≤ ‖u k‖) :
    ∑ k ∈ Finset.range n, 1 / ‖u k‖ ^ 2 ≤ (n : ℝ) / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hterm : ∀ k ∈ Finset.range n, 1 / ‖u k‖ ^ 2 ≤ 1 / c ^ 2 := by
    intro k hk
    have h1 : c ≤ ‖u k‖ := h k (Finset.mem_range.mp hk)
    have h2 : c ^ 2 ≤ ‖u k‖ ^ 2 := by nlinarith [norm_nonneg (u k)]
    exact one_div_le_one_div_of_le hc2 h2
  calc ∑ k ∈ Finset.range n, 1 / ‖u k‖ ^ 2
      ≤ ∑ _k ∈ Finset.range n, 1 / c ^ 2 := Finset.sum_le_sum hterm
    _ = (Finset.range n).card • (1 / c ^ 2) := Finset.sum_const _
    _ = (n : ℝ) * (1 / c ^ 2) := by simp
    _ = (n : ℝ) / c ^ 2 := by ring


theorem orbit_ends_control {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') {N : ℝ} (hN : 0 < N) :
    ∃ M C : ℝ, 0 < M ∧ 0 ≤ C ∧ ∀ x : ℂ, M < |x.im| → -3 * |x.im| < x.re →
      ∃ n : ℕ,
        N < ((Work.FatouCoord.wMap f)^[n] x).re ∧
        (∀ k < n, ((Work.FatouCoord.wMap f)^[k] x).re ≤ N) ∧
        (∀ k ≤ n, |x.im| / 4 ≤ ‖(Work.FatouCoord.wMap f)^[k] x‖) ∧
        (∀ k ≤ n, |((Work.FatouCoord.wMap f)^[k] x).im - x.im| ≤ C * (1 + Real.log (k + 1))) ∧
        (∑ k ∈ Finset.range n, 1 / ‖(Work.FatouCoord.wMap f)^[k] x‖ ^ 2 ≤ C / |x.im|) := by
  obtain ⟨N₀, K, hN₀pos, hN₀r, hKnn, hstep⟩ := Work.Parab.leftCoord.wMap_step_bound_norm hb
  set M : ℝ := 100 * K + 4 * N₀ + 100 * N + 101 with hMdef
  set C : ℝ := 4 * K * N + 20 * K + 98 with hCdef
  have hMpos : 0 < M := by rw [hMdef]; linarith
  have hCnn : 0 ≤ C := by rw [hCdef]; nlinarith [hKnn, hN]
  refine ⟨M, C, hMpos, hCnn, ?_⟩
  intro x hxim hxre
  have hxM : 100 * K + 4 * N₀ + 100 * N + 101 < |x.im| := by rwa [hMdef] at hxim
  have him1 : (1:ℝ) < |x.im| := by linarith [hN₀pos, hN]
  have him100K : 100 * K < |x.im| := by linarith [hN₀pos, hN]
  have him100N : 100 * N < |x.im| := by linarith [hN₀pos, hKnn]
  have him4N₀ : 4 * N₀ < |x.im| := by linarith [hN, hKnn]
  have himpos : 0 < |x.im| := lt_trans (by norm_num) him1
  let w : ℕ → ℂ := fun k => (Work.FatouCoord.wMap f)^[k] x
  have hwsucc : ∀ k : ℕ, w (k+1) = Work.FatouCoord.wMap f (w k) := fun k =>
    Function.iterate_succ_apply' _ k x
  set k₀ : ℕ := ⌈2 * N + 6 * |x.im|⌉₊ + 3 with hk₀def
  have hk₀le : ((k₀:ℕ):ℝ) ≤ 2 * N + 6 * |x.im| + 4 := by
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * N + 6 * |x.im| by positivity)
    rw [hk₀def]; push_cast; linarith
  have hk₀ge : 2 * N + 6 * |x.im| ≤ ((k₀:ℕ):ℝ) := by
    have h := Nat.le_ceil (2 * N + 6 * |x.im|)
    rw [hk₀def]; push_cast; linarith
  obtain ⟨har1, har2, har3⟩ := orbit_arith hKnn hN (le_of_lt him1) (le_of_lt him100N)
      (le_of_lt him100K) hk₀le
  have key : ∀ k ≤ k₀, |x.im| / 2 ≤ ‖w k‖ ∧ x.re + (k:ℝ)/2 ≤ (w k).re ∧
      |(w k).im - x.im| ≤ 2 * K * (k:ℝ) / |x.im| := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · show |x.im| / 2 ≤ ‖x‖
        have := Complex.abs_im_le_norm x
        linarith
      · show x.re + ((0:ℕ):ℝ) / 2 ≤ x.re
        simp
      · show |x.im - x.im| ≤ 2 * K * ((0:ℕ):ℝ) / |x.im|
        simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ k₀ := Nat.le_of_succ_le hk
      obtain ⟨hnorm, hre, him⟩ := ih hk'
      have hN₀lt : N₀ < ‖w k‖ := by linarith
      obtain ⟨hstepN, hstepR⟩ := hstep (w k) hN₀lt
      have hwk : w (k+1) = Work.FatouCoord.wMap f (w k) := hwsucc k
      have him_new : |(w (k+1)).im - x.im| ≤ 2 * K * ((k+1:ℕ):ℝ) / |x.im| := by
        have h1 : |(w (k+1)).im - (w k).im| ≤ K / ‖w k‖ := by
          rw [hwk]
          have h2 : (Work.FatouCoord.wMap f (w k)).im - (w k).im
              = (Work.FatouCoord.wMap f (w k) - (w k + 1)).im := by simp
          rw [h2]
          exact le_trans (Complex.abs_im_le_norm _) hstepN
        have h3 : K / ‖w k‖ ≤ 2 * K / |x.im| := by
          have h4 := div_le_div_of_nonneg_left hKnn (show 0 < |x.im|/2 by linarith) hnorm
          have h5 : K / (|x.im| / 2) = 2 * K / |x.im| := by field_simp
          linarith
        calc |(w (k+1)).im - x.im|
            ≤ |(w (k+1)).im - (w k).im| + |(w k).im - x.im| := abs_sub_le _ _ _
          _ ≤ K / ‖w k‖ + 2 * K * (k:ℝ) / |x.im| := by linarith
          _ ≤ 2 * K / |x.im| + 2 * K * (k:ℝ) / |x.im| := by linarith
          _ = 2 * K * ((k+1:ℕ):ℝ) / |x.im| := by push_cast; field_simp; ring
      refine ⟨?_, ?_, him_new⟩
      · have h3 : 2 * K * ((k+1:ℕ):ℝ) / |x.im| ≤ |x.im| / 2 := by
          rw [div_le_iff₀ himpos]
          have h4 : 4 * K * ((k+1:ℕ):ℝ) ≤ |x.im|^2 / 2 := by
            have h5 : ((k+1:ℕ):ℝ) ≤ (k₀:ℝ) := by exact_mod_cast hk
            nlinarith [har1, hKnn, h5]
          nlinarith [h4]
        have h6 : |x.im| - 2 * K * ((k+1:ℕ):ℝ) / |x.im| ≤ |(w (k+1)).im| := by
          have h := abs_sub_le x.im ((w (k+1)).im) 0
          rw [sub_zero, abs_sub_comm] at h
          simp only [sub_zero] at h
          linarith
        have h7 : |(w (k+1)).im| ≤ ‖w (k+1)‖ := Complex.abs_im_le_norm _
        linarith
      · rw [hwk]
        push_cast
        linarith
  have hk₀P : N < (w k₀).re := by
    have h := (key k₀ le_rfl).2.1
    have h2 : 2 * (N - x.re) < (k₀:ℝ) := by
      have h3 : -2 * x.re < 6 * |x.im| := by nlinarith [hxre]
      linarith [hk₀ge]
    linarith
  have hex : ∃ m : ℕ, N < (w m).re := ⟨k₀, hk₀P⟩
  set n : ℕ := Nat.find hex with hndef
  have hnP : N < (w n).re := by
    rw [hndef]; exact Nat.find_spec hex
  have hnmin : ∀ k < n, (w k).re ≤ N := by
    intro k hk
    rw [hndef] at hk
    exact not_lt.mp (Nat.find_min hex hk)
  have hnle : n ≤ k₀ := by
    rw [hndef]; exact Nat.find_le hk₀P
  refine ⟨n, hnP, hnmin, ?_, ?_, ?_⟩
  · intro k hk
    have h1 : |x.im| / 2 ≤ ‖w k‖ := (key k (le_trans hk hnle)).1
    linarith
  · intro k hk
    have h1 : |(w k).im - x.im| ≤ 2 * K * (k:ℝ) / |x.im| := (key k (le_trans hk hnle)).2.2
    have h2 : 2 * K * (k:ℝ) / |x.im| ≤ C * (1 + Real.log ((k:ℝ) + 1)) := by
      have hk' : (k:ℝ) ≤ (k₀:ℝ) := by exact_mod_cast (le_trans hk hnle)
      have h3 : 2 * K * (k:ℝ) ≤ (4*K*N + 20*K) * |x.im| := by
        have h4 : 2 * K * (k:ℝ) ≤ 2 * K * (k₀:ℝ) := by nlinarith [hKnn, hk']
        linarith [har3]
      have h4 : 2 * K * (k:ℝ) / |x.im| ≤ 4*K*N + 20*K := by
        rw [div_le_iff₀ himpos]; linarith [h3]
      have h5 : 4*K*N + 20*K ≤ C * (1 + Real.log ((k:ℝ) + 1)) := by
        rw [hCdef]
        have hknn : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        have hlog : 0 ≤ Real.log ((k:ℝ) + 1) := Real.log_nonneg (by linarith)
        nlinarith [hKnn, hN]
      linarith
    simpa only [Nat.cast_add, Nat.cast_one] using le_trans h1 h2
  · have hsum := sum_inv_sq_le (u := w) (c := |x.im| / 2) (by linarith) n
      (fun k hk => (key k (le_of_lt (lt_of_lt_of_le hk hnle))).1)
    have h2 : (n:ℝ) / (|x.im|/2)^2 ≤ C / |x.im| := by
      have h3 : (n:ℝ) / (|x.im|/2)^2 = 4 * (n:ℝ) / |x.im|^2 := by
        field_simp
        ring
      rw [h3]
      have hn' : (n:ℝ) ≤ (k₀:ℝ) := by exact_mod_cast hnle
      have h4 : 4 * (n:ℝ) ≤ C * |x.im| := by
        rw [hCdef]; nlinarith [har2, hn']
      have h5 : 4 * (n:ℝ) / |x.im| ≤ C := by
        rw [div_le_iff₀ himpos]; exact h4
      have h6 : 4 * (n:ℝ) / |x.im|^2 = (4 * (n:ℝ) / |x.im|) / |x.im| := by
        rw [pow_two, div_div]
      rw [h6]
      exact div_le_div_of_nonneg_right h5 (le_of_lt himpos)
    linarith

end Work.Parab.leftCoordData
