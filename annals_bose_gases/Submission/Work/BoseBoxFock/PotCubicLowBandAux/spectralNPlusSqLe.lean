import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Recomb.recomb_clause
import Submission.Work.BoseFixB2.Sector.secProj_resolution
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.spectralNPlusSqLe`

The **sharp spectral form** `⟨n₊²⟩ ≤ 𝓜⟨n₊⟩` of the corpus's all-moments spectral window
`Work.BoseBox.SpectralNPlusLe ℓ 𝓜 Φ` (FS `eq:LocalizedNPlus`
`1_{[0,𝓜]}(n₊)Φ = Φ`, rendered as `⟨Φ, n₊^m Φ⟩ ≤ 𝓜^m‖Φ‖²` for every `m : ℕ`).

The excitation-number operator `n₊ = Σᵢ Qᵢ` is *bounded* on the box (`Qᵢ` are the
mean-free projections, `0 ≤ n₊ ≤ n`), and the all-moments condition pins its spectrum
down to `[0, 𝓜]`; the honest way to see this in the corpus's vocabulary is the
**sector diagonalisation** of FS §6 (`lem:LocMatrices`):

    `secProj ℓ k Φ = 1_{n₊ = k}Φ`,   `Σ_{k ≤ n} secProj ℓ k Φ = Φ`   (`secProj_resolution`),

the sectors are pairwise orthogonal for the box pairing
(`Recomb.integral_mul_weighted_secProj`, hence Pythagoras), and every iterate of `n₊`
acts on them diagonally:

    `n₊^m Φ = Σ_{k ≤ n} k^m·secProj ℓ k Φ`     (`Recomb.nPlusPow_secProj_sum`).

Writing `w k := ∫_{abox n ℓ} (secProj ℓ k Φ)² ≥ 0` for the sector weights, the
hypothesis becomes `Σ_k k^m w k ≤ 𝓜^m Σ_k w k` for all `m`, and the claim becomes
`Σ_k k² w k ≤ 𝓜 Σ_k k w k`, which follows from the elementary finite-moment lemma
`sum_sq_mul_le_of_moments` below (Chebyshev: a positive weight above `𝓜` would be
amplified by `k^m/𝓜^m → ∞`).

This is exactly the input §4 of `Work.BoseBoxFock.PotCubicLowBandG_holds` consumes
(`⟨n₊²⟩ ≤ bigM·⟨n₊⟩` for a state with `SpectralNPlusLe ℓ bigM Φ`).
-/

namespace Work.BoseBoxFock.PotCubicLowBandAux

open scoped BigOperators
open MeasureTheory

/-- **The finite moment lemma.**  For a finitely supported nonnegative weight `w` on the
integers `0, …, N` whose moments are all dominated by the moments of a point mass
`(Σ_k w k)·δ_t` (`t ≥ 0`), the second moment is dominated by `t` times the first:
`Σ_k k² w k ≤ t·Σ_k k w k`.

*Proof.*  If some `k > t` carried positive weight, the set `S := {k ≤ N | t < k}` would
be nonempty with total weight `B = Σ_{k∈S} w k > 0`, and with `c := min S > t` the
moments would give `c^m·B ≤ t^m·W` (where `W = Σ_k w k`) for every `m`, i.e.
`(c/t)^m·B ≤ W` — impossible for large `m` (and for `t = 0` already at `m = 1`).  So
`w` vanishes on `S`, every term `k(k−t)w k` is `≤ 0`, and summing gives the claim. -/
lemma sum_sq_mul_le_of_moments {N : ℕ} {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) {t : ℝ}
    (ht : 0 ≤ t)
    (h : ∀ m : ℕ, ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ m * w k
        ≤ t ^ m * ∑ k ∈ Finset.range (N + 1), w k) :
    ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ 2 * w k
      ≤ t * ∑ k ∈ Finset.range (N + 1), (k : ℝ) * w k := by
  classical
  -- The set of indices above `t`.
  set S : Finset ℕ := (Finset.range (N + 1)).filter (fun (j : ℕ) => t < (j : ℝ)) with hS
  have hSsub : S ⊆ Finset.range (N + 1) := Finset.filter_subset _ _
  -- The weight of `S` vanishes: otherwise the moments blow up.
  have hB0 : ∑ k ∈ S, w k = 0 := by
    by_contra hBne
    have hBpos : 0 < ∑ k ∈ S, w k :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun k _ => hw k)) (Ne.symm hBne)
    have hSne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      exact hBne (by rw [hempty]; simp)
    set c : ℕ := S.min' hSne with hc
    have hcS : c ∈ S := Finset.min'_mem S hSne
    have hcmin : ∀ k ∈ S, c ≤ k := fun k hk => Finset.min'_le S k hk
    have hct : t < (c : ℝ) := (Finset.mem_filter.mp hcS).2
    have hcle : ∀ m : ℕ, ∀ k ∈ S, (c : ℝ) ^ m ≤ (k : ℝ) ^ m := fun m k hk =>
      pow_le_pow_left₀ (Nat.cast_nonneg c) (by exact_mod_cast hcmin k hk) m
    -- `c^m·(Σ_{k∈S} w k) ≤ 𝓜^m·(Σ_k w k)` for every `m`.
    have hineq : ∀ m : ℕ, (c : ℝ) ^ m * (∑ k ∈ S, w k)
        ≤ t ^ m * (∑ k ∈ Finset.range (N + 1), w k) := by
      intro m
      calc (c : ℝ) ^ m * (∑ k ∈ S, w k)
          = ∑ k ∈ S, (c : ℝ) ^ m * w k := by rw [Finset.mul_sum]
        _ ≤ ∑ k ∈ S, (k : ℝ) ^ m * w k :=
              Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right (hcle m k hk) (hw k))
        _ ≤ ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ m * w k :=
              Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun k _ _ =>
                mul_nonneg (pow_nonneg (Nat.cast_nonneg k) m) (hw k))
        _ ≤ t ^ m * (∑ k ∈ Finset.range (N + 1), w k) := h m
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · -- `t = 0`: the very first moment already contradicts `B > 0` and `c ≥ 1`.
      have h1 := hineq 1
      rw [← ht0] at h1
      norm_num at h1
      have hcpos : (0 : ℝ) < (c : ℝ) := by rw [ht0]; exact hct
      nlinarith [h1, hBpos, hcpos]
    · -- `t > 0`: `(c/t)^m·B ≤ W` for all `m`, impossible since `c/t > 1` and `B > 0`.
      have hcpos : (0 : ℝ) < (c : ℝ) := lt_trans htpos hct
      have hr1 : 1 < (c : ℝ) / t := (one_lt_div htpos).mpr hct
      obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt
        ((∑ k ∈ Finset.range (N + 1), w k) / (∑ k ∈ S, w k)) hr1
      have hm' : (∑ k ∈ Finset.range (N + 1), w k) < ((c : ℝ) / t) ^ m * (∑ k ∈ S, w k) := by
        rw [div_lt_iff₀ hBpos] at hm
        linarith [hm]
      have hle : ((c : ℝ) / t) ^ m * (∑ k ∈ S, w k)
          ≤ ∑ k ∈ Finset.range (N + 1), w k := by
        have h2 := hineq m
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos htpos m)]
        linarith [h2]
      linarith [hm', hle]
  -- Off `S` every term `k(k−t)w k` is `≤ 0`; on `S` the weight vanishes.
  have hoff : ∀ k : ℕ, k ∈ (Finset.range (N + 1)).filter (fun (j : ℕ) => ¬ t < (j : ℝ)) →
      ((k : ℝ) * ((k : ℝ) - t)) * w k ≤ 0 := by
    intro k hk
    obtain ⟨hkN, hkt⟩ := Finset.mem_filter.mp hk
    have hkt' : (k : ℝ) ≤ t := le_of_not_gt hkt
    have hknn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hsub : (k : ℝ) - t ≤ 0 := sub_nonpos.mpr hkt'
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hknn hsub) (hw k)
  have honS : ∀ k : ℕ, k ∈ S → ((k : ℝ) * ((k : ℝ) - t)) * w k = 0 := by
    intro k hk
    have hwk : w k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hw x)).mp hB0 k hk
    rw [hwk, mul_zero]
  have hkey : ∑ k ∈ Finset.range (N + 1), ((k : ℝ) * ((k : ℝ) - t)) * w k ≤ 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range (N + 1))
      (p := fun (j : ℕ) => t < (j : ℝ)) (f := fun k => ((k : ℝ) * ((k : ℝ) - t)) * w k)
    rw [← hsplit]
    have hzero : ∑ k ∈ S, ((k : ℝ) * ((k : ℝ) - t)) * w k = 0 := Finset.sum_eq_zero honS
    rw [hzero, zero_add]
    exact Finset.sum_nonpos hoff
  -- `Σ k² w = Σ k(k−t)w + t·Σ k w ≤ t·Σ k w`.
  calc ∑ k ∈ Finset.range (N + 1), (k : ℝ) ^ 2 * w k
      = ∑ k ∈ Finset.range (N + 1), ((k : ℝ) * ((k : ℝ) - t)) * w k
          + t * ∑ k ∈ Finset.range (N + 1), (k : ℝ) * w k := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
    _ ≤ 0 + t * ∑ k ∈ Finset.range (N + 1), (k : ℝ) * w k := by linarith [hkey]
    _ = t * ∑ k ∈ Finset.range (N + 1), (k : ℝ) * w k := by rw [zero_add]

theorem spectralNPlusSqLe {ℓ 𝓜 : ℝ} (hℓ : 0 < ℓ) (h𝓜 : 0 ≤ 𝓜) {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hmom : ∀ m : ℕ, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseBox.nPlusPow ℓ n m Φ x * Φ x
      ≤ 𝓜 ^ m * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :
    ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n 2 Φ x * Φ x
      ≤ 𝓜 * ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseBox.nPlusPow ℓ n 1 Φ x * Φ x := by
  have hΦc : Continuous Φ := hΦ.continuous
  -- The resolution of the identity `Σ_k 1_{n₊ = k}Φ = Φ`, as an identity of functions.
  have harg : (fun x : Submission.BoseGases.X n => ∑ k ∈ Finset.range (n + 1),
      (fun _ : ℕ => (1 : ℝ)) k * Work.BoseFixB2.secProj ℓ k Φ x) = Φ := by
    have hs : (fun x : Submission.BoseGases.X n => ∑ k ∈ Finset.range (n + 1),
        Work.BoseFixB2.secProj ℓ k Φ x) = Φ := by
      funext x
      have h := congrFun (Work.BoseFixB2.Sector.secProj_resolution hℓ hΦc) x
      rwa [Finset.sum_apply] at h
    rw [show (fun x : Submission.BoseGases.X n => ∑ k ∈ Finset.range (n + 1),
          (fun _ : ℕ => (1 : ℝ)) k * Work.BoseFixB2.secProj ℓ k Φ x)
        = (fun x : Submission.BoseGases.X n => ∑ k ∈ Finset.range (n + 1),
          Work.BoseFixB2.secProj ℓ k Φ x) from by funext x; simp]
    exact hs
  -- Every iterate of `n₊` acts diagonally on the sectors.
  have hpowfun : ∀ m : ℕ, Work.BoseBox.nPlusPow ℓ n m Φ
      = fun x => ∑ k ∈ Finset.range (n + 1),
          (k : ℝ) ^ m * Work.BoseFixB2.secProj ℓ k Φ x := by
    intro m
    have hp := Work.BoseFixB2.Recomb.nPlusPow_secProj_sum (ℓ := ℓ) hℓ hΦ (fun _ : ℕ => (1 : ℝ)) m
    rw [harg] at hp
    simpa using hp
  -- The `m`-th moment of `Φ` is the corresponding moment of the sector weights.
  have hId : ∀ m : ℕ, (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseBox.nPlusPow ℓ n m Φ x * Φ x)
      = ∑ k ∈ Finset.range (n + 1),
          (k : ℝ) ^ m * (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2) := by
    intro m
    have h3 := Work.BoseFixB2.Recomb.integral_mul_weighted_secProj (ℓ := ℓ) hℓ hΦc
      (fun k => (k : ℝ) ^ m) (fun _ : ℕ => (1 : ℝ))
    have hfun : (fun x : Submission.BoseGases.X n =>
          Work.BoseBox.nPlusPow ℓ n m Φ x * Φ x)
        = fun x => (∑ k ∈ Finset.range (n + 1),
              (fun (k : ℕ) => (k : ℝ) ^ m) k * Work.BoseFixB2.secProj ℓ k Φ x)
            * (∑ l ∈ Finset.range (n + 1),
              (fun (_ : ℕ) => (1 : ℝ)) l * Work.BoseFixB2.secProj ℓ l Φ x) := by
      funext x
      rw [congrFun (hpowfun m) x, congrFun harg x]
    rw [hfun]
    simpa using h3
  -- The hypothesis, in terms of the sector weights.
  have hmomW : ∀ m : ℕ, (∑ k ∈ Finset.range (n + 1),
        (k : ℝ) ^ m * (∫ x in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2))
      ≤ 𝓜 ^ m * (∑ k ∈ Finset.range (n + 1),
          (∫ x in Submission.BoseGases.abox n ℓ,
            (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2)) := by
    intro m
    have h0 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        = ∑ k ∈ Finset.range (n + 1),
            (∫ x in Submission.BoseGases.abox n ℓ,
              (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2) := by
      have h := hId 0
      simpa only [pow_zero, one_mul, Work.BoseBox.nPlusPow, pow_two] using h
    have h1 : (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseBox.nPlusPow ℓ n m Φ x * Φ x)
        ≤ 𝓜 ^ m * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := hmom m
    rw [h0] at h1
    rw [hId m] at h1
    exact h1
  -- The finite-moment (Chebyshev) step on the sector weights.
  have key := sum_sq_mul_le_of_moments
    (w := fun k => ∫ x in Submission.BoseGases.abox n ℓ,
      (Work.BoseFixB2.secProj ℓ k Φ x) ^ 2)
    (fun k => integral_nonneg (fun x => sq_nonneg _)) h𝓜 hmomW
  rw [hId 2, hId 1] at *
  simpa using key

end Work.BoseBoxFock.PotCubicLowBandAux
