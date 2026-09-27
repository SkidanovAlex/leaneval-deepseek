import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.H0_invParam_ge

namespace Work.EQ

/-! ## Auxiliary facts for the far-backward (η) region of `candChain`

These are the small technical ingredients of `eqRelC_candChain_etaRegion`:
* `eqRelC_etaRegion_norm_lam_pow_mul_lt`: for every `k : ℕ`, `‖λ^k · (C/z)‖ < min δf ρ`,
  given `‖C/z‖ < min δf ρ · λ^N` and `0 < λ < 1` (the exponents of the mirrored fan of `η`
  are non-negative, and `λ^k ≤ 1`).
* `eqRelC_etaRegion_bsq_subO1_fan_ne_zero`: `FanGood` at a fan value makes the backward
  radicand `bsq (subO1 a ·)` nonzero (its real part is positive).
* `eqRelC_etaRegion_candChain_neg_eqMirror`: the explicit formula for the value of `candChain`
  at a negative index `-(m:ℤ)` with `N ≤ m`: it is the mirrored fan of `η` with parameter
  `λ^m (C/z)` (with the boundary case `m = N` given by the junction hypothesis `hjun`).
-/

open Complex

/-- The `k`-th argument appearing in the mirrored fan of `η` lies in the disc of radius
`min δf ρ`: `‖λ^k (C/z)‖ < min δf ρ`. -/
private lemma eqRelC_etaRegion_norm_lam_pow_mul_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {δf ρ : ℝ} (hδf : 0 < δf) (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) {C z : ℂ}
    (hzc : ‖C / z‖ < min δf ρ * (eqLam a) ^ N) (k : ℕ) :
    ‖(((eqLam a : ℝ) : ℂ) ^ (k:ℤ) * (C / z))‖ < min δf ρ := by
  have hlam0 : (0:ℝ) < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hmin : 0 < min δf ρ := lt_min hδf hρ
  have hpow1 : (eqLam a) ^ N < 1 := pow_lt_one₀ hlam0.le hlam1 (ne_of_gt hN)
  have hle : (eqLam a) ^ k ≤ 1 := pow_le_one₀ hlam0.le hlam1.le
  rw [norm_mul, zpow_natCast]
  have hnorm : ‖(((eqLam a : ℝ) : ℂ) ^ k)‖ = (eqLam a)^k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
  rw [hnorm]
  calc (eqLam a)^k * ‖C / z‖ ≤ 1 * ‖C / z‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖C / z‖ := one_mul _
    _ < min δf ρ * (eqLam a)^N := hzc
    _ < min δf ρ * 1 := mul_lt_mul_of_pos_left hpow1 hmin
    _ = min δf ρ := mul_one _

/-- The backward radicand `bsq (subO1 a Q)` is nonzero at a `FanGood` fan value `Q`. -/
private lemma eqRelC_etaRegion_bsq_subO1_fan_ne_zero {a : ℝ} {h : ℂ → ℂ} {Ke Lam Q δf : ℝ}
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    {ε' : List Bool} {v : ℂ} (hv : ‖v‖ < δf) :
    bsq (subO1 a (fan a h ε' v)) ≠ 0 := by
  have hgood := hFG ε' v hv
  have hre : 0 < (bsq (subO1 a (fan a h ε' v))).re := by
    have h := hgood.2.2.2.2
    simpa [bsq, subO1] using h
  intro h0
  rw [h0] at hre
  simp at hre

/-- **The value of `candChain` at a negative index.**  For `N ≤ m`,
`(candChain a h ε η s N C z).1 (-(m:ℤ)) = eqMirror (fan a h (η.drop (m - N)) (λ^m (C/z)))`.
For `m > N` this is the defining `else` branch of `candChain`; for `m = N` it is the junction
identity `hjun` (the `else` branch of `candChain` instead gives the backward fan of `s`, and
`s.take N = s`). -/
private lemma eqRelC_etaRegion_candChain_neg_eqMirror {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool}
    {N : ℕ} {C z : ℂ}
    (hN : 0 < N) (hη : η.length = N) (hs : s.length = N)
    (hjun : bwdP a s (fan a h ε z) =
      eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z))))
    (m : ℕ) (hm : N ≤ m) :
    (candChain a h ε η s N C z).1 (-(m:ℤ)) =
      eqMirror (fan a h (η.drop (m - N)) (((eqLam a : ℝ) : ℂ) ^ (m:ℤ) * (C / z))) := by
  rcases eq_or_lt_of_le hm with hNm | hlt
  · rw [← hNm]
    simp only [candChain]
    have h1 : ¬ ((0:ℤ) ≤ -(N:ℤ)) := by omega
    have h2 : (-(-(N:ℤ))).toNat ≤ N := by simp
    simp only [h1, h2, ite_false, ite_true]
    simp only [neg_neg, Int.toNat_natCast, Nat.sub_self, List.drop_zero]
    rw [List.take_of_length_le (le_of_eq hs), hjun, zpow_natCast]
  · have h1 : ¬ ((0:ℤ) ≤ -(m:ℤ)) := by omega
    have h2 : ¬ ((-(-(m:ℤ))).toNat ≤ N) := by
      simp only [neg_neg, Int.toNat_natCast]; omega
    simp only [candChain]
    simp only [h1, h2, ite_false]
    simp only [neg_neg, Int.toNat_natCast]

/-- **The candidate chain satisfies the equichordal relation at all indices `n < -N`**, i.e. the
"far backward" end: the junction step `n = -N-1` and the mirrored fan recursion of `η` beyond it.

Let `P n = (candChain a h ε η s N C z).1 n`, `F = fan a h ε z`, `c = C/z`,
`Λ = ((eqLam a : ℝ) : ℂ)` and, for `m ≥ N`,
`G m = fan a h (η.drop (m-N)) (Λ^m * c)`.  The value of `candChain` at a negative index is
`eqMirror (fan a h (η.drop ((-j).toNat - N)) (Λ^j * c))` when `(-j).toNat > N`, and for `m = N`
(pure backward case) `hjun` identifies `P (-(N:ℤ)) = bwdP a (s.take N) F = bwdP a s F` with
`eqMirror (G N)` (using `hs : s.length = N`).  Hence for `m ≥ N`:
`P (-(m:ℤ)) = eqMirror (G m)`.

Now let `n < -(N : ℤ)`, `m := (-n).toNat ≥ N+1`; then `n = -(m:ℤ)` and `n+1 = -((m-1):ℤ)` with
`m-1 ≥ N`, so `P n = eqMirror (G m)`, `P (n+1) = eqMirror (G (m-1))`.  By the mirror swap
`H0_invParam_ge_eqRelC_mirror` (`Submission/Work/EQ/H0_invParam_ge.lean`; or reprove it locally —
it is a two-line `ring`/`linear_combination` computation) it suffices to prove
`EqRelC a (G (m-1)) (G m)`.  Two cases:
* `m ≤ 2N`: then `m-1-N < N = η.length`, so
  `η.drop (m-1-N) = η[m-1-N] :: η.drop (m-N)`, whence `G (m-1) = invBranch a η[m-1-N] (G m)`
  (the `fan` recursion; note `Λ * (Λ^{m-1} * c) = Λ^m * c`), and `eqRelC_invBranch` applies with
  the radicand at `G m = fan a h (η.drop (m-N)) (Λ^m * c)` nonzero by `hFG` and
  `‖Λ^m * c‖ < δf` (from `hzc` and `λ ∈ (0,1)`; the estimate `‖Λ^k * c‖ < min δf ρ` holds for
  every `k : ℕ`).
* `m ≥ 2N+1`: then `η.drop (m-1-N) = η.drop (m-N) = []`, so `G (m-1) = germC a h (Λ^{m-1} * c)`
  and `G m = germC a h (Λ * (Λ^{m-1} * c))`, and `hreg` (with `‖Λ^{m-1} * c‖ < ρ`) gives the
  `RegPair`, hence `EqRelC`.  (`hδf` and `hρ` follow from `hz`/`hzc`.) -/
theorem eqRelC_candChain_etaRegion {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {N : ℕ} (hN : 0 < N) {ε η s : List Bool}
    (hη : η.length = N) (hs : s.length = N) {C : ℂ} {Ke Lam Q δf ρ : ℝ}
    (hδf : 0 < δf) (hρ : 0 < ρ)
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    (hreg : ∀ u : ℂ, ‖u‖ < ρ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    {z : ℂ} (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N)
    (hzc : ‖C / z‖ < min δf ρ * (eqLam a) ^ N)
    (hjun : bwdP a s (fan a h ε z) =
      eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z))))
    {n : ℤ} (hn : n < -(N : ℤ)) :
    EqRelC a ((candChain a h ε η s N C z).1 n)
      ((candChain a h ε η s N C z).1 (n + 1)) := by
  have _hh := hh
  have _hz := hz
  have hlam0 : (0:ℝ) < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hlamCne : ((eqLam a : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]; exact ne_of_gt hlam0
  have hbound : ∀ k : ℕ, ‖(((eqLam a : ℝ) : ℂ) ^ (k:ℤ) * (C / z))‖ < min δf ρ :=
    fun k => eqRelC_etaRegion_norm_lam_pow_mul_lt ha0 ha1 hδf hρ hN hzc k
  have hboundρ : ∀ k : ℕ, ‖(((eqLam a : ℝ) : ℂ) ^ (k:ℤ) * (C / z))‖ < ρ :=
    fun k => lt_of_lt_of_le (hbound k) (min_le_right _ _)
  have hboundδ : ∀ k : ℕ, ‖(((eqLam a : ℝ) : ℂ) ^ (k:ℤ) * (C / z))‖ < δf :=
    fun k => lt_of_lt_of_le (hbound k) (min_le_left _ _)
  have hfan_ne : ∀ (ε' : List Bool) (k : ℕ),
      bsq (subO1 a (fan a h ε' (((eqLam a : ℝ) : ℂ) ^ (k:ℤ) * (C / z)))) ≠ 0 :=
    fun ε' k => eqRelC_etaRegion_bsq_subO1_fan_ne_zero hFG (hboundδ k)
  have hPval := eqRelC_etaRegion_candChain_neg_eqMirror (a := a) (h := h) (ε := ε) (η := η)
    (s := s) (N := N) (C := C) (z := z) hN hη hs hjun
  -- write `n = -(m:ℤ)` with `m = (-n).toNat ≥ N+1`
  obtain ⟨m, hmn, hmge⟩ : ∃ m : ℕ, n = -(m:ℤ) ∧ N + 1 ≤ m := by
    refine ⟨(-n).toNat, ?_, ?_⟩
    · have hcast : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      rw [hcast]; ring
    · have hcast : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      omega
  have hmN : N ≤ m := by omega
  have hmN1 : N ≤ m - 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hmcast : (m : ℤ) = (((m - 1 : ℕ)) : ℤ) + 1 := by
    have hsub : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := Nat.cast_sub hm1
    omega
  have hmn1 : n + 1 = -(((m - 1 : ℕ)) : ℤ) := by omega
  have hPn : (candChain a h ε η s N C z).1 n =
      eqMirror (fan a h (η.drop (m - N)) (((eqLam a : ℝ) : ℂ) ^ (m:ℤ) * (C / z))) := by
    rw [hmn]; exact hPval m hmN
  have hPn1 : (candChain a h ε η s N C z).1 (n + 1) =
      eqMirror (fan a h (η.drop ((m - 1) - N))
        (((eqLam a : ℝ) : ℂ) ^ (((m - 1 : ℕ)) : ℤ) * (C / z))) := by
    rw [hmn1]; exact hPval (m - 1) hmN1
  -- the core: `EqRelC a (G (m-1)) (G m)`
  have hmain : EqRelC a (fan a h (η.drop ((m - 1) - N))
        (((eqLam a : ℝ) : ℂ) ^ (((m - 1 : ℕ)) : ℤ) * (C / z)))
      (fan a h (η.drop (m - N)) (((eqLam a : ℝ) : ℂ) ^ (m:ℤ) * (C / z))) := by
    by_cases hle : m ≤ 2 * N
    · -- still inside the word `η`: one fan recursion step of `η`
      have hk : (m - 1) - N < η.length := by rw [hη]; omega
      have hidx : (m - 1) - N + 1 = m - N := by omega
      have hdrop : η.drop ((m - 1) - N) = η[(m - 1) - N] :: η.drop (m - N) := by
        rw [List.drop_eq_getElem_cons hk, hidx]
      rw [hdrop, fan_cons]
      have hzpow : (((eqLam a : ℝ) : ℂ) *
            ((((eqLam a : ℝ) : ℂ) ^ (((m - 1 : ℕ)) : ℤ)) * (C / z)))
          = (((eqLam a : ℝ) : ℂ) ^ (m:ℤ)) * (C / z) := by
        rw [hmcast, zpow_add_one₀ hlamCne]; ring
      rw [hzpow]
      exact eqRelC_invBranch (η[(m - 1) - N]) (hfan_ne (η.drop (m - N)) m)
    · -- beyond the word `η`: the germ recursion
      have hdrop1 : η.drop ((m - 1) - N) = [] := by
        rw [List.drop_eq_nil_iff, hη]; omega
      have hdrop2 : η.drop (m - N) = [] := by
        rw [List.drop_eq_nil_iff, hη]; omega
      rw [hdrop1, hdrop2, fan_nil, fan_nil]
      have hzpow : (((eqLam a : ℝ) : ℂ) *
            ((((eqLam a : ℝ) : ℂ) ^ (((m - 1 : ℕ)) : ℤ)) * (C / z)))
          = (((eqLam a : ℝ) : ℂ) ^ (m:ℤ)) * (C / z) := by
        rw [hmcast, zpow_add_one₀ hlamCne]; ring
      rw [← hzpow]
      exact (hreg ((((eqLam a : ℝ) : ℂ) ^ (((m - 1 : ℕ)) : ℤ)) * (C / z))
        (hboundρ (m - 1))).1
  rw [hPn, hPn1]
  exact (H0_invParam_ge_eqRelC_mirror (a := a)
    (P := fan a h (η.drop ((m - 1) - N))
      (((eqLam a : ℝ) : ℂ) ^ (((m - 1 : ℕ)) : ℤ) * (C / z)))
    (Q := fan a h (η.drop (m - N)) (((eqLam a : ℝ) : ℂ) ^ (m:ℤ) * (C / z)))).mpr hmain

end Work.EQ
