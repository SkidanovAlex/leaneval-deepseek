import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.exists_regular_of_family
import Submission.Work.EQ.eqRelC_candChain_fanRegion
import Submission.Work.EQ.eqRelC_candChain_etaRegion

namespace Work.EQ

open Complex

noncomputable section

/-!
## Auxiliary facts about `candChain`

The main theorem below splits the integer index line into four windows, each of which is the
recursion of one of the three objects defining `candChain` (the stable fan of `ε`, the principal
germ, the backward iterates along `s`, and the mirrored fan of `η`).  The lemmas in this section
record the explicit value of `candChain` in the corresponding window, and the two elementary size
estimates saying that every fan argument occurring in the construction is small.
-/

/-- **The value of `candChain` at a nonnegative index.**  For `0 ≤ n` the index-`n` point is the
fan of the suffix `ε.drop n.toNat` evaluated at `λ^{n} z`.  (When `n.toNat > N` the suffix is empty
and the fan is the germ, so the formula covers both the fan window `n ≤ N` and the germ window
`n ≥ N`.) -/
private theorem eccAux_val_nonneg {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool} {N : ℕ} {C z : ℂ}
    {n : ℤ} (hε : ε.length = N) (hn : 0 ≤ n) :
    (candChain a h ε η s N C z).1 n
      = fan a h (ε.drop n.toNat) (((eqLam a : ℝ) : ℂ) ^ (n.toNat : ℤ) * z) := by
  have hn' : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn
  by_cases hle : n.toNat ≤ N
  · simp only [candChain, if_pos hn, if_pos hle]
    rw [hn']
  · have hnil : ε.drop n.toNat = [] := by
      apply List.drop_eq_nil_of_le
      rw [hε]
      exact Nat.le_of_not_le hle
    simp only [candChain, if_pos hn, if_neg hle, hnil, fan_nil]
    rw [hn']

/-- **The value of `candChain` at index `-m` for `m ≤ N`.**  The point is the `m`-fold backward
image of the fan of `ε` along the sign list `s`. -/
private theorem eccAux_val_neg_le {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool} {N : ℕ} {C z : ℂ}
    {m : ℕ} (hm : m ≤ N) :
    (candChain a h ε η s N C z).1 (-(m : ℤ))
      = bwdP a (s.take m) (fan a h ε z) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simp [candChain, bwdP_nil]
  · have hneg : ¬ (0 ≤ (-(m : ℤ))) := by omega
    have htoNat : (-(-(m : ℤ))).toNat = m := by rw [neg_neg, Int.toNat_natCast]
    simp only [candChain, if_neg hneg, htoNat, if_pos hm]

/-- **The value of `candChain` at index `-m` for `N ≤ m`.**  The point is the mirror image of the
fan of `η` evaluated at `λ^m (C/z)`; at `m = N` this is the junction identity `hjun` (the `N`-th
backward iterate of the fan of `ε` equals the mirror of the fan of `η`). -/
private theorem eccAux_val_neg_gt {a : ℝ} {h : ℂ → ℂ} {ε η s : List Bool} {N : ℕ} {C z : ℂ}
    {m : ℕ} (hN : 0 < N) (hη : η.length = N) (hs : s.length = N)
    (hjun : bwdP a s (fan a h ε z)
      = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z))))
    (hm : N ≤ m) :
    (candChain a h ε η s N C z).1 (-(m : ℤ))
      = eqMirror (fan a h (η.drop (m - N)) (((eqLam a : ℝ) : ℂ) ^ m * (C / z))) := by
  have hneg : ¬ (0 ≤ (-(m : ℤ))) := by omega
  have htoNat : (-(-(m : ℤ))).toNat = m := by rw [neg_neg, Int.toNat_natCast]
  simp only [candChain, if_neg hneg, htoNat]
  by_cases hle : m ≤ N
  · have hmN : m = N := le_antisymm hle hm
    rw [if_pos hle, hmN]
    rw [show s.take N = s from List.take_of_length_le (by rw [hs])]
    rw [hjun]
    simp
  · rw [if_neg hle, zpow_natCast]

/-- **The basic size estimate.**  If `‖z‖ < min δf ρ · λ^N` and `0 < λ < 1`, then
`‖λ^k z‖ < min δf ρ` for *every* `k : ℕ`: the argument of every fan occurring in `candChain`
(either `λ^k z` or, with `z` replaced by `C/z`, `λ^k (C/z)`) lies strictly inside the disc where
the uniform fan estimates hold. -/
private theorem eccAux_norm_pow_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {δf ρ : ℝ} {N : ℕ}
    {z : ℂ} (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N) (k : ℕ) :
    ‖(((eqLam a : ℝ) : ℂ) ^ k * z)‖ < min δf ρ := by
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hδ0 : 0 < min δf ρ := by
    by_contra h
    push_neg at h
    have h1 : min δf ρ * eqLam a ^ N ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (pow_nonneg hl0.le N)
    linarith [norm_nonneg z]
  calc ‖(((eqLam a : ℝ) : ℂ) ^ k * z)‖
      = (eqLam a) ^ k * ‖z‖ := by
        rw [norm_mul, norm_pow, Complex.norm_of_nonneg hl0.le]
    _ < (eqLam a) ^ k * (min δf ρ * (eqLam a) ^ N) :=
        mul_lt_mul_of_pos_left hz (pow_pos hl0 k)
    _ = min δf ρ * (eqLam a) ^ (k + N) := by rw [pow_add]; ring
    _ ≤ min δf ρ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hl0.le hl1.le) hδ0.le
    _ = min δf ρ := mul_one _

/-- **The size estimate for the backward windows.**  If `k ≤ N` then the backward argument
`z / λ^k` is still inside the fan disc. -/
private theorem eccAux_norm_div_lt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {δf ρ : ℝ} {N : ℕ}
    {z : ℂ} (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N) {k : ℕ} (hk : k ≤ N) :
    ‖z / (((eqLam a : ℝ) : ℂ) ^ k)‖ < min δf ρ := by
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hδ0 : 0 < min δf ρ := by
    by_contra h
    push_neg at h
    have h1 : min δf ρ * eqLam a ^ N ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (pow_nonneg hl0.le N)
    linarith [norm_nonneg z]
  calc ‖z / (((eqLam a : ℝ) : ℂ) ^ k)‖
      = ‖z‖ / (eqLam a) ^ k := by
        rw [norm_div, norm_pow, Complex.norm_of_nonneg hl0.le]
    _ < (min δf ρ * (eqLam a) ^ N) / (eqLam a) ^ k :=
        div_lt_div_of_pos_right hz (pow_pos hl0 k)
    _ = min δf ρ * (eqLam a) ^ (N - k) := by
        rw [div_eq_iff (pow_ne_zero k (ne_of_gt hl0)), mul_assoc, ← pow_add,
          Nat.sub_add_cancel hk]
    _ ≤ min δf ρ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hl0.le hl1.le) hδ0.le
    _ = min δf ρ := mul_one _

/-- `bsq (subO1 a Q)` written out with the cast `↑(a/2)` (the form in which the radicand appears
in `EqRelC`) — definitional. -/
private theorem eccAux_bsq' (a : ℝ) (Q : ℂ × ℂ) :
    bsq (subO1 a Q) = (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 := rfl

/-- `bsq (subO1 a Q)` written out with the cast `(a : ℂ) / 2` (the form in which the radicand
appears in `FanGood`). -/
private theorem eccAux_bsq (a : ℝ) (Q : ℂ × ℂ) :
    bsq (subO1 a Q) = (Q.1 + (a : ℂ) / 2) ^ 2 + Q.2 ^ 2 := by
  simp only [bsq, subO1]
  push_cast
  ring

/-- **`bwdP` applied to a fan value is a fan value again**: with `λ = eqLam a`,
`bwdP a l (fan a h ε u) = fan a h (l.reverse ++ ε) (u/λ^{|l|})`.  Purely algebraic (the only
side condition is `λ ≠ 0`); it identifies the intermediate points of the backward window of
`candChain` as fan values, to which `FanGood` applies. -/
private theorem eccAux_bwdP_fan {a : ℝ} (h : ℂ → ℂ) (hlam : ((eqLam a : ℝ) : ℂ) ≠ 0)
    (l ε : List Bool) (u : ℂ) :
    bwdP a l (fan a h ε u) =
      fan a h (l.reverse ++ ε) (u / (((eqLam a : ℝ) : ℂ) ^ l.length)) := by
  induction l generalizing ε u with
  | nil => simp [bwdP]
  | cons s₀ l' ih =>
    have h1 : bwdP a (s₀ :: l') (fan a h ε u) =
        bwdP a l' (fan a h (s₀ :: ε) (u / ((eqLam a : ℝ) : ℂ))) := by
      rw [bwdP_cons, fan_cons]
      congr 1
      field_simp
    rw [h1, ih]
    have hL : l'.reverse ++ (s₀ :: ε) = (s₀ :: l').reverse ++ ε := by
      rw [List.reverse_cons, List.append_assoc]
      congr 1
    have hR : (u / ((eqLam a : ℝ) : ℂ)) / (((eqLam a : ℝ) : ℂ) ^ l'.length)
        = u / (((eqLam a : ℝ) : ℂ) ^ (s₀ :: l').length) := by
      rw [List.length_cons, div_div, pow_succ]
      ring
    rw [hL, hR]

/-- **The backward window `-N ≤ n < 0`.**  Both `P n` and `P (n+1)` are backward iterates of the
fan of `ε` along `s`, so they differ by one `invBranch` step: `eqRelC_bwdP_step` applies, and the
nonvanishing of the radicand at the second point is supplied by `FanGood` after rewriting the
backward iterate as a fan value (`eccAux_bwdP_fan`) with argument `z/λ^k` (`eccAux_norm_div_lt`). -/
private theorem eccAux_bwdRegion {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {N : ℕ} (hN : 0 < N) {ε η s : List Bool} (hs : s.length = N) {C : ℂ} {Ke Lam Q δf ρ : ℝ}
    (hδf : 0 < δf)
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    {z : ℂ} (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N)
    {n : ℤ} (hn1 : -(N : ℤ) ≤ n) (hn2 : n < 0) :
    EqRelC a ((candChain a h ε η s N C z).1 n)
      ((candChain a h ε η s N C z).1 (n + 1)) := by
  have hm_le : (-n).toNat ≤ N := (Int.toNat_le).mpr (by omega)
  have hk_le : (-(n + 1)).toNat ≤ N := (Int.toNat_le).mpr (by omega)
  have hm_eq : n = -(((-n).toNat : ℕ) : ℤ) := by
    have := Int.toNat_of_nonneg (show (0:ℤ) ≤ -n by omega); omega
  have hk_eq : n + 1 = -(((-(n + 1)).toNat : ℕ) : ℤ) := by
    have := Int.toNat_of_nonneg (show (0:ℤ) ≤ -(n + 1) by omega); omega
  have hk1 : (-n).toNat = (-(n + 1)).toNat + 1 := by
    have h := Int.toNat_add (show (0:ℤ) ≤ -(n + 1) by omega)
      (show (0:ℤ) ≤ (1:ℤ) by norm_num)
    rw [Int.toNat_one] at h
    have h2 : (-(n + 1) + 1).toNat = (-n).toNat := by congr 1; ring
    omega
  set k : ℕ := (-(n + 1)).toNat with hkdef
  have hPn : (candChain a h ε η s N C z).1 n = bwdP a (s.take (k + 1)) (fan a h ε z) := by
    rw [hm_eq, eccAux_val_neg_le hm_le, hk1]
  have hPn1 : (candChain a h ε η s N C z).1 (n + 1) = bwdP a (s.take k) (fan a h ε z) := by
    rw [hk_eq, eccAux_val_neg_le hk_le]
  have hklt : k < s.length := by rw [hs]; omega
  have htake : s.take (k + 1) = s.take k ++ [s[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hklt]
    rfl
  rw [hPn, hPn1, htake]
  refine eqRelC_bwdP_step ?_
  set W : ℂ × ℂ := fan a h ((s.take k).reverse ++ ε)
    (z / (((eqLam a : ℝ) : ℂ) ^ (s.take k).length)) with hW
  have hlen : (s.take k).length ≤ N := by
    rw [List.length_take]
    exact le_trans (min_le_left _ _) hk_le
  have hnorm : ‖z / (((eqLam a : ℝ) : ℂ) ^ (s.take k).length)‖ < δf :=
    lt_of_lt_of_le (eccAux_norm_div_lt ha0 ha1 hz hlen) (min_le_left _ _)
  have hpos : 0 < ((W.1 + (a : ℂ) / 2) ^ 2 + W.2 ^ 2).re :=
    (hFG ((s.take k).reverse ++ ε) (z / (((eqLam a : ℝ) : ℂ) ^ (s.take k).length))
      hnorm).2.2.2.2
  have hrew : bwdP a (s.take k) (fan a h ε z)
      = fan a h ((s.take k).reverse ++ ε)
          (z / (((eqLam a : ℝ) : ℂ) ^ (s.take k).length)) :=
    eccAux_bwdP_fan h (Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos' ha0 ha1)))
      (s.take k) ε z
  rw [hrew, ← hW]
  intro h0
  rw [← eccAux_bsq a W] at hpos
  rw [← eccAux_bsq' a W] at h0
  rw [h0] at hpos
  simp at hpos

/-- **The germ window `n ≥ N`.**  For indices at or beyond the depth `N` both `P n` and
`P (n+1)` are germ points, so the principal recursion `RegPair a (germC u) (germC (λu))` applies
at `u = λ^n z` (which lies in the disc of radius `ρ` by `eccAux_norm_pow_lt`). -/
private theorem eccAux_germRegion {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {N : ℕ} {ε η s : List Bool} (hε : ε.length = N)
    {C : ℂ} {δf ρ : ℝ}
    (hreg : ∀ u : ℂ, ‖u‖ < ρ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    {z : ℂ} (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N)
    {n : ℤ} (hn : (N : ℤ) ≤ n) :
    EqRelC a ((candChain a h ε η s N C z).1 n)
      ((candChain a h ε η s N C z).1 (n + 1)) := by
  have hn0 : 0 ≤ n := by omega
  have hn0' : 0 ≤ n + 1 := by omega
  have hNatN : N ≤ n.toNat := (Int.le_toNat hn0).mpr hn
  have hNatN' : N ≤ (n + 1).toNat := (Int.le_toNat hn0').mpr (by omega)
  have hdrop : ε.drop n.toNat = [] := by
    apply List.drop_eq_nil_of_le; rw [hε]; exact hNatN
  have hdrop' : ε.drop (n + 1).toNat = [] := by
    apply List.drop_eq_nil_of_le; rw [hε]; exact hNatN'
  have hPn : (candChain a h ε η s N C z).1 n
      = germC a h (((eqLam a : ℝ) : ℂ) ^ n.toNat * z) := by
    rw [eccAux_val_nonneg hε hn0, hdrop, fan_nil, zpow_natCast]
  have hPn1 : (candChain a h ε η s N C z).1 (n + 1)
      = germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1).toNat * z) := by
    rw [eccAux_val_nonneg hε hn0', hdrop', fan_nil, zpow_natCast]
  have htoNat1 : (n + 1).toNat = n.toNat + 1 := by
    rw [Int.toNat_add hn0 (by norm_num : (0:ℤ) ≤ 1), Int.toNat_one]
  have hu : ‖(((eqLam a : ℝ) : ℂ) ^ n.toNat * z)‖ < ρ :=
    lt_of_lt_of_le (eccAux_norm_pow_lt ha0 ha1 hz n.toNat) (min_le_right _ _)
  have hEq := (hreg _ hu).1
  rw [hPn, hPn1]
  have hval : (eqLam a : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n.toNat * z)
      = ((eqLam a : ℝ) : ℂ) ^ (n + 1).toNat * z := by
    rw [htoNat1, pow_succ]; ring
  rw [← hval]
  exact hEq

/-- **The candidate chain satisfies the equichordal relation at every step.**  Let `Ke, Lam, Q, δf`
be the constants of the uniform fan estimates (`FanGood`, see `Work.EQ.fan_induction`), let `ρ` be a
radius on which the principal germ recursion holds (`Work.EQ.germC_facts`), and let `ε, η, s` be
words of length `N ≥ 1`.  For `z, C` with `‖z‖ < min δf ρ * λ^N` and `‖C/z‖ < min δf ρ * λ^N`
(so every argument of a fan — or of a germ — appearing in `candChain` is in the corresponding disc)
and with the junction identity `bwdP a s (fan a h ε z) = eqMirror (fan a h η (λ^N * (C/z)))`, the
candidate chain `candChain a h ε η s N C z` links every consecutive pair by `EqRelC`.

This is the "the family of candidate chains is a family of chains" computation: the pairs
`n ≥ N` are the principal (`germC`) pairs, the pairs `0 ≤ n < N` are the fan recursion of `ε`, the
pairs `-N ≤ n < 0` are the backward recursion of `s` (using `bwdP a l (fan a h ε z) =
fan a h (l.reverse ++ ε) (z/λ^{|l|})`, so `FanGood` supplies the nonvanishing radicand), the pair
`n = -N-1` is the junction identity combined with the mirror-swap `EqRelC a P Q ↔
EqRelC a (eqMirror Q) (eqMirror P)` and the recursion of `η`, and the pairs `n < -N-1` are the
mirrored fan recursion of `η`. -/
theorem eqRelC_candChain {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {N : ℕ} (hN : 0 < N) {ε η s : List Bool}
    (hε : ε.length = N) (hη : η.length = N) (hs : s.length = N) {C : ℂ}
    {Ke Lam Q δf ρ : ℝ}
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    (hreg : ∀ u : ℂ, ‖u‖ < ρ → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)))
    {z : ℂ} (hz : ‖z‖ < min δf ρ * (eqLam a) ^ N)
    (hzc : ‖C / z‖ < min δf ρ * (eqLam a) ^ N)
    (hjun : bwdP a s (fan a h ε z) = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))) :
    ∀ n : ℤ, EqRelC a ((candChain a h ε η s N C z).1 n)
      ((candChain a h ε η s N C z).1 (n + 1)) := by
  have hδ0 : 0 < min δf ρ := by
    by_contra hcon
    push_neg at hcon
    have h1 : min δf ρ * (eqLam a) ^ N ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon (pow_nonneg (le_of_lt (eqLam_pos' ha0 ha1)) N)
    linarith [norm_nonneg z]
  have hδf0 : 0 < δf := lt_of_lt_of_le hδ0 (min_le_left _ _)
  have hρ0 : 0 < ρ := lt_of_lt_of_le hδ0 (min_le_right _ _)
  intro n
  by_cases hN1 : (N : ℤ) ≤ n
  · exact eccAux_germRegion ha0 ha1 hε hreg hz hN1
  · have hN1' : n < (N : ℤ) := by omega
    by_cases h0 : 0 ≤ n
    · exact eqRelC_candChain_fanRegion ha0 ha1 hε hδf0 hFG hz h0 hN1'
    · have h0' : n < 0 := by omega
      by_cases h1 : -(N : ℤ) ≤ n
      · exact eccAux_bwdRegion ha0 ha1 hN hs hδf0 hFG hz h1 h0'
      · have h1' : n < -(N : ℤ) := by omega
        exact eqRelC_candChain_etaRegion ha0 ha1 hh hN hη hs hδf0 hρ0 hFG hreg hz hzc hjun h1'

end

end Work.EQ
