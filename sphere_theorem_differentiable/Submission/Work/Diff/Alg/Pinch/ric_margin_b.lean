import Mathlib
import Submission.Work.Diff.Alg.Pinch.RoomAux.RFAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The quantitative Böhm–Wilking Ricci margin, branch `0 < b ≤ 1/2`

`ric_margin_b` is the *quantitative* form of the pointwise strictness
`Work.Diff.Alg.Pinch.ricForm_X_strict_at_tight`: if `S ∈ Dpic (ccP n b)` is nonzero and `v ≠ 0`
is a *tight* direction of the Ricci pinching of `S`, then the pulled-back reaction

`X = linv (ccA n b) b (Q (ell (ccA n b) b S))`

improves the Ricci form by at least the explicit positive amount

`RFAux.bwCρ n b · |Ric₀ S|² · |v|²`,

i.e. `bwCρ n b · ric0Frob2 S · |v|² ≤ ric X v v − (ccP n b · scal X / n) · |v|²`.

The proof is the same computation as in `ric_X_strict_aux` (Böhm–Wilking Theorem 2, via the
identity `linv a b (Q (ell a b R)) = Q R + bwCorr a b R` of `Work.Diff.Alg.Pinch.linv_Q_ell`):

* `QY_lower` bounds `ricForm (Q (ell a b S)) v` from below by the `bwS`-combination;
* `scalAlg_Q_ell` identifies `scalAlg (Q (ell a b S))` with `bwsQY`;
* `bwCρ_key` is the *identity* behind `RFAux.bw_final_algebra`, which holds without the
  positivity assumptions on `ρ` and `q` that the strict statement needs.

The only structural difference from `ric_X_strict_aux` is that the improvement is measured by the
*identity* `bwCρ ρ q = (1−β(n−2))·X + …` rather than by strict positivity, so the argument also
covers the case `Ric₀ S = 0` (e.g. `S = Iso n`), where the conclusion degenerates to `0 ≤ ·`.
-/

namespace Work.Diff.Alg.Pinch.RFAux

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The algebraic identity behind `bw_final_algebra`, **without** the positivity hypotheses on `ρ`
and `q`: both sides are equal as rational functions of `(n, b, s, ρ, q)`.  (The proof is the
`key` step of `bw_final_algebra`, where only `ρ > 0`, `q > 0` were used at the very end.) -/
theorem bwCρ_key (n : ℕ) (hn : 2 ≤ n) {b s ρ q : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    (1 - bwβ n b * ((n : ℝ) - 2))
          * (2 * (bwS1 n b s q + b * bwS2 n b s ρ q
              + (ccA n b * s / (n : ℝ)) * bwS3 n b s q))
        + (bwβ n b * ((n : ℝ) - 2) - ccP n b) * (bwsQY n b s ρ / (n : ℝ)) * q
        - bwγ0 n b * bwsQY n b s ρ * (2 * (n : ℝ) - 2) * q * (1 - ccP n b)
      = bwCρ n b * ρ * q := by
  have hn0 : ((n : ℝ)) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  have hnm1 : (0 : ℝ) ≤ ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hnm2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hA0 : 1 + ((n : ℝ) - 2) * b ≠ 0 := by
    have : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b := by nlinarith
    linarith
  have hq0 : 1 + ((n : ℝ) - 2) * b ^ 2 ≠ 0 := by
    have hb2 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
    have h : (0 : ℝ) < 1 + ((n : ℝ) - 2) * b ^ 2 := by nlinarith
    linarith
  have hR0 : 1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 ≠ 0 := by
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt (by
        have : (0 : ℕ) < n := by omega
        exact_mod_cast this)) hnm2) (sq_nonneg b)
    have h1 : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) * b :=
      mul_nonneg (mul_nonneg (by norm_num) hnm1) hb.le
    have h : (0 : ℝ) < 1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2 := by
      nlinarith [h1, h2]
    linarith
  have hden : 1 + 2 * ((n : ℝ) - 1) * ccA n b
      = (1 + 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 2) * b ^ 2)
          / (1 + ((n : ℝ) - 2) * b ^ 2) := by
    rw [ccA]
    field_simp
    ring
  simp only [bwβ, bwγ0, bwS1, bwS2, bwS3, bwsQY, bwCρ, bwΛ, bwμ, bwA0, bwκ, bwR, bwq0]
  rw [hden]
  simp only [ccA, ccP]
  field_simp
  set_option maxHeartbeats 4000000 in
  ring_nf

end Work.Diff.Alg.Pinch.RFAux

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

theorem ric_margin_b (n : ℕ) (hn2 : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    {S : Submission.Diff.Alg.Curv4 n} (hS : Submission.Diff.Alg.IsAlgCurv S) (hS0 : S ≠ 0)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hric : Work.Diff.Alg.Pinch.RicPinch (Work.Diff.Alg.Pinch.ccP n b) S)
    {v : Fin n → ℝ} (hv : v ≠ 0)
    (htight : (Work.Diff.Alg.Pinch.ccP n b * Submission.Diff.Alg.scalAlg S / ↑n)
        * (∑ i, v i * v i) = ∑ i, ∑ j, Work.Diff.Alg.Pinch.ric S i j * v i * v j) :
    Work.Diff.Alg.Pinch.RFAux.bwCρ n b * Work.Diff.Alg.Pinch.ric0Frob2 S * (∑ i, v i * v i)
      ≤ (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric
              (Work.Diff.Alg.Pinch.linv (Work.Diff.Alg.Pinch.ccA n b) b
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell (Work.Diff.Alg.Pinch.ccA n b) b S)))
              i j * v i * v j)
        - (Work.Diff.Alg.Pinch.ccP n b * Submission.Diff.Alg.scalAlg
              (Work.Diff.Alg.Pinch.linv (Work.Diff.Alg.Pinch.ccA n b) b
                (Submission.Diff.Alg.Q (Work.Diff.Alg.Pinch.ell (Work.Diff.Alg.Pinch.ccA n b) b S)))
              / ↑n) * (∑ i, v i * v i) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
  have hn0 : ((n : ℝ)) ≠ 0 := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  have hA0pos : 0 < 1 + ((n : ℝ) - 2) * b := by
    have hnm2 : (0 : ℝ) ≤ ((n : ℝ) - 2) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    nlinarith
  have hβ0 : 1 + ((n : ℝ) - 2) * b ≠ 0 := ne_of_gt hA0pos
  have haden : 1 + 2 * ((n : ℝ) - 1) * ccA n b ≠ 0 := ccA_denom_ne hn1 hb hb'
  have hY : IsAlgCurv (ell (ccA n b) b S) := ell_isAlgCurv n (ccA n b) b hS
  have hQYalg : IsAlgCurv (Q (ell (ccA n b) b S)) := Q_isAlgCurv n hY
  have hρeq : ric0Frob2 S = ∑ p, ∑ q, ric0 S p q ^ 2 := by
    simp only [ric0Frob2, pow_two]
  rw [hρeq]
  rw [show (∑ i, ∑ j, ric (linv (ccA n b) b (Q (ell (ccA n b) b S))) i j * v i * v j)
      = RFAux.ricForm (linv (ccA n b) b (Q (ell (ccA n b) b S))) v from rfl]
  -- the algebraic splitting of `ricForm (linv a b Y) v` (as in `ric_X_strict_aux`)
  have hE : RFAux.ricForm (linv (ccA n b) b (Q (ell (ccA n b) b S))) v
        - (ccP n b * scalAlg (linv (ccA n b) b (Q (ell (ccA n b) b S))) / (n : ℝ))
            * (∑ i, v i * v i)
      = (1 - b / (1 + ((n : ℝ) - 2) * b) * ((n : ℝ) - 2))
          * RFAux.ricForm (Q (ell (ccA n b) b S)) v
        + (b / (1 + ((n : ℝ) - 2) * b) * ((n : ℝ) - 2) - ccP n b)
            * (scalAlg (Q (ell (ccA n b) b S)) / (n : ℝ)) * (∑ i, v i * v i)
        - ((ccA n b / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * ccA n b))
            * scalAlg (Q (ell (ccA n b) b S)) * (2 * (n : ℝ) - 2) * (∑ i, v i * v i)
            * (1 - ccP n b) := by
    rw [RFAux.qform_ric_linv n (ccA n b) b (Y := Q (ell (ccA n b) b S)) v,
      scalAlg_linv n (a := ccA n b) (b := b) hβ0 haden hQYalg]
    field_simp
    ring
  rw [hE]
  rw [RFAux.scalAlg_Q_ell n hn0 (b := b) hS]
  rw [show b / (1 + ((n : ℝ) - 2) * b) = RFAux.bwβ n b from rfl]
  rw [show (ccA n b / (n : ℝ)) / (1 + 2 * ((n : ℝ) - 1) * ccA n b) = RFAux.bwγ0 n b from rfl]
  have hkey := RFAux.bwCρ_key n hn2 (s := scalAlg S) (ρ := ∑ p, ∑ q, ric0 S p q ^ 2)
    (q := ∑ i, v i * v i) hb hb'
  have hQY := RFAux.QY_lower n hn2 hb hb' hS hP hric htight
  have hβc : (1 : ℝ) - RFAux.bwβ n b * ((n : ℝ) - 2) = 1 / (1 + ((n : ℝ) - 2) * b) := by
    rw [show RFAux.bwβ n b = b / (1 + ((n : ℝ) - 2) * b) from rfl]
    rw [eq_div_iff hβ0, sub_mul, one_mul]
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hβ0]
    ring
  have hβnn : 0 ≤ (1 : ℝ) / (1 + ((n : ℝ) - 2) * b) := by positivity
  have hmono : (1 - RFAux.bwβ n b * ((n : ℝ) - 2))
        * (2 * (RFAux.bwS1 n b (scalAlg S) (∑ i, v i * v i)
            + b * RFAux.bwS2 n b (scalAlg S) (∑ p, ∑ q, ric0 S p q ^ 2) (∑ i, v i * v i)
            + (ccA n b * scalAlg S / (n : ℝ)) * RFAux.bwS3 n b (scalAlg S) (∑ i, v i * v i)))
      ≤ (1 - RFAux.bwβ n b * ((n : ℝ) - 2)) * RFAux.ricForm (Q (ell (ccA n b) b S)) v := by
    rw [hβc]
    exact mul_le_mul_of_nonneg_left hQY hβnn
  linarith [hkey, hmono]

end Work.Diff.Alg.Pinch
