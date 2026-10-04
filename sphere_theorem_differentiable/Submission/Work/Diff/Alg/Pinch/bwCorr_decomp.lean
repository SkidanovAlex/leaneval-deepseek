import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.BQDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Decomposition of the Böhm–Wilking correction `bwCorr`

`bwCorr a b R` is the difference `linv a b (Q (ell a b R)) - Q R` of Böhm–Wilking Theorem 2:
it is a quadratic function of `R`, given by the explicit combination

`bwCorr a b R = c₀ • (Ric₀ ∧ Ric₀) + 2a • (Ric ∧ Ric) + 2b² • (Ric₀² ∧ id)
                 + c₃ • (id ∧ id)`

of Kulkarni–Nomizu products (`Work.Diff.Alg.Pinch.bwCorr`).

The purpose of the present file is the identity used in the one-step improvement of the cones
`Ccone (ccA n b) b (ccP n b)` (Brendle–Schoen Prop. 13, Böhm–Wilking Lemma 3.4): for the special
parameter values `a = ccA n b`, `p = ccP n b` the *pure* quadratic pieces can be regrouped as a
Kulkarni–Nomizu product of the *shifted* Ricci tensor `Ric - (p·scal/n)·id`:

* the coefficient `2a` is replaced by `2a/(1-p)`, and
* the leading term `c₀ • (Ric₀ ∧ Ric₀) + 2a • (Ric ∧ Ric)` becomes
  `(2a/(1-p)) • ((Ric - (p·scal/n)·id) ∧ (Ric - (p·scal/n)·id))`,

the point being that `1-p = 1/(1+(n-2)b²)`, `2a/(1-p) = (n-2)b² + 2b = c₀ + 2a`, and
`2a = (2a/(1-p))·(1-p)`, so the three coefficients match after expanding `Ric = Ric₀ + (scal/n)·id`.

Everything is formal: the only ingredients are `Ric = Ric₀ + (scal/n)·id` (by definition of
`Ric₀`) and bilinearity of the Kulkarni–Nomizu product.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- Writing `ric S = ric0 S + (scalAlg S / n) • id2 n`, the Kulkarni–Nomizu square of the shifted
Ricci tensor `ric S - c • id2 n` expands as
`(Ric₀ ∧ Ric₀) + 2(t - c) • (Ric₀ ∧ id) + (t - c)² • (id ∧ id)` with `t = scalAlg S / n`. -/
lemma knProd_ric_sub_smul (S : Curv4 n) (c : ℝ) :
    knProd (fun i j => ric S i j - c * id2 n i j) (fun i j => ric S i j - c * id2 n i j)
      = knProd (ric0 S) (ric0 S)
        + (2 * (scalAlg S / (n:ℝ) - c)) • knProd (ric0 S) (id2 n)
        + ((scalAlg S / (n:ℝ) - c)^2) • knProd (id2 n) (id2 n) := by
  funext i j k l
  simp only [knProd, ric0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The `c = 0` case of `knProd_ric_sub_smul`: the Kulkarni–Nomizu square of the Ricci tensor. -/
lemma knProd_ric_self (S : Curv4 n) :
    knProd (ric S) (ric S)
      = knProd (ric0 S) (ric0 S)
        + (2 * (scalAlg S / (n:ℝ))) • knProd (ric0 S) (id2 n)
        + ((scalAlg S / (n:ℝ))^2) • knProd (id2 n) (id2 n) := by
  funext i j k l
  simp only [knProd, ric0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Decomposition of `bwCorr` at the pinching-set parameters `(ccA n b, ccP n b)`.**

The quadratic part `c₀ • (Ric₀ ∧ Ric₀) + 2a • (Ric ∧ Ric)` (with `a = ccA n b`) is regrouped as
the Kulkarni–Nomizu square of the shifted Ricci tensor `Ric - (ccP n b · scal/n) • id`; the
remaining `Ric₀² ∧ id` and `id ∧ id` pieces are unchanged.  The scalar identities behind the
regrouping are `2·ccA n b = (2·ccA n b/(1-ccP n b))·(1-ccP n b)` and
`2·ccA n b/(1-ccP n b) = (n-2)b² + 2b = c₀ + 2·ccA n b`. -/
theorem bwCorr_decomp (n : ℕ) (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2)
    (S : Submission.Diff.Alg.Curv4 n) :
    Work.Diff.Alg.Pinch.bwCorr (Work.Diff.Alg.Pinch.ccA n b) b S
      = (2 * Work.Diff.Alg.Pinch.ccA n b / (1 - Work.Diff.Alg.Pinch.ccP n b)) •
          Work.Diff.Alg.Pinch.knProd
            (fun i j => Work.Diff.Alg.Pinch.ric S i j
              - (Work.Diff.Alg.Pinch.ccP n b * (Submission.Diff.Alg.scalAlg S / (n : ℝ))) * Work.Diff.Alg.Pinch.id2 n i j)
            (fun i j => Work.Diff.Alg.Pinch.ric S i j
              - (Work.Diff.Alg.Pinch.ccP n b * (Submission.Diff.Alg.scalAlg S / (n : ℝ))) * Work.Diff.Alg.Pinch.id2 n i j)
        + (2 * b ^ 2) • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric0sq S) (Work.Diff.Alg.Pinch.id2 n)
        + (2 * Work.Diff.Alg.Pinch.ccA n b * Work.Diff.Alg.Pinch.ccP n b
              * (Submission.Diff.Alg.scalAlg S / (n : ℝ)) ^ 2
            + (((n : ℝ) * b ^ 2 * (1 - 2 * b)
                - 2 * (Work.Diff.Alg.Pinch.ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
                / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * Work.Diff.Alg.Pinch.ccA n b)))
              * Work.Diff.Alg.Pinch.ric0Frob2 S)
          • Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.id2 n) (Work.Diff.Alg.Pinch.id2 n) := by
  have hn1 : 1 ≤ n := by omega
  -- `ccP n b < 1`, so `1 - ccP n b ≠ 0`
  have hden : 1 - ccP n b ≠ 0 := by
    have h := ccP_lt_one hn1 hb hb'
    linarith
  -- the key arithmetic identity `2·ccA/(1-ccP) = (n-2)b² + 2b`
  have hkey : 2 * ccA n b / (1 - ccP n b) = ((n:ℝ) - 2) * b^2 + 2 * b := by
    have hD : (1 : ℝ) + ((n:ℝ) - 2) * b^2 ≠ 0 := ne_of_gt (ccP_denom_pos hn1 hb hb')
    have hone : 1 - ccP n b = 1 / (1 + ((n:ℝ) - 2) * b^2) := by rw [ccP]; ring
    have htwo : 2 * ccA n b = (2 * b + ((n:ℝ) - 2) * b^2) / (1 + ((n:ℝ) - 2) * b^2) := by
      rw [ccA]; field_simp
    rw [htwo, hone, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hD]
    ring
  rw [bwCorr]
  rw [knProd_ric_self S]
  rw [knProd_ric_sub_smul S (ccP n b * (scalAlg S / (n:ℝ)))]
  -- name the atoms: the scalar parameters, and the four tensors in play
  set k : ℝ := 2 * ccA n b / (1 - ccP n b) with hk
  set t : ℝ := scalAlg S / (n:ℝ) with ht
  set C0 : ℝ := ((n:ℝ) - 2) * b^2 - 2 * (ccA n b - b) with hC0
  set Ch : ℝ := ((n : ℝ) * b ^ 2 * (1 - 2 * b)
                - 2 * (ccA n b - b) * (1 - 2 * b + (n : ℝ) * b ^ 2))
                / ((n : ℝ) * (1 + 2 * ((n : ℝ) - 1) * ccA n b)) with hCh
  set P := knProd (ric0 S) (ric0 S) with hP
  set Q := knProd (ric0 S) (id2 n) with hQ
  set R := knProd (id2 n) (id2 n) with hR
  set Ss := knProd (ric0sq S) (id2 n) with hSs
  set fr : ℝ := ric0Frob2 S with hfr
  have h1 : C0 + 2 * (ccA n b) = k := by
    rw [hC0, hkey]; ring
  have h2 : 2 * (ccA n b) - k * (1 - ccP n b) = 0 := by
    rw [hk, div_mul_cancel₀ (2 * ccA n b) hden]; ring
  funext i j k l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (P i j k l) * h1
    + (2 * t * (Q i j k l) + t ^ 2 * (1 - ccP n b) * (R i j k l)) * h2

end Work.Diff.Alg.Pinch
