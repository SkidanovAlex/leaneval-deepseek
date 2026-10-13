import Mathlib
import Submission.Work.WilE3.Taylor.Grad.tendsto_rpow_nhdsGT_zero_of_pos
import Submission.Work.WilE3.Taylor.Grad.eventually_const_mul_rpow_le
import Submission.Work.WilE3.Taylor.Grad.eventually_sum_abs_eq_mul_sum_abs

/-!
  annals_wilkies_conjecture, AREA E3: the order bookkeeping `order_le_of_rpow_le`.

  Suppose, on a right neighbourhood of `0`,

  `c * |G t| ^ κ ≤ ∑ j, |v j t|`

  with `c > 0`, `κ ≥ 0`, where `G =ᶠ t ^ m * g t` with `g` continuous at `0` and `g 0 ≠ 0`, and
  where `v j =ᶠ t ^ n * w j t` for every `j`.  Since `|G t| ≈ |g 0| · t ^ m` and
  `∑ j |v j t| ≈ (∑ j |w j 0|) · t ^ n`, dividing by `t ^ (κ * m) > 0` produces the eventual
  inequality

  `c * (|g 0| / 2) ^ κ ≤ (∑ j, |w j t|) * t ^ ((n : ℝ) - κ * m)`

  on `𝓝[>] 0`.  The left side is a positive constant, while the right side tends to `0` whenever
  the exponent `(n : ℝ) - κ * m` is positive; hence that exponent must be `≤ 0`, i.e. `n ≤ κ * m`.
-/

open Filter

namespace Work.WilE3.Taylor.Grad

/-- **Order bookkeeping for the `rpow` inequality.**  If `c * |G t| ^ κ ≤ ∑ j, |v j t|` on a
right neighbourhood of `0`, with `G ≈ t ^ m * g` (`g` continuous at `0`, `g 0 ≠ 0`) and
`v j ≈ t ^ n * w j`, then necessarily `n ≤ κ * m`.

Indeed the inequality forces the order `κ * m` of the left side to be at least the order `n` of the
right side: if `(n : ℝ) - κ * m > 0`, then dividing by `t ^ (κ * m)` leaves a positive constant
dominated by a quantity tending to `0`. -/
theorem order_le_of_rpow_le {k : ℕ} {G : ℝ → ℝ} {v : Fin k → ℝ → ℝ}
    {g : ℝ → ℝ} {w : Fin k → ℝ → ℝ} {κ c : ℝ} {m n : ℕ} {i : Fin k}
    (hg : ContinuousAt g 0) (hg0 : g 0 ≠ 0)
    (hGg : G =ᶠ[nhds (0:ℝ)] fun t => t ^ m * g t)
    (hw : ∀ j, ContinuousAt (w j) 0) (hwi0 : w i 0 ≠ 0)
    (hvw : ∀ j, v j =ᶠ[nhds (0:ℝ)] fun t => t ^ n * w j t)
    (hc : 0 < c) (hκ : 0 ≤ κ)
    (hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * |G t| ^ κ ≤ ∑ j, |v j t|) :
    (n : ℝ) ≤ κ * m := by
  have := hwi0
  by_contra hcon
  simp only [not_le] at hcon
  -- `hcon : κ * ↑m < ↑n`
  have hs : 0 < (n : ℝ) - κ * (m : ℝ) := by linarith
  -- Lower bound for the left-hand side and factorisation of the right-hand side.
  have hA := eventually_const_mul_rpow_le (G := G) (g := g) hg hg0 hGg hc hκ
  have hB := eventually_sum_abs_eq_mul_sum_abs (v := v) (w := w) (n := n) hvw
  -- Combine the three eventual statements into one: `c * (|g 0|/2)^κ * (t^m)^κ ≤ t^n * ∑|w j t|`.
  have hcomb : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (|g 0| / 2) ^ κ * (t ^ m) ^ κ ≤ t ^ n * ∑ j, |w j t| := by
    filter_upwards [hA, hB, hineq] with t hAt hBt hI
    rw [hBt] at hI
    exact le_trans hAt hI
  -- Divide by `(t ^ m) ^ κ = t ^ (κ * m) > 0`.
  have hmain : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (|g 0| / 2) ^ κ ≤ (∑ j, |w j t|) * t ^ ((n : ℝ) - κ * (m : ℝ)) := by
    filter_upwards [hcomb, self_mem_nhdsWithin] with t hle ht
    have ht0 : (0 : ℝ) < t := ht
    have hpow : (t ^ m) ^ κ = t ^ (κ * (m : ℝ)) := by
      rw [← Real.rpow_natCast t m, ← Real.rpow_mul (le_of_lt ht0) (m : ℝ) κ, mul_comm]
    have hn : t ^ n = t ^ (κ * (m : ℝ)) * t ^ ((n : ℝ) - κ * (m : ℝ)) := by
      have h1 : (n : ℝ) = κ * (m : ℝ) + ((n : ℝ) - κ * (m : ℝ)) := by ring
      calc t ^ n = t ^ (n : ℝ) := (Real.rpow_natCast t n).symm
        _ = t ^ (κ * (m : ℝ) + ((n : ℝ) - κ * (m : ℝ))) :=
              congrArg (fun e : ℝ => t ^ e) h1
        _ = t ^ (κ * (m : ℝ)) * t ^ ((n : ℝ) - κ * (m : ℝ)) := Real.rpow_add ht0 _ _
    rw [hpow, hn] at hle
    have hpos : 0 < t ^ (κ * (m : ℝ)) := Real.rpow_pos_of_pos ht0 _
    have h2 : t ^ (κ * (m : ℝ)) * (c * (|g 0| / 2) ^ κ) ≤
        t ^ (κ * (m : ℝ)) * ((∑ j, |w j t|) * t ^ ((n : ℝ) - κ * (m : ℝ))) := by
      calc t ^ (κ * (m : ℝ)) * (c * (|g 0| / 2) ^ κ)
          = c * (|g 0| / 2) ^ κ * t ^ (κ * (m : ℝ)) := by ring
        _ ≤ (t ^ (κ * (m : ℝ)) * t ^ ((n : ℝ) - κ * (m : ℝ))) * (∑ j, |w j t|) := hle
        _ = t ^ (κ * (m : ℝ)) * ((∑ j, |w j t|) * t ^ ((n : ℝ) - κ * (m : ℝ))) := by ring
    exact le_of_mul_le_mul_left h2 hpos
  -- The right-hand side of `hmain` tends to `0`.
  have hlim : Tendsto (fun t : ℝ => (∑ j, |w j t|) * t ^ ((n : ℝ) - κ * (m : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hW : Tendsto (fun t : ℝ => ∑ j, |w j t|) (nhds (0 : ℝ)) (nhds (∑ j, |w j 0|)) := by
      apply tendsto_finsetSum (Finset.univ : Finset (Fin k))
      intro j _
      exact (hw j).abs.tendsto
    have h := (hW.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).mul
      (tendsto_rpow_nhdsGT_zero_of_pos hs)
    simpa using h
  -- A positive constant is `≤ 0`: contradiction.
  have hle0 : c * (|g 0| / 2) ^ κ ≤ 0 := ge_of_tendsto hlim hmain
  have hcpos : 0 < c * (|g 0| / 2) ^ κ :=
    mul_pos hc (Real.rpow_pos_of_pos (half_pos (abs_pos.mpr hg0)) κ)
  linarith

end Work.WilE3.Taylor.Grad
