import Mathlib
import Submission.Work.NAKANE.Defs
import Submission.Work.Bottcher.Core.ProductFormulaTelescoping

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE.Asymptotic

open Work.Bottcher

/-- **The product formula is *positive real* at positive real points.**  For real `c > 0` and real
`x > 0` there is a positive real `r` with `bottcher (c:ℂ) (x:ℂ) = (r : ℂ)`.

Route: `bottcher c z = z * exp (bottcherSeries c z)`.  For real `c > 0` and real `x > 0` the whole
`pMap c`-orbit of `x` is real and `> 0` (`pMap c w = (w^2 + c)^2 + c > 0` for real `w`), hence every
factor `normFactor c ((pMap c)^[n] x) = pMap c w / w^4` is a *positive real*, so `Complex.log` of it
is the real logarithm (`Complex.ofReal_log`) and each term
`4^{-(n+1)} * log (normFactor …)` of `bottcherSeries` is real.  `Complex.ofReal_tsum` is
unconditional, so `bottcherSeries (c:ℂ) (x:ℂ) = (s:ℂ)` for some real `s`, and
`bottcher (c:ℂ) (x:ℂ) = (x * Real.exp s : ℂ)` with `x * Real.exp s > 0`. -/
theorem bottcher_real_pos {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ Work.Bottcher.bottcher (c : ℂ) (x : ℂ) = (r : ℂ) := by
  -- The real orbit `u n = (pMap c)^[n] x`, computed as `(qReal c)^[n] x`, is positive.
  have hqpos : ∀ n : ℕ, 0 < (Work.Bottcher.Core.qReal c)^[n] x := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        simp only [Work.Bottcher.Core.qReal]
        nlinarith [sq_nonneg (((Work.Bottcher.Core.qReal c)^[n] x) ^ 2 + c), hc]
  -- Each term of the Böttcher series is a real number.
  have hterm : ∀ n : ℕ,
      Work.Bottcher.bottcherTerm (c : ℂ) n (x : ℂ)
        = (((1 / 4 : ℝ) ^ (n + 1) *
            Real.log (Work.Bottcher.Core.qReal c ((Work.Bottcher.Core.qReal c)^[n] x)
              / ((Work.Bottcher.Core.qReal c)^[n] x) ^ 4) : ℝ) : ℂ) := by
    intro n
    have hu : 0 < (Work.Bottcher.Core.qReal c)^[n] x := hqpos n
    have hnum : 0 < Work.Bottcher.Core.qReal c ((Work.Bottcher.Core.qReal c)^[n] x) := by
      simp only [Work.Bottcher.Core.qReal]
      nlinarith [sq_nonneg (((Work.Bottcher.Core.qReal c)^[n] x) ^ 2 + c), hc]
    have hpos : (0 : ℝ) < Work.Bottcher.Core.qReal c ((Work.Bottcher.Core.qReal c)^[n] x)
        / ((Work.Bottcher.Core.qReal c)^[n] x) ^ 4 :=
      div_pos hnum (pow_pos hu 4)
    rw [Work.Bottcher.bottcherTerm, Work.Bottcher.Core.pMap_iterate_ofReal,
      Work.Bottcher.Core.normFactor_ofReal, ← Complex.ofReal_log hpos.le,
      ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  -- The series is a real number.
  set S : ℝ := ∑' n : ℕ, (1 / 4 : ℝ) ^ (n + 1) *
      Real.log (Work.Bottcher.Core.qReal c ((Work.Bottcher.Core.qReal c)^[n] x)
        / ((Work.Bottcher.Core.qReal c)^[n] x) ^ 4) with hSdef
  have hseries : Work.Bottcher.bottcherSeries (c : ℂ) (x : ℂ) = (S : ℂ) := by
    rw [Work.Bottcher.bottcherSeries]
    rw [show (∑' n : ℕ, Work.Bottcher.bottcherTerm (c : ℂ) n (x : ℂ))
        = ∑' n : ℕ, (((1 / 4 : ℝ) ^ (n + 1) *
            Real.log (Work.Bottcher.Core.qReal c ((Work.Bottcher.Core.qReal c)^[n] x)
              / ((Work.Bottcher.Core.qReal c)^[n] x) ^ 4) : ℝ) : ℂ)
        from tsum_congr hterm]
    rw [← Complex.ofReal_tsum, hSdef]
  refine ⟨x * Real.exp S, by positivity, ?_⟩
  rw [Work.Bottcher.bottcher, hseries, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

end Work.NAKANE.Asymptotic
