/-
  WilC4/ratio_lower_infty : the *lower bound at `+∞`* for the doubling ratio of a
  `∅`-definable family of graphs.

  ## The statement

  For a `∅`-definable family `Y ⊆ ℝ^{k+2}` whose fibres are graphs, there is a *uniform*
  constant `m > 0` such that for every parameter `c` and all large enough `t`

    `f_c t ≠ 0  →  m * |f_c t| ≤ |f_c (2 t)|`.

  ## The proof

  No o-minimality, no breakpoint family and no telescoping is needed: the whole content is
  already contained in the *polynomial boundedness* hypothesis

    `hPB : PolyBoundedRExp`

  which — applied to `Y` itself, with the parameter `c` playing the role of the family
  parameter — gives a *finite* set `Qs : Finset ℚ` such that every fibre `c ↦ f_c` either
  vanishes identically for large `x`, or is asymptotic to a monomial `a · x ^ q` with
  `q ∈ Qs`, `a ≠ 0`.

  * For a fibre of the first kind there is nothing to prove: beyond the vanishing threshold
    the only value is `0`, and the hypothesis `y ≠ 0` is contradictory.
  * For a fibre of the second kind, the asymptotic relation at the tolerance `|a| / 2`
    gives the two two-sided estimates `|f_c t| ≤ (3|a|/2) t^q` and
    `|f_c (2t)| ≥ (|a|/2) (2t)^q`, whence `|f_c (2t)| / |f_c t| ≥ 2^q / 3`.

  The uniform constant is `2 ^ (min Qs) / 3` (the `min` exists because `Qs` is finite and
  nonempty; if `Qs` is empty then every fibre vanishes eventually and `m = 1` works).

  The hypotheses `hBcard` and `GoodFibre Y B` are not needed for this statement; they are
  the structural hypotheses of the surrounding ULPM argument and are recorded here because
  the callers pass them along.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ULPMAsm
import Submission.Work.WilC0.Main

namespace Work.WilC4

/-- **Upper estimate.**  If `y / t ^ q` is within the relative tolerance `1/2` of `a`, then
`|y|` is at most `(3 |a| / 2) · t ^ q`. -/
lemma abs_le_mul_rpow_of_close {y t q a : ℝ} (ht : 0 < t)
    (h : |y / t ^ q - a| < |a| / 2) : |y| ≤ 3 * |a| / 2 * t ^ q := by
  have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  have h1 : |y / t ^ q| < 3 * |a| / 2 := by
    have h2 := abs_add_le (y / t ^ q - a) a
    have he : y / t ^ q - a + a = y / t ^ q := by ring
    rw [he] at h2
    linarith
  have h3 : |y| = |y / t ^ q| * t ^ q := by
    rw [abs_div, abs_of_pos htq]
    exact (div_mul_cancel₀ |y| (ne_of_gt htq)).symm
  rw [h3]
  exact mul_le_mul_of_nonneg_right (le_of_lt h1) (le_of_lt htq)

/-- **Lower estimate.**  If `y / t ^ q` is within the relative tolerance `1/2` of `a`, then
`|y|` is at least `(|a| / 2) · t ^ q`. -/
lemma mul_rpow_le_abs_of_close {y t q a : ℝ} (ht : 0 < t)
    (h : |y / t ^ q - a| < |a| / 2) : |a| / 2 * t ^ q ≤ |y| := by
  have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  have h1 : |a| / 2 ≤ |y / t ^ q| := by
    have h2 := abs_sub_abs_le_abs_sub a (y / t ^ q)
    have he : a - y / t ^ q = -(y / t ^ q - a) := by ring
    rw [he, abs_neg] at h2
    linarith
  have h3 : |y| = |y / t ^ q| * t ^ q := by
    rw [abs_div, abs_of_pos htq]
    exact (div_mul_cancel₀ |y| (ne_of_gt htq)).symm
  rw [h3]
  exact mul_le_mul_of_nonneg_right h1 (le_of_lt htq)

theorem ratio_lower_infty {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B : Set (Fin (k + 1) → ℝ)) (N₀ : ℕ)
    (hBcard : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ B}.encard ≤ N₀)
    (hgf : Work.WilC4.GoodFibre Y B) :
    ∃ m : ℝ, 0 < m ∧ ∀ c : Fin k → ℝ, ∃ R : ℝ, ∀ t : ℝ, R ≤ t →
      ∀ y y' : ℝ, Work.WilC4.Route.Gr Y c t y → Work.WilC4.Route.Gr Y c (2 * t) y' →
        y ≠ 0 → m * |y| ≤ |y'| := by
  -- `C0` turns the `LRc`-definability of `Y` into `RExpExist Y`, so that `hPB` applies.
  have hYrex : WilkiesDesign.RExpExist Y :=
    WilkiesDesign.CG.C0_rexp_syntax_proved hR Y hY
  -- polynomial boundedness: a finite exponent set, and each fibre vanishes eventually or is
  -- asymptotic to a monomial with exponent from the finite set.
  obtain ⟨Qs, hQs⟩ := hPB k Y hYrex hfun
  rcases Qs.eq_empty_or_nonempty with hQe | hQne
  · -- `Qs = ∅`: every fibre vanishes for large `x`, so the fibre carries no nonzero value there
    refine ⟨1, one_pos, fun c => ?_⟩
    rcases hQs c with h1 | ⟨q, hq, a, ha, hε⟩
    · obtain ⟨R0, hR0⟩ := h1
      exact ⟨R0, fun t ht y y' hy hy' hy0 => absurd (hR0 t y ht hy) hy0⟩
    · exact absurd (hQe ▸ hq) (by simp)
  · -- the uniform constant: `2 ^ (min Qs) / 3`
    refine ⟨(2 : ℝ) ^ ((Qs.min' hQne : ℚ) : ℝ) / 3, by positivity, fun c => ?_⟩
    rcases hQs c with h1 | ⟨q, hq, a, ha, hε⟩
    · -- the fibre vanishes for large `x`: no nonzero `y` is available
      obtain ⟨R0, hR0⟩ := h1
      exact ⟨R0, fun t ht y y' hy hy' hy0 => absurd (hR0 t y ht hy) hy0⟩
    · -- the fibre is asymptotic to `a · x ^ q`; the scale `t` is chosen so that `t` and `2t`
      -- both lie in the asymptotic regime.
      have hmle : (2 : ℝ) ^ ((Qs.min' hQne : ℚ) : ℝ) / 3 ≤ (2 : ℝ) ^ (q : ℝ) / 3 := by
        have hmin : ((Qs.min' hQne : ℚ) : ℝ) ≤ (q : ℝ) := by
          have h := Finset.min'_le Qs q hq
          exact_mod_cast h
        have h2 : (2 : ℝ) ^ ((Qs.min' hQne : ℚ) : ℝ) ≤ (2 : ℝ) ^ (q : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hmin
        linarith
      have hapos : 0 < |a| := abs_pos.mpr ha
      obtain ⟨R1, hR1⟩ := hε (|a| / 2) (by linarith)
      refine ⟨max R1 1, fun t ht y y' hy hy' hy0 => ?_⟩
      have htR1 : R1 ≤ t := le_trans (le_max_left _ _) ht
      have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
      have htpos : 0 < t := lt_of_lt_of_le one_pos ht1
      have hy_est : |y / t ^ (q : ℝ) - a| < |a| / 2 := hR1 t y htR1 hy
      have h2t_est : |y' / (2 * t) ^ (q : ℝ) - a| < |a| / 2 :=
        hR1 (2 * t) y' (by linarith) hy'
      have hup := abs_le_mul_rpow_of_close htpos hy_est
      have hlo := mul_rpow_le_abs_of_close (show (0 : ℝ) < 2 * t by linarith) h2t_est
      calc (2 : ℝ) ^ ((Qs.min' hQne : ℚ) : ℝ) / 3 * |y|
          ≤ (2 : ℝ) ^ (q : ℝ) / 3 * |y| :=
            mul_le_mul_of_nonneg_right hmle (abs_nonneg y)
        _ ≤ (2 : ℝ) ^ (q : ℝ) / 3 * (3 * |a| / 2 * t ^ (q : ℝ)) :=
            mul_le_mul_of_nonneg_left hup (by positivity)
        _ = |a| / 2 * (2 * t) ^ (q : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (le_of_lt htpos)]
            ring
        _ ≤ |y'| := hlo

end Work.WilC4
