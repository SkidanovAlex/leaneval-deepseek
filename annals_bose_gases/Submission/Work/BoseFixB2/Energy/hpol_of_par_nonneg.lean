import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.RCLike.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Energy.hpol_of_par_nonneg`

The **polarisation of a non-negative solution of the parallelogram law is `ℝ`-homogeneous in its
first variable**.

For a function `Q : V → ℝ` on a real vector space which

* satisfies the parallelogram law `Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y` (`hpar`),
* is `2`-homogeneous, `Q (t • x) = t ^ 2 * Q x` (`hhom`), and
* is **non-negative**, `0 ≤ Q x` for all `x` (`hnn`),

one has

`Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y))`     for all `t : ℝ`, `x y : V`.

In other words the polar form `B x y = (Q (x + y) - Q (x - y)) / 4` is `ℝ`-homogeneous in its
first variable.  The statement is the missing hypothesis `hpol` of
`Work.BoseFixB2.Polar.par_polarisation_hpol`, and it is *not* a formal consequence of `hpar` and
`hhom` alone: the sibling module `Work.BoseFixB2.Polar.par_polarisation` records that for fixed
`(x, y)` the defect

`D t = (Q (t • x + y) - Q (t • x - y)) - t * (Q (x + y) - Q (x - y))`

is a *derivation* of `ℝ`, and that non-zero derivations of `ℝ` exist (the Wronskian form of
`∂/∂π`); that Wronskian form is not non-negative, and this is exactly what the present
hypothesis `hnn` excludes.  (The same conclusion, in the same form, is the content of
`Work.BoseFixB2.Recomb.jvn_polar_homogeneous_of_nonneg`.)

## Proof

Fix `x y`.  Write `G u = Q (u + y) - Q (u - y)` for the polarised difference.  From the
parallelogram law alone one gets the three-term identity

`(Q (a+b+c) - Q (a+b-c)) + (Q (a-b+c) - Q (a-b-c)) = 2 (Q (a+c) - Q (a-c))`,

obtained from the parallelogram law at the pairs `(a+c, b)`, `(a-c, b)`, `(a, b+c)`, `(a, b-c)`;
combining it at `(a,b,c)` with the same identity at `(b,a,c)` gives additivity of `G`:

`G (a + b) = G a + G b`.

Consequently the defect `F t = G (t • x) - t * (Q (x + y) - Q (x - y))` is additive in `t`, and
`F 1 = 0`.  It is also bounded on `[-1, 1]`: the parallelogram law at `(t • x, y)` writes
`Q (t•x+y) + Q (t•x-y) = 2 t² Q x + 2 Q y` as a sum of two non-negative numbers, so that
`|G (t • x)| ≤ 2 t² Q x + 2 Q y`, whence `|F t| ≤ (2 Q x + 2 Q y) + |Q (x+y) - Q (x-y)|` for
`|t| ≤ 1`.  An additive function `ℝ → ℝ` bounded on a neighbourhood of `0` is `ℝ`-linear
(proof below: it is continuous at `0` by a scaling argument, hence continuous, hence agrees with
`t ↦ t * F 1` on the dense set `ℚ`).  Thus `F t = t * F 1 = 0`, which is the claim.

The difficulty is genuinely the last step: without `hnn` the bound fails and `D` can be a
non-zero derivation.

## Relation to the corpus

The additivity computation of Step 1 is the one already recorded (divided by `4`) as
`Work.BoseFixB2.Polar.polarForm_add`; it is reproduced here so that this module depends on
Mathlib alone.  The reduction of the target to the additive boundedness of the defect is the one
used by `Work.BoseFixB2.Recomb.jvn_polar_expansion`, whose helper
`Work.BoseFixB2.Recomb.additive_bdd_eq_smul_one` is supplied here (`additive_bdd_eq_smul_one`,
below).
-/

namespace Work.BoseFixB2.Energy

/-- **An additive map `ℝ → ℝ` bounded on a neighbourhood of `0` is `ℝ`-linear.**

`f` is `ℚ`-linear (`map_rat_smul`); the bound gives `|f s| ≤ M / n` for `|s| ≤ 1 / n`, so `f`
is continuous at `0`, hence continuous (additivity, `continuous_of_continuousAt_zero`); the
equality on the dense set `ℚ` then propagates by continuity (`DenseRange.equalizer`). -/
private theorem additive_bdd_eq_smul_one (f : ℝ → ℝ) (hadd : ∀ s t : ℝ, f (s + t) = f s + f t)
    (hbd : ∃ M : ℝ, ∀ t : ℝ, |t| ≤ 1 → |f t| ≤ M) : ∀ t : ℝ, f t = t * f 1 := by
  obtain ⟨M, hM⟩ := hbd
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [zero_add] at h
    linarith
  let F : ℝ →+ ℝ := { toFun := f, map_zero' := hf0, map_add' := hadd }
  have hFM : ∀ t : ℝ, |t| ≤ 1 → |F t| ≤ M := fun t ht => hM t ht
  -- continuity at `0`, by the scaling argument `F (n s) = n F s`
  have hcont0 : ContinuousAt F 0 := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (max (M / ε) 1)
    have h1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have h2 : M / ε < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hMlt : M < (n : ℝ) * ε := by
      rw [div_lt_iff₀ hε] at h2
      linarith
    refine ⟨1 / (n : ℝ), one_div_pos.mpr hnpos, ?_⟩
    intro y hy
    have hy' : |y| < 1 / (n : ℝ) := by simpa [Real.dist_eq] using hy
    have hny : |(n : ℝ) * y| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hnpos)]
      have h3 : (n : ℝ) * |y| < (n : ℝ) * (1 / (n : ℝ)) := mul_lt_mul_of_pos_left hy' hnpos
      rw [mul_one_div, div_self (ne_of_gt hnpos)] at h3
      linarith
    have hstep : |F y| ≤ M / (n : ℝ) := by
      have h := F.map_nsmul n y
      rw [nsmul_eq_mul, nsmul_eq_mul] at h
      have hFy : F y = F ((n : ℝ) * y) / (n : ℝ) := by
        rw [h, mul_div_cancel_left₀ _ (ne_of_gt hnpos)]
      rw [hFy, abs_div, abs_of_nonneg (le_of_lt hnpos)]
      exact div_le_div_of_nonneg_right (hFM _ hny) (le_of_lt hnpos)
    have hlt : M / (n : ℝ) < ε := by
      rw [div_lt_iff₀ hnpos]
      linarith
    rw [Real.dist_eq, map_zero, sub_zero]
    linarith
  have hcont : Continuous F := continuous_of_continuousAt_zero F hcont0
  have hkey : (F : ℝ → ℝ) = fun t => t * F 1 := by
    refine (Rat.denseRange_cast).equalizer hcont ?_ ?_
    · fun_prop
    · funext q
      have h := map_rat_smul F q (1 : ℝ)
      rw [Rat.smul_one_eq_cast, Rat.smul_def] at h
      simpa using h
  intro t
  have ht := congr_fun hkey t
  simpa [F] using ht

theorem hpol_of_par_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V] (Q : V → ℝ) (hpar : ∀ x y : V, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) (hhom : ∀ (t : ℝ) (x : V), Q (t • x) = t ^ 2 * Q x) (hnn : ∀ x : V, 0 ≤ Q x) : ∀ (t : ℝ) (x y : V), Q (t • x + y) - Q (t • x - y) = t * (Q (x + y) - Q (x - y)) := by
  intro t x y
  -- ### Step 1: the polarised difference `G u = Q (u + y) - Q (u - y)` is additive in `u`
  have hkey : ∀ a b c : V, Q (a + b + c) - Q (a + b - c)
      = (Q (a + c) - Q (a - c)) + (Q (b + c) - Q (b - c)) := by
    intro a b c
    have p1 := hpar (a + c) b
    have p2 := hpar (a - c) b
    have p3 := hpar a (b + c)
    have p4 := hpar a (b - c)
    rw [show (a + c) + b = a + b + c by abel,
        show (a + c) - b = a - b + c by abel] at p1
    rw [show (a - c) + b = a + b - c by abel,
        show (a - c) - b = a - b - c by abel] at p2
    rw [show a + (b + c) = a + b + c by abel,
        show a - (b + c) = a - b - c by abel] at p3
    rw [show a + (b - c) = a + b - c by abel,
        show a - (b - c) = a - b + c by abel] at p4
    linarith
  -- ### Step 2: the defect `F s = G (s • x) - s (Q (x+y) - Q (x-y))`
  set F : ℝ → ℝ :=
    fun s => (Q (s • x + y) - Q (s • x - y)) - s * (Q (x + y) - Q (x - y)) with hF
  have hFadd : ∀ s u : ℝ, F (s + u) = F s + F u := by
    intro s u
    have h := hkey (s • x) (u • x) y
    simp only [hF]
    rw [add_smul, h]
    ring
  -- ### Step 3: `F` is bounded on `[-1, 1]`
  have hbd : ∃ M : ℝ, ∀ s : ℝ, |s| ≤ 1 → |F s| ≤ M := by
    refine ⟨2 * Q x + 2 * Q y + |Q (x + y) - Q (x - y)|, ?_⟩
    intro s hs
    -- the parallelogram law at `(s • x, y)`, with both terms non-negative
    have hDbd : |Q (s • x + y) - Q (s • x - y)| ≤ 2 * s ^ 2 * Q x + 2 * Q y := by
      have hp := hpar (s • x) y
      rw [hhom s x] at hp
      have h1 : 0 ≤ Q (s • x + y) := hnn _
      have h2 : 0 ≤ Q (s • x - y) := hnn _
      rw [abs_le]
      constructor <;> linarith
    have hs2 : s ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one s).mpr hs
    have hQx : 0 ≤ Q x := hnn x
    have hle2 : 2 * s ^ 2 * Q x ≤ 2 * Q x := by
      have h := mul_le_mul_of_nonneg_right hs2 hQx
      linarith
    have hsplit : |F s| ≤ |Q (s • x + y) - Q (s • x - y)|
        + |s| * |Q (x + y) - Q (x - y)| := by
      simp only [hF]
      have h := abs_sub_le (Q (s • x + y) - Q (s • x - y)) 0
        (s * (Q (x + y) - Q (x - y)))
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using h
    have hle1 : |s| * |Q (x + y) - Q (x - y)| ≤ |Q (x + y) - Q (x - y)| :=
      mul_le_of_le_one_left (abs_nonneg _) hs
    linarith
  -- ### Step 4: `F 1 = 0`, and local boundedness kills `F`
  have hF1 : F 1 = 0 := by
    simp only [hF, one_smul, one_mul]
    ring
  have hmain : F t = 0 := by
    have h := additive_bdd_eq_smul_one F hFadd hbd t
    rw [hF1, mul_zero] at h
    exact h
  exact sub_eq_zero.mp (by simpa only [hF] using hmain)

end Work.BoseFixB2.Energy
