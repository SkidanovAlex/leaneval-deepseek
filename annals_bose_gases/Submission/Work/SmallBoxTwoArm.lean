import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# FS `thm:smallbox`, two-arm arithmetic (the `1/18` step)

This module machine-checks the elementary real-arithmetic core of the last
step of Fournais--Solovej `thm:smallbox`
(`final_v2.tex` ll.3965--4063, the sentence "*This easily implies the result
in the theorem*").

## FS's two-arm split

Choose an integer `n' ≥ C_n` in `[C_n μ|B|, (C_n+1)μ|B|)` and write
`n = m n' + n''` (`m, n'' ∈ ℕ`, `n'' < n'`).  The `m` groups of `n'`
particles and the single group of `n''` particles give (FS's assembled
bound)

    e_B(n,μ) ≥ ( ¼((n''/|B|) − μ)² + (1/18)μ(n − n'')/|B| )∬w_{1,B}
                 − ½μ²∬w_{1,B} − errors .

The theorem's main term is `c((n/|B|) − μ)²/(1 + n/(|B|μ))∬w_{1,B}` with
`∬w_{1,B} ≥ 8πa|B|`, so the step reduces to the pure inequality

    ¼(a − μ)² + (1/18)μ(t − a) ≥ (1/18)·(t − μ)²/(1 + t/μ)      (`two_arm_gain`)

for the *density* variables `t := n/|B| ≥ a := n''/|B| ≥ 0` in the regime
`t − a = m n'/|B| ≥ 2μ` (which holds since `n' ≥ C_n μ|B|` with `C_n ≥ 2`),
together with its boundary case `t = a` (`m = 0`, `sharp_branch_gain`).

The certificate for `two_arm_gain` is polynomial and exact: with
`A := a/μ`, `S := (t−a)/μ ≥ 2`, one has

    (9/2)(A−1)² + S − (A+S−1)²/(A+S+1) = (9/2)(A − 10/9)² + 35/18 − 4/(A+S+1),

so the difference is `≥ 35/18 − 4/3 = 11/18 > 0`: the constant `1/18` has
slack.  (FS's text uses the cruder chain `(1/9)(μ−u)² ≥ (1/18)μu`, which is
what pins the constant at `1/18`.)

`exists_two_arm_split` supplies the *choice* of `n', m, n''` (with
`n' := ⌈2μβ⌉`) and combines the two branches, so that the whole
"easily implies" step is available as a single machine-checked lemma.
-/

noncomputable section
open MeasureTheory
open scoped Real

namespace Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Normalised two-arm core** (`A ≥ 0`, `S ≥ 2`):

    (A + S − 1)²/(A + S + 1) ≤ (9/2)(A − 1)² + S .

Exact certificate: the difference equals
`(9/2)(A − 10/9)² + 35/18 − 4/(A + S + 1) ≥ 35/18 − 4/3 = 11/18 > 0`. -/
lemma two_arm_core {A S : ℝ} (hA : 0 ≤ A) (hS : 2 ≤ S) :
    (A + S - 1) ^ 2 / (A + S + 1) ≤ (9 / 2) * (A - 1) ^ 2 + S := by
  have hden : 0 < A + S + 1 := by linarith
  rw [div_le_iff₀ hden]
  have key : ((9 / 2) * (A - 1) ^ 2 + S) * (A + S + 1) - (A + S - 1) ^ 2
      = (A + S + 1) * ((9 / 2) * (A - 10 / 9) ^ 2 + 35 / 18) - 4 := by ring
  nlinarith [sq_nonneg (A - 10 / 9), key, hA, hS]

/-- **FS two-arm gain** (the `1/18` step of `thm:smallbox`): for `μ > 0`,
`0 ≤ a ≤ t` and `t − a ≥ 2μ` (the `m ≥ 1` branch, where the `n'`-groups
supply `μ(t−a)`),

    ¼(a − μ)² + (1/18)μ(t − a) ≥ (1/18)·(t − μ)²/(1 + t/μ) . -/
lemma two_arm_gain {μ t a : ℝ} (hμ : 0 < μ) (ha : 0 ≤ a) (hat : a ≤ t)
    (hs : 2 * μ ≤ t - a) :
    (1 / 18) * ((t - μ) ^ 2 / (1 + t / μ)) ≤ (1 / 4) * (a - μ) ^ 2 + (1 / 18) * μ * (t - a) := by
  have ht0 : 0 ≤ t := le_trans ha hat
  have htμ : 0 < t + μ := by linarith
  have h1 : (t - μ) ^ 2 / (1 + t / μ) = μ * (t - μ) ^ 2 / (t + μ) := by
    rw [div_eq_div_iff (by positivity) (ne_of_gt htμ)]
    field_simp
    ring
  rw [h1]
  rw [show (1 / 18 : ℝ) * (μ * (t - μ) ^ 2 / (t + μ))
        = (1 / 18 : ℝ) * μ * (t - μ) ^ 2 / (t + μ) by ring]
  rw [div_le_iff₀ htμ]
  have key : ((9 / 2) * (a - μ) ^ 2 + μ * (t - a)) * (t + μ) - μ * (t - μ) ^ 2
      = (t + μ) * ((9 / 2) * (a - 10 / 9 * μ) ^ 2 + (35 / 18) * μ ^ 2) - 4 * μ ^ 3 := by ring
  nlinarith [sq_nonneg (a - 10 / 9 * μ), key, hμ, hs, ha, hat, sq_nonneg μ,
    mul_nonneg (by linarith : (0:ℝ) ≤ t + μ) (sq_nonneg (a - 10 / 9 * μ)),
    mul_nonneg (by linarith : (0:ℝ) ≤ t + μ) (sq_nonneg μ)]

/-- **Boundary branch `m = 0`** (`t = a`, i.e. `n < n'`): the single sharp
group gives `¼(t − μ)²`, which dominates
`(1/18)(t − μ)²/(1 + t/μ)` for `t ≥ 0` since `1 + t/μ ≥ 1`. -/
lemma sharp_branch_gain {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    (1 / 18) * ((t - μ) ^ 2 / (1 + t / μ)) ≤ (1 / 4) * (t - μ) ^ 2 := by
  have h1 : 1 ≤ 1 + t / μ := by
    have : 0 ≤ t / μ := div_nonneg ht (le_of_lt hμ)
    linarith
  have h2 : 0 ≤ (t - μ) ^ 2 := sq_nonneg _
  have h3 : (t - μ) ^ 2 / (1 + t / μ) ≤ (t - μ) ^ 2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + t / μ)]
    nlinarith
  have h4 : (1 / 18 : ℝ) * (t - μ) ^ 2 ≤ (1 / 4) * (t - μ) ^ 2 := by
    nlinarith
  calc (1 / 18) * ((t - μ) ^ 2 / (1 + t / μ)) ≤ (1 / 18) * (t - μ) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
    _ ≤ (1 / 4) * (t - μ) ^ 2 := h4

/-- **FS's choice of the two-arm split**: for `μ > 0`, `β = |B| > 0` with
`1 ≤ μβ` (the small-box shortest-side hypothesis `μ|B| ≥ 1`) and every
`n : ℕ` there are `m, n', n'' ∈ ℕ` with `n = m n' + n''`, `n'' < n'`, such
that the *density-level* two-arm inequality holds:

    ¼(n''/β − μ)² + (1/18)μ(n − n'')/β ≥ (1/18)·(n/β − μ)²/(1 + n/(βμ)) .

The split is `n' := ⌈2μβ⌉`, and for `n ≥ n'` one takes the Euclidean
division `n = (n / n')·n' + n % n'`; since `n' ≥ 2μβ` the regime
`(n − n'')/β ≥ 2μ` of `two_arm_gain` holds.  For `n < n'` one takes
`m := 0`, `n'' := n` and the boundary branch `sharp_branch_gain`.

The lemma also records the two *window* facts FS's error absorption uses:
`2μβ ≤ n'` (their `n' ≥ C_nμ|B|` with `C_n := 2`, which is what makes
`(1/9)(μ−u)² ≥ (1/18)μu` at `u = n'/|B|`) and `n'' < 3μβ` (their
`n'' < (C_n+1)μ|B| ≤ 2C_nμ|B|`; note `Nat.ceil_lt_add_one` gives
`n' < 2μβ + 1 ≤ 3μβ` since `μβ ≥ 1`). -/
theorem exists_two_arm_split {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 < β) (hμβ : 1 ≤ μ * β)
    (n : ℕ) :
    ∃ m n' n'' : ℕ, n = m * n' + n'' ∧ n'' < n' ∧ 2 * μ * β ≤ (n' : ℝ) ∧ (n'' : ℝ) < 3 * μ * β ∧
      (1 / 18) * (((n : ℝ) / β - μ) ^ 2 / (1 + ((n : ℝ) / β) / μ))
        ≤ (1 / 4) * (((n'' : ℝ) / β - μ) ^ 2)
          + (1 / 18) * μ * (((n : ℝ) - (n'' : ℝ)) / β) := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hμne : μ ≠ 0 := ne_of_gt hμ
  set N : ℕ := Nat.ceil (2 * μ * β) with hNdef
  have hNge : 2 * μ * β ≤ (N : ℝ) := Nat.le_ceil _
  have hNpos : 0 < N := by
    have h : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hNge
    exact_mod_cast h
  have hN3 : (N : ℝ) < 3 * μ * β := by
    have h1 : (N : ℝ) < 2 * μ * β + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  by_cases hn : n < N
  · refine ⟨0, N, n, by simp, hn, hNge, ?_, ?_⟩
    · have hcast : (n : ℝ) < (N : ℝ) := by exact_mod_cast hn
      linarith
    have ht0 : 0 ≤ (n : ℝ) / β := by positivity
    have h := sharp_branch_gain (μ := μ) hμ ht0
    simpa using h
  · have hNle : N ≤ n := le_of_not_gt hn
    refine ⟨n / N, N, n % N, ?_, Nat.mod_lt _ hNpos, hNge, ?_, ?_⟩
    · rw [mul_comm]
      exact (Nat.div_add_mod n N).symm
    · have hcast : (((n % N : ℕ)) : ℝ) < (N : ℝ) := by
        exact_mod_cast Nat.mod_lt n hNpos
      linarith
    · rw [show ((n : ℝ) - (((n % N : ℕ)) : ℝ)) / β
            = (n : ℝ) / β - (((n % N : ℕ)) : ℝ) / β by ring]
      have hdiv1 : 1 ≤ n / N := (Nat.one_le_div_iff hNpos).mpr hNle
      have hNge2 : 2 * μ ≤ (N : ℝ) / β := by
        rw [le_div_iff₀ hβ]
        exact hNge
      have hcast : ((n : ℝ) - ((n % N : ℕ) : ℝ)) = ((n / N : ℕ) : ℝ) * (N : ℝ) := by
        have hnn : n - n % N = n / N * N := by
          have h := Nat.sub_eq_of_eq_add (Nat.div_add_mod n N).symm
          rwa [mul_comm] at h
        rw [← Nat.cast_sub (Nat.mod_le n N), hnn]
        push_cast
        ring
      have hs : 2 * μ ≤ (n : ℝ) / β - ((n % N : ℕ) : ℝ) / β := by
        have hs0 : 2 * μ ≤ ((n : ℝ) - ((n % N : ℕ) : ℝ)) / β := by
          rw [hcast]
          have h1 : (1 : ℝ) ≤ ((n / N : ℕ) : ℝ) := by exact_mod_cast hdiv1
          have h2 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
          calc 2 * μ ≤ (N : ℝ) / β := hNge2
            _ = 1 * ((N : ℝ) / β) := by ring
            _ ≤ ((n / N : ℕ) : ℝ) * ((N : ℝ) / β) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = ((n / N : ℕ) : ℝ) * (N : ℝ) / β := by ring
        rwa [show ((n : ℝ) - ((n % N : ℕ) : ℝ)) / β
              = (n : ℝ) / β - (((n % N : ℕ)) : ℝ) / β by ring] at hs0
      have ha0 : 0 ≤ ((n % N : ℕ) : ℝ) / β := by positivity
      have hat : ((n % N : ℕ) : ℝ) / β ≤ (n : ℝ) / β := by
        have h1 : ((n % N : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.mod_le n N
        exact div_le_div_of_nonneg_right h1 (le_of_lt hβ)
      exact two_arm_gain (μ := μ) (t := (n : ℝ) / β) (a := ((n % N : ℕ) : ℝ) / β)
        hμ ha0 hat hs

/-- **FS error absorption, the pure arithmetic** (`final_v2.tex` l.3993: the
errors "*can be absorbed in the positive term ... if we choose `C' ≥ CC_n`*"):
for every `C ≥ 0` and `μ > 0` there is a universal `Cn ≥ 2` such that on the
`n'`-window `Cn·μ ≤ u < (Cn+1)·μ` the per-`n'`-group error `C·μ·u` is
dominated by the `∬w₁`-positive term `(8π/9)(μ−u)²` (i.e. by `(1/9)(μ−u)²`
times the `8πa|B|` value of `∬w₁`, with `∫χ_B² = |B|` cancelling the `a|B|`
factors).  Explicit witness `Cn := max 2 (1 + 2C)`: with
`t := Cn − 1 ≥ max 1 (2C)` one has `u − μ ≥ tμ` (so `(μ−u)² ≥ t²μ²`) and
`u < (t+2)μ`, whence `Cμu ≤ C(t+2)μ² ≤ 2t²μ² ≤ (8π/9)t²μ² ≤ (8π/9)(μ−u)²`. -/
lemma two_arm_error_absorption {C μ : ℝ} (hC : 0 ≤ C) (hμ : 0 < μ) :
    ∃ Cn : ℝ, 2 ≤ Cn ∧ ∀ u : ℝ, Cn * μ ≤ u → u < (Cn + 1) * μ →
      C * μ * u ≤ (8 * π / 9) * (μ - u) ^ 2 := by
  refine ⟨max 2 (1 + 2 * C), le_max_left _ _, ?_⟩
  intro u hu1 hu2
  set t : ℝ := max 2 (1 + 2 * C) - 1 with htdef
  have ht1 : 1 ≤ t := by rw [htdef]; linarith [le_max_left (2 : ℝ) (1 + 2 * C)]
  have htC : 2 * C ≤ t := by rw [htdef]; linarith [le_max_right (2 : ℝ) (1 + 2 * C)]
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hmax_eq : max 2 (1 + 2 * C) = t + 1 := by rw [htdef]; ring
  have hu_ge : t * μ ≤ u - μ := by
    rw [hmax_eq] at hu1
    linarith
  have hsq : t ^ 2 * μ ^ 2 ≤ (μ - u) ^ 2 := by
    have h2 : (t * μ) ^ 2 ≤ (u - μ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hu_ge 2
    have h3 : (u - μ) ^ 2 = (μ - u) ^ 2 := by ring
    linarith [h2, h3]
  have hu_le : u ≤ (t + 2) * μ := by
    rw [hmax_eq] at hu2
    linarith
  have hkey : C * (t + 2) ≤ 2 * t ^ 2 := by
    have hCt : C * t ≤ t ^ 2 / 2 := by
      have h' : C * t ≤ (t / 2) * t :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt htpos)
      nlinarith [h']
    have ht_le : t ≤ t ^ 2 := by nlinarith [ht1]
    nlinarith [hCt, htC, ht_le, sq_nonneg t]
  have h2pi : (2 : ℝ) ≤ 8 * π / 9 := by nlinarith [Real.pi_gt_three]
  have hCμ2 : C * μ * u ≤ C * (t + 2) * μ ^ 2 := by
    have h1 : C * μ * u ≤ C * μ * ((t + 2) * μ) :=
      mul_le_mul_of_nonneg_left hu_le (by positivity)
    calc C * μ * u ≤ C * μ * ((t + 2) * μ) := h1
      _ = C * (t + 2) * μ ^ 2 := by ring
  have hstep : C * (t + 2) * μ ^ 2 ≤ (8 * π / 9) * (t ^ 2 * μ ^ 2) := by
    have hm2 : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
    have hA : C * (t + 2) * μ ^ 2 ≤ 2 * (t ^ 2 * μ ^ 2) := by nlinarith [hkey, hm2]
    have hB : 2 * (t ^ 2 * μ ^ 2) ≤ (8 * π / 9) * (t ^ 2 * μ ^ 2) := by
      have hnn : (0 : ℝ) ≤ t ^ 2 * μ ^ 2 := by positivity
      nlinarith [h2pi, hnn]
    linarith [hA, hB]
  have h8 : (0 : ℝ) ≤ 8 * π / 9 := by nlinarith [Real.pi_gt_three]
  calc C * μ * u ≤ C * (t + 2) * μ ^ 2 := hCμ2
    _ ≤ (8 * π / 9) * (t ^ 2 * μ ^ 2) := hstep
    _ ≤ (8 * π / 9) * (μ - u) ^ 2 := mul_le_mul_of_nonneg_left hsq h8

/-- **FS's per-group weakening** (`final_v2.tex` l.4000: "*`e_B(n',μ) ≥
(1/9)(μ − n'/|B|)²∬w₁ ≥ (1/18)μ(n'/|B|)∬w₁`*"): for `μ > 0` and
`u = n'/|B| ≥ 2μ` (the window `n' ≥ C_nμ|B|`, `C_n ≥ 2`),

    (1/18)·μ·u ≤ (1/9)(μ − u)² .

Indeed `(μ−u)² = (u−μ)² ≥ μ²` for `u ≥ 2μ`, while `μu ≤ 2μ²`. -/
lemma two_arm_group_bound {μ u : ℝ} (hμ : 0 < μ) (hu : 2 * μ ≤ u) :
    (1 / 18) * μ * u ≤ (1 / 9) * (μ - u) ^ 2 := by
  have hfac : 2 * (μ - u) ^ 2 - μ * u = (2 * u - μ) * (u - 2 * μ) := by ring
  have h1 : 0 ≤ 2 * u - μ := by linarith
  have h2 : 0 ≤ u - 2 * μ := by linarith
  have h3 : 0 ≤ 2 * (μ - u) ^ 2 - μ * u := by
    rw [hfac]
    exact mul_nonneg h1 h2
  linarith [h3]

/-- **FS `thm:smallbox`, the final reduction, packaged** ("*This easily
implies the result in the theorem*"): given the two-arm assembled bound for a
normalised state,

    (¼(a−μ)² + (1/18)μ(t−a))·w₁ − ½μ²·w₁ − E ≤ eB ,

with `w₁ := ∬w_{1,B} ≥ 0` (`t = n/|B|`, `a = n''/|B|`, `2μ ≤ t−a`), and any
error `E' ≥ E`, the theorem's main term follows:

    ((1/18)·(t−μ)²/(1+t/μ) − ½μ²)·w₁ − E' ≤ eB .

(The `1/18` in the main term is the FS constant; see
`two_arm_error_absorption` for why larger `c` is not available from FS's
weak per-group chain, and the note in the module header about the
`c < 1/2`-quantification of `SmallBoxDLBound.smallbox_dl_energy_bound`.) -/
theorem two_arm_assembled_bound {μ t a w1 E E' eBval : ℝ}
    (hμ : 0 < μ) (ha : 0 ≤ a) (hat : a ≤ t) (hs : 2 * μ ≤ t - a)
    (hw1 : 0 ≤ w1) (hE : E ≤ E')
    (hbound : (1 / 4) * (a - μ) ^ 2 * w1 + (1 / 18) * μ * (t - a) * w1
        - (1 / 2) * μ ^ 2 * w1 - E ≤ eBval) :
    ((1 / 18) * ((t - μ) ^ 2 / (1 + t / μ)) - (1 / 2) * μ ^ 2) * w1 - E' ≤ eBval := by
  have hg := two_arm_gain hμ ha hat hs
  have h1 : (1 / 18) * ((t - μ) ^ 2 / (1 + t / μ)) * w1
      ≤ ((1 / 4) * (a - μ) ^ 2 + (1 / 18) * μ * (t - a)) * w1 :=
    mul_le_mul_of_nonneg_right hg hw1
  nlinarith [hbound, h1, hE]

/-- **FS `thm:smallbox`, the assembly of the two-arm chain**: this isolates
EXACTLY the obligation the D1 (Bogolubov) layer must supply.

Assume that for EVERY FS-admissible split `N = m·n' + n''` (with
`n'' < n'`, `2μβ ≤ n'`, `n'' < 3μβ`) the two per-group bounds hold in
assembled form,

    (m : ℝ)·((1/9)(μ − n'/β)²·w₁) + (¼(n''/β − μ)²·w₁ − ½μ²·w₁ − E) ≤ eB

(`(1/9)(μ − n'/β)²∬w₁` for the `m` groups of `n'` particles, the sharp
`¼(n''/β − μ)²∬w₁ − ½μ²∬w₁` for the `n''` group, both multiplied by the
`∬w₁`-value `w₁ ≥ 0`; `eB` the ground energy).  Then FS's final bound holds:

    ((1/18)·(N/β − μ)²/(1 + N/(βμ)) − ½μ²)·w₁ − E ≤ eB .

Proof: take the split `exists_two_arm_split`; if `m = 0` then `n'' = N` and
`sharp_branch_gain` finishes; otherwise `t − a = m·(n'/β) ≥ n'/β ≥ 2μ` and
`two_arm_group_bound` weakens `(m)·(1/9)(μ − u)²` to `(1/18)μ·m·u =
(1/18)μ(t−a)`, after which `two_arm_assembled_bound` (i.e. `two_arm_gain`)
finishes. -/
theorem smallbox_two_arm_assembly {μ β w1 E eB : ℝ} (hμ : 0 < μ) (hβ : 0 < β)
    (hμβ : 1 ≤ μ * β) (hw1 : 0 ≤ w1) (N : ℕ)
    (hgroup : ∀ m n' n'' : ℕ, N = m * n' + n'' → n'' < n' → 2 * μ * β ≤ (n' : ℝ) →
      (n'' : ℝ) < 3 * μ * β →
      (m : ℝ) * ((1 / 9) * (μ - (n' : ℝ) / β) ^ 2 * w1)
        + ((1 / 4) * ((n'' : ℝ) / β - μ) ^ 2 * w1 - (1 / 2) * μ ^ 2 * w1 - E) ≤ eB) :
    ((1 / 18) * (((N : ℝ) / β - μ) ^ 2 / (1 + ((N : ℝ) / β) / μ)) - (1 / 2) * μ ^ 2) * w1
      - E ≤ eB := by
  obtain ⟨m, n', n'', hN, hlt, hwin, hwin2, _hsplit⟩ := exists_two_arm_split hμ hβ hμβ N
  have hcastN : (N : ℝ) = (m : ℝ) * (n' : ℝ) + (n'' : ℝ) := by
    rw [hN]; push_cast; ring
  have hnn : (n'' : ℝ) ≤ (N : ℝ) := by
    have h : n'' ≤ N := by omega
    exact_mod_cast h
  have ha0 : 0 ≤ (n'' : ℝ) / β := by positivity
  have hat : (n'' : ℝ) / β ≤ (N : ℝ) / β :=
    div_le_div_of_nonneg_right hnn (le_of_lt hβ)
  have hdiff : (N : ℝ) / β - (n'' : ℝ) / β = (m : ℝ) * ((n' : ℝ) / β) := by
    rw [← sub_div, hcastN]
    ring
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- the `m = 0` branch: `n'' = N`, and the single sharp group gives the result
    have hgrp := hgroup m n' n'' hN hlt hwin hwin2
    rw [hm] at hgrp hcastN
    simp only [Nat.cast_zero, zero_mul, zero_add] at hgrp hcastN
    have hsub : (n'' : ℝ) / β = (N : ℝ) / β := by rw [← hcastN]
    rw [hsub] at hgrp
    have ht0 : 0 ≤ (N : ℝ) / β := by positivity
    have hsharp := sharp_branch_gain (μ := μ) (t := (N : ℝ) / β) hμ ht0
    have hmul : (1 / 18) * (((N : ℝ) / β - μ) ^ 2 / (1 + ((N : ℝ) / β) / μ)) * w1
        ≤ (1 / 4) * ((N : ℝ) / β - μ) ^ 2 * w1 :=
      mul_le_mul_of_nonneg_right hsharp hw1
    linarith [hgrp, hmul]
  · -- the `m ≥ 1` branch: the `n'`-groups supply `μ(t − a)`
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hu2 : 2 * μ ≤ (n' : ℝ) / β := by
      rw [le_div_iff₀ hβ]
      linarith [hwin]
    have hs : 2 * μ ≤ (N : ℝ) / β - (n'' : ℝ) / β := by
      rw [hdiff]
      calc 2 * μ ≤ (n' : ℝ) / β := hu2
        _ = 1 * ((n' : ℝ) / β) := by ring
        _ ≤ (m : ℝ) * ((n' : ℝ) / β) :=
              mul_le_mul_of_nonneg_right hm1 (by positivity)
    have hgrp := hgroup m n' n'' hN hlt hwin hwin2
    have hgb := two_arm_group_bound hμ hu2
    have hmul : (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / β) * w1)
        ≤ (m : ℝ) * ((1 / 9) * (μ - (n' : ℝ) / β) ^ 2 * w1) := by
      have h2 : (1 / 18) * μ * ((n' : ℝ) / β) * w1
          ≤ (1 / 9) * (μ - (n' : ℝ) / β) ^ 2 * w1 :=
        mul_le_mul_of_nonneg_right hgb hw1
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have hcancel : (1 / 18) * μ * ((N : ℝ) / β - (n'' : ℝ) / β) * w1
        = (m : ℝ) * ((1 / 18) * μ * ((n' : ℝ) / β) * w1) := by
      rw [hdiff]
      ring
    have hbound : (1 / 4) * ((n'' : ℝ) / β - μ) ^ 2 * w1
        + (1 / 18) * μ * ((N : ℝ) / β - (n'' : ℝ) / β) * w1
        - (1 / 2) * μ ^ 2 * w1 - E ≤ eB := by
      rw [hcancel]
      linarith [hgrp, hmul]
    exact two_arm_assembled_bound (μ := μ) (t := (N : ℝ) / β)
      (a := (n'' : ℝ) / β) (w1 := w1) (E := E) (E' := E)
      (eBval := eB) hμ ha0 hat hs hw1 le_rfl hbound

end Submission.BoseGases
