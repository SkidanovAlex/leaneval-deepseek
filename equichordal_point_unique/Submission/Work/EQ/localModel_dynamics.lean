import Mathlib
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.LocalModelAux
import Submission.Work.EQ.dyn_geom_bounds
import Submission.Work.EQ.localModel_limit

set_option linter.unusedVariables false

/-!
# The local dynamics of `LocalModel`

The requested statement is

```
LocalModel T A lam C ε → ε ≤ (1 - lam)/4 → (trap) ∧ (limit exists on the real axis) ∧ (uniqueness)
```

where the conjuncts say that for every `P` with `‖P - A‖ ≤ ε`

1. `‖(T^[n]) P - A‖ ≤ 2 ε` for all `n` (the ball is trapped, up to the factor `2`);
2. the orbit of `P` converges to a point `Q` of the real axis with `‖Q - A‖ ≤ 2 ε`;
3. two points `P`, `P'` of the ball with the same imaginary part whose orbits both converge
   to `A` must be equal.

**The third conjunct needs the second hypothesis `ε ≤ (1 - lam)/4`.**  Without it the statement
is *false*: `LocalModel` alone bounds the vertical multiplier `G` only by
`lam + 2 C ε = (1 + lam)/2 ≤ 1` on the ball and puts no ceiling on `C η²`, so the horizontal map
`ξ ↦ ξ + F(ξ,η)` may fold, and a single fold produces two distinct points with the same imaginary
part whose orbits coincide from the next step on.  The machine-checked counterexample
`LocalModelCtr.localModel_dynamics_counterexample` (section below) exhibits exactly this: with
`A = 0`, `lam = 1/2`, `C = 1/80`, `ε = 10` the points `9 i` and `81/80 + 9 i` both lie in the
ball, have the same imaginary part, and both orbits converge to `A`, while the first step folds
`81/80` onto `0` because `C η² = 81/80 > 1`.

With the extra hypothesis `ε ≤ (1 - lam)/4`, both `ε` and `C ε` are at most `(1 - lam)/4`, so
`C η² ≤ C ε² ≤ (1 - lam)²/16` is *small*: the horizontal map becomes strictly increasing and
the third conjunct holds.  All three conjuncts are proved for the statement as requested
(`localModel_dynamics` at the end of this file), with the pieces:

* `Work.EQ.dynTrap` (`Submission/Work/EQ/LocalModelAux.lean`): trap and geometric decay of `η`;
* `Work.EQ.localModel_limit` (`Submission/Work/EQ/localModel_limit.lean`, by a colleague):
  the limit on the real axis;
* `Work.EQ.dyn_expand` + `Work.EQ.localModel_unique` (below): uniqueness;
* `Work.EQ.dyn_geom_bounds` (`Submission/Work/EQ/dyn_geom_bounds.lean`, by a colleague): the
  numeric/geometric-series estimates used by the uniqueness argument.

The uniqueness argument in one line: with `μ = (1 + lam)/2`, `|η_n| ≤ μ^n ε` and the differences
`d_n = ξ'_n - ξ_n`, `e_n = η'_n - η_n` of two orbits with the same initial imaginary part satisfy
`|e_n| ≤ 4 C ε d_0 n μ^{n-1}` and

`d_{n+1} = d_n + F(ξ'_n,η'_n) - F(ξ_n,η_n)`, with
`|F(ξ'_n,η'_n) - F(ξ_n,η_n)| ≤ C ε² μ^{2n} |d_n| + C(|η_n| + |η'_n|) |e_n|`;

summing over a whole orbit gives `|d_n - d_0| ≤ (3/4) d_0`, so `d_n ≥ d_0/4 > 0` for every `n`.
If both orbits converge to `A` then `d_n → 0`, which forces `d_0 = 0`.
-/

namespace Work.EQ
namespace LocalModelCtr

open Complex Filter Topology

noncomputable section

/-- `x ↦ -clamp (x, -1, 1)`: 1-Lipschitz, `|φ| ≤ 1`, `φ 0 = 0`, `φ 1 = -1`. -/
def cePhi (x : ℝ) : ℝ := -(max (-1) (min x 1))

lemma cePhi_zero : cePhi 0 = 0 := by simp [cePhi]

lemma cePhi_one : cePhi 1 = -1 := by simp [cePhi]

lemma cePhi_of_one_le {x : ℝ} (hx : 1 ≤ x) : cePhi x = -1 := by
  rw [cePhi, min_eq_right hx, max_eq_right (by norm_num)]

lemma cePhi_abs_le_one (x : ℝ) : |cePhi x| ≤ 1 := by
  rw [cePhi, abs_neg]
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

lemma cePhi_lipschitz (x y : ℝ) : |cePhi x - cePhi y| ≤ |x - y| := by
  have heq : cePhi x - cePhi y = -(max (-1) (min x 1) - max (-1) (min y 1)) := by
    rw [cePhi, cePhi]; ring
  rw [heq, abs_neg]
  calc |max (-1) (min x 1) - max (-1) (min y 1)|
      ≤ max |(-1 : ℝ) - (-1)| |min x 1 - min y 1| := abs_max_sub_max_le_max _ _ _ _
    _ = |min x 1 - min y 1| := by
        rw [show |(-1 : ℝ) - (-1)| = 0 by norm_num, max_eq_right (abs_nonneg _)]
    _ ≤ max |x - y| |(1 : ℝ) - 1| := abs_min_sub_min_le_max _ _ _ _
    _ = |x - y| := by
        rw [show |(1 : ℝ) - 1| = 0 by norm_num, max_eq_left (abs_nonneg _)]

/-- Horizontal displacement of the counterexample model. -/
def ceF (ξ η : ℝ) : ℝ := (1 / 80) * η ^ 2 * cePhi ξ

/-- Vertical multiplier of the counterexample model. -/
def ceG (_ξ _η : ℝ) : ℝ := 1 / 2

/-- The counterexample map: the skew product `(ξ,η) ↦ (ξ + ceF ξ η, η · ceG ξ η)` on the box
`|ξ|, |η| ≤ 40`, and the identity outside it (where the model makes no requirement). -/
def ceT (P : ℂ) : ℂ :=
  if |P.re| ≤ 40 ∧ |P.im| ≤ 40 then
    ((P.re + ceF P.re P.im : ℝ) : ℂ) + ((P.im * ceG P.re P.im : ℝ) : ℂ) * I
  else P

lemma ceT_repr (ξ η : ℝ) (hξ : |ξ| ≤ 40) (hη : |η| ≤ 40) :
    ceT ((ξ : ℂ) + (η : ℂ) * I) =
      ((ξ + ceF ξ η : ℝ) : ℂ) + ((η * ceG ξ η : ℝ) : ℂ) * I := by
  have hre : ((ξ : ℂ) + (η : ℂ) * I).re = ξ := by simp
  have him : ((ξ : ℂ) + (η : ℂ) * I).im = η := by simp
  rw [ceT, hre, him, ite_eq_left ⟨hξ, hη⟩]

lemma ceF_abs_le (ξ η : ℝ) : |ceF ξ η| ≤ (1 / 80) * η ^ 2 := by
  have h := cePhi_abs_le_one ξ
  rw [ceF, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 80),
    abs_of_nonneg (sq_nonneg η)]
  nlinarith [abs_nonneg (cePhi ξ)]

lemma ceF_lipschitz (ξ η ξ' η' : ℝ) :
    |ceF ξ η - ceF ξ' η'| ≤ (1 / 80) * (η ^ 2 * |ξ - ξ'| + (|η| + |η'|) * |η - η'|) := by
  have hlip := cePhi_lipschitz ξ ξ'
  have hb := cePhi_abs_le_one ξ'
  have hkey : ceF ξ η - ceF ξ' η' =
      (1 / 80) * (η ^ 2 * (cePhi ξ - cePhi ξ') + (η ^ 2 - η' ^ 2) * cePhi ξ') := by
    rw [ceF, ceF]; ring
  have h1 : |η ^ 2 * (cePhi ξ - cePhi ξ')| ≤ η ^ 2 * |ξ - ξ'| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul_of_nonneg_left hlip (sq_nonneg η)
  have h2 : |(η ^ 2 - η' ^ 2) * cePhi ξ'| ≤ (|η| + |η'|) * |η - η'| := by
    have hdiff : |η ^ 2 - η' ^ 2| = |η - η'| * |η + η'| := by
      rw [show η ^ 2 - η' ^ 2 = (η - η') * (η + η') by ring, abs_mul]
    rw [abs_mul, hdiff]
    have h3 : |η + η'| ≤ |η| + |η'| := abs_add_le η η'
    have h6 : |η + η'| * |cePhi ξ'| ≤ |η| + |η'| := by
      calc |η + η'| * |cePhi ξ'| ≤ (|η| + |η'|) * 1 :=
            mul_le_mul h3 hb (abs_nonneg _) (by positivity)
        _ = |η| + |η'| := by ring
    calc |η - η'| * |η + η'| * |cePhi ξ'| = |η - η'| * (|η + η'| * |cePhi ξ'|) := by ring
      _ ≤ |η - η'| * (|η| + |η'|) := mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
      _ = (|η| + |η'|) * |η - η'| := by ring
  rw [hkey, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 80)]
  calc (1 / 80) * |η ^ 2 * (cePhi ξ - cePhi ξ') + (η ^ 2 - η' ^ 2) * cePhi ξ'|
      ≤ (1 / 80) * (|η ^ 2 * (cePhi ξ - cePhi ξ')| + |(η ^ 2 - η' ^ 2) * cePhi ξ'|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 80) * (η ^ 2 * |ξ - ξ'| + (|η| + |η'|) * |η - η'|) := by
        exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)

lemma ceG_bound (ξ η : ℝ) : |ceG ξ η - 1 / 2| ≤ (1 / 80) * (|ξ| + |η|) := by
  simp only [ceG]
  rw [sub_self, abs_zero]
  positivity

lemma ceG_lipschitz (ξ η ξ' η' : ℝ) :
    |ceG ξ η - ceG ξ' η'| ≤ (1 / 80) * (|ξ - ξ'| + |η - η'|) := by
  simp only [ceG]
  rw [sub_self, abs_zero]
  positivity

/-- **The counterexample is a `LocalModel`**: `A = 0`, `lam = 1/2`, `C = 1/80`, `ε = 10`, with
`C ε = 1/8 = (1 - lam)/4`. -/
theorem ceT_localModel : LocalModel ceT 0 (1 / 2) (1 / 80) 10 := by
  refine ⟨by simp, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_,
    ceF, ceG, ?_, ?_, ?_, ?_, ?_⟩
  · -- `ceT` fixes the real axis
    intro ξ hξ
    have hξ' : |ξ| ≤ 40 := by norm_num at hξ ⊢; exact hξ
    have h1 : (0 : ℂ) + (ξ : ℂ) = (ξ : ℂ) + ((0 : ℝ) : ℂ) * I := by simp
    rw [h1, ceT_repr ξ 0 hξ' (by norm_num)]
    simp [ceF]
  · -- the `F`-`G` representation of `ceT`
    intro ξ η hξ hη
    have hξ' : |ξ| ≤ 40 := by norm_num at hξ ⊢; exact hξ
    have hη' : |η| ≤ 40 := by norm_num at hη ⊢; exact hη
    have h1 : (0 : ℂ) + (ξ : ℂ) + (η : ℂ) * I = (ξ : ℂ) + (η : ℂ) * I := by ring
    rw [h1, ceT_repr ξ η hξ' hη']
    ring
  · intro ξ η _ _; exact ceF_abs_le ξ η
  · intro ξ η _ _; exact ceG_bound ξ η
  · intro ξ η ξ' η' _ _ _ _; exact ceF_lipschitz ξ η ξ' η'
  · intro ξ η ξ' η' _ _ _ _; exact ceG_lipschitz ξ η ξ' η'

/-- One step of `ceT` on the imaginary axis: the vertical coordinate is halved and, because
`ceF 0 η = 0`, the horizontal coordinate stays `0`. -/
lemma ceT_axis {η : ℝ} (hη : |η| ≤ 40) : ceT ((η : ℂ) * I) = ((η / 2 : ℝ) : ℂ) * I := by
  have h1 : (η : ℂ) * I = ((0 : ℝ) : ℂ) + (η : ℂ) * I := by simp
  rw [h1, ceT_repr 0 η (by norm_num) hη]
  have hF : ceF 0 η = 0 := by simp [ceF, cePhi]
  have hG : (η : ℝ) * ceG 0 η = η / 2 := by rw [ceG]; ring
  rw [hF, hG]
  simp

/-- The `n`-th iterate of `ceT` on the imaginary axis. -/
lemma ceT_iter_axis (η : ℝ) (hη : |η| ≤ 40) (n : ℕ) :
    (ceT^[n]) ((η : ℂ) * I) = ((η / 2 ^ n : ℝ) : ℂ) * I := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ceT_axis (η := η / 2 ^ n) ?_]
      · congr 1
        rw [div_div, pow_succ]
      · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
        have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        nlinarith [abs_nonneg η]

/-- The `ceT`-orbit of a point of the imaginary axis converges to `A = 0`. -/
lemma ceT_tendsto_axis (η : ℝ) (hη : |η| ≤ 40) :
    Tendsto (fun n : ℕ => (ceT^[n]) ((η : ℂ) * I)) atTop (nhds 0) := by
  have hiter : (fun n : ℕ => (ceT^[n]) ((η : ℂ) * I)) =
      fun n : ℕ => ((η / 2 ^ n : ℝ) : ℂ) * I := by
    funext n
    exact ceT_iter_axis η hη n
  rw [hiter, tendsto_zero_iff_norm_tendsto_zero]
  have hreal : Tendsto (fun n : ℕ => |η| / 2 ^ n) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 := h1.const_mul |η|
    simpa [div_eq_mul_inv, inv_pow] using h2
  have hnorm : (fun n : ℕ => ‖((η / 2 ^ n : ℝ) : ℂ) * I‖) = fun n : ℕ => |η| / 2 ^ n := by
    funext n; simp
  rw [hnorm]
  exact hreal

/-- **Counterexample.**  There are `T`, `A`, `lam`, `C`, `ε` with `LocalModel T A lam C ε` for
which the third conjunct of `localModel_dynamics` fails. -/
theorem localModel_dynamics_counterexample :
    ∃ (T : ℂ → ℂ) (A : ℂ) (lam C ε : ℝ), LocalModel T A lam C ε ∧
      ¬ (∀ P P' : ℂ, ‖P - A‖ ≤ ε → ‖P' - A‖ ≤ ε → P.im = P'.im →
        Tendsto (fun n : ℕ => (T^[n]) P) atTop (nhds A) →
        Tendsto (fun n : ℕ => (T^[n]) P') atTop (nhds A) → P = P') := by
  refine ⟨ceT, 0, 1 / 2, 1 / 80, 10, ceT_localModel, ?_⟩
  intro h
  set P : ℂ := ((9 : ℝ) : ℂ) * I with hP
  set P' : ℂ := ((81 / 80 : ℝ) : ℂ) + ((9 : ℝ) : ℂ) * I with hP'
  have hPnorm : ‖P - (0 : ℂ)‖ ≤ (10 : ℝ) := by
    rw [hP, sub_zero]; simp; norm_num
  have hP'norm : ‖P' - (0 : ℂ)‖ ≤ (10 : ℝ) := by
    have hsq : ‖((81 / 80 : ℝ) : ℂ) + ((9 : ℝ) : ℂ) * I - (0 : ℂ)‖ ^ 2 ≤ (10 : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
      norm_num
    rw [hP']
    nlinarith [norm_nonneg (((81 / 80 : ℝ) : ℂ) + ((9 : ℝ) : ℂ) * I - (0 : ℂ))]
  have him : P.im = P'.im := by
    rw [hP, hP']; simp
  have htendP : Tendsto (fun n : ℕ => (ceT^[n]) P) atTop (nhds (0 : ℂ)) := by
    rw [hP]
    exact ceT_tendsto_axis 9 (by norm_num)
  have hTP' : ceT (((81 / 80 : ℝ) : ℂ) + ((9 : ℝ) : ℂ) * I) = ceT (((9 : ℝ) : ℂ) * I) := by
    rw [ceT_repr (81 / 80) 9 (by norm_num) (by norm_num)]
    have hξ : (81 / 80 : ℝ) + ceF (81 / 80) 9 = 0 := by
      rw [ceF, cePhi_of_one_le (by norm_num : (1 : ℝ) ≤ 81 / 80)]; norm_num
    have hη : (9 : ℝ) * ceG (81 / 80) 9 = 9 / 2 := by
      rw [ceG]; norm_num
    rw [hξ, hη, ceT_axis (η := 9) (by norm_num)]
    simp
  have htendP' : Tendsto (fun n : ℕ => (ceT^[n]) P') atTop (nhds (0 : ℂ)) := by
    have hshift : Tendsto (fun n : ℕ => (ceT^[n + 1]) P') atTop (nhds (0 : ℂ)) := by
      have heq : (fun n : ℕ => (ceT^[n + 1]) P') = fun n : ℕ => (ceT^[n]) (ceT P') := by
        funext n; rw [Function.iterate_succ_apply]
      rw [heq, hP', hTP', ceT_axis (η := 9) (by norm_num)]
      exact ceT_tendsto_axis (9 / 2) (by norm_num)
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun n : ℕ => (ceT^[n]) P') (l := nhds (0 : ℂ))
      1).mp hshift
  have hne : P ≠ P' := by
    intro heq
    have hre := congrArg Complex.re heq
    rw [hP, hP'] at hre
    simp at hre
    norm_num at hre
  exact hne (h P P' hPnorm hP'norm him htendP htendP')

end

end LocalModelCtr

/-! ## Dynamics of a local model

With the extra hypothesis `ε ≤ (1 - lam)/4` (so that `ε` *and* `C ε` are both at most half of
`1 - (1+lam)/2`) the third conjunct *does* hold, and we prove all three conjuncts below.

Write `μ = (1 + lam)/2` and let `ξ_n, η_n` (resp. `ξ'_n, η'_n`) be the coordinates of `T^[n] P`
(resp. `T^[n] P'`) relative to `A`.  Then `|η_n| ≤ μ^n ε`, and for two points with the same
imaginary part the differences `d_n = ξ'_n - ξ_n`, `e_n = η'_n - η_n` satisfy

* `e_{n+1} = e_n G(ξ'_n,η'_n) + η_n (G(ξ'_n,η'_n) - G(ξ_n,η_n))`, so `|e_n| ≤ 4 C ε d_0 n μ^{n-1}`;
* `d_{n+1} = d_n + F(ξ'_n,η'_n) - F(ξ_n,η_n)`, where the correction is at most
  `C ε² μ^{2n} |d_n| + C(|η_n| + |η'_n|)|e_n|`.

Summing the second estimate over a whole orbit gives `|d_n - d_0| ≤ (3/4) d_0`, hence
`d_n ≥ d_0/4 > 0` for all `n`: the horizontal difference can never vanish.  If both orbits
converge to `A` then `d_n → 0`, a contradiction. -/

/-- Difference of the `ξ`-coordinates of the orbits of `P` and `P'`. -/
def dynD (T : ℂ → ℂ) (A P P' : ℂ) (n : ℕ) : ℝ :=
  dynXi A ((T^[n]) P') - dynXi A ((T^[n]) P)

/-- Difference of the `η`-coordinates of the orbits of `P` and `P'`. -/
def dynE (T : ℂ → ℂ) (A P P' : ℂ) (n : ℕ) : ℝ :=
  dynEta A ((T^[n]) P') - dynEta A ((T^[n]) P)

lemma key_pow_mul {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    (k : ℝ) * μ ^ (k - 1) * μ = (k : ℝ) * μ ^ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Nat.succ_sub_one, pow_succ]; ring

lemma key_pow {μ : ℝ} (hμ : 0 < μ) (k : ℕ) :
    (k : ℝ) * μ ^ k * μ ^ (k - 1) = (k : ℝ) * μ ^ (2 * k - 1) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; norm_num
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have e2 : 2 * j.succ - 1 = j.succ + j := by omega
    rw [Nat.succ_sub_one, e2, pow_add]
    ring

lemma arith_e {C ε D μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    4 * C * ε * D * ((n : ℝ) * μ ^ (n - 1)) * μ + (ε * μ ^ n) * (C * (2 * D + 2 * D)) =
      4 * C * ε * D * (((n : ℝ) + 1) * μ ^ n) := by
  have h1 : (n : ℝ) * μ ^ (n - 1) * μ = (n : ℝ) * μ ^ n := key_pow_mul hμ n
  calc 4 * C * ε * D * ((n : ℝ) * μ ^ (n - 1)) * μ + (ε * μ ^ n) * (C * (2 * D + 2 * D))
      = 4 * C * ε * D * ((n : ℝ) * μ ^ (n - 1) * μ) + (ε * μ ^ n) * (C * (2 * D + 2 * D)) := by
        ring
    _ = 4 * C * ε * D * ((n : ℝ) * μ ^ n) + (ε * μ ^ n) * (C * (2 * D + 2 * D)) := by rw [h1]
    _ = 4 * C * ε * D * (((n : ℝ) + 1) * μ ^ n) := by ring

/-- **Comparison of two orbits.**  If two points of the ball have the same imaginary part, and the
`ξ`-coordinate of `P'` is *larger* than that of `P`, then the horizontal difference
`d_n = ξ'_n - ξ_n` stays bounded below by `d_0/4 > 0` along the orbits, so it cannot tend to `0`.
Hence both orbits cannot converge to `A`.  This is the third conjunct. -/
lemma dyn_expand {T : ℂ → ℂ} {A : ℂ} {lam C ε : ℝ} (h : LocalModel T A lam C ε)
    (hε : ε ≤ (1 - lam) / 4)
    (hμ0 : 0 < (1 + lam) / 2) (hμ1 : (1 + lam) / 2 < 1)
    (hCμ : 2 * C * ε ≤ 1 - (1 + lam) / 2)
    (hSum1 : ∀ n : ℕ, ∑ k ∈ Finset.range n, C * ε ^ 2 * ((1 + lam) / 2) ^ (2 * k) ≤ 1 / 8)
    (hSum2 : ∀ n : ℕ, ∑ k ∈ Finset.range n,
      8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * ((1 + lam) / 2) ^ (2 * k - 1)) ≤ 1 / 2)
    (hK : ∀ k : ℕ, 2 * C * ε * ((k : ℝ) * ((1 + lam) / 2) ^ (k - 1)) ≤ 1)
    {P P' : ℂ} (hP : ‖P - A‖ ≤ ε) (hP' : ‖P' - A‖ ≤ ε) (him : P.im = P'.im)
    (hpos : dynXi A P < dynXi A P')
    (hξ : Filter.Tendsto (fun n : ℕ => dynXi A ((T^[n]) P)) Filter.atTop (nhds 0))
    (hξ' : Filter.Tendsto (fun n : ℕ => dynXi A ((T^[n]) P')) Filter.atTop (nhds 0)) : False := by
  have trapP := dynTrap h P hP
  have trapP' := dynTrap h P' hP'
  obtain ⟨hA, hε0, hC0, hlam0, hlam1, hCε, haxis, F, G, hrep, hFb, hGb, hFl, hGl⟩ := h
  set μ : ℝ := (1 + lam) / 2 with hμdef
  have hSum2b : ∀ n : ℕ, ∑ k ∈ Finset.range n,
      8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ k * μ ^ (k - 1)) ≤ 1 / 2 := by
    intro n
    have heq : (∑ k ∈ Finset.range n, 8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ k * μ ^ (k - 1))) =
        ∑ k ∈ Finset.range n, 8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ (2 * k - 1)) :=
      Finset.sum_congr rfl (fun k _ => by rw [key_pow hμ0 k])
    rw [heq]; exact hSum2 n
  have hξb : ∀ n : ℕ, |dynXi A ((T^[n]) P)| ≤ 2 * ε := fun n =>
    (le_add_of_nonneg_right (abs_nonneg _)).trans (trapP.1 n)
  have hηb : ∀ n : ℕ, |dynEta A ((T^[n]) P)| ≤ 2 * ε := fun n =>
    (le_add_of_nonneg_left (abs_nonneg _)).trans (trapP.1 n)
  have hξb' : ∀ n : ℕ, |dynXi A ((T^[n]) P')| ≤ 2 * ε := fun n =>
    (le_add_of_nonneg_right (abs_nonneg _)).trans (trapP'.1 n)
  have hηb' : ∀ n : ℕ, |dynEta A ((T^[n]) P')| ≤ 2 * ε := fun n =>
    (le_add_of_nonneg_left (abs_nonneg _)).trans (trapP'.1 n)
  have hηd : ∀ n : ℕ, |dynEta A ((T^[n]) P)| ≤ ε * μ ^ n := fun n => by
    have h1 := trapP.2.2 n; rwa [mul_comm] at h1
  have hηd' : ∀ n : ℕ, |dynEta A ((T^[n]) P')| ≤ ε * μ ^ n := fun n => by
    have h1 := trapP'.2.2 n; rwa [mul_comm] at h1
  have h4x : ∀ n : ℕ, |dynXi A ((T^[n]) P)| ≤ 4 * ε := fun n => by linarith [hξb n, hε0]
  have h4y : ∀ n : ℕ, |dynEta A ((T^[n]) P)| ≤ 4 * ε := fun n => by linarith [hηb n, hε0]
  have h4x' : ∀ n : ℕ, |dynXi A ((T^[n]) P')| ≤ 4 * ε := fun n => by linarith [hξb' n, hε0]
  have h4y' : ∀ n : ℕ, |dynEta A ((T^[n]) P')| ≤ 4 * ε := fun n => by linarith [hηb' n, hε0]
  have stepξ : ∀ n : ℕ, dynXi A ((T^[n + 1]) P) =
      dynXi A ((T^[n]) P) + F (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P)) := by
    intro n
    have hs := (dynStep hrep (h4x n) (h4y n)).1
    rw [Function.iterate_succ_apply']
    exact hs
  have stepη : ∀ n : ℕ, dynEta A ((T^[n + 1]) P) =
      dynEta A ((T^[n]) P) * G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P)) := by
    intro n
    have hs := (dynStep hrep (h4x n) (h4y n)).2
    rw [Function.iterate_succ_apply']
    exact hs
  have stepξ' : ∀ n : ℕ, dynXi A ((T^[n + 1]) P') =
      dynXi A ((T^[n]) P') + F (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) := by
    intro n
    have hs := (dynStep hrep (h4x' n) (h4y' n)).1
    rw [Function.iterate_succ_apply']
    exact hs
  have stepη' : ∀ n : ℕ, dynEta A ((T^[n + 1]) P') =
      dynEta A ((T^[n]) P') * G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) := by
    intro n
    have hs := (dynStep hrep (h4x' n) (h4y' n)).2
    rw [Function.iterate_succ_apply']
    exact hs
  have hD0 : dynD T A P P' 0 = dynXi A P' - dynXi A P := by simp [dynD]
  have hE0 : dynE T A P P' 0 = 0 := by
    simp only [dynE, Function.iterate_zero_apply, dynEta, Complex.sub_im]
    linarith [him]
  set D : ℝ := dynD T A P P' 0 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    rw [show dynD T A P P' 0 = dynXi A P' - dynXi A P by simp [dynD]]
    simp only [dynXi] at hpos ⊢
    linarith [hpos]
  have hDrec : ∀ n : ℕ, dynD T A P P' (n + 1) = dynD T A P P' n +
      (F (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) -
        F (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))) := by
    intro n
    simp only [dynD, stepξ n, stepξ' n]
    ring
  have hErec : ∀ n : ℕ, dynE T A P P' (n + 1) =
      dynE T A P P' n * G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) +
        dynEta A ((T^[n]) P) * (G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) -
          G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))) := by
    intro n
    simp only [dynE, stepη n, stepη' n]
    ring
  have htel : ∀ n : ℕ, dynD T A P P' n = D + ∑ k ∈ Finset.range n,
      (F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
        F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))) := by
    intro n
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]; exact hDdef.symm
    | succ n ih => rw [hDrec n, ih, Finset.sum_range_succ]; ring
  have key : ∀ n : ℕ, ∀ k ≤ n,
      |dynE T A P P' k| ≤ 4 * C * ε * D * ((k : ℝ) * μ ^ (k - 1)) ∧
      |dynE T A P P' k| ≤ 2 * D ∧
      dynD T A P P' k ≤ 2 * D ∧
      D / 4 ≤ dynD T A P P' k := by
    intro n
    induction n with
    | zero =>
        intro k hk
        obtain rfl : k = 0 := Nat.le_zero.mp hk
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hE0]; simp
        · rw [hE0, abs_zero]; linarith [hDpos]
        · show D ≤ 2 * D; linarith [hDpos]
        · show D / 4 ≤ D; linarith [hDpos]
    | succ n ih =>
        intro k hk
        rcases Nat.lt_or_eq_of_le hk with hlt | heq
        · exact ih k (Nat.lt_succ_iff.mp hlt)
        · subst heq
          have hGle : |G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P'))| ≤ μ :=
            dyn_G_le hC0 hlam0 hCε (hGb _ _ (h4x' n) (h4y' n)) (trapP'.1 n)
          have hGd : |G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) -
              G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))| ≤ C * (2 * D + 2 * D) := by
            have h1 := hGl _ _ _ _ (h4x' n) (h4y' n) (h4x n) (h4y n)
            have hdn : 0 ≤ dynD T A P P' n := le_trans (by linarith [hDpos]) (ih n le_rfl).2.2.2
            have h2 : |dynD T A P P' n| + |dynE T A P P' n| ≤ 2 * D + 2 * D := by
              rw [abs_of_nonneg hdn]
              linarith [(ih n le_rfl).2.2.1, (ih n le_rfl).2.1]
            have h3 : C * (|dynXi A ((T^[n]) P') - dynXi A ((T^[n]) P)| +
                |dynEta A ((T^[n]) P') - dynEta A ((T^[n]) P)|) =
                C * (|dynD T A P P' n| + |dynE T A P P' n|) := by simp [dynD, dynE]
            rw [h3] at h1
            exact h1.trans (mul_le_mul_of_nonneg_left h2 (le_of_lt hC0))
          have he1 : |dynE T A P P' (n + 1)| ≤ 4 * C * ε * D * (((n : ℝ) + 1) * μ ^ n) := by
            calc |dynE T A P P' (n + 1)|
                = |dynE T A P P' n * G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) +
                    dynEta A ((T^[n]) P) * (G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) -
                      G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P)))| := by rw [hErec n]
              _ ≤ |dynE T A P P' n * G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P'))| +
                    |dynEta A ((T^[n]) P) * (G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) -
                      G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P)))| := abs_add_le _ _
              _ = |dynE T A P P' n| * |G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P'))| +
                    |dynEta A ((T^[n]) P)| * |G (dynXi A ((T^[n]) P')) (dynEta A ((T^[n]) P')) -
                      G (dynXi A ((T^[n]) P)) (dynEta A ((T^[n]) P))| := by rw [abs_mul, abs_mul]
              _ ≤ (4 * C * ε * D * ((n : ℝ) * μ ^ (n - 1))) * μ +
                    (ε * μ ^ n) * (C * (2 * D + 2 * D)) := by
                  refine add_le_add ?_ ?_
                  · exact mul_le_mul (ih n le_rfl).1 hGle (abs_nonneg _) (by positivity)
                  · exact mul_le_mul (hηd n) hGd (abs_nonneg _) (by positivity)
              _ = 4 * C * ε * D * (((n : ℝ) + 1) * μ ^ n) := arith_e hμ0 n
          have he2 : |dynE T A P P' (n + 1)| ≤ 2 * D := by
            have hK' : 2 * C * ε * (((n : ℝ) + 1) * μ ^ n) ≤ 1 := by
              have h1 := hK (n + 1)
              simpa using h1
            have hmul : 2 * D * (2 * C * ε * (((n : ℝ) + 1) * μ ^ n)) ≤ 2 * D * 1 :=
              mul_le_mul_of_nonneg_left hK' (by linarith [hDpos])
            have hrew : 4 * C * ε * D * (((n : ℝ) + 1) * μ ^ n) =
                2 * D * (2 * C * ε * (((n : ℝ) + 1) * μ ^ n)) := by ring
            linarith [he1, hmul, hrew]
          have hterm : ∀ k ∈ Finset.range (n + 1),
              |F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))| ≤
              2 * D * (C * ε ^ 2 * μ ^ (2 * k)) +
                D * (8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ k * μ ^ (k - 1))) := by
            intro k hk
            have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have ihk := ih k hkn
            have hl := hFl _ _ _ _ (h4x' k) (h4y' k) (h4x k) (h4y k)
            have hl' : |F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))| ≤
                C * ((dynEta A ((T^[k]) P')) ^ 2 * |dynD T A P P' k| +
                  (|dynEta A ((T^[k]) P')| + |dynEta A ((T^[k]) P)|) * |dynE T A P P' k|) := by
              simpa only [dynD, dynE, abs_sub_comm] using hl
            have hb1 : (dynEta A ((T^[k]) P')) ^ 2 * |dynD T A P P' k| ≤
                ε ^ 2 * μ ^ (2 * k) * (2 * D) := by
              have h1 : (dynEta A ((T^[k]) P')) ^ 2 ≤ ε ^ 2 * μ ^ (2 * k) := by
                rw [← sq_abs]
                calc |dynEta A ((T^[k]) P')| ^ 2 ≤ (ε * μ ^ k) ^ 2 :=
                      pow_le_pow_left₀ (abs_nonneg _) (hηd' k) 2
                  _ = ε ^ 2 * μ ^ (2 * k) := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]
              have hdn : 0 ≤ dynD T A P P' k := le_trans (by linarith [hDpos]) ihk.2.2.2
              have h2 : |dynD T A P P' k| ≤ 2 * D := by
                rw [abs_of_nonneg hdn]; exact ihk.2.2.1
              exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
            have hb2 : (|dynEta A ((T^[k]) P')| + |dynEta A ((T^[k]) P)|) *
                |dynE T A P P' k| ≤
                (2 * ε * μ ^ k) * (4 * C * ε * D * ((k : ℝ) * μ ^ (k - 1))) := by
              have h1 : |dynEta A ((T^[k]) P')| + |dynEta A ((T^[k]) P)| ≤ 2 * ε * μ ^ k := by
                have h2 := hηd k; have h3 := hηd' k; linarith
              have h2 : |dynE T A P P' k| ≤ 4 * C * ε * D * ((k : ℝ) * μ ^ (k - 1)) := ihk.1
              exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
            calc |F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                  F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))|
                ≤ C * ((dynEta A ((T^[k]) P')) ^ 2 * |dynD T A P P' k| +
                    (|dynEta A ((T^[k]) P')| + |dynEta A ((T^[k]) P)|) * |dynE T A P P' k|) := hl'
              _ ≤ C * (ε ^ 2 * μ ^ (2 * k) * (2 * D) +
                    (2 * ε * μ ^ k) * (4 * C * ε * D * ((k : ℝ) * μ ^ (k - 1)))) :=
                  mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (le_of_lt hC0)
              _ = 2 * D * (C * ε ^ 2 * μ ^ (2 * k)) +
                    D * (8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ k * μ ^ (k - 1))) := by ring
          have hSumAbs : ∑ k ∈ Finset.range (n + 1),
              |F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))| ≤ 3 * D / 4 := by
            calc ∑ k ∈ Finset.range (n + 1),
                  |F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                    F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))|
                ≤ ∑ k ∈ Finset.range (n + 1), (2 * D * (C * ε ^ 2 * μ ^ (2 * k)) +
                    D * (8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ k * μ ^ (k - 1)))) :=
                  Finset.sum_le_sum (fun k hk => hterm k hk)
              _ = 2 * D * (∑ k ∈ Finset.range (n + 1), C * ε ^ 2 * μ ^ (2 * k)) +
                    D * (∑ k ∈ Finset.range (n + 1),
                      8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * μ ^ k * μ ^ (k - 1))) := by
                  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
              _ ≤ 2 * D * (1 / 8) + D * (1 / 2) := by
                  have h1 := hSum1 (n + 1)
                  have h2 := hSum2b (n + 1)
                  nlinarith [h1, h2, hDpos]
              _ = 3 * D / 4 := by ring
          have hSumSigned : ∑ k ∈ Finset.range (n + 1),
              (F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))) ≤ 3 * D / 4 :=
            (Finset.sum_le_sum (fun k _ => le_abs_self _)).trans hSumAbs
          have hSumSigned' : -(3 * D / 4) ≤ ∑ k ∈ Finset.range (n + 1),
              (F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))) := by
            have h1 : -(∑ k ∈ Finset.range (n + 1),
                |F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                  F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))|) ≤
                -(|∑ k ∈ Finset.range (n + 1),
                  (F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                    F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P)))|) :=
              neg_le_neg (Finset.abs_sum_le_sum_abs _ _)
            have h2 : -(|∑ k ∈ Finset.range (n + 1),
                  (F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                    F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P)))|) ≤
                ∑ k ∈ Finset.range (n + 1),
                  (F (dynXi A ((T^[k]) P')) (dynEta A ((T^[k]) P')) -
                    F (dynXi A ((T^[k]) P)) (dynEta A ((T^[k]) P))) := neg_abs_le _
            linarith [h1, h2, hSumAbs]
          refine ⟨?_, he2, ?_, ?_⟩
          · simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using he1
          · have h1 := htel (n + 1)
            linarith [h1, hSumSigned, hDpos]
          · have h1 := htel (n + 1)
            linarith [h1, hSumSigned', hDpos]
  have hfin : ∀ n : ℕ, D / 4 ≤ dynD T A P P' n := fun n => (key n n le_rfl).2.2.2
  have hlim : Filter.Tendsto (fun n : ℕ => dynD T A P P' n) Filter.atTop (nhds 0) := by
    have h1 := hξ'.sub hξ
    have h2 : (fun n : ℕ => dynXi A ((T^[n]) P') - dynXi A ((T^[n]) P)) =
        fun n : ℕ => dynD T A P P' n := rfl
    rw [h2] at h1
    simpa using h1
  have hle : D / 4 ≤ 0 := ge_of_tendsto' hlim hfin
  linarith [hDpos, hle]

/-- **Uniqueness** (third conjunct of `localModel_dynamics`). -/
theorem localModel_unique {T : ℂ → ℂ} {A : ℂ} {lam C ε : ℝ} (h : LocalModel T A lam C ε)
    (hε : ε ≤ (1 - lam) / 4)
    (hμ0 : 0 < (1 + lam) / 2) (hμ1 : (1 + lam) / 2 < 1)
    (hCμ : 2 * C * ε ≤ 1 - (1 + lam) / 2)
    (hSum1 : ∀ n : ℕ, ∑ k ∈ Finset.range n, C * ε ^ 2 * ((1 + lam) / 2) ^ (2 * k) ≤ 1 / 8)
    (hSum2 : ∀ n : ℕ, ∑ k ∈ Finset.range n,
      8 * C ^ 2 * ε ^ 2 * ((k : ℝ) * ((1 + lam) / 2) ^ (2 * k - 1)) ≤ 1 / 2)
    (hK : ∀ k : ℕ, 2 * C * ε * ((k : ℝ) * ((1 + lam) / 2) ^ (k - 1)) ≤ 1) :
    ∀ P P' : ℂ, ‖P - A‖ ≤ ε → ‖P' - A‖ ≤ ε → P.im = P'.im →
      Filter.Tendsto (fun n : ℕ => (T^[n]) P) Filter.atTop (nhds A) →
      Filter.Tendsto (fun n : ℕ => (T^[n]) P') Filter.atTop (nhds A) → P = P' := by
  intro P P' hP hP' him hlim hlim'
  have hξ : Filter.Tendsto (fun n : ℕ => dynXi A ((T^[n]) P)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (T^[n]) P - A) Filter.atTop (nhds (A - A)) :=
      hlim.sub tendsto_const_nhds
    have h3 := Complex.continuous_re.continuousAt.tendsto.comp h1
    have h4 : Filter.Tendsto (fun n : ℕ => ((T^[n]) P - A).re) Filter.atTop
        (nhds ((A - A).re)) := h3
    simpa [dynXi, Complex.sub_re] using h4
  have hξ' : Filter.Tendsto (fun n : ℕ => dynXi A ((T^[n]) P')) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (T^[n]) P' - A) Filter.atTop (nhds (A - A)) :=
      hlim'.sub tendsto_const_nhds
    have h3 := Complex.continuous_re.continuousAt.tendsto.comp h1
    have h4 : Filter.Tendsto (fun n : ℕ => ((T^[n]) P' - A).re) Filter.atTop
        (nhds ((A - A).re)) := h3
    simpa [dynXi, Complex.sub_re] using h4
  rcases lt_trichotomy (dynXi A P) (dynXi A P') with hlt | heq | hgt
  · exact (dyn_expand h hε hμ0 hμ1 hCμ hSum1 hSum2 hK hP hP' him hlt hξ hξ').elim
  · have hA : A.im = 0 := h.1
    have hη : dynEta A P = dynEta A P' := by
      simp only [dynEta, Complex.sub_im, hA, sub_zero]
      exact him
    rw [← dyn_point_eq A P, ← dyn_point_eq A P', heq, hη]
  · exact (dyn_expand h hε hμ0 hμ1 hCμ hSum1 hSum2 hK hP' hP him.symm hgt hξ' hξ).elim

/-- **Local normal form dynamics.** -/
theorem localModel_dynamics {T : ℂ → ℂ} {A : ℂ} {lam C ε : ℝ} (h : LocalModel T A lam C ε)
    (hε : ε ≤ (1 - lam) / 4) :
    (∀ P : ℂ, ‖P - A‖ ≤ ε → ∀ n : ℕ, ‖(T^[n]) P - A‖ ≤ 2 * ε) ∧
    (∀ P : ℂ, ‖P - A‖ ≤ ε → ∃ Q : ℂ, Q.im = 0 ∧ ‖Q - A‖ ≤ 2 * ε ∧
      Filter.Tendsto (fun n : ℕ => (T^[n]) P) Filter.atTop (nhds Q)) ∧
    (∀ P P' : ℂ, ‖P - A‖ ≤ ε → ‖P' - A‖ ≤ ε → P.im = P'.im →
      Filter.Tendsto (fun n : ℕ => (T^[n]) P) Filter.atTop (nhds A) →
      Filter.Tendsto (fun n : ℕ => (T^[n]) P') Filter.atTop (nhds A) → P = P') := by
  obtain ⟨hμ0, hμ1, hCμ, hSum1, hSum2, hK, _hM1, _hM2⟩ :=
    dyn_geom_bounds h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 hε
  exact ⟨fun P hP n => (dynTrap h P hP).2.1 n, localModel_limit h,
    localModel_unique h hε hμ0 hμ1 hCμ hSum1 hSum2 hK⟩

end Work.EQ
