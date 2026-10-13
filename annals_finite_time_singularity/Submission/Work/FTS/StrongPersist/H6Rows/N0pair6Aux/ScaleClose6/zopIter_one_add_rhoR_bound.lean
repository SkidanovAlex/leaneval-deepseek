import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Construction.H6N_GammaTerm_rho_bound
import Submission.Work.Construction.GammaTermAux
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.leibniz_radial_mul
import Submission.Work.FTS.FinalClock.ZopIterLeibniz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `(1+z)·ρ` companion of the radial `ℋ⁶` bound

The task statement asks for the `Zop`-iterate bound of the *shifted* radial profile
`(1+z)·ρ(z)` (`ρ = Work.Construction.rhoR`), given the corresponding bound for `ρ` itself:

`|(Zop^[j] ρ)(z)·w(z)| ≤ M/(1+z)²`  ⟹  `|(Zop^[j] ((1+z)·ρ))(z)·w(z)| ≤ 64M/(1+z)`  (`j ≤ 6`).

The whole content is the **iterated Leibniz rule** for the radial derivation
`Zop u = z u'` (`Work.FTS.FinalClock.ZopIterLeibniz`), applied to the product
`(fun z => 1 + z) * ρ` on the open set `Ioi (-1)` (where both factors are `C^j`), together with
the elementary fact that

* `Zop^[0] (fun z => 1 + z) = fun z => 1 + z`, and
* `Zop^[b+1] (fun z => 1 + z) = fun z => z`   (since `Zop (1+·) = 1·(1+·)' ·z = z` and `Zop z = z`);

hence `0 ≤ Zop^[b](1+·) z ≤ 1 + z` for `z ≥ 0`.  The Leibniz sum therefore factors as

`|Zop^[j]((1+z)ρ) z · w z| ≤ ∑_{b ≤ j} C(j,b) · (1+z) · M/(1+z)² = 2^j · M/(1+z) ≤ 64 M/(1+z)`

for `j ≤ 6`.  The case `z = 0` is trivial because `w 0 = 0` (`w` is totalised division).

This is the standard `2^j`-loss one expects from a Leibniz expansion; the constant `64 = 2^6`
of the statement is exactly `2^j` at the top order `j = 6`, so the bound is sharp as an
application of this method.
-/

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6

/-! ## The `Zop`-iterates of `fun z => 1 + z` -/

/-- `Zop` sends `fun z => 1 + z` to `fun z => z`. -/
theorem zop_one_eq_id : Work.Spaces.Zop (fun z : ℝ => 1 + z) = fun z : ℝ => z := by
  funext z; simp [Work.Spaces.Zop]

/-- `fun z => z` is a fixed point of `Zop`. -/
theorem zop_id_eq_id : Work.Spaces.Zop (fun z : ℝ => z) = fun z : ℝ => z := by
  funext z; simp [Work.Spaces.Zop]

/-- Every `Zop`-iterate of `fun z => z` is `fun z => z`. -/
theorem zop_iter_self (b : ℕ) : Work.Spaces.Zop^[b] (fun z : ℝ => z) = fun z : ℝ => z := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Function.iterate_succ, Function.comp_apply, zop_id_eq_id, ih]

/-- The `(b+1)`-st `Zop`-iterate of `fun z => 1 + z` is `fun z => z`. -/
theorem zop_iter_one_add_succ (b : ℕ) :
    Work.Spaces.Zop^[b + 1] (fun z : ℝ => 1 + z) = fun z : ℝ => z := by
  rw [Function.iterate_succ, Function.comp_apply, zop_one_eq_id]
  exact zop_iter_self b

/-- The pointwise value of the `Zop`-iterates of `fun z => 1 + z`. -/
theorem zop_one_add_val (b : ℕ) (z : ℝ) :
    Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z = (if b = 0 then 1 + z else z) := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
    rw [zop_iter_one_add_succ c]
    simp

/-- For `z ≥ 0` every `Zop`-iterate of `fun z => 1 + z` lies in `[0, 1+z]`. -/
theorem zop_one_add_le (b : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z ∧
      Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z ≤ 1 + z := by
  rw [zop_one_add_val b z]
  split_ifs <;> constructor <;> linarith

/-! ## Smoothness of `ρ` on `(-1,∞)` -/

/-- `ρ(z) = z²/(1+z)⁴` is `C^j` on `(-1,∞)`. -/
theorem rhoR_contDiffOn (j : ℕ) :
    ContDiffOn ℝ j Work.Construction.rhoR (Set.Ioi (-1 : ℝ)) := by
  have hnum : ContDiffOn ℝ j (fun z : ℝ => z ^ 2) (Set.Ioi (-1 : ℝ)) :=
    (contDiff_id.contDiffOn).pow 2
  have hden : ContDiffOn ℝ j (fun z : ℝ => (1 + z) ^ 4) (Set.Ioi (-1 : ℝ)) :=
    ((contDiff_const.add contDiff_id).contDiffOn).pow 4
  have hne : ∀ z ∈ Set.Ioi (-1 : ℝ), (1 + z) ^ 4 ≠ 0 := by
    intro z hz
    have h : (-1 : ℝ) < z := hz
    have h2 : (0 : ℝ) < 1 + z := by linarith
    positivity
  have h := hnum.div hden hne
  have hfun : Work.Construction.rhoR = ((fun z : ℝ => z ^ 2) / fun z : ℝ => (1 + z) ^ 4) := by
    funext z
    simp [Work.Construction.rhoR, Pi.div_apply]
  rw [hfun]
  exact h

/-! ## The bound -/

theorem zopIter_one_add_rhoR_bound {M : ℝ} (hM : 0 < M)
    (hMr : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] Work.Construction.rhoR) z * Work.Spaces.w z| ≤ M / (1 + z) ^ 2) :
    ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z →
      |(Work.Spaces.Zop^[j] (fun z : ℝ => (1 + z) * Work.Construction.rhoR z)) z
        * Work.Spaces.w z| ≤ (64 * M) / (1 + z) := by
  intro j hj z hz
  -- the total weight of the Leibniz sum is `2^j`
  have hchoose2j : ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  rcases eq_or_lt_of_le hz with h0 | hzpos
  · -- `z = 0` is trivial since `w 0 = 0`
    subst h0
    rw [show Work.Spaces.w 0 = 0 by norm_num [Work.Spaces.w], mul_zero, abs_zero]
    positivity
  · have h1z : (0 : ℝ) < 1 + z := by linarith
    have hV : IsOpen (Set.Ioi (-1 : ℝ)) := isOpen_Ioi
    have hzV : z ∈ Set.Ioi (-1 : ℝ) := by show (-1 : ℝ) < z; linarith
    have hu : ContDiffOn ℝ j (fun w : ℝ => 1 + w) (Set.Ioi (-1 : ℝ)) :=
      (contDiff_const.add contDiff_id).contDiffOn
    have hv : ContDiffOn ℝ j Work.Construction.rhoR (Set.Ioi (-1 : ℝ)) := rhoR_contDiffOn j
    -- the iterated Leibniz rule for `Zop u = z u'` on `(-1,∞)`
    have hleib : Work.Spaces.Zop^[j] (fun w : ℝ => (1 + w) * Work.Construction.rhoR w) z
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z) := by
      have hfun : (fun w : ℝ => (1 + w) * Work.Construction.rhoR w)
          = (fun w : ℝ => 1 + w) * Work.Construction.rhoR := by
        funext w; rfl
      rw [hfun]
      exact Work.FTS.FinalClock.ZopIterLeibniz hV hu hv hzV
    rw [hleib]
    -- every summand of the Leibniz expansion is at most `C(j,b)·(1+z)·M/(1+z)²`
    have hterm : ∀ b ∈ Finset.range (j + 1),
        |((j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
            * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z|
          ≤ (j.choose b : ℝ) * ((1 + z) * (M / (1 + z) ^ 2)) := by
      intro b hb
      have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hjb : j - b ≤ 6 := by omega
      have hX := zop_one_add_le b z hz
      have hY := hMr (j - b) hjb z hz
      calc |((j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
              * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z|
          = (j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
              * |(Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z * Work.Spaces.w z|) := by
            rw [show ((j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z
                = (j.choose b : ℝ) * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * ((Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z * Work.Spaces.w z))
                from by ring]
            rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hX.1]
        _ ≤ (j.choose b : ℝ) * ((1 + z) * (M / (1 + z) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            exact mul_le_mul hX.2 hY (abs_nonneg _) (by linarith)
    calc |(∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z|
        = |∑ b ∈ Finset.range (j + 1), ((j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z| := by
            rw [Finset.sum_mul]
      _ ≤ ∑ b ∈ Finset.range (j + 1), |((j.choose b : ℝ)
              * (Work.Spaces.Zop^[b] (fun w : ℝ => 1 + w) z
                  * (Work.Spaces.Zop^[j - b] Work.Construction.rhoR) z)) * Work.Spaces.w z| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * ((1 + z) * (M / (1 + z) ^ 2)) :=
            Finset.sum_le_sum hterm
      _ = (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) * ((1 + z) * (M / (1 + z) ^ 2)) := by
            rw [Finset.sum_mul]
      _ = (2 : ℝ) ^ j * ((1 + z) * (M / (1 + z) ^ 2)) := by rw [hchoose2j]
      _ ≤ (64 * M) / (1 + z) := by
            have h2j : (2 : ℝ) ^ j ≤ 64 := by
              have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
              norm_num at h
              linarith
            have hbnd : (1 + z) * (M / (1 + z) ^ 2) = M / (1 + z) := by
              field_simp
            rw [hbnd]
            have hMdiv : 0 ≤ M / (1 + z) := by positivity
            calc (2 : ℝ) ^ j * (M / (1 + z)) ≤ 64 * (M / (1 + z)) :=
                  mul_le_mul_of_nonneg_right h2j hMdiv
              _ = (64 * M) / (1 + z) := by ring

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6
