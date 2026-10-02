/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.exists_uniform_bounds` — local uniformity of the second return map

The parabolic splitting argument (`Work.PARIMPL.ParSplit.split_exists`) and its consumers need
the second return map `Work.EL.F c = (T_c)^{10} = (Tsq c)^[5]` to be *uniformly* controlled, in
`c` and in `z`, on a small bidisc around `(c₀, z₁)`: bounded values, bounded derivatives up to
order three, and joint continuity of the derivative tower.

Nothing here is subtle complex analysis: `Tsq c z = (z² + c̄)² + c` is a polynomial in `(c, c̄, z)`,
so `(c, z) ↦ (Tsq c)^[n] z` and all its `z`-derivatives are continuous in `(c, z)`.  The module
makes that precise by running the *chain rule* induction on `n`:

* `Zr n`, `Ar n`, `Br n`, `Cr n` are the joint maps `(c,z) ↦ (Tsq c)^[n] z`,
  `deriv`, `iteratedDeriv 2`, `iteratedDeriv 3` respectively;
* `Zr_succ`, `Ar_succ`, `Br_succ`, `Cr_succ` are the recurrences (chain rule for one iterate
  step), proved from the composition formulas `iteratedDeriv_two_comp`, `iteratedDeriv_three_comp`
  for the second and third derivatives of `f ∘ g` (Faà di Bruno for a single inner function);
* `continuous_tower` assembles these into continuity of the whole tower for every `n ≥ 1`.

The base case `n = 1` is the explicit computation of the first three derivatives of `Tsq c`
(`deriv_Tsq`, `iteratedDeriv_two_Tsq`, `iteratedDeriv_three_Tsq`).

## Main result

* `exists_uniform_bounds` — a positive `ρ`, `R` and a constant `M ≥ 0` bound
  `F c z`, `∂_z F c z`, `∂_z² F c z`, `∂_z³ F c z` on `ball c₀ ρ × ball z₁ R`, and the
  four-tuple map is continuous on that bidisc.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## The derivatives of the second return map `Tsq` -/

/-- The derivative of the holomorphic second iterate `Tsq c z = (z² + c̄)² + c`. -/
theorem deriv_Tsq (c z : ℂ) : deriv (Work.Landing.Tsq c) z = 4 * z * (z ^ 2 + star c) := by
  unfold Work.Landing.Tsq
  simp
  ring

/-- The second derivative of `Tsq`. -/
theorem iteratedDeriv_two_Tsq (c z : ℂ) :
    iteratedDeriv 2 (Work.Landing.Tsq c) z = 12 * z ^ 2 + 4 * star c := by
  have h1 : deriv (Work.Landing.Tsq c) = fun y => 4 * y * (y ^ 2 + star c) := by
    funext y; exact deriv_Tsq c y
  have h2 : iteratedDeriv 2 (Work.Landing.Tsq c) = deriv (deriv (Work.Landing.Tsq c)) := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h2, h1]
  change deriv ((fun y : ℂ => 4 * y) * (fun y : ℂ => y ^ 2 + star c)) z
      = 12 * z ^ 2 + 4 * star c
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp
  ring

/-- The third derivative of `Tsq`. -/
theorem iteratedDeriv_three_Tsq (c z : ℂ) :
    iteratedDeriv 3 (Work.Landing.Tsq c) z = 24 * z := by
  have h1 : iteratedDeriv 2 (Work.Landing.Tsq c) = fun y => 12 * y ^ 2 + 4 * star c := by
    funext y; exact iteratedDeriv_two_Tsq c y
  have h2 : iteratedDeriv 3 (Work.Landing.Tsq c) = deriv (iteratedDeriv 2 (Work.Landing.Tsq c)) := by
    simp [iteratedDeriv_succ]
  rw [h2, h1]
  simp
  ring

/-! ## Chain rules for the second and third derivative of a composition -/

/-- The second derivative of a composition of entire functions:
`(f ∘ g)'' = (f'' ∘ g)·(g')² + (f' ∘ g)·g''`. -/
theorem iteratedDeriv_two_comp {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z : ℂ) :
    iteratedDeriv 2 (f ∘ g) z =
      iteratedDeriv 2 f (g z) * (deriv g z) ^ 2 + deriv f (g z) * iteratedDeriv 2 g z := by
  have hfg : deriv (f ∘ g) = fun w => deriv f (g w) * deriv g w := by
    funext w
    exact deriv_comp (x := w) (h := g) (h₂ := f) hf.differentiableAt hg.differentiableAt
  have h1 : iteratedDeriv 2 (f ∘ g) = deriv (deriv (f ∘ g)) := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1, hfg]
  change deriv (((deriv f) ∘ g) * (deriv g)) z =
    iteratedDeriv 2 f (g z) * (deriv g z) ^ 2 + deriv f (g z) * iteratedDeriv 2 g z
  rw [deriv_mul ((hf.deriv.differentiableAt).comp z hg.differentiableAt)
    hg.deriv.differentiableAt]
  have hcomp : deriv ((deriv f) ∘ g) z = deriv (deriv f) (g z) * deriv g z :=
    deriv_comp (x := z) (h := g) (h₂ := deriv f) (hf.deriv.differentiableAt) hg.differentiableAt
  rw [hcomp]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_apply]
  ring

/-- The third derivative of a composition of entire functions (Faà di Bruno with one inner
function): `(f ∘ g)''' = (f''' ∘ g)·(g')³ + 3·(f'' ∘ g)·g'·g'' + (f' ∘ g)·g'''`. -/
theorem iteratedDeriv_three_comp {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z : ℂ) :
    iteratedDeriv 3 (f ∘ g) z =
      iteratedDeriv 3 f (g z) * (deriv g z) ^ 3
        + 3 * (iteratedDeriv 2 f (g z) * deriv g z * iteratedDeriv 2 g z)
        + deriv f (g z) * iteratedDeriv 3 g z := by
  have hP : iteratedDeriv 2 (f ∘ g) =
      fun w => iteratedDeriv 2 f (g w) * deriv g w ^ 2 + deriv f (g w) * iteratedDeriv 2 g w :=
    funext fun w => iteratedDeriv_two_comp hf hg w
  have h3 : iteratedDeriv 3 (f ∘ g) = deriv (iteratedDeriv 2 (f ∘ g)) := by
    simp [iteratedDeriv_succ]
  rw [h3, hP]
  have hfun :
      (fun w => iteratedDeriv 2 f (g w) * deriv g w ^ 2 + deriv f (g w) * iteratedDeriv 2 g w)
      = ((fun w => iteratedDeriv 2 f (g w)) * (deriv g ^ 2)
          + (fun w => deriv f (g w)) * (fun w => iteratedDeriv 2 g w)) := rfl
  rw [hfun]
  have hA : DifferentiableAt ℂ (fun w : ℂ => iteratedDeriv 2 f (g w)) z :=
    ((by simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
        (hf.deriv.deriv.differentiableAt (x := g z)) :
        DifferentiableAt ℂ (iteratedDeriv 2 f) (g z))).comp z hg.differentiableAt
  have hB : DifferentiableAt ℂ (deriv g ^ 2) z := hg.deriv.differentiableAt.pow 2
  have hC : DifferentiableAt ℂ (fun w : ℂ => deriv f (g w)) z :=
    (hf.deriv.differentiableAt).comp z hg.differentiableAt
  have hD : DifferentiableAt ℂ (fun w : ℂ => iteratedDeriv 2 g w) z := by
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using (hg.deriv.deriv.differentiableAt (x := z))
  rw [deriv_add (hA.mul hB) (hC.mul hD)]
  rw [deriv_mul hA hB, deriv_mul hC hD]
  have hA' : deriv (fun w : ℂ => iteratedDeriv 2 f (g w)) z
      = deriv (iteratedDeriv 2 f) (g z) * deriv g z :=
    deriv_comp (x := z) (h := g) (h₂ := iteratedDeriv 2 f)
      (by simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
        (hf.deriv.deriv.differentiableAt (x := g z)))
      hg.differentiableAt
  have hB' : deriv (deriv g ^ 2) z = 2 * deriv g z * deriv (deriv g) z := by
    rw [show (deriv g ^ 2 : ℂ → ℂ) = fun i => deriv g i ^ 2 from rfl]
    rw [deriv_fun_pow hg.deriv.differentiableAt 2]
    norm_num
  have hC' : deriv (fun w : ℂ => deriv f (g w)) z = deriv (deriv f) (g z) * deriv g z :=
    deriv_comp (x := z) (h := g) (h₂ := deriv f) (hf.deriv.differentiableAt) hg.differentiableAt
  rw [hA', hB', hC']
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Pi.pow_apply]
  ring

/-! ## The joint derivative tower -/

/-- The `n`-th `z`-iterate shift: `(c, z) ↦ (c, Tsq c z)`. -/
def H : ℂ × ℂ → ℂ × ℂ := fun p => (p.1, Work.Landing.Tsq p.1 p.2)

theorem continuous_H : Continuous H := by
  unfold H
  exact Continuous.prodMk continuous_fst (by unfold Work.Landing.Tsq; fun_prop)

/-- Joint values of the `n`-th iterate of `Tsq`: `(c,z) ↦ (Tsq c)^[n] z`. -/
def Zr (n : ℕ) : ℂ × ℂ → ℂ := fun p => (Work.Landing.Tsq p.1) ^[n] p.2

/-- Joint first derivative of the `n`-th iterate of `Tsq`. -/
def Ar (n : ℕ) : ℂ × ℂ → ℂ := fun p => deriv ((Work.Landing.Tsq p.1) ^[n]) p.2

/-- Joint second derivative of the `n`-th iterate of `Tsq`. -/
def Br (n : ℕ) : ℂ × ℂ → ℂ := fun p => iteratedDeriv 2 ((Work.Landing.Tsq p.1) ^[n]) p.2

/-- Joint third derivative of the `n`-th iterate of `Tsq`. -/
def Cr (n : ℕ) : ℂ × ℂ → ℂ := fun p => iteratedDeriv 3 ((Work.Landing.Tsq p.1) ^[n]) p.2

theorem differentiable_Tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  unfold Work.Landing.Tsq; fun_prop

theorem differentiable_Tsq_iterate (c : ℂ) (n : ℕ) :
    Differentiable ℂ ((Work.Landing.Tsq c) ^[n]) := by
  induction n with
  | zero => simpa [Function.iterate_zero] using differentiable_id (𝕜 := ℂ)
  | succ k ih => rw [Function.iterate_succ']; exact (differentiable_Tsq c).comp ih

theorem Zr_succ (n : ℕ) : Zr (n + 1) = Zr n ∘ H := by
  funext p
  obtain ⟨c, z⟩ := p
  simp only [Zr, H, Function.comp_apply]
  exact Function.iterate_succ_apply (Work.Landing.Tsq c) n z

theorem Ar_succ (n : ℕ) : Ar (n + 1) = (Ar n ∘ H) * Ar 1 := by
  funext p
  obtain ⟨c, z⟩ := p
  have hf : Differentiable ℂ ((Work.Landing.Tsq c) ^[n]) := differentiable_Tsq_iterate c n
  have hg : Differentiable ℂ (Work.Landing.Tsq c) := differentiable_Tsq c
  simp only [Ar, H, Function.comp_apply, Pi.mul_apply, Function.iterate_one]
  rw [Function.iterate_succ,
    deriv_comp (x := z) (h := Work.Landing.Tsq c) (h₂ := (Work.Landing.Tsq c) ^[n])
      hf.differentiableAt hg.differentiableAt]

theorem Br_succ (n : ℕ) : Br (n + 1) = (Br n ∘ H) * (Ar 1) ^ 2 + (Ar n ∘ H) * Br 1 := by
  funext p
  obtain ⟨c, z⟩ := p
  have hf : Differentiable ℂ ((Work.Landing.Tsq c) ^[n]) := differentiable_Tsq_iterate c n
  have hg : Differentiable ℂ (Work.Landing.Tsq c) := differentiable_Tsq c
  simp only [Br, Ar, H, Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply,
    Function.iterate_one]
  rw [Function.iterate_succ, iteratedDeriv_two_comp hf hg z]

theorem Cr_succ (n : ℕ) :
    Cr (n + 1) = (Cr n ∘ H) * (Ar 1) ^ 3 + 3 * ((Br n ∘ H) * Ar 1 * Br 1)
      + (Ar n ∘ H) * Cr 1 := by
  funext p
  obtain ⟨c, z⟩ := p
  have hf : Differentiable ℂ ((Work.Landing.Tsq c) ^[n]) := differentiable_Tsq_iterate c n
  have hg : Differentiable ℂ (Work.Landing.Tsq c) := differentiable_Tsq c
  simp only [Cr, Br, Ar, H, Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply,
    Function.iterate_one, Pi.ofNat_apply]
  rw [Function.iterate_succ, iteratedDeriv_three_comp hf hg z]

/-! ## Continuity of the tower -/

theorem continuous_Zr_one : Continuous (Zr 1) := by
  have h : Zr 1 = fun p : ℂ × ℂ => Work.Landing.Tsq p.1 p.2 := by
    funext p
    obtain ⟨c, z⟩ := p
    simp only [Zr, Function.iterate_one]
  rw [h]
  unfold Work.Landing.Tsq
  fun_prop

theorem continuous_Ar_one : Continuous (Ar 1) := by
  have h : Ar 1 = fun p : ℂ × ℂ => 4 * p.2 * (p.2 ^ 2 + star p.1) := by
    funext p
    obtain ⟨c, z⟩ := p
    simp only [Ar, Function.iterate_one]
    exact deriv_Tsq c z
  rw [h]
  fun_prop

theorem continuous_Br_one : Continuous (Br 1) := by
  have h : Br 1 = fun p : ℂ × ℂ => 12 * p.2 ^ 2 + 4 * star p.1 := by
    funext p
    obtain ⟨c, z⟩ := p
    simp only [Br, Function.iterate_one]
    exact iteratedDeriv_two_Tsq c z
  rw [h]
  fun_prop

theorem continuous_Cr_one : Continuous (Cr 1) := by
  have h : Cr 1 = fun p : ℂ × ℂ => 24 * p.2 := by
    funext p
    obtain ⟨c, z⟩ := p
    simp only [Cr, Function.iterate_one]
    exact iteratedDeriv_three_Tsq c z
  rw [h]
  fun_prop

/-- **Continuity of the whole joint derivative tower** of `Tsq`, for every iterate count
`n ≥ 1`. -/
theorem continuous_tower : ∀ k : ℕ,
    Continuous (Zr (k + 1)) ∧ Continuous (Ar (k + 1)) ∧ Continuous (Br (k + 1))
      ∧ Continuous (Cr (k + 1)) := by
  intro k
  induction k with
  | zero => exact ⟨continuous_Zr_one, continuous_Ar_one, continuous_Br_one, continuous_Cr_one⟩
  | succ m ih =>
      obtain ⟨ihZ, ihA, ihB, ihC⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Zr_succ (m + 1)]
        exact ihZ.comp continuous_H
      · rw [Ar_succ (m + 1)]
        exact (ihA.comp continuous_H).mul continuous_Ar_one
      · rw [Br_succ (m + 1)]
        exact ((ihB.comp continuous_H).mul (continuous_Ar_one.pow 2)).add
          ((ihA.comp continuous_H).mul continuous_Br_one)
      · rw [Cr_succ (m + 1)]
        exact (((ihC.comp continuous_H).mul (continuous_Ar_one.pow 3)).add
          (((continuous_const : Continuous (fun _ : ℂ × ℂ => (3 : ℂ))).mul
            (((ihB.comp continuous_H).mul continuous_Ar_one).mul
              continuous_Br_one)))).add
          ((ihA.comp continuous_H).mul continuous_Cr_one)

theorem continuous_Zr_five : Continuous (Zr 5) := (continuous_tower 4).1
theorem continuous_Ar_five : Continuous (Ar 5) := (continuous_tower 4).2.1
theorem continuous_Br_five : Continuous (Br 5) := (continuous_tower 4).2.2.1
theorem continuous_Cr_five : Continuous (Cr 5) := (continuous_tower 4).2.2.2

/-! ## The uniform bounds -/

/-- **Uniform local control of the second return map `F = (Tsq ·)^[5]`.**  There are a parameter
radius `ρ > 0`, a dynamical radius `R > 0` and a constant `M ≥ 0` such that on
`ball c₀ ρ × ball z₁ R` the values of `F c z` and of its `z`-derivatives up to order three are
bounded by `M`, and the four-tuple of those quantities is continuous there. -/
theorem exists_uniform_bounds {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    ∃ ρ R M : ℝ, 0 < ρ ∧ 0 < R ∧ 0 ≤ M ∧
      (∀ c ∈ Metric.ball c₀ ρ, ∀ z ∈ Metric.ball d.z₁ R,
        ‖Work.EL.F c z‖ ≤ M ∧ ‖deriv (Work.EL.F c) z‖ ≤ M ∧
          ‖iteratedDeriv 2 (Work.EL.F c) z‖ ≤ M ∧ ‖iteratedDeriv 3 (Work.EL.F c) z‖ ≤ M) ∧
      ContinuousOn (fun p : ℂ × ℂ => (Work.EL.F p.1 p.2, deriv (Work.EL.F p.1) p.2,
        iteratedDeriv 2 (Work.EL.F p.1) p.2, iteratedDeriv 3 (Work.EL.F p.1) p.2))
        (Metric.ball c₀ ρ ×ˢ Metric.ball d.z₁ R) := by
  have hK : IsCompact (Metric.closedBall c₀ 1 ×ˢ Metric.closedBall d.z₁ 1) :=
    (isCompact_closedBall c₀ 1).prod (isCompact_closedBall d.z₁ 1)
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn continuous_Zr_five.continuousOn
  obtain ⟨M₂, hM₂⟩ := hK.exists_bound_of_continuousOn continuous_Ar_five.continuousOn
  obtain ⟨M₃, hM₃⟩ := hK.exists_bound_of_continuousOn continuous_Br_five.continuousOn
  obtain ⟨M₄, hM₄⟩ := hK.exists_bound_of_continuousOn continuous_Cr_five.continuousOn
  refine ⟨1, 1, max 0 (max (max M₁ M₂) (max M₃ M₄)), one_pos, one_pos, le_max_left _ _, ?_, ?_⟩
  · intro c hc z hz
    have hmem : (c, z) ∈ Metric.closedBall c₀ 1 ×ˢ Metric.closedBall d.z₁ 1 :=
      ⟨Metric.ball_subset_closedBall hc, Metric.ball_subset_closedBall hz⟩
    have h1 : M₁ ≤ max 0 (max (max M₁ M₂) (max M₃ M₄)) :=
      le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    have h2 : M₂ ≤ max 0 (max (max M₁ M₂) (max M₃ M₄)) :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    have h3 : M₃ ≤ max 0 (max (max M₁ M₂) (max M₃ M₄)) :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have h4 : M₄ ≤ max 0 (max (max M₁ M₂) (max M₃ M₄)) :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    exact ⟨le_trans (hM₁ (c, z) hmem) h1, le_trans (hM₂ (c, z) hmem) h2,
      le_trans (hM₃ (c, z) hmem) h3, le_trans (hM₄ (c, z) hmem) h4⟩
  · exact (Continuous.prodMk continuous_Zr_five
      (Continuous.prodMk continuous_Ar_five
        (Continuous.prodMk continuous_Br_five continuous_Cr_five))).continuousOn

end Work.PARIMPL.ParSplit
