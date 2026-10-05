import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPV.levelPt_omega

/-!
# B5: the collar region `x < -√2` of the assembled family is Lagrangian

For `x < -√2` the assembled family `lagPt W Γc Ac rho` agrees, in a *neighbourhood* of `x`
(and for every `t`), with the collar point
`levelPt (Γc τ (sig x) t) (sig x) (Ac τ (sig x) t)` of
`Submission/Work/RPB/B5/Defs.lean` (`sig x = x²/2 - 1 > 0` there, so `x` lies in the interior of
the collar's range `x ≤ -√2`).

Write `F τ σ t = levelPt (Γc τ σ t) σ (Ac τ σ t)` for the collar family.  Then

* `∂_x (lagPt …τ · t) x = sig'(x) • ∂_σ F` (chain rule, since `lagPt = F (sig ·) t` near `x`);
* `∂_t (lagPt …τ x ·) t = ∂_t F` (the two functions agree *everywhere* in `t`);
* `symp (c • v) w = c * symp v w` (`symp` is `ℝ`-linear in its first argument);

so the assertion reduces to the collar's Lagrangian condition

`symp (∂_σ F) (∂_t F) = ω_ℂ(∂_σ Γc) (∂_t Γc) - ∂_t Ac = 0`,

which is `Work.RPV.levelPt_omega` combined with the Lagrangian condition `hlag` of `LagData`.

The differentiability of the collar slices in `σ` and in `t` is *not* immediate from the
smoothness fields `hΓsm`/`hAsm` of `LagData`: these are `ContDiffOn` statements on
`Set.Icc 0 1 ×ˢ Set.univ ×ˢ Set.Ici 0` — the `×ˢ` is right associative, so the constraint
`Ici 0` applies to the *third* argument `t`, and `τ` is constrained to `Icc 0 1`.  Since `Γc` is
`2π`-periodic in `t` and `Ac` satisfies `Ac τ σ (t + 2π) = Ac τ σ t + 2π`, the values for
`t < 0` are determined by those for `t ≥ 0` and differentiability transfers (the slices through
a point `(τ, σ, t + 2πk)` with `t + 2πk > 0` stay inside the constraint set for `τ ∈ Icc 0 1`).
This is `slice_derivs_of_quasi_periodic` below, applied with `c = 0` for `Γc` and `c = 2π`
for `Ac`.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- `symp` is `ℝ`-homogeneous in its first argument. -/
private lemma symp_smul_fst (c : ℝ) (a b : Work.RPV.PS) :
    Work.RPV.symp (c • a) b = c * Work.RPV.symp (a) (b) := by
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := a
  obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := b
  simp [Work.RPV.symp]
  ring

/-- Chain rule in the form used below: for `F : ℝ → E` differentiable at `g x` and
`g : ℝ → ℝ` differentiable at `x`, the derivative of `y ↦ F (g y)` at `x` is
`g'(x) • F'(g x)`. -/
private lemma deriv_comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (g : ℝ → ℝ) (x : ℝ) (hF : DifferentiableAt ℝ F (g x))
    (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => F (g y)) x = deriv g x • deriv F (g x) := by
  have h := hF.hasFDerivAt.comp_hasDerivAt x hg.hasDerivAt
  have hd : deriv (fun y => F (g y)) x = fderiv ℝ F (g x) (deriv g x) := by
    simpa only [Function.comp_def] using h.deriv
  rw [hd, fderiv_eq_smul_deriv]

/-- Iterating the quasi-periodicity relation `f τ σ (t + 2π) = f τ σ t + c`. -/
private lemma quasi_periodic_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E)
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c) (k : ℕ) (τ σ t : ℝ) :
    f τ σ (t + 2 * Real.pi * (k : ℝ)) = f τ σ t + (k : ℝ) • c := by
  induction k generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    rw [show t + 2 * Real.pi * ((n : ℝ) + 1) = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi by ring]
    rw [hper τ σ (t + 2 * Real.pi * (n : ℝ)), ih t]
    rw [add_smul, one_smul]
    abel

/-- **Slicing a half-space-smooth quasi-periodic family.**  If `f : ℝ → ℝ → ℝ → E` is `C⁸`
jointly on the set where the *third* argument `t` is `≥ 0` (and the first argument lies in `s`),
and is quasi-periodic in `t` with shift `c`, then `f` is determined on the whole of `ℝ³` by its
values for `t ≥ 0`, and every `σ`- and `t`-slice through a point with first coordinate in `s` is
differentiable (with the derivative being `deriv`, as always for `HasDerivAt`). -/
private lemma slice_derivs_of_quasi_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E) (s : Set ℝ)
    (hsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (s ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)))
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c) :
    ∀ τ ∈ s, ∀ σ t, HasDerivAt (fun u => f τ u t) (deriv (fun u => f τ u t) σ) σ ∧
      HasDerivAt (fun u => f τ σ u) (deriv (fun u => f τ σ u) t) t := by
  intro τ hτ σ t
  -- a shift of `t` into the half-space `{t ≥ 0}`, where `hsm` applies
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < t + 2 * Real.pi * (k : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (-t / (2 * Real.pi))
    refine ⟨k, ?_⟩
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := mul_lt_mul_of_pos_right hk hπ
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h
    linarith
  have hperk := quasi_periodic_nat f c hper k τ
  set F : ℝ × (ℝ × ℝ) → E := fun z => f z.1 z.2.1 z.2.2 with hF
  have hpt : (τ, (σ, t + 2 * Real.pi * (k : ℝ))) ∈ s ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ) :=
    ⟨hτ, Set.mem_univ _, le_of_lt hk⟩
  have hFw : ContDiffWithinAt ℝ 8 F (s ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ))
      (τ, (σ, t + 2 * Real.pi * (k : ℝ))) := by
    rw [hF]
    exact hsm.contDiffWithinAt hpt
  -- the `σ`-slice (the whole line `u ↦ (τ, (u, t + 2πk))` stays in the constraint set)
  have hσcd : ContDiffAt ℝ 8 (fun u : ℝ => f τ u (t + 2 * Real.pi * (k : ℝ))) σ := by
    have hg : ContDiffWithinAt ℝ 8 (fun u : ℝ => (τ, (u, t + 2 * Real.pi * (k : ℝ))))
        Set.univ σ :=
      (by fun_prop :
        ContDiff ℝ 8 (fun u : ℝ => (τ, (u, t + 2 * Real.pi * (k : ℝ))))).contDiffWithinAt
    have hmt : Set.MapsTo (fun u : ℝ => (τ, (u, t + 2 * Real.pi * (k : ℝ)))) Set.univ
        (s ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) := fun u _ => ⟨hτ, Set.mem_univ _, le_of_lt hk⟩
    simpa only [hF, Function.comp_def] using (hFw.comp σ hg hmt).contDiffAt (by simp)
  have hσslice : DifferentiableAt ℝ (fun u : ℝ => f τ u t) σ := by
    have heq : (fun u : ℝ => f τ u t)
        = fun u : ℝ => f τ u (t + 2 * Real.pi * (k : ℝ)) - (k : ℝ) • c := by
      funext u
      rw [hperk u t]
      abel
    rw [heq]
    exact (hσcd.differentiableAt (by norm_num)).sub_const _
  -- the `t`-slice (the ray where `u ↦ u + 2πk ≥ 0` stays in the constraint set)
  have htcd : ContDiffAt ℝ 8 (fun u : ℝ => f τ σ (u + 2 * Real.pi * (k : ℝ))) t := by
    have hU : Set.Ici (-(2 * Real.pi * (k : ℝ))) ∈ 𝓝 t := by
      apply Ici_mem_nhds
      linarith
    have hg : ContDiffWithinAt ℝ 8 (fun u : ℝ => (τ, (σ, u + 2 * Real.pi * (k : ℝ))))
        (Set.Ici (-(2 * Real.pi * (k : ℝ)))) t :=
      (by fun_prop :
        ContDiff ℝ 8 (fun u : ℝ => (τ, (σ, u + 2 * Real.pi * (k : ℝ))))).contDiffWithinAt
    have hmt : Set.MapsTo (fun u : ℝ => (τ, (σ, u + 2 * Real.pi * (k : ℝ))))
        (Set.Ici (-(2 * Real.pi * (k : ℝ)))) (s ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
      intro u hu
      have hu' : -(2 * Real.pi * (k : ℝ)) ≤ u := hu
      exact ⟨hτ, Set.mem_univ _, Set.mem_Ici.mpr (by linarith)⟩
    exact (hFw.comp t hg hmt).contDiffAt hU
  have htslice : DifferentiableAt ℝ (fun u : ℝ => f τ σ u) t := by
    have heq : (fun u : ℝ => f τ σ u)
        = fun u : ℝ => f τ σ (u + 2 * Real.pi * (k : ℝ)) - (k : ℝ) • c := by
      funext u
      rw [hperk σ u]
      abel
    rw [heq]
    exact (htcd.differentiableAt (by norm_num)).sub_const _
  exact ⟨hσslice.hasDerivAt, htslice.hasDerivAt⟩

theorem collar_region_lag (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x, x < -Real.sqrt 2 → ∀ t,
      Work.RPV.symp
        (deriv (fun y => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ y t) x)
        (deriv (fun s => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x s) t) = 0 := by
  intro τ hτ x hx t
  have hxle : x ≤ -Real.sqrt 2 := le_of_lt hx
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hx0 : x ≤ 0 := le_of_lt (by linarith)
  -- the `x`-derivative: `lagPt` agrees with the collar family near `x`
  have hev : (fun y => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ y t) =ᶠ[𝓝 x]
      (fun y => Work.RPV.levelPt (D.Γc τ (Work.RPB.B5.sig y) t) (Work.RPB.B5.sig y)
        (D.Ac τ (Work.RPB.B5.sig y) t)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    have hy' : y < -Real.sqrt 2 := hy
    have hy0 : y ≤ 0 := le_of_lt (by linarith)
    simp only [Work.RPB.B5.lagPt, Work.RPB.B5.basePt, Work.RPB.B5.collarPt]
    rw [ite_eq_left hy0, ite_eq_left (le_of_lt hy')]
  rw [hev.deriv_eq]
  -- differentiability of the collar slices (see the module docstring)
  have hΓslice := slice_derivs_of_quasi_periodic D.Γc 0 (Set.Icc (0 : ℝ) 1) D.hΓsm
    (fun τ σ t => by rw [D.hΓper τ σ t, add_zero])
  have hAslice := slice_derivs_of_quasi_periodic D.Ac (2 * Real.pi) (Set.Icc (0 : ℝ) 1) D.hAsm
    (fun τ σ t => D.hAper τ σ t)
  have hΓσ := (hΓslice τ hτ (Work.RPB.B5.sig x) t).1
  have hΓt := (hΓslice τ hτ (Work.RPB.B5.sig x) t).2
  have hAσ := (hAslice τ hτ (Work.RPB.B5.sig x) t).1
  have hAt := (hAslice τ hτ (Work.RPB.B5.sig x) t).2
  have hF1 := Work.RPV.hasDerivAt_levelPt_fst (fun σ u => D.Γc τ σ u) (fun σ u => D.Ac τ σ u)
      (Work.RPB.B5.sig x) t (deriv (fun s => D.Γc τ s t) (Work.RPB.B5.sig x))
      (deriv (fun s => D.Ac τ s t) (Work.RPB.B5.sig x)) hΓσ hAσ
  have hFdiff : DifferentiableAt ℝ
      (fun σ : ℝ => Work.RPV.levelPt (D.Γc τ σ t) σ (D.Ac τ σ t)) (Work.RPB.B5.sig x) :=
    hF1.differentiableAt
  have hsigdiff : DifferentiableAt ℝ Work.RPB.B5.sig x := by
    unfold Work.RPB.B5.sig
    fun_prop
  rw [deriv_comp_smul _ _ _ hFdiff hsigdiff]
  -- the `t`-derivative: the two functions agree for all `t`
  have hfun2 : (fun s => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x s) =
      (fun s => Work.RPV.levelPt (D.Γc τ (Work.RPB.B5.sig x) s) (Work.RPB.B5.sig x)
        (D.Ac τ (Work.RPB.B5.sig x) s)) := by
    funext s
    simp only [Work.RPB.B5.lagPt, Work.RPB.B5.basePt, Work.RPB.B5.collarPt]
    rw [ite_eq_left hx0, ite_eq_left hxle]
  rw [hfun2]
  rw [symp_smul_fst]
  -- the collar's Lagrangian condition
  have homega := Work.RPV.levelPt_omega (fun σ u => D.Γc τ σ u) (fun σ u => D.Ac τ σ u)
      (Work.RPB.B5.sig x) t (deriv (fun s => D.Γc τ s t) (Work.RPB.B5.sig x))
      (deriv (fun s => D.Γc τ (Work.RPB.B5.sig x) s) t)
      (deriv (fun s => D.Ac τ s t) (Work.RPB.B5.sig x))
      (deriv (fun s => D.Ac τ (Work.RPB.B5.sig x) s) t) hΓσ hΓt hAσ hAt
  rw [homega, D.hlag τ (Work.RPB.B5.sig x) t, sub_self, mul_zero]

end Work.RPB.B5
