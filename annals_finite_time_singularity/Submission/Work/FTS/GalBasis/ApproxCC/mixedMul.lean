/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Leibniz rule for the mixed operators `D_z^a D_θ^b` on globally `C^9` functions

`Work.Spaces.mixed a b h = D_z^a D_θ^b h` where `D_z f = z ∂_z f` and
`D_θ f = sin(2θ) ∂_θ f`; both are derivations with respect to the pointwise product, so
the iterated Leibniz rule

`D_z^a D_θ^b (f·g) = ∑_{i ≤ a} ∑_{j ≤ b} C(a,i) C(b,j) (D_z^i D_θ^j f)(D_z^{a-i} D_θ^{b-j} g)`

holds.  This file proves it for globally `C^9` functions of `(z,θ)`, for all `a + b ≤ 4`
and **all** `(z,θ) ∈ ℝ²` (no restriction to the closed quadrant is needed, and none is
available: the hypotheses are only of finite order, so the machinery of
`Submission.Work.Spaces.mixed_mul_eq` — which is stated for `C^∞`/analytic functions on the
open quadrant — does not apply).

The proof is a direct induction on the pair `(a,b)`:
`D_z^a D_θ^b = D_z (D_z^{a-1} D_θ^b)` resp. `D_θ (D_z^a D_θ^{b-1})`, one application of the
product rule for `D_z` resp. `D_θ`, and the Pascal identity `Work.Spaces.leibniz_step` to
recombine the two shifted binomial sums.  The differentiability side conditions are
discharged from the global `C^9` hypothesis through the smoothness of the iterates
`Zb^a Tb^b` of the operators acting on uncurried functions.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.ApproxCC.Defs
import Submission.Work.Spaces.mixed_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Work.Spaces

namespace Work.FTS.GalBasis.ApproxCC

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Smoothness of the iterates `Zb^a Tb^b`

Each application of `Zb = z ∂_z` or `Tb = sin(2θ) ∂_θ` lowers the order of a *global*
`C^n`-regularity on `ℝ × ℝ` by one.  The statement is phrased with the "shifted" form
`k + M` so that no truncated subtraction of natural numbers is needed. -/

private lemma natCast_succ_add (n : ℕ) :
    (((n : ℕ) : WithTop ENat)) + 1 = (((n + 1 : ℕ)) : WithTop ENat) := by
  push_cast
  ring

private lemma Zb_contDiff_succ {u : ℝ × ℝ → ℝ} {n : ℕ}
    (h : ContDiff ℝ (((n + 1 : ℕ)) : WithTop ENat) u) :
    ContDiff ℝ ((n : ℕ) : WithTop ENat) (Zb u) := by
  have h1 : ContDiff ℝ (1 : WithTop ENat) u :=
    h.of_le (by exact_mod_cast Nat.succ_pos n)
  have hfd : ContDiff ℝ ((n : ℕ) : WithTop ENat) (fderiv ℝ u) :=
    h.fderiv_right (m := ((n : ℕ) : WithTop ENat)) (natCast_succ_add n).le
  have happ : ContDiff ℝ ((n : ℕ) : WithTop ENat)
      (fun p : ℝ × ℝ => (fderiv ℝ u p) (1, 0)) := hfd.clm_apply contDiff_const
  have hmul : ContDiff ℝ ((n : ℕ) : WithTop ENat)
      (fun p : ℝ × ℝ => p.1 * (fderiv ℝ u p) (1, 0)) := contDiff_fst.mul happ
  have hZb : Zb u = fun p : ℝ × ℝ => p.1 * (fderiv ℝ u p) (1, 0) := by
    funext p
    obtain ⟨z, θ⟩ := p
    have hdiff : DifferentiableAt ℝ u (z, θ) :=
      (h1.differentiable (by norm_num) : Differentiable ℝ u) (z, θ)
    simp only [Zb]
    rw [deriv_slice_fst u z θ hdiff]
  rw [hZb]
  exact hmul

private lemma Tb_contDiff_succ {u : ℝ × ℝ → ℝ} {n : ℕ}
    (h : ContDiff ℝ (((n + 1 : ℕ)) : WithTop ENat) u) :
    ContDiff ℝ ((n : ℕ) : WithTop ENat) (Tb u) := by
  have h1 : ContDiff ℝ (1 : WithTop ENat) u :=
    h.of_le (by exact_mod_cast Nat.succ_pos n)
  have hfd : ContDiff ℝ ((n : ℕ) : WithTop ENat) (fderiv ℝ u) :=
    h.fderiv_right (m := ((n : ℕ) : WithTop ENat)) (natCast_succ_add n).le
  have happ : ContDiff ℝ ((n : ℕ) : WithTop ENat)
      (fun p : ℝ × ℝ => (fderiv ℝ u p) (0, 1)) := hfd.clm_apply contDiff_const
  have hsin : ContDiff ℝ ((n : ℕ) : WithTop ENat)
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).of_le le_top
  have hmul : ContDiff ℝ ((n : ℕ) : WithTop ENat)
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ u p) (0, 1)) := hsin.mul happ
  have hTb : Tb u = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (fderiv ℝ u p) (0, 1) := by
    funext p
    obtain ⟨z, θ⟩ := p
    have hdiff : DifferentiableAt ℝ u (z, θ) :=
      (h1.differentiable (by norm_num) : Differentiable ℝ u) (z, θ)
    simp only [Tb]
    rw [deriv_slice_snd u z θ hdiff]
  rw [hTb]
  exact hmul

private lemma Zb_iterate_contDiff (u : ℝ × ℝ → ℝ) :
    ∀ (k M : ℕ), ContDiff ℝ (((k + M : ℕ)) : WithTop ENat) u →
      ContDiff ℝ ((M : ℕ) : WithTop ENat) (Zb^[k] u) := by
  intro k
  induction k with
  | zero => intro M h; simpa using h
  | succ k ih =>
      intro M h
      have h1 : ContDiff ℝ (((k + (M + 1) : ℕ)) : WithTop ENat) u :=
        h.of_le (by exact_mod_cast (by omega : k + (M + 1) ≤ k + 1 + M))
      have h2 : ContDiff ℝ (((M + 1 : ℕ)) : WithTop ENat) (Zb^[k] u) := ih (M + 1) h1
      rw [Function.iterate_succ_apply']
      exact Zb_contDiff_succ h2

private lemma Tb_iterate_contDiff (u : ℝ × ℝ → ℝ) :
    ∀ (k M : ℕ), ContDiff ℝ (((k + M : ℕ)) : WithTop ENat) u →
      ContDiff ℝ ((M : ℕ) : WithTop ENat) (Tb^[k] u) := by
  intro k
  induction k with
  | zero => intro M h; simpa using h
  | succ k ih =>
      intro M h
      have h1 : ContDiff ℝ (((k + (M + 1) : ℕ)) : WithTop ENat) u :=
        h.of_le (by exact_mod_cast (by omega : k + (M + 1) ≤ k + 1 + M))
      have h2 : ContDiff ℝ (((M + 1 : ℕ)) : WithTop ENat) (Tb^[k] u) := ih (M + 1) h1
      rw [Function.iterate_succ_apply']
      exact Tb_contDiff_succ h2

/-! ## The mixed derivatives of a `C^9` function and their slices -/

private lemma mixed_contDiff {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 9 (Function.uncurry f))
    (i j : ℕ) (hij : i + j ≤ 4) :
    ContDiff ℝ (5 : WithTop ENat) (Function.uncurry (Work.Spaces.mixed i j f)) := by
  have heq : Function.uncurry (Work.Spaces.mixed i j f)
      = Zb^[i] (Tb^[j] (Function.uncurry f)) := by
    rw [show Work.Spaces.mixed i j f = Work.Spaces.DzIter i (Work.Spaces.DthIter j f)
          from rfl,
      ← Work.Spaces.Zb_iterate_uncurry i (Work.Spaces.DthIter j f),
      ← Work.Spaces.Tb_iterate_uncurry j f]
  rw [heq]
  have h1 : ContDiff ℝ (((j + (i + 5) : ℕ)) : WithTop ENat) (Function.uncurry f) :=
    hf.of_le (by exact_mod_cast (by omega : j + (i + 5) ≤ 9))
  have h2 : ContDiff ℝ (((i + 5 : ℕ)) : WithTop ENat) (Tb^[j] (Function.uncurry f)) :=
    Tb_iterate_contDiff (Function.uncurry f) j (i + 5) h1
  exact Zb_iterate_contDiff (Tb^[j] (Function.uncurry f)) i 5 h2

private lemma mixed_diff_z {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 9 (Function.uncurry f))
    (i j : ℕ) (hij : i + j ≤ 4) (z θ : ℝ) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j f z' θ) z :=
  differentiableAt_slice_fst
    ((mixed_contDiff hf i j hij).differentiable (by norm_num) (z, θ))

private lemma mixed_diff_θ {f : ℝ → ℝ → ℝ} (hf : ContDiff ℝ 9 (Function.uncurry f))
    (i j : ℕ) (hij : i + j ≤ 4) (z θ : ℝ) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j f z θ') θ :=
  differentiableAt_slice_snd
    ((mixed_contDiff hf i j hij).differentiable (by norm_num) (z, θ))

/-! ## Product rule and linearity for `D_z` and `D_θ` -/

private lemma Dz_mul {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => u z θ * v z θ) z θ
      = Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ := by
  show z * deriv (fun z' : ℝ => u z' θ * v z' θ) z
      = z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z)
  rw [show deriv (fun z' : ℝ => u z' θ * v z' θ) z
        = deriv ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) z from rfl]
  rw [deriv_mul hu hv]
  ring

private lemma Dz_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun z' => u z' θ) z)
    (hv : DifferentiableAt ℝ (fun z' => v z' θ) z) :
    Work.Spaces.Dz (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dz u z θ * v z θ + u z θ * Work.Spaces.Dz v z θ) := by
  show z * deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
      = cc * (z * deriv (fun z' : ℝ => u z' θ) z * v z θ
        + u z θ * (z * deriv (fun z' : ℝ => v z' θ) z))
  rw [show deriv (fun z' : ℝ => cc * (u z' θ * v z' θ)) z
        = deriv (fun y => cc * ((fun z' : ℝ => u z' θ) * (fun z' : ℝ => v z' θ)) y) z from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dz_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => A i z' θ) z) :
    Work.Spaces.Dz (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dz (A i) z θ := by
  have hfun : (fun z' : ℝ => ∑ i ∈ s, A i z' θ) = (∑ i ∈ s, fun z' : ℝ => A i z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  show z * deriv (fun z' : ℝ => ∑ i ∈ s, A i z' θ) z
      = ∑ i ∈ s, z * deriv (fun z' : ℝ => A i z' θ) z
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma Dth_mul {u v : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => u z θ * v z θ) z θ
      = Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ' * v z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ)
  rw [show deriv (fun θ' : ℝ => u z θ' * v z θ') θ
        = deriv ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) θ from rfl]
  rw [deriv_mul hu hv]
  ring

private lemma Dth_cmul {u v : ℝ → ℝ → ℝ} {z θ : ℝ} (cc : ℝ)
    (hu : DifferentiableAt ℝ (fun θ' => u z θ') θ)
    (hv : DifferentiableAt ℝ (fun θ' => v z θ') θ) :
    Work.Spaces.Dth (fun z θ => cc * (u z θ * v z θ)) z θ
      = cc * (Work.Spaces.Dth u z θ * v z θ + u z θ * Work.Spaces.Dth v z θ) := by
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
      = cc * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => u z θ') θ * v z θ
        + u z θ * (Real.sin (2 * θ) * deriv (fun θ' : ℝ => v z θ') θ))
  rw [show deriv (fun θ' : ℝ => cc * (u z θ' * v z θ')) θ
        = deriv (fun y => cc * ((fun θ' : ℝ => u z θ') * (fun θ' : ℝ => v z θ')) y) θ from rfl]
  rw [deriv_const_mul cc (hu.mul hv), deriv_mul hu hv]
  ring

private lemma Dth_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (fun θ' => A i z θ') θ) :
    Work.Spaces.Dth (fun z θ => ∑ i ∈ s, A i z θ) z θ
      = ∑ i ∈ s, Work.Spaces.Dth (A i) z θ := by
  have hfun : (fun θ' : ℝ => ∑ i ∈ s, A i z θ') = (∑ i ∈ s, fun θ' : ℝ => A i z θ') := by
    funext θ'
    rw [Finset.sum_apply]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => ∑ i ∈ s, A i z θ') θ
      = ∑ i ∈ s, Real.sin (2 * θ) * deriv (fun θ' : ℝ => A i z θ') θ
  rw [hfun, deriv_sum h, Finset.mul_sum]

private lemma differentiableAt_sum {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {z : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) z) :
    DifferentiableAt ℝ (fun z' => ∑ i ∈ s, A i z') z := by
  have hfun : (fun z' => ∑ i ∈ s, A i z') = (∑ i ∈ s, A i) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

private lemma differentiableAt_sum_θ {ι : Type*} (s : Finset ι) (A : ι → ℝ → ℝ) {θ : ℝ}
    (h : ∀ i ∈ s, DifferentiableAt ℝ (A i) θ) :
    DifferentiableAt ℝ (fun θ' => ∑ i ∈ s, A i θ') θ := by
  have hfun : (fun θ' => ∑ i ∈ s, A i θ') = (∑ i ∈ s, A i) := by
    funext θ'
    rw [Finset.sum_apply]
  rw [hfun]
  exact DifferentiableAt.sum h

/-! ## The Leibniz rule -/

theorem mixedMul {f g : ℝ → ℝ → ℝ}
    (hf : ContDiff ℝ 9 (Function.uncurry f)) (hg : ContDiff ℝ 9 (Function.uncurry g)) :
    ∀ a b : ℕ, a + b ≤ 4 → ∀ z θ : ℝ,
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) *
            (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
  have hfz : ∀ i j : ℕ, i + j ≤ 4 → ∀ z θ : ℝ,
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j f z' θ) z :=
    fun i j hij z θ => mixed_diff_z hf i j hij z θ
  have hgz : ∀ i j : ℕ, i + j ≤ 4 → ∀ z θ : ℝ,
      DifferentiableAt ℝ (fun z' => Work.Spaces.mixed i j g z' θ) z :=
    fun i j hij z θ => mixed_diff_z hg i j hij z θ
  have hfθ : ∀ i j : ℕ, i + j ≤ 4 → ∀ z θ : ℝ,
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j f z θ') θ :=
    fun i j hij z θ => mixed_diff_θ hf i j hij z θ
  have hgθ : ∀ i j : ℕ, i + j ≤ 4 → ∀ z θ : ℝ,
      DifferentiableAt ℝ (fun θ' => Work.Spaces.mixed i j g z θ') θ :=
    fun i j hij z θ => mixed_diff_θ hg i j hij z θ
  have key : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → a + b ≤ 4 → ∀ z θ : ℝ,
      Work.Spaces.mixed a b (fun z θ => f z θ * g z θ) z θ =
        ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) *
            (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a - i) (b - j) g z θ) := by
    intro n
    induction n with
    | zero =>
        intro a b hsum h4 z θ
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha
        subst hb
        simp [Work.Spaces.mixed]
    | succ n ih =>
        intro a b hsum h4 z θ
        rcases Nat.eq_zero_or_pos a with ha | ha
        · subst ha
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb
            simp [Work.Spaces.mixed]
          · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
            have hs : 0 + b' ≤ n := by omega
            have h4' : 0 + b' ≤ 4 := by omega
            have hIHfun : Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ) =
                (fun z θ => ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) := by
              funext z' θ'
              exact ih 0 b' hs h4' z' θ'
            have hL : Work.Spaces.mixed 0 (b' + 1) (fun z θ => f z θ * g z θ) z θ
                = Work.Spaces.Dth
                    (Work.Spaces.mixed 0 b' (fun z θ => f z θ * g z θ)) z θ := by
              simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DzIter_zero]
            rw [hL, hIHfun]
            have hstep1 : Work.Spaces.Dth (fun z θ => ∑ i ∈ Finset.range (0 + 1),
                  ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ)) z θ
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                  (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                    (Work.Spaces.mixed i (j + 1) f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ) := by
              rw [Dth_sum (Finset.range (0 + 1))
                    (fun i z θ => ∑ j ∈ Finset.range (b' + 1),
                      (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun i hi => differentiableAt_sum_θ (Finset.range (b' + 1))
                      (fun j θ' => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ' * Work.Spaces.mixed (0 - i) (b' - j) g z θ'))
                      (fun j hj => ((hfθ i j (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ).mul
                        (hgθ (0 - i) (b' - j) (by
                            have := Finset.mem_range.mp hi
                            have := Finset.mem_range.mp hj
                            omega) z θ)).const_mul _))]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [Dth_sum (Finset.range (b' + 1))
                    (fun j z θ => (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' - j) g z θ))
                    z θ
                    (fun j hj => ((hfθ i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ).mul
                      (hgθ (0 - i) (b' - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ)).const_mul _)]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hi0 : i = 0 := by have := Finset.mem_range.mp hi; omega
              rw [Dth_cmul (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ))
                    (hfθ i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ)
                    (hgθ (0 - i) (b' - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ)]
              rw [show Work.Spaces.Dth (Work.Spaces.mixed i j f) z θ
                    = Work.Spaces.mixed i (j + 1) f z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero],
                  show Work.Spaces.Dth (Work.Spaces.mixed (0 - i) (b' - j) g) z θ
                    = Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ from by
                    rw [show i = 0 from hi0]
                    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ,
                      Work.Spaces.DzIter_zero, Nat.sub_zero]]
            have hstep2 : (∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                = ∑ i ∈ Finset.range (0 + 1), ∑ j ∈ Finset.range (b' + 1 + 1),
                    (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
              refine Finset.sum_congr rfl fun i hi => ?_
              have h1 : (∑ j ∈ Finset.range (b' + 1),
                    (((0 : ℕ).choose i : ℝ) * (b'.choose j : ℝ)) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ))
                  = ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1), (b'.choose j : ℝ) *
                      (Work.Spaces.mixed i (j + 1) f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j) g z θ
                        + Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' - j + 1) g z θ)) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              rw [h1, leibniz_step b' (fun j => Work.Spaces.mixed i j f z θ)
                    (fun m => Work.Spaces.mixed (0 - i) m g z θ)]
              have h2 : ((0 : ℕ).choose i : ℝ) * (∑ j ∈ Finset.range (b' + 1 + 1),
                    ((b' + 1).choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ))
                  = ∑ j ∈ Finset.range (b' + 1 + 1),
                      (((0 : ℕ).choose i : ℝ) * ((b' + 1).choose j : ℝ)) *
                        (Work.Spaces.mixed i j f z θ
                          * Work.Spaces.mixed (0 - i) (b' + 1 - j) g z θ) := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
              exact h2
            rw [hstep1, hstep2]
        · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
          have hs : a' + b ≤ n := by omega
          have h4' : a' + b ≤ 4 := by omega
          have hIHfun : Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ) =
              (fun z θ => ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ)) := by
            funext z' θ'
            exact ih a' b hs h4' z' θ'
          have hL : Work.Spaces.mixed (a' + 1) b (fun z θ => f z θ * g z θ) z θ
              = Work.Spaces.Dz (Work.Spaces.mixed a' b (fun z θ => f z θ * g z θ)) z θ := by
            simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]
          rw [hL, hIHfun]
          have hstep1 : Work.Spaces.Dz (fun z θ => ∑ i ∈ Finset.range (a' + 1),
                ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ)) z θ
              = ∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                  (Work.Spaces.mixed (i + 1) j f z θ
                      * Work.Spaces.mixed (a' - i) (b - j) g z θ
                    + Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ) := by
            rw [Dz_sum (Finset.range (a' + 1))
                  (fun i z θ => ∑ j ∈ Finset.range (b + 1),
                    ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun i hi => differentiableAt_sum (Finset.range (b + 1))
                    (fun j z' => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                      (Work.Spaces.mixed i j f z' θ * Work.Spaces.mixed (a' - i) (b - j) g z' θ))
                    (fun j hj => ((hfz i j (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ).mul
                      (hgz (a' - i) (b - j) (by
                          have := Finset.mem_range.mp hi
                          have := Finset.mem_range.mp hj
                          omega) z θ)).const_mul _))]
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Dz_sum (Finset.range (b + 1))
                  (fun j z θ => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed i j f z θ * Work.Spaces.mixed (a' - i) (b - j) g z θ))
                  z θ
                  (fun j hj => ((hfz i j (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ).mul
                    (hgz (a' - i) (b - j) (by
                        have := Finset.mem_range.mp hi
                        have := Finset.mem_range.mp hj
                        omega) z θ)).const_mul _)]
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Dz_cmul ((a'.choose i : ℝ) * (b.choose j : ℝ))
                  (hfz i j (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ)
                  (hgz (a' - i) (b - j) (by
                      have := Finset.mem_range.mp hi
                      have := Finset.mem_range.mp hj
                      omega) z θ)]
            rw [show Work.Spaces.Dz (Work.Spaces.mixed i j f) z θ
                  = Work.Spaces.mixed (i + 1) j f z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ],
                show Work.Spaces.Dz (Work.Spaces.mixed (a' - i) (b - j) g) z θ
                  = Work.Spaces.mixed (a' - i + 1) (b - j) g z θ from by
                  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ]]
          have hstep2 : (∑ i ∈ Finset.range (a' + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
              = ∑ i ∈ Finset.range (a' + 1 + 1), ∑ j ∈ Finset.range (b + 1),
                  ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
            have hkey1 := Finset.sum_comm (s := Finset.range (a' + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                (Work.Spaces.mixed (i + 1) j f z θ
                    * Work.Spaces.mixed (a' - i) (b - j) g z θ
                  + Work.Spaces.mixed i j f z θ
                    * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
            have hkey2 := Finset.sum_comm (s := Finset.range (a' + 1 + 1))
              (t := Finset.range (b + 1))
              (f := fun i j => ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                (Work.Spaces.mixed i j f z θ
                  * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
            rw [hkey1, hkey2]
            refine Finset.sum_congr rfl fun j hj => ?_
            have h1 : (∑ i ∈ Finset.range (a' + 1),
                  ((a'.choose i : ℝ) * (b.choose j : ℝ)) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ))
                = (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1), (a'.choose i : ℝ) *
                    (Work.Spaces.mixed (i + 1) j f z θ
                        * Work.Spaces.mixed (a' - i) (b - j) g z θ
                      + Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' - i + 1) (b - j) g z θ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [h1, leibniz_step a' (fun i => Work.Spaces.mixed i j f z θ)
                  (fun m => Work.Spaces.mixed m (b - j) g z θ)]
            have h2 : (b.choose j : ℝ) * (∑ i ∈ Finset.range (a' + 1 + 1),
                  ((a' + 1).choose i : ℝ) *
                    (Work.Spaces.mixed i j f z θ
                      * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ))
                = ∑ i ∈ Finset.range (a' + 1 + 1),
                    ((a' + 1).choose i : ℝ) * (b.choose j : ℝ) *
                      (Work.Spaces.mixed i j f z θ
                        * Work.Spaces.mixed (a' + 1 - i) (b - j) g z θ) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            exact h2
          rw [hstep1, hstep2]
  intro a b hab z θ
  exact key (a + b) a b le_rfl hab z θ

end Work.FTS.GalBasis.ApproxCC
