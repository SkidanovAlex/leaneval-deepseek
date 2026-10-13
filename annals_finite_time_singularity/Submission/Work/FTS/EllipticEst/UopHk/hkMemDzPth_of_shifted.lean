/-
Copyright: work module for the Elgindi finite-time singularity project.

# `UopHk/hkMemDzPth_of_shifted` — the radial shift `∂_θΨ ∈ ℋ^{k+1} ⟹ D_z∂_θΨ ∈ ℋ^k`

The target of this file is

  `HkMem α k (D_z (∂_θΨ))`, from `SmoothOpen (∂_θΨ)` and `HkMem α (k+1) (∂_θΨ)`.

Mathematically nothing new is needed: `D_z = z ∂_z` only *shifts the index*,

  `D_z^i (D_z f) = D_z^{i+1} f`   (definitional, from `D_z^{i+b} = D_z^i ∘ D_z^b`),

  `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`   (Clairaut for the two curvilinear derivatives),

so *every* summand of `HkIntegrand α k (D_z f)` is a summand of `HkIntegrand α (k+1) f`, with the
same weight.  Hence the pointwise domination

  `HkIntegrand α k (D_z f) z θ ≤ HkIntegrand α (k+1) f z θ`   on `Iz × Iθ`,

and the membership follows from `Work.FTS.LocData.HkMem_of_majorant` with the majorant the
`(k+1)`-integrand of `f` itself (whose slices are integrable by `HkMem α (k+1) f`).

This is the open-quadrant (`SmoothOpen`, genuine `C^∞` on `(0,∞) × (0,π/2)`) instance of the
argument of `Work.FTS.CoercivityFix.QuadPorts.HkMem_Dz_quad`; the only difference from that file
is that smoothness is assumed on the *open quadrant* `Q0 = (0,∞) × (0,π/2)` rather than on the
larger open strip `(-1,∞) × (0,π/2)`, and that smoothness is available only at the finite orders
(`Work.Stability.smoothOrder`), not as analyticity.  Consequently the commutation `D_z`-`D_θ` is
reproved here for an arbitrary open set at the genuine smooth order.

The index shift `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` holds on the *whole* domain
`Iz × Iθ`, not only in the open quadrant: at `z = 0` every `D_z`-iterate of positive order
vanishes, and at an angle with `sin(2θ) = 0` every positive `D_θ`-iterate vanishes, so there both
sides are `0`.

Everything here is proved and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.pz_aux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.SumShiftZ_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.UopHk

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The definitional index shift `D_z^i (D_z f) = D_z^{i+1} f` -/

/-- The `D_z`-iterates of `D_z f` are the `D_z`-iterates of `f`, shifted by one
(this is `Work.Spaces.DzIter_add_right` together with the definitional `D_z^1 = D_z`). -/
theorem DzIter_Dz_eq (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-! ## 2. `D_z` commutes with the iterates of `D_θ` at the genuine smooth order

`Work.Spaces.DzDthIterCommOn` is stated for the analytic order `⊤`; the hypothesis
`SmoothOpen` only supplies `Work.Stability.smoothOrder = ∞`.  The proof below is that of
`Work.FTS.CoercivityFix.QuadPorts.DzDthIterCommOn_quad`, with the fixed strip replaced by an
arbitrary open set. -/

/-- On an open set on which `g` is `C^∞` (genuine smooth order), `D_z` commutes with every
iterate of `D_θ`. -/
theorem Dz_DthIter_comm_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) V :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (hV.mem_nhds hy)).of_le (by simp [Work.Stability.smoothOrder])
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hF
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- On an open set on which `g` is `C^∞` (genuine smooth order), `D_z^b` commutes with
`D_θ^a`. -/
theorem DzIter_DthIter_comm_of_isOpen {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) V := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Dz_DthIter_comm_of_isOpen hV
          (Work.FTS.LocData.contDiffOn_DzIter hV hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-! ## 3. The index shift `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`

* `mixed_Dz_shift_Q0` is the identity on the open quadrant, where Clairaut is available;
* `mixed_Dz_shift` extends it to the whole domain `Iz × Iθ`, where the boundary points are
  handled by the vanishing of the two operators.
-/

/-- **The index shift on the open quadrant.** -/
theorem mixed_Dz_shift_Q0 {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (b a : ℕ) {z θ : ℝ}
    (hQ : (z, θ) ∈ Q0) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hDzf : SmoothOpen (Work.Spaces.Dz f) := hf.Dz
  have h1 : Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := by
    simpa only [Work.Spaces.mixed, Function.uncurry] using
      (DzIter_DthIter_comm_of_isOpen isOpen_Q0 hDzf b a hQ)
  have h2 : Work.Spaces.DzIter b (Work.Spaces.Dz f) = Work.Spaces.DzIter (b + 1) f :=
    DzIter_Dz_eq b f
  have h3 : Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := by
    simpa only [Function.uncurry] using
      (DzIter_DthIter_comm_of_isOpen isOpen_Q0 hf (b + 1) a hQ).symm
  calc Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := h1
    _ = Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ := by rw [h2]
    _ = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := h3
    _ = Work.Spaces.mixed (b + 1) a f z θ := rfl

/-! ### The boundary cases: everything vanishes -/

/-- At `z = 0`, every `D_z`-iterate of order `≥ 1` vanishes. -/
private lemma DzIter_succ_apply_zero (b : ℕ) (H : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.DzIter (b + 1) H 0 θ = 0 := by
  show (0 : ℝ) * Work.Spaces.pz (Work.Spaces.DzIter b H) 0 θ = 0
  rw [zero_mul]

/-- If the `θ`-slice of `H` at `z = 0` vanishes identically, so do all of its `D_θ`-iterates. -/
private lemma DthIter_slice_zero_of_slice_zero (a : ℕ) {H : ℝ → ℝ → ℝ}
    (hH : ∀ θ' : ℝ, H 0 θ' = 0) :
    (fun θ' => Work.Spaces.DthIter a H 0 θ') = fun _ => (0 : ℝ) := by
  induction a with
  | zero => funext θ'; exact hH θ'
  | succ a ih =>
      funext θ'
      have hpth : Work.Spaces.pth (Work.Spaces.DthIter a H) 0 θ' = 0 := by
        show deriv (fun θ'' => Work.Spaces.DthIter a H 0 θ'') θ' = 0
        rw [ih]
        simp
      show Real.sin (2 * θ') * Work.Spaces.pth (Work.Spaces.DthIter a H) 0 θ' = 0
      rw [hpth, mul_zero]

/-- If the `θ`-slice of `H` at a fixed angle vanishes identically in `z`, so do all of its
`D_z`-iterates. -/
private lemma DzIter_apply_of_zslice_zero (b : ℕ) {H : ℝ → ℝ → ℝ} {θ : ℝ}
    (hH : ∀ z' : ℝ, H z' θ = 0) : ∀ z : ℝ, Work.Spaces.DzIter b H z θ = 0 := by
  induction b with
  | zero => exact hH
  | succ b ih =>
      intro z
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b H) z θ = 0 := by
        show deriv (fun z' => Work.Spaces.DzIter b H z' θ) z = 0
        rw [show (fun z' => Work.Spaces.DzIter b H z' θ) = fun _ => (0 : ℝ) from funext ih]
        simp
      show z * Work.Spaces.pz (Work.Spaces.DzIter b H) z θ = 0
      rw [hpz, mul_zero]

/-- At `z = 0`, a mixed derivative of a function whose `θ`-slice at `z = 0` vanishes is zero. -/
private lemma mixed_apply_zero_fst_of_slice_zero (b a : ℕ) {H : ℝ → ℝ → ℝ}
    (hH : ∀ θ' : ℝ, H 0 θ' = 0) (θ : ℝ) : Work.Spaces.mixed b a H 0 θ = 0 := by
  rcases b with _ | b
  · exact congrFun (DthIter_slice_zero_of_slice_zero a hH) θ
  · exact DzIter_succ_apply_zero b (Work.Spaces.DthIter a H) θ

/-- At an angle with `sin(2θ) = 0`, a mixed derivative of angular order `a ≥ 1` vanishes. -/
private lemma mixed_apply_of_sin_zero (b a : ℕ) (ha : 1 ≤ a) (H : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.mixed b a H z θ = 0 := by
  have hslice : ∀ z' : ℝ, Work.Spaces.DthIter a H z' θ = 0 := by
    intro z'
    rcases a with _ | a
    · exact absurd ha (by omega)
    · exact Work.Spaces.DthIter_succ_eq_zero_of_sin_eq_zero a H hs
  exact DzIter_apply_of_zslice_zero b hslice z

/-- **The index shift on the whole domain**:
`D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` on `Iz × Iθ`, for `f` smooth on the open quadrant.
At the interior points this is the commutation of `D_z` and `D_θ`; at `z = 0` and at the angular
endpoints both sides vanish. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hDz0 : ∀ θ' : ℝ, Work.Spaces.Dz f 0 θ' = 0 := fun θ' => by
    show (0 : ℝ) * Work.Spaces.pz f 0 θ' = 0
    rw [zero_mul]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rcases a with _ | a
    · show Work.Spaces.DzIter b (Work.Spaces.Dz f) 0 θ = Work.Spaces.DzIter (b + 1) f 0 θ
      rw [DzIter_Dz_eq]
    · rw [mixed_apply_zero_fst_of_slice_zero b (a + 1) hDz0 θ]
      exact (DzIter_succ_apply_zero b (Work.Spaces.DthIter (a + 1) f) θ).symm
  · by_cases hθin : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · exact mixed_Dz_shift_Q0 hf b a ⟨hzpos, hθin⟩
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθin
      rcases a with _ | a
      · show Work.Spaces.DzIter b (Work.Spaces.Dz f) z θ = Work.Spaces.DzIter (b + 1) f z θ
        rw [DzIter_Dz_eq]
      · rw [mixed_apply_of_sin_zero b (a + 1) (by omega) (Work.Spaces.Dz f) hs]
        exact (mixed_apply_of_sin_zero (b + 1) (a + 1) (by omega) f hs).symm

/-! ## 4. Pointwise domination of the `ℋ^n`-integrands -/

/-- A sum over `i ≤ n` of `F (i+1)` is dominated by the sum over `a ≤ n+1` of `F a` when
`F ≥ 0` (the extra term being `F 0`). -/
private lemma SumSuccRange_le (n : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (n + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (n + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (n + 2), F a)
      = (∑ i ∈ Finset.range (n + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (n + 1)
  linarith [hF 0]

/-- **Every summand of `HkIntegrand α n (D_z f)` is a summand of `HkIntegrand α (n+1) f`**, with
the same weight: the pure summands by `D_z^i (D_z f) = D_z^{i+1} f`, the mixed summands by the
index shift `mixed_Dz_shift`.  Hence the pointwise domination of the two integrands. -/
theorem HkIntegrand_Dz_le_succ (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ
      ≤ Work.Spaces.HkIntegrand α (n + 1) f z θ := by
  set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
  set W : ℝ := Work.Spaces.Wt α z θ with hW
  have hLHS : Work.Spaces.HkIntegrand α n (Work.Spaces.Dz f) z θ
      = (∑ i ∈ Finset.range (n + 1),
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i ∧ i + j ≤ n
              then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have hRHS : Work.Spaces.HkIntegrand α (n + 1) f z θ
      = (∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2)
        + (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2),
            (if 1 ≤ a ∧ a + b ≤ n + 1
              then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) := by
    simp only [Work.Spaces.HkIntegrand, ← hH, ← hW]
  have h1 : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le n
      (fun a => (Work.Spaces.DzIter a f z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz_eq i f])
  have h2 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ * W) ^ 2 else 0))
      = (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [ite_eq_left hc, ite_eq_left hc, mixed_Dz_shift hf j i hz hθ]
    · rw [ite_eq_right hc, ite_eq_right hc]
  have hkey : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
              (if 1 ≤ i ∧ i + j ≤ n
                then (Work.Spaces.mixed (j + 1) i f z θ * W) ^ 2 else 0))
      ≤ (∑ a ∈ Finset.range (n + 2), ∑ b ∈ Finset.range (n + 2),
            (if 1 ≤ a ∧ a + b ≤ n + 1
              then (Work.Spaces.mixed b a f z θ * W) ^ 2 else 0)) :=
    Work.Coercivity.SumShiftZ_le n
      (fun a b => (Work.Spaces.mixed b a f z θ * W) ^ 2) (fun a b => sq_nonneg _)
  have hnn : 0 ≤ ∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  rw [hLHS, hRHS]
  linarith [h1, h2, hkey, hnn]

/-! ## 5. The `ℋ^n`-membership of `D_z f` -/

/-- **The membership step**: for `f` which is `C^∞` on the open quadrant and in `ℋ^{n+1}`, the
radial derivative `D_z f` lies in `ℋ^n`.  This is `Work.FTS.LocData.HkMem_of_majorant` with the
majorant the `(n+1)`-integrand of `f` itself, the pointwise domination being
`HkIntegrand_Dz_le_succ` and the measurability input the continuity of the integrand of `D_z f`
on the open quadrant. -/
theorem HkMem_Dz_of_smoothOpen (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothOpen f)
    (h : Work.Spaces.HkMem α (n + 1) f) : Work.Spaces.HkMem α n (Work.Spaces.Dz f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dz f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    ((SmoothOpen.Dz hf).continuousOn_HkIntegrand α n)
    h.1 h.2
    (fun z hz θ hθ => HkIntegrand_Dz_le_succ α n hf z θ hz hθ)

/-! ## 6. The target -/

theorem hkMemDzPth_of_shifted {α : ℝ} {k : ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hk : 1 ≤ k)
    (hsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Ψ))
    (hshift : Work.Spaces.HkMem α (k + 1) (Work.Spaces.pth Ψ)) :
    Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth Ψ)) :=
  HkMem_Dz_of_smoothOpen α k hsm hshift

end Work.FTS.EllipticEst.UopHk
