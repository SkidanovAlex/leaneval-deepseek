/-
# The port `RegQ α n (D_z f)` of the interior regularity class

`Work.FTS.Nonlin.RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f` is the class in
which the modified induction of the coercivity node runs (`FTS/N45_DESIGN_LEAD.md §3.1`).  It is
*not* smoothness on a neighbourhood of the closed quadrant (`Work.Spaces.SmoothNbhd`, which in
this Mathlib is analyticity and is destroyed by every cut-off): `SmoothQuad` is genuine `C^∞`
on the open strip `quadU = (-1,∞) × (0,π/2)`, and the boundary information is carried
separately, and only as one-sided *limits*, by `BdryTraces`.

This module proves the `D_z`-port of the class:

  `RegQ α (n+1) f → RegQ α n (D_z f)`.

The three components of the class are treated separately.

* **Smoothness.**  `D_z f = z ∂_z f`, and `∂_z f` is `C^∞` on `quadU` whenever `f` is
  (`Work.FTS.LocData.contDiffOn_Dz`), so this is closure of `SmoothQuad` under the operator.

* **`𝓗ⁿ`-membership.**  The pointwise comparison of the integrands is *literally* the index
  shift `D_z^i (D_z f) = D_z^{i+1} f`, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`: every summand
  of `HkIntegrand α n (D_z f)` is a summand of `HkIntegrand α (n+1) f`, with the *same* weight,
  so `HkIntegrand α n (D_z f) ≤ HkIntegrand α (n+1) f` pointwise on the quadrant.  The pure
  family needs no hypothesis; the mixed family is the commutation of `D_z` with `D_θ`, which on
  the interior class `SmoothQuad` is available only at the *interior points* of the quadrant
  (Clairaut for the two curvilinear derivatives).  The identity is nevertheless global on
  `Iz ×ˢ Iθ`: outside the open quadrant one of the two variables sits at `z = 0` resp.
  `sin(2θ) = 0`, where both sides vanish — the `D_z`'s contribute a factor `z = 0`, and a
  `D_θ` at an angle with `sin(2θ) = 0` kills every slice (`mixed_apply_of_sin_zero`,
  `mixed_apply_zero_fst_of_slice_zero`).  With the pointwise domination, the membership is
  `Work.FTS.LocData.HkMem_of_majorant` with the majorant the `(n+1)`-integrand itself — exactly
  as in `Work.GalerkinFix.RegQ.HkMem_mono_Q` (the `SmoothQuad` replacement of
  `Work.Coercivity.HkMem_mono`), the measurability input being
  `Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad`.

* **Boundary traces.**  `BdryTraces` only asks for one-sided limits at `z = 0`, `z = ∞` and at
  the two angular endpoints; those limits are approached through points of the domain on which
  the mixed derivatives of `D_z f` and of `f` agree (`mixed_Dz_shift`), so the traces of `f` of
  order `(a, b+1)` give those of `D_z f` of order `(a,b)` by reindexing.  Unlike the `D_θ`-case
  (`RegQ_dth.lean`) the identity is only available on the domain, so the transport has to be
  performed through `Filter.EventuallyEq`/`Filter.Tendsto.congr'` rather than by `simpa`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.QuadAux
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.SumShiftZ_le
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.pz_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.QuadPorts

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

/-! ## Commutation of `D_z` with the iterates of `D_θ` on the open strip

`Work.Spaces.quadU = (-1,∞) × (0,π/2)` is exactly the strip on which `SmoothQuad` is stated.
The two proofs below are the `SmoothQuad` counterpart of `Work.Spaces.DzDthIterCommOn` /
`Work.Spaces.Dth_DzIter_comm_eqOn`, which are stated for the analytic class `SmoothNbhd`: at
each step Clairaut (`Work.Spaces.Dz_Dth_comm`, which only needs `C²` at the point) pushes the
outer `D_z` past the `D_θ`, and the resulting functions are compared by the congruence lemmas
`Work.Spaces.pth_congr_of_isOpen` / `Work.Spaces.pz_congr_of_isOpen` for arbitrary open sets. -/

/-- On the open strip, `D_z` commutes with every iterate of `D_θ`. -/
theorem DzDthIterCommOn_quad {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) Work.Spaces.quadU := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hGi : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hg i
      have hF : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (hGi.contDiffAt (Work.Spaces.isOpen_quadU.mem_nhds hy)).of_le
          (by simp [Work.Stability.smoothOrder])
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
      rw [Work.Spaces.pth_congr_of_isOpen Work.Spaces.isOpen_quadU ih hy]

/-- On the open strip, `D_z^b` commutes with `D_θ^a`. -/
theorem DzIter_DthIter_comm_quad {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) Work.Spaces.quadU := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
      intro p hp
      have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
        DzDthIterCommOn_quad
          (Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hg b) a hp
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen Work.Spaces.isOpen_quadU ih hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
          = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
      exact hstep

/-! ## The index shift `D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` -/

/-- `D_z^i (D_z f) = D_z^{i+1} f` (definitional, from `D_z^{i+b} = D_z^i ∘ D_z^b`). -/
private lemma DzIter_Dz (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (Work.Spaces.Dz f) = Work.Spaces.DzIter (i + 1) f := by
  rw [Work.Spaces.DzIter_add_right]
  rfl

/-- The index shift at the *interior* points of the quadrant, where Clairaut is available. -/
theorem mixed_Dz_shift_interior {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (b a : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hy : (z, θ) ∈ Work.Spaces.quadU :=
    Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (by linarith), hθ⟩
  have hDzf : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.Dz f)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hf
  have h1 : Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := by
    simpa only [Work.Spaces.mixed, Function.uncurry] using
      (DzIter_DthIter_comm_quad hDzf b a hy)
  have h2 : Work.Spaces.DzIter b (Work.Spaces.Dz f) = Work.Spaces.DzIter (b + 1) f :=
    DzIter_Dz b f
  have h3 : Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ
      = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := by
    simpa only [Function.uncurry] using
      (DzIter_DthIter_comm_quad hf (b + 1) a hy).symm
  calc Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ
      = Work.Spaces.DthIter a (Work.Spaces.DzIter b (Work.Spaces.Dz f)) z θ := h1
    _ = Work.Spaces.DthIter a (Work.Spaces.DzIter (b + 1) f) z θ := by rw [h2]
    _ = Work.Spaces.DzIter (b + 1) (Work.Spaces.DthIter a f) z θ := h3
    _ = Work.Spaces.mixed (b + 1) a f z θ := rfl

/-! ### The boundary cases: everything vanishes

At `z = 0` every `D_z`-iterate of positive order vanishes (the outer factor of `D_z` is `z`); at
an angle with `sin(2θ) = 0` every positive iterate of `D_θ` vanishes, hence so do the `D_z`-slices
of the resulting functions. -/

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
`D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f` on `Iz ×ˢ Iθ`, for `f` smooth on the open quadrant.
At the interior points this is the commutation of `D_z` and `D_θ`; at `z = 0` and at the angular
endpoints both sides vanish. -/
theorem mixed_Dz_shift {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (b + 1) a f z θ := by
  have hDz0 : ∀ θ' : ℝ, Work.Spaces.Dz f 0 θ' = 0 := fun θ' => by
    show (0 : ℝ) * Work.Spaces.pz f 0 θ' = 0
    rw [zero_mul]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rcases a with _ | a
    · show Work.Spaces.DzIter b (Work.Spaces.Dz f) 0 θ = Work.Spaces.DzIter (b + 1) f 0 θ
      rw [DzIter_Dz]
    · rw [mixed_apply_zero_fst_of_slice_zero b (a + 1) hDz0 θ]
      exact (DzIter_succ_apply_zero b (Work.Spaces.DthIter (a + 1) f) θ).symm
  · by_cases hθin : θ ∈ Set.Ioo (0 : ℝ) (π / 2)
    · exact mixed_Dz_shift_interior hf b a hzpos hθin
    · have hs : Real.sin (2 * θ) = 0 :=
        Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθin
      rcases a with _ | a
      · show Work.Spaces.DzIter b (Work.Spaces.Dz f) z θ = Work.Spaces.DzIter (b + 1) f z θ
        rw [DzIter_Dz]
      · rw [mixed_apply_of_sin_zero b (a + 1) (by omega) (Work.Spaces.Dz f) hs]
        exact (mixed_apply_of_sin_zero (b + 1) (a + 1) (by omega) f hs).symm

/-! ## Pointwise domination of the `ℋⁿ`-integrand of `D_z f` -/

/-- A sum over `i ≤ k` of `F (i+1)` is dominated by the sum over `a ≤ k+1` of `F a`. -/
private lemma SumSuccRange_le (k : ℕ) (F : ℕ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ i ∈ Finset.range (k + 1), F (i + 1)) ≤ ∑ a ∈ Finset.range (k + 2), F a := by
  have h2 : (∑ a ∈ Finset.range (k + 2), F a)
      = (∑ i ∈ Finset.range (k + 1), F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F (k + 1)
  linarith [hF 0]

/-- **Every summand of `HkIntegrand α n (D_z f)` is a summand of `HkIntegrand α (n+1) f`**, with
the same weight: the pure summands by `D_z^i (D_z f) = D_z^{i+1} f`, the mixed summands by the
index shift `mixed_Dz_shift`.  Hence the pointwise domination of the integrands (this is the
`SmoothQuad` version of `Work.Coercivity.HkIntegrand_Dz_le`, which asks for the analytic class
`Work.Spaces.SmoothNbhd` and for `0 < α`). -/
theorem HkIntegrand_Dz_le_succ (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
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
  have h1 : (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * H) ^ 2)
      ≤ ∑ a ∈ Finset.range (n + 2), (Work.Spaces.DzIter a f z θ * H) ^ 2 := by
    refine le_trans (le_of_eq ?_) (SumSuccRange_le n
      (fun a => (Work.Spaces.DzIter a f z θ * H) ^ 2) (fun a => sq_nonneg _))
    exact Finset.sum_congr rfl (fun i _ => by rw [DzIter_Dz i f])
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

/-! ## The membership `HkMem α n (D_z f)` -/

/-- **The `𝓗ⁿ`-membership of `D_z f`**, by domination of its integrand by the `(n+1)`-integrand
of `f`: `Work.FTS.LocData.HkMem_of_majorant` with `M = HkIntegrand α (n+1) f`, the smoothness
input being `continuousOn_HkIntegrand_smoothQuad` for `D_z f`. -/
theorem HkMem_Dz_quad (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (h : Work.Spaces.HkMem α (n + 1) f) : Work.Spaces.HkMem α n (Work.Spaces.Dz f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dz f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n (Work.Spaces.Dz f)
      (Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hf))
    h.1 h.2
    (fun z hz θ hθ => HkIntegrand_Dz_le_succ α n hf z θ hz hθ)

/-! ## The transport of the boundary traces -/

/-- **The boundary traces of `D_z f`** from those of `f`: the traces at order `(a,b)` of `D_z f`
are the traces at order `(a,b+1)` of `f`, because the mixed derivatives agree on the domain
(`mixed_Dz_shift`) and every one-sided limit is taken through points of the domain. -/
theorem BdryTraces_Dz (α : ℝ) (n : ℕ) {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (hbd : Work.FTS.Nonlin.BdryTraces α (n + 1) f) :
    Work.FTS.Nonlin.BdryTraces α n (Work.Spaces.Dz f) := by
  intro a b hab
  obtain ⟨hzlim, hθlim⟩ := hbd a (b + 1) (by omega)
  -- the two filters `𝓝[>] 0`, `𝓝[<] π/2` count the open interval as an eventual set
  have hmemGT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    (nhdsGT_basis_of_exists_gt ⟨π / 2, Real.pi_div_two_pos⟩).mem_of_mem Real.pi_div_two_pos
  have hmemLT : Set.Ioo (0 : ℝ) (π / 2) ∈ 𝓝[<] (π / 2) :=
    (nhdsLT_basis_of_exists_lt ⟨0, by linarith [Real.pi_pos]⟩).mem_of_mem
      (by linarith [Real.pi_pos])
  constructor
  · intro θ hθ
    have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    constructor
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [mixed_Dz_shift hf b a (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).1.congr' hev
    · have hev : (fun z => z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2)
          =ᶠ[atTop]
          fun z => z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2 :=
        Filter.eventually_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun z hz => by
          show z * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
            = z * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ * Work.Spaces.w z) ^ 2
          rw [mixed_Dz_shift hf b a (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hz))) hθIθ])
      exact (hzlim θ hθ).2.congr' hev
  · intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
    constructor
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemGT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [mixed_Dz_shift hf b a hzIz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).1.congr' hev
    · have hev : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2)
          =ᶠ[𝓝[<] (π / 2)]
          fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2 :=
        Filter.eventually_of_mem hmemLT (fun θ hθ => by
          show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed (b + 1) a f z θ) ^ 2
            = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (Work.Spaces.mixed b a (Work.Spaces.Dz f) z θ) ^ 2
          rw [mixed_Dz_shift hf b a hzIz ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩])
      exact (hθlim z hz).2.congr' hev

/-! ## The port -/

theorem RegQ_dz (α : ℝ) {n : ℕ} {f : ℝ → ℝ → ℝ} (h : Work.FTS.Nonlin.RegQ α (n + 1) f) :
    Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dz f) := by
  obtain ⟨hsm, hmem, hbd⟩ := h
  exact ⟨Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hsm,
    HkMem_Dz_quad α n hsm hmem, BdryTraces_Dz α n hsm hbd⟩

end Work.FTS.CoercivityFix.QuadPorts
