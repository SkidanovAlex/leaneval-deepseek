/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z`-pairing in the interior class `SmoothQuad`: Leibniz expansions

This module contains the two Leibniz expansions of the `D_z`-pairing integrand
`H4PairInt α (fun z θ => f z θ * D_z g z θ) g` in the interior class
`Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on the open quadrant), namely

* `DzIter_mul_Dz_eq_Q` : `D_z^i (f · D_zg) = ∑_{k≤i} C(i,k) D_z^k f · D_z^{i+1-k} g`, and
* `mixed_mul_Dz_eq_Q`  : `D_z^jD_θ^i (f · D_zg)
    = ∑_{a≤i}∑_{b≤j} C(i,a)C(j,b) D_z^bD_θ^a f · D_z^{j-b+1}D_θ^{i-a} g`,

together with the two calculus inputs they need on the open quadrant
(`mixed_Dz_apply_Q`, the commutation of one `D_z` with every `D_θ`-iterate), and the
bookkeeping identity

* `H4PairInt_sub_Badz_eq_Q` : `H4PairInt α (f·D_zg) g - Badz = Z3.easyZ + Z3.easyM`

whose right-hand side is the sum of the surviving Leibniz summands (the order-five
"all derivatives on `g`" summands removed).

These are the interior-class analogues of `Work.FTS.H2.Transport3Aux.Z3.DzIter_mul_Dz_eq`,
`...mixed_mul_Dz_eq` and `...H4PairInt_sub_Badz_eq`, whose proofs run verbatim once the
Leibniz rules `Work.FTS.H2.STQ.DzIter_mul_quad` / `...mixed_mul_quad` (available because both
factors are `SmoothQuad`) are used in place of `Work.Spaces.DzIter_mul` /
`Work.Spaces.mixed_mul_eq` (which need `SmoothInt`/`SmoothNbhd`).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.FTS.H2.HQ.DthDzIterComm
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.H2.Transport3Aux.Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Defs
import Submission.Work.FTS.H2.Transport3Aux.Z3Aux
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T3Q

open Work.FTS.H2.Transport3Aux.Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Closure of `SmoothQuad` under the two transport operators -/

/-- `D_z` preserves `SmoothQuad`. -/
theorem smoothQuad_Dz {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.Dz g) :=
  Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
    (Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU hg)

/-! ## Commutation of `D_z` with the `D_θ`-iterates on the open quadrant -/

/-- **`D_θ^i` commutes with every iterate of `D_z` on the open quadrant**, for `g` of class
`SmoothQuad`: `D_z^b (D_θ^i g) = D_θ^i (D_z^b g)` on `quadU`.

This is the `SmoothQuad` counterpart of `Work.Spaces.DthIter_DzIter_comm_eqOn` (stated for
`SmoothNbhd` on `nbhU`); the induction only uses the single-step commutation
`Work.FTS.H2.HQ.Dth_DzIter_comm_quadU` (proved) and the `θ`-congruence of two functions that
agree on the open quadrant. -/
theorem DthIter_DzIter_comm_eqOn_Q {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g)
    (b i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.DzIter b g)))
      (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter i g))) Work.Spaces.quadU := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      -- `D_θ` of the two (pointwise equal on `quadU`) functions agree at `y`
      have hDth : Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i g)) y.1 y.2 := by
        show Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.DzIter b g)) y.1 y.2
            = Real.sin (2 * y.2)
              * Work.Spaces.pth (Work.Spaces.DzIter b (Work.Spaces.DthIter i g)) y.1 y.2
        rw [Work.Spaces.pth_congr_of_isOpen Work.Spaces.isOpen_quadU ih hy]
      -- the single-step commutation on the input `D_θ^i g`
      have hstep : Work.Spaces.Dth (Work.Spaces.DzIter b (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.FTS.H2.HQ.Dth_DzIter_comm_quadU
          (Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hg i) b hy
      show Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.DzIter b g)) y.1 y.2
          = Work.Spaces.DzIter b (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
      rw [hDth, hstep]

/-- **One `D_z` commutes past every mixed iterate**: in the interior class,
`D_z^jD_θ^i (D_z g) = D_z^{j+1}D_θ^i g` at every point of the open quadrant.

The `SmoothNbhd` counterpart is `Work.FTS.H2.Transport3Aux.Z3.mixed_Dz_apply`. -/
theorem mixed_Dz_apply_Q (m n : ℕ) (g : ℝ → ℝ → ℝ) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.mixed m n (Work.Spaces.Dz g) z θ = Work.Spaces.mixed (m + 1) n g z θ := by
  intro z hz θ hθ
  have hz1 : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    linarith
  have hy : (z, θ) ∈ Work.Spaces.quadU := ⟨hz1, hθ⟩
  have hcomm := DthIter_DzIter_comm_eqOn_Q hg 1 n
  have hcongr := Work.FTS.H2.DzIter_congr_of_isOpen Work.Spaces.isOpen_quadU hcomm m hy
  rw [show Work.Spaces.mixed m n (Work.Spaces.Dz g) z θ
        = Work.Spaces.DzIter m (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ from rfl,
    show Work.Spaces.DzIter m (Work.Spaces.DthIter n (Work.Spaces.Dz g)) z θ
        = Work.Spaces.DzIter m (Work.Spaces.DzIter 1 (Work.Spaces.DthIter n g)) z θ from hcongr]
  rw [← Work.Spaces.DzIter_add_right m 1 (Work.Spaces.DthIter n g)]
  rfl

/-! ## The two Leibniz expansions -/

/-- **Leibniz expansion of `D_z^i (f · D_zg)` in the interior class.** -/
theorem DzIter_mul_Dz_eq_Q (i : ℕ) (f g : ℝ → ℝ → ℝ) (hf : Work.FTS.LocData.SmoothQuad f)
    (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ)
            * (Work.Spaces.DzIter k f z θ * Work.Spaces.DzIter (i + 1 - k) g z θ) := by
  intro z hz θ hθ
  rw [Work.FTS.H2.STQ.DzIter_mul_quad hf (smoothQuad_Dz hg) hz hθ]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [DzIter_Dz (i - k) g, show i - k + 1 = i + 1 - k by
    have := Finset.mem_range.mp hk; omega]

/-- **Leibniz expansion of `D_z^jD_θ^i (f · D_zg)` in the interior class.** -/
theorem mixed_mul_Dz_eq_Q (j i : ℕ) (f g : ℝ → ℝ → ℝ) (hf : Work.FTS.LocData.SmoothQuad f)
    (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((i.choose a : ℝ) * (j.choose b : ℝ))
              * (Work.Spaces.mixed b a f z θ
                  * Work.Spaces.mixed (j - b + 1) (i - a) g z θ) := by
  intro z hz θ hθ
  rw [Work.FTS.H2.STQ.mixed_mul_quad hf (smoothQuad_Dz hg) hz hθ]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  rw [mixed_Dz_apply_Q (j - b) (i - a) g hg z hz θ hθ]

/-! ## The expansion of the pairing and the removal of `Badz` -/

/-- **`H4PairInt α (f D_z g) g - Badz = easyZ + easyM` in the interior class.**

The `SmoothNbhd` counterpart is `Work.FTS.H2.Transport3Aux.Z3.H4PairInt_sub_Badz_eq`; the
proof is the same bookkeeping, with the two Leibniz rules above replacing
`DzIter_mul_Dz_eq`/`mixed_mul_Dz_eq`. -/
theorem H4PairInt_sub_Badz_eq_Q (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.FTS.H2.H4PairInt α (fun z θ => f z θ * Work.Spaces.Dz g z θ) g z θ
          - Work.FTS.H2.Badz α f g z θ
        = easyZ α f g z θ + easyM α f g z θ := by
  intro z hz θ hθ
  have hZ : (∑ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ * Whz z θ)
          * (Work.Spaces.DzIter i g z θ * Whz z θ))
      = ∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), TZ α f g i k z θ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_mul_Dz_eq_Q i f g hf hg z hz θ hθ]
    simp only [Finset.sum_mul, TZ]
  have hM : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ * Wm α z θ)
            * (Work.Spaces.mixed j i g z θ * Wm α z θ)
        else 0))
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), TM α f g i j a b z θ
          else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, if_pos hc, mixed_mul_Dz_eq_Q j i f g hf hg z hz θ hθ]
      simp only [Finset.sum_mul, TM]
    · rw [if_neg hc, if_neg hc]
  have hBsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then
          f z θ * Work.Spaces.Dz (Work.Spaces.mixed j i g) z θ
            * Work.Spaces.mixed j i g z θ * Wm α z θ ^ 2
        else 0))
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j = 4
    · rw [if_pos hc, if_pos hc, TM_zero_zero]
    · rw [if_neg hc, if_neg hc]
  have hZsplit : (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), TZ α f g i k z θ)
      = TZ α f g 4 0 z θ + easyZ α f g z θ := by
    rw [z_split, easyZ]
  have hMsp : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), TM α f g i j a b z θ)
        else 0))
      - (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0))
      = easyM α f g z θ := by
    rw [easyM, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · have hx : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              TM α f g i j a b z θ) else 0) = _ := if_pos hc
      have hy0 : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)) else 0) = _ :=
        if_pos hc
      rw [hx, hy0]
      by_cases h4 : i + j = 4
      · rw [if_pos ⟨hc.1, h4⟩]
        have h := mx_split i j (fun a b => TM α f g i j a b z θ)
        rw [if_pos h4] at h
        exact h
      · rw [if_neg (fun hh => h4 hh.2), sub_zero]
        refine (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_).symm
        rw [if_neg (by omega : ¬ (i + j = 4 ∧ a = 0 ∧ b = 0))]
    · have hx : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              TM α f g i j a b z θ) else 0) = 0 := if_neg hc
      have hy0 : (if 1 ≤ i ∧ i + j ≤ 4 then
            (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if i + j = 4 ∧ a = 0 ∧ b = 0 then 0 else TM α f g i j a b z θ)) else 0) = 0 :=
        if_neg hc
      have hy : (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0) = 0 :=
        if_neg (fun hh => hc ⟨hh.1, by omega⟩)
      rw [hx, hy0, hy, sub_zero]
  rw [Work.FTS.H2.H4PairInt, Work.FTS.H2.Badz, ← TZ_four_zero α f g z θ, hBsum, hZ, hM]
  exact (show (∑ i ∈ Finset.range 5, ∑ k ∈ Finset.range (i + 1), TZ α f g i k z θ)
      + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              TM α f g i j a b z θ else 0))
      - (TZ α f g 4 0 z θ
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j = 4 then TM α f g i j 0 0 z θ else 0))
      = easyZ α f g z θ + easyM α f g z θ from by
    linear_combination hZsplit + hMsp)

end Work.FTS.H2.T3Q
