/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise domination of the `ℋ^k`-integrand of a mixed derivative

For `f` that is `C^∞` on the open quadrant `quadU = (-1,∞) × (0,π/2)`
(`Work.FTS.LocData.SmoothQuad f`), the curvilinear operators `D_z = z ∂_z` and
`D_θ = sin(2θ) ∂_θ` commute on `quadU` (`Work.Spaces.Dz_Dth_comm`, valid at every point at
which the profile is `C²`, together with the locality of `D_θ` and of `D_z^j` on the open
quadrant).  Consequently every weighted derivative occurring in the integrand of the
`ℋ^k`-norm of `D_z^j D_θ^i f` is a weighted derivative of `f` of total order at most
`i + j + k`:

  `D_z^a (D_z^jD_θ^if) = D_z^{a+j}D_θ^i f`,  `D_z^b D_θ^a (D_z^jD_θ^if) = D_z^{b+j}D_θ^{a+i} f`,

and the `H^0`-weight `w/sin(2θ)^{η/2}` is dominated by the mixed weight
`Wt = w·sin(2θ)^{-γ/2}` (`η = 99/100 < 1 < γ = 1 + α/10`, `Work.Spaces.H_le_Wt`).  Hence

  `HkIntegrand α k (mixed j i f) z θ ≤ HkIntegrand α (i + j + k) f z θ`

for `z > 0` and `θ ∈ Iθ`.  (On the angular boundary `sin(2θ) = 0` both sides vanish, so the
pointwise commutativity of the operators is needed only in the interior.)

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongLWP.Defs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.H_le_Wt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option autoImplicit false

/-! ## Congruence of the iterates of `D_z` on the open quadrant

`D_z = z ∂_z` is local, so two functions that agree on the open quadrant have the same
`D_z`-iterates there. -/

private lemma DzIter_congr_quadU {F G : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry F) (Function.uncurry G) Work.Spaces.quadU) (b : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter b F))
      (Function.uncurry (Work.Spaces.DzIter b G)) Work.Spaces.quadU := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  induction b with
  | zero => exact h
  | succ n ih =>
      intro y hy
      have hpz : Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2 :=
        Work.Spaces.pz_congr_of_isOpen hV ih hy
      show y.1 * Work.Spaces.pz (Work.Spaces.DzIter n F) y.1 y.2
          = y.1 * Work.Spaces.pz (Work.Spaces.DzIter n G) y.1 y.2
      rw [hpz]

/-! ## `D_z` commutes with the iterates of `D_θ` on the open quadrant -/

/-- `D_z (D_θ^a g) = D_θ^a (D_z g)` on the open quadrant, for a profile that is `C^∞` (in the
genuine smooth order `Work.Stability.smoothOrder`) there.  This is
`Work.Spaces.DzDthIterCommOn` with the finite-order smooth class `SmoothQuad` in place of the
analytic order `⊤`. -/
private theorem Dz_DthIter_comm_quadU {g : ℝ → ℝ → ℝ}
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Work.Spaces.quadU)
    (a : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.Dz g))) Work.Spaces.quadU := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  have h2le : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    rw [Work.Stability.smoothOrder]; exact WithTop.coe_le_coe.mpr le_top
  induction a with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hsmD : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DthIter i g)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DthIter hV hg i
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.DthIter i g)) y :=
        (ContDiffOn.of_le hsmD h2le).contDiffAt (hV.mem_nhds hy)
      have hcomm : Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2 :=
        Work.Spaces.Dz_Dth_comm (f := Work.Spaces.DthIter i g) hcd
      show Work.Spaces.Dz (Work.Spaces.Dth (Work.Spaces.DthIter i g)) y.1 y.2
          = Work.Spaces.Dth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [hcomm]
      show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.Dz (Work.Spaces.DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2)
            * Work.Spaces.pth (Work.Spaces.DthIter i (Work.Spaces.Dz g)) y.1 y.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

/-- `D_z^j (D_θ^a X) = D_θ^a (D_z^j X)` on the open quadrant, for a profile that is `C^∞`
there. -/
private theorem DzIter_DthIter_comm_quadU {X : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry X) Work.Spaces.quadU)
    (a j : ℕ) :
    EqOn (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter j X))) Work.Spaces.quadU := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  induction j with
  | zero => intro y hy; rfl
  | succ j ih =>
      intro y hy
      have hDzSm : ContDiffOn ℝ Work.Stability.smoothOrder
          (Function.uncurry (Work.Spaces.DzIter j X)) Work.Spaces.quadU :=
        Work.FTS.LocData.contDiffOn_DzIter hV hX j
      have hstep : Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)) y.1 y.2
          = Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter j X)) y.1 y.2 := by
        have hpz := Work.Spaces.pz_congr_of_isOpen hV ih hy
        show y.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)) y.1 y.2
            = y.1 * Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter j X)) y.1 y.2
        rw [hpz]
      show Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.DthIter a X)) y.1 y.2
          = Work.Spaces.DthIter a (Work.Spaces.DzIter (j + 1) X) y.1 y.2
      rw [hstep]
      exact Dz_DthIter_comm_quadU hDzSm a hy

/-! ## The mixed derivatives of a mixed derivative -/

/-- `D_z^bD_θ^a (D_z^jD_θ^if) = D_z^{b+j}D_θ^{a+i}f` at every point of the open quadrant,
for a `SmoothQuad` datum. -/
private theorem mixed_mixed_quadU {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) Work.Spaces.quadU)
    (b a j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.mixed b a (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed (b + j) (a + i) f z θ := by
  have hV : IsOpen Work.Spaces.quadU := Work.Spaces.isOpen_quadU
  have hy : (z, θ) ∈ Work.Spaces.quadU := by
    simp only [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith, hθ0, hθ1⟩
  have hX : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DthIter i f)) Work.Spaces.quadU :=
    Work.FTS.LocData.contDiffOn_DthIter hV hf i
  have hcommEq : EqOn
      (Function.uncurry
        (Work.Spaces.DthIter a (Work.Spaces.DzIter j (Work.Spaces.DthIter i f))))
      (Function.uncurry
        (Work.Spaces.DzIter j (Work.Spaces.DthIter a (Work.Spaces.DthIter i f))))
      Work.Spaces.quadU := (DzIter_DthIter_comm_quadU hX a j).symm
  have h1 : Work.Spaces.DzIter b
        (Work.Spaces.DthIter a (Work.Spaces.DzIter j (Work.Spaces.DthIter i f))) z θ
      = Work.Spaces.DzIter b
        (Work.Spaces.DzIter j (Work.Spaces.DthIter a (Work.Spaces.DthIter i f))) z θ :=
    (DzIter_congr_quadU hcommEq b) hy
  simp only [Work.Spaces.mixed]
  rw [h1, ← Work.Spaces.DzIter_add_right b j (Work.Spaces.DthIter a (Work.Spaces.DthIter i f)),
    Work.Spaces.DthIter_add_right a i f]

/-! ## Vanishing of the integrand on the angular boundary -/

/-- At `sin(2θ) = 0` the `ℋ^k`-integrand vanishes for every `f`: the `1/sin(2θ)^{η/2}` of the
first sum and the `Wt = w·sin(2θ)^{-γ/2}` of the second are both `0`. -/
private lemma HkIntegrand_eq_zero_of_sin (α : ℝ) (hα : 0 < α) (k : ℕ) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have hgam : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hWt : Work.Spaces.Wt α z θ = 0 := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, hs,
      Real.zero_rpow (neg_ne_zero.mpr (ne_of_gt (div_pos hgam (by norm_num)))), mul_zero]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [hWt, mul_zero, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-! ## The pointwise domination -/

theorem HkIntegrand_mixed_le {α : ℝ} (hα : 0 < α) {k j i : ℕ} (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (Work.Spaces.mixed j i f) z θ
      ≤ Work.Spaces.HkIntegrand α (i + j + k) f z θ := by
  have hθ0le : 0 ≤ θ := hθ.1
  have hθ1le : θ ≤ π / 2 := hθ.2
  by_cases hsin : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α hα k (Work.Spaces.mixed j i f) hsin,
      HkIntegrand_eq_zero_of_sin α hα (i + j + k) f hsin]
  · have hθ0 : 0 < θ := by
      rcases eq_or_lt_of_le hθ0le with h | h
      · exact absurd (by rw [← h]; simp) hsin
      · exact h
    have hθ1 : θ < π / 2 := by
      rcases lt_or_eq_of_le hθ1le with h | h
      · exact h
      · exact absurd (by rw [h]; rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) hsin
    have hzIz : z ∈ Work.Spaces.Iz := by
      rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
    set H : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hH
    set W : ℝ := Work.Spaces.Wt α z θ with hW
    have hHW : H ^ 2 ≤ W ^ 2 := by
      rw [hH, hW]; exact Work.Spaces.H_le_Wt α hα z θ hzIz hθ
    -- The `(D_θ`-order, `D_z`-order)`-indexed building block of the two integrands.
    set T : ℕ × ℕ → ℝ := fun x =>
      if x.1 = 0 then (Work.Spaces.DzIter x.2 f z θ * H) ^ 2
      else (Work.Spaces.mixed x.2 x.1 f z θ * W) ^ 2 with hT
    have hTnn : ∀ x, 0 ≤ T x := by
      rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
    -- The index sets of the two sums of the right-hand side.
    set R1 : Finset (ℕ × ℕ) := (Finset.range (i + j + k + 1)).image (fun q => ((0 : ℕ), q))
      with hR1def
    set R2 : Finset (ℕ × ℕ) :=
      ((Finset.range (i + j + k + 1)) ×ˢ (Finset.range (i + j + k + 1))).filter
        (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ i + j + k) with hR2def
    -- The index sets of the two sums of the left-hand side, shifted into the right-hand side.
    set S1 : Finset (ℕ × ℕ) := (Finset.range (k + 1)).image (fun a => (i, a + j)) with hS1def
    set S2 : Finset (ℕ × ℕ) :=
      (((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
        (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)).image
          (fun x : ℕ × ℕ => (x.1 + i, x.2 + j)) with hS2def
    have hR1 : (∑ x ∈ R1, T x)
        = ∑ q ∈ Finset.range (i + j + k + 1), (Work.Spaces.DzIter q f z θ * H) ^ 2 := by
      rw [hR1def]
      have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q))
          (↑(Finset.range (i + j + k + 1)) : Set ℕ) := by
        intro x _ y _ h; simpa using h
      rw [Finset.sum_image (f := T) hinj]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [hT]; simp
    have hR2 : (∑ x ∈ R2, T x)
        = ∑ p ∈ Finset.range (i + j + k + 1), ∑ q ∈ Finset.range (i + j + k + 1),
            (if 1 ≤ p ∧ p + q ≤ i + j + k
              then (Work.Spaces.mixed q p f z θ * W) ^ 2 else 0) := by
      rw [hR2def, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      simp only [hT]
      by_cases hc : 1 ≤ p ∧ p + q ≤ i + j + k
      · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
      · rw [if_neg hc, if_neg hc]
    have hLHSunfold : Work.Spaces.HkIntegrand α k (Work.Spaces.mixed j i f) z θ
        = (∑ a ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter a (Work.Spaces.mixed j i f) z θ * H) ^ 2)
          + ∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
              (if 1 ≤ a ∧ a + b ≤ k
                then (Work.Spaces.mixed b a (Work.Spaces.mixed j i f) z θ * W) ^ 2 else 0) := by
      simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
    have hRHSunfold : Work.Spaces.HkIntegrand α (i + j + k) f z θ
        = (∑ q ∈ Finset.range (i + j + k + 1), (Work.Spaces.DzIter q f z θ * H) ^ 2)
          + ∑ p ∈ Finset.range (i + j + k + 1), ∑ q ∈ Finset.range (i + j + k + 1),
              (if 1 ≤ p ∧ p + q ≤ i + j + k
                then (Work.Spaces.mixed q p f z θ * W) ^ 2 else 0) := by
      simp [Work.Spaces.HkIntegrand, ← hH, ← hW]
    -- The first sum of the left-hand side sits on `S1`.
    have hS1 : (∑ a ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter a (Work.Spaces.mixed j i f) z θ * H) ^ 2)
        ≤ ∑ x ∈ S1, T x := by
      rw [hS1def]
      have hinj : Set.InjOn (fun a : ℕ => (i, a + j)) (↑(Finset.range (k + 1)) : Set ℕ) := by
        intro x _ y _ h; simpa using h
      rw [Finset.sum_image (f := T) hinj]
      refine Finset.sum_le_sum (fun a _ => ?_)
      simp only [hT]
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl, Work.Spaces.mixed_zero_right, ← Work.Spaces.DzIter_add_right a j f]
      · rw [if_neg (by omega : ¬ i = 0)]
        have hDz : Work.Spaces.DzIter a (Work.Spaces.mixed j i f)
            = Work.Spaces.mixed (a + j) i f := by
          simp only [Work.Spaces.mixed]; rw [Work.Spaces.DzIter_add_right]
        rw [hDz]
        nlinarith [hHW, sq_nonneg (Work.Spaces.mixed (a + j) i f z θ)]
    -- The second sum of the left-hand side equals the sum on `S2`.
    have hS2 : (∑ a ∈ Finset.range (k + 1), ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ a ∧ a + b ≤ k
            then (Work.Spaces.mixed b a (Work.Spaces.mixed j i f) z θ * W) ^ 2 else 0))
        = ∑ x ∈ S2, T x := by
      rw [hS2def]
      have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + i, x.2 + j))
          (↑(((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
            (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ k)) : Set (ℕ × ℕ)) := by
        intro x _ y _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
      rw [Finset.sum_image (f := T) hinj, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      dsimp only
      by_cases hc : 1 ≤ a ∧ a + b ≤ k
      · rw [if_pos hc, if_pos hc]
        simp only [hT]
        rw [if_neg (by omega : ¬ a + i = 0)]
        rw [mixed_mixed_quadU hsm b a j i hz hθ0 hθ1]
      · rw [if_neg hc, if_neg hc]
    have hdisjS : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [hS1def, Finset.mem_image] at hx1
      obtain ⟨a, _, rfl⟩ := hx1
      rw [hS2def, Finset.mem_image] at hx2
      obtain ⟨y, hy, hxy⟩ := hx2
      rw [Finset.mem_filter] at hy
      simp only [Prod.mk.injEq] at hxy
      have hy1 : 1 ≤ y.1 := hy.2.1
      omega
    have hdisjR : Disjoint R1 R2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [hR1def, Finset.mem_image] at hx1
      obtain ⟨q, _, rfl⟩ := hx1
      rw [hR2def, Finset.mem_filter] at hx2
      have h := hx2.2.1
      simp only at h
      omega
    have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · rw [hS1def, Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        rw [Finset.mem_range] at ha
        by_cases hi : i = 0
        · left
          rw [hR1def, Finset.mem_image]
          exact ⟨a + j, by rw [Finset.mem_range]; omega, by simp [hi]⟩
        · right
          rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          dsimp only
          exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
      · rw [hS2def, Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
        right
        rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        dsimp only
        exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    rw [hLHSunfold, hRHSunfold, ← hR1, ← hR2]
    calc _ ≤ (∑ x ∈ S1, T x) + (∑ x ∈ S2, T x) := add_le_add hS1 (le_of_eq hS2)
      _ = ∑ x ∈ S1 ∪ S2, T x := (Finset.sum_union hdisjS).symm
      _ ≤ ∑ x ∈ R1 ∪ R2, T x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
      _ = (∑ x ∈ R1, T x) + (∑ x ∈ R2, T x) := Finset.sum_union hdisjR

end Work.FTS.StrongLWP.Sobolev
