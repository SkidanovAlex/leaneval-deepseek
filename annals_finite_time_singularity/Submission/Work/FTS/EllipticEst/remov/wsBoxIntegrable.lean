/-
Copyright: work module for the Elgindi finite-time singularity project.

# Box integrability of `(∂_z D_z^j Ψ)² sin(2θ)^{-η}` for a datum of the weak class

This module proves `Work.FTS.EllipticEst.remov.wsBoxIntegrable`: for every datum
`h : EllWeakPos α k F Ψ` with `k ≥ 1`, every `j ≤ 2` and every compact interval
`[a,b] ⊆ (0,∞)`, the uncurried function

  `(s,θ) ↦ (∂_z D_z^j Ψ (s,θ))² · sin(2θ)^{-η}`

is integrable on the box `[a,b] ×ˢ Iθ`.

## Route

The only `θ`-energies that the hypothesis class `EllWeakPos` makes available are the
slices of the two functions `∂_θ²Ψ` and `z²∂_z²Ψ` (the fields `memB` and `memA`):

  `TE_i(s) := ∫_θ (D_z^i g(s,θ))² sin(2θ)^{-η}`,  `g ∈ {∂_θ²Ψ, z²∂_z²Ψ}`,  `i = 0,1`,

and each of them is `z`-integrable on `(a,b]` by `wsAux.ws_thetaE_integrable`.  Write

  `wsRef Ψ s := TE_0(∂_θ²Ψ) + TE_1(∂_θ²Ψ) + TE_0(z²∂_z²Ψ) + TE_1(z²∂_z²Ψ)`

for their sum.  The pointwise input is the slice Poincaré bound
`wsAux.ws_slice_pointwise_le`, applied to the slices `v = Ψ(s,·)` and `v = ∂_zΨ(s,·)`;
it bounds `v(θ)²` by the value of `v` and `v'` at `θ = π/4` together with the weighted
energy of `v''`.  For `v = ∂_zΨ(s,·)` one uses `∂_θ²∂_zΨ = ∂_z∂_θ²Ψ` (Clairaut) and
`∂_z = D_z/z`, so its energy is `TE_1(∂_θ²Ψ)(s)/s²` (the delegated lemma
`ws_pz_slice_pointwise_le`).  The continuity of the four numbers
`Ψ(s,π/4)`, `∂_θΨ(s,π/4)`, `∂_zΨ(s,π/4)`, `∂_θ∂_zΨ(s,π/4)` on the compact `[a,b]`
(`wsAbsBound`) turns the pointwise bounds into

  `(D_z^mΨ(s,θ))² ≤ Cb (1 + wsRef Ψ s) + Cb ((z²∂_z²Ψ(s,θ))² + (D_z(z²∂_z²Ψ)(s,θ))²)`

for `m ≤ 3` — the two explicit `z²∂_z²Ψ`-terms are unavoidable, because `HkMem` gives no
pointwise bound on `z²∂_z²Ψ`; they are exactly the two slots whose `θ`-slices are
integrable by `ws_slot_slice`.  Integrating in `θ` gives
`thetaE (D_z^mΨ) s ≤ Ct (1 + wsRef Ψ s)`, and `integrableOn_box_of_slice_of_nonneg` then
yields the box integrability of `(D_z^mΨ)² sin(2θ)^{-η}` for `m ∈ {1,2,3}`, i.e. of
`(∂_z D_z^jΨ)² sin(2θ)^{-η}` with `m = j + 1`, since `∂_z D_z^jΨ = D_z^{j+1}Ψ / z` and
`1/z² ≤ 1/a²` on the box.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.remov.wsAbsBound
import Submission.Work.FTS.EllipticEst.remov.ws_DzIter_two_eq
import Submission.Work.FTS.EllipticEst.remov.ws_DzIter_three_eq
import Submission.Work.FTS.EllipticEst.remov.ws_pz_slice_pointwise_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "SS" => Work.FTS.EllipticEst.sEta

/-! ## The reference radial energy -/

/-- The sum of the four `θ`-energies that the weak class makes available: the `D_z^i`-slots
(`i = 0,1`) of the two functions `∂_θ²Ψ` and `z²∂_z²Ψ`. -/
def wsRef (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  thetaE (Work.Spaces.pthIter 2 Ψ) s
    + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
    + thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
    + thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s

theorem wsRef_nonneg (Ψ : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ wsRef Ψ s := by
  have h : wsRef Ψ s = thetaE (Work.Spaces.pthIter 2 Ψ) s
      + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
      + thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
      + thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s :=
    rfl
  rw [h]
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
  have h4 := thetaE_nonneg
    (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s
  linarith

theorem wsRef_ge_1 (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (Work.Spaces.pthIter 2 Ψ) s ≤ wsRef Ψ s := by
  have h : wsRef Ψ s = thetaE (Work.Spaces.pthIter 2 Ψ) s
      + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
      + thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
      + thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s :=
    rfl
  rw [h]
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
  have h4 := thetaE_nonneg
    (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s
  linarith

theorem wsRef_ge_2 (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s ≤ wsRef Ψ s := by
  have h : wsRef Ψ s = thetaE (Work.Spaces.pthIter 2 Ψ) s
      + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
      + thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
      + thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s :=
    rfl
  rw [h]
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h3 := thetaE_nonneg (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
  have h4 := thetaE_nonneg
    (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s
  linarith

theorem wsRef_ge_3 (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s ≤ wsRef Ψ s := by
  have h : wsRef Ψ s = thetaE (Work.Spaces.pthIter 2 Ψ) s
      + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
      + thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
      + thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s :=
    rfl
  rw [h]
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h4 := thetaE_nonneg
    (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s
  linarith

theorem wsRef_ge_4 (Ψ : ℝ → ℝ → ℝ) (s : ℝ) :
    thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s
      ≤ wsRef Ψ s := by
  have h : wsRef Ψ s = thetaE (Work.Spaces.pthIter 2 Ψ) s
      + thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
      + thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
      + thetaE (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s :=
    rfl
  rw [h]
  have h1 := thetaE_nonneg (Work.Spaces.pthIter 2 Ψ) s
  have h2 := thetaE_nonneg (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
  have h3 := thetaE_nonneg (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s
  linarith

/-! ## The `θ`-energy of a slot is integrable on a closed interval -/

/-- `ws_thetaE_integrable` upgraded from `(a,b]` to `[a,b]`: the two sets differ by the
single point `a`. -/
theorem ws_thetaE_Icc_integrable {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun u => thetaE (Work.Spaces.DzIter i g) u)
      (Set.Icc a b) := by
  by_cases hba : b < a
  · have hemp : Set.Icc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      rw [Set.mem_Icc] at hx
      exact absurd (lt_of_lt_of_le hba hx.1) (not_lt.mpr hx.2)
    rw [hemp]
    exact MeasureTheory.integrableOn_empty
  · have hle : a ≤ b := le_of_not_gt hba
    have hIoc : MeasureTheory.IntegrableOn (fun u => thetaE (Work.Spaces.DzIter i g) u)
        (Set.Ioc a b) := ws_thetaE_integrable hs hm i hi ha
    rw [← Set.Ioc_union_left hle]
    exact MeasureTheory.integrableOn_union.mpr
      ⟨hIoc, MeasureTheory.integrableOn_singleton
        (f := fun u => thetaE (Work.Spaces.DzIter i g) u) (x := a)
        (hfx := by finiteness)
        (hx := by rw [MeasureTheory.measure_singleton a]; exact ENNReal.zero_lt_top)⟩

/-! ## Uniform bounds on the four numbers at `θ = π/4` -/

/-- The four numbers `Ψ(s,π/4)`, `∂_θΨ(s,π/4)`, `∂_zΨ(s,π/4)`, `∂_θ∂_zΨ(s,π/4)` are
bounded on the compact interval `[a,b]` (`0 < a`) by continuity on the open quadrant. -/
theorem ws_midpoint_bounds {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {a b : ℝ}
    (ha : 0 < a) :
    ∃ KA KB KA' KB' : ℝ, 0 ≤ KA ∧ 0 ≤ KB ∧ 0 ≤ KA' ∧ 0 ≤ KB' ∧
      (∀ s ∈ Set.Icc a b, (Ψ s (Real.pi / 4)) ^ 2 ≤ KA) ∧
      (∀ s ∈ Set.Icc a b, (deriv (fun θ => Ψ s θ) (Real.pi / 4)) ^ 2 ≤ KB) ∧
      (∀ s ∈ Set.Icc a b, (Work.Spaces.pz Ψ s (Real.pi / 4)) ^ 2 ≤ KA') ∧
      (∀ s ∈ Set.Icc a b, (deriv (fun θ => Work.Spaces.pz Ψ s θ) (Real.pi / 4)) ^ 2 ≤ KB') := by
  have hθ₀ : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hab : a ≤ max a b := le_max_left a b
  obtain ⟨C0, hC00, hC0⟩ :=
    wsAbsBound (g := Ψ) hΨ.continuousOn (a := a) (b := max a b) (θ₀ := Real.pi / 4) ha hab hθ₀
  obtain ⟨C1, hC10, hC1⟩ := wsAbsBound (g := Work.Spaces.pth Ψ) (hΨ.pth).continuousOn
    (a := a) (b := max a b) (θ₀ := Real.pi / 4) ha hab hθ₀
  obtain ⟨C2, hC20, hC2⟩ := wsAbsBound (g := Work.Spaces.pz Ψ) (hΨ.pz).continuousOn
    (a := a) (b := max a b) (θ₀ := Real.pi / 4) ha hab hθ₀
  obtain ⟨C3, hC30, hC3⟩ := wsAbsBound (g := Work.Spaces.pth (Work.Spaces.pz Ψ))
    ((hΨ.pz).pth).continuousOn (a := a) (b := max a b) (θ₀ := Real.pi / 4) ha hab hθ₀
  have hsq : ∀ {x C : ℝ}, |x| ≤ C → x ^ 2 ≤ C ^ 2 := by
    intro x C h
    have h1 : |x| ^ 2 ≤ C ^ 2 := by
      have := mul_self_le_mul_self (abs_nonneg x) h
      simpa only [sq] using this
    rwa [sq_abs] at h1
  refine ⟨C0 ^ 2, C1 ^ 2, C2 ^ 2, C3 ^ 2, by positivity, by positivity, by positivity,
    by positivity, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : s ∈ Set.Icc a (max a b) := ⟨hs.1, le_trans hs.2 (le_max_right a b)⟩
    have h := hC0 s hs'
    exact hsq h
  · intro s hs
    have hs' : s ∈ Set.Icc a (max a b) := ⟨hs.1, le_trans hs.2 (le_max_right a b)⟩
    have h := hC1 s hs'
    exact hsq h
  · intro s hs
    have hs' : s ∈ Set.Icc a (max a b) := ⟨hs.1, le_trans hs.2 (le_max_right a b)⟩
    have h := hC2 s hs'
    exact hsq h
  · intro s hs
    have hs' : s ∈ Set.Icc a (max a b) := ⟨hs.1, le_trans hs.2 (le_max_right a b)⟩
    have h := hC3 s hs'
    exact hsq h

/-! ## The target -/

theorem wsBoxIntegrable (α : ℝ) (k : ℕ) (F Ψ : ℝ → ℝ → ℝ) (hk : 1 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn
        (Function.uncurry (fun z θ : ℝ => (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro j hj a b ha hab
  -- ## The hypothesis data
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hm1 : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hm2 : Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := h.memA
  have hm1s : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) := by
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using (hΨ.pth).pth
  have hm2s : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 Ψ p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      ((contDiffOn_fst (𝕜 := ℝ) (s := Work.FTS.EllipticEst.Q0)).pow 2).mul (hΨ.pzIter 2)
    exact h2
  set F2 : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hF2def
  -- ## The constants
  set S0 : ℝ := ∫ θ in Iθ, SS θ with hS0
  have hS0nn : 0 ≤ S0 := by rw [hS0]; exact ws_sEta_integral_nonneg
  set K0 : ℝ := 4 * Real.pi ^ 2 * (1 + S0) with hK0
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    have h1 : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith
  obtain ⟨KA, KB, KA', KB', hKAnn, hKBnn, hKA'nn, hKB'nn, bA, bB, bA', bB'⟩ :=
    ws_midpoint_bounds hΨ ha
  set A0 : ℝ := 2 * KA + K0 * (1 + KB) with hA0
  have hA0nn : 0 ≤ A0 := by rw [hA0]; nlinarith [hKAnn, hKBnn, hK0nn]
  set A1 : ℝ := 2 * KA' + K0 * (1 + KB') with hA1
  have hA1nn : 0 ≤ A1 := by rw [hA1]; nlinarith [hKA'nn, hKB'nn, hK0nn]
  set Q1 : ℝ := (1 + b ^ 2) * (A0 + A1 + K0 + 1) with hQ1
  have hQ1ge1 : 1 ≤ Q1 := by
    rw [hQ1]
    have h1 : (0 : ℝ) ≤ b ^ 2 := sq_nonneg b
    have h2 : 1 ≤ A0 + A1 + K0 + 1 := by linarith
    nlinarith
  have hQ1nn : 0 ≤ Q1 := le_trans zero_le_one hQ1ge1
  set Cb : ℝ := 4 * Q1 with hCb
  have hCbnn : 0 ≤ Cb := by rw [hCb]; linarith
  set Ct : ℝ := Cb * (S0 + 2) with hCt
  have hCtnn : 0 ≤ Ct := by rw [hCt]; nlinarith [hCbnn, hS0nn]
  -- ## The two pointwise Poincaré bounds
  have hpsi : ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Ψ s θ) ^ 2 ≤ A0 + K0 * wsRef Ψ s := by
    intro s hs θ hθ
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hslice : ContDiffOn ℝ 2 (fun θ => Ψ s θ) (Set.Ioo 0 (Real.pi / 2)) :=
      contDiffOn_iff_forall_nat_le.mp (hΨ.curry_θ hspos) 2 le_top
    have hE : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv (fun t => deriv (fun θ' => Ψ s θ') t) θ) ^ 2 * SS θ) Iθ :=
      ws_slot_slice (g := Work.Spaces.pthIter 2 Ψ) hm1s hm1 0 (Nat.zero_le k) hspos
    have hp := ws_slice_pointwise_le hslice hE θ hθ
    have hTE : (∫ s_1 in Iθ,
          (deriv (fun t => deriv (fun θ' => Ψ s θ') t) s_1) ^ 2 * SS s_1)
        = thetaE (Work.Spaces.pthIter 2 Ψ) s := rfl
    rw [hTE, ← hS0, ← hK0] at hp
    have hb1 : 2 * (Ψ s (Real.pi / 4)) ^ 2 ≤ 2 * KA := by linarith [bA s hs]
    have hb2 : (deriv (fun θ => Ψ s θ) (Real.pi / 4)) ^ 2 ≤ KB := bB s hs
    have hb3 : K0 * (1 + ((deriv (fun θ => Ψ s θ) (Real.pi / 4)) ^ 2
        + thetaE (Work.Spaces.pthIter 2 Ψ) s))
        ≤ K0 * (1 + (KB + wsRef Ψ s)) := by
      refine mul_le_mul_of_nonneg_left ?_ hK0nn
      linarith [hb2, wsRef_ge_1 Ψ s]
    rw [hA0]
    linarith [hp, hb1, hb3, wsRef_ge_1 Ψ s]
  have hpz : ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ A1 + K0 * ((1 / s ^ 2)
            * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s) := by
    intro s hs θ hθ
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have h := ws_pz_slice_pointwise_le hΨ hk hm1 hspos (bA' s hs) (bB' s hs) θ hθ
    rw [← hS0, ← hK0] at h
    rw [hA1]
    linarith [h]
  -- ## The pointwise chain for `D_z^m`
  have hDz0 : ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Ψ s θ) ^ 2 ≤ Q1 * (1 + wsRef Ψ s) := by
    intro s hs θ hθ
    have h := hpsi s hs θ hθ
    have hR := wsRef_nonneg Ψ s
    have h1 : 0 ≤ 1 + wsRef Ψ s := by linarith
    have h2 : A0 + K0 * wsRef Ψ s ≤ (A0 + K0) * (1 + wsRef Ψ s) := by nlinarith
    have h3 : A0 + K0 ≤ Q1 := by
      rw [hQ1]
      nlinarith [hA1nn, hK0nn, sq_nonneg b]
    nlinarith [h, h2, h3, h1]
  have hDz1 : ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.DzIter 1 Ψ s θ) ^ 2 ≤ Q1 * (1 + wsRef Ψ s) := by
    intro s hs θ hθ
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hid : (Work.Spaces.DzIter 1 Ψ s θ) ^ 2
        = s ^ 2 * (Work.Spaces.pz Ψ s θ) ^ 2 := by
      show (s * Work.Spaces.pz Ψ s θ) ^ 2 = s ^ 2 * (Work.Spaces.pz Ψ s θ) ^ 2
      ring
    have h := hpz s hs θ hθ
    have hTE2 := wsRef_ge_2 Ψ s
    have hR := wsRef_nonneg Ψ s
    have hs2 : s ^ 2 ≤ b ^ 2 := by nlinarith [ha, hs.1, hs.2]
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hkey : s ^ 2 * (A1 + K0 * ((1 / s ^ 2)
        * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s))
        = s ^ 2 * A1 + K0 * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := by
      field_simp
    have hmid : s ^ 2 * A1 + K0 * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
        ≤ (b ^ 2 * A1 + K0) * (1 + wsRef Ψ s) := by
      have h1 : s ^ 2 * A1 ≤ b ^ 2 * A1 := by nlinarith [hA1nn]
      have h2 : K0 * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s
          ≤ K0 * wsRef Ψ s := mul_le_mul_of_nonneg_left hTE2 hK0nn
      have h3 : 0 ≤ b ^ 2 * A1 + K0 := by nlinarith [hA1nn, hK0nn, sq_nonneg b]
      have h4 : 0 ≤ wsRef Ψ s := hR
      have h5 : 0 ≤ b ^ 2 * A1 := by nlinarith [hA1nn, sq_nonneg b]
      nlinarith [h1, h2, h3, h4, h5]
    have hQ1ge : b ^ 2 * A1 + K0 ≤ Q1 := by
      rw [hQ1]
      nlinarith [hA0nn, hK0nn, sq_nonneg b]
    have h1 : 0 ≤ 1 + wsRef Ψ s := by linarith
    rw [hid]
    calc s ^ 2 * (Work.Spaces.pz Ψ s θ) ^ 2
        ≤ s ^ 2 * (A1 + K0 * ((1 / s ^ 2)
            * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg s)
      _ = s ^ 2 * A1 + K0 * thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s := hkey
      _ ≤ (b ^ 2 * A1 + K0) * (1 + wsRef Ψ s) := hmid
      _ ≤ Q1 * (1 + wsRef Ψ s) := mul_le_mul_of_nonneg_right hQ1ge h1
  have hDz2 : ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.DzIter 2 Ψ s θ) ^ 2
        ≤ 2 * Q1 * (1 + wsRef Ψ s) + 2 * (F2 s θ) ^ 2 := by
    intro s hs θ hθ
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hid : Work.Spaces.DzIter 2 Ψ s θ = Work.Spaces.DzIter 1 Ψ s θ + F2 s θ := by
      have h0 := ws_DzIter_two_eq hΨ hspos hθ
      rw [hF2def]
      exact h0
    have h1 := hDz1 s hs θ hθ
    have h2 : (Work.Spaces.DzIter 2 Ψ s θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter 1 Ψ s θ) ^ 2 + 2 * (F2 s θ) ^ 2 := by
      rw [hid]
      nlinarith [sq_nonneg (Work.Spaces.DzIter 1 Ψ s θ - F2 s θ)]
    linarith [h1, h2]
  have hDz3 : ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.DzIter 3 Ψ s θ) ^ 2
        ≤ 4 * Q1 * (1 + wsRef Ψ s) + 4 * (F2 s θ) ^ 2
          + 2 * (Work.Spaces.DzIter 1 F2 s θ) ^ 2 := by
    intro s hs θ hθ
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hid : Work.Spaces.DzIter 3 Ψ s θ
        = Work.Spaces.DzIter 2 Ψ s θ + Work.Spaces.DzIter 1 F2 s θ := by
      have h0 := ws_DzIter_three_eq hΨ hspos hθ
      rw [← hF2def] at h0
      exact h0
    have h1 := hDz2 s hs θ hθ
    have h2 : (Work.Spaces.DzIter 3 Ψ s θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter 2 Ψ s θ) ^ 2
          + 2 * (Work.Spaces.DzIter 1 F2 s θ) ^ 2 := by
      rw [hid]
      nlinarith [sq_nonneg (Work.Spaces.DzIter 2 Ψ s θ - Work.Spaces.DzIter 1 F2 s θ)]
    linarith [h1, h2]
  -- ## The unified pointwise bound
  have hpoint : ∀ m : ℕ, m ≤ 3 → ∀ s ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (Work.Spaces.DzIter m Ψ s θ) ^ 2
        ≤ Cb * (1 + wsRef Ψ s)
          + Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) := by
    intro m hm s hs θ hθ
    have hgnn : 0 ≤ (F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2 := by positivity
    have hR : 0 ≤ 1 + wsRef Ψ s := by linarith [wsRef_nonneg Ψ s]
    have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rw [hCb]
    rcases hm4 with rfl | rfl | rfl | rfl
    · have h := hDz0 s hs θ hθ
      have hid0 : Work.Spaces.DzIter 0 Ψ s θ = Ψ s θ := rfl
      rw [hid0]
      have hQR : 0 ≤ Q1 * (1 + wsRef Ψ s) := mul_nonneg hQ1nn hR
      have hQS : 0 ≤ Q1 * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) :=
        mul_nonneg hQ1nn hgnn
      linarith [h, hQR, hQS]
    · have h := hDz1 s hs θ hθ
      have hQR : 0 ≤ Q1 * (1 + wsRef Ψ s) := mul_nonneg hQ1nn hR
      have hQS : 0 ≤ Q1 * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) :=
        mul_nonneg hQ1nn hgnn
      linarith [h, hQR, hQS]
    · have h := hDz2 s hs θ hθ
      have hQR : 0 ≤ Q1 * (1 + wsRef Ψ s) := mul_nonneg hQ1nn hR
      have hG2 : 0 ≤ (F2 s θ) ^ 2 := sq_nonneg _
      nlinarith [h, hQR, hQ1ge1, hgnn, hG2]
    · have h := hDz3 s hs θ hθ
      have hQR : 0 ≤ Q1 * (1 + wsRef Ψ s) := mul_nonneg hQ1nn hR
      have hG2 : 0 ≤ (F2 s θ) ^ 2 := sq_nonneg _
      have hH2 : 0 ≤ (Work.Spaces.DzIter 1 F2 s θ) ^ 2 := sq_nonneg _
      nlinarith [h, hQR, hQ1ge1, hgnn, hG2, hH2]
  -- ## The angular slices
  have hslF2_0 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.Integrable (fun θ : ℝ => (F2 s θ) ^ 2 * SS θ)
        (MeasureTheory.volume.restrict Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    exact ws_slot_slice hm2s hm2 0 (Nat.zero_le k) hspos
  have hslF2_1 : ∀ s ∈ Set.Icc a b,
      MeasureTheory.Integrable (fun θ : ℝ => (Work.Spaces.DzIter 1 F2 s θ) ^ 2 * SS θ)
        (MeasureTheory.volume.restrict Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    exact ws_slot_slice hm2s hm2 1 hk hspos
  have hsl : ∀ m : ℕ, m ≤ 3 → ∀ s ∈ Set.Icc a b,
      MeasureTheory.Integrable (fun θ : ℝ => (Work.Spaces.DzIter m Ψ s θ) ^ 2 * SS θ)
        (MeasureTheory.volume.restrict Iθ) := by
    intro m hm s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter m Ψ p.1 p.2) ^ 2 * SS p.2)
        Work.FTS.EllipticEst.Q0 :=
      ((hΨ.DzIter m).continuousOn.pow 2).mul ws_contOn_sEta
    have haesm : AEStronglyMeasurable
        (fun θ : ℝ => (Work.Spaces.DzIter m Ψ s θ) ^ 2 * SS θ)
        (MeasureTheory.volume.restrict Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hspos
    have h1 := hslF2_0 s hs
    have h2 := hslF2_1 s hs
    have hsum : MeasureTheory.Integrable
        (fun θ : ℝ => ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
        (MeasureTheory.volume.restrict Iθ) := by
      have h := h1.add h2
      refine h.congr ?_
      filter_upwards with θ
      simp only [Pi.add_apply]
      ring
    have hconst : MeasureTheory.Integrable
        (fun θ : ℝ => Cb * (1 + wsRef Ψ s) * SS θ) (MeasureTheory.volume.restrict Iθ) :=
      ws_sEta_integrableOn.const_mul (Cb * (1 + wsRef Ψ s))
    have hG : MeasureTheory.Integrable
        (fun θ : ℝ => Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
        (MeasureTheory.volume.restrict Iθ) := by
      have h := hsum.const_mul Cb
      refine h.congr ?_
      filter_upwards with θ
      ring
    have hdom : MeasureTheory.Integrable
        (fun θ : ℝ => Cb * (1 + wsRef Ψ s) * SS θ
          + Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
        (MeasureTheory.volume.restrict Iθ) :=
      hconst.add hG
    refine hdom.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, ws_ae_mem_Ioo]
      with θ hθI hθIoo
    have hSSnn : 0 ≤ SS θ := ws_sEta_nonneg hθI
    have hp := hpoint m hm s hs θ hθIoo
    have hmult := mul_le_mul_of_nonneg_right hp hSSnn
    have hnorm : ‖(Work.Spaces.DzIter m Ψ s θ) ^ 2 * SS θ‖
        = (Work.Spaces.DzIter m Ψ s θ) ^ 2 * SS θ :=
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hSSnn)
    rw [hnorm]
    nlinarith [hmult]
  -- ## The integrated `θ`-bounds
  have hint : ∀ m : ℕ, m ≤ 3 → MeasureTheory.Integrable
      (fun s : ℝ => thetaE (Work.Spaces.DzIter m Ψ) s)
      (MeasureTheory.volume.restrict (Set.Icc a b)) := by
    intro m hm
    have hvol : (MeasureTheory.volume : Measure ℝ) (Set.Icc a b) ≠ ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hconst : MeasureTheory.Integrable (fun _ : ℝ => (1 : ℝ))
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      MeasureTheory.integrableOn_const (C := (1 : ℝ)) hvol
    have hRefint : MeasureTheory.Integrable (wsRef Ψ)
        (MeasureTheory.volume.restrict (Set.Icc a b)) := by
      have h1 : MeasureTheory.Integrable (fun s => thetaE (Work.Spaces.pthIter 2 Ψ) s)
          (MeasureTheory.volume.restrict (Set.Icc a b)) :=
        ws_thetaE_Icc_integrable hm1s hm1 0 (Nat.zero_le k) ha
      have h2 : MeasureTheory.Integrable
          (fun s => thetaE (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) s)
          (MeasureTheory.volume.restrict (Set.Icc a b)) :=
        ws_thetaE_Icc_integrable hm1s hm1 1 hk ha
      have h3 : MeasureTheory.Integrable
          (fun s => thetaE (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s)
          (MeasureTheory.volume.restrict (Set.Icc a b)) :=
        ws_thetaE_Icc_integrable hm2s hm2 0 (Nat.zero_le k) ha
      have h4 : MeasureTheory.Integrable
          (fun s => thetaE
            (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) s)
          (MeasureTheory.volume.restrict (Set.Icc a b)) :=
        ws_thetaE_Icc_integrable hm2s hm2 1 hk ha
      have hsum := ((h1.add h2).add h3).add h4
      refine hsum.congr ?_
      filter_upwards with s
      rfl
    have hbase : MeasureTheory.Integrable (fun s : ℝ => Ct * (1 + wsRef Ψ s))
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      (hconst.add hRefint).const_mul Ct
    refine hbase.mono' ?_ ?_
    · have hcont : ContinuousOn
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter m Ψ p.1 p.2) ^ 2 * SS p.2)
          Work.FTS.EllipticEst.Q0 :=
        ((hΨ.DzIter m).continuousOn.pow 2).mul ws_contOn_sEta
      have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
        fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
      have hle : (MeasureTheory.volume.restrict (Set.Icc a b)).prod
            (MeasureTheory.volume.restrict Iθ)
          ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Iθ) :=
        MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable
          (fun p : ℝ × ℝ => (Work.Spaces.DzIter m Ψ p.1 p.2) ^ 2 * SS p.2)
          ((MeasureTheory.volume.restrict (Set.Icc a b)).prod
            (MeasureTheory.volume.restrict Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).mono_measure hle
      have h2 := hAEj.integral_prod_right' (μ := MeasureTheory.volume.restrict (Set.Icc a b))
        (ν := MeasureTheory.volume.restrict Iθ)
      simpa only [thetaE] using h2
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
      have hspos : 0 < s := lt_of_lt_of_le ha hs.1
      have h1 := hslF2_0 s hs
      have h2 := hslF2_1 s hs
      have hsum : MeasureTheory.Integrable
          (fun θ : ℝ => ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
          (MeasureTheory.volume.restrict Iθ) := by
        have h := h1.add h2
        refine h.congr ?_
        filter_upwards with θ
        simp only [Pi.add_apply]
        ring
      have hconst : MeasureTheory.Integrable
          (fun θ : ℝ => Cb * (1 + wsRef Ψ s) * SS θ) (MeasureTheory.volume.restrict Iθ) :=
        ws_sEta_integrableOn.const_mul (Cb * (1 + wsRef Ψ s))
      have hG : MeasureTheory.Integrable
          (fun θ : ℝ => Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
          (MeasureTheory.volume.restrict Iθ) := by
        have h := hsum.const_mul Cb
        refine h.congr ?_
        filter_upwards with θ
        ring
      have hdomint : MeasureTheory.Integrable
          (fun θ : ℝ => Cb * (1 + wsRef Ψ s) * SS θ
            + Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
          (MeasureTheory.volume.restrict Iθ) :=
        hconst.add hG
      have hnonneg : (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[MeasureTheory.volume.restrict Iθ]
          (fun θ : ℝ => (Work.Spaces.DzIter m Ψ s θ) ^ 2 * SS θ) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hθ)
      have hle2 : (fun θ : ℝ => (Work.Spaces.DzIter m Ψ s θ) ^ 2 * SS θ)
          ≤ᵐ[MeasureTheory.volume.restrict Iθ]
          (fun θ : ℝ => Cb * (1 + wsRef Ψ s) * SS θ
            + Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc, ws_ae_mem_Ioo]
          with θ hθI hθIoo
        have hSSnn : 0 ≤ SS θ := ws_sEta_nonneg hθI
        have hp := hpoint m hm s hs θ hθIoo
        nlinarith [mul_le_mul_of_nonneg_right hp hSSnn]
      have hstep1 : thetaE (Work.Spaces.DzIter m Ψ) s
          ≤ ∫ θ in Iθ, (Cb * (1 + wsRef Ψ s) * SS θ
              + Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ) :=
        MeasureTheory.integral_mono_of_nonneg hnonneg hdomint hle2
      have hstep2 : (∫ θ in Iθ, (Cb * (1 + wsRef Ψ s) * SS θ
              + Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ))
          = Cb * (1 + wsRef Ψ s) * S0
            + Cb * (thetaE F2 s + thetaE (Work.Spaces.DzIter 1 F2) s) := by
        rw [MeasureTheory.integral_add hconst hG]
        congr 1
        · rw [MeasureTheory.integral_const_mul, hS0]
        · rw [show (fun θ : ℝ => Cb * ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
              = fun θ : ℝ => Cb * (((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
              from by funext θ; ring]
          rw [MeasureTheory.integral_const_mul]
          congr 1
          rw [show (fun θ : ℝ => ((F2 s θ) ^ 2 + (Work.Spaces.DzIter 1 F2 s θ) ^ 2) * SS θ)
              = fun θ : ℝ => (F2 s θ) ^ 2 * SS θ
                + (Work.Spaces.DzIter 1 F2 s θ) ^ 2 * SS θ from by
            funext θ; ring]
          rw [MeasureTheory.integral_add h1 h2]
          rfl
      have hstep3 : Cb * (1 + wsRef Ψ s) * S0
            + Cb * (thetaE F2 s + thetaE (Work.Spaces.DzIter 1 F2) s)
          ≤ Ct * (1 + wsRef Ψ s) := by
        have h3 := wsRef_ge_3 Ψ s
        have h4 := wsRef_ge_4 Ψ s
        have hR := wsRef_nonneg Ψ s
        rw [hCt]
        nlinarith [h3, h4, hS0nn, hCbnn, hR]
      have hfin : thetaE (Work.Spaces.DzIter m Ψ) s ≤ Ct * (1 + wsRef Ψ s) :=
        le_trans hstep1 (le_trans (le_of_eq hstep2) hstep3)
      have hnorm : ‖thetaE (Work.Spaces.DzIter m Ψ) s‖
          = thetaE (Work.Spaces.DzIter m Ψ) s :=
        Real.norm_of_nonneg (thetaE_nonneg (Work.Spaces.DzIter m Ψ) s)
      rw [hnorm]
      exact hfin
  -- ## Box integrability of the slots `D_z^m Ψ`, `m ∈ {1,2,3}`
  have hbox : ∀ m : ℕ, m ≤ 3 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter m Ψ z θ) ^ 2 * SS θ))
      (Set.Icc a b ×ˢ Iθ) := by
    intro m hm
    refine Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg ha hab ?_ ?_ ?_ ?_
    · exact ((hΨ.DzIter m).continuousOn.pow 2).mul ws_contOn_sEta
    · intro z hz θ hθ
      exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hθ)
    · intro s hs
      exact hsl m hm s hs
    · exact hint m hm
  -- ## Back to `∂_z D_z^j Ψ = D_z^{j+1} Ψ / z`
  have hm3 : j + 1 ≤ 3 := by omega
  have hboxm : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter (j + 1) Ψ z θ) ^ 2 * SS θ))
      (Set.Icc a b ×ˢ Iθ) := hbox (j + 1) hm3
  have hdom : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter (j + 1) Ψ p.1 p.2) ^ 2 * SS p.2 / a ^ 2)
      (Set.Icc a b ×ˢ Iθ) := by
    have h := hboxm.const_mul ((a ^ 2)⁻¹)
    refine h.congr ?_
    filter_upwards with p
    have hfun : Function.uncurry
        (fun z θ : ℝ => (Work.Spaces.DzIter (j + 1) Ψ z θ) ^ 2 * SS θ) p
        = (Work.Spaces.DzIter (j + 1) Ψ p.1 p.2) ^ 2 * SS p.2 := rfl
    rw [hfun, div_eq_mul_inv]
    ring_nf
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hcont : ContinuousOn
        (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2 * SS p.2)
        Work.FTS.EllipticEst.Q0 :=
      (((hΨ.DzIter j).pz).continuousOn.pow 2).mul ws_contOn_sEta
    have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
      fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
    have hle : (MeasureTheory.volume.restrict (Set.Icc a b)).prod
          (MeasureTheory.volume.restrict Iθ)
        ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Iθ) :=
      MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl
    have hboxmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Iθ)
        = (MeasureTheory.volume.restrict (Set.Icc a b)).prod
            (MeasureTheory.volume.restrict Iθ) :=
      Work.FTS.EllipticEst.volume_restrict_box a b
    rw [hboxmeas]
    exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).mono_measure hle
  · filter_upwards [MeasureTheory.self_mem_ae_restrict
      (measurableSet_Icc.prod (show MeasurableSet Iθ from measurableSet_Icc))] with p hp
    obtain ⟨hzz, hθθ⟩ := hp
    have hz1 : 0 < p.1 := lt_of_lt_of_le ha hzz.1
    have hSSnn : 0 ≤ SS p.2 := ws_sEta_nonneg hθθ
    have hid : Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2
        = Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 / p.1 := by
      have h0 : Work.Spaces.DzIter (j + 1) Ψ p.1 p.2
          = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2 := rfl
      rw [h0, mul_div_cancel_left₀ _ (ne_of_gt hz1)]
    have ha2 : 0 < a ^ 2 := by positivity
    have hz2 : a ^ 2 ≤ p.1 ^ 2 := pow_le_pow_left₀ (le_of_lt ha) hzz.1 2
    change ‖(Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2 * SS p.2‖
      ≤ Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 * SS p.2 / a ^ 2
    have hnorm : ‖(Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2 * SS p.2‖
        = (Work.Spaces.pz (Work.Spaces.DzIter j Ψ) p.1 p.2) ^ 2 * SS p.2 :=
      Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hSSnn)
    rw [hnorm, hid, div_pow]
    have hstep : (Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 / p.1 ^ 2) * SS p.2
        ≤ (Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 / a ^ 2) * SS p.2 := by
      have hX : 0 ≤ Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 := sq_nonneg _
      have h1 : Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 / p.1 ^ 2
          ≤ Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 / a ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ ha2 hz2) hX
      exact mul_le_mul_of_nonneg_right h1 hSSnn
    calc (Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 / p.1 ^ 2) * SS p.2
        ≤ (Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 / a ^ 2) * SS p.2 := hstep
      _ = Work.Spaces.DzIter (j + 1) Ψ p.1 p.2 ^ 2 * SS p.2 / a ^ 2 := by ring_nf

end Work.FTS.EllipticEst.remov
