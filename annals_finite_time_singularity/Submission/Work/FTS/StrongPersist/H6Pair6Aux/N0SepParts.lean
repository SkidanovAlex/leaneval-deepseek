/-
# `H6Pair6Aux/N0SepParts` — the three *separated* pieces of the `N₀`-row at level six

The `N₀`-row of the level-six modulation table contains the three terms

* `N04a α F f = (3/(2α))·sin(2θ)·L₁₂ f ·∂_θF_*`,
* `N05a α F f = -c2m(θ)·L₁₂ f ·D_zF_*`,
* `N06  α F f = -c2m(θ)·L₁₂(F_*)·D_zf`

(`F = F_* + f`).  Using the two explicit forms of the `F_*`-derivatives,

* `∂_θF_* = α·(Γ'/c)·φ`  (`pth_Fstar_eq`, on the open quadrant),
* `D_zF_* = α·(Γ/c)·D_zφ`  (`Dz_Fstar_eq`, for `z > 0`),

each of the three terms is a *separated* product `a(θ)·ρ(z)`, where the angular profile is
built from `Γ` and its `dthU`-iterates (`qfun·Γ`, `c2m·Γ`) and the radial profile from
`L₁₂ f` and the bounded function `φ = FM.Fstar` or its first `D_z`-jet.  The membership
`HkMem α 6` of such a product is the content of `sep_mem6_local`, whose angular input is the
jet bound `(dthU^[i] a)² ≤ B1·sin(2θ)^{2α/5}`, `1 ≤ i ≤ 6` (`Γ ≤ sin(2θ)^{α/5}` together
with the jet bounds `GamQfun_dthU_Iθ` / `H6N_GammaTerm_Lop_bound`), and whose radial input is
the slot integrability coming from `slots_radial_mul` (`L12slotLe7` for the `L₁₂ f` factor and
`FstarJet7` for the `φ`-factor).

`N06` is different in kind: there `L₁₂(F_*) = 2α/(1+z)` is *explicit*, so the term is the
radial multiplier `2α/(1+z)` applied to the honest field `-c2m(θ)·D_zf` (`RadialMul6`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NAngAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.c2mGam_Wt_bound
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12FieldsAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SepMem6Local
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RadialMul6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RadialSlots
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
import Submission.Work.FTS.StrongPersist.RMul6.Defs
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Construction.H6N_GammaTerm_Lop_bound
import Submission.Work.FTS.Nonlinear.Open.Row23

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2400000

/-! ## The one-variable `dthU`-calculus -/

/-- `dthU` is linear in the constant: `dthU (c·g) = c·dthU g`. -/
theorem dthU_const_mul (c : ℝ) (g : ℝ → ℝ) :
    Work.Spaces.dthU (fun θ => c * g θ) = fun θ => c * Work.Spaces.dthU g θ := by
  funext θ
  simp only [Work.Spaces.dthU_apply, deriv_const_mul_field]
  ring

/-- The iterate of `dthU` is linear in the constant. -/
theorem dthU_iter_const_mul (c : ℝ) (g : ℝ → ℝ) (i : ℕ) :
    (Work.Spaces.dthU^[i]) (fun θ => c * g θ)
      = fun θ => c * (Work.Spaces.dthU^[i]) g θ := by
  induction i generalizing g with
  | zero => rfl
  | succ n ih =>
      show (Work.Spaces.dthU^[n]) (Work.Spaces.dthU (fun θ => c * g θ))
        = fun θ => c * (Work.Spaces.dthU^[n]) (Work.Spaces.dthU g) θ
      rw [dthU_const_mul c g]
      exact ih (Work.Spaces.dthU g)

/-- At a point where `sin(2θ) = 0` every positive iterate of `dthU` vanishes. -/
theorem dthU_iter_eq_zero_of_sin_eq_zero {g : ℝ → ℝ} {θ : ℝ} (i : ℕ) (hi : 1 ≤ i)
    (h : Real.sin (2 * θ) = 0) : (Work.Spaces.dthU^[i]) g θ = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  simp only [Work.Spaces.dthU_apply, h, zero_mul]

/-- `(sin(2θ)^κ)² = sin(2θ)^{2κ}` on the open interval. -/
theorem sq_sin_rpow {κ θ : ℝ} (hs : 0 < Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ κ) ^ 2 = (Real.sin (2 * θ)) ^ (2 * κ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hs)]
  congr 1
  ring

/-- `|c2m θ| ≤ 2` for every `θ`. -/
theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      = |Real.cos (2 * θ) + -(Real.sin θ ^ 2)| := by ring_nf
    _ ≤ |Real.cos (2 * θ)| + |-(Real.sin θ ^ 2)| := abs_add_le _ _
    _ = |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by rw [abs_neg]
    _ ≤ 1 + 1 := by
        have hs : |Real.sin θ ^ 2| ≤ 1 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact Real.sin_sq_le_one θ
        have hc := Real.abs_cos_le_one (2 * θ)
        linarith
    _ = 2 := by norm_num

/-- **The angular reduction.**  It suffices to bound the `dthU`-iterates of an angular
profile on the *open* interval `(0,π/2)`: at the two endpoints every positive iterate
vanishes, and so does `sin(2θ)^{2κ}`. -/
theorem dthU_iter_sq_le_sin_aux {a : ℝ → ℝ} {κ B1 : ℝ} (hκ : 0 < κ)
    (hint : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ((Work.Spaces.dthU^[i]) a θ) ^ 2 ≤ B1 * (Real.sin (2 * θ)) ^ (2 * κ)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      ((Work.Spaces.dthU^[i]) a θ) ^ 2 ≤ B1 * (Real.sin (2 * θ)) ^ (2 * κ) := by
  intro i hi1 hi6 θ hθ
  by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · exact hint i hi1 hi6 θ hθo
  · have hs : Real.sin (2 * θ) = 0 := sin_two_zero_of_not_Ioo hθ hθo
    rw [dthU_iter_eq_zero_of_sin_eq_zero i hi1 hs, hs,
      Real.zero_rpow (ne_of_gt (by linarith : (0 : ℝ) < 2 * κ))]
    simp

/-! ## The radial profile `φ = FM.Fstar = 2z/(1+z)²` -/

/-- All finite orders of smoothness of `φ` on `(0,∞)`. -/
theorem Fstar_contDiffOn : ∀ m : ℕ, ContDiffOn ℝ m Work.FM.Fstar (Set.Ioi 0) := by
  intro m
  have h1 : ContDiffOn ℝ m (fun z : ℝ => 2 * z) (Set.Ioi 0) :=
    contDiffOn_const.mul contDiffOn_id
  show ContDiffOn ℝ m (fun z : ℝ => 2 * z / (1 + z) ^ 2) (Set.Ioi 0)
  exact h1.div ((contDiffOn_const.add contDiffOn_id).pow 2)
    (fun z hz => by have hz' : (0 : ℝ) < z := hz; positivity)

/-- All finite orders of smoothness of the first `D_z`-jet of `φ`. -/
theorem Fstar_shift_contDiffOn :
    ∀ n : ℕ, ContDiffOn ℝ n (fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z) (Set.Ioi 0) := by
  intro n
  exact Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial
    (r := Work.FM.Fstar) (n := n + 1) (fun m _ => Fstar_contDiffOn m)
    (a := 1) (t := n) (by omega)

/-- **The `z`-jet bounds of `φ` and of its first jet.**  `DzdIter m φ = DzdIter (m-1) (DzdIter 1 φ)`
as functions, so the order-seven bound of `FstarJet7` transfers to the shifted family. -/
theorem Fstar_jets_shift (M₂ : ℝ)
    (hM₂ : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M₂) :
    (∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter j Work.FM.Fstar z| ≤ M₂) ∧
      (∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter j (fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z) z| ≤ M₂) := by
  have hshift : ∀ m : ℕ, Work.Elliptic.DzdIter m
      (fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
        = Work.Elliptic.DzdIter (m + 1) Work.FM.Fstar := by
    intro m
    induction m with
    | zero => rfl
    | succ k ih =>
        rw [Work.Elliptic.DzdIter_succ, ih, Work.Elliptic.DzdIter_succ]
        rfl
  exact ⟨fun j hj z hz => hM₂ j (by omega) z hz,
    fun j hj z hz => by rw [hshift j]; exact hM₂ (j + 1) (by omega) z (le_of_lt hz)⟩

/-- The smoothness of the `L₁₂ f`-factor and the slot integrability of its `D_z`-jets. -/
theorem L12_slots6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z))
    (h0 : Work.Construction.L12 f 0 = 0)
    (m6 : Work.Spaces.HkMem α 6 f) (m7 : Work.Spaces.HkMem α 7 f) :
    ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) ∧
      (∀ b : ℕ, b ≤ 6 → MeasureTheory.IntegrableOn
        (fun z : ℝ => (Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 f z) z
          * Work.Spaces.w z) ^ 2) Work.Spaces.Iz) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := L12slotLe7
  exact ⟨curry_six hL, fun b hb => ((hC₁ α f hα hα1 hf m6 m7 h0 b (by omega)).1).congr
    (Filter.Eventually.of_forall fun z => by ring)⟩

/-- The `-c2m(θ)·D_z f`-field is honest in `ℋ⁶` (`c2m = cos 2θ - sin²θ = -1 + 3sin²θ`). -/
theorem c2m_Dz_mem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) := by
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le hf m7
  have hsin2sm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) :=
    so_snd ((Real.contDiff_sin).pow 2)
  obtain ⟨_, _, hmul⟩ := Work.Blocks.HkMul_ang_le 6
  obtain ⟨-, -, hmain⟩ := hmul α (Work.Spaces.Dz f) hα hα1 hf.Dz
  obtain ⟨-, -, hs2mem, -⟩ := hmain hDzmem
  have h1 : Work.Spaces.HkMem α 6 (fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 (-1) hDzmem
  have h2 : Work.Spaces.HkMem α 6
      (fun z θ => (3 : ℝ) * (Real.sin θ ^ 2 * Work.Spaces.Dz f z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 6 3 hs2mem
  have hsm1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-1 : ℝ) * Work.Spaces.Dz f z θ) :=
    so_const_mul (-1) hf.Dz
  have hsm2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 : ℝ) * (Real.sin θ ^ 2 * Work.Spaces.Dz f z θ)) :=
    so_const_mul 3 (so_mul hsin2sm hf.Dz)
  have hsum := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 6 hsm1 hsm2 h1 h2
  refine Work.Coercivity.HkMem_congr_Ioi α 6 hsum ?_
  intro z hz θ hθ
  rw [Work.Construction.c2m_eq, Real.cos_two_mul, Real.sin_sq]
  ring

/-! ## The term `N04a` -/

theorem N04a_mem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z))
    (h0 : Work.Construction.L12 f 0 = 0)
    (m6 : Work.Spaces.HkMem α 6 f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (fun z θ =>
      Work.Construction.N04a α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) := by
  obtain ⟨M₂, hM₂pos, hM₂⟩ := FstarJet7
  obtain ⟨hFj6, _⟩ := Fstar_jets_shift M₂ hM₂
  obtain ⟨hΛc, hΛslot⟩ := L12_slots6 hα hα1 hf hL h0 m6 m7
  set Λ : ℝ → ℝ := fun z => Work.Construction.L12 f z with hΛdef
  have hcg : 0 < Work.Spaces.c α := by
    linarith [(Work.Spaces.c_bounds α hα hα1).1]
  have hslot1 : ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z => Λ z * Work.FM.Fstar z) z
        * Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    slots_radial_mul (X := Λ) (r := fun z => Work.FM.Fstar z) (M := M₂)
      hΛc (Fstar_contDiffOn 6) hΛslot (fun m hm z hz => hFj6 m (by omega) z (le_of_lt hz))
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      ((3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
        * (Λ z * Work.FM.Fstar z)) :=
    so_mul (so_const_mul _ (smoothOpen_qfunGam α))
      (so_mul hL (so_radial (fun m => Fstar_contDiffOn m)))
  have hmem : Work.Spaces.HkMem α 6 (fun z θ =>
      ((3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
        * (Λ z * Work.FM.Fstar z)) := by
    refine sep_mem6_local
      (a := fun θ => (3 * α / (2 * Work.Spaces.c α))
        * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
      (ρ := fun z => Λ z * Work.FM.Fstar z)
      (κ := α / 5) (B0 := |3 * α / (2 * Work.Spaces.c α)| * (4 / 3))
      (B1 := (3 * α / (2 * Work.Spaces.c α)) ^ 2 * gamqK ^ 2)
      (by positivity) (by positivity) ?_ ?_ ?_ hsm hslot1
    · simp only [Work.Spaces.gam]; linarith
    · intro θ hθ
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun, abs_le]
        constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hqG : |Work.Spaces.qfun θ * Work.Spaces.Gam α θ| ≤ 4 / 3 := by
        rw [abs_mul, abs_of_nonneg hG0]
        calc |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ ≤ (4 / 3) * 1 :=
              mul_le_mul hq hG1 hG0 (by norm_num)
          _ = 4 / 3 := by ring
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hqG (abs_nonneg _)
    · have hinterior : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ((Work.Spaces.dthU^[i])
            (fun θ' => (3 * α / (2 * Work.Spaces.c α))
              * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ')) θ) ^ 2
            ≤ ((3 * α / (2 * Work.Spaces.c α)) ^ 2 * gamqK ^ 2)
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
        intro i hi1 hi6 θ hθo
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθo.1])
            (by linarith [hθo.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθo.1, le_of_lt hθo.2⟩
        have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
        have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
        have hjet : |(Work.Spaces.dthU^[i])
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ|
            ≤ gamqK * (Real.sin (2 * θ)) ^ (α / 5) := by
          have h := GamQfun_dthU_Iθ α hα hα1 i hi6 θ hθI
          rw [show (fun t => Work.Spaces.Gam α t * Work.Spaces.qfun t)
              = fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t from by
            funext t; ring] at h
          exact h.trans (mul_le_mul_of_nonneg_left hGle gamqK_nonneg)
        have hsq : ((Work.Spaces.dthU^[i])
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2
            ≤ (gamqK * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hjet 2
          rwa [sq_abs] at h2
        have hconst : (Work.Spaces.dthU^[i])
            (fun θ' => (3 * α / (2 * Work.Spaces.c α))
              * (Work.Spaces.qfun θ' * Work.Spaces.Gam α θ'))
            = fun θ' => (3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
                (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ' :=
          dthU_iter_const_mul (3 * α / (2 * Work.Spaces.c α))
            (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) i
        rw [hconst]
        calc ((3 * α / (2 * Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
              (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2
            = (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * ((Work.Spaces.dthU^[i])
                (fun t => Work.Spaces.qfun t * Work.Spaces.Gam α t) θ) ^ 2 := by ring
          _ ≤ (3 * α / (2 * Work.Spaces.c α)) ^ 2
              * (gamqK * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (3 * α / (2 * Work.Spaces.c α)) ^ 2 * gamqK ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
              rw [mul_pow, sq_sin_rpow hsin]
              ring
      exact dthU_iter_sq_le_sin_aux (a := fun θ => (3 * α / (2 * Work.Spaces.c α))
          * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ))
        (κ := α / 5) (B1 := (3 * α / (2 * Work.Spaces.c α)) ^ 2 * gamqK ^ 2)
        (by positivity) hinterior
  refine Work.Coercivity.HkMem_congr_Ioi α 6 hmem ?_
  intro z hz θ hθ
  simp only [Work.Construction.N04a, Work.Construction.s2_eq]
  by_cases hθo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · rw [pth_Fstar_eq α z θ hθo]
    have hα0 : α ≠ 0 := ne_of_gt hα
    have hc0 : Work.Spaces.c α ≠ 0 := ne_of_gt hcg
    have h2α : (2 : ℝ) * α ≠ 0 := by positivity
    have h2c : (2 : ℝ) * Work.Spaces.c α ≠ 0 := by positivity
    have hkey : Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ
        = α * (Work.Spaces.qfun θ * Work.Spaces.Gam α θ) := by
      rw [s2_deriv_Gam_Iθ α hα hθ]
      ring
    have hA : (3 / (2 * α)) * Real.sin (2 * θ) * Λ z
          * (α * (deriv (Work.Spaces.Gam α) θ / Work.Spaces.c α) * Work.FM.Fstar z)
        = (3 / (2 * α)) * α * (Work.Spaces.c α)⁻¹
          * (Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ)
          * (Λ z * Work.FM.Fstar z) := by ring
    rw [hA, hkey]
    first
      | (field_simp; ring)
      | field_simp
  · have hs : Real.sin (2 * θ) = 0 := sin_two_zero_of_not_Ioo hθ hθo
    have hG : Work.Spaces.Gam α θ = 0 := Gam_zero_of_not_Ioo hα hθ hθo
    rw [hs, hG]
    ring

/-! ## The term `N05a` -/

theorem N05a_mem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z))
    (h0 : Work.Construction.L12 f 0 = 0)
    (m6 : Work.Spaces.HkMem α 6 f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (fun z θ =>
      Work.Construction.N05a α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) := by
  obtain ⟨M₂, hM₂pos, hM₂⟩ := FstarJet7
  obtain ⟨_, hFj6'⟩ := Fstar_jets_shift M₂ hM₂
  obtain ⟨D, hDpos, hD⟩ := Work.Construction.H6N_GammaTerm_Lop_bound
  obtain ⟨hΛc, hΛslot⟩ := L12_slots6 hα hα1 hf hL h0 m6 m7
  set Λ : ℝ → ℝ := fun z => Work.Construction.L12 f z with hΛdef
  have hcg : 0 < Work.Spaces.c α := by
    linarith [(Work.Spaces.c_bounds α hα hα1).1]
  have hslot2 : ∀ j : ℕ, j ≤ 6 → MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (fun z =>
        Λ z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz :=
    slots_radial_mul (X := Λ) (r := fun z => Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
      (M := M₂) hΛc (Fstar_shift_contDiffOn 6) hΛslot
      (fun m hm z hz => hFj6' m (by omega) z hz)
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      (-(α / Work.Spaces.c α) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        * (Λ z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)) :=
    so_mul
      (so_const_mul (-(α / Work.Spaces.c α))
        (so_mul (so_snd contDiff_c2m) (Work.FTS.Nonlinear.Open.row23_smoothOpen_Gam α)))
      (so_mul hL (so_radial Fstar_shift_contDiffOn))
  have hmem : Work.Spaces.HkMem α 6 (fun z θ =>
      (-(α / Work.Spaces.c α) * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        * (Λ z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)) := by
    refine sep_mem6_local
      (a := fun θ => -(α / Work.Spaces.c α)
        * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
      (ρ := fun z => Λ z * Work.Elliptic.DzdIter 1 Work.FM.Fstar z)
      (κ := α / 5) (B0 := |α / Work.Spaces.c α| * 2)
      (B1 := (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
      (by positivity) (by positivity) ?_ ?_ ?_ hsm hslot2
    · simp only [Work.Spaces.gam]; linarith
    · intro θ hθ
      have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
      have hc2G : |Work.Construction.c2m θ * Work.Spaces.Gam α θ| ≤ 2 := by
        rw [abs_mul, abs_of_nonneg hG0]
        calc |Work.Construction.c2m θ| * Work.Spaces.Gam α θ ≤ 2 * 1 :=
              mul_le_mul (abs_c2m_le_two θ) hG1 hG0 (by norm_num)
          _ = 2 := by ring
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left hc2G (abs_nonneg _)
    · have hinterior : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ((Work.Spaces.dthU^[i])
            (fun θ' => -(α / Work.Spaces.c α)
              * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ')) θ) ^ 2
            ≤ ((α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
        intro i hi1 hi6 θ hθo
        have hsin : 0 < Real.sin (2 * θ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hθo.1])
            (by linarith [hθo.2, Real.pi_pos])
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθo.1, le_of_lt hθo.2⟩
        have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
        have hGle : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) :=
          Work.FTS.LocData.Gam_le_sin_two_rpow α hα hθI
        have hbd : |(Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
            ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) :=
          hD α hα hα1 i hi1 hi6 θ hθo
        have hsin2 : Real.sin (2 * θ) ^ 2 + α ≤ 2 := by
          have h1 := Real.sin_sq_le_one (2 * θ)
          linarith
        have h3 : 0 ≤ Real.sin (2 * θ) ^ 2 + α := by
          nlinarith [sq_nonneg (Real.sin (2 * θ)), hα.le]
        have h4 : 0 ≤ D * (Real.sin (2 * θ)) ^ (α / 5) :=
          mul_nonneg hDpos.le (Real.rpow_nonneg (le_of_lt hsin) _)
        have hstep : |(Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
            ≤ 2 * D * (Real.sin (2 * θ)) ^ (α / 5) := by
          calc |(Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ|
              ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := hbd
            _ ≤ D * (Real.sin (2 * θ)) ^ (α / 5) * 2 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hGle hDpos.le) hsin2 h3 h4
            _ = 2 * D * (Real.sin (2 * θ)) ^ (α / 5) := by ring
        have hsq : ((Work.Spaces.dthU^[i])
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2
            ≤ (2 * D * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 := by
          have h2 := pow_le_pow_left₀ (abs_nonneg _) hstep 2
          rwa [sq_abs] at h2
        have hconst : (Work.Spaces.dthU^[i])
            (fun θ' => -(α / Work.Spaces.c α)
              * (Work.Construction.c2m θ' * Work.Spaces.Gam α θ'))
            = fun θ' => -(α / Work.Spaces.c α) * (Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ' :=
          dthU_iter_const_mul (-(α / Work.Spaces.c α))
            (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) i
        rw [hconst]
        calc ((-(α / Work.Spaces.c α)) * (Work.Spaces.dthU^[i])
              (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2
            = (α / Work.Spaces.c α) ^ 2
              * ((Work.Spaces.dthU^[i])
                (fun t => Work.Construction.c2m t * Work.Spaces.Gam α t) θ) ^ 2 := by ring
          _ ≤ (α / Work.Spaces.c α) ^ 2
              * (2 * D * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (α / 5)) := by
              rw [mul_pow, sq_sin_rpow hsin]
              ring
      exact dthU_iter_sq_le_sin_aux (a := fun θ => -(α / Work.Spaces.c α)
          * (Work.Construction.c2m θ * Work.Spaces.Gam α θ))
        (κ := α / 5) (B1 := (α / Work.Spaces.c α) ^ 2 * (2 * D) ^ 2)
        (by positivity) hinterior
  refine Work.Coercivity.HkMem_congr_Ioi α 6 hmem ?_
  intro z hz θ hθ
  simp only [Work.Construction.N05a]
  rw [Dz_Fstar_eq α z θ hz]
  ring

/-! ## The term `N06` -/

theorem N06_mem {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (fun z θ =>
      Work.Construction.N06 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => 2 * α / (1 + z)) :=
    so_radial (fun n => (contDiffOn_const (c := 2 * α)).div
      (contDiffOn_const.add contDiffOn_id)
      (fun z hz => by have hz' : (0 : ℝ) < z := hz; positivity))
  have hXb : ∀ b : ℕ, b ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter b (fun z => 2 * α / (1 + z)) z| ≤ 2 * α * (250 * 720) :=
    inv_one_add_jets α hα
  have hψsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) :=
    so_mul (so_neg (so_snd contDiff_c2m)) hf.Dz
  have hψmem : Work.Spaces.HkMem α 6
      (fun z θ => -(Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) :=
    c2m_Dz_mem hα hα1 hf m7
  have hmain := RadialMul6 (α := α) (M := 2 * α * (250 * 720)) (by positivity)
    hXsm hXb hψsm hψmem
  refine Work.Coercivity.HkMem_congr_Ioi α 6 hmain ?_
  intro z hz θ hθ
  rw [Work.Construction.N06,
    Work.Construction.L12_Fstar_eq hα hα1 (le_of_lt hz)]
  ring

end Work.FTS.StrongPersist.H6Pair6Aux
