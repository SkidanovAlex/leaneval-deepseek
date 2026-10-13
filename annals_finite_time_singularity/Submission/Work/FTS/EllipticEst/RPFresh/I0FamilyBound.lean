import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.RPFresh.InterpState
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.interpS_theta
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.E2Mixed.E2model_mixed_split
import Submission.Work.FTS.EllipticEst.RPFresh.DdIntSlotBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `i0`-family of the mixed-derivative interpolation, `α`-uniform on `(0,1]`

For `V` smooth on a neighbourhood of the closed quadrant which vanishes on the two angular
boundaries, the sum over `r ≤ k` of the radial functionals `∫_z mixIntS (D_z^r V) z` is bounded
by the `ℋ^k`-squares of `z²∂_z²V`, `∂_θ²V` and `D_zV`:

`α² ∑_{r≤k} ∫_z mixIntS (D_z^r V) z ≤ C (α⁴ HkSq(z²∂_z²V) + HkSq(∂_θ²V) + α² HkSq(D_zV))`.

The single-function interpolation estimate (`Work.EllipticEst.Core.i0Aux.interpS_theta`, the
paper's §7 estimate, which holds for `α' ≤ 1/4` and for functions smooth on the strip
`(0,∞) × (-1, π/2+1)`) is applied to each `h = D_z^r V`; the three right-hand slots are then
bounded by the corresponding `ℋ^k`-slots (`ttIntS_integral_le_HkSq`, `dIntS_integral_le_HkSq`
and the `ddIntS`-slot lemma `DdIntSlotBound`, which replaces the `D_z²V`-slot by the `z²∂_z²V`-slot
via the Euler identity `D_z²V = z²∂_z²V + D_zV`).  Finally the estimate at the auxiliary exponent
`α' = min α (1/4)` is transferred to `α ∈ (0,1]` (the functionals do not depend on `α`), at the
cost of the factor `16`.

The proof rests only on the permitted axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

set_option autoImplicit false

/-! ## The Euler identity `z²∂_z²V = D_z²V - D_zV` -/

/-- **The pointwise Euler identity** on the open box `U = (-1,∞) × (-1,π/2+1)`:
`z² ∂_z²V = D_z²V - D_zV`, from `D_z²V = z∂_z(z∂_zV) = z∂_zV + z²∂_z²V`. -/
theorem zsq_pzIter_two_eq_U {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V)
    {p : ℝ × ℝ} (hp : p ∈ Work.Spaces.U) :
    p.1 ^ 2 * Work.Spaces.pzIter 2 V p.1 p.2
      = Work.Spaces.Dz (Work.Spaces.Dz V) p.1 p.2 - Work.Spaces.Dz V p.1 p.2 := by
  have h1 : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pz V)) Work.Spaces.U :=
    Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm
  have hd2 : DifferentiableAt ℝ (fun z' => deriv (fun z'' => V z'' p.2) z') p.1 := by
    have h := Work.Spaces.differentiableAt_curry_left
      ((h1.differentiableOn (n := ⊤) (by simp)).differentiableAt
        (Work.Spaces.isOpen_U.mem_nhds hp))
    simpa only [Work.Spaces.pz, Function.uncurry] using h
  have hprod : deriv (fun z' => z' * deriv (fun z'' => V z'' p.2) z') p.1
      = deriv (fun z'' => V z'' p.2) p.1
        + p.1 * deriv (fun z' => deriv (fun z'' => V z'' p.2) z') p.1 := by
    have h := deriv_mul (c := id) (d := fun z' => deriv (fun z'' => V z'' p.2) z')
      (x := p.1) differentiableAt_id hd2
    rw [show (id * fun z' => deriv (fun z'' => V z'' p.2) z')
        = (fun z' => z' * deriv (fun z'' => V z'' p.2) z') from rfl] at h
    simpa using h
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero]
  rw [hprod]
  ring

/-- **The Euler split for the `D_z`-iterates**, on the closed quadrant:
`D_z^r(D_z²V) = D_z^r(z²∂_z²V) + D_z^r(D_zV)`.  This is the `r`-fold `D_z`-iterate of the
identity `D_z²V = z²∂_z²V + D_zV` (valid on the open box `U`, which contains `Iz × Iθ`), pushed
through `D_z^r` by `EqOn`-congruence and additivity of the iterates on an open set. -/
theorem DzIter_split {V : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd V) (r : ℕ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ
      = Work.Spaces.DzIter r (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) z θ
        + Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ := by
  have hU : (z, θ) ∈ Work.Spaces.U := Work.Spaces.mem_U_of_dom hz hθ
  have hpz2 : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pzIter 2 V)) Work.Spaces.U := by
    have h1 := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U (G := V) hsm
    have h2 := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U (G := Work.Spaces.pz V) h1
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h2
  have hQU : ContDiffOn ℝ ⊤
      (Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)) Work.Spaces.U := by
    rw [show Function.uncurry (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
        = (fun p : ℝ × ℝ => p.1 ^ 2) * Function.uncurry (Work.Spaces.pzIter 2 V) from rfl]
    exact (contDiffOn_fst.pow 2).mul hpz2
  have hBU : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz V)) Work.Spaces.U := by
    rw [show Function.uncurry (Work.Spaces.Dz V)
        = (fun p : ℝ × ℝ => p.1) * Function.uncurry (Work.Spaces.pz V) from rfl]
    exact contDiffOn_fst.mul (Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U hsm)
  -- the `m = 0` step: `D_z²V = z²∂_z²V + D_zV` on `U`
  have hstep : Set.EqOn (Function.uncurry (Work.Spaces.DzIter 2 V))
      (Function.uncurry
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ + Work.Spaces.Dz V z θ))
      Work.Spaces.U := by
    rintro ⟨z', θ'⟩ hp
    have hid := zsq_pzIter_two_eq_U hsm hp
    simp only [Function.uncurry, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    linarith [hid]
  have hcongr := Work.Coercivity.E2Mixed.DzIter_congr_of_isOpen Work.Spaces.isOpen_U hstep r
  have hadd := Work.Coercivity.E2Mixed.DzIter_add_of_isOpen Work.Spaces.isOpen_U hQU hBU r
  have hfinal := (hcongr.trans hadd) hU
  simpa only [Function.uncurry, Pi.add_apply] using hfinal

/-! ## Helper: nonnegativity of the slice functionals -/

private theorem mul_sq_sliceInt_nonneg (wz : ℝ) (g : ℝ → ℝ) :
    0 ≤ wz ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (g θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
  mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _)
        (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ))))

/-! ## The main family bound -/

theorem I0FamilyBound (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.Spaces.SmoothNbhd V → Work.Spaces.VanishTheta V →
      Work.Spaces.HkMem α k V →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      Work.Spaces.HkMem α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      α ^ 2 * (∑ r ∈ Finset.range (k + 1),
          ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        ≤ C * (α ^ 4 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  obtain ⟨Cc, hCcpos, hstrip⟩ := Work.EllipticEst.Core.i0Aux.interpS_theta
  refine ⟨((k : ℝ) + 1) * 16 * Cc, by positivity, ?_⟩
  intro α V hα hα1 hsm hvan _hM hMd hMQ hM2
  -- `SmoothNbhd` implies the open-quadrant smoothness used by the slice identities
  have hso : Work.FTS.EllipticEst.SmoothOpen V := by
    have h' : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (Function.uncurry V)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hsm
    show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry V)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    refine (h'.of_le le_top).mono (Set.prod_mono ?_ ?_)
    · exact Set.Ioi_subset_Ioi (by norm_num)
    · exact Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos])
  -- smoothness of the `D_z`-iterates on the strip of the interpolation estimate
  have hstrip_smooth : ∀ r : ℕ, ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter r V))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    intro r n
    have hU : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter r V)) Work.Spaces.U := by
      induction r with
      | zero => show ContDiffOn ℝ ⊤ (Function.uncurry V) Work.Spaces.U; exact hsm
      | succ m ih =>
          have hpz := Work.Spaces.contDiffOn_uncurry_pz Work.Spaces.isOpen_U ih
          have hfun : Function.uncurry (Work.Spaces.DzIter (m + 1) V)
              = (fun p : ℝ × ℝ => p.1)
                * Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter m V)) := by
            funext p
            simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Function.uncurry, Pi.mul_apply]
          rw [hfun]
          exact contDiffOn_fst.mul hpz
    refine (hU.mono ?_).of_le le_top
    rintro ⟨z', θ'⟩ hp
    exact ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp.1]), hp.2⟩
  -- the per-`r` estimate
  have key : ∀ r ∈ Finset.range (k + 1),
      α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        ≤ 16 * Cc * (α ^ 4
              * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
    intro r hr
    have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    set A : ℝ := Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ) with hA
    set B : ℝ := Work.Spaces.HkSq α k (Work.Spaces.Dz V) with hB
    set B2 : ℝ := Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) with hB2
    have hA0 : 0 ≤ A := by rw [hA]; exact Work.Spaces.HkSq_nonneg _ _ _
    have hB0 : 0 ≤ B := by rw [hB]; exact Work.Spaces.HkSq_nonneg _ _ _
    have hB20 : 0 ≤ B2 := by rw [hB2]; exact Work.Spaces.HkSq_nonneg _ _ _
    set X : ℝ := ∫ z in Work.Spaces.Iz,
      Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z with hX
    set DD : ℝ := ∫ z in Work.Spaces.Iz,
      Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z with hDD'
    set TT : ℝ := ∫ z in Work.Spaces.Iz,
      Work.EllipticEst.Core.ttIntS (Work.Spaces.DzIter r V) z with hTT'
    set D : ℝ := ∫ z in Work.Spaces.Iz,
      Work.EllipticEst.Core.dIntS (Work.Spaces.DzIter r V) z with hD'
    -- nonnegativity of the four quantities
    have hX0 : 0 ≤ X := by
      rw [hX]
      refine integral_nonneg fun z => ?_
      exact mul_sq_sliceInt_nonneg _ _
    have hDD0 : 0 ≤ DD := by
      rw [hDD']
      refine integral_nonneg fun z => ?_
      exact mul_sq_sliceInt_nonneg _ _
    have hTT0 : 0 ≤ TT := by
      rw [hTT']
      refine integral_nonneg fun z => ?_
      exact mul_sq_sliceInt_nonneg _ _
    have hD0 : 0 ≤ D := by
      rw [hD']
      refine integral_nonneg fun z => ?_
      exact mul_sq_sliceInt_nonneg _ _
    -- the three slot bounds
    have hdd := Work.FTS.EllipticEst.RPFresh.DdIntSlotBound (k := k) (r := r) (α := α) (V := V)
      hsm (fun z hz θ hθ => DzIter_split hsm r hz hθ) hMQ hMd hrk
    have hDDle : DD ≤ 2 * A + 2 * B := by
      rw [hDD', hA, hB]
      exact hdd.2
    have hTTle : TT ≤ B2 := by
      rw [hTT', hB2]
      exact Work.EllipticEst.Core.i0Aux.ttIntS_integral_le_HkSq hso hM2 hrk
    have hDle : D ≤ B := by
      rw [hD', hB]
      exact Work.EllipticEst.Core.i0Aux.dIntS_integral_le_HkSq hMd hrk
    -- integrability of the three right-hand slots
    have hddI := hdd.1
    have httI := Work.EllipticEst.Core.i0Aux.ttIntS_integrableOn hso hM2 hrk
    have hdI := Work.EllipticEst.Core.i0Aux.dIntS_integrableOn hso hMd hrk
    have hv0 : ∀ z : ℝ, Work.Spaces.DzIter r V z 0 = 0 :=
      Work.EllipticEst.Core.i0Aux.DzIter_zero_theta hvan.1 r
    have hvpi : ∀ z : ℝ, Work.Spaces.DzIter r V z (Real.pi / 2) = 0 :=
      Work.EllipticEst.Core.i0Aux.DzIter_pi_theta hvan.2 r
    by_cases hmix : MeasureTheory.IntegrableOn
        (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        Work.Spaces.Iz
    · -- the honest case: apply the interpolation estimate at `α' = min α (1/4)`
      set α' : ℝ := min α (1 / 4) with hα'def
      have hα'pos : 0 < α' := by rw [hα'def]; exact lt_min hα (by norm_num)
      have hα'le4 : α' ≤ 1 / 4 := by rw [hα'def]; exact min_le_right _ _
      have hα'leα : α' ≤ α := by rw [hα'def]; exact min_le_left _ _
      have hres := hstrip α' (Work.Spaces.DzIter r V) hα'pos hα'le4
        (hstrip_smooth r) hv0 hvpi hmix hddI httI hdI
      -- arithmetic: transfer from `α'` to `α`
      have hsq2 : α ^ 2 * α' ^ 2 ≤ α ^ 4 := by
        have h : α' ^ 2 ≤ α ^ 2 := by nlinarith [hα'leα, hα'pos.le, hα.le]
        nlinarith [h, sq_nonneg α]
      have hratio : α ^ 2 / α' ^ 2 ≤ 16 := by
        have h4 : α ≤ 4 * α' := by
          by_cases h : α ≤ 1 / 4
          · rw [hα'def, min_eq_left h]; linarith
          · have h' : 1 / 4 < α := lt_of_not_ge h
            rw [hα'def, min_eq_right h'.le]; linarith
        have hdiv : α / α' ≤ 4 := by
          rw [div_le_iff₀ hα'pos]; linarith
        have h2 : (α / α') ^ 2 ≤ 16 := by
          nlinarith [hdiv, div_nonneg hα.le hα'pos.le]
        calc α ^ 2 / α' ^ 2 = (α / α') ^ 2 := (div_pow α α' 2).symm
          _ ≤ 16 := h2
      have hXle : X ≤ Cc * (α' ^ 4 * DD + TT + α' ^ 2 * D) / α' ^ 2 := by
        rw [le_div_iff₀ (show (0 : ℝ) < α' ^ 2 by positivity), mul_comm X (α' ^ 2)]
        exact hres
      have hmain : α ^ 2 * X ≤ Cc * (α ^ 4 * DD + 16 * TT + α ^ 2 * D) := by
        calc α ^ 2 * X
            ≤ α ^ 2 * (Cc * (α' ^ 4 * DD + TT + α' ^ 2 * D) / α' ^ 2) :=
              mul_le_mul_of_nonneg_left hXle (sq_nonneg α)
          _ = Cc * (α ^ 2 / α' ^ 2) * (α' ^ 4 * DD + TT + α' ^ 2 * D) := by ring
          _ = Cc * (α ^ 2 * α' ^ 2 * DD + (α ^ 2 / α' ^ 2) * TT + α ^ 2 * D) := by
              field_simp
          _ ≤ Cc * (α ^ 4 * DD + 16 * TT + α ^ 2 * D) := by
              refine mul_le_mul_of_nonneg_left ?_ hCcpos.le
              have h1 : α ^ 2 * α' ^ 2 * DD ≤ α ^ 4 * DD :=
                mul_le_mul_of_nonneg_right hsq2 hDD0
              have h2 : α ^ 2 / α' ^ 2 * TT ≤ 16 * TT :=
                mul_le_mul_of_nonneg_right hratio hTT0
              linarith
      have hfin : Cc * (α ^ 4 * DD + 16 * TT + α ^ 2 * D)
          ≤ 16 * Cc * (α ^ 4 * A + B2 + α ^ 2 * B) := by
        have hα4le : α ^ 4 ≤ α ^ 2 := by
          have h : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
          calc α ^ 4 = α ^ 2 * α ^ 2 := by ring
            _ ≤ α ^ 2 * 1 := mul_le_mul_of_nonneg_left h (sq_nonneg α)
            _ = α ^ 2 := by ring
        have h1 : α ^ 4 * DD ≤ 2 * (α ^ 4 * A) + 2 * (α ^ 2 * B) := by
          have h := mul_le_mul_of_nonneg_left hDDle (show (0 : ℝ) ≤ α ^ 4 by positivity)
          have h5 : α ^ 4 * B ≤ α ^ 2 * B :=
            mul_le_mul_of_nonneg_right hα4le hB0
          nlinarith [h, h5, hA0, hB0]
        have h2 : 16 * TT ≤ 16 * B2 := by linarith
        have h3 : α ^ 2 * D ≤ α ^ 2 * B := mul_le_mul_of_nonneg_left hDle (sq_nonneg α)
        have h4 : α ^ 4 * B ≤ α ^ 2 * B := mul_le_mul_of_nonneg_right hα4le hB0
        have hA' : 0 ≤ α ^ 4 * A := mul_nonneg (by positivity) hA0
        have hB' : 0 ≤ α ^ 2 * B := mul_nonneg (by positivity) hB0
        have hstep : α ^ 4 * DD + 16 * TT + α ^ 2 * D ≤ 16 * (α ^ 4 * A + B2 + α ^ 2 * B) := by
          nlinarith [h1, h2, h3, h4, hA', hB', hB20]
        calc Cc * (α ^ 4 * DD + 16 * TT + α ^ 2 * D)
            ≤ Cc * (16 * (α ^ 4 * A + B2 + α ^ 2 * B)) :=
              mul_le_mul_of_nonneg_left hstep hCcpos.le
          _ = 16 * Cc * (α ^ 4 * A + B2 + α ^ 2 * B) := by ring
      exact le_trans hmain hfin
    · -- the junk case: the integral is `0` by the junk-value convention
      rw [hX, MeasureTheory.integral_undef hmix, mul_zero]
      have h1 : 0 ≤ α ^ 4 * A := mul_nonneg (by positivity) hA0
      have h2 : 0 ≤ α ^ 2 * B := mul_nonneg (by positivity) hB0
      nlinarith [h1, h2, hB20, hCcpos.le]
  -- summation over `r ≤ k`
  have hsum : (∑ r ∈ Finset.range (k + 1),
        α ^ 2 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
      ≤ ((k : ℝ) + 1)
        * (16 * Cc * (α ^ 4
              * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))) := by
    calc (∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z))
        ≤ ∑ _r ∈ Finset.range (k + 1),
            16 * Cc * (α ^ 4
                * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
              + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
              + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := Finset.sum_le_sum key
      _ = ((k : ℝ) + 1)
          * (16 * Cc * (α ^ 4
                * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
              + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
              + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  calc α ^ 2 * (∑ r ∈ Finset.range (k + 1),
        ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      = ∑ r ∈ Finset.range (k + 1),
          α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z) := by
        rw [Finset.mul_sum]
    _ ≤ ((k : ℝ) + 1)
        * (16 * Cc * (α ^ 4
              * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V))) := hsum
    _ = ((k : ℝ) + 1) * 16 * Cc
        * (α ^ 4 * Work.Spaces.HkSq α k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 V z θ)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by ring

end Work.FTS.EllipticEst.RPFresh
