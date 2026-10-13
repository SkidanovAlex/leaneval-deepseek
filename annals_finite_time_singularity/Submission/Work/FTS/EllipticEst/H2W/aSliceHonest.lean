/-
Copyright: work module for the Elgindi finite-time singularity project.

# Honesty of the angular slice of `z² ∂_z²Ψ` at level `2` (weak hypothesis class)

The target `Work.FTS.EllipticEst.H2W.aSliceHonest` states that for every datum of the *weak*
hypothesis class `Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ` (`0 < α ≤ 1/4`) and every
`z ∈ Iz = [0,∞)`, the angular slice

  `θ ↦ (∂_θ² (z² ∂_z²Ψ z ·))(θ)² · sin(2θ)^{-η}`

is integrable on `Iθ = [0,π/2]` (`η = 99/100`).

## Where the content comes from

The class carries the honesty of `∂_θ²Ψ` at level `2`
(`Work.FTS.EllipticEst.TT.EllWeakPos.memB : HkMem α 2 (∂_θ²Ψ)`).  Writing `H = ∂_θ²Ψ`, the
first (`D_z`-)group of `HkIntegrand α 2 H` contains the two nonnegative summands

  `(D_z H · w/sin(2θ)^{η/2})²`  and  `(D_z² H · w/sin(2θ)^{η/2})²`,

which are therefore honest on every slice `z ∈ Iz` (`HkMem` is a sum of nonnegative squares:
`Work.FTS.EllipticEst.RPFresh.excess_zsummand_mem`); dividing by `w(z)² ≠ 0` (`z > 0`) turns
them into the η-weighted squares `(D_z^i H)² sin(2θ)^{-η}`.

The remaining step is the *pointwise identity* which relates these two quantities to the
slice of the target.  On the open quadrant, `z²∂_z² = D_z² - D_z`
(`Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz`), the plain `z`- and `θ`-derivatives commute
(Clairaut, proved here for the iterates as `pthIter_pzIter_comm_Q0`), and `z²` is a constant in
`θ`, so

  `∂_θ² (z² ∂_z²Ψ z ·)(θ) = z² ∂_z²(∂_θ²Ψ) z θ = D_z²H z θ - D_zH z θ`,

(`deriv_deriv_zsq_pzIter2_Qop`, `deriv_deriv_zsq_pzIter2_eq`).  This identifies the target
slice with a difference of the two honest summands above, so it is honest as well
(`HkMem_zero_of_majorant`).

The hypotheses `0 < α`, `α ≤ 1/4`, the equation, the Dirichlet data, the moment conditions and
the honesty of `F` and of `z²∂_z²Ψ` are not used: the statement is true in the class, and the
whole content is the `H = ∂_θ²Ψ` field together with the Clairaut identity.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.RPFresh.excess_finite
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## `∂_θ`-iterates of a function smooth on the open quadrant -/

/-- `∂_θ^i f` is again `C^∞` on the open quadrant when `f` is. -/
theorem smoothOpen_pthIter_H2W {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-! ## Clairaut at the level of the iterated plain derivatives -/

/-- On the open quadrant, `∂_θ^m` commutes with `∂_z`. -/
theorem pz_pthIter_comm_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g) (m : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter m g)))
      (Function.uncurry (Work.Spaces.pthIter m (Work.Spaces.pz g)))
        Work.FTS.EllipticEst.Q0 := by
  induction m with
  | zero => intro p hp; rfl
  | succ k ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter k g)) (z, θ) :=
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pthIter k g)).mp
          (smoothOpen_pthIter_H2W hg k) 2).contDiffAt
            (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hpt)
      have hstep : Work.Spaces.pz (Work.Spaces.pthIter (k + 1) g) z θ
          = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pthIter k g)) z θ := by
        rw [Work.Spaces.pthIter_succ]
        exact Work.Spaces.pz_pth_comm hcd
      have hstep2 : Work.Spaces.pthIter (k + 1) (Work.Spaces.pz g) z θ
          = Work.Spaces.pth (Work.Spaces.pthIter k (Work.Spaces.pz g)) z θ := by
        rw [Work.Spaces.pthIter_succ]
      change Work.Spaces.pz (Work.Spaces.pthIter (k + 1) g) z θ
        = Work.Spaces.pthIter (k + 1) (Work.Spaces.pz g) z θ
      rw [hstep, hstep2]
      exact Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hpt

/-- On the open quadrant, `∂_θ^m` commutes with `∂_z^j`. -/
theorem pthIter_pzIter_comm_Q0 {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (m j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter m (Work.Spaces.pzIter j g)))
      (Function.uncurry (Work.Spaces.pzIter j (Work.Spaces.pthIter m g)))
        Work.FTS.EllipticEst.Q0 := by
  induction j with
  | zero => intro p hp; rfl
  | succ k ih =>
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      have hpt : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hle : Work.Spaces.pthIter m (Work.Spaces.pz (Work.Spaces.pzIter k g)) z θ
          = Work.Spaces.pz (Work.Spaces.pthIter m (Work.Spaces.pzIter k g)) z θ :=
        (pz_pthIter_comm_Q0 (hg.pzIter k) m hpt).symm
      have hpz : Work.Spaces.pz (Work.Spaces.pthIter m (Work.Spaces.pzIter k g)) z θ
          = Work.Spaces.pz (Work.Spaces.pzIter k (Work.Spaces.pthIter m g)) z θ :=
        Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hpt
      change Work.Spaces.pthIter m (Work.Spaces.pzIter (k + 1) g) z θ
        = Work.Spaces.pzIter (k + 1) (Work.Spaces.pthIter m g) z θ
      rw [show Work.Spaces.pzIter (k + 1) g = Work.Spaces.pz (Work.Spaces.pzIter k g) from rfl,
        show Work.Spaces.pzIter (k + 1) (Work.Spaces.pthIter m g)
            = Work.Spaces.pz (Work.Spaces.pzIter k (Work.Spaces.pthIter m g)) from rfl,
        hle, hpz]

/-! ## The pointwise identity for the slice of `z²∂_z²Ψ` -/

/-- **The second angular derivative of the radial slice `z²∂_z²Ψ z ·`, in `Qop`-form.**
On the open quadrant it equals `z²∂_z²(∂_θ²Ψ)`: the factor `z²` is constant in `θ`, and the
plain `θ`- and `z`-derivatives commute (Clairaut). -/
theorem deriv_deriv_zsq_pzIter2_Qop {Ψ : ℝ → ℝ → ℝ} (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ
      = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hinner : ∀ t : ℝ,
      deriv (fun θ' : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t
        = z ^ 2 * deriv (fun θ' : ℝ => Work.Spaces.pzIter 2 Ψ z θ') t :=
    fun t => deriv_const_mul_field (z ^ 2)
  calc deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ
      = deriv (fun t => z ^ 2 * deriv (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') t) θ := by
        congr 1 with t; exact hinner t
    _ = z ^ 2 * deriv (fun t => deriv (fun θ' => Work.Spaces.pzIter 2 Ψ z θ') t) θ :=
        deriv_const_mul_field (z ^ 2)
    _ = z ^ 2 * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ := rfl
    _ = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
        rw [show Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ
            = Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
          from pthIter_pzIter_comm_Q0 hSΨ 2 2 hmem]

/-- **The second angular derivative of the radial slice `z²∂_z²Ψ z ·`, in `D_z`-form.**
`z²∂_z² = D_z² - D_z`, so the slice is the difference of the two radial summands of the
`ℋ²`-integrand of `∂_θ²Ψ`. -/
theorem deriv_deriv_zsq_pzIter2_eq {Ψ : ℝ → ℝ → ℝ} (hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ
      = Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ
        - Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ := by
  rw [deriv_deriv_zsq_pzIter2_Qop hSΨ hz hθ]
  exact Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz (smoothOpen_pthIter_H2W hSΨ 2) hz hθ

/-! ## Honesty of a slice from `ℋ⁰`-membership -/

/-- **An `ℋ⁰`-membership makes every angular slice η-weighted-square honest.**  If
`g ∈ ℋ⁰` then for every `z > 0` the slice `θ ↦ g z θ² sin(2θ)^{-η}` is integrable on `Iθ`:
the `ℋ⁰`-integrand is `(g z θ · w(z)/sin(2θ)^{η/2})²`, and for `z > 0` the factor `w(z)² ≠ 0`
can be divided out. -/
theorem integrable_slice_sq_sEta_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) (h : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.congr_fun (h.1 z hzI)
      (fun θ hθ => Work.FTS.EllipticEst.RPFresh.HkIntegrand_zero_eq α g z θ) hIθ
  have h2 := h1.const_mul ((Work.Spaces.w z) ^ 2)⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h2 (fun θ hθ => ?_) hIθ
  rw [Work.FTS.EllipticEst.sEta,
    Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z) hθ]
  field_simp

/-! ## The target -/

theorem aSliceHonest : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      ∀ z ∈ Work.Spaces.Iz,
        MeasureTheory.IntegrableOn (fun θ =>
            (deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the slice is identically zero
    subst hz0
    have hzero : (fun θ : ℝ =>
        (deriv (fun t => deriv (fun θ' => (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) = fun _ => (0 : ℝ) := by
      have hfun : (fun θ' : ℝ => (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ')
          = fun _ => (0 : ℝ) := by
        funext t; ring
      funext θ
      rw [hfun]
      simp
    rw [hzero]
    exact integrableOn_zero
  · -- the `ℋ²`-membership of `∂_θ²Ψ` and its two radial summands
    have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mpr h.smooth
    have hSH : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
      smoothOpen_pthIter_H2W hSΨ 2
    have hb1 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.RPFresh.excess_zsummand_mem α 2 1 (Work.Spaces.pthIter 2 Ψ)
        ((hSH.DzIter 1).continuousOn) h.memB (by norm_num)
    have hb2 : Work.Spaces.HkMem α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) :=
      Work.FTS.EllipticEst.RPFresh.excess_zsummand_mem α 2 2 (Work.Spaces.pthIter 2 Ψ)
        ((hSH.DzIter 2).continuousOn) h.memB (by norm_num)
    -- the two-variable slice function is continuous on the open quadrant
    have hcontG : ContinuousOn
        (Function.uncurry (fun z θ =>
          deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hbase : ContinuousOn
          (fun p : ℝ × ℝ =>
            p.1 ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter 2 Ψ) p.1 p.2)
          Work.FTS.EllipticEst.Q0 :=
        (continuousOn_fst.pow 2).mul ((hSH.pzIter 2).continuousOn)
      refine hbase.congr ?_
      rintro ⟨z, θ⟩ hp
      obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact deriv_deriv_zsq_pzIter2_Qop hSΨ hz ⟨hθ0, hθ1⟩
    -- honesty of the slice function, by domination with the two radial summands
    have hGfun : Work.Spaces.HkMem α 0
        (fun z θ => deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ) := by
      refine Work.FTS.EllipticEst.RPFresh.HkMem_zero_of_majorant (α := α)
        (f := fun z θ =>
          deriv (fun t => deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') t) θ)
        (M := fun z θ =>
          2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
            + 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ)
        hcontG ?_ ?_ ?_
      · intro z hz
        exact ((hb2.1 z hz).const_mul 2).add ((hb1.1 z hz).const_mul 2)
      · have h' := (hb2.2.const_mul 2).add (hb1.2.const_mul 2)
        refine h'.congr ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        rw [Pi.add_apply, MeasureTheory.integral_add ((hb2.1 z hz).const_mul 2)
          ((hb1.1 z hz).const_mul 2), MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
      · intro z hz θ hθ
        have hMnn : 0 ≤ 2 * Work.Spaces.HkIntegrand α 0
              (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
              (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ := by
          have h₁ := Work.Spaces.HkIntegrand_nonneg α 0
            (Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ)) z θ
          have h₂ := Work.Spaces.HkIntegrand_nonneg α 0
            (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ
          linarith
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz_eq | hz_pos
        · -- `z = 0`
          subst hz_eq
          rw [Work.FTS.EllipticEst.RPFresh.HkIntegrand_zero_zero]
          exact hMnn
        · rcases eq_or_lt_of_le hθ.1 with hθ_eq | hθ_pos
          · -- `θ = 0`
            subst hθ_eq
            rw [Work.FTS.EllipticEst.RPFresh.HkIntegrand_zero_theta_zero]
            exact hMnn
          · rcases eq_or_lt_of_le hθ.2 with hθ_eq | hθ_lt
            · -- `θ = π/2`
              subst hθ_eq
              rw [Work.FTS.EllipticEst.RPFresh.HkIntegrand_zero_theta_pi]
              exact hMnn
            · -- interior: use the pointwise identity and AM–GM
              rw [Work.FTS.EllipticEst.RPFresh.HkIntegrand_zero_eq,
                deriv_deriv_zsq_pzIter2_eq hSΨ hz_pos ⟨hθ_pos, hθ_lt⟩,
                Work.FTS.EllipticEst.RPFresh.HkIntegrand_zero_eq,
                Work.FTS.EllipticEst.RPFresh.HkIntegrand_zero_eq]
              set A := Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ with hA
              set B := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ with hB
              set c := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hc
              nlinarith [sq_nonneg (A * c + B * c), sq_nonneg (A * c), sq_nonneg (B * c)]
    exact integrable_slice_sq_sEta_of_HkMem hzpos hGfun

end Work.FTS.EllipticEst.H2W
