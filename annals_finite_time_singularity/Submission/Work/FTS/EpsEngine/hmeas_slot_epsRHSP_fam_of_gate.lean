/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/hmeas_slot_epsRHSP_fam_of_gate.lean`

**The jet-measurability gate of the projected `ε`-scheme**: along a family `g` whose slices lie in
the `X`-ball `XBall α ρ ε R C₀` and are `EpsSq`-Lipschitz in the fake time, *every* mixed jet
`(D_z^j D_θ^i (epsRHSP α ρ ε Φs E g s)) z θ` is a.e. strongly measurable in `s` on the horizon
`Icc 0 δ`, for every point `(z,θ)` of the **open** quadrant.

The parent `Work.FTS.EpsEngine.aesm_epsRHSP_fam_of_gate` proves only the *joint* measurability of
`(s,z,θ) ↦ epsRHSP … g s z θ`; the slot statement cannot be read off it, because a fixed section of
an a.e. strongly measurable function need not be a.e. strongly measurable.  The route used here is
the one designed in the audit of the statement: the *slicewise* conclusion of the parent's gate
(`MeasAlt.aesm_slice_of_lipschitz_gate`, applied to `Feps` and the `X`-ball) is combined with the
`C^∞`-regularity of each slice on the open quadrant and the fact that a partial derivative at an
interior point is the limit of difference quotients at *nearby interior points* — those are again
evaluations of the a.e. strongly measurable family, and `AEStronglyMeasurable` is closed under
pointwise limits.  For fixed `(z,θ)` in the open quadrant no uniform slot bound whatever is needed.

Everything here is `sorry`-free.

The file records the small general engine that the argument needs:

* `aesm_deriv_of_increments` — the difference-quotient limit step;
* `aesm_deriv_z_slot_of_pointwise` / `aesm_deriv_theta_slot_of_pointwise` — its two specialisations
  along the `z`- and the `θ`-direction, the approximating points staying in the open quadrant;
* `aesm_mixed_of_slicewise` — the induction on `D_z^j D_θ^i` producing the measurability of every
  jet from the measurability of the zeroth order slots.

(`open scoped Real` is needed for the statement's `π / 2` to be `Real.pi / 2`: the file has
`autoImplicit` set to `false` through its imports, so a bare `π` is an error rather than a free
variable.)
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.aesm_epsRHSP_fam_of_gate
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.SmoothOpenFeps

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The difference-quotient limit step -/

/-- `((n : ℝ) + 1)⁻¹ → 0`, avoiding `0`. -/
lemma tendsto_inv_succ_nhdsNE_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
  · simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · show ((n : ℝ) + 1)⁻¹ ≠ 0
    positivity

/-- **A derivative slot is a.e. strongly measurable as soon as it is so at the limit point and at
all points of an approximating sequence, and the function is a.e. differentiable at the limit
point.**

The derivative `deriv (fun u => A s u) c` is the limit of the difference quotients
`(A s (c + d n) − A s c) / d n`, which are a.e. strongly measurable by hypothesis; the conclusion
follows from `aestronglyMeasurable_of_tendsto_ae` (`d n → 0` avoiding `0` by `hd`). -/
lemma aesm_deriv_of_increments {μ : Measure ℝ} {A : ℝ → ℝ → ℝ} {c : ℝ} {d : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝[≠] (0 : ℝ)))
    (hAn : ∀ n, AEStronglyMeasurable (fun s => A s (c + d n)) μ)
    (hAc : AEStronglyMeasurable (fun s => A s c) μ)
    (hdiff : ∀ᵐ s ∂μ, DifferentiableAt ℝ (fun u => A s u) c) :
    AEStronglyMeasurable (fun s => deriv (fun u => A s u) c) μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n s => (A s (c + d n) - A s c) * (d n)⁻¹) (fun n => ?_) ?_
  · exact ((hAn n).sub hAc).mul_const _
  · filter_upwards [hdiff] with s hs
    have hlim := (hs.hasDerivAt).tendsto_slope_zero.comp hd
    refine Tendsto.congr' (Filter.Eventually.of_forall (fun n => ?_)) hlim
    simp only [Function.comp_apply, smul_eq_mul]
    ring

/-! ## The two one-dimensional specialisations -/

/-- **The `z`-derivative slot**: if `s ↦ B s z' θ` is a.e. strongly measurable at every `z' > 0`,
and `z' ↦ B s z' θ` is a.e. differentiable at `z > 0`, then so is the derivative slot. -/
lemma aesm_deriv_z_slot_of_pointwise {μ : Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z)
    (hB : ∀ z' : ℝ, 0 < z' → AEStronglyMeasurable (fun s => B s z' θ) μ)
    (hdiff : ∀ᵐ s ∂μ, DifferentiableAt ℝ (fun z' => B s z' θ) z) :
    AEStronglyMeasurable (fun s => deriv (fun z' => B s z' θ) z) μ :=
  aesm_deriv_of_increments (A := fun s u => B s u θ) (c := z)
    (d := fun n : ℕ => ((n : ℝ) + 1)⁻¹) tendsto_inv_succ_nhdsNE_zero
    (fun n => hB _ (by positivity)) (hB z hz) hdiff

/-- **The `θ`-derivative slot**: if `s ↦ B s z θ'` is a.e. strongly measurable at every interior
angle `θ'`, and `θ' ↦ B s z θ'` is a.e. differentiable at `θ ∈ (0,π/2)`, then so is the derivative
slot.  The approximating angles are `θ − (θ/2) / (n+1)`, which lie in the open quadrant. -/
lemma aesm_deriv_theta_slot_of_pointwise {μ : Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hB : ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (π / 2) →
      AEStronglyMeasurable (fun s => B s z θ') μ)
    (hdiff : ∀ᵐ s ∂μ, DifferentiableAt ℝ (fun θ' => B s z θ') θ) :
    AEStronglyMeasurable (fun s => deriv (fun θ' => B s z θ') θ) μ := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  refine aesm_deriv_of_increments (A := fun s u => B s z u) (c := θ)
    (d := fun n : ℕ => -((θ / 2) * ((n : ℝ) + 1)⁻¹)) ?_ ?_ (hB θ hθ) hdiff
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · have h := (tendsto_inv_succ_nhdsNE_zero.mono_right nhdsWithin_le_nhds).const_mul (-(θ / 2))
      simpa using h
    · show -((θ / 2) * ((n : ℝ) + 1)⁻¹) ≠ 0
      have hn : ((n : ℝ) + 1)⁻¹ ≠ 0 := by positivity
      exact neg_ne_zero.mpr (mul_ne_zero (by linarith) hn)
  · intro n
    have hnle : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr (by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
    have hnn : 0 ≤ (θ / 2) * ((n : ℝ) + 1)⁻¹ := by positivity
    have hmem : θ + -((θ / 2) * ((n : ℝ) + 1)⁻¹) ∈ Set.Ioo 0 (π / 2) := by
      have hb : (θ / 2) * ((n : ℝ) + 1)⁻¹ ≤ θ / 2 :=
        mul_le_of_le_one_right (by linarith) hnle
      constructor <;> linarith
    exact hB _ hmem

/-! ## Assembly: measurability of every jet from the zeroth order slots -/

/-- **Every jet is a.e. strongly measurable** as soon as each slice is `C^∞` on the open quadrant
(for `s` in the horizon) and the zeroth order slots are a.e. strongly measurable there.

The proof is the double induction on `mixed j i = D_z^j D_θ^i`: the `i`-induction uses
`aesm_deriv_theta_slot_of_pointwise` (via `D_θ = sin 2θ · ∂_θ`), the `j`-induction its
`z`-counterpart (via `D_z = z · ∂_z`), and at each step the differentiability of the intermediate
slot is `SmoothOpen` of that slot at the interior point. -/
lemma aesm_mixed_of_slicewise {B : ℝ → ℝ → ℝ → ℝ} {δ : ℝ}
    (hsm : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (B s))
    (hB : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      AEStronglyMeasurable (fun s => B s z θ) (volume.restrict (Set.Icc 0 δ)))
    (j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    AEStronglyMeasurable (fun s => Work.Spaces.mixed j i (B s) z θ)
      (volume.restrict (Set.Icc 0 δ)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 δ)
  have hae : ∀ᵐ s ∂μ, s ∈ Set.Icc 0 δ := ae_restrict_mem measurableSet_Icc
  have main : ∀ j : ℕ, ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      AEStronglyMeasurable (fun s => Work.Spaces.mixed j i (B s) z θ) μ := by
    intro j
    induction j with
    | zero =>
      have inner : ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
          AEStronglyMeasurable (fun s => Work.Spaces.DthIter i (B s) z θ) μ := by
        intro i
        induction i with
        | zero => intro z θ hz hθ; simpa using hB z θ hz hθ
        | succ i ih =>
          intro z θ hz hθ
          have h1 : AEStronglyMeasurable
              (fun s => deriv (fun θ' => Work.Spaces.DthIter i (B s) z θ') θ) μ :=
            aesm_deriv_theta_slot_of_pointwise hθ (fun θ' hθ' => ih z θ' hz hθ')
              (by
                filter_upwards [hae] with s hs
                exact (((hsm s hs).DthIter i).curry_θ hz).differentiableOn
                  Work.FTS.LocData.smoothOrder_ne_zero |>.differentiableAt
                    (isOpen_Ioo.mem_nhds hθ))
          have h2 := h1.const_mul (Real.sin (2 * θ))
          simpa only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth] using h2
      intro i z θ hz hθ
      simpa only [Work.Spaces.mixed_zero_left] using inner i z θ hz hθ
    | succ j ih =>
      intro i z θ hz hθ
      have h1 : AEStronglyMeasurable
          (fun s => deriv (fun z' => Work.Spaces.mixed j i (B s) z' θ) z) μ :=
        aesm_deriv_z_slot_of_pointwise hz (fun z' hz' => ih i z' θ hz' hθ)
          (by
            filter_upwards [hae] with s hs
            exact (((hsm s hs).mixed j i).hasDerivAt_slice hθ hz).differentiableAt)
      have h2 := h1.const_mul z
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz,
        Work.Spaces.pz] using h2
  exact main j i z θ hz hθ

/-! ## The target -/

theorem hmeas_slot_epsRHSP_fam_of_gate {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {ε : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsSq α (fun z θ =>
      Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ) ≤ Lw * (s - t) ^ 2)
    (j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
  -- each slice is `C^∞` on the open quadrant
  have hBsm : ∀ s ∈ Set.Icc 0 δ,
      Work.FTS.EllipticEst.SmoothOpen (Feps α ρ ε Φs E (slice g s)) := fun s hs =>
    smoothOpen_Feps_of_classC (α := α) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (u := slice g s) hα hρ hε hEll hstar (hP s hs).classC
  -- the order-zero slots are a.e. strongly measurable (the slicewise half of the parent's gate)
  have hBAe : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Feps α ρ ε Φs E (slice g s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro z θ hz hθ
    by_cases hδ : 0 ≤ δ
    · obtain ⟨C, hCpos, hpt⟩ :=
        pt_of_XBall (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs) (ρ := ρ)
          (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hR
      have hcont : ∀ w : Fn, XBall α ρ ε R C₀ w →
          ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E w q.1 q.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun w hw =>
        (continuousOn_Feps_of_XBall (α := α) (Ce := Ce) (Cs := Cs) (R := R) (C₀ := C₀)
          (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := w) hα hρ hε hEll hstar hw).1
      have hzero : ∀ (w : Fn) (q : ℝ × ℝ),
          q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E w q.1 q.2 = 0 :=
        fun w q hq => Feps_eq_zero_off_Q0 α ρ ε Φs E w q hq
      exact MeasAlt.aesm_slice_of_lipschitz_gate (F := fun u : Fn => Feps α ρ ε Φs E u)
        (V := fun s : ℝ => slice g s) (P := fun u : Fn => XBall α ρ ε R C₀ u)
        (α := α) (δ := δ) (Cpt := C) (Lb := Lw) hδ hLw hCpos.le hP hcont hzero hpt
        (fun s t hs ht => hEq s hs t ht) z θ
    · -- `δ < 0`: the horizon is empty, hence the restricted measure vanishes
      have hIcc : Set.Icc (0 : ℝ) δ = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hδ)
      rw [hIcc, Measure.restrict_empty]
      exact aestronglyMeasurable_zero_measure _
  have hmain := aesm_mixed_of_slicewise (B := fun s => Feps α ρ ε Φs E (slice g s))
    hBsm hBAe j i hz hθ
  refine hmain.congr (Filter.Eventually.of_forall (fun s => ?_))
  exact congrArg (fun f : Fn => Work.Spaces.mixed j i f z θ)
    (epsRHSP_eq_Feps_slice α ρ ε Φs E g s).symm

end Work.FTS.EpsEngine
