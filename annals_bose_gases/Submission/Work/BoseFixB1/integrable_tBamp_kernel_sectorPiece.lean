import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.perSectorBoundG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.integrable_tBamp_kernel_sectorPiece`

The `z`-kernel of the (FS-faithful, `boxQInd`) windowed amplitude of a count-sector piece is
`Integrable` on `ℝ³`:

    z ↦ χ_{B(u)}(z)·e^{−i⟪p,z⟫}·(Q_{B(u),i}Ψ)(x_{i←z}),

both for the sector pieces `Ψ = 1_{n_{B(u)}=k}·Φ` of a continuous state `Φ` and for `Φ` itself.

## The argument

`χ_{B(u)}` is continuous with compact support, contained in `B(u) = dlBox ℓ d u`; the phase is
unimodular; and the projection evaluated on the updated configuration collapses to the *explicit*
`A`-indicator form

    (Q_{A,i}Ψ)(x_{i←z}) = 1_A(z)·(Ψ(x_{i←z}) − (1/|A|)·∫_A Ψ(x_{i←w}) dw )

because updating slot `i` by `z` and then by `w` is updating by `w`.  Since `χ_{B(u)}` is
supported in `B(u)`, the factor `1_A(z)` is invisible and the whole kernel is
`χ·e^{−i⟪p,z⟫}·(Ψ(x_{i←z}) − c)`; it is dominated by `‖χ_{B(u)}‖·(‖Ψ(x_{i←·}) − c‖)`, which is
integrable as soon as `Ψ(x_{i←·}) − c` is bounded on the (compact) support of `χ_{B(u)}`.  That
bound is supplied in the two instantiations by continuity of `Φ` (compactness of the support) and
by `|1_{sector}·Φ| ≤ |Φ|`.

## Structure

* `boxQInd_update_eq` — the pointwise identity above (an algebraic unfolding of `boxQInd`).
* `integrable_chiB_exp_mul` — the abstract domination core (compact support + boundedness).
* the target — two instantiations, plus the two boundedness witnesses.
-/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseFixB1

/-! ## 1. The fibre map `z ↦ x_{i←z}` -/

/-- Updating one slot is continuous in the inserted value. -/
private theorem continuous_update_fixed {n : ℕ} (x : Submission.BoseGases.X n) (i : Fin n) :
    Continuous (fun z : E3 => Function.update x i z) := by
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · have hfun : (fun z : E3 => Function.update x i z j) = fun z : E3 => z := by
      funext z
      rw [Function.update_apply, if_pos hj]
    rw [hfun]
    fun_prop
  · have hfun : (fun z : E3 => Function.update x i z j) = fun _ : E3 => x j := by
      funext z
      rw [Function.update_apply, if_neg hj]
    rw [hfun]
    exact continuous_const

/-! ## 2. The box mean collapse of `boxQInd` on the updated configuration -/

/-- The box mean `(1/|A|)·∫_A Ψ(x_{i←w}) dw` of `Ψ` in slot `i` over the box `A`, at `x`. -/
private noncomputable def boxQMean {n : ℕ} (volA : ℝ) (A : Set E3) (i : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) : ℝ :=
  (1 / volA) * ∫ w in A, Ψ (Function.update x i w)

/-- **`boxQInd` on an updated configuration**: the `A`-indicator times the deviation of `Ψ` on the
fibre from its box mean.  Updating slot `i` by `z` and then by `w` is updating by `w`
(`Function.update_idem`), so the box mean is independent of `z` and the two indicators coincide. -/
private theorem boxQInd_update_eq {n : ℕ} (volA : ℝ) (A : Set E3) (i : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (z : E3) :
    Work.UBBInputs8.boxQInd volA A i Ψ (Function.update x i z)
      = A.indicator (fun _ => 1) z * (Ψ (Function.update x i z) - boxQMean volA A i Ψ x) := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  have h1 : (Function.update x i z) i = z := by
    rw [Function.update_apply, if_pos rfl]
  have h2 : ∀ w : E3, Ψ (Function.update (Function.update x i z) i w)
      = Ψ (Function.update x i w) := fun w => by rw [Function.update_idem]
  simp only [h1, h2, boxQMean]
  ring

/-! ## 3. The abstract domination core -/

/-- **The `z`-kernel `χ·e^{−i⟪p,z⟫}·(Ψ(x_{i←z}) − c)` is integrable.**  `χ = χ_{B(u)}` is
continuous with compact support, hence integrable (and its absolute value too), the phase has norm
one, and `Ψ(x_{i←·}) − c` is bounded on that compact support, so `‖χ‖·max C 0` dominates. -/
private theorem integrable_chiB_exp_mul {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (i : Fin n) (p : E3) (x : Submission.BoseGases.X n) (c : ℂ)
    {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨm : Measurable Ψ)
    (hbd : ∃ C : ℝ, ∀ z ∈ tsupport (Submission.BoseGases.chiB ℓ d u),
      ‖((Ψ (Function.update x i z) : ℂ) - c)‖ ≤ C) :
    Integrable (fun z : E3 =>
      (Submission.BoseGases.chiB ℓ d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((Ψ (Function.update x i z) : ℂ) - c)) := by
  obtain ⟨C, hC⟩ := hbd
  have hχc : Continuous (Submission.BoseGases.chiB ℓ d u) :=
    (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).continuous
  have hχint : Integrable (Submission.BoseGases.chiB ℓ d u) :=
    hχc.integrable_of_hasCompactSupport (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u)
  have hg : Integrable (fun z : E3 => ‖Submission.BoseGases.chiB ℓ d u z‖ * max C 0) :=
    hχint.norm.mul_const _
  refine hg.mono' ?_ ?_
  · -- measurability of the kernel
    have hχm : Measurable (Submission.BoseGases.chiB ℓ d u) := hχc.measurable
    have hexp : Measurable (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) := by
      refine Complex.continuous_exp.measurable.comp ?_
      refine Continuous.measurable ?_
      exact ((continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_const.prodMk continuous_id)))).neg)
    exact (((Complex.continuous_ofReal.measurable.comp hχm).mul hexp).mul
      ((Complex.continuous_ofReal.measurable.comp
        (hΨm.comp (continuous_update_fixed x i).measurable)).sub
          measurable_const)).aestronglyMeasurable
  · -- the pointwise domination
    refine Filter.Eventually.of_forall (fun z => ?_)
    by_cases hz : Submission.BoseGases.chiB ℓ d u z = 0
    · simp [hz]
    · have hzK : z ∈ tsupport (Submission.BoseGases.chiB ℓ d u) := subset_tsupport _ hz
      have h1 : ‖((Ψ (Function.update x i z) : ℂ) - c)‖ ≤ max C 0 :=
        le_trans (hC z hzK) (le_max_left _ _)
      have hexp1 : ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      calc ‖(Submission.BoseGases.chiB ℓ d u z : ℂ)
            * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
            * ((Ψ (Function.update x i z) : ℂ) - c)‖
          = ‖Submission.BoseGases.chiB ℓ d u z‖ * 1
              * ‖((Ψ (Function.update x i z) : ℂ) - c)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, hexp1]
        _ ≤ ‖Submission.BoseGases.chiB ℓ d u z‖ * max C 0 := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

/-! ## 4. The `boxQInd` kernel -/

/-- **The `z`-kernel of `Q_{A,i}Ψ` on the updated configuration is integrable**, `A = dlBox ℓ d u`
being the support of `χ_{B(u)}`: the collapse identity of §2 makes the kernel equal to
`χ·e^{−i⟪p,z⟫}·(Ψ(x_{i←z}) − c)` (the `A`-indicator is invisible under `χ_{B(u)}`'s support), and
§3 gives integrability from boundedness of `Ψ(x_{i←·}) − c` on `tsupport χ_{B(u)}`. -/
private theorem integrable_chiB_boxQInd {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (i : Fin n) (volA : ℝ) {Ψ : Submission.BoseGases.X n → ℝ} (hΨm : Measurable Ψ)
    (hbd : ∀ x : Submission.BoseGases.X n, ∃ C : ℝ,
      ∀ z ∈ tsupport (Submission.BoseGases.chiB ℓ d u),
        ‖((Ψ (Function.update x i z) : ℂ)
          - (boxQMean volA (Submission.BoseGases.dlBox ℓ d u) i Ψ x : ℂ))‖ ≤ C) :
    ∀ (p : E3) (x : Submission.BoseGases.X n),
      Integrable (fun z : E3 =>
        (Submission.BoseGases.chiB ℓ d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.UBBInputs8.boxQInd volA (Submission.BoseGases.dlBox ℓ d u) i Ψ)
              (Function.update x i z) : ℂ)) := by
  intro p x
  have hker : Integrable (fun z : E3 =>
      (Submission.BoseGases.chiB ℓ d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((Ψ (Function.update x i z) : ℂ)
            - (boxQMean volA (Submission.BoseGases.dlBox ℓ d u) i Ψ x : ℂ))) :=
    integrable_chiB_exp_mul hℓ hd u i p x
      (boxQMean volA (Submission.BoseGases.dlBox ℓ d u) i Ψ x : ℂ) hΨm (hbd x)
  refine hker.congr (Filter.Eventually.of_forall (fun z => ?_))
  show (Submission.BoseGases.chiB ℓ d u z : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((Ψ (Function.update x i z) : ℂ)
            - (boxQMean volA (Submission.BoseGases.dlBox ℓ d u) i Ψ x : ℂ))
      = (Submission.BoseGases.chiB ℓ d u z : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((Work.UBBInputs8.boxQInd volA (Submission.BoseGases.dlBox ℓ d u) i Ψ)
            (Function.update x i z) : ℂ)
  rw [boxQInd_update_eq volA (Submission.BoseGases.dlBox ℓ d u) i Ψ x z]
  by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem hz]
    push_cast
    ring
  · have h0 : Submission.BoseGases.chiB ℓ d u z = 0 := by
      by_contra hne
      exact hz (Submission.BoseGases.chiB_support_mem hℓ hd u z hne)
    simp [h0]

/-! ## 5. The target -/

theorem integrable_tBamp_kernel_sectorPiece {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (i : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∀ (k : ℕ) (p : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n),
      MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.chiB ℓ d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i
              (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)
              (Function.update x i z)) : ℂ)))
    ∧ (∀ (p : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X n),
      MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.chiB ℓ d u z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Φ) (Function.update x i z) : ℂ)))
    := by
  constructor
  · intro k p x
    refine integrable_chiB_boxQInd (ℓ := ℓ) (d := d) hℓ hd u i
      (Work.SmallBoxSliding.boxMass ℓ d u)
      (Ψ := Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) ?_ ?_ p x
    · exact hΦc.measurable.indicator
        (Work.FockBridge.sectorSet_measurable (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) k)
    · intro x'
      -- the sector piece is bounded by `Φ` on the (compact) support of the cutoff
      have hK : IsCompact (tsupport (Submission.BoseGases.chiB ℓ d u)) :=
        Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u
      obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn
          ((hΦc.comp (continuous_update_fixed x' i)).norm.continuousOn)
      refine ⟨C₀ + ‖(boxQMean (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i
        (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ) x' : ℂ)‖, ?_⟩
      intro z hz
      have hC₀' : ‖Φ (Function.update x' i z)‖ ≤ C₀ := by
        simpa using hC₀ z hz
      have h1 : ‖(Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ
            (Function.update x' i z) : ℝ)‖ ≤ ‖Φ (Function.update x' i z)‖ := by
        simpa only [Work.FockBridge.sectorPiece] using
          (norm_indicator_le_norm_self (s := Work.FockBridge.sectorSet
            (Submission.BoseGases.dlBox ℓ d u) k) (f := Φ) (a := Function.update x' i z))
      have h1c : ‖((Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ
            (Function.update x' i z) : ℝ) : ℂ)‖ ≤ ‖Φ (Function.update x' i z)‖ := by
        rw [Complex.norm_real]
        exact h1
      refine le_trans (norm_sub_le _ _) (by linarith)
  · intro p x
    refine integrable_chiB_boxQInd (ℓ := ℓ) (d := d) hℓ hd u i
      (Work.SmallBoxSliding.boxMass ℓ d u) (Ψ := Φ) hΦc.measurable ?_ p x
    intro x'
    -- `Φ(x_{i←·})` is continuous, hence bounded on the compact support of the cutoff
    have hK : IsCompact (tsupport (Submission.BoseGases.chiB ℓ d u)) :=
      Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
        (((Complex.continuous_ofReal.comp (hΦc.comp (continuous_update_fixed x' i))).sub
          continuous_const).continuousOn)
    exact ⟨C, hC⟩

end Work.BoseFixB1
