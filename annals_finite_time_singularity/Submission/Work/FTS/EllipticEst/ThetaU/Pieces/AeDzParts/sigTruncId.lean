import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngAWeak.aeTruncIdent

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Helper lemmas for `sigTruncId`

`sigTruncId` is the `sEta`-weighted truncated energy identity of the almost-everywhere class:
the slice-wise `z`-integration by parts `AngAWeak.sliceIBP` of
`Submission/Work/FTS/EllipticEst/AngAWeak/aeTruncIdent.lean`, integrated in `θ` against the
weight `sEta θ = sin(2θ)^{-η}`, with the joint (product-measure) integrability hypotheses
`hI1`–`hI5` supplying both the Fubini swaps and the a.e.-in-`θ` honesty of the `Lzero`-slice
pairing.

The generic ingredients are separated out below:

* `fubiniWeight` — the weighted Fubini identity in both directions
  `∫_z f z (∫_θ g θ h z θ) = ∫_θ g θ (∫_z f z h z θ)`;
* `Lzero1_slice` — the `θ`-slice of `Lzero1` is `Work.Elliptic.Lzero`;
* `sEta_ne_zero_of_mem_Ioo`, `ae_mem_Ioo_of_mem_Icc` — the structural facts about the
  weight `sEta θ = sin(2θ)^{-η}` used to remove it from the a.e. integrability hypothesis. -/

/-- Weighted Fubini: if `(z,θ) ↦ f z * (g θ * h z θ)` is jointly integrable then
`∫_z f z * (∫_θ g θ * h z θ) = ∫_θ g θ * (∫_z f z * h z θ)`. -/
theorem fubiniWeight {μ ν : MeasureTheory.Measure ℝ} [MeasureTheory.SFinite μ]
    [MeasureTheory.SFinite ν] {f g : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.Integrable
      (Function.uncurry fun z θ => f z * (g θ * h z θ)) (μ.prod ν)) :
    (∫ z, f z * (∫ θ, g θ * h z θ ∂ν) ∂μ)
      = ∫ θ, g θ * (∫ z, f z * h z θ ∂μ) ∂ν := by
  rw [show (fun z => f z * (∫ θ, g θ * h z θ ∂ν))
      = fun z => ∫ θ, f z * (g θ * h z θ) ∂ν from by
    funext z; rw [MeasureTheory.integral_const_mul]]
  rw [MeasureTheory.integral_integral_swap hint]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show (∫ x, f x * (g θ * h x θ) ∂μ) = g θ * ∫ z, f z * h z θ ∂μ
  rw [show (fun x => f x * (g θ * h x θ)) = fun x => g θ * (f x * h x θ) from by
    funext x; ring]
  rw [MeasureTheory.integral_const_mul]

/-- The `θ`-slice of `Work.FTS.EllipticEst.Lzero1` is `Work.Elliptic.Lzero`. -/
theorem Lzero1_slice (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ = Work.Elliptic.Lzero u z θ := by
  simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero, Work.Spaces.pthIter_succ,
    Work.Spaces.pthIter_zero, Work.Spaces.pth]

/-- `sEta θ = sin(2θ)^{-η}` does not vanish for `θ ∈ (0,π/2)`. -/
theorem sEta_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.sEta θ ≠ 0 := by
  rw [Work.FTS.EllipticEst.sEta]
  exact ne_of_gt (Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])) _)

/-- `sEta` vanishes at the two endpoints of `Iθ`. -/
theorem sEta_zero : Work.FTS.EllipticEst.sEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show (2:ℝ) * 0 = 0 from by ring, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-- `sEta` vanishes at the two endpoints of `Iθ`. -/
theorem sEta_pi_div_two : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.sEta,
    show (2:ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-- Almost every point of `Iθ = [0,π/2]` lies in the open interval `(0,π/2)`. -/
theorem ae_mem_Ioo_of_mem_Icc : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    θ ∈ Set.Icc (0:ℝ) (Real.pi/2) → θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) := by
  have hsub : {θ : ℝ | ¬ (θ ∈ Set.Icc 0 (Real.pi/2) → θ ∈ Set.Ioo 0 (Real.pi/2))}
      ⊆ ({0, Real.pi/2} : Set ℝ) := by
    intro θ hθ
    simp only [Set.mem_ofPred_eq] at hθ
    push Not at hθ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases eq_or_lt_of_le hθ.1.1 with h | h
    · exact Or.inl h.symm
    · rcases eq_or_lt_of_le hθ.1.2 with h' | h'
      · exact Or.inr h'
      · exact absurd ⟨h, h'⟩ hθ.2
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure ℝ) ({0, Real.pi/2} : Set ℝ) = 0 := by
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} from rfl,
      MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)]
    exact MeasureTheory.measure_singleton _
  rw [MeasureTheory.ae_iff]
  exact measure_mono_null hsub hnull

theorem sigTruncId (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W)
    (δ R : ℝ) (hδ0 : 0 < δ) (hδR : δ ≤ R)
    (hδW : ∀ z, z ≤ δ → W z = 0) (hRW : ∀ z, R ≤ z → W z = 0)
    (hI1 : MeasureTheory.Integrable (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.sEta p.2
        * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hI2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2
        * Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.pz u p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hI3 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) p.1
        * Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hI4 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) p.1
        * Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hI5 : MeasureTheory.Integrable (fun p : ℝ × ℝ => W p.1 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.sEta p.2
        * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u p.1 θ') p.2 * u p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
      = α ^ 2 * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
                * (Work.Spaces.pz u z θ) ^ 2))
        + (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
                * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ)))
        - (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
              * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
              * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
  -- the four `θ`-slice integrals
  set A : ℝ → ℝ := fun θ => ∫ z in Work.Spaces.Iz,
      W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 with hAdef
  set B : ℝ → ℝ := fun θ => ∫ z in Work.Spaces.Iz,
      W z * (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ) with hBdef
  set C : ℝ → ℝ := fun θ => ∫ z in Work.Spaces.Iz,
      deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z * (u z θ) ^ 2 with hCdef
  set D : ℝ → ℝ := fun θ => ∫ z in Work.Spaces.Iz,
      deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2 with hDdef
  -- ## joint integrability of the five product integrands, in `Fubini` normal form
  have exp1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (W p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Work.FTS.EllipticEst.sEta p.2
            * (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hI1.congr (Filter.Eventually.of_forall fun p => by ring)
  have exp2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (W p.1 * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2)
        * (Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.pz u p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hI2.congr (Filter.Eventually.of_forall fun p => by ring)
  have exp3 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) p.1
        * (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hI3.congr (Filter.Eventually.of_forall fun p => by ring)
  have exp4 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) p.1
        * (Work.FTS.EllipticEst.sEta p.2 * (u p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hI4.congr (Filter.Eventually.of_forall fun p => by ring)
  have exp5 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (W p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Work.FTS.EllipticEst.sEta p.2
            * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u p.1 θ') p.2 * u p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hI5.congr (Filter.Eventually.of_forall fun p => by ring)
  -- ## structural facts about `sEta`
  have haeIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ae_mem_Ioo_of_mem_Icc
  -- ## a.e. honesty of the `Lzero`-slice pairing (from `hI5` by dividing by `sEta θ`)
  have hIntL_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.Lzero u z θ * u z θ)) Work.Spaces.Iz := by
    filter_upwards [exp5.prod_left_ae, haeIoo] with θ hθint hθ
    have hs : Work.FTS.EllipticEst.sEta θ ≠ 0 := sEta_ne_zero_of_mem_Ioo hθ
    have h1 : MeasureTheory.Integrable (fun z => (Work.FTS.EllipticEst.sEta θ)⁻¹
        * ((W z * (Work.Spaces.w z) ^ 2)
            * (Work.FTS.EllipticEst.sEta θ
                * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ))))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hθint.const_mul _
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only []
    rw [← Lzero1_slice u z θ]
    field_simp
  -- ## the slice-wise identity, a.e. in `θ`
  have hper : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.EllipticEst.sEta θ * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (Work.Elliptic.bslOp α u z θ * u z θ))
        = Work.FTS.EllipticEst.sEta θ
            * (α ^ 2 * A θ + B θ - (α ^ 2 / 2) * C θ + (α * (5 + α) / 2) * D θ) := by
    filter_upwards [hIntL_ae, haeIoo] with θ hIntL hθ
    have hslice := Work.FTS.EllipticEst.AngAWeak.sliceIBP α u W hW2 hδ0 hδR hθ hδW hRW
      (Work.FTS.EllipticEst.AngAWeak.contDiffOn_slice_z h.smooth hθ 2) hIntL
    have hBθ : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (Work.Elliptic.Lzero u z θ * u z θ)) = B θ := by
      simp only [hBdef]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
      rw [← Lzero1_slice u z θ]
    rw [hslice, hBθ]
  -- ## the four `θ`-slice integrals are honest
  have intA : MeasureTheory.Integrable (fun θ => Work.FTS.EllipticEst.sEta θ * A θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (exp2.integral_prod_right).congr (Filter.Eventually.of_forall fun θ => ?_)
    show (∫ z, (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
        * (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz u z θ) ^ 2)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = Work.FTS.EllipticEst.sEta θ * A θ
    rw [show (fun z => (W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz u z θ) ^ 2))
        = fun z => Work.FTS.EllipticEst.sEta θ
            * (W z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (Work.Spaces.pz u z θ) ^ 2) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  have intB : MeasureTheory.Integrable (fun θ => Work.FTS.EllipticEst.sEta θ * B θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (exp5.integral_prod_right).congr (Filter.Eventually.of_forall fun θ => ?_)
    show (∫ z, (W z * (Work.Spaces.w z) ^ 2)
        * (Work.FTS.EllipticEst.sEta θ
            * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ))
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = Work.FTS.EllipticEst.sEta θ * B θ
    rw [show (fun z => (W z * (Work.Spaces.w z) ^ 2)
          * (Work.FTS.EllipticEst.sEta θ
              * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ)))
        = fun z => Work.FTS.EllipticEst.sEta θ
            * (W z * (Work.Spaces.w z) ^ 2
                * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ)) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  have intC : MeasureTheory.Integrable (fun θ => Work.FTS.EllipticEst.sEta θ * C θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (exp3.integral_prod_right).congr (Filter.Eventually.of_forall fun θ => ?_)
    show (∫ z, deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
        * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = Work.FTS.EllipticEst.sEta θ * C θ
    rw [show (fun z => deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
          * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        = fun z => Work.FTS.EllipticEst.sEta θ
            * (deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
                * (u z θ) ^ 2) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  have intD : MeasureTheory.Integrable (fun θ => Work.FTS.EllipticEst.sEta θ * D θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine (exp4.integral_prod_right).congr (Filter.Eventually.of_forall fun θ => ?_)
    show (∫ z, deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
        * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      = Work.FTS.EllipticEst.sEta θ * D θ
    rw [show (fun z => deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
          * (Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        = fun z => Work.FTS.EllipticEst.sEta θ
            * (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z * (u z θ) ^ 2) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
  -- ## weighted Fubini on the left-hand side
  have hfub1 : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
            * (Work.Elliptic.bslOp α u z θ * u z θ)))
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
          * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
              * (Work.Elliptic.bslOp α u z θ * u z θ)) :=
    fubiniWeight (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z => W z * (Work.Spaces.w z) ^ 2)
      (g := Work.FTS.EllipticEst.sEta)
      (h := fun z θ => Work.Elliptic.bslOp α u z θ * u z θ) exp1
  have hcomb : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
        * (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
            * (Work.Elliptic.bslOp α u z θ * u z θ)))
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
          * (α ^ 2 * A θ + B θ - (α ^ 2 / 2) * C θ + (α * (5 + α) / 2) * D θ) :=
    MeasureTheory.integral_congr_ae hper
  -- ## linearity in `θ`
  have hA' : MeasureTheory.Integrable
      (fun θ => α ^ 2 * (Work.FTS.EllipticEst.sEta θ * A θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := intA.const_mul _
  have hAB : MeasureTheory.Integrable
      (fun θ => α ^ 2 * (Work.FTS.EllipticEst.sEta θ * A θ)
        + Work.FTS.EllipticEst.sEta θ * B θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hA'.add intB
  have hC' : MeasureTheory.Integrable
      (fun θ => (α ^ 2 / 2) * (Work.FTS.EllipticEst.sEta θ * C θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := intC.const_mul _
  have hABC : MeasureTheory.Integrable
      (fun θ => (α ^ 2 * (Work.FTS.EllipticEst.sEta θ * A θ)
        + Work.FTS.EllipticEst.sEta θ * B θ)
        - (α ^ 2 / 2) * (Work.FTS.EllipticEst.sEta θ * C θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hAB.sub hC'
  have hD' : MeasureTheory.Integrable
      (fun θ => (α * (5 + α) / 2) * (Work.FTS.EllipticEst.sEta θ * D θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := intD.const_mul _
  have hlin : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
        * (α ^ 2 * A θ + B θ - (α ^ 2 / 2) * C θ + (α * (5 + α) / 2) * D θ))
      = α ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * A θ)
        + (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * B θ)
        - (α ^ 2 / 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * C θ)
        + (α * (5 + α) / 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * D θ) := by
    rw [show (fun θ => Work.FTS.EllipticEst.sEta θ
          * (α ^ 2 * A θ + B θ - (α ^ 2 / 2) * C θ + (α * (5 + α) / 2) * D θ))
        = fun θ => α ^ 2 * (Work.FTS.EllipticEst.sEta θ * A θ)
            + Work.FTS.EllipticEst.sEta θ * B θ
            - (α ^ 2 / 2) * (Work.FTS.EllipticEst.sEta θ * C θ)
            + (α * (5 + α) / 2) * (Work.FTS.EllipticEst.sEta θ * D θ) from by
      funext θ; ring]
    simp only [MeasureTheory.integral_add hABC hD', MeasureTheory.integral_sub hAB hC',
      MeasureTheory.integral_add hA' intB, MeasureTheory.integral_const_mul]
  -- ## weighted Fubini back for the four terms
  have f1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * A θ)
      = ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2 * z ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
              * (Work.Spaces.pz u z θ) ^ 2) := by
    simp only [hAdef]
    exact (fubiniWeight (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)
      (g := Work.FTS.EllipticEst.sEta)
      (h := fun z θ => (Work.Spaces.pz u z θ) ^ 2) exp2).symm
  have f2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * B θ)
      = ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
              * (Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ)) := by
    simp only [hBdef]
    exact (fubiniWeight (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z => W z * (Work.Spaces.w z) ^ 2)
      (g := Work.FTS.EllipticEst.sEta)
      (h := fun z θ => Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ)
      exp5).symm
  have f3 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * C θ)
      = ∫ z in Work.Spaces.Iz,
          deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
    simp only [hCdef]
    exact (fubiniWeight (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z => deriv (deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z ^ 2)) z)
      (g := Work.FTS.EllipticEst.sEta)
      (h := fun z θ => (u z θ) ^ 2) exp3).symm
  have f4 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * D θ)
      = ∫ z in Work.Spaces.Iz,
          deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
    simp only [hDdef]
    exact (fubiniWeight (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z => deriv (fun z => W z * (Work.Spaces.w z) ^ 2 * z) z)
      (g := Work.FTS.EllipticEst.sEta)
      (h := fun z θ => (u z θ) ^ 2) exp4).symm
  -- ## replace `G` by `bslOp α u` in the left-hand side
  have hG : (∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)))
      = ∫ z in Work.Spaces.Iz, W z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ
            * (Work.Elliptic.bslOp α u z θ * u z θ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    by_cases hzδ : z ≤ δ
    · rw [hδW z hzδ]; ring
    · have hz0 : 0 < z := lt_trans hδ0 (lt_of_not_ge hzδ)
      congr 1
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards with θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · rw [← h0, sEta_zero]; ring
      · rcases eq_or_lt_of_le hθ.2 with hpi | hpi
        · rw [hpi, sEta_pi_div_two]; ring
        · rw [h.eq z hz0 θ h0 hpi]
  rw [hG, hfub1, hcomb, hlin, f1, f2, f3, f4]

end

end Work.FTS.EllipticEst.ThetaU.Pieces.AeDzParts
