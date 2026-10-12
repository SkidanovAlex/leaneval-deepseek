import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixGlue.IBP.green_identity
import Submission.Work.BoseFixGlue.Params.kinRegime_of_params
import Submission.Work.BoseFixGlue.Wiring.ShiftHam
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Wiring.Main` — the wiring to `HBoxGSymStateScaled`

This is the C-side wiring of the corrected BoseBox chapter: it takes FS's box theorem
`Work.BoseBoxFix.LHYBoxB` (`thm:LHY-Box` on symmetric states, `n` free, at FS's parameters),
feeds it through

* the localisation comparison `Work.BoseKinLoc.Compare.compare_box_energy_v2` (FS
  `thm:CompareBoxEnergy`, proved in the workspace),
* the C-side inputs `Work.BoseFixGlue.CompareInputs` (the kinetic lifting, the fibre bound, FS
  `lem:LocPotential` and the Fubini input; each clause is discharged by a separate lemma of this
  chapter — see `Wiring/Glue.lean`),
* the transport of a corner-box state to the centred box (`Wiring/Shift.lean`,
  `Wiring/ShiftHam.lean`) and the Green identity,
* the arithmetic `Λ = gcTwoTerm ∘ (1/2 + η₀)` (`Work.BoseBox.Lambda_eq_gcTwoTerm`) and
  `∫g₀ = 8π a v` (`Submission.BoseGases.g0_integral`),

and produces **`Work.BoseTop.HBoxGSymStateScaled v η₀ C (ρ ↦ sideAt ρ (a v))`** — the per-state
handoff consumed by the proved `Work.BoseTop.theorem_1_2_of_HBoxGSymStateScaled` (through
`Work.BoseTop.PerN.HBoxGp_of_scaledState`).  The hypothesis `hb` is BoseKinLoc's
`KineticLocalisation` at some `c₀ ≥ bValue` (`D2` of the design, `BOSE_BOXNODES_LEAD.md` §5).

The scaled form is exactly what FS's route produces: the localisation comparison carries the
volume factor `((L+ℓ)/ℓ)³ = (L+ℓ)³/ℓ³`, so multiplying the box theorem `ℓ³Λ ≤ E_Λ` by it gives
`(L+ℓ)³Λ = (L+ℓ)³·gcTwoTerm` on the left, with no finite-`L` slack bookkeeping.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The symmetric Rayleigh quotient in integral form -/

/-- `symQuot` is the ratio of the two corner-box integrals. -/
lemma symQuot_eq_integral {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (Ψ : SymBox N L) :
    symQuot N L v Ψ
      = (∫ x in box N L, (Ψ : X N → ℝ) x * 𝓗 N v (Ψ : X N → ℝ) x)
        / (∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2) := by
  unfold symQuot
  rw [show (fun x : X N => (Ψ : X N → ℝ) x * (Ψ : X N → ℝ) x)
        = fun x : X N => ((Ψ : X N → ℝ) x) ^ 2 from by funext x; ring,
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]

/-- The elementary algebra of the volume factor: `(L+ℓ)³ c = ((L+ℓ)/ℓ)³ (ℓ³ c)`. -/
lemma cube_mul_eq_div_cube_mul {L ℓ c : ℝ} (hℓ : ℓ ≠ 0) :
    (L + ℓ) ^ 3 * c = ((L + ℓ) / ℓ) ^ 3 * (ℓ ^ 3 * c) := by
  field_simp

/-! ## 2. The wiring -/

/-- **The wiring, with the C-side inputs bundled** (`CompareInputs`).

This is the mathematical content of the wiring: the C-side clauses are consumed exactly as
`compare_box_energy_v2` consumes them, so the only remaining work of a caller is to produce
`CompareInputs` (i.e. the kinetic lifting, the fibre bound, FS `lem:LocPotential` and the
Fubini input) and `LHYBoxB`. -/
theorem HBoxGSymStateScaled_of_compareInputs {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀' : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hav : 0 < a v)
    (hb : ∃ c₀ : ℝ, 0 < c₀ ∧ bValue ≤ c₀ ∧ KineticLocalisation c₀)
    (hCI : CompareInputs v h) (hL : LHYBoxB v h η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ C (fun ρ => sideAt ρ (a v)) := by
  classical
  obtain ⟨c₀, hc₀, hbc₀, _hKin⟩ := hb
  obtain ⟨εCI, hεCI, hCI'⟩ := hCI
  have hLcopy := hL
  obtain ⟨ε₁, hε₁, _hbox⟩ := hLcopy
  obtain ⟨εΛ, hεΛ, hAux⟩ := EΛ_ge_lambda_of_LHYBoxB hav hC hL
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixGlue.Params.kinRegime_of_params hc₀ hbc₀ hav
  obtain ⟨ε₂, hε₂, hΛ⟩ := Lambda_nonpos_of_small (a := a v) (C := C) (η₀ := η₀) hav hC
  let M : ℝ := min εCI (min ε₁ (min εΛ (min εr ε₂)))
  have hMpos : 0 < M := by
    dsimp only [M]
    exact lt_min hεCI (lt_min hε₁ (lt_min hεΛ (lt_min hεr hε₂)))
  have hM_CI : M ≤ εCI := by dsimp only [M]; exact min_le_left _ _
  have hM_1 : M ≤ ε₁ := by
    dsimp only [M]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hM_Λ : M ≤ εΛ := by
    dsimp only [M]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hM_r : M ≤ εr := by
    dsimp only [M]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hM_2 : M ≤ ε₂ := by
    dsimp only [M]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- the diluteness tends to `0⁺`
  have htend : Tendsto (fun ρ : ℝ => ρ * (a v) ^ 3) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h1 : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        ((tendsto_id'.2 le_rfl : Tendsto (fun ρ : ℝ => ρ) (𝓝[>] (0 : ℝ))
          (𝓝[>] (0 : ℝ)))).mono_right
          nhdsWithin_le_nhds
      simpa using h1.mul_const ((a v) ^ 3)
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact Set.mem_Ioi.mpr (mul_pos hρ (pow_pos hav 3))
  have hsmall : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ * (a v) ^ 3 ≤ M := by
    have hb' := (htend.mono_right nhdsWithin_le_nhds).eventually
      (Metric.ball_mem_nhds (0 : ℝ) hMpos)
    filter_upwards [hb'] with ρ hρ
    rw [Real.dist_eq, sub_zero] at hρ
    linarith [(abs_lt.mp hρ).2]
  have hpar : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ParamsOK (paramsAt ρ (a v)) (ρ * (a v) ^ 3) := by
    have := htend.eventually paramsOK_fsParams
    exact this.mono fun ρ hρ => hρ
  filter_upwards [hsmall, hpar, self_mem_nhdsWithin] with ρ hρle hparOK hρpos
  have hAdm : Adm v M ρ := ⟨hρpos, hρle, hparOK⟩
  have hℓ : 0 < ℓB v ρ := sideB_pos hρpos hav
  have hℓne : ℓB v ρ ≠ 0 := ne_of_gt hℓ
  refine ⟨max 1 (ℓB v ρ), le_max_left _ _, fun L hL0 N hN Ψ => ?_⟩
  have hℓL : ℓB v ρ ≤ L := le_trans (le_max_right _ _) hL0
  have hLpos : 0 < L := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hL0
  -- ## the transported state
  set Φ : X N → ℝ := fun x => (Ψ : X N → ℝ) (cellShift N (-(cubeC L)) x) with hΦdef
  have hΨsupp : tsupport (Ψ : X N → ℝ) ⊆ box N L :=
    subset_trans Ψ.support interior_subset
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞) Φ := contDiff_shift_neg_cubeC (psi_contDiff Ψ.toCInfty0Box)
  have hΦsym : PermInvariant N Φ := permInvariant_shift_neg_cubeC Ψ.sym
  have hΦsupp : tsupport Φ ⊆ abox N L := tsupport_shift_neg_cubeC_subset_abox hΨsupp
  -- ## the C-side inputs at this density
  have hAdmCI : Adm v εCI ρ := ⟨hρpos, le_trans hρle hM_CI, hparOK⟩
  obtain ⟨hkinC, hfibC, hswapC, hpotC⟩ :=
    hCI' ρ hAdmCI N L hℓL Φ hΦcd hΦsym hΦsupp
  -- ## the change-of-variables identities
  have hA : (∫ x in abox N L, (Φ x) ^ 2) = ∫ w in box N L, ((Ψ : X N → ℝ) w) ^ 2 := by
    rw [hΦdef]
    exact abox_sq_eq_box hLpos hΨsupp
  have hB : (∫ x in abox N L, Φ x * 𝓗 N v Φ x)
      = ∫ w in box N L, (Ψ : X N → ℝ) w * 𝓗 N v (Ψ : X N → ℝ) w := by
    rw [hΦdef]
    exact abox_ham_eq_box hLpos hΨsupp
  have hApos : 0 < ∫ w in box N L, ((Ψ : X N → ℝ) w) ^ 2 := by
    have h := box_sq_integral_pos (N := N) hLpos Ψ.toCInfty0Box
    have h1 : (fun x : X N => (Ψ : X N → ℝ) x * (Ψ : X N → ℝ) x)
        = fun x : X N => ((Ψ : X N → ℝ) x) ^ 2 := by
      funext x; ring
    rwa [← h1]
  -- ## FS's comparison
  have hregρ : KinRegime c₀ (ℓB v ρ) (dB v ρ) (sB v ρ) (eTB v ρ) (bB v ρ) :=
    hreg ρ hρpos (le_trans hρle hM_r)
  have hvol := Work.BoseKinLoc.Volume.volume_coverU (ℓ := ℓB v ρ) hℓ hLpos.le
  have hIBP := Work.BoseFixGlue.IBP.green_identity hΦcd hΦsupp
  have hcmp := Work.BoseKinLoc.Compare.compare_box_energy_v2 (N := N) (v := v) (g := g0 v h) (ℓ := ℓB v ρ) (L := L)
    (μ := ρ) (d := dB v ρ) (s := sB v ρ) (εT := eTB v ρ) (b := bB v ρ) (c₀ := c₀)
    Φ hΦcd hΦsym hΦsupp hℓ hℓL hregρ hkinC hfibC hpotC hswapC hvol hIBP
  -- ## the box theorem bounds the box energy
  have hAdmΛ : Adm v εΛ ρ := ⟨hρpos, le_trans hρle hM_Λ, hparOK⟩
  have hmin : (ℓB v ρ) ^ 3 * Lambda (a v) C η₀ ρ
      ≤ min 0 (EΛ v (g0 v h) (ℓB v ρ) ρ (dB v ρ) (sB v ρ) (eTB v ρ) (bB v ρ)) :=
    (hAux ρ hAdmΛ).2.1
  -- ## `∫g₀ = 8π a v` and the division by the norm
  have hg0 : (∫ y : ℝ³, g0 v h y) = 8 * π * a v := g0_integral hR hv_supp h
  rw [hg0] at hcmp
  have hAwhole : (∫ x : X N, (Φ x) ^ 2) = ∫ x in abox N L, (Φ x) ^ 2 := by
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable N L)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ abox N L
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      by_contra hne
      have hne' : Φ x ≠ 0 := fun h => hne (by simp [h])
      exact hx (hΦsupp (subset_tsupport Φ hne'))
  have hmain : ((L + ℓB v ρ) / ℓB v ρ) ^ 3
        * min 0 (EΛ v (g0 v h) (ℓB v ρ) ρ (dB v ρ) (sB v ρ) (eTB v ρ) (bB v ρ))
      ≤ (∫ x in abox N L, Φ x * 𝓗 N v Φ x) / (∫ x in abox N L, (Φ x) ^ 2)
        - 8 * π * (a v) * ρ * (N : ℝ) := by
    rw [hAwhole] at hcmp
    have hAposAbox : 0 < ∫ x in abox N L, (Φ x) ^ 2 := by rw [hA]; exact hApos
    rw [le_sub_iff_add_le, le_div_iff₀ hAposAbox]
    linarith [hcmp]
  -- ## conclusion
  rw [symQuot_eq_integral Ψ, ← hA, ← hB]
  calc (L + sideAt ρ (a v)) ^ 3 * gcTwoTerm (a v) C (1 / 2 + η₀) ρ
      = ((L + ℓB v ρ) / ℓB v ρ) ^ 3
          * ((ℓB v ρ) ^ 3 * gcTwoTerm (a v) C (1 / 2 + η₀) ρ) :=
        cube_mul_eq_div_cube_mul hℓne
    _ = ((L + ℓB v ρ) / ℓB v ρ) ^ 3 * ((ℓB v ρ) ^ 3 * Lambda (a v) C η₀ ρ) := by
        rw [Work.BoseBox.Lambda_eq_gcTwoTerm]
    _ ≤ ((L + ℓB v ρ) / ℓB v ρ) ^ 3
          * min 0 (EΛ v (g0 v h) (ℓB v ρ) ρ (dB v ρ) (sB v ρ) (eTB v ρ) (bB v ρ)) := by
        refine mul_le_mul_of_nonneg_left hmin ?_
        exact pow_nonneg (div_nonneg (by linarith) hℓ.le) 3
    _ ≤ (∫ x in abox N L, Φ x * 𝓗 N v Φ x) / (∫ x in abox N L, (Φ x) ^ 2)
          - 8 * π * (a v) * ρ * (N : ℝ) := hmain

end Work.BoseFixGlue
