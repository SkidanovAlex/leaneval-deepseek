import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixGlue.Wiring.Glue
import Submission.Work.BoseFixKin.Kinetic.fibre_lift_pt
import Submission.Work.BoseFixKin.Kinetic.kinetic_localisation_fs
import Submission.Work.BoseFixKin.kinRegimeFS_of_params
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixKin.Wiring` — the `hb`-free wiring from `LHYBoxB` to `HBoxGSymStateScaled`

Node G3 of `BOSE_BCLASH_LEAD.md`: the D2 (`b`-clash) repair, wired.

The three theorems here are the `hb`-free versions of the corresponding
`Work.BoseFixGlue` theorems.  The old chain carried the hypothesis

`hb : ∃ c₀, 0 < c₀ ∧ bValue ≤ c₀ ∧ KineticLocalisation c₀`

(an instance of FS `lem:LocKinEn` at a regime constant at least `1/16`).  It is now replaced by
the coupled-regime localisation `Work.BoseFixKin.Kinetic.kinetic_localisation_fs` together with the
parameter arithmetic `Work.BoseFixKin.kinRegimeFS_of_params`, both of which hold at FS's own
parameters (the coupling `ε_T s ≤ c₀ d` is `X^{3/4} ⇒ 0`).

* `kinInput_holds` — the kinetic lifting clause, `hb`-free;
* `HBoxGSymStateScaled_of_compareInputs` — the wiring, `hb`-free (the only use of `hb` was to
  produce *some* `KinRegime c₀` at FS's parameters; `c₀ := 1` supplies it);
* `HBoxGSymStateScaled_of_LHYBoxB` — the headline, with **no B-side hypothesis beyond `hL`**.

Nothing here edits `Submission/Work/BoseFixGlue/`; the `hb`-carrying originals stay in place.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixKin

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix Work.BoseFixGlue

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The kinetic clause, `hb`-free -/

/-- **The kinetic lifting at FS's parameters, without `hb`.**  From the coupled-regime
localisation (`kinetic_localisation_fs`) and FS's parameter arithmetic
(`kinRegimeFS_of_params`), the `N`-body kinetic word is dominated by the total kinetic energy for
every state supported in a centred box `abox N L` with `L ≥ ℓ(μ)`. -/
theorem kinInput_holds {v : ℝ³ → ℝ} (hav : 0 < a v) : ∃ ε : ℝ, 0 < ε ∧ KinInput v ε := by
  obtain ⟨c₀, hc₀, hKin⟩ := Work.BoseFixKin.Kinetic.kinetic_localisation_fs
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixKin.kinRegimeFS_of_params (v := v) hc₀ hav
  refine ⟨εr, hεr, fun μ hAdm N L hℓL Φ hΦ _hsym hsupp => ?_⟩
  have hregμ := hreg μ hAdm.1 hAdm.2.1
  have hℓpos : 0 < ℓB v μ := hregμ.1
  have hdpos : 0 < dB v μ := hregμ.2.1
  have hLpos : 0 < L := lt_of_lt_of_le hℓpos hℓL
  exact Work.BoseFixKin.Kinetic.fibre_lift_pt hℓpos hdpos (hKin _ _ _ _ _ hregμ) hLpos.le hΦ hsupp
    (Work.BoseFixGlue.Kinetic.integrable_kinForm hℓpos hdpos hLpos hΦ hsupp)

/-! ## 2. The wiring, `hb`-free -/

/-- **The wiring, with the C-side inputs bundled** (`CompareInputs`), without `hb`.

This is `Work.BoseFixGlue.HBoxGSymStateScaled_of_compareInputs` with the hypothesis `hb` deleted:
the only place the old proof used it was to produce *some* `KinRegime c₀` at FS's parameters,
which `Work.BoseFixGlue.Params.kinRegime_of_params` supplies at `c₀ := 1` (its `bValue ≤ 1` is
`by norm_num`).  `compare_box_energy_v2` consumes `hreg` only through `0 < d`, so `c₀ := 1`
is harmless. -/
theorem HBoxGSymStateScaled_of_compareInputs {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀' : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hav : 0 < a v)
    (hCI : CompareInputs v h) (hL : LHYBoxB v h η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ C (fun ρ => sideAt ρ (a v)) := by
  classical
  obtain ⟨εCI, hεCI, hCI'⟩ := hCI
  have hLcopy := hL
  obtain ⟨ε₁, hε₁, _hbox⟩ := hLcopy
  obtain ⟨εΛ, hεΛ, hAux⟩ := EΛ_ge_lambda_of_LHYBoxB hav hC hL
  obtain ⟨εr, hεr, hreg⟩ :=
    Work.BoseFixGlue.Params.kinRegime_of_params (c₀ := 1) one_pos (by norm_num [bValue]) hav
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
  have hregρ : KinRegime 1 (ℓB v ρ) (dB v ρ) (sB v ρ) (eTB v ρ) (bB v ρ) :=
    hreg ρ hρpos (le_trans hρle hM_r)
  have hvol := Work.BoseKinLoc.Volume.volume_coverU (ℓ := ℓB v ρ) hℓ hLpos.le
  have hIBP := Work.BoseFixGlue.IBP.green_identity hΦcd hΦsupp
  have hcmp := Work.BoseKinLoc.Compare.compare_box_energy_v2 (N := N) (v := v) (g := g0 v h)
    (ℓ := ℓB v ρ) (L := L)
    (μ := ρ) (d := dB v ρ) (s := sB v ρ) (εT := eTB v ρ) (b := bB v ρ) (c₀ := 1)
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

/-! ## 3. The headline, `hb`-free -/

/-- **The `hb`-free headline.**  From FS's box theorem `LHYBoxB` (on symmetric box states, particle
number free, at FS's parameters) the per-state scaled handoff
`Work.BoseTop.HBoxGSymStateScaled v η₀ C (ρ ↦ sideAt ρ (a v))` follows, with **no hypothesis on
the B side beyond `hL : LHYBoxB v h η₀ C`**. -/
theorem HBoxGSymStateScaled_of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hη₀ : 1 / 2000 < η₀) (hη₀' : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hv1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hav : 0 < a v) (hL : LHYBoxB v h η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ C (fun ρ => sideAt ρ (a v)) := by
  obtain ⟨εk, hεk, hkin⟩ := kinInput_holds (v := v) hav
  obtain ⟨εf, hεf, hfib⟩ := fibreInput_holds hav hC hL
  obtain ⟨εp, hεp, hpot⟩ := Work.BoseFixGlue.Pot.potInput_holds hR hv1 hv_supp hav
  obtain ⟨εs, hεs, hswap⟩ := Work.BoseFixGlue.Pot.swapInput_holds hR hv1 hv_supp hav
  have hCI : CompareInputs v h :=
    compareInputs_of_parts (ε₀ := min εk (min εp (min εf εs)))
      (lt_min hεk (lt_min hεp (lt_min hεf hεs)))
      (hkin.mono (min_le_left _ _))
      (hfib.mono (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
      (hswap.mono (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
      (hpot.mono (le_trans (min_le_right _ _) (min_le_left _ _)))
  exact HBoxGSymStateScaled_of_compareInputs hη₀ hη₀' hC hv1 hR hv_supp hav hCI hL

/-! ## 4. The rest of the chain, `hb`-free

The `hb`-free counterparts of `Work.BoseFixGlue`'s `compareInputs_of_fibre`,
`compareInputs_of_data`, `HBoxGSymStateScaled_of_LHYBoxB_fs` and
`HBoxGSymStateScaled_of_grading` (the `hb`-carrying originals stay in `BoseFixGlue`). -/

/-- **The C-side inputs** from the discharged kinetic clause and a given fibre clause at `εf`,
without `hb`. -/
theorem compareInputs_of_fibre {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    {εf : ℝ} (hεf : 0 < εf) (hfib : FibreInput v h εf) : CompareInputs v h := by
  obtain ⟨εk, hεk, hkin⟩ := kinInput_holds (v := v) hav
  obtain ⟨εp, hεp, hpot⟩ := Work.BoseFixGlue.Pot.potInput_holds hR hv1 hv_supp hav
  obtain ⟨εs, hεs, hswap⟩ := Work.BoseFixGlue.Pot.swapInput_holds hR hv1 hv_supp hav
  have hε : 0 < min εk (min εp (min εf εs)) :=
    lt_min hεk (lt_min hεp (lt_min hεf hεs))
  have h1 : min εk (min εp (min εf εs)) ≤ εk := min_le_left _ _
  have h2 : min εk (min εp (min εf εs)) ≤ εp :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have h3 : min εk (min εp (min εf εs)) ≤ εf :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : min εk (min εp (min εf εs)) ≤ εs :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨min εk (min εp (min εf εs)), hε, ?_⟩
  intro μ hAdm N L hℓL Φ hΦ hsym hsupp
  exact ⟨KinInput.mono hkin h1 μ hAdm N L hℓL Φ hΦ hsym hsupp,
    FibreInput.mono hfib h3 μ hAdm N L hℓL Φ hΦ hsym hsupp,
    SwapInput.mono hswap h4 μ hAdm N L hℓL Φ hΦ hsym hsupp,
    PotInput.mono hpot h2 μ hAdm N L hℓL Φ hΦ hsym hsupp⟩

/-- **The C-side inputs** with all four clauses discharged from `LHYBoxB`, without `hb`. -/
theorem compareInputs_of_data {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ} {R : ℝ}
    (hR : 0 < R) (hv1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hC : 0 ≤ C) (hL : LHYBoxB v h η₀ C) : CompareInputs v h := by
  obtain ⟨εf, hεf, hfib⟩ := fibreInput_holds hav hC hL
  exact compareInputs_of_fibre hR hv1 hv_supp hav hεf hfib

/-- The headline in the paper's ambient hypotheses (`0 ≤ v`, radial, `MemLp v 1`,
`tsupport v ⊆ ball 0 R`); the extra hypotheses are unused, kept to match the shape of the
original. -/
theorem HBoxGSymStateScaled_of_LHYBoxB_fs {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hv : 0 ≤ v) (hv1 : MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hη₀ : 1 / 2000 < η₀) (hη₀' : η₀ ≤ 1 / 2) (hC : 0 ≤ C)
    (hL : LHYBoxB v h η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ C (fun ρ => sideAt ρ (a v)) :=
  HBoxGSymStateScaled_of_LHYBoxB hη₀ hη₀' hC hv1 hR hv_supp hav hL

/-- **The end-to-end B-side chain, `hb`-free.**  From the §6 grading data (`NodeB2gB`) and the
§7–§11 restricted bound (`NodeRestrictedB`) the box theorem `LHYBoxB` follows
(`Work.BoseFixGlue.Ports.LHYBoxB_of_grading`, at the shifted constant `C + 1`), and the wiring
converts it into `HBoxGSymStateScaled`. -/
theorem HBoxGSymStateScaled_of_grading {v : ℝ³ → ℝ} {h : ScatSol v} {J J' η₀ C : ℝ}
    (hlhy : lhyC ≤ J) (hJJ : J < J') (hη₀ : 1 / 2000 < η₀) (hη₂ : η₀ < 2 / 323)
    (hC : 0 ≤ C) (hv1 : MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hav : 0 < a v)
    (hg : NodeB2gB v h J J') (hr : NodeRestrictedB v h J' η₀ C) :
    Work.BoseTop.HBoxGSymStateScaled v η₀ (C + 1) (fun ρ => sideAt ρ (a v)) :=
  HBoxGSymStateScaled_of_LHYBoxB hη₀ (by linarith) (by linarith) hv1 hR hv_supp hav
    (Work.BoseFixGlue.Ports.LHYBoxB_of_grading hlhy hav hC (by linarith) hη₂ hJJ hg hr)

end Work.BoseFixKin
