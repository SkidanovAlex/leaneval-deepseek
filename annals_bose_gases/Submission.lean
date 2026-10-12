import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChallengeDeps
import Submission.Ensembles
import Submission.Work.BoseRoot.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- ℝ³ as in Solution.lean (the global notation in BoseKinLoc.Defs is scoped[Work] since 10-09)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
open _root_.BoseGases.IsScatteringSolution
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian

open scoped ContDiff Topology Real

-- (ℝ³ notation now comes from the imported BoseKinLoc.Defs; same meaning)

local notation "Δ[" i "]" => partialLaplacian i

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

local notation "‖" f "‖_["N "," L"]" => √ ⟪f,f⟫_[N,L]

/-- Constant `η` in Theorem 1.2 (universal constant, cf. Theorem 6.8 of Fournais--Solovej). -/
noncomputable def η : ℝ := 1 / 2000

/-- Constant `𝓒` in Theorem 1.2; it depends on `𝓡 v` and `R / a v`. -/
noncomputable def 𝓒 (𝓡 : ℝ) (r : ℝ) : ℝ := 1

lemma eta_pos : 0 < η := by
  unfold η
  norm_num


/--
`theorem_1_2` reduced to its two deep research inputs (machine-verified).

The second conjunct of `theorem_1_2` is the Lee--Huang--Yang lower bound on the
thermodynamic ground-state energy density.  This meta-theorem shows that the
whole theorem follows from exactly two hypotheses:

  * `hing` -- Ingredient 1 (`gcExcess_witness_aux`, `Submission.Excess`): the
    T = 0 equivalence of ensembles (vanishing canonical excess) on some density
    interval `(0,ρmax)`.  Via `Closure2.gcSup_upper_of_excess` and
    `GCPressure.eventually_hconv_of_gcSup_upper` (assembled in
    `Layer2.layer2_hconv_of_excess`) it yields the convergence of the
    box-energy densities along the joint filter at every small density -- the
    thermodynamic-limit existence (`hconv` of `Endgame`);

  * `hbox` -- the eventual Fournais--Solovej box lower bound (their Theorem
    LHY-Box): for every small density `ρ`, eventually along the joint filter,
    `lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1/2 + η) (N/L³) ≤ L⁻³ · E(N,L,v)`.

Everything else (continuity of the right-hand side in the density, the filter
lifting, the positivity of `η`) is proved here.
-/
theorem theorem_1_2_of_ensembles_and_box (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball 0 R)
    (hing : ∃ ρmax : ℝ, 0 < ρmax ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → gcExcess_witness_aux v ρmax ρ)
    (hbox : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p) :
    0 < η ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        𝓒 (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + η)) := by
  constructor
  · exact eta_pos
  · rcases hing with ⟨ρmax, hρmax0, haux⟩
    have hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ,
        Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) :=
      layer2_hconv_of_excess (v := v) hv_nonneg hv_memL1 hR.le hv_supp hρmax0 haux
    have hs : 0 < 1 / 2 + η := by linarith [eta_pos]
    have hb : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ρ ≤ e ρ v :=
      lhy_bound_of_convergence_and_box (v := v) (A := a v) (K := 𝓒 (𝓡 v) (R / a v))
        (s := 1 / 2 + η) hs hconv hbox
    filter_upwards [hb] with ρ hρ
    simpa [lhyRhs] using hρ


/--
`theorem_1_2` reduced to its two *classical* research inputs (machine-verified).

This is the cleanest interface for future work.  Writing

    ensembles(ρmax) := ∀ ρ ∈ (0,ρmax):  diag v ρ L ⟶ gcSup v ρmax ρ   as L → ∞

(the existence of the thermodynamic limit of the canonical box-energy density
and its identification with the grand-canonical Legendre envelope — the T = 0
equivalence of ensembles; via `Submission.Ensembles` this implies Ingredient 1
`gcExcess_witness_aux` and hence Layer-2 convergence `hconv`), the whole
theorem reduces to exactly

  * `hens`  — `∃ρmax>0`, `ensembles(ρmax)`;
  * `hbox`  — the eventual Fournais--Solovej box lower bound (Theorem
    LHY-Box) in `lhyRhs` form along the joint filter.

Everything else (the RHS algebra, the continuity of the RHS in the density,
the filter lifting, the positivity of `η`) is machine-verified here and in the
modules below.
-/
theorem theorem_1_2_of_diag_limit_and_box (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball 0 R)
    (hens : ∃ ρmax : ℝ, 0 < ρmax ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρmax →
      Tendsto (fun L : ℝ => diag v ρ L) atTop (𝓝 (gcSup v ρmax ρ)))
    (hbox : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p) :
    0 < η ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        𝓒 (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + η)) := by
  rcases hens with ⟨ρmax, hρmax0, hensρ⟩
  have hing : ∃ ρmax : ℝ, 0 < ρmax ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → gcExcess_witness_aux v ρmax ρ := by
    refine ⟨ρmax, hρmax0, ?_⟩
    intro ρ hρ0 hρlt
    exact haux_of_diag_tendsto_gcSup (v := v) (ρ := ρ) (ρmax := ρmax)
      hv_nonneg hv_memL1 hρmax0 hρ0 hR.le hv_supp (hensρ ρ hρ0 hρlt)
  exact theorem_1_2_of_ensembles_and_box v hv_nonneg hv_memL1 hR hv_supp hing hbox

/--
The `a v = 0` branch of `theorem_1_2` needs only Ingredient 1 (Layer 2), not
the Fournais--Solovej box bound: when `a v = 0` the right-hand side of the
Lee--Huang--Yang inequality vanishes, so only `e ρ v ≥ 0` is required -- and
that follows from the thermodynamic-limit convergence of the (nonnegative)
box-energy densities along the joint filter (`layer2_hconv_of_excess` +
`ThermoLimit.e_nonneg_of_tendsto`).
-/
theorem theorem_1_2_av_zero_of_ensembles (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball 0 R)
    (hav : a v = 0)
    (hing : ∃ ρmax : ℝ, 0 < ρmax ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρmax → gcExcess_witness_aux v ρmax ρ) :
    0 < η ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        𝓒 (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + η)) := by
  constructor
  · exact eta_pos
  · rcases hing with ⟨ρmax, hρmax0, haux⟩
    have hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ,
        Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) :=
      layer2_hconv_of_excess (v := v) hv_nonneg hv_memL1 hR.le hv_supp hρmax0 haux
    filter_upwards [hconv, (self_mem_nhdsWithin : (Set.Ioi (0 : ℝ)) ∈ 𝓝[>] (0 : ℝ))]
      with ρ hρ hmem
    rcases hρ with ⟨x, hx⟩
    have hρpos : 0 < ρ := hmem
    have hxη : Tendsto (fun p : ℝ × ℕ => boxDensity v p) (jointFilter ρ) (𝓝 x) := hx
    unfold boxDensity at hxη
    have hE : 0 ≤ e ρ v := e_nonneg_of_tendsto (v := v) hρpos hv_nonneg (x := x) hxη
    have hX : 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        𝓒 (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + η)) = 0 := by
      rw [hav]
      ring
    rwa [hX]


/--
`theorem_1_2` reduced to the *continuity* of the liminf density plus the box bound
(machine-verified).

This is the cleanest interface for the elementary classical program.  Write

    cont(ρmax) := ∀ ρ' ∈ (0,ρmax):  ρ ↦ diagLiminf v ρ is continuous at ρ'.

By the window sandwich (`DiagLimit.diagLimsup_le_diagLiminf_of_right_lc`) and the
joint-filter lifting (`JointLim.tendsto_boxDensity_of_diag_limits_on`), continuity
of the liminf function yields the thermodynamic-limit convergence `hconv`
(`eventually_hconv_of_liminf_continuous`) -- the box-energy densities converge
along the joint filter at every small density.  Continuity of `ρ ↦ diagLiminf v ρ`
is classically derived from the marginal-cost bound (adding `k` particles to a box
costs at most `k·M`), which gives Lipschitz regularity of the liminf density; it is
strictly weaker than the equivalence-of-ensembles statement `hing` of
`theorem_1_2_of_ensembles_and_box` (`hing` forces the limit to equal the
grand-canonical envelope `gcSup`, which is continuous).  This meta-theorem shows
that the `a v = 0` case of `theorem_1_2` needs only this elementary continuity
claim -- no scattering/box-bound content (`hbox` then holds with zero right-hand
side) -- and that the `a v ≠ 0` case needs additionally the eventual
Fournais--Solovej box lower bound `hbox`.
-/
theorem theorem_1_2_of_liminf_continuous_and_box (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v)
    (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball 0 R)
    (hcont : ∃ ρmax : ℝ, 0 < ρmax ∧
      ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρmax → ContinuousAt (diagLiminf v) ρ')
    (hbox : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p) :
    0 < η ∧ ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      e ρ v ≥ 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        𝓒 (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + η)) := by
  constructor
  · exact eta_pos
  · rcases hcont with ⟨ρmax, hρmax0, hcontρ⟩
    have hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ,
        Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) :=
      eventually_hconv_of_liminf_continuous (v := v) hv_nonneg hv_memL1 hR.le hv_supp
        hρmax0 hcontρ
    have hs : 0 < 1 / 2 + η := by linarith [eta_pos]
    have hb : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ρ ≤ e ρ v :=
      lhy_bound_of_convergence_and_box (v := v) (A := a v) (K := 𝓒 (𝓡 v) (R / a v))
        (s := 1 / 2 + η) hs hconv hbox
    filter_upwards [hb] with ρ hρ
    simpa [lhyRhs] using hρ

/-- The box lower bound `hbox` in the `a v = 0` case: the right-hand side
vanishes (`lhyRhs_eq_zero_of_A_eq_zero`) and the box densities are nonnegative
along the joint filter (`eventually_pos_L` + `boxEnergy_nonneg`).  So when the
scattering length is zero, `hbox` needs no Fournais--Solovej input. -/
theorem hbox_of_av_zero {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) {R : ℝ} (hav : a v = 0) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ᶠ p in jointFilter ρ,
      lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ((p.2 : ℝ) / p.1 ^ 3) ≤ boxDensity v p := by
  filter_upwards [(self_mem_nhdsWithin : (Set.Ioi (0 : ℝ)) ∈ 𝓝[>] (0 : ℝ))] with ρ hρpos
  have hRhs : ∀ x : ℝ, lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) x = 0 := by
    intro x
    rw [hav]
    exact lhyRhs_eq_zero_of_A_eq_zero (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) x
  filter_upwards [eventually_pos_L ρ (le_of_lt hρpos)] with p hp
  rw [hRhs]
  unfold boxDensity
  have hzpow : 0 ≤ p.1 ^ (-3 : ℤ) := by
    rw [zpow_neg]
    exact inv_nonneg.mpr (pow_nonneg hp.le 3)
  exact mul_nonneg hzpow (boxEnergy_nonneg hp hv_nonneg)

 /-- Non-negativity of the scattering length under the hypotheses of Theorem 1.2:
in the branch where a radial scattering solution exists, `0 ≤ a v ≤ R`
(`Submission.ScatT3.chosen_av_bounds_weak`, from the a.e. bounds `0 ≤ ω ≤ 1`
of the scattering solution), and `a v = 0` otherwise
(`ScatteringDefs.a_eq_zero_of_not_exists`).  The chemical potential
`8πa v·ρ` used in the grand-canonical comparison is therefore nonnegative. -/
lemma av_nonneg {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hv_radial : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) : 0 ≤ a v := by
  by_cases h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v
  · exact (chosen_av_bounds_weak (v := v) (R := R) hR hv_nonneg hv_radial hv_supp h).1
  · have hav : a v = 0 := a_eq_zero_of_not_exists v h
    rw [hav]

/--
Statement of Theorem 1.2 (The Lee-Huang-Yang Formula).
-/
theorem theorem_1_2 (v : ℝ³ → ℝ) (hv_ne_zero : ¬ v =ᵐ[volume] 0) (hv_nonneg : 0 ≤ v)
    (hv_radial : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball 0 R) : 0 < η ∧ ∀ᶠ ρ in 𝓝[>] 0,
      e ρ v ≥ 4 * π * ρ ^ 2 * a v * (1 + (128 / (15 * √ π)) * √ (ρ * a v ^ 3) -
        𝓒 (𝓡 v) (R / a v) * (ρ * a v ^ 3) ^ (1 / 2 + η)) := by
  constructor
  · exact eta_pos
  · -- Layer 2: the thermodynamic-limit convergence of the box-energy densities
    -- along the joint filter at every small density (hypothesis-free; from the
    -- marginal-cost Lipschitz continuity of `diagLiminf`, see NOTES.md).
    have hcont : ∃ ρmax : ℝ, 0 < ρmax ∧
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < ρmax → ContinuousAt (diagLiminf v) ρ' :=
      liminf_continuous_hcont (v := v) hv_nonneg hv_memL1
    have hconv : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ x : ℝ,
        Tendsto (boxDensity v) (jointFilter ρ) (𝓝 x) := by
      rcases hcont with ⟨ρmax, hρmax0, hcontρ⟩
      exact eventually_hconv_of_liminf_continuous (v := v) hv_nonneg hv_memL1
        hR.le hv_supp hρmax0 hcontρ
    have hav0 : 0 ≤ a v := av_nonneg (v := v) hv_nonneg hv_radial hR hv_supp
    -- (hpres) The remaining deep input: the Fournais--Solovej LHY-Background
    -- bound at the *pressure* level (the corpus-native grand-canonical form of
    -- their Theorem LHY-Background, which follows from Theorem LHY-Box by
    -- CompareBoxEnergy).  At the FS chemical potential `λ = 8πa v·ρ`, for some
    -- truncation `ρmax > ρ` of the admissible particle numbers, the
    -- grand-canonical pressure density `gcPressure v ρmax (8πa v ρ)` satisfies
    -- the two-term Lee--Huang--Yang lower bound (with any positive error
    -- exponent `1/2 + η₀ > 1/2 + η`; the coefficient absorption into
    -- `𝓒 (𝓡 v) (R / a v)` is automatic since `(ρa³)^(η₀−η) → 0` as `ρ → 0`).
    have hpres : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∃ ρmax : ℝ, 0 < ρmax ∧ ρ < ρmax ∧
        lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ρ ≤
          gcPressure v ρmax (8 * π * a v * ρ) + 8 * π * a v * ρ * ρ := by
      -- Wired (curric-46, 2026-10-08): root assembly `Submission/Work/BoseRoot/Assembly.lean`.
      simpa only [η, 𝓒, Work.BoseTop.etaBose_eq] using
        Work.BoseRootAsm.hpres_root v hv_nonneg hv_radial hv_memL1 hR hv_supp
    filter_upwards [self_mem_nhdsWithin, hconv, hpres] with ρ hρpos hconvρ hpresρ
    rcases hpresρ with ⟨ρmax, hρmax0, hρlt, hp⟩
    rcases hconvρ with ⟨x, hx⟩
    have hμ : 0 ≤ 8 * π * a v * ρ := by
      have h1 : 0 ≤ 8 * π := by positivity
      have h2 : 0 ≤ 8 * π * a v := mul_nonneg h1 hav0
      exact mul_nonneg h2 hρpos.le
    have hgc : gcPressure v ρmax (8 * π * a v * ρ) + (8 * π * a v * ρ) * ρ ≤ e ρ v :=
      e_ge_gcPressure_add (v := v) (ρ := ρ) (μ := 8 * π * a v * ρ) (ρmax := ρmax)
        hρpos hρmax0 hρlt hμ hv_nonneg hv_memL1 hR.le hv_supp hx
    have hRhs : lhyRhs (a v) (𝓒 (𝓡 v) (R / a v)) (1 / 2 + η) ρ ≤ e ρ v := le_trans hp hgc
    simpa [lhyRhs] using hRhs

end BoseGases

end Submission
