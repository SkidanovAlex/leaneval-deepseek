import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.mst_minor_sup
import Submission.Work.BourgainPlan.Maximal.mst_minor_lp_per_n
import Submission.Work.BourgainPlan.Maximal.mstEta_support
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.mst_iw_lift

set_option linter.unusedVariables false

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped Topology

noncomputable section

/-- **The support of the MST bump is closed.**  A `C²` bump vanishing strictly outside `[-1/2,1/2]`
(`|x| > 1/2 → η x = 0`) also vanishes at the two boundary points `|x| = 1/2`: continuity at `±1/2`
and the one-sided limits (`𝓝[>]` at `1/2`, `𝓝[<]` at `-1/2`) give `η (±1/2) = 0`.  This is the
hypothesis shape (`1/2 ≤ |x|`) required by `mikhlin_conditions_scaled_bump`, `memLp_scaled_bump`
and `mstEta_support`, whereas the data supplied for the MST bump is the strict one. -/
lemma contDiff_eta_zero_of_half_le_abs {η : ℝ → ℂ} (hηc : ContDiff ℝ 2 η)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 := by
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact hη0 x hlt
  · -- the only new points are `x = ± 1/2`, handled by a one-sided limit
    have hx2 : x = 1 / 2 ∨ x = -(1 / 2) := (abs_eq (by norm_num)).mp heq.symm
    rcases hx2 with h | h
    · rw [h]
      have hev : η =ᶠ[𝓝[>] (1 / 2)] fun _ : ℝ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : (1 : ℝ) / 2 < y := hy
        exact hη0 y (by rw [abs_of_pos (by linarith : (0 : ℝ) < y)]; exact hy')
      have h1 : Filter.Tendsto η (𝓝[>] (1 / 2)) (𝓝 (η (1 / 2))) :=
        hηc.continuous.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto η (𝓝[>] (1 / 2)) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    · rw [h]
      have hev : η =ᶠ[𝓝[<] (-(1 / 2))] fun _ : ℝ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : y < (-(1 / 2) : ℝ) := hy
        exact hη0 y (by rw [abs_of_neg (by linarith : y < 0)]; linarith)
      have h1 : Filter.Tendsto η (𝓝[<] (-(1 / 2))) (𝓝 (η (-(1 / 2)))) :=
        hηc.continuous.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto η (𝓝[<] (-(1 / 2))) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2

/-- **The per-scale minor-arc gain `(n+1)^{-2}` without the Weyl input**: the same statement as
`mst_minor_lp_gain`, but with the pointwise minor-arc bound (MST (63)) taken as the explicit
hypothesis `hMS` — the type of `Maximal/mst_minor_sup_direct` (MST (63) proved from
`polyWeylKernel_offArc_gauss`, i.e. without `MSTWeylBound`).  Everything else is verbatim
`mst_minor_lp_gain`: `hMS` at the exponent `α = p(3-p)/(p-1)` feeds `mst_minor_per_n` (via
`iwSupersetBoundLift_proof`, the Mikhlin data `mikhlin_conditions_scaled_bump`, the narrowness
`mstEta_support` and the strict/closed support conversion `contDiff_eta_zero_of_half_le_abs`). -/
theorem mst_minor_lp_gain_direct
    (hMS : ∀ (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
      {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
      (η : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
      (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
      {α : ℝ} (hα : 0 < α),
      ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
          ‖star (Work.BourgainPlan.Maximal.mstWeyl P (2 ^ n) ξ)
            * (1 - Work.BourgainPlan.Maximal.mstXi l P.natDegree χ η n ξ)‖
            ≤ C * ((n : ℝ) + 1) ^ (-α))
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (M : ℝ) (hM : 0 < M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη1 : ∀ x : ℝ, |x| ≤ 1 / 4 → η x = 1)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (hηml : ∀ n : ℕ, MeasureTheory.MemLp (mstEta P.natDegree χ η n) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => mstMinorOp P l P.natDegree χ η n (hηml n) (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * ((n : ℝ) + 1) ^ (-2 : ℝ))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  -- the exponent of the pointwise bound, and its positivity
  have hαpos : (0 : ℝ) < p * (3 - p) / (p - 1) := by
    have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
    have h1 : (0 : ℝ) < p - 1 := by linarith
    have h2 : (0 : ℝ) < 3 - p := by linarith
    positivity
  -- the pointwise minor-arc bound of MST (63), at the exponent `p(3-p)/(p-1)`
  obtain ⟨l₀, hl₀⟩ := hMS (α := p * (3 - p) / (p - 1))
    P hd hc hχ0 hχ1 η M hM.le hηbd hη1 hη0 hαpos
  refine ⟨max l₀ 1, fun l hl => ?_⟩
  have hl₀' : l₀ ≤ l := le_trans (le_max_left _ _) hl
  have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hl
  obtain ⟨C, hCpos, N₀, hsup⟩ := hl₀ l hl₀'
  -- the strict-to-closed support of the bump
  have hsupp : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 :=
    contDiff_eta_zero_of_half_le_abs hηc hη0
  -- the Mikhlin data of the level bumps: `mikhlin_conditions_scaled_bump` at `c = 2^{n(d−χ)}`
  have h2d : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hmikh : ∀ n : ℕ,
      ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) ∧
      (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n) x‖ ≤ M) ∧
      (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
        (mstEta P.natDegree χ η n)) x‖ ≤ M) ∧
      (∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
        (mstEta P.natDegree χ η n)) x‖ ≤ M) := by
    intro n
    have he : 0 ≤ (n : ℝ) * ((P.natDegree : ℝ) - χ) :=
      mul_nonneg (Nat.cast_nonneg n) (by linarith)
    have hc1 : 1 ≤ |(2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ))| := by
      rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
      exact Real.one_le_rpow (by norm_num) he
    exact mikhlin_conditions_scaled_bump (η := η) (M := M)
      (c := (2 : ℝ) ^ ((n : ℝ) * ((P.natDegree : ℝ) - χ)))
      hM.le hc1 hηc hηbd hder hder2 hsupp
  have hcd : ∀ n : ℕ,
      ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) :=
    fun n => (hmikh n).1
  have hbdd : ∀ (n : ℕ) (x : ℝ),
      ‖Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n) x‖ ≤ M :=
    fun n => (hmikh n).2.1
  have hder' : ∀ (n : ℕ) (x : ℝ), |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
      (mstEta P.natDegree χ η n)) x‖ ≤ M := fun n => (hmikh n).2.2.1
  have hder2' : ∀ (n : ℕ) (x : ℝ), |x| ^ 2 * ‖iteratedDeriv 2
      (Work.BourgainPlan.Thm52.circleLift (mstEta P.natDegree χ η n)) x‖ ≤ M :=
    fun n => (hmikh n).2.2.2
  -- the narrow support of the level bumps (`mstEta_support`)
  have hsuppη : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        iwEps (mstRho l) (n ^ l) < ‖ξ‖ → mstEta P.natDegree χ η n ξ = 0 :=
    mstEta_support l hl1 P.natDegree (by omega) χ hχ0 (by linarith) η hηc.continuous hsupp
  -- the interpolation at the endpoints, with the pointwise bound of `mst_minor_sup`
  obtain ⟨C', hC'pos, N₁, hbound⟩ :=
    mst_minor_per_n iwSupersetBoundLift_proof P hp hp2 l hl1 χ η hηml M hM
      hcd hbdd hder' hder2' hsuppη le_rfl ⟨C, hCpos, N₀, hsup⟩
  refine ⟨C', hC'pos, N₁, fun n hn g => ?_⟩
  have hCnn : (0 : ℝ) ≤ C' * ((n : ℝ) + 1) ^ (-2 : ℝ) :=
    le_of_lt (mul_pos hC'pos (Real.rpow_pos_of_pos (by positivity) _))
  exact eLpNorm_le_of_lintegral_rpow_le_count (q := p)
    (C := C' * ((n : ℝ) + 1) ^ (-2 : ℝ)) (lt_trans zero_lt_one hp) hCnn (hbound n hn g)

end

end Work.BourgainPlan.Maximal
