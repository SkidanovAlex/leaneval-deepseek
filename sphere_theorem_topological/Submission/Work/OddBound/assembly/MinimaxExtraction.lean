import Mathlib
import Submission.Work.OddBound.AssemblyKit
import Submission.Work.OddBound.assembly.continuous_gonEnergy
import Submission.Work.OddBound.assembly.gonSideLen_le_of_gonEnergy_le
import Submission.Work.OddBound.assembly.curveSpeed_comp_mul_of_unitSpeed
import Submission.Work.OddBound.assembly.gonEnergy_inscribed_le
import Submission.Work.OddBound.assembly.minimaxValue_bounds

/-!
# `MinimaxExtraction`: the loop-space minimax on the based polygon space

This module proves `Work.OddBound.MinimaxExtraction K` — the last classical input of the
odd-dimensional Klingenberg length bound — for the **based** polygon model `P = Fin (N-1) → M`:

* the competitor set is `Work.OddBound.GonMinimaxSet p a b` (continuous paths of based `N`-gons from
  the polygon inscribed in the closed geodesic `γ` to the constant polygon `p`), with value
  `Work.OddBound.GonMinimaxValue p a b`;
* the value bound `Λ ≥ 2π²/K` is `Work.OddBound.polygonValueBound` (proved);
* the upper bound `Λ ≤ B²/2` comes from the balanced based null-homotopy
  (`Work.OddBound.exists_balanced_based_nullhomotopy`, `Work.OddBound.exists_gonEnergy_le_of_balanced_nullhomotopy`);
* the mountain pass `Work.OddBound.mountainPass3.exists_critical_index_le_one_local` produces a
  critical polygon at level `Λ` with no negative-definite plane;
* the first variation `Work.OddBound.polygon.isCritical_gonEnergy_geodesic` turns it into a closed
  geodesic of length `T = √(2Λ) ≥ 2π/√K`;
* the index transfer `Work.OddBound.indexTransfer.hasNegDefPlane_of_negativeDirichletIndex`
  converts a negative-definite Dirichlet plane along that geodesic into a negative-definite plane for
  the polygon energy, contradicting the mountain pass.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

theorem minimaxExtraction
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] {K : ℝ} :
    MinimaxExtraction (I := I) (cov := cov) hmet htor K := by
  intro hsc hcurv hK p γ L hL hLlt hγsm hgeo hne hunit hclosed hγ0 hper hLHL
  classical
  haveI : SimplyConnectedSpace M := hsc
  -- ## Step 0: a uniform injectivity radius, shrunk below `π/√K`
  obtain ⟨ρ₀, hρ₀pos, hρ₀all⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  set ρ : ℝ := min ρ₀ (Real.pi / (2 * Real.sqrt K)) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀pos (by positivity)
  have hρlt : ρ < Real.pi / Real.sqrt K := by
    rw [hρdef]
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    have h2s : Real.sqrt K < 2 * Real.sqrt K := by linarith
    exact div_lt_div_of_pos_left Real.pi_pos hsK h2s
  have hρinj : ∀ x : M, InjAtLeast hmet x ρ := fun x =>
    Submission.InjRadius.injAtLeast_mono (I := I) hmet (hρ₀all x)
      (by rw [hρdef]; exact min_le_left _ _)
  -- ## Step 1: the balanced based null-homotopy and its length bound `B`
  have hγbalspeed : ∀ s : ℝ, curveSpeed (I := I) (fun r : ℝ => γ (L * r)) s
      = curveLength (I := I) (fun r : ℝ => γ (L * r)) 0 1 := by
    intro s
    have h := Work.OddBound.assembly.curveSpeed_comp_mul_of_unitSpeed (I := I) hL hγsm hunit hper
    rw [h.1 s, h.2]
  obtain ⟨Hf, B, hBpos, hcont, hHfper, hHfbase, hHf0, hHf1, hHfpiece, hHflen, hHfbal⟩ :=
    Work.OddBound.exists_balanced_based_nullhomotopy (I := I) (cov := cov) hmet htor hL hγsm
      hper hγ0 hγbalspeed
  -- ## Step 2: choose `N`
  set C : ℝ := B ^ 2 / 2 + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  obtain ⟨N, hNgt⟩ : ∃ N : ℕ,
      max (max (4 * Real.pi ^ 2 / (K * ρ ^ 2)) (2 * C / ρ ^ 2)) 3 < (N : ℝ) :=
    exists_nat_gt _
  have hN3 : 3 ≤ N := by
    have h : (3 : ℝ) ≤ (N : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hNgt)
    exact_mod_cast h
  have hNpos : 0 < N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hρ2pos : (0 : ℝ) < ρ ^ 2 := by positivity
  have hbig : 4 * Real.pi ^ 2 / (K * ρ ^ 2) < (N : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hNgt
  have hNside : 2 * C / ρ ^ 2 < (N : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hNgt
  have hside_lt : Real.sqrt (2 * C / (N : ℝ)) < ρ := by
    rw [Real.sqrt_lt' hρpos, div_lt_iff₀ hNposR]
    have h2 : 2 * C < ρ ^ 2 * (N : ℝ) := by
      rw [div_lt_iff₀ hρ2pos] at hNside
      linarith [hNside]
    linarith [h2]
  -- ## Step 3: the polygon space as a charted space on `Fin (N-1) → E`
  letI : ChartedSpace ((Fin (N - 1)) → E) ((Fin (N - 1)) → M) :=
    Work.OddBound.piChartedSpaceExt (I := I) N
  letI : IsManifold (𝓘(ℝ, (Fin (N - 1)) → E)) 2 ((Fin (N - 1)) → M) :=
    Work.OddBound.isManifold_piChartedSpaceExt (I := I) N 2 (by decide)
  -- ## Step 4: the value bounds for the minimax value `Λ`
  have hfcont : Continuous (fun w : Fin (N - 1) → M => gonEnergy (I := I) p w) :=
    Work.OddBound.assembly.continuous_gonEnergy (I := I) (N := N) p
  set Λ : ℝ := GonMinimaxValue (N := N) (I := I) p (inscribedGon (N := N) L γ)
    (constantGon (N := N) p) with hΛdef
  have hval : 2 * Real.pi ^ 2 / K ≤ Λ ∧ Λ ≤ B ^ 2 / 2 := by
    have h := Work.OddBound.assembly.minimaxValue_bounds (I := I) (cov := cov) hmet htor hK hcurv
      hL hLlt hγsm hgeo hne hunit hper hγ0 hρpos hρlt hρinj hN3 hbig
      hcont hHfper hHfbase hHf0 hHf1 hHfpiece hBpos hHflen hHfbal
    rw [← hΛdef] at h
    exact h
  have hΛC : Λ < C := by rw [hCdef]; linarith [hval.2]
  have hΛpos : 0 < Λ := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 / K) hval.1
  -- the mountain pass hypotheses
  have hside_le : ∀ (w : Fin (N - 1) → M), gonEnergy (I := I) p w ≤ C →
      ∀ i : Fin N, gonSideLen (I := I) p w i < ρ := by
    intro w hw i
    exact lt_of_le_of_lt
      (Work.OddBound.assembly.gonSideLen_le_of_gonEnergy_le (I := I) (N := N) hNpos p
        (le_of_lt hCpos) hw i) hside_lt
  have hsm : ∀ z : Fin (N - 1) → M, gonEnergy (I := I) p z ≤ C →
      ∃ e : OpenPartialHomeomorph ((Fin (N - 1)) → M) ((Fin (N - 1)) → E),
        e ∈ atlas ((Fin (N - 1)) → E) ((Fin (N - 1)) → M) ∧ z ∈ e.source ∧
        ContDiffAt ℝ 2 (fun x : (Fin (N - 1)) → E => gonEnergy (I := I) p (e.symm x)) (e z) := by
    intro z hz
    refine ⟨Work.OddBound.piExtChart (I := I) z,
      Work.OddBound.piExtChart_mem_atlas (I := I) z,
      Work.OddBound.mem_piExtChart_source (I := I) z, ?_⟩
    exact Work.OddBound.chartAlgebra.contDiffAt_gonEnergy_piExtChart_gen (I := I) (cov := cov)
      hmet htor (N := N) hN3 (p := p) (x := z) (w := z)
      (Work.OddBound.mem_piExtChart_source (I := I) z) (R := ρ) hρpos hρinj
      (fun i => hside_le z hz i)
  have hfa : gonEnergy (I := I) (N := N) p (inscribedGon (N := N) L γ) ≤ L ^ 2 / 2 := by
    rw [← hγ0]
    exact Work.OddBound.assembly.gonEnergy_inscribed_le (I := I) (N := N) hN2 hL hγsm hunit hclosed
  have hLsq : L ^ 2 / 2 < 2 * Real.pi ^ 2 / K := by
    have h2 : (2 * Real.pi / Real.sqrt K) ^ 2 = 4 * Real.pi ^ 2 / K := by
      rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hK)]
      ring
    have h1 : L ^ 2 < 4 * Real.pi ^ 2 / K := by
      rw [← h2]
      exact pow_lt_pow_left₀ hLlt (le_of_lt hL) two_ne_zero
    have h1' : L ^ 2 * K < 4 * Real.pi ^ 2 := (lt_div_iff₀ hK).mp h1
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hK]
    linarith [h1']
  have hfb : gonEnergy (I := I) (N := N) p (constantGon (N := N) p) = 0 := by
    have hzero : ∀ i : Fin N, gonSideLen (I := I) (N := N) p (constantGon (N := N) p) i = 0 := by
      intro i
      have hv0 : gonVert (N := N) p (constantGon (N := N) p) (i : ℕ) = p := by
        simp only [gonVert, constantGon]
        split_ifs <;> rfl
      have hv1 : gonVert (N := N) p (constantGon (N := N) p) ((i : ℕ) + 1) = p := by
        simp only [gonVert, constantGon]
        split_ifs <;> rfl
      rw [gonSideLen, hv0, hv1, Submission.Distance.riemannianDist_self]
    rw [gonEnergy, Finset.sum_eq_zero (fun i _ => by rw [hzero i]; ring)]
    ring
  have hlt : max (gonEnergy (I := I) (N := N) p (inscribedGon (N := N) L γ))
      (gonEnergy (I := I) (N := N) p (constantGon (N := N) p)) < Λ :=
    max_lt (lt_of_le_of_lt hfa (lt_of_lt_of_le hLsq hval.1))
      (by rw [hfb]; exact hΛpos)
  -- the competitor path
  have hpath : ∃ σ : ℝ → Fin (N - 1) → M,
      ContinuousOn σ (Set.Icc (0 : ℝ) 1) ∧ σ 0 = inscribedGon (N := N) L γ ∧
        σ 1 = constantGon (N := N) p := by
    refine ⟨fun τ i => Hf (((i : ℕ) + 1 : ℝ) / N) τ, ?_, ?_, ?_⟩
    · apply Continuous.continuousOn
      apply continuous_pi
      intro i
      exact hcont.comp (Continuous.prodMk continuous_const continuous_id)
    · funext i
      show Hf (((i : ℕ) + 1 : ℝ) / N) 0 = inscribedGon (N := N) L γ i
      rw [hHf0]
      congr 1
      ring
    · funext i
      exact hHf1 (((i : ℕ) + 1 : ℝ) / N)
  -- ## Step 5: the mountain pass
  obtain ⟨z, hzval, hzcrit, hznndef⟩ :=
    Work.OddBound.mountainPass3.exists_critical_index_le_one_local
      (H' := (Fin (N - 1)) → E) (P := (Fin (N - 1)) → M)
      (f := fun w : Fin (N - 1) → M => gonEnergy (I := I) p w)
      hfcont hpath (Λ := Λ) (by rw [hΛdef]; rfl) hlt (C := C) hΛC hsm
  have hzC : gonEnergy (I := I) p z ≤ C := hzval ▸ hΛC.le
  have hzpos : 0 < gonEnergy (I := I) p z := hzval ▸ hΛpos
  have hsz : ∀ i : Fin N, gonSideLen (I := I) p z i < ρ := hside_le z hzC
  -- ## Step 6: criticality in the concrete extended chart, hence first variation
  obtain ⟨e, he, hzsrc, hfderiv⟩ := hzcrit
  obtain ⟨x, hx⟩ := Work.OddBound.exists_piExtChart_eq_of_mem_atlas (I := I) he
  rw [hx] at hfderiv hzsrc
  have hC2x : ContDiffAt ℝ 2
      (fun u : (Fin (N - 1)) → E =>
        gonEnergy (I := I) p ((Work.OddBound.piExtChart (I := I) x).symm u))
      ((Work.OddBound.piExtChart (I := I) x) z) :=
    Work.OddBound.chartAlgebra.contDiffAt_gonEnergy_piExtChart_gen (I := I) (cov := cov)
      hmet htor (N := N) hN3 hzsrc (R := ρ) hρpos hρinj hsz
  have hGonCrit : GonCritical (I := I) p z :=
    Work.OddBound.gonCritical_of_piExtChart_critical (I := I) hzsrc
      (hC2x.differentiableAt (by norm_num)) hfderiv
  obtain ⟨T, c, hTpos, hTlen, hTsq, hc0, hcT, hcsmOn, hcgeoOn, hcneOn, hcspOn, hcsample,
    hcstraight⟩ :=
    Work.OddBound.polygon.isCritical_gonEnergy_geodesic (I := I) (cov := cov) hmet htor
      (N := N) hN2 (p := p) (w := z) (R := ρ) hρpos hρinj hsz hzpos hGonCrit
  -- ## Step 7: the length bound `T ≥ 2π/√K`
  have hTge : 2 * Real.pi / Real.sqrt K ≤ T := by
    have h2 : (2 * Real.pi / Real.sqrt K) ^ 2 = 4 * Real.pi ^ 2 / K := by
      rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hK)]
      ring
    have hT2 : (2 * Real.pi / Real.sqrt K) ^ 2 ≤ T ^ 2 := by
      have hΛK : 2 * Real.pi ^ 2 ≤ Λ * K := (div_le_iff₀ hK).mp hval.1
      rw [← hTsq, hzval, h2, div_le_iff₀ hK]
      nlinarith [hΛK]
    have h := Real.sqrt_le_sqrt hT2
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (le_of_lt hTpos)] at h
  -- ## Step 8: extend to a global geodesic (with unit speed)
  obtain ⟨c', hc'sm, hc'geo, hc'ne, hc'speed, hc'eq⟩ :=
    Work.OddBound.exists_global_geodesic_extension (I := I) (cov := cov) hmet
      (a := (0 : ℝ)) (b := T) hTpos hcsmOn hcgeoOn
      (fun t ht => hcneOn t (Set.Ioo_subset_Icc_self ht)) hcspOn
  have hcsp' : ∀ t ∈ Set.Icc (0 : ℝ) T, curveSpeed (I := I) c' t = 1 :=
    fun t _ => hc'speed t
  refine ⟨T, c', hTge, ?_, hc'sm, hc'geo, hc'ne, hcsp', ?_⟩
  · rw [hc'eq T ⟨hTpos.le, le_rfl⟩, hcT, hc'eq 0 ⟨le_rfl, hTpos.le⟩, hc0]
  · -- the index conclusion, by contradiction with the index transfer
    by_contra hcon
    rw [DirichletIndexLeOne] at hcon
    push_neg at hcon
    obtain ⟨V, W, hVsm, hV0, hVT, hWsm, hW0, hWT, hneg⟩ := hcon
    have hsd : ∀ i : Fin N, gonSideLen (I := I) p z i = T / (N : ℝ) := fun i => hcstraight.1 i
    have hsmpl : ∀ i : Fin (N + 1), c' (((i : ℕ) : ℝ) * T / N) = gonVert p z (i : ℕ) := by
      intro i
      have hmem : (((i : ℕ) : ℝ) * T / N) ∈ Set.Icc (0 : ℝ) T := by
        refine ⟨by positivity, ?_⟩
        have hi : ((i : ℕ) : ℝ) ≤ (N : ℝ) := by
          have h : (i : ℕ) ≤ N := by omega
          exact_mod_cast h
        rw [div_le_iff₀ hNposR]
        nlinarith [hTpos, hi]
      rw [hc'eq _ hmem]
      exact hcsample i
    exact hznndef (Work.OddBound.indexTransfer.hasNegDefPlane_of_negativeDirichletIndex
      (I := I) (cov := cov) hmet htor (T := T) hTpos
      (p := p) (c := c') hc'sm hc'geo hc'ne hcsp'
      (by rw [hc'eq 0 ⟨le_rfl, hTpos.le⟩, hc0])
      (by rw [hc'eq T ⟨hTpos.le, le_rfl⟩, hcT])
      (N := N) hN3 (w := z) hsmpl hsd (x := x) hzsrc
      (Work.OddBound.piExtChart_mem_atlas (I := I) x) hC2x hfderiv
      (V := V) (W := W) hVsm hV0 hVT hWsm hW0 hWT hneg)

end

end Work.OddBound
