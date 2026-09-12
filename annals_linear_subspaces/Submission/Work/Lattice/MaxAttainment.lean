import Mathlib
import Submission.Work.Lattice.MaxEuclidBridge
import Submission.Work.Lattice.MixedRankSpectrum
import Submission.Work.Lattice.FiniteSaturatedHulls
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul
import Submission.Work.Lattice.CnormDataBdd

/-!
# Attainment of the intrinsic max-norm data (route 1 for the max-norm flag)

The max-norm analogue of `DataAttainment.exists_subgroup_logCovol_eq_rankData`: the infimum
`maxRankData Λ j` of `log (cnorm (⋀^j v))` over `ℝ`-independent families `v : Fin j → Λ` is
attained by a subgroup of `Λ` (equivalently, by a presentation family of it).

The proof follows the Euclidean scheme, with the *spectrum discreteness* input coming from
`MixedRankSpectrum`:

* `cnorm_smul` — homogeneity of the sup norm;
* `maxCovol_le_log_cnorm_of_span` — for a family `v` of `ℝ`-independent elements of `W` of size
  `subDim W`, the intrinsic max-norm covolume of `W` is at most `log cnorm (⋀v)`
  (the presentation family and `v` differ by an integer matrix with `|det| ≥ 1`);
* `finite_maxCovolSpectrum` — for `0 < j ≤ d` and any bound `B`, only finitely many rank-`j`
  subgroups `W ≤ Λ` have `maxCovol W ≤ B` (they are a subset of the Euclidean
  `mixedRankSpectrumStatement` at `exp (B + A₂)`, via
  `MaxCovol.log_latticeCovol_le_maxCovol_add`);
* **`exists_subgroup_maxCovol_eq_maxRankData`** — attainment, given
  `BddBelow (maxRankDataSet Λ j)` (which holds for the §3 lattice).

Module `Submission.Work.Lattice.MaxAttainment`, namespace `Submission.MaxAttainment`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxAttainment

open Submission.GraysonLattice
open Submission.GraysonData
open Submission.ExteriorCoordinates
open Submission.MaxNorm
open Submission.DiagonalFlow
open Submission.MaxNormFlow
open Submission.MaxEuclidData
open Submission.MaxRankData
open Submission.MaxCovol
open Submission.MaxPhi
open Submission.MaxPhiPolygon
open Submission.MaxEuclidBridge
open Submission.MixedRankSpectrum
open Submission.UniformBddBelow
open Submission.LatticePolygon
open Submission.JoinSubmodularity

variable {d : ℕ}

/-- **Homogeneity of the sup norm**: `cnorm (c • w) = |c| · cnorm w`. -/
lemma cnorm_smul {k : ℕ} (hk : k ≤ d) (c : ℝ) (w : WK d k) :
    cnorm hk (c • w) = |c| * cnorm hk w := by
  have hA : ∀ c : ℝ, ∀ w : WK d k, cnorm hk (c • w) ≤ |c| * cnorm hk w := by
    intro c w
    refine cnorm_le_of_forall hk _ (fun I => ?_)
    rw [Submission.DiagonalFlow.wcoord_smul, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_cnorm hk w I) (abs_nonneg c)
  refine le_antisymm (hA c w) ?_
  rcases eq_or_ne c 0 with hc | hc
  · rw [hc, zero_smul, cnorm_zero]; simp
  · have h1 := hA c⁻¹ (c • w)
    rw [abs_inv] at h1
    have h2 : c⁻¹ • (c • w) = w := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    rw [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul] at h3
    exact h3

/-- **The intrinsic max-norm covolume is at most the `cnorm` of the wedge of any `ℝ`-independent
spanning family.**  (The presentation family and `v` differ by an integer matrix whose determinant
is a nonzero integer, hence `|det| ≥ 1`.) -/
theorem maxCovol_le_log_cnorm_of_span {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {hΛfin : Module.finrank ℤ Λ = d}
    {W : Submodule ℤ (E d)} {hWΛ : W ≤ Λ} (hW0 : W ≠ ⊥)
    {v : Fin (subDim W) → E d} (hvmem : ∀ i, v i ∈ W) (hvli : LinearIndependent ℝ v) :
    maxCovol (d := d) Λ hΛfin W hWΛ ≤
      Real.log (cnorm (subDim_le_ambient W)
        (exteriorPower.ιMulti ℝ (subDim W) v)) := by
  classical
  set b : Fin (subDim W) → E d := presFam (d := d) Λ hΛfin W hWΛ hW0 with hbdef
  have hspanW : W = Submodule.span ℤ (Set.range b) := by
    rw [hbdef]
    exact presFam_span (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := W) (hXΛ := hWΛ) (hX0 := hW0)
  have hbli : LinearIndependent ℝ b := presFam_linearIndependent (d := d) (Λ := Λ)
    (hΛfin := hΛfin) (X := W) (hXΛ := hWΛ) (hX0 := hW0)
  have hbne : exteriorPower.ιMulti ℝ (subDim W) b ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent b hbli
  choose c hc using fun i : Fin (subDim W) =>
    (Submodule.mem_span_range_iff_exists_fun ℤ (v := b)).mp
      (show v i ∈ Submodule.span ℤ (Set.range b) by rw [← hspanW]; exact hvmem i)
  let M : Matrix (Fin (subDim W)) (Fin (subDim W)) ℝ :=
    (Matrix.of (fun r i => c i r)).map (Int.castRingHom ℝ)
  have hcoord : ∀ j : Fin (subDim W), v j = ∑ i, M i j • b i := by
    intro j
    rw [← hc j]
    have h1 : (∑ i, c j i • b i) = ∑ i, ((c j i : ℤ) : ℝ) • b i :=
      Finset.sum_congr rfl (fun i _ => (Int.cast_smul_eq_zsmul ℝ (c j i) (b i)).symm)
    rw [h1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine congrArg (fun x : ℝ => x • b i) ?_
    simp [M, Matrix.map_apply, Matrix.of_apply]
  have hwedge : exteriorPower.ιMulti ℝ (subDim W) v =
      M.det • exteriorPower.ιMulti ℝ (subDim W) b :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul b M v hcoord
  have hvne : exteriorPower.ιMulti ℝ (subDim W) v ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent v hvli
  have hdetne : M.det ≠ 0 := by
    intro h0
    rw [hwedge, h0, zero_smul] at hvne
    exact hvne rfl
  have hdet_eq : M.det = (((Matrix.of (fun r i => c i r)).det : ℤ) : ℝ) := by
    dsimp only [M]
    exact (RingHom.map_det (Int.castRingHom ℝ) (Matrix.of (fun r i => c i r))).symm
  have hdetge : 1 ≤ |M.det| := by
    rw [hdet_eq, ← Int.cast_abs]
    have hz : ((Matrix.of (fun r i => c i r)).det : ℤ) ≠ 0 := by
      intro h0
      exact hdetne (by rw [hdet_eq, h0]; norm_num)
    exact_mod_cast Int.one_le_abs hz
  have hcn : cnorm (subDim_le_ambient W) (exteriorPower.ιMulti ℝ (subDim W) v) =
      |M.det| * cnorm (subDim_le_ambient W) (exteriorPower.ιMulti ℝ (subDim W) b) := by
    rw [hwedge, cnorm_smul]
  have hpos : 0 < cnorm (subDim_le_ambient W) (exteriorPower.ιMulti ℝ (subDim W) b) :=
    cnorm_pos_of_ne_zero _ _ hbne
  have hmax : maxCovol (d := d) Λ hΛfin W hWΛ =
      Real.log (cnorm (subDim_le_ambient W) (exteriorPower.ιMulti ℝ (subDim W) b)) := by
    rw [maxCovol, dif_neg hW0, ← hbdef]
  rw [hmax, hcn, Real.log_mul (by positivity) hpos.ne']
  have hlog : 0 ≤ Real.log (|M.det|) := Real.log_nonneg hdetge
  linarith

/-- **`maxCovol W ≤ B` forces a Euclidean covolume bound.** -/
theorem latticeCovol_le_exp_of_maxCovol_le {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {hΛfin : Module.finrank ℤ Λ = d} {W : Submodule ℤ (E d)} {hWΛ : W ≤ Λ}
    {B : ℝ} (hB : maxCovol (d := d) Λ hΛfin W hWΛ ≤ B) :
    latticeCovol W ≤ Real.exp (B + (1 / 2) * Real.log (Nat.choose d (subDim W))) := by
  have hlog := log_latticeCovol_le_maxCovol_add (d := d) (Λ := Λ) (hΛfin := hΛfin)
    (X := W) (hXΛ := hWΛ)
  have h2 : Real.log (latticeCovol W) ≤ B + (1 / 2) * Real.log (Nat.choose d (subDim W)) := by
    linarith
  calc latticeCovol W ≤ Real.exp (Real.log (latticeCovol W)) := Real.le_exp_log _
    _ ≤ Real.exp (B + (1 / 2) * Real.log (Nat.choose d (subDim W))) := Real.exp_le_exp.mpr h2

/-- **Discreteness of the max-norm spectrum**: only finitely many rank-`j` subgroups `W ≤ Λ`
have `maxCovol W ≤ B`.  (They form a subset of the Euclidean bounded-covolume spectrum at
`exp (B + A₂ d j)`.) -/
theorem finite_maxCovolSpectrum {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ} (hj0 : 0 < j) (hjd : j ≤ d) (B : ℝ) :
    Finite {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle ≤ B} := by
  classical
  haveI : Finite {W : Submodule ℤ (E d) // W ≤ Λ ∧ subDim W = j ∧
      latticeCovol W ≤ Real.exp (B + (1 / 2) * Real.log (Nat.choose d j))} :=
    Submission.FiniteSaturatedHulls.finite_mixedRankSpectrum (d := d) (r := j) Λ hj0 hjd _
  have hcov : ∀ x : {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle ≤ B},
      latticeCovol x.1 ≤ Real.exp (B + (1 / 2) * Real.log (Nat.choose d j)) := by
    intro x
    have h := x.2.choose_spec.2
    have h1 := latticeCovol_le_exp_of_maxCovol_le (d := d) (Λ := Λ) (hΛfin := hΛfin)
      (W := x.1) (hWΛ := x.2.choose) h
    simpa [x.2.choose_spec.1] using h1
  let f : {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle ≤ B} →
      {W : Submodule ℤ (E d) // W ≤ Λ ∧ subDim W = j ∧
        latticeCovol W ≤ Real.exp (B + (1 / 2) * Real.log (Nat.choose d j))} :=
    fun x => ⟨x.1, x.2.choose, x.2.choose_spec.1, hcov x⟩
  refine Finite.of_injective f ?_
  intro a b hab
  have h1 : (f a).1 = (f b).1 := congrArg (fun y => y.1) hab
  exact Subtype.ext h1


/-- `cnorm` is invariant under reindexing an `ιMulti` family along `Fin.cast`. -/
lemma cnorm_iMulti_reindex {n k : ℕ} (h : n = k) (v : Fin k → E d) (hn : n ≤ d) (hk : k ≤ d) :
    cnorm hn (exteriorPower.ιMulti ℝ n (fun i => v (Fin.cast h i))) =
      cnorm hk (exteriorPower.ιMulti ℝ k v) := by
  subst h
  rfl

/-- **A subgroup realising a value below a threshold.**  From any element `r < m` of the
max-norm data set, one gets a rank-`j` subgroup of `Λ` with `maxCovol < m`. -/
lemma exists_maxCovol_lt_of_data_lt {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {hΛfin : Module.finrank ℤ Λ = d} {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    {m : ℝ} (h : ∃ r ∈ maxRankDataSet (d := d) Λ j hjd, r < m) :
    ∃ (W : Submodule ℤ (E d)) (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle < m := by
  classical
  obtain ⟨r, ⟨v, hvmem, hvli, rfl⟩, hrlt⟩ := h
  set W : Submodule ℤ (E d) := Submodule.span ℤ (Set.range v) with hW
  have hWle : W ≤ Λ := Submodule.span_le.mpr (Set.range_subset_iff.mpr hvmem)
  have hdim : subDim W = j := by rw [hW]; exact subDim_span_range_of_linearIndependent v hvli
  have hW0 : W ≠ ⊥ := by
    intro hbot
    rw [hbot] at hdim
    have hz := (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl
    omega
  refine ⟨W, hWle, hdim, ?_⟩
  have hcov := maxCovol_le_log_cnorm_of_span (d := d) (Λ := Λ) (hΛfin := hΛfin) (W := W)
    (hWΛ := hWle) hW0
    (v := fun i : Fin (subDim W) => v (Fin.cast hdim i))
    (fun i => Submodule.subset_span ⟨_, rfl⟩)
    (hvli.comp (Fin.cast hdim) (Fin.cast_injective hdim))
  rw [cnorm_iMulti_reindex hdim v (subDim_le_ambient W) hjd] at hcov
  linarith

/-- **Attainment of the max-norm data.**  Given `BddBelow` of the data (which holds for the §3
lattice), the infimum `maxRankData Λ j` is attained by the presentation family of a subgroup
`W ≤ Λ` of rank `j`, i.e. `maxCovol W = maxRankData Λ j`. -/
theorem exists_subgroup_maxCovol_eq_maxRankData {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    (hBdd : BddBelow (maxRankDataSet (d := d) Λ j hjd)) :
    ∃ (W : Submodule ℤ (E d)) (hWΛ : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWΛ = maxRankData (d := d) Λ j hjd := by
  classical
  set m : ℝ := maxRankData (d := d) Λ j hjd with hm
  have hne := maxRankDataSet_nonempty (d := d) (Λ := Λ) hΛfin hj hjd
  -- finiteness and nonemptiness of the truncated spectrum
  have hfinS : Finite {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle ≤ m + 1} :=
    finite_maxCovolSpectrum (d := d) (Λ := Λ) hΛfin (by omega) hjd (m + 1)
  have hneS : Nonempty {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle ≤ m + 1} := by
    have hlt : ∃ r ∈ maxRankDataSet (d := d) Λ j hjd, r < m + 1 :=
      (csInf_lt_iff hBdd hne).mp (by rw [hm, maxRankData]; linarith)
    obtain ⟨W, hWle, hdim, hcov⟩ := exists_maxCovol_lt_of_data_lt (d := d) (Λ := Λ)
      (hΛfin := hΛfin) (j := j) hj hjd hlt
    exact ⟨⟨W, hWle, hdim, le_of_lt hcov⟩⟩
  haveI : Fintype {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle ≤ m + 1} := Fintype.ofFinite _
  obtain ⟨W₀, -, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
      maxCovol (d := d) Λ hΛfin W hWle ≤ m + 1})
    (fun W => maxCovol (d := d) Λ hΛfin W.1 W.2.choose) Finset.univ_nonempty
  have hW₀0 : W₀.1 ≠ ⊥ := by
    intro hbot
    have h2 := W₀.2.choose_spec.1
    rw [hbot] at h2
    have hz := (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl
    omega
  have hge : m ≤ maxCovol (d := d) Λ hΛfin W₀.1 W₀.2.choose := by
    have hdim₀ : subDim W₀.1 = j := W₀.2.choose_spec.1
    conv_lhs => rw [hm, maxRankData]
    rw [maxCovol, dif_neg hW₀0]
    refine csInf_le hBdd ⟨fun i : Fin j =>
      presFam (d := d) Λ hΛfin W₀.1 W₀.2.choose hW₀0 (Fin.cast hdim₀.symm i), ?_, ?_, ?_⟩
    · intro i
      exact presFam_mem (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := W₀.1) (hXΛ := W₀.2.choose)
        (hX0 := hW₀0) _
    · exact (presFam_linearIndependent (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := W₀.1)
        (hXΛ := W₀.2.choose) (hX0 := hW₀0)).comp (Fin.cast hdim₀.symm)
        (Fin.cast_injective hdim₀.symm)
    · exact (congrArg Real.log (cnorm_iMulti_reindex (d := d) hdim₀.symm
        (presFam (d := d) Λ hΛfin W₀.1 W₀.2.choose hW₀0) hjd (subDim_le_ambient W₀.1))).symm
  have hle : maxCovol (d := d) Λ hΛfin W₀.1 W₀.2.choose ≤ m := by
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    have hε'pos : 0 < min ε 1 := lt_min hε one_pos
    have hε'le : min ε 1 ≤ 1 := min_le_right _ _
    have hlt : ∃ r ∈ maxRankDataSet (d := d) Λ j hjd, r < m + min ε 1 :=
      (csInf_lt_iff hBdd hne).mp (by rw [hm, maxRankData]; linarith)
    obtain ⟨W, hWle, hdim, hcov⟩ :=
      exists_maxCovol_lt_of_data_lt (d := d) (Λ := Λ) (hΛfin := hΛfin) (j := j) hj hjd hlt
    have hmem : (⟨W, hWle, hdim, le_of_lt (lt_of_lt_of_le hcov (by linarith))⟩ :
        {W : Submodule ℤ (E d) // ∃ (hWle : W ≤ Λ), subDim W = j ∧
          maxCovol (d := d) Λ hΛfin W hWle ≤ m + 1}) ∈
        (Finset.univ : Finset _) := Finset.mem_univ _
    have h1 := hmin _ hmem
    linarith [h1, hcov, min_le_left ε 1]
  exact ⟨W₀.1, W₀.2.choose, W₀.2.choose_spec.1, le_antisymm hle hge⟩


/-! ## Discharging the `BddBelow` hypothesis for the §3 lattice -/

/-- **The max-norm data of the flowed §3 lattice is bounded below.**  For `Λ₀ = s(ℤᵈ)`
(`s` a linear isometry) and `Λ = a_t Λ₀` (the image of `Λ₀` under the exponential two-scale
flow), the intrinsic max-norm data `maxRankDataSet Λ j` is bounded below — it is the flow data
`flowMaxDataSet Λ₀ ℓ t j`, whose boundedness is `CnormDataBdd.bddBelow_flowMaxDataSet_imageSpan`. -/
theorem bddBelow_maxRankDataSet_imageSpan_flow {ℓ j : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    (hjd : j ≤ d) (hj1 : 1 ≤ j) (s : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    BddBelow (maxRankDataSet (d := d)
      ((Submission.ImageLattice.imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)).map
        ((FlowDataMax.eFlow (d := d) ℓ t).restrictScalars ℤ)) j hjd) := by
  have h := Submission.CnormDataBdd.bddBelow_flowMaxDataSet_imageSpan (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hjd hj1 s t
  rwa [flowMaxDataSet_eq_maxRankDataSet (d := d) (Λ₀ :=
    Submission.ImageLattice.imageSpan (d := d) (s : RD d ≃ₗ[ℝ] RD d)) ℓ t j hjd] at h


/-! ## Saturation of the attained realiser -/

/-- The hull of `⊥` is `⊥`. -/
lemma hull_bot (Λ : Submodule ℤ (E d)) : hull Λ ⊥ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [hull_mem_iff] at hx
  have h2 : realSpan (⊥ : Submodule ℤ (E d)) = ⊥ := by simp [realSpan]
  rw [h2] at hx
  simpa using hx.2

/-- **The max-norm covolume of the hull is at most that of the subgroup.**  `hull Λ W` contains
`W` with the same real span, so a presentation family of `W` is an integer matrix (of determinant
`≥ 1` in absolute value) applied to a presentation family of the hull; hence the `cnorm` of its
wedge is no smaller, and `maxCovol_le_log_cnorm_of_span` applies. -/
theorem maxCovol_hull_le {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {hΛfin : Module.finrank ℤ Λ = d} {W : Submodule ℤ (E d)} (hWΛ : W ≤ Λ) :
    maxCovol (d := d) Λ hΛfin (hull Λ W) (hull_le_Λ Λ W) ≤
      maxCovol (d := d) Λ hΛfin W hWΛ := by
  classical
  by_cases hW0 : W = ⊥
  · have h1 : maxCovol (d := d) Λ hΛfin (hull Λ W) (hull_le_Λ Λ W) = 0 := by
      rw [maxCovol, dif_pos (by rw [hW0]; exact hull_bot Λ)]
    have h2 : maxCovol (d := d) Λ hΛfin W hWΛ = 0 := by
      rw [maxCovol, dif_pos hW0]
    rw [h1, h2]
  · have hdimH : subDim (hull Λ W) = subDim W := subDim_hull_eq Λ W hWΛ
    have hH0 : hull Λ W ≠ ⊥ := by
      intro h
      have h2 := hdimH
      rw [h] at h2
      have hz := (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl
      have hj0 : 0 < subDim W := Nat.pos_of_ne_zero fun hz' => hW0 ((subDim_eq_zero_iff_bot W).mp hz')
      omega
    have hmem : ∀ i : Fin (subDim (hull Λ W)),
        presFam (d := d) Λ hΛfin W hWΛ hW0 (Fin.cast hdimH i) ∈ hull Λ W := fun i =>
      W_le_hull Λ W hWΛ (presFam_mem_self (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := W)
        (hXΛ := hWΛ) (hX0 := hW0) _)
    have hli : LinearIndependent ℝ (fun i : Fin (subDim (hull Λ W)) =>
        presFam (d := d) Λ hΛfin W hWΛ hW0 (Fin.cast hdimH i)) :=
      (presFam_linearIndependent (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := W) (hXΛ := hWΛ)
        (hX0 := hW0)).comp (Fin.cast hdimH) (Fin.cast_injective hdimH)
    have h1 := maxCovol_le_log_cnorm_of_span (d := d) (Λ := Λ) (hΛfin := hΛfin)
      (W := hull Λ W) (hWΛ := hull_le_Λ Λ W) hH0
      (v := fun i : Fin (subDim (hull Λ W)) =>
        presFam (d := d) Λ hΛfin W hWΛ hW0 (Fin.cast hdimH i)) hmem hli
    rw [cnorm_iMulti_reindex (d := d) hdimH (presFam (d := d) Λ hΛfin W hWΛ hW0)
      (subDim_le_ambient (hull Λ W)) (subDim_le_ambient W)] at h1
    have hmaxW : maxCovol (d := d) Λ hΛfin W hWΛ =
        Real.log (cnorm (subDim_le_ambient W) (exteriorPower.ιMulti ℝ (subDim W)
          (presFam (d := d) Λ hΛfin W hWΛ hW0))) := by
      rw [maxCovol, dif_neg hW0]
    rw [hmaxW]
    exact h1

/-- **Saturated attainment of the max-norm data.**  The hull of an attained realiser is a
*saturated* realiser at the same rank and the same value. -/
theorem exists_saturated_maxCovol_eq_maxRankData {Λ : Submodule ℤ (E d)} [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {j : ℕ} (hj : 1 ≤ j) (hjd : j ≤ d)
    (hBdd : BddBelow (maxRankDataSet (d := d) Λ j hjd)) :
    ∃ (V : Submodule ℤ (E d)) (hVΛ : V ≤ Λ), Saturated Λ V ∧ subDim V = j ∧
      maxCovol (d := d) Λ hΛfin V hVΛ = maxRankData (d := d) Λ j hjd := by
  classical
  obtain ⟨W, hWΛ, hdim, hcov⟩ :=
    exists_subgroup_maxCovol_eq_maxRankData (d := d) (Λ := Λ) hΛfin hj hjd hBdd
  have hdimH : subDim (hull Λ W) = j := by rw [subDim_hull_eq Λ W hWΛ, hdim]
  have hH0 : hull Λ W ≠ ⊥ := by
    intro h
    rw [h] at hdimH
    have hz := (subDim_eq_zero_iff_bot (⊥ : Submodule ℤ (E d))).mpr rfl
    omega
  refine ⟨hull Λ W, hull_le_Λ Λ W, ?_, hdimH, ?_⟩
  · exact (hull_idempotent Λ W hWΛ).symm
  · refine le_antisymm ?_ ?_
    · rw [← hcov]
      exact maxCovol_hull_le (d := d) (Λ := Λ) (hΛfin := hΛfin) (W := W) hWΛ
    · rw [maxRankData]
      refine csInf_le hBdd ⟨fun i : Fin j =>
        presFam (d := d) Λ hΛfin (hull Λ W) (hull_le_Λ Λ W) hH0 (Fin.cast hdimH.symm i), ?_, ?_, ?_⟩
      · intro i
        exact presFam_mem (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := hull Λ W)
          (hXΛ := hull_le_Λ Λ W) (hX0 := hH0) _
      · exact (presFam_linearIndependent (d := d) (Λ := Λ) (hΛfin := hΛfin) (X := hull Λ W)
          (hXΛ := hull_le_Λ Λ W) (hX0 := hH0)).comp (Fin.cast hdimH.symm)
          (Fin.cast_injective hdimH.symm)
      · rw [maxCovol, dif_neg hH0]
        exact (congrArg Real.log (cnorm_iMulti_reindex (d := d) hdimH.symm
          (presFam (d := d) Λ hΛfin (hull Λ W) (hull_le_Λ Λ W) hH0) hjd
          (subDim_le_ambient (hull Λ W)))).symm


end Submission.MaxAttainment

end
