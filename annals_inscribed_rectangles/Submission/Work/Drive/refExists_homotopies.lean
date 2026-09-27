import Mathlib
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.classRowAvoidParallel
import Submission.Work.Drive.exists_clauseHomotopy_linBase
import Submission.Work.Drive.oddClassLift
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.classProjectionBricks
import Submission.Work.Drive.refTripleClause
import Submission.Work.Drive.classRowDesignData
import Submission.Work.Drive.endsHomotopyClauses

namespace Work.Drive

/-- **The sheared linear chart on the real diameter is the permuted chart.**  On the real line the
shear `linShear k` fixes the sphere lift `linVecC` (`linShear_linVecC_ofReal`), so `linBase A k`
agrees there with the unsheared permuted chart `(coordPermCLM (coordPerms k)).trans A`.  This is the
identity that turns the cone-avoidance condition of `exists_trans_avoid_negParallel_cr` (stated for
the unsheared family) into the non-collision condition `hgood` of the `(B)`-lane homotopies
(`exists_diskClassHomotopy_linear_of_neg`), which is stated at the `linBase A k`. -/
lemma linBase_linVecC_ofReal (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (t : ℝ) :
    linBase A k (linVecC (t : ℂ)) = ((coordPermCLM (coordPerms k)).trans A) (linVecC (t : ℂ)) := by
  rw [linBase_apply, linShear_linVecC_ofReal, ContinuousLinearEquiv.trans_apply]

/-- **The (untransported) homotopies of the reference-triple design.**  For an injective Jordan curve
with a plane chart `Q`, two angles `u`, `v`, a linear family `φ` and the level `lam` of the reference
plane, there is a *single* linear family `A` (the cone-avoidance chooser) and three homotopies from
the reference triple `(rotPresentation Q u, rotPresentation Q v, refPlanePres φ lam hlam)` to the
disk models of the sheared linear charts `linBase A k` at the level `c` — seam-invariant, with `C^∞`
chains. -/
theorem refExists_homotopies {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    (u v : ℝ) (φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (c : ℝ) (hc : 0 < c) :
    ∃ (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
      (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Work.Drive.Eucl 3)),
      (∀ y : EuclideanSpace ℝ (Fin 2), H0 0 (0, y) = Work.Drive.planeClassMap (Work.Drive.rotPresentation Q ((u : ℝ) : UnitAddCircle)) y) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), H0 1 (0, y) = Work.Drive.planeClassMap (Work.Drive.rotPresentation Q ((v : ℝ) : UnitAddCircle)) y) ∧
      (∀ y : EuclideanSpace ℝ (Fin 2), H0 2 (0, y) = Work.Drive.planeClassMap (Work.Drive.refPlanePres φ lam hlam) y) ∧
      (∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
        H0 k (1, y) = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Work.Drive.linBase A k) c hc)) y) ∧
      (∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
        Work.Drive.onSeam2 y → H0 k (s, Work.Drive.seamInv2 y) = H0 k (s, y)) ∧
      (∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin 3) => H0 k (x 2, Work.Drive.mk2 (x 0) (x 1)))) := by
  classical
  -- 1. the class lift of the chart and its essentiality on the boundary circle
  obtain ⟨V, hVne, hVsm, hQcls⟩ := exists_classLift_of_isPlaneChart hγne hQ
  have hVneC : ∀ z : ℂ, ‖z‖ = 1 → V z ≠ 0 := fun z _ => hVne z
  have hVcont : ContinuousOn V {z : ℂ | ‖z‖ = 1} := hVsm.continuous.continuousOn
  have hVcls : ∀ z (hz : ‖z‖ = 1),
      Projectivization.mk ℝ (V z) (hVneC z hz) = (cappingSpaceHomeoProj (Q z)).2 :=
    fun z hz => (hQcls z).symm
  obtain ⟨hVpar, hVneg⟩ :=
    exists_neg_parallelism_of_planeChart_of_isPlaneChart hγinj hγne hQ V hVneC hVcont hVcls
  -- 2. the three lifts of the sources of the three homotopies
  let W₀ : ℂ → Eucl 3 := fun z => diagRotL u (V z)
  let W₁ : ℂ → Eucl 3 := fun z => diagRotL v (V z)
  let W₂ : ℂ → Eucl 3 := fun z => φ 2 (linVecC z)
  let W : Fin 3 → ℂ → Eucl 3 := ![W₀, W₁, W₂]
  let w : Fin 3 → ℝ → Eucl 3 := fun k t => W k ((t : ℝ) : ℂ)
  have hW₀ne : ∀ z : ℂ, W₀ z ≠ 0 := fun z h => hVne z ((diagRotL u).map_eq_zero_iff.mp h)
  have hW₁ne : ∀ z : ℂ, W₁ z ≠ 0 := fun z h => hVne z ((diagRotL v).map_eq_zero_iff.mp h)
  have hW₂ne : ∀ z : ℂ, W₂ z ≠ 0 := fun z => phi_linVecC_ne_zero (φ 2) z
  have hWne : ∀ k z, W k z ≠ 0 := by
    intro k z
    fin_cases k
    · simpa [W] using hW₀ne z
    · simpa [W] using hW₁ne z
    · simpa [W] using hW₂ne z
  have hW₀sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W₀ :=
    ((diagRotL u : Eucl 3 →L[ℝ] Eucl 3)).contDiff.comp hVsm
  have hW₁sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W₁ :=
    ((diagRotL v : Eucl 3 →L[ℝ] Eucl 3)).contDiff.comp hVsm
  have hW₂sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W₂ := (φ 2).contDiff.comp linVecC_contDiff
  have hWsm : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W k) := by
    intro k
    fin_cases k
    · simpa [W] using hW₀sm
    · simpa [W] using hW₁sm
    · simpa [W] using hW₂sm
  have hwne : ∀ (k : Fin 3) (t : ℝ), w k t ≠ 0 := fun k t => hWne k ((t : ℝ) : ℂ)
  have hwsm : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w k) := by
    intro k
    exact (hWsm k).comp Complex.ofRealCLM.contDiff
  -- 3. the cone-avoidance chooser
  obtain ⟨A, -, hA⟩ := exists_trans_avoid_negParallel_cr w hwne hwsm 1 one_pos
  -- 4. the non-collision conditions, on the real diameter
  have hgood : ∀ (k : Fin 3) (z : ℂ), ‖z‖ ≤ 1 → z.im = 0 →
      ¬ ∃ lam : ℝ, linBase A k (linVecC z) = lam • W k z ∧ lam < 0 := by
    intro k z hz hzim
    rintro ⟨lam, hlam, hlt⟩
    have hzre : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using hzim)
    have hmem : z.re ∈ Set.Icc (-1 : ℝ) 1 := by
      have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hzim] at h1
      have h2 : z.re ^ 2 ≤ 1 := by nlinarith [norm_nonneg z, hz]
      constructor <;> nlinarith [sq_nonneg z.re]
    refine hA k z.re hmem ⟨lam, hlt, ?_⟩
    rw [hzre] at hlam
    rw [linBase_linVecC_ofReal] at hlam
    exact hlam
  -- 5. the parallelism and the essentiality of the three lifts
  have hpar₀ : ∀ z : ℂ, ‖z‖ = 1 → ∃ cc : ℝ, W₀ (-z) = cc • W₀ z := by
    intro z hz
    obtain ⟨cc, hcc⟩ := hVpar z hz
    exact ⟨cc, by simp only [W₀, hcc, map_smul]⟩
  have hneg₀ : ∃ cc : ℝ, W₀ (-1) = cc • W₀ 1 ∧ cc < 0 := by
    obtain ⟨cc, hcc, hccneg⟩ := hVneg
    exact ⟨cc, by simp only [W₀, hcc, map_smul], hccneg⟩
  have hpar₁ : ∀ z : ℂ, ‖z‖ = 1 → ∃ cc : ℝ, W₁ (-z) = cc • W₁ z := by
    intro z hz
    obtain ⟨cc, hcc⟩ := hVpar z hz
    exact ⟨cc, by simp only [W₁, hcc, map_smul]⟩
  have hneg₁ : ∃ cc : ℝ, W₁ (-1) = cc • W₁ 1 ∧ cc < 0 := by
    obtain ⟨cc, hcc, hccneg⟩ := hVneg
    exact ⟨cc, by simp only [W₁, hcc, map_smul], hccneg⟩
  have hpar₂ : ∀ z : ℂ, ‖z‖ = 1 → ∃ cc : ℝ, W₂ (-z) = cc • W₂ z := by
    intro z hz
    exact ⟨-1, by simp only [W₂, linVecC_neg hz, map_neg, neg_one_smul]⟩
  have hneg₂ : ∃ cc : ℝ, W₂ (-1) = cc • W₂ 1 ∧ cc < 0 := by
    refine ⟨-1, ?_, by norm_num⟩
    simp only [W₂]
    rw [linVecC_neg (by norm_num : ‖(1 : ℂ)‖ = 1), map_neg, neg_one_smul]
  -- 6. the class lifts of the three sources
  have hcls₀ : IsClassLift (fun z : ℂ => rotCapping ((u : ℝ) : UnitAddCircle) (Q z)) W₀ hW₀ne :=
    (isClassLift_rotCapping hVne hQcls u).choose_spec
  have hcls₁ : IsClassLift (fun z : ℂ => rotCapping ((v : ℝ) : UnitAddCircle) (Q z)) W₁ hW₁ne :=
    (isClassLift_rotCapping hVne hQcls v).choose_spec
  have hcls₂ : IsClassLift (linPlaneChart (φ 2) lam hlam) W₂ hW₂ne := by
    intro z
    rw [cappingSpaceHomeoProj_linPlaneChart]
  -- 7. the three homotopies
  obtain ⟨_, H₀, hH₀0, hH₀1, hH₀seam, -, hH₀sm⟩ :=
    exists_diskClassHomotopy_linear_of_neg
      (fun z : ℂ => rotCapping ((u : ℝ) : UnitAddCircle) (Q z)) W₀ hW₀ne hW₀sm hcls₀ hpar₀
      (z₀ := (1 : ℂ)) (by norm_num) hneg₀ (linBase A 0) c hc (fun z : ℂ => z.im)
      Complex.imCLM.contDiff (fun z _ => by simp) (hgood 0)
  obtain ⟨_, H₁, hH₁0, hH₁1, hH₁seam, -, hH₁sm⟩ :=
    exists_diskClassHomotopy_linear_of_neg
      (fun z : ℂ => rotCapping ((v : ℝ) : UnitAddCircle) (Q z)) W₁ hW₁ne hW₁sm hcls₁ hpar₁
      (z₀ := (1 : ℂ)) (by norm_num) hneg₁ (linBase A 1) c hc (fun z : ℂ => z.im)
      Complex.imCLM.contDiff (fun z _ => by simp) (hgood 1)
  obtain ⟨_, H₂, hH₂0, hH₂1, hH₂seam, -, hH₂sm⟩ :=
    exists_diskClassHomotopy_linear_of_neg
      (linPlaneChart (φ 2) lam hlam) W₂ hW₂ne hW₂sm hcls₂ hpar₂
      (z₀ := (1 : ℂ)) (by norm_num) hneg₂ (linBase A 2) c hc (fun z : ℂ => z.im)
      Complex.imCLM.contDiff (fun z _ => by simp) (hgood 2)
  -- 8. the assembly
  refine ⟨A, ![H₀, H₁, H₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact hH₀0 y
  · intro y
    exact hH₁0 y
  · intro y
    exact hH₂0 y
  · intro k y
    fin_cases k
    · exact hH₀1 y
    · exact hH₁1 y
    · exact hH₂1 y
  · intro k s y hy
    fin_cases k
    · exact hH₀seam s y hy
    · exact hH₁seam s y hy
    · exact hH₂seam s y hy
  · intro k
    fin_cases k
    · exact hH₀sm
    · exact hH₁sm
    · exact hH₂sm

end Work.Drive
