import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.exists_section_box
import Submission.Work.Cusp.coreLayer_subset_range_coreCoordM

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Finitely many core charts cover the core layer of `M̂`

`Work.Cusp.coreLayer_subset_range_coreCoordM` shows that *every* point of the core layer
(`‖p‖∞ < 1/12`) of a filling piece lies in the range of the core coordinate inclusion
`Work.Cusp.coreCoordM a v tor W` for a suitable *local section* `W` of the quotient
`E2 → (ℝ/ℤ)²` in the `w`-coordinates.  The same chart is an open embedding, so this gives an open
cover of the (compact) core layer by open sets of `M̂`.

This file makes the cover **finite**, which is what the assembly of `M̂` needs: the core charts that
occur in the Atlas belong to a finite family.  The mechanism is the usual one: the local sections
`W` can be taken to be *balls of a fixed radius* `secR v` in the `w`-coordinates.  Indeed, for a
ball `W = ball c ρ` the section condition `wOf v y' ∈ W → wOf v y'' ∈ W → [y'] = [y''] → y' = y''`
holds as soon as `ρ` is smaller than half the mesh of the image lattice `wOf v (ℤ²)`; the operator
norm bound `invBd v` of the inverse `invYLin v` of `wOf v` provides such a radius:
`secR v = 1 / (2 (invBd v + 1))`.

With `W` of fixed radius anchored at an arbitrary centre, the cover becomes the statement that
finitely many `secR v`-balls cover the compact set `wOf v '' [-1,1]²` (the image of a compact
fundamental domain of `E2 ↠ (ℝ/ℤ)²`), which is immediate from compactness.
-/

namespace Work.RTOwed

noncomputable section

open Set Topology Function
open scoped RealInnerProductSpace

/-- `√((r cos θ)² + (r sin θ)²) = r` for `r ≥ 0`: the radial coordinate of the Cartesian core
coordinates `(r cos θ, r sin θ)`. -/
private lemma core_sqrt_sq_cos_sin {r θ : ℝ} (hr : 0 ≤ r) :
    Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    have hs := Real.sin_sq_add_cos_sq θ
    nlinarith [hs]
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

/-! ### A uniform radius of the local sections

`Work.Cusp.invYLin v` is the (continuous) inverse of the linear isomorphism `wOf v`, hence has an
operator norm bound `invBd v > 0`.  Any ball of radius `< 1 / (2 invBd v)` is then a local section
of `wOf v`. -/

lemma exists_invYLin_bound (v : Work.Space.Cusp) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Work.Cusp.E2, ‖Work.Cusp.invYLin v x‖ ≤ C * ‖x‖ :=
  SemilinearMapClass.bound_of_continuous _
    (LinearMap.continuous_of_finiteDimensional _)

/-- The operator norm bound of `Work.Cusp.invYLin v`. -/
noncomputable def invBd (v : Work.Space.Cusp) : ℝ :=
  Classical.choose (exists_invYLin_bound v)

lemma invBd_pos (v : Work.Space.Cusp) : 0 < invBd v :=
  (Classical.choose_spec (exists_invYLin_bound v)).1

lemma norm_invYLin_le (v : Work.Space.Cusp) (x : Work.Cusp.E2) :
    ‖Work.Cusp.invYLin v x‖ ≤ invBd v * ‖x‖ :=
  (Classical.choose_spec (exists_invYLin_bound v)).2 x

/-- A uniform radius of the local sections of `wOf v`: a ball of this radius satisfies the section
condition of the core charts. -/
noncomputable def secR (v : Work.Space.Cusp) : ℝ := 1 / (2 * (invBd v + 1))

lemma secR_pos (v : Work.Space.Cusp) : 0 < secR v := by
  have h : 0 < invBd v + 1 := by linarith [invBd_pos v]
  simp only [secR]
  positivity

lemma invBd_mul_two_secR_lt_one (v : Work.Space.Cusp) : invBd v * (2 * secR v) < 1 := by
  have h : 0 < invBd v + 1 := by linarith [invBd_pos v]
  have h2 : 2 * secR v = (invBd v + 1)⁻¹ := by
    simp only [secR]
    field_simp
  rw [h2, ← div_eq_mul_inv, div_lt_one h]
  linarith

/-- **A ball of radius `secR v` is a local section of `wOf v`.**  Two points `y'`, `y''` whose
`wOf v`-images lie in the same `secR v`-ball and which agree in `(ℝ/ℤ)²` are equal. -/
lemma ball_section (v : Work.Space.Cusp) (c : Work.Cusp.E2) :
    ∀ y' y'' : Work.Cusp.E2,
      Work.Cusp.wOf v y' ∈ Metric.ball c (secR v) →
      Work.Cusp.wOf v y'' ∈ Metric.ball c (secR v) →
      (∀ i, ((y' i : ℝ) : AddCircle (1 : ℝ)) = ((y'' i : ℝ) : AddCircle (1 : ℝ))) →
      y' = y'' := by
  intro y' y'' hy' hy'' hmod
  have hCpos : 0 < invBd v := invBd_pos v
  rw [Metric.mem_ball, dist_eq_norm] at hy' hy''
  -- the two `w`-values are close to each other
  have htri : ‖Work.Cusp.wOf v y' - Work.Cusp.wOf v y''‖ < 2 * secR v := by
    have hsplit : (Work.Cusp.wOf v y' - c) + (c - Work.Cusp.wOf v y'')
        = Work.Cusp.wOf v y' - Work.Cusp.wOf v y'' := by abel
    have ht : ‖Work.Cusp.wOf v y' - Work.Cusp.wOf v y''‖
        ≤ ‖Work.Cusp.wOf v y' - c‖ + ‖c - Work.Cusp.wOf v y''‖ := by
      rw [← hsplit]; exact norm_add_le _ _
    rw [norm_sub_rev c (Work.Cusp.wOf v y'')] at ht
    have h2 : ‖Work.Cusp.wOf v y' - c‖ + ‖Work.Cusp.wOf v y'' - c‖ < 2 * secR v := by
      rw [show 2 * secR v = secR v + secR v from by ring]
      exact add_lt_add hy' hy''
    linarith
  have h1 : Work.Cusp.invYLin v (Work.Cusp.wOf v y') = y' := Work.Cusp.invY_wOf v y'
  have h2 : Work.Cusp.invYLin v (Work.Cusp.wOf v y'') = y'' := Work.Cusp.invY_wOf v y''
  have hkey : y' - y'' = Work.Cusp.invYLin v (Work.Cusp.wOf v y' - Work.Cusp.wOf v y'') := by
    rw [map_sub, h1, h2]
  have hnorm : ‖y' - y''‖ < 1 := by
    rw [hkey]
    have hb : invBd v * ‖Work.Cusp.wOf v y' - Work.Cusp.wOf v y''‖
        < invBd v * (2 * secR v) := mul_lt_mul_of_pos_left htri hCpos
    have hle := norm_invYLin_le v (Work.Cusp.wOf v y' - Work.Cusp.wOf v y'')
    linarith [invBd_mul_two_secR_lt_one v]
  -- coordinate-wise: an integer vector of norm `< 1` is zero
  ext i
  have hlt : |y' i - y'' i| < 1 := by
    simpa using lt_of_le_of_lt (PiLp.norm_apply_le (y' - y'') i) hnorm
  obtain ⟨n, hn⟩ := Work.Cusp.sub_eq_intCast_of_addCircle_eq (hmod i)
  have hn0 : n = 0 := by
    have h3 : (n : ℝ) < 1 := by rw [← hn]; exact (abs_lt.mp hlt).2
    have h4 : -(1 : ℝ) < (n : ℝ) := by rw [← hn]; exact (abs_lt.mp hlt).1
    have h5 : n < 1 := by exact_mod_cast h3
    have h6 : -1 < n := by exact_mod_cast h4
    omega
  have hzero : y' i - y'' i = 0 := by rw [hn, hn0]; norm_num
  exact sub_eq_zero.mp hzero

/-! ### Continuity of `wOf` -/

lemma continuous_wOf (v : Work.Space.Cusp) : Continuous (Work.Cusp.wOf v) := by
  rw [← (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).comp_continuous_iff]
  rw [continuous_pi_iff]
  intro i
  have hc := Work.Cusp.continuous_cuspY v
  fin_cases i <;> exact Continuous.inner hc continuous_const

/-! ### Finitely many `secR v`-balls cover the image of the fundamental square -/

lemma sq_image_wOf_cover (v : Work.Space.Cusp) :
    ∃ F : Finset Work.Cusp.E2, ∀ y : Work.Cusp.E2, y ∈ Work.Space.Sq →
      ∃ c ∈ F, Work.Cusp.wOf v y ∈ Metric.ball c (secR v) := by
  have hK : IsCompact (Work.Cusp.wOf v '' Work.Space.Sq) :=
    Work.Space.isCompact_sq.image (continuous_wOf v)
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun c : Work.Cusp.E2 => Metric.ball c (secR v))
    (fun _ => Metric.isOpen_ball) (by
      intro z hz
      obtain ⟨y, -, rfl⟩ := hz
      exact Set.mem_iUnion.mpr ⟨_, by rw [Metric.mem_ball, dist_self]; exact secR_pos v⟩)
  refine ⟨F, fun y hy => ?_⟩
  have hz := hF ⟨y, hy, rfl⟩
  rw [Set.mem_iUnion₂] at hz
  obtain ⟨c, hcF, hcy⟩ := hz
  exact ⟨c, hcF, hcy⟩

/-! ### Lifts in the fundamental square -/

/-- Every point of the standard torus `(ℝ/ℤ)²` has a lift in the fundamental square `[-1,1]²`. -/
lemma exists_lift_Sq (t : Fin 2 → AddCircle (1 : ℝ)) :
    ∃ y : Work.Cusp.E2, y ∈ Work.Space.Sq ∧
      ∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = t i := by
  have h : ∀ i : Fin 2, ∃ s : ℝ, (s : AddCircle (1 : ℝ)) = t i :=
    fun i => QuotientAddGroup.mk'_surjective _ _
  choose s hs using h
  refine ⟨!₂[Int.fract (s 0), Int.fract (s 1)], ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show |Int.fract (s 0)| ≤ 1
      rw [abs_of_nonneg (Int.fract_nonneg (s 0))]; linarith [Int.fract_lt_one (s 0)]
    · show |Int.fract (s 1)| ≤ 1
      rw [abs_of_nonneg (Int.fract_nonneg (s 1))]; linarith [Int.fract_lt_one (s 1)]
  · intro i
    fin_cases i <;> simpa using (AddCircle.coe_fract (s _)).trans (hs _)

/-! ### The core chart with a `secR v`-ball covers the core layer -/

/-- **A point of the core layer lies in the range of the core chart of any `secR v`-ball that
contains a lift of its torus coordinate.**  This is the computation of
`Work.Cusp.coreLayer_subset_range_coreCoordM`, with the local section `W` replaced by the ball of
radius `secR v` around an arbitrary centre. -/
lemma mem_range_coreCoordM_ball (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (c : Work.Cusp.E2)
    (p : Work.Space.SquarePt) (y0 : a.Torus v) (y : Work.Cusp.E2)
    (hy : ∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = tor y0 i)
    (hyc : Work.Cusp.wOf v y ∈ Metric.ball c (secR v))
    (hp : Work.Cusp.nrm (p : Work.Cusp.E2) < 1 / 12) :
    a.incW v (p, y0) ∈ Set.range (Work.Cusp.coreCoordM a v tor (Metric.ball c (secR v))) := by
  set W : Set Work.Cusp.E2 := Metric.ball c (secR v) with hWdef
  have hycW : Work.Cusp.wOf v y ∈ W := hyc
  -- the Cartesian core coordinates of `(p, y)`
  set qp : Work.Cusp.E4 := Work.Cusp.ThetaCore v (p : Work.Cusp.E2) y with hqpdef
  have hIC : Work.Cusp.cuspInvCore v qp = ((p : Work.Cusp.E2), y) := by
    rw [hqpdef]; exact Work.Cusp.cuspInvCore_ThetaCore v (p : Work.Cusp.E2) y
  have hq0 : qp 0 = Work.Cusp.radial v (p : Work.Cusp.E2) y
      * Real.cos (Work.Cusp.thetaAng v (p : Work.Cusp.E2) y) := by
    rw [hqpdef]; simp [Work.Cusp.ThetaCore]
  have hq1 : qp 1 = Work.Cusp.radial v (p : Work.Cusp.E2) y
      * Real.sin (Work.Cusp.thetaAng v (p : Work.Cusp.E2) y) := by
    rw [hqpdef]; simp [Work.Cusp.ThetaCore]
  have hq23 : (!₂[qp 2, qp 3] : Work.Cusp.E2) = Work.Cusp.wOf v y := by
    rw [hqpdef]; exact Work.Cusp.CoreChartM.ccm_thetaCore_coord23 v (p : Work.Cusp.E2) y
  have hp_le : Work.Cusp.nrm (p : Work.Cusp.E2) ≤ 1 / 2 := by
    linarith [Work.Cusp.nrm_nonneg (p : Work.Cusp.E2)]
  have hrad : Work.Cusp.radial v (p : Work.Cusp.E2) y = 6 * Work.Cusp.nrm (p : Work.Cusp.E2) := by
    rw [Work.Cusp.radial_eq_inner v (p : Work.Cusp.E2) y hp_le]; norm_num [Work.Cusp.rJ]
  have hrnn : 0 ≤ Work.Cusp.radial v (p : Work.Cusp.E2) y := by
    rw [hrad]; linarith [Work.Cusp.nrm_nonneg (p : Work.Cusp.E2)]
  have hq_sqrt : Real.sqrt (qp 0 ^ 2 + qp 1 ^ 2) < 1 / 2 := by
    rw [hq0, hq1, core_sqrt_sq_cos_sin hrnn, hrad]
    linarith
  have hq_w : (!₂[qp 2, qp 3] : Work.Cusp.E2) ∈ W := by rw [hq23]; exact hycW
  have hqmem : qp ∈ Work.Cusp.coreBoxSect W := ⟨hq_sqrt, hq_w⟩
  refine ⟨⟨qp, hqmem⟩, ?_⟩
  have htor : tor.symm (fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ))) = y0 := by
    rw [show (fun i : Fin 2 => ((y i : ℝ) : AddCircle (1 : ℝ))) = tor y0 from funext hy,
      Homeomorph.symm_apply_apply]
  rw [Work.Cusp.CoreChartM.ccm_coreCoordM_eq_comp]
  have hgoal : Work.Cusp.CoreChartM.ccmFillProj a v tor
      (Work.Cusp.CoreChartM.ccmCoreInv v W ⟨qp, hqmem⟩) = (p, y0) := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : Work.Cusp.E2 × Work.Cusp.E2 => z.1) hIC
    · show tor.symm (fun i => (((Work.Cusp.cuspInvCore v qp).2 i : ℝ) : AddCircle (1 : ℝ))) = y0
      rw [congrArg (fun z : Work.Cusp.E2 × Work.Cusp.E2 => z.2) hIC]
      exact htor
  rw [show (a.incW v ∘ Work.Cusp.CoreChartM.ccmFillProj a v tor
        ∘ Work.Cusp.CoreChartM.ccmCoreInv v W) ⟨qp, hqmem⟩
      = a.incW v (Work.Cusp.CoreChartM.ccmFillProj a v tor
          (Work.Cusp.CoreChartM.ccmCoreInv v W ⟨qp, hqmem⟩)) from rfl, hgoal]

/-! ### The finite cover of the core layer -/

theorem core_cover_fin (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) :
    ∃ (N : ℕ) (par : Fin N → Σ v : Work.Space.Cusp, Set Work.Cusp.E2),
      (∀ i, IsOpen (par i).2) ∧
      (∀ i, ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf (par i).1 y ∈ (par i).2 → Work.Cusp.wOf (par i).1 y' ∈ (par i).2 →
        (∀ j : Fin 2, ((y j : ℝ) : AddCircle (1 : ℝ)) = ((y' j : ℝ) : AddCircle (1 : ℝ))) → y = y') ∧
      ∀ (v : Work.Space.Cusp) (q : Work.Space.SquarePt × a.Torus v),
        Work.Cusp.nrm (q.1 : Work.Cusp.E2) < 1/12 →
        ∃ i, (par i).1 = v ∧ a.incW v q ∈ Set.range (Work.Cusp.coreCoordM a v (tor v) (par i).2) := by
  classical
  choose F hF using fun v => sq_image_wOf_cover v
  let ι := Σ v : Work.Space.Cusp, {c : Work.Cusp.E2 // c ∈ F v}
  have : Fintype ι := inferInstance
  let par : Fin (Fintype.card ι) → Σ v : Work.Space.Cusp, Set Work.Cusp.E2 :=
    fun i => let x := (Fintype.equivFin ι).symm i; ⟨x.1, Metric.ball x.2.1 (secR x.1)⟩
  refine ⟨Fintype.card ι, par, ?_, ?_, ?_⟩
  · intro i
    exact Metric.isOpen_ball
  · intro i y y' h1 h2 hmod
    exact ball_section ((Fintype.equivFin ι).symm i).1
      ((Fintype.equivFin ι).symm i).2.1 y y' h1 h2 hmod
  · intro v q hq
    obtain ⟨y, hySq, hy⟩ := exists_lift_Sq (tor v q.2)
    obtain ⟨c, hcF, hcy⟩ := hF v y hySq
    let x : ι := ⟨v, ⟨c, hcF⟩⟩
    refine ⟨Fintype.equivFin ι x, ?_, ?_⟩
    · show ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)).1 = v
      rw [Equiv.symm_apply_apply]
    · have hpar2 : (par (Fintype.equivFin ι x)).2 = Metric.ball c (secR v) := by
        show Metric.ball ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)).2.1
            (secR ((Fintype.equivFin ι).symm (Fintype.equivFin ι x)).1) = Metric.ball c (secR v)
        rw [Equiv.symm_apply_apply]
      rw [hpar2]
      exact mem_range_coreCoordM_ball a v (tor v) c q.1 q.2 y hy hcy hq

end

end Work.RTOwed
