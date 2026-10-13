/-
  WilCrux — N4b (REVISED): the slice derivative at the sheet, uniformly.

  For a definable family `G` with `C^1` slices on a ball and jointly `C^1` off the sheet, there is
  an open `Q1 ⊆ Q` with `Q ⊆ closure Q1` such that on `Q1` the slice derivative is *uniformly*
  close to its value at the sheet (`fderiv ℝ (G w) 0`), and `w ↦ fderiv ℝ (G w) 0` is
  continuous.

  ## Structure of the argument

  The first conjunct is a Baire ("generic uniformity") statement.  Write `D_j(w,z)` for the
  `z_j`-partial of `famFun G` at `(w,z)`, taken on its `C¹`-locus `c1Loc` (where it is the graph
  `Work.WilG4b.derivGraph`, hence `Ω`-definable by `SharpDeriv`).

  * `goodSet G j ε` (`Work.WilCrux.SliceCauchyDefs`) is the open set of parameters `w` at which
    `D_j(·,·)` obeys the uniform Cauchy property at level `ε` in a whole neighbourhood of `w`;
    its complement `failSet G j ε` is closed.
  * For fixed `ε` the sets `sliceCauchySet G j k ε` (with the *uniform* radius threshold
    `1/(k+1)`) are `Ω`-definable with bounds independent of `k` and `ε`
    (`Work.WilCrux.sliceCauchy_mem`), they cover `Q` (`Work.WilCrux.sliceCauchy_cover`), and
    their interiors lie in `goodSet` (`interior_sliceCauchySet_subset_goodSet`).  Feeding the
    cover into Baire (`Work.WilCrux.BaireDefinableCover`) gives
    `interior (failSet G j ε) ∩ Q = ∅`.
  * Taking the level `ε` as a *coordinate* makes the union over the levels an `Ω`-set
    (`Work.WilCrux.failSet_mem`); its projection
    `Fail := ⋃_j projLast {u | 0 < u (last a) ∧ Fin.init u ∈ failSet G j (u (last a))}`
    is `Ω`-definable, and Baire plus the previous point give `interior Fail ∩ Q = ∅`.
  * A sharp cell decomposition (`Work.WilCrux.exists_closed_nowhereDense_cover`, from `SharpCD`)
    then produces a closed set `N` with empty interior and `Fail ∩ Q ⊆ N`, and `Q1 := Q ∖ N`
    is the open set we want: it is dense in `Q`, and on it the partials obey the uniform Cauchy
    property at every level, which (via `famFun_dDir_append` and the `C¹`-ness of the slices at
    the sheet) gives the joint estimate.

  The second conjunct follows from the first by comparing `fderiv ℝ (G w) 0 (Pi.single j 1)` with
  the off-sheet partial `fderiv ℝ (G w) z₀ (Pi.single j 1)` for a fixed small `z₀ ≠ 0`, which is
  continuous in `w` because `famFun G` is `C¹` at `(w₀, z₀)`
  (`Work.WilCrux.continuousAt_slice_fderiv_offSheet`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4b.ESet_mem
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilCrux.SliceCauchyDefs
import Submission.Work.WilCrux.fibreFderivFamFun
import Submission.Work.WilCrux.BaireDefinableCover
import Submission.Work.WilCrux.sliceCauchy_mem
import Submission.Work.WilCrux.sliceCauchy_cover
import Submission.Work.WilCrux.continuousAt_slice_fderiv_offSheet
import Submission.Work.WilCrux.failSet_mem

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-- The fibre direction `Pi.single (Fin.natAdd a j) 1` of `ℝ^{a+b}` is `Fin.append 0 v` for
`v = Pi.single j 1`. -/
theorem append_zero_single {a b : ℕ} (j : Fin b) :
    (Fin.append (0 : Fin a → ℝ) (Pi.single j (1 : ℝ)) : Fin (a + b) → ℝ)
      = Pi.single (Fin.natAdd a j) 1 := by
  funext k
  induction k using Fin.addCases with
  | left i =>
      have hne : (Fin.castAdd b i) ≠ (Fin.natAdd a j) := by
        intro h
        have h2 := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
        omega
      rw [Fin.append_left, Pi.single_eq_of_ne hne]
      rfl
  | right i =>
      rw [Fin.append_right]
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same, Pi.single_eq_same]
      · have hne : (Fin.natAdd a i) ≠ (Fin.natAdd a j) := by
          intro hh
          refine h (Fin.ext ?_)
          have h2 := congrArg Fin.val hh
          simp only [Fin.val_natAdd] at h2
          omega
        rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne hne]

/-- The `z_j`-partial of the joint function `famFun G` at `(w, z)` is the `j`-th partial of the
slice `G w` at `z`. -/
theorem famFun_dDir_append {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z : Fin b → ℝ) (j : Fin b)
    (h : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w z)
      = fderiv ℝ (G w) z (Pi.single j 1) := by
  rw [Work.WilG4b.dDir, ← append_zero_single j]
  exact fibreFderivFamFun G w z (Pi.single j 1) h

/-- The operator norm of a linear functional on `ℝ^b` is bounded by the sum of the absolute values
of its values on the standard basis vectors. -/
theorem norm_le_sum_single {b : ℕ} (L : (Fin b → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ j : Fin b, |L (Pi.single j 1)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _)
    fun x => ?_
  have hx : x = ∑ j : Fin b, x j • Pi.single j (1 : ℝ) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hLx : L x = ∑ j : Fin b, x j * L (Pi.single j 1) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl
  calc ‖L x‖ = |L x| := by rw [Real.norm_eq_abs]
    _ = |∑ j : Fin b, x j * L (Pi.single j 1)| := by rw [hLx]
    _ ≤ ∑ j : Fin b, |x j * L (Pi.single j 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin b, |x j| * |L (Pi.single j 1)| := by simp [abs_mul]
    _ ≤ ∑ j : Fin b, ‖x‖ * |L (Pi.single j 1)| := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j)
          (abs_nonneg _)
    _ = ‖x‖ * ∑ j : Fin b, |L (Pi.single j 1)| := by rw [Finset.mul_sum]
    _ = (∑ j : Fin b, |L (Pi.single j 1)|) * ‖x‖ := by rw [mul_comm]

/-- `goodSet` is monotone in the level `ε`. -/
theorem goodSet_mono {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b)
    {ε ε' : ℝ} (h : ε ≤ ε') : goodSet G j ε ⊆ goodSet G j ε' := by
  rintro w ⟨η, hη, hw⟩
  exact ⟨η, hη, fun w' z z' hd hz hzlt hz' hz'lt => by
    obtain ⟨h1, h2, h3⟩ := hw w' z z' hd hz hzlt hz' hz'lt
    exact ⟨h1, h2, lt_of_lt_of_le h3 h⟩⟩

/-- `goodSet` is open. -/
theorem isOpen_goodSet {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (ε : ℝ) :
    IsOpen (goodSet G j ε) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨η, hη, hgood⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds w (show (0:ℝ) < η/2 by linarith)) ?_
  intro w₁ hw₁
  rw [Metric.mem_ball] at hw₁
  refine ⟨η / 2, by linarith, fun w' z z' hd hz hzlt hz' hz'lt => ?_⟩
  have htri : dist w' w ≤ dist w' w₁ + dist w₁ w := dist_triangle _ _ _
  exact hgood w' z z' (by linarith) hz (by linarith) hz' (by linarith)

/-- `failSet` is closed. -/
theorem isClosed_failSet {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (ε : ℝ) :
    IsClosed (failSet G j ε) :=
  (isOpen_goodSet G j ε).isClosed_compl

/-- The interior of the uniform-Cauchy set is contained in the good set. -/
theorem interior_sliceCauchySet_subset_goodSet {a b : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (k : ℕ) (ε : ℝ) :
    interior (sliceCauchySet G j k ε) ⊆ goodSet G j ε := by
  intro w hw
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hw)
  refine ⟨min δ (1 / ((k : ℝ) + 1)), lt_min hδ (by positivity), ?_⟩
  intro w' z z' hd hz hzlt hz' hz'lt
  have hw'S : w' ∈ sliceCauchySet G j k ε :=
    hδsub (Metric.mem_ball.mpr (lt_of_lt_of_le hd (min_le_left _ _)))
  obtain ⟨ηw, hηw, -, hprop⟩ := hw'S
  exact hprop z z' hz (lt_trans hzlt (lt_of_le_of_lt (min_le_right _ _) hηw)) hz'
    (lt_trans hz'lt (lt_of_le_of_lt (min_le_right _ _) hηw))

end Work.WilCrux

namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-- The interior of `failSet` at a positive level meets `Q` in the empty set: `Q` is covered by
the uniform-Cauchy sets `sliceCauchySet G j k ε`, whose interiors sit inside the good set. -/
theorem interior_failSet_inter_Q_empty (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (hder : S.SharpDeriv) {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q : Set (Fin a → ℝ)) (hQ : IsOpen Q) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (j : Fin b) (ε : ℝ) (hε : 0 < ε) :
    interior (failSet G j ε) ∩ Q = ∅ := by
  obtain ⟨A, q, hmemS⟩ := sliceCauchy_mem S hder G hG
  rw [Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hwint, hwQ⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hwint)
  obtain ⟨δQ, hδQ, hδQsub⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hwQ)
  set ρ : ℝ := min δ δQ with hρdef
  have hρpos : 0 < ρ := lt_min hδ hδQ
  have hρsub : Metric.ball w ρ ⊆ failSet G j ε ∩ Q := by
    intro x hx
    rw [Metric.mem_ball] at hx
    exact ⟨hδsub (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_left _ _))),
      hδQsub (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _)))⟩
  obtain ⟨k, hk⟩ := BaireDefinableCover S hcd (fun k : ℕ => sliceCauchySet G j k ε)
    (fun k => ⟨A, q.eval D, hmemS j k ε⟩) (Metric.ball w ρ) Metric.isOpen_ball
    ⟨w, Metric.mem_ball_self hρpos⟩
    (fun x hx => sliceCauchy_cover G Q r0 hr0 hsl hoff j hε (hρsub hx).2)
  obtain ⟨x, hxint, hxball⟩ := hk
  exact (hρsub hxball).1 (interior_sliceCauchySet_subset_goodSet G j k ε hxint)

theorem SliceDerivJointContV2 (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q : Set (Fin a → ℝ)) (hQ : IsOpen Q) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z)) :
    ∃ Q1 : Set (Fin a → ℝ), IsOpen Q1 ∧ Q1 ⊆ Q ∧ Q ⊆ closure Q1 ∧
      (∀ w₀ ∈ Q1, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
        dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε) ∧
      (∀ w₀ ∈ Q1, ∀ j : Fin b, Filter.Tendsto
        (fun w => fderiv ℝ (G w) 0 (Pi.single j 1)) (nhds w₀)
        (nhds (fderiv ℝ (G w₀) 0 (Pi.single j 1)))) := by
  classical
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    refine ⟨Q, hQ, fun x hx => hx, subset_closure, ?_, ?_⟩
    · intro w₀ hw₀ ε hε
      exact ⟨1, one_pos, fun w z _ hz => absurd (funext fun i => i.elim0) hz⟩
    · intro w₀ hw₀ j
      exact j.elim0
  obtain ⟨A, q, hmemS⟩ := sliceCauchy_mem S hder G hG
  obtain ⟨A', q', hmemF⟩ := failSet_mem S hder G hG
  have hbm : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  -- the total failure set
  set Fail : Set (Fin a → ℝ) :=
    ⋃ j : Fin b, projLast {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a) ∧
      Fin.init u ∈ failSet G j (u (Fin.last a))} with hFaildef
  have hFailmem : Fail ∈ S.Ω (A' + 1) ((Polynomial.C b * q').eval D) a := by
    rw [hFaildef]
    refine Work.WilG1.Omega.union_mem (S := S) (D := D) _ (fun j => ?_)
    exact Work.WilG1.Omega.mono (S.proj (hmemF j)) le_rfl le_rfl
  have hFaileq : Fail = ⋃ j : Fin b, ⋃ m : ℕ, failSet G j (1 / ((m : ℝ) + 1)) := by
    rw [hFaildef]
    ext w
    simp only [Set.mem_iUnion, projLast, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    constructor
    · rintro ⟨j, ε, hε, hw⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      exact ⟨j, m, fun hc => hw (goodSet_mono G j (le_of_lt hm) hc)⟩
    · rintro ⟨j, m, hw⟩
      exact ⟨j, 1 / ((m : ℝ) + 1), by positivity, hw⟩
  -- thinness of `Fail` relative to `Q`
  have hFailthin : interior Fail ∩ Q = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hwint, hwQ⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hwint)
    obtain ⟨δQ, hδQ, hδQsub⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hwQ)
    set ρ : ℝ := min δ δQ with hρdef
    have hρpos : 0 < ρ := lt_min hδ hδQ
    have hρsub : Metric.ball w ρ ⊆ Fail ∩ Q := by
      intro x hx
      rw [Metric.mem_ball] at hx
      exact ⟨hδsub (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_left _ _))),
        hδQsub (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _)))⟩
    set C : Fin b → ℕ → Set (Fin a → ℝ) := fun j m =>
      Metric.closedBall w (ρ / 2) ∩ failSet G j (1 / ((m : ℝ) + 1)) with hCdef
    have hCclosed : ∀ j m, IsClosed (C j m) := fun j m =>
      Metric.isClosed_closedBall.inter (isClosed_failSet G j _)
    have hcover : Metric.closedBall w (ρ / 2) ⊆ ⋃ j : Fin b, ⋃ m : ℕ, C j m := by
      intro x hx
      have hxρ : x ∈ Metric.ball w ρ := Metric.mem_ball.mpr (by
        rw [Metric.mem_closedBall] at hx; linarith)
      obtain ⟨hxF, -⟩ := hρsub hxρ
      rw [hFaileq] at hxF
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxF
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hj
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨m, ⟨hx, hm⟩⟩⟩
    have hex : ∃ j : Fin b, ∃ m : ℕ, (interior (C j m)).Nonempty := by
      by_contra hcon
      push Not at hcon
      have hdense : ∀ j m, Dense ((C j m)ᶜ) := fun j m => by
        rw [← interior_eq_empty_iff_dense_compl]; exact hcon j m
      have hopen : ∀ j m, IsOpen ((C j m)ᶜ) := fun j m => (hCclosed j m).isOpen_compl
      have h1 : ∀ m : ℕ, Dense (⋂ j : Fin b, (C j m)ᶜ) := fun m =>
        dense_iInter_of_isOpen (fun j => hopen j m) (fun j => hdense j m)
      have h2 : Dense (⋂ m : ℕ, ⋂ j : Fin b, (C j m)ᶜ) :=
        dense_iInter_of_isOpen (fun m => isOpen_iInter_of_finite (fun j => hopen j m)) h1
      obtain ⟨x, hxS, hxB⟩ := h2.exists_mem_open (Metric.isOpen_ball (x := w) (ε := ρ/4))
        ⟨w, Metric.mem_ball_self (by linarith)⟩
      have hxc : x ∈ Metric.closedBall w (ρ / 2) := Metric.mem_closedBall.mpr (by
        rw [Metric.mem_ball] at hxB; linarith)
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hxc)
      obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hj
      exact (Set.mem_iInter.mp (Set.mem_iInter.mp hxS m) j) hxm
    obtain ⟨j, m, hnint⟩ := hex
    obtain ⟨x, hx⟩ := hnint
    have hxQ : x ∈ Q := by
      have hxN : x ∈ C j m := interior_subset hx
      have hxc : x ∈ Metric.closedBall w (ρ/2) := hxN.1
      rw [Metric.mem_closedBall] at hxc
      exact (hρsub (Metric.mem_ball.mpr (by linarith))).2
    have hxint : x ∈ interior (failSet G j (1 / ((m : ℝ) + 1))) :=
      interior_mono Set.inter_subset_right hx
    have hthin := interior_failSet_inter_Q_empty S hcd hder G hG Q hQ r0 hr0 hsl hoff j _
      (by positivity : (0:ℝ) < 1 / ((m : ℝ) + 1))
    rw [Set.eq_empty_iff_forall_notMem] at hthin
    exact hthin x ⟨hxint, hxQ⟩
  obtain ⟨N, hNclosed, hNint, hNsub⟩ := exists_closed_nowhereDense_cover hcd hFailmem Q hFailthin
  have hQ1open : IsOpen (Q \ N) := hQ.sdiff hNclosed
  have hQ1sub : Q \ N ⊆ Q := Set.diff_subset
  have hQ1dense : Q ⊆ closure (Q \ N) := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_contra hcon
    push_neg at hcon
    have hsub : Metric.ball x ε ∩ Q ⊆ N := by
      intro y hy
      by_contra hyN
      have hyb : dist y x < ε := Metric.mem_ball.mp hy.1
      have hge : ε ≤ dist x y := hcon y ⟨hy.2, hyN⟩
      rw [dist_comm] at hyb
      exact absurd hyb (not_lt.mpr hge)
    have hxint : x ∈ interior N :=
      interior_maximal hsub (Metric.isOpen_ball.inter hQ) ⟨Metric.mem_ball_self hε, hx⟩
    rw [hNint] at hxint
    exact hxint
  have hfirst : ∀ w₀ ∈ Q \ N, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η → ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖ < ε := by
    intro w₀ hw₀ ε hε
    have hw₀Q : w₀ ∈ Q := hw₀.1
    have hw₀N : w₀ ∉ N := hw₀.2
    have hgood : ∀ j : Fin b, ∀ n : ℕ, w₀ ∈ goodSet G j (1 / ((n : ℝ) + 1)) := by
      intro j n
      by_contra hc
      exact hw₀N (hNsub ⟨by
        rw [hFaileq]
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨n, hc⟩⟩, hw₀Q⟩)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (b : ℝ) / ((n : ℝ) + 1) < ε := by
      have hbp1 : (0 : ℝ) < (b : ℝ) + 1 := by linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < ε / ((b : ℝ) + 1) by positivity)
      refine ⟨n, ?_⟩
      rw [div_eq_mul_one_div]
      calc (b : ℝ) * (1 / ((n : ℝ) + 1)) < (b : ℝ) * (ε / ((b : ℝ) + 1)) :=
            mul_lt_mul_of_pos_left hn hbm
        _ = ((b : ℝ) / ((b : ℝ) + 1)) * ε := by ring
        _ < 1 * ε := by
            refine mul_lt_mul_of_pos_right ?_ hε
            rw [div_lt_one hbp1]; linarith
        _ = ε := one_mul ε
    have hwit : ∀ j : Fin b, ∃ η : ℝ, 0 < η ∧ ∀ (w' : Fin a → ℝ) (z z' : Fin b → ℝ),
        dist w' w₀ < η → z ≠ 0 → ‖z‖ < η → z' ≠ 0 → ‖z'‖ < η →
          Fin.append w' z ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
          Fin.append w' z' ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
          |Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w' z) -
           Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w' z')|
            < 1 / ((n : ℝ) + 1) := fun j => hgood j n
    choose ηf hηf using hwit
    obtain ⟨ηu, hηupos, hηule⟩ : ∃ ηu : ℝ, 0 < ηu ∧ ∀ j : Fin b, ηu ≤ ηf j := by
      have hne : (Finset.univ.image ηf).Nonempty :=
        ⟨ηf ⟨0, hbpos⟩, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
      refine ⟨(Finset.univ.image ηf).min' hne, ?_, ?_⟩
      · obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
        rw [← hj]; exact (hηf j).1
      · intro j
        exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    obtain ⟨δQ, hδQ, hδQsub⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hw₀Q)
    refine ⟨min ηu δQ, lt_min hηupos hδQ, fun w z hw hz hzlt => ?_⟩
    have hwQ : w ∈ Q := hδQsub (Metric.mem_ball.mpr (lt_of_lt_of_le hw (min_le_right _ _)))
    have hwdist : ∀ j : Fin b, dist w w₀ < ηf j := fun j =>
      lt_of_lt_of_le hw (le_trans (min_le_left _ _) (hηule j))
    have hzlt' : ∀ j : Fin b, ‖z‖ < ηf j := fun j =>
      lt_of_lt_of_le hzlt (le_trans (min_le_left _ _) (hηule j))
    have hcomp : ∀ j : Fin b,
        |fderiv ℝ (G w) z (Pi.single j 1) - fderiv ℝ (G w) 0 (Pi.single j 1)|
          ≤ 1 / ((n : ℝ) + 1) := by
      intro j
      have hηj : 0 < ηf j := (hηf j).1
      have hmpos : 0 < min (ηf j) r0 := lt_min hηj hr0
      set c : ℕ → ℝ := fun m => min (ηf j) r0 / ((m : ℝ) + 2) with hcdef
      have hcpos : ∀ m, 0 < c m := fun m => by rw [hcdef]; positivity
      have hcltη : ∀ m, c m < ηf j := by
        intro m
        have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by
          have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        have h3 : min (ηf j) r0 / ((m : ℝ) + 2) ≤ min (ηf j) r0 / 2 :=
          div_le_div_of_nonneg_left (le_of_lt hmpos) (show (0 : ℝ) < 2 by norm_num) h2
        have h4 : min (ηf j) r0 / 2 < ηf j := by
          have := min_le_left (ηf j) r0; linarith
        rw [hcdef]; linarith
      have hzsne : ∀ m, (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) ≠ 0 := by
        intro m h
        have := congrArg (fun v : Fin b → ℝ => v j) h
        simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply] at this
        exact absurd this (ne_of_gt (hcpos m))
      have hzsnorm : ∀ m, ‖c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)‖ = c m := fun m => by
        rw [norm_smul, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs,
          abs_of_pos (hcpos m)]
      have hinst : ∀ m : ℕ,
          Fin.append w z ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
          Fin.append w (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) ∈
            Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
          |Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w z) -
           Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j)
             (Fin.append w (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)))| < 1 / ((n : ℝ) + 1) :=
        fun m => (hηf j).2 w z (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) (hwdist j) hz
          (hzlt' j) (hzsne m) (by rw [hzsnorm]; exact hcltη m)
      have htrz : Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w z)
          = fderiv ℝ (G w) z (Pi.single j 1) :=
        famFun_dDir_append G w z j ((show ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
            (Fin.append w z) from interior_subset (hinst 0).1).differentiableAt (by norm_num))
      have htrm : ∀ m, Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j)
            (Fin.append w (c m • (Pi.single j (1:ℝ) : Fin b → ℝ)))
          = fderiv ℝ (G w) (c m • (Pi.single j (1:ℝ) : Fin b → ℝ)) (Pi.single j 1) := fun m =>
        famFun_dDir_append G w (c m • Pi.single j 1) j
          ((show ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
            (Fin.append w (c m • Pi.single j (1 : ℝ))) from
            interior_subset (hinst m).2.1).differentiableAt (by norm_num))
      have hbnd : ∀ m, |fderiv ℝ (G w) z (Pi.single j 1) -
            fderiv ℝ (G w) (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) (Pi.single j 1)|
            < 1 / ((n : ℝ) + 1) := fun m => by
        rw [← htrz, ← htrm m]; exact (hinst m).2.2
      have hcont : ContinuousAt (fun z : Fin b → ℝ => fderiv ℝ (G w) z (Pi.single j 1)) 0 := by
        have h1 : ContDiffAt ℝ 1 (G w) 0 :=
          (hsl w hwQ).contDiffAt (Metric.ball_mem_nhds 0 hr0)
        have h2 : ContinuousAt (fderiv ℝ (G w)) 0 := h1.continuousAt_fderiv (by norm_num)
        have h3 : ContinuousAt (fun L : (Fin b → ℝ) →L[ℝ] ℝ => L (Pi.single j 1))
            (fderiv ℝ (G w) 0) :=
          ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)).continuous).continuousAt
        exact h3.comp h2
      have hc0 : Filter.Tendsto c Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2)) Filter.atTop (nhds 0) := by
          have hbase : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1))
              Filter.atTop (nhds 0) :=
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
              (Filter.tendsto_add_atTop_nat 1)
          have := hbase
          rw [show (fun m : ℕ => (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1))
              = fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 2) from by
            funext m; push_cast; ring] at this
          exact this
        have h3 : Filter.Tendsto (fun m : ℕ => min (ηf j) r0 * (1 / ((m : ℝ) + 2)))
            Filter.atTop (nhds 0) := by
          have h4 := Filter.Tendsto.const_mul (min (ηf j) r0) h1
          simpa using h4
        have h5 : (fun m : ℕ => min (ηf j) r0 * (1 / ((m : ℝ) + 2)))
            = fun m : ℕ => min (ηf j) r0 / ((m : ℝ) + 2) := by
          funext m; ring
        rw [hcdef, ← h5]
        exact h3
      have hsm : Filter.Tendsto (fun m : ℕ => c m • (Pi.single j (1 : ℝ) : Fin b → ℝ))
          Filter.atTop (nhds (0 : Fin b → ℝ)) := by
        simpa using hc0.smul_const (Pi.single j (1 : ℝ) : Fin b → ℝ)
      have hlim : Filter.Tendsto
          (fun m : ℕ => fderiv ℝ (G w) (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) (Pi.single j 1))
          Filter.atTop (nhds (fderiv ℝ (G w) 0 (Pi.single j 1))) :=
        hcont.tendsto.comp hsm
      have hlim' : Filter.Tendsto
          (fun m : ℕ => |fderiv ℝ (G w) z (Pi.single j 1) -
            fderiv ℝ (G w) (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) (Pi.single j 1)|)
          Filter.atTop
          (nhds (|fderiv ℝ (G w) z (Pi.single j 1) - fderiv ℝ (G w) 0 (Pi.single j 1)|)) :=
        (Filter.Tendsto.const_sub (fderiv ℝ (G w) z (Pi.single j 1)) hlim).abs
      exact le_of_tendsto' hlim' (fun m => le_of_lt (hbnd m))
    calc ‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖
        ≤ ∑ j : Fin b, |(fderiv ℝ (G w) z - fderiv ℝ (G w) 0) (Pi.single j 1)| :=
          norm_le_sum_single _
      _ = ∑ j : Fin b,
            |fderiv ℝ (G w) z (Pi.single j 1) - fderiv ℝ (G w) 0 (Pi.single j 1)| := by
          simp only [sub_apply]
      _ ≤ ∑ _j : Fin b, 1 / ((n : ℝ) + 1) := Finset.sum_le_sum fun j _ => hcomp j
      _ = (b : ℝ) * (1 / ((n : ℝ) + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < ε := by rw [div_eq_mul_one_div] at hn; exact hn
  refine ⟨Q \ N, hQ1open, hQ1sub, hQ1dense, hfirst, ?_⟩
  intro w₀ hw₀ j
  refine ContinuousAt.tendsto ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨ηa, hηapos, hηa⟩ := hfirst w₀ hw₀ (ε / 3) (by linarith)
  have hηar0 : 0 < min ηa r0 := lt_min hηapos hr0
  set z₀ : Fin b → ℝ := (min ηa r0 / 2) • (Pi.single j (1 : ℝ)) with hz₀def
  have hz₀norm : ‖z₀‖ = min ηa r0 / 2 := by
    rw [hz₀def, norm_smul, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have hz₀pos : 0 < min ηa r0 / 2 := by linarith
  have hz₀ne : z₀ ≠ 0 := by
    intro h
    have := congrArg (fun v : Fin b → ℝ => v j) h
    simp only [hz₀def, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.zero_apply]
      at this
    exact absurd this (ne_of_gt hz₀pos)
  have hz₀r0 : ‖z₀‖ < r0 := by
    rw [hz₀norm]; have := min_le_right ηa r0; linarith
  have hz₀η : ‖z₀‖ < ηa := by
    rw [hz₀norm]; have := min_le_left ηa r0; linarith
  have hcontw := continuousAt_slice_fderiv_offSheet G w₀ z₀ j (hoff w₀ hw₀.1 z₀ hz₀ne hz₀r0)
  have hex : ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin a → ℝ,
      dist y w₀ < δ → dist (fderiv ℝ (G y) z₀ (Pi.single j 1))
        (fderiv ℝ (G w₀) z₀ (Pi.single j 1)) < ε / 3 :=
    Metric.continuousAt_iff.mp hcontw (ε / 3) (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := hex
  refine ⟨min ηa δ, lt_min hηapos hδpos, fun w hw => ?_⟩
  have hw1 : dist w w₀ < ηa := lt_of_lt_of_le hw (min_le_left _ _)
  have hw2 : dist w w₀ < δ := lt_of_lt_of_le hw (min_le_right _ _)
  have h1 : |fderiv ℝ (G w) z₀ (Pi.single j 1) - fderiv ℝ (G w) 0 (Pi.single j 1)| < ε / 3 := by
    have h2 : ‖(fderiv ℝ (G w) z₀ - fderiv ℝ (G w) 0) (Pi.single j 1)‖
        ≤ ‖fderiv ℝ (G w) z₀ - fderiv ℝ (G w) 0‖ := by
      have := ContinuousLinearMap.le_opNorm (fderiv ℝ (G w) z₀ - fderiv ℝ (G w) 0)
        (Pi.single j 1)
      rwa [Pi.norm_single, norm_one, mul_one] at this
    rw [sub_apply, Real.norm_eq_abs] at h2
    exact lt_of_le_of_lt h2 (hηa w z₀ hw1 hz₀ne hz₀η)
  have h3 : |fderiv ℝ (G w₀) z₀ (Pi.single j 1) - fderiv ℝ (G w₀) 0 (Pi.single j 1)| < ε / 3 := by
    have h2 : ‖(fderiv ℝ (G w₀) z₀ - fderiv ℝ (G w₀) 0) (Pi.single j 1)‖
        ≤ ‖fderiv ℝ (G w₀) z₀ - fderiv ℝ (G w₀) 0‖ := by
      have := ContinuousLinearMap.le_opNorm (fderiv ℝ (G w₀) z₀ - fderiv ℝ (G w₀) 0)
        (Pi.single j 1)
      rwa [Pi.norm_single, norm_one, mul_one] at this
    rw [sub_apply, Real.norm_eq_abs] at h2
    exact lt_of_le_of_lt h2 (hηa w₀ z₀ (by simpa using hηapos) hz₀ne hz₀η)
  have h4 : |fderiv ℝ (G w) z₀ (Pi.single j 1) - fderiv ℝ (G w₀) z₀ (Pi.single j 1)| < ε / 3 := by
    have := hδ w hw2
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq]
  calc |fderiv ℝ (G w) 0 (Pi.single j 1) - fderiv ℝ (G w₀) 0 (Pi.single j 1)|
      ≤ |fderiv ℝ (G w) 0 (Pi.single j 1) - fderiv ℝ (G w) z₀ (Pi.single j 1)|
        + |fderiv ℝ (G w) z₀ (Pi.single j 1) - fderiv ℝ (G w₀) z₀ (Pi.single j 1)|
        + |fderiv ℝ (G w₀) z₀ (Pi.single j 1) - fderiv ℝ (G w₀) 0 (Pi.single j 1)| := by
        have h1' := abs_sub_le (fderiv ℝ (G w) 0 (Pi.single j 1))
          (fderiv ℝ (G w) z₀ (Pi.single j 1)) (fderiv ℝ (G w₀) 0 (Pi.single j 1))
        have h2' := abs_sub_le (fderiv ℝ (G w) z₀ (Pi.single j 1))
          (fderiv ℝ (G w₀) z₀ (Pi.single j 1)) (fderiv ℝ (G w₀) 0 (Pi.single j 1))
        linarith
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1' : |fderiv ℝ (G w) 0 (Pi.single j 1) - fderiv ℝ (G w) z₀ (Pi.single j 1)|
            < ε / 3 := by rw [abs_sub_comm]; exact h1
        linarith
    _ = ε := by ring

end Work.WilCrux
