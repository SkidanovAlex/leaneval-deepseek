import Mathlib
import Submission.Work.WilCruxN.DerivGraphClean
import Submission.Work.WilCruxN.SliceCauchyMemPerJ
import Submission.Work.WilCruxN.FailSetMemPerJ
import Submission.Work.WilCrux.ParamDerivAux
import Submission.Work.WilCrux.OmegaModulus
import Submission.Work.WilCrux.SliceDerivJointContV2

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
open scoped Topology

namespace Work.WilCruxN

open WilkiesDesign WilkiesDesign.CG

/-
  **Node N4b of the WilCrux flat-sheet chain, per fibre direction and without `SharpDeriv`.**

  `Work.WilCrux.SliceDerivJointContV2` proves this statement (with the direction `j` quantified
  inside and with the norm `‖fderiv ℝ (G w) z - fderiv ℝ (G w) 0‖` instead of the single
  coordinate) *assuming* `hder : S.SharpDeriv`.  The proof only uses `SharpDeriv` at order one,
  and the order-one derivative graph is `Ω`-definable from `SharpCD` alone
  (`Work.WilCruxN.derivGraph_mem_clean`).  Do **not** call `Work.WilG4b.derivGraph_mem`, nor the
  `hder`-taking files `Work.WilCrux.sliceCauchy_mem` / `Work.WilCrux.failSet_mem`.

  Implementation (a faithful port of the proof of `Work.WilCrux.SliceDerivJointContV2` with the
  direction `j` fixed, so that the `Ω`-bounds may depend on `j`): the only two inputs of that proof
  which used `SharpDeriv` are the `Ω`-definability of the uniform-Cauchy sets
  `Work.WilCrux.sliceCauchySet G j k ε` (`Work.WilCruxN.SliceCauchyMemPerJ`) and of the failure
  set with the level as a coordinate (`Work.WilCruxN.FailSetMemPerJ`); both are available from
  `SharpCD` alone at a fixed `j`.  With those two in hand the rest of the argument is
  `Work.WilCrux.BaireDefinableCover` (for each level `ε`, the sets `sliceCauchySet G j k ε` cover
  `Q`, so their interiors meet `Q`, whence `interior (failSet G j ε) ∩ Q = ∅`), the countable Baire
  step for `Fail := ⋃_{ε>0} failSet G j ε`, the sharp decomposition
  `Work.WilCrux.exists_closed_nowhereDense_cover`, and the limit argument at the sheet using
  `hsl` to compare the off-sheet partials with `fderiv ℝ (G w) 0 (Pi.single j 1)`.

  `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`.
-/

/-- **Baire step at a fixed level.**  If the uniform-Cauchy sets `sliceCauchySet G j k ε` are
`Ω`-definable with format and degree independent of `k`, then the interior of the failure set at
level `ε` misses `Q`: `Q` is covered by the `sliceCauchySet G j k ε` (`sliceCauchy_cover`), whose
interiors lie in `goodSet G j ε`, so `BaireDefinableCover` produces a point of
`interior (sliceCauchySet G j k ε) ∩ Q`, which cannot lie in `failSet G j ε`. -/
theorem interior_failSet_inter_Q_empty_aux (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q : Set (Fin a → ℝ)) (hQ : IsOpen Q) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (j : Fin b) (A : ℕ) (q : Polynomial ℕ)
    (hmemS : ∀ (k : ℕ) (ε : ℝ), Work.WilCrux.sliceCauchySet G j k ε ∈ S.Ω A (q.eval D) a)
    (ε : ℝ) (hε : 0 < ε) :
    interior (Work.WilCrux.failSet G j ε) ∩ Q = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro w ⟨hwint, hwQ⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hwint)
  obtain ⟨δQ, hδQ, hδQsub⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hwQ)
  set ρ : ℝ := min δ δQ with hρdef
  have hρpos : 0 < ρ := lt_min hδ hδQ
  have hρsub : Metric.ball w ρ ⊆ Work.WilCrux.failSet G j ε ∩ Q := by
    intro x hx
    rw [Metric.mem_ball] at hx
    exact ⟨hδsub (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_left _ _))),
      hδQsub (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _)))⟩
  obtain ⟨k, hk⟩ := Work.WilCrux.BaireDefinableCover S hcd
    (fun k : ℕ => Work.WilCrux.sliceCauchySet G j k ε)
    (fun k => ⟨A, q.eval D, hmemS k ε⟩) (Metric.ball w ρ) Metric.isOpen_ball
    ⟨w, Metric.mem_ball_self hρpos⟩
    (fun x hx => Work.WilCrux.sliceCauchy_cover G Q r0 hr0 hsl hoff j hε (hρsub hx).2)
  obtain ⟨x, hxint, hxball⟩ := hk
  exact (hρsub hxball).1 (Work.WilCrux.interior_sliceCauchySet_subset_goodSet G j k ε hxint)

theorem SliceDerivJointPerJ (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {a b F D : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (Q : Set (Fin a → ℝ)) (hQ : IsOpen Q) (r0 : ℝ) (hr0 : 0 < r0)
    (hsl : ∀ w ∈ Q, ContDiffOn ℝ 1 (G w) (Metric.ball 0 r0))
    (hoff : ∀ w ∈ Q, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    (j : Fin b) :
    ∃ Q1 : Set (Fin a → ℝ), IsOpen Q1 ∧ Q1 ⊆ Q ∧ Q ⊆ closure Q1 ∧
      (∀ w₀ ∈ Q1, ∀ ε > 0, ∃ η > 0, ∀ (w : Fin a → ℝ) (z : Fin b → ℝ),
        dist w w₀ < η → z ≠ 0 → ‖z‖ < η →
          |(fderiv ℝ (G w) z - fderiv ℝ (G w) 0) (Pi.single j 1)| < ε) ∧
      (∀ w₀ ∈ Q1, Filter.Tendsto (fun w => fderiv ℝ (G w) 0 (Pi.single j 1)) (nhds w₀)
        (nhds (fderiv ℝ (G w₀) 0 (Pi.single j 1)))) := by
  classical
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    exact j.elim0
  obtain ⟨A, q, hmemS⟩ := SliceCauchyMemPerJ S hcd G hG j
  obtain ⟨A', q', hmemF⟩ := FailSetMemPerJ S hcd G hG j
  have hbm : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hbpos
  -- the failure set with the level as a coordinate, projected to the parameter space
  set Fail : Set (Fin a → ℝ) :=
    projLast {u : Fin (a + 1) → ℝ | 0 < u (Fin.last a) ∧
      Fin.init u ∈ Work.WilCrux.failSet G j (u (Fin.last a))} with hFaildef
  have hFailmem : Fail ∈ S.Ω (A' + 1) (q'.eval D) a := by
    rw [hFaildef]
    exact Work.WilG1.Omega.mono (S.proj hmemF) le_rfl le_rfl
  have hFaileq : Fail = ⋃ m : ℕ, Work.WilCrux.failSet G j (1 / ((m : ℝ) + 1)) := by
    rw [hFaildef]
    ext w
    simp only [Set.mem_iUnion, projLast, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    constructor
    · rintro ⟨ε, hε, hw⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      exact ⟨m, fun hc => hw (Work.WilCrux.goodSet_mono G j (le_of_lt hm) hc)⟩
    · rintro ⟨m, hw⟩
      exact ⟨1 / ((m : ℝ) + 1), by positivity, hw⟩
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
    set C : ℕ → Set (Fin a → ℝ) := fun m =>
      Metric.closedBall w (ρ / 2) ∩ Work.WilCrux.failSet G j (1 / ((m : ℝ) + 1)) with hCdef
    have hCclosed : ∀ m, IsClosed (C m) := fun m =>
      Metric.isClosed_closedBall.inter (Work.WilCrux.isClosed_failSet G j _)
    have hcover : Metric.closedBall w (ρ / 2) ⊆ ⋃ m : ℕ, C m := by
      intro x hx
      have hxρ : x ∈ Metric.ball w ρ := Metric.mem_ball.mpr (by
        rw [Metric.mem_closedBall] at hx; linarith)
      obtain ⟨hxF, -⟩ := hρsub hxρ
      rw [hFaileq] at hxF
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxF
      exact Set.mem_iUnion.mpr ⟨m, ⟨hx, hm⟩⟩
    have hex : ∃ m : ℕ, (interior (C m)).Nonempty := by
      by_contra hcon
      push Not at hcon
      have hdense : ∀ m, Dense ((C m)ᶜ) := fun m => by
        rw [← interior_eq_empty_iff_dense_compl]; exact hcon m
      have hopen : ∀ m, IsOpen ((C m)ᶜ) := fun m => (hCclosed m).isOpen_compl
      have h2 : Dense (⋂ m : ℕ, (C m)ᶜ) :=
        dense_iInter_of_isOpen (fun m => hopen m) (fun m => hdense m)
      obtain ⟨x, hxS, hxB⟩ := h2.exists_mem_open (Metric.isOpen_ball (x := w) (ε := ρ / 4))
        ⟨w, Metric.mem_ball_self (by linarith)⟩
      have hxc : x ∈ Metric.closedBall w (ρ / 2) := Metric.mem_closedBall.mpr (by
        rw [Metric.mem_ball] at hxB; linarith)
      obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp (hcover hxc)
      exact (Set.mem_iInter.mp hxS m) hxm
    obtain ⟨m, hnint⟩ := hex
    obtain ⟨x, hx⟩ := hnint
    have hxQ : x ∈ Q := by
      have hxN : x ∈ C m := interior_subset hx
      have hxc : x ∈ Metric.closedBall w (ρ / 2) := hxN.1
      rw [Metric.mem_closedBall] at hxc
      exact (hρsub (Metric.mem_ball.mpr (by linarith))).2
    have hxint : x ∈ interior (Work.WilCrux.failSet G j (1 / ((m : ℝ) + 1))) :=
      interior_mono Set.inter_subset_right hx
    have hthin := interior_failSet_inter_Q_empty_aux S hcd G hG Q hQ r0 hr0 hsl hoff j A q
      hmemS _ (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
    rw [Set.eq_empty_iff_forall_notMem] at hthin
    exact hthin x ⟨hxint, hxQ⟩
  obtain ⟨N, hNclosed, hNint, hNsub⟩ :=
    Work.WilCrux.exists_closed_nowhereDense_cover hcd hFailmem Q hFailthin
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
      dist w w₀ < η → z ≠ 0 → ‖z‖ < η →
        |(fderiv ℝ (G w) z - fderiv ℝ (G w) 0) (Pi.single j 1)| < ε := by
    intro w₀ hw₀ ε hε
    have hw₀Q : w₀ ∈ Q := hw₀.1
    have hw₀N : w₀ ∉ N := hw₀.2
    have hgood : ∀ n : ℕ, w₀ ∈ Work.WilCrux.goodSet G j (1 / ((n : ℝ) + 1)) := by
      intro n
      by_contra hc
      exact hw₀N (hNsub ⟨by
        rw [hFaileq]
        exact Set.mem_iUnion.mpr ⟨n, hc⟩, hw₀Q⟩)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 1) < ε := exists_nat_one_div_lt hε
    obtain ⟨ηf, hηfpos, hηfprop⟩ := hgood n
    obtain ⟨δQ, hδQ, hδQsub⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hw₀Q)
    refine ⟨min (min ηf r0) δQ, lt_min (lt_min hηfpos hr0) hδQ, fun w z hw hz hzlt => ?_⟩
    have hwQ : w ∈ Q := hδQsub (Metric.mem_ball.mpr (lt_of_lt_of_le hw (min_le_right _ _)))
    have hwdist : dist w w₀ < ηf :=
      lt_of_lt_of_le hw (le_trans (min_le_left _ _) (min_le_left _ _))
    have hzlt' : ‖z‖ < ηf :=
      lt_of_lt_of_le hzlt (le_trans (min_le_left _ _) (min_le_left _ _))
    have hmpos : 0 < min ηf r0 := lt_min hηfpos hr0
    set c : ℕ → ℝ := fun m => min ηf r0 / ((m : ℝ) + 2) with hcdef
    have hcpos : ∀ m, 0 < c m := fun m => by rw [hcdef]; positivity
    have hcltη : ∀ m, c m < ηf := by
      intro m
      have h2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have h3 : min ηf r0 / ((m : ℝ) + 2) ≤ min ηf r0 / 2 :=
        div_le_div_of_nonneg_left (le_of_lt hmpos) (show (0 : ℝ) < 2 by norm_num) h2
      have h4 : min ηf r0 / 2 < ηf := by
        have := min_le_left ηf r0; linarith
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
           (Fin.append w (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)))| <
          1 / ((n : ℝ) + 1) :=
      fun m => hηfprop w z (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) hwdist hz hzlt'
        (hzsne m) (by rw [hzsnorm]; exact hcltη m)
    have htrz : Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w z)
        = fderiv ℝ (G w) z (Pi.single j 1) :=
      Work.WilCrux.famFun_dDir_append G w z j
        ((show ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z) from
            interior_subset (hinst 0).1).differentiableAt (by norm_num))
    have htrm : ∀ m, Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j)
          (Fin.append w (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)))
        = fderiv ℝ (G w) (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) (Pi.single j 1) := fun m =>
      Work.WilCrux.famFun_dDir_append G w (c m • Pi.single j 1) j
        ((show ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
            (Fin.append w (c m • (Pi.single j (1 : ℝ)))) from
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
      have h3 : Filter.Tendsto (fun m : ℕ => min ηf r0 * (1 / ((m : ℝ) + 2)))
          Filter.atTop (nhds 0) := by
        have h4 := Filter.Tendsto.const_mul (min ηf r0) h1
        simpa using h4
      have h5 : (fun m : ℕ => min ηf r0 * (1 / ((m : ℝ) + 2)))
          = fun m : ℕ => min ηf r0 / ((m : ℝ) + 2) := by
        funext m; ring
      rw [hcdef, ← h5]
      exact h3
    have hsm : Filter.Tendsto (fun m : ℕ => c m • (Pi.single j (1 : ℝ) : Fin b → ℝ))
        Filter.atTop (nhds (0 : Fin b → ℝ)) := by
      simpa using hc0.smul_const (Pi.single j (1 : ℝ) : Fin b → ℝ)
    have hlim : Filter.Tendsto
        (fun m : ℕ => fderiv ℝ (G w) (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ))
          (Pi.single j 1))
        Filter.atTop (nhds (fderiv ℝ (G w) 0 (Pi.single j 1))) :=
      hcont.tendsto.comp hsm
    have hlim' : Filter.Tendsto
        (fun m : ℕ => |fderiv ℝ (G w) z (Pi.single j 1) -
          fderiv ℝ (G w) (c m • (Pi.single j (1 : ℝ) : Fin b → ℝ)) (Pi.single j 1)|)
        Filter.atTop
        (nhds (|fderiv ℝ (G w) z (Pi.single j 1) - fderiv ℝ (G w) 0 (Pi.single j 1)|)) :=
      (Filter.Tendsto.const_sub (fderiv ℝ (G w) z (Pi.single j 1)) hlim).abs
    have hle := le_of_tendsto' hlim' (fun m => le_of_lt (hbnd m))
    simpa only [ContinuousLinearMap.sub_apply] using lt_of_le_of_lt hle hn
  refine ⟨Q \ N, hQ1open, hQ1sub, hQ1dense, hfirst, ?_⟩
  intro w₀ hw₀
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
  have hcontw := Work.WilCrux.continuousAt_slice_fderiv_offSheet G w₀ z₀ j
    (hoff w₀ hw₀.1 z₀ hz₀ne hz₀r0)
  have hex : ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin a → ℝ,
      dist y w₀ < δ → dist (fderiv ℝ (G y) z₀ (Pi.single j 1))
        (fderiv ℝ (G w₀) z₀ (Pi.single j 1)) < ε / 3 :=
    Metric.continuousAt_iff.mp hcontw (ε / 3) (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := hex
  refine ⟨min ηa δ, lt_min hηapos hδpos, fun w hw => ?_⟩
  have hw1 : dist w w₀ < ηa := lt_of_lt_of_le hw (min_le_left _ _)
  have hw2 : dist w w₀ < δ := lt_of_lt_of_le hw (min_le_right _ _)
  have h1 : |fderiv ℝ (G w) z₀ (Pi.single j 1) - fderiv ℝ (G w) 0 (Pi.single j 1)|
      < ε / 3 := by
    simpa only [ContinuousLinearMap.sub_apply] using hηa w z₀ hw1 hz₀ne hz₀η
  have h3 : |fderiv ℝ (G w₀) z₀ (Pi.single j 1) - fderiv ℝ (G w₀) 0 (Pi.single j 1)|
      < ε / 3 := by
    simpa only [ContinuousLinearMap.sub_apply] using
      hηa w₀ z₀ (by simpa using hηapos) hz₀ne hz₀η
  have h4 : |fderiv ℝ (G w) z₀ (Pi.single j 1) - fderiv ℝ (G w₀) z₀ (Pi.single j 1)|
      < ε / 3 := by
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

end Work.WilCruxN
