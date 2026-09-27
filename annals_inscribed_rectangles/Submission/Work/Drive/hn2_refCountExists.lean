import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.refTripleLocalAssembly
import Submission.Work.Drive.hn2CountInterface
import Submission.Work.Drive.blockFactorIdentification
import Submission.Work.Drive.transportThreeLevel
import Submission.Work.Drive.sideGerm_indep
import Submission.Work.Drive.sideGermLocalconstUnconditional
import Submission.Work.Drive.refPlaneLevel
import Submission.Work.Drive.mixedFactorBox
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.chartPert_rotCapping_comm
import Submission.Work.Drive.guardedParity
import Submission.Work.Drive.refTripleOneT
import Submission.Work.Drive.germLevelParity
import Submission.Work.Drive.sideGerm_parity_eq_of_close_loop
import Submission.Work.Drive.coreLoop_disjoint_rotCapping
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.hn2_refTripleAt_producerHuv
import Submission.Work.Drive.odd_sum_bottomBdryMeet_of_classTriple
import Submission.Work.Drive.bottomBdryMeet_clampedSweep_count

/-!
# The counting datum of `hn2` (`Work.Drive.hn2_refCountExists`)

This file proves the **counting datum** of the germ lane: for the concrete chart perturbation family
`chartPert`, at every angle `a ∈ Zc γ` different from the half turn and at every scale `ε > 0`, there
are `chartPert`-parameters `t`, `t'` of norm `< ε` at which the two opposite configurations are good
(`GoodAt`) and whose loop-vs-sweep counts have **odd sum**.

## Route

The datum is the *count form* of Hugelmeyer's Lemma 3 (the antisymmetry of the germ side value); the
implication *germ antisymmetry ⟹ count datum* uses only the **definition** of the germ value
`sideGerm`, the Sard existence of good configurations, and the elementary parity dichotomy:

* the germ antisymmetry `sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1` at every `a ∈ Zc γ`, `a ≠ 1/2`,
  is proved here (`Work.Drive.hn2_germ_antisym`) from the **one-parameter reference-triple producer**
  `Work.Drive.hn2_refTripleAt_producer` and the germ-locality data assembled below
  (`Work.Drive.exists_germLocalityTwo`);
* `Work.Drive.sideGerm_eq_one_iff` reads the germ value as
  `sideGerm Ξ Q c w = 1 ↔ ¬ ∃ᶠ t in 𝓝 0, GoodAt Ξ Q c w t ∧ Even (CntAt Ξ Q c w t)`, so
  * `sideGerm = 1` gives `∀ᶠ t, GoodAt → Odd` (every good configuration near `0` has odd count), and
  * `sideGerm ≠ 1` gives good configurations with **even** count arbitrarily close to `0`;
* `Work.Drive.sideGerm_good_exists` (the Sard existence) supplies good configurations arbitrarily close
  to `0` at every angle — this turns the `∀ᶠ`/`∃ᶠ` statements into *existence at an arbitrarily small
  scale*.

Since the two germ values sum to `1` in `ZMod 2`, exactly one of them is `1` and the other `0`: one
angle therefore has a good configuration of odd count and the other a good configuration of even count,
at any prescribed scale `ε`, and the sum of the two counts is odd.

The converse implication (count datum ⟹ germ antisymmetry) is the proved reduction
`Work.Drive.hn2_off_half`; the two forms are therefore equivalent.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The germ locality data at one angle and the two levels `c₀ < c`, `c₁ < c`.**  The six pieces are
the parity locality at the level `c` and at the level `c₀` at the angle `a`, the cross-level parity
`c ↔ c₀` at `a`, and the same three at the angle `-a` with the level `c₁`.  All six hold at one common
radius `ε`. -/
theorem exists_germLocalityTwo {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₀c : c₀ < c) (hc₁ : 0 < c₁) (hc₁c : c₁ < c)
    (a : UnitAddCircle) (ha : a ∈ Zc γ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
        ‖t‖ < ε → ‖t'‖ < ε →
        GoodAt (fun s p => chartPert s p) Q c a t → GoodAt (fun s p => chartPert s p) Q c a t' →
        Odd (CntAt (fun s p => chartPert s p) Q c a t) =
          Odd (CntAt (fun s p => chartPert s p) Q c a t')) ∧
      (∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
        ‖t‖ < ε → ‖t'‖ < ε →
        GoodAt (fun s p => chartPert s p) Q c₀ a t → GoodAt (fun s p => chartPert s p) Q c₀ a t' →
        Odd (CntAt (fun s p => chartPert s p) Q c₀ a t) =
          Odd (CntAt (fun s p => chartPert s p) Q c₀ a t')) ∧
      (∀ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖t‖ < ε →
        GoodAt (fun s p => chartPert s p) Q c a t →
        GoodAt (fun s p => chartPert s p) Q c₀ a t →
        Odd (CntAt (fun s p => chartPert s p) Q c a t) =
          Odd (CntAt (fun s p => chartPert s p) Q c₀ a t)) ∧
      (∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
        ‖t‖ < ε → ‖t'‖ < ε →
        GoodAt (fun s p => chartPert s p) Q c (-a) t → GoodAt (fun s p => chartPert s p) Q c (-a) t' →
        Odd (CntAt (fun s p => chartPert s p) Q c (-a) t) =
          Odd (CntAt (fun s p => chartPert s p) Q c (-a) t')) ∧
      (∀ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
        ‖t‖ < ε → ‖t'‖ < ε →
        GoodAt (fun s p => chartPert s p) Q c₁ (-a) t →
        GoodAt (fun s p => chartPert s p) Q c₁ (-a) t' →
        Odd (CntAt (fun s p => chartPert s p) Q c₁ (-a) t) =
          Odd (CntAt (fun s p => chartPert s p) Q c₁ (-a) t')) ∧
      (∀ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4), ‖t‖ < ε →
        GoodAt (fun s p => chartPert s p) Q c (-a) t →
        GoodAt (fun s p => chartPert s p) Q c₁ (-a) t →
        Odd (CntAt (fun s p => chartPert s p) Q c (-a) t) =
          Odd (CntAt (fun s p => chartPert s p) Q c₁ (-a) t)) := by
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  obtain ⟨εl, hεl, hlvl⟩ :=
    exists_eps_level_lt_pertChart_fam hQ (fun s p => chartPert s p) hΞc c hcbot
  have hna : -a ∈ Zc γ := neg_mem_Zc ha
  have hla : Disjoint (Set.range (coreLoop Q)) (rotCapping a '' chartDisk Q) :=
    disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ ha
  have hln : Disjoint (Set.range (coreLoop Q)) (rotCapping (-a) '' chartDisk Q) :=
    disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ hna
  obtain ⟨ε₁, δ₁, hε₁, hδ₁, hU₁⟩ :=
    sideGerm_parity_eq_of_close_loop (fun s p => chartPert s p) Q c hΞc hQd hc hcbot a hla
  have hcbot₀ : ∀ p ∈ chartDisk Q, c₀ < levelOf p :=
    fun p hp => lt_trans hc₀c (hcbot p hp)
  obtain ⟨ε₂, δ₂, hε₂, hδ₂, hU₂⟩ :=
    sideGerm_parity_eq_of_close_loop (fun s p => chartPert s p) Q c₀ hΞc hQd hc₀ hcbot₀ a hla
  obtain ⟨ε₃, δ₃, hε₃, hδ₃, hU₃⟩ :=
    sideGerm_parity_eq_of_close_loop (fun s p => chartPert s p) Q c hΞc hQd hc hcbot (-a) hln
  have hcbot₁ : ∀ p ∈ chartDisk Q, c₁ < levelOf p :=
    fun p hp => lt_trans hc₁c (hcbot p hp)
  obtain ⟨ε₄, δ₄, hε₄, hδ₄, hU₄⟩ :=
    sideGerm_parity_eq_of_close_loop (fun s p => chartPert s p) Q c₁ hΞc hQd hc₁ hcbot₁ (-a) hln
  set ε := min εl (min ε₁ (min ε₂ (min ε₃ ε₄))) with hεdef
  have hb₁ : ε ≤ ε₁ := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hb₂ : ε ≤ ε₂ := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hb₃ : ε ≤ ε₃ := by
    rw [hεdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hb₄ : ε ≤ ε₄ := by
    rw [hεdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hbl : ε ≤ εl := by rw [hεdef]; exact min_le_left _ _
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min hεl (lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)))
  refine ⟨ε, hεpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' ht ht' hg hg'
    exact hU₁ t t' a (lt_of_lt_of_le ht hb₁) (lt_of_lt_of_le ht' hb₁)
      (by rw [dist_self]; exact hδ₁) hg hg'
  · intro t t' ht ht' hg hg'
    exact hU₂ t t' a (lt_of_lt_of_le ht hb₂) (lt_of_lt_of_le ht' hb₂)
      (by rw [dist_self]; exact hδ₂) hg hg'
  · intro t ht hg hg'
    have htεl : ‖t‖ < εl := lt_of_lt_of_le ht hbl
    have ht1 : ‖t.1‖ < εl := lt_of_le_of_lt (norm_fst_le t) htεl
    have ht2 : ‖t.2‖ < εl := lt_of_le_of_lt (norm_snd_le t) htεl
    exact odd_CntAt_eq_of_goodAt_of_levels (fun s p => chartPert s p) Q c c₀ a t hc hc₀
      (levelLoop_pertChart _ Q c t.1 (fun p hp => hlvl t.1 ht1 p hp))
      (levelLoop_pertChart _ Q c₀ t.1 (fun p hp => lt_trans hc₀c (hlvl t.1 ht1 p hp)))
      (level_rotPresentation_pertChart _ Q c t.2 a (fun p hp => hlvl t.2 ht2 p hp))
      (level_rotPresentation_pertChart _ Q c₀ t.2 a
        (fun p hp => lt_trans hc₀c (hlvl t.2 ht2 p hp)))
      hg hg'
  · intro t t' ht ht' hg hg'
    exact hU₃ t t' (-a) (lt_of_lt_of_le ht hb₃) (lt_of_lt_of_le ht' hb₃)
      (by rw [dist_self]; exact hδ₃) hg hg'
  · intro t t' ht ht' hg hg'
    exact hU₄ t t' (-a) (lt_of_lt_of_le ht hb₄) (lt_of_lt_of_le ht' hb₄)
      (by rw [dist_self]; exact hδ₄) hg hg'
  · intro t ht hg hg'
    have htεl : ‖t‖ < εl := lt_of_lt_of_le ht hbl
    have ht1 : ‖t.1‖ < εl := lt_of_le_of_lt (norm_fst_le t) htεl
    have ht2 : ‖t.2‖ < εl := lt_of_le_of_lt (norm_snd_le t) htεl
    exact odd_CntAt_eq_of_goodAt_of_levels (fun s p => chartPert s p) Q c c₁ (-a) t hc hc₁
      (levelLoop_pertChart _ Q c t.1 (fun p hp => hlvl t.1 ht1 p hp))
      (levelLoop_pertChart _ Q c₁ t.1 (fun p hp => lt_trans hc₁c (hlvl t.1 ht1 p hp)))
      (level_rotPresentation_pertChart _ Q c t.2 (-a) (fun p hp => hlvl t.2 ht2 p hp))
      (level_rotPresentation_pertChart _ Q c₁ t.2 (-a)
        (fun p hp => lt_trans hc₁c (hlvl t.2 ht2 p hp)))
      hg hg'

/-- **The truncation levels of the design** `![c/2, c/3, c/4]` are positive. -/
lemma hn2cblk_pos {c : ℝ} (hc : 0 < c) : ∀ k : Fin 3, 0 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k := by
  intro k
  fin_cases k <;> norm_num <;> linarith

/-- **The truncation levels of the design** `![c/2, c/3, c/4]` are strictly below `c`. -/
lemma hn2cblk_lt {c : ℝ} (hc : 0 < c) :
    ∀ k : Fin 3, (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k < c := by
  intro k
  fin_cases k <;> norm_num <;> linarith

/-- The truncation levels of the design are strictly below the first one. -/
lemma hn2cblk_lt_zero {c : ℝ} (hc : 0 < c) {k : Fin 3} (hk : k ≠ 0) :
    (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) k < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 := by
  fin_cases k
  · exact absurd rfl hk
  · norm_num; linarith
  · norm_num; linarith



/-! ## A second route to the class-triple parity: the collision data

`Work.Drive.sum_bottomBdryMeet_clampedSweep_eq_one_local` computes the **end contribution** of the
radial sweeps of three plane presentations *exactly* (`= 1`), from the collision data: a unique class
`q` common to the three class images, attained at a unique box point of each plane, and no other common
class.  Since the block-`0` bottom triple points are in bijection with the class triples
(`Work.Drive.EndDesign.ncard_bottomBdryMeet_zero_eq_ncard_classTripleSet`) and the other two bottom
counts vanish under the level trichotomy (`bottomBdryMeet_eq_empty_of_lt_level_local`), that computation
*is* `#(classTripleSet) = 1`, i.e. the class-triple parity of the ends clause — **without**
`HasClassLinearization` and without the encoded chains.  This is recorded here because it is the one
cheap sufficient condition for `hodd` that the workspace's lemmas already provide. -/
theorem odd_ncard_classTripleSet_of_collisionData
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (c : Fin 3 → ℝ) (hcpos : ∀ k : Fin 3, 0 < c k) (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (q : Projectivization ℝ (Eucl 3))
    (hy : ∀ k, ∃! y : EuclideanSpace ℝ (Fin 2), y ∈ Submission.Drive.unitBox 1 ∧
      (cappingSpaceHomeoProj (P k y)).2 = q)
    (huniq : ∀ q' : Projectivization ℝ (Eucl 3),
      (∀ k, ∃ y ∈ Submission.Drive.unitBox 1, (cappingSpaceHomeoProj (P k y)).2 = q') → q' = q) :
    Odd (classTripleSet P).ncard := by
  classical
  set ψ : ℝ → ℝ := fun t => 1 - t with hψdef
  have hψ0 : ψ 0 = 1 := by simp [hψdef]
  have hψ1 : ψ 1 = 0 := by simp [hψdef]
  have hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨by simp only [hψdef]; linarith [ht.2], by simp only [hψdef]; linarith [ht.1]⟩
  have hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    rw [hψdef]
    exact (continuous_const.sub continuous_id).continuousOn
  have hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    simp only [hψdef]
    linarith
  have hbot := sum_bottomBdryMeet_clampedSweep_eq_one_local c hcpos hc1 hc2 ψ hψ0 hψ1 hψ01
    hcont hanti P hlev q hy huniq
  let D : EndDesign P :=
    { c := c
      psi := ψ
      hcpos := hcpos
      hcne := by
        intro k hk
        fin_cases k
        · exact absurd rfl hk
        · exact hc1
        · exact hc2
      hlev := hlev
      hψ0 := hψ0
      hψ1 := hψ1
      hψ01 := hψ01
      hcont := hcont
      hanti := hanti }
  have hlev' : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c k ≤ levelOf (P k y) := by
    intro k y
    fin_cases k
    · exact le_of_lt (hlev 0 y)
    · exact le_trans (le_of_lt hc1) (le_of_lt (hlev 1 y))
    · exact le_trans (le_of_lt hc2) (le_of_lt (hlev 2 y))
  have hbot1 : bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local c hcpos ψ hψ0 hψ01 P hlev' (k := 1) (l := 0) hc1
  have hbot2 : bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local c hcpos ψ hψ0 hψ01 P hlev' (k := 2) (l := 0) hc2
  have hcard := D.ncard_bottomBdryMeet_zero_eq_ncard_classTripleSet
  have hone : (classTripleSet P).ncard = 1 := by
    rw [hcard]
    change (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard = 1
    rw [← hbot]
    simp only [hbot1, hbot2, Set.ncard_empty, add_zero]
  rw [hone]
  exact ⟨0, rfl⟩

/-- **The germ antisymmetry at an angle, for the concrete family `chartPert`.**  This is
`Work.Drive.hn2_sideGerm_off_half` specialised to the canonical chart perturbation and proved from the
one-parameter reference-triple producer `Work.Drive.hn2_refTripleAt_producer` (rather than from the
existential family-independence `Work.Drive.sideGerm_indep`). -/
theorem hn2_germ_antisym {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγsmooth : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγinj : Function.Injective γ) {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (c : ℝ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Zc γ →
      Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)) :
    ∀ u v : UnitAddCircle, v - u ∈ Zc γ →
      v - u ≠ (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) →
      sideGerm (fun s p => chartPert s p) Q c (v - u)
        + sideGerm (fun s p => chartPert s p) Q c (u - v) = 1 := by
  intro u v hu hne
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  obtain ⟨lam, hlam, φ, _habove, hprod⟩ :=
    hn2_refTripleAt_producerHuv hγsmooth hγinj hQ c hc hcbot hdisjZc u v hu
  obtain ⟨ε, hε, hUa, hUa', hparA, hUn, hUn', hparN⟩ :=
    exists_germLocalityTwo hγinj hQ c hc hcbot (c / 3) (c / 2) (by linarith) (by linarith)
      (by linarith) (by linarith) (v - u) hu
  obtain ⟨t, ht, hgen⟩ := hprod ε hε
  have hc1 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 1 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 := by
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    linarith
  have hc2 : (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 2 < (![c / 2, c / 3, c / 4] : Fin 3 → ℝ) 0 := by
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Matrix.cons_val_zero]
    linarith
  exact sideGerm_add_neg_eq_one_of_refTripleOneT_guarded hΞc hQd c hc
    (diskPlane (linPlaneChart (φ 2) lam hlam)) u v (![c / 2, c / 3, c / 4] : Fin 3 → ℝ)
    (hn2cblk_pos hc) hc1 hc2 hε hUa hUa' hparA hUn hUn' hparN
    ⟨t, ht, hgen⟩

theorem hn2_refCountExists {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγsm : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {c : ℝ}
    (hc : 0 < c) (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q)) :
    ∀ ε : ℝ, 0 < ε → ∀ a : UnitAddCircle, a ∈ Work.Drive.Zc γ →
      a ≠ (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) →
      ∃ t t' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
        ‖t‖ < ε ∧ ‖t'‖ < ε ∧
        Work.Drive.GoodAt (fun s p => Work.Drive.chartPert s p) Q c a t ∧
        Work.Drive.GoodAt (fun s p => Work.Drive.chartPert s p) Q c (-a) t' ∧
        Odd (Work.Drive.CntAt (fun s p => Work.Drive.chartPert s p) Q c a t
          + Work.Drive.CntAt (fun s p => Work.Drive.chartPert s p) Q c (-a) t') := by
  intro ε hε a ha hne
  have hγinj : Function.Injective γ := hγsm.isEmbedding.injective
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  have hΞ : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  -- the germ antisymmetry at the two angles
  have hanti : sideGerm (fun s p => chartPert s p) Q c a
      + sideGerm (fun s p => chartPert s p) Q c (-a) = 1 := by
    have h := hn2_germ_antisym (γ := γ) (hγne := hγne) hγsm hγinj hQ c hc hcbot hdisjZc 0 a
      (by simpa using ha) (by simpa using hne)
    simpa using h
  -- good configurations accumulate at `0` at both angles
  have hEa : ∃ᶠ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) in 𝓝 0,
      GoodAt (fun s p => chartPert s p) Q c a t :=
    sideGerm_good_exists (fun s p => chartPert s p) Q c hΞ hQsm hc a
  have hEn : ∃ᶠ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) in 𝓝 0,
      GoodAt (fun s p => chartPert s p) Q c (-a) t :=
    sideGerm_good_exists (fun s p => chartPert s p) Q c hΞ hQsm hc (-a)
  -- the ball condition
  have hball : ∀ᶠ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) in 𝓝 0, ‖t‖ < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4))
      hε] with t ht
    rwa [Metric.mem_ball, dist_zero_right] at ht
  by_cases h1 : sideGerm (fun s p => chartPert s p) Q c a = 1
  · -- the angle `a` has odd counts at every good configuration near `0`;
    -- the angle `-a` has good configurations of even count
    have hn0 : sideGerm (fun s p => chartPert s p) Q c (-a) ≠ 1 := by
      intro hc1
      rw [h1, hc1] at hanti
      exact absurd hanti (by decide)
    -- the angle `a`: a good configuration of odd count, of norm `< ε`
    have hodd : ∀ᶠ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) in 𝓝 0,
        GoodAt (fun s p => chartPert s p) Q c a t →
          Odd (CntAt (fun s p => chartPert s p) Q c a t) :=
      (sideGerm_eq_iff (fun s p => chartPert s p) Q c a).mp h1
    obtain ⟨t, hgt, hoddimp, ht⟩ := (hEa.and_eventually (hodd.and hball)).exists
    have hoddt : Odd (CntAt (fun s p => chartPert s p) Q c a t) := hoddimp hgt
    have htε : ‖t‖ < ε := ht
    -- the angle `-a`: a good configuration of even count, of norm `< ε`
    have heven : ∃ᶠ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) in 𝓝 0,
        GoodAt (fun s p => chartPert s p) Q c (-a) t ∧
          Even (CntAt (fun s p => chartPert s p) Q c (-a) t) :=
      not_not.mp ((sideGerm_eq_one_iff (fun s p => chartPert s p) Q c (-a)).not.mp hn0)
    obtain ⟨t', ⟨hgt', hevent'⟩, ht'⟩ := (heven.and_eventually hball).exists
    have ht'ε : ‖t'‖ < ε := ht'
    refine ⟨t, t', htε, ht'ε, hgt, hgt', ?_⟩
    exact hoddt.add_even hevent'
  · -- the angle `a` has good configurations of even count, the angle `-a` of odd count
    have h0 : sideGerm (fun s p => chartPert s p) Q c a = 0 := zmod2_eq_zero_of_ne_one h1
    have hn1 : sideGerm (fun s p => chartPert s p) Q c (-a) = 1 := by
      rw [h0, zero_add] at hanti
      exact hanti
    -- the angle `a`: a good configuration of even count, of norm `< ε`
    have heven : ∃ᶠ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) in 𝓝 0,
        GoodAt (fun s p => chartPert s p) Q c a t ∧
          Even (CntAt (fun s p => chartPert s p) Q c a t) :=
      not_not.mp ((sideGerm_eq_one_iff (fun s p => chartPert s p) Q c a).not.mp h1)
    obtain ⟨t, ⟨hgt, hevent⟩, ht⟩ := (heven.and_eventually hball).exists
    have htε : ‖t‖ < ε := ht
    -- the angle `-a`: a good configuration of odd count, of norm `< ε`
    have hodd : ∀ᶠ t : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) in 𝓝 0,
        GoodAt (fun s p => chartPert s p) Q c (-a) t →
          Odd (CntAt (fun s p => chartPert s p) Q c (-a) t) :=
      (sideGerm_eq_iff (fun s p => chartPert s p) Q c (-a)).mp hn1
    obtain ⟨t', hgt', hoddimp', ht'⟩ := (hEn.and_eventually (hodd.and hball)).exists
    have hoddt' : Odd (CntAt (fun s p => chartPert s p) Q c (-a) t') := hoddimp' hgt'
    have ht'ε : ‖t'‖ < ε := ht'
    refine ⟨t, t', htε, ht'ε, hgt, hgt', ?_⟩
    exact hevent.add_odd hoddt'

end

end Work.Drive
