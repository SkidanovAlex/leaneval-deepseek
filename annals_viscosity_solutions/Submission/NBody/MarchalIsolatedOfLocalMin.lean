import Submission.NBody.MarchalIsolatedCollision
import Submission.NBody.MarchalCollClass
import Submission.NBody.MarchalCollisionSolutionData
import Submission.NBody.EnergyAe

/-!
# A locally minimal collision is isolated (assembly)

This file assembles the isolatedness theorem from the two preceding layers:

* `MarchalIsolatedCollision.exists_local_min_collision` — the existence of a collision time whose
  collision classes are locally constant (minimising the number of colliding pairs);
* `MarchalIsolatedCollision.exists_no_sandwich_of_sperner` — the Rolle--Sperner step, showing that
  two zeros of `I_k ∘ γ` cannot sandwich a positive value near such a collision;
* the density of `{I_k > 0}` — a consequence of the finiteness of the action.

The relative-energy bound `hE` is the only analytic input left; it is supplied (for a colliding
minimiser) by the multi-cluster analysis.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **A locally minimal collision is isolated.**  Let `γ` be an `h`-minimiser on `[a,b]`, `t₁` a
collision time in `[c,d] ⊆ (a,b)` whose collision class `k = collClass γ t₁ i₁` is subject to the
local minimality property (every nearby collision makes all of `k` collide) and whose relative
energy is bounded below on `{I_k > 0}`.  Then `t₁` is the only collision time of `Icc c d` close to
it. -/
theorem isolated_of_local_min {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b c d t₁ C₁ : ℝ}
    {i₁ : Fin N} (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (hcd : Icc c d ⊆ Ioo a b) (ht₁ : t₁ ∈ Icc c d)
    (hk2 : 2 ≤ (collClass γ t₁ i₁).card)
    (hloc : ∃ ε > 0, ∀ t ∈ Icc c d, |t - t₁| < ε → (∃ i j, i ≠ j ∧ γ t i = γ t j) →
      ∀ i ∈ collClass γ t₁ i₁, ∀ j ∈ collClass γ t₁ i₁, γ t i = γ t j)
    (hc1 : 0 ≤ C₁)
    (hE : ∀ t ∈ Icc c d, 0 < clusterInertia m (collClass γ t₁ i₁) (γ t) →
      -C₁ ≤ clusterRelEnergy m (collClass γ t₁ i₁) (γ t) (deriv γ t)) :
    ∃ η > 0, η ≤ 1 ∧ ∀ t ∈ Icc c d, |t - t₁| < η → t ≠ t₁ → WithoutCollisions (γ t) := by
  classical
  set k : Finset (Fin N) := collClass γ t₁ i₁ with hkdef
  have hkne : k.Nonempty := ⟨i₁, mem_collClass.mpr rfl⟩
  have hcontab : ContinuousOn γ (Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have ht₁Ioo : t₁ ∈ Ioo a b := hcd ht₁
  have hcontcd : ContinuousOn γ (Icc c d) :=
    hcontab.mono (fun t ht => ⟨(hcd ht).1.le, (hcd ht).2.le⟩)
  obtain ⟨ν, hνpos, ε₀, hε₀pos, hsepc⟩ := exists_clusterSeparatedWeak_of_collClass
    (γ := γ) (a := a) (b := b) (t₀ := t₁) (i₀ := i₁) hcontab ht₁Ioo
  obtain ⟨ε, hεpos, hloc'⟩ := hloc
  set ε' : ℝ := min ε ε₀ with hε'def
  have hε'pos : 0 < ε' := lt_min hεpos hε₀pos
  set W : Set ℝ := Icc c d ∩ Metric.ball t₁ ε' with hWdef
  have ht₁W : t₁ ∈ W := ⟨ht₁, by
    rw [Metric.mem_ball, Real.dist_eq, sub_self, abs_zero]
    exact hε'pos⟩
  have hcontW : ContinuousOn (fun t : ℝ => clusterInertia m k (γ t)) W :=
    ((continuous_clusterInertia m k).comp_continuousOn hcontcd).mono (fun t ht => ht.1)
  -- the collision at `t₁`
  obtain ⟨j₁, hj₁, hj₁ne⟩ : ∃ j ∈ k, j ≠ i₁ := by
    have h1 : 1 < k.card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
    by_cases hqi : q = i₁
    · exact ⟨p, hp, fun hpi => hpq (hpi.trans hqi.symm)⟩
    · exact ⟨q, hq, hqi⟩
  have hij₁ : i₁ ≠ j₁ := fun h => hj₁ne h.symm
  have hcoll₁ : ¬ WithoutCollisions (γ t₁) := by
    intro hnc'
    have heq : γ t₁ i₁ = γ t₁ j₁ := (mem_collClass.mp (hkdef ▸ hj₁)).symm
    exact (hnc' i₁ j₁ hij₁) (by rw [r_eq_norm_sub, heq, sub_self, norm_zero])
  have hF0 : clusterInertia m k (γ t₁) = 0 := by
    rw [clusterInertia_eq_zero_iff hm k (γ t₁)]
    intro i hi j hj
    exact (mem_collClass.mp (hkdef ▸ hi)).trans (mem_collClass.mp (hkdef ▸ hj)).symm
  -- the local structure of the zeros of `F`
  have hzero : ∀ t ∈ W, (∃ i j, i ≠ j ∧ γ t i = γ t j) →
      clusterInertia m k (γ t) = 0 := by
    intro t ht hcol
    have hlt_ε : |t - t₁| < ε := by
      have hb : t ∈ Metric.ball t₁ ε' := ht.2
      rw [Metric.mem_ball, Real.dist_eq] at hb
      exact lt_of_lt_of_le hb (min_le_left ε ε₀)
    have hall := hloc' t ht.1 hlt_ε hcol
    rw [clusterInertia_eq_zero_iff hm k (γ t)]
    exact hall
  have hncW : ∀ t ∈ W, 0 < clusterInertia m k (γ t) → WithoutCollisions (γ t) := by
    intro t ht hFt
    by_contra hcol
    have h1 : ∃ i j, i ≠ j ∧ γ t i = γ t j := by
      by_contra h
      exact hcol fun i j hij hr => h ⟨i, j, hij, by
        rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hr
        exact hr⟩
    exact absurd (hzero t ht h1) (ne_of_gt hFt)
  -- the Newton data on `{F > 0}`
  have hsolW : ∀ t ∈ W, 0 < clusterInertia m k (γ t) →
      (∀ᶠ s in 𝓝 t, HasDerivAt γ (deriv γ s) s) ∧
      HasDerivAt (deriv γ) (iteratedDeriv 2 γ t) t ∧
      iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t) := by
    intro t ht hFt
    have h := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
      (S := {s : ℝ | s ∈ W ∧ 0 < clusterInertia m k (γ s)})
      (fun s hs => hcd hs.1.1)
      (fun s hs => hncW s hs.1 hs.2)
    exact h t ⟨ht, hFt⟩
  -- the one-sided separation
  have hsepW : ∀ t ∈ W, 0 < clusterInertia m k (γ t) → ClusterSeparatedWeak k (γ t) ν := by
    intro t ht _
    have hb : t ∈ Metric.ball t₁ ε' := ht.2
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have hlt : |t - t₁| < ε₀ := lt_of_lt_of_le hb (min_le_right ε ε₀)
    have hmem : t ∈ Ioo (t₁ - ε₀) (t₁ + ε₀) := by
      rw [abs_lt] at hlt
      exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
    exact hsepc t hmem
  -- the no-sandwich statement
  obtain ⟨ηs, hηspos, hηs1, hns⟩ := exists_no_sandwich_of_sperner (m := m) (k := k) (γ := γ)
    (W := W) (t₁ := t₁) (ν := ν) (C₁ := C₁) hm hkne (by omega) hcontW ht₁W hF0 hncW hsolW
    hνpos hsepW hc1 (fun t ht hFt => hE t ht.1 hFt)
  -- the density of `{F > 0}`
  have hfinOn : actionOn m h γ a b < ⊤ :=
    IsHMinimizer.actionOn_lt_top hmin (hfin (γ a) (γ b))
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t) :=
    ae_withoutCollisions_of_actionOn_lt_top hac hfinOn
  have hnull : volume ({t : ℝ | ¬ WithoutCollisions (γ t)} ∩ Ioo a b) = 0 := by
    have h1 : volume (({t : ℝ | ¬ WithoutCollisions (γ t)}) ∩ Set.Ioc a b) = 0 := by
      have h2 := MeasureTheory.ae_iff.mp hae
      simpa [Set.inter_comm] using h2
    refine measure_mono_null ?_ h1
    exact Set.inter_subset_inter_right _ (fun t ht => ⟨ht.1, ht.2.le⟩)
  -- the density of `{F > 0}` inside the window
  have hdensity : ∀ a' b' : ℝ, a' < b' → Icc a' b' ⊆ W → |a' - t₁| < ηs → |b' - t₁| < ηs →
      ∃ x ∈ Ioo a' b', 0 < clusterInertia m k (γ x) := by
    intro a' b' hab' hsub _ _
    have hdom : Ioo a' b' ⊆ Ioo a b := fun x hx =>
      hcd (hsub (Set.Ioo_subset_Icc_self hx)).1
    have hnull' : volume ({y : ℝ | ¬ WithoutCollisions (γ y)} ∩ Ioo a' b') = 0 :=
      measure_mono_null (Set.inter_subset_inter_right _ hdom) hnull
    have hpos' : (0:ℝ≥0∞) < volume (Ioo a' b') := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    obtain ⟨x, hx, hxnot⟩ :
        ∃ x ∈ Ioo a' b', x ∉ ({y : ℝ | ¬ WithoutCollisions (γ y)} ∩ Ioo a' b') := by
      by_contra h
      push Not at h
      have hsub' : Ioo a' b' ⊆ ({y : ℝ | ¬ WithoutCollisions (γ y)} ∩ Ioo a' b') :=
        fun x hx => h x hx
      have hz : volume (Ioo a' b') = 0 := measure_mono_null hsub' hnull'
      rw [hz] at hpos'
      exact absurd hpos' (lt_irrefl 0)
    have hncx : WithoutCollisions (γ x) := by
      by_contra hxc
      exact hxnot ⟨hxc, hx⟩
    have hne0 : clusterInertia m k (γ x) ≠ 0 := by
      intro h0
      have hall := (clusterInertia_eq_zero_iff hm k (γ x)).mp h0
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < k.card)
      exact (hncx i j hij) (by rw [r_eq_norm_sub, hall i hi j hj, sub_self, norm_zero])
    exact ⟨x, hx, lt_of_le_of_ne (clusterInertia_nonneg (fun i => (hm i).le) k (γ x))
      (Ne.symm hne0)⟩
  -- the conclusion
  refine ⟨min ηs ε', lt_min hηspos hε'pos, le_trans (min_le_left _ _) hηs1, ?_⟩
  intro t htcd htlt htne
  by_contra hcol
  have hltηs : |t - t₁| < ηs := lt_of_lt_of_le htlt (min_le_left _ _)
  have hltε' : |t - t₁| < ε' := lt_of_lt_of_le htlt (min_le_right _ _)
  have htW : t ∈ W := ⟨htcd, by rw [Metric.mem_ball, Real.dist_eq]; exact hltε'⟩
  have hcol' : ∃ i j, i ≠ j ∧ γ t i = γ t j := by
    by_contra h
    exact hcol fun i j hij hr => h ⟨i, j, hij, by
      rw [r_eq_norm_sub, norm_eq_zero, sub_eq_zero] at hr
      exact hr⟩
  have hFt : clusterInertia m k (γ t) = 0 := hzero t htW hcol'
  rcases lt_or_gt_of_ne htne with hlt | hgt
  · -- `t < t₁`
    have hsub : Icc t t₁ ⊆ W := by
      intro u hu
      have hut : t ≤ u := (Set.mem_Icc.mp hu).1
      have huu : u ≤ t₁ := (Set.mem_Icc.mp hu).2
      refine ⟨⟨le_trans htcd.1 hut, le_trans huu ht₁.2⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have h2u : u - t₁ ≤ 0 := by linarith
      have h2t : t - t₁ ≤ 0 := by linarith
      have h1 : |u - t₁| ≤ |t - t₁| := by
        rw [abs_of_nonpos h2u, abs_of_nonpos h2t]
        linarith
      linarith [h1, hltε']
    have hd := hdensity t t₁ hlt hsub hltηs (by simpa using hηspos)
    exact hns t t₁ hlt hsub hltηs (by simpa using hηspos) hFt hF0 hd
  · -- `t₁ < t`
    have hsub : Icc t₁ t ⊆ W := by
      intro u hu
      have hut : t₁ ≤ u := (Set.mem_Icc.mp hu).1
      have huu : u ≤ t := (Set.mem_Icc.mp hu).2
      refine ⟨⟨le_trans ht₁.1 hut, le_trans huu htcd.2⟩, ?_⟩
      rw [Metric.mem_ball, Real.dist_eq]
      have h2u : 0 ≤ u - t₁ := by linarith
      have h2t : 0 ≤ t - t₁ := by linarith
      have h1 : |u - t₁| ≤ |t - t₁| := by
        rw [abs_of_nonneg h2u, abs_of_nonneg h2t]
        linarith
      linarith [h1, hltε']
    have hd := hdensity t₁ t hgt hsub (by simpa using hηspos) hltηs
    exact hns t₁ t hgt hsub (by simpa using hηspos) hltηs hF0 hFt hd

end Submission.NBody
