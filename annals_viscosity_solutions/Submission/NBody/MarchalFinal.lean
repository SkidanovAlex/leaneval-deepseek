import Submission.NBody.MarchalEndgameFinal
import Submission.NBody.MarchalIsolatedMulti
import Submission.NBody.MarchalCollClass
import Submission.NBody.MadernaEstimate
import Submission.NBody.Assembly

/-!
# Marchal's theorem: an action-minimising motion has no interior collision

This module assembles the isolated-collision endgame into Marchal's theorem:

* `exists_withoutCollisions_mem_Ioc_left/right` — the collision times of a finite-action minimiser
  are null, so there are collision-free times arbitrarily close to any collision;
* `marchal_property` — `NBody.MarchalProperty m h`, for `0 < h` and `2 ≤ finrank ℝ E`.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- There is a collision-free time just below a given time. -/
lemma exists_withoutCollisions_mem_Ioc_left {γ : ℝ → EN E N} {a b t : ℝ}
    (hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ s)) (hat : a < t)
    (htb : t ≤ b) : ∃ c ∈ Set.Ioc a t, WithoutCollisions (γ c) := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioc a t ⊆ Set.Ioc a b := fun s hs => ⟨hs.1, le_trans hs.2 htb⟩
  have hae' : ∀ᵐ s ∂(volume.restrict (Set.Ioc a t)), WithoutCollisions (γ s) :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have hfalse : ∀ᵐ s ∂(volume.restrict (Set.Ioc a t)), False :=
    (hae'.and (MeasureTheory.ae_restrict_mem measurableSet_Ioc)).mono
      (fun s hs => hcon s hs.2 hs.1)
  have hzero : volume (Set.Ioc a t) = 0 := by
    have h := MeasureTheory.ae_iff.mp hfalse
    have h2 : {a : ℝ | ¬ False} = Set.univ := by ext a; simp
    rw [h2, MeasureTheory.Measure.restrict_apply_univ] at h
    exact h
  have hpos : (0:ℝ≥0∞) < volume (Set.Ioc a t) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  rw [hzero] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- There is a collision-free time just above a given time. -/
lemma exists_withoutCollisions_mem_Ioc_right {γ : ℝ → EN E N} {a b t : ℝ}
    (hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ s)) (hat : a ≤ t)
    (htb : t < b) : ∃ d ∈ Set.Ioc t b, WithoutCollisions (γ d) := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Ioc t b ⊆ Set.Ioc a b := fun s hs => ⟨lt_of_le_of_lt hat hs.1, hs.2⟩
  have hae' : ∀ᵐ s ∂(volume.restrict (Set.Ioc t b)), WithoutCollisions (γ s) :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have hfalse : ∀ᵐ s ∂(volume.restrict (Set.Ioc t b)), False :=
    (hae'.and (MeasureTheory.ae_restrict_mem measurableSet_Ioc)).mono
      (fun s hs => hcon s hs.2 hs.1)
  have hzero : volume (Set.Ioc t b) = 0 := by
    have h := MeasureTheory.ae_iff.mp hfalse
    have h2 : {a : ℝ | ¬ False} = Set.univ := by ext a; simp
    rw [h2, MeasureTheory.Measure.restrict_apply_univ] at h
    exact h
  have hpos : (0:ℝ≥0∞) < volume (Set.Ioc t b) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  rw [hzero] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **Marchal's theorem.**  For `0 < h` and `2 ≤ finrank ℝ E`, an action-minimising trajectory of
the Newtonian `N`-body problem at level `h` has no interior collision. -/
theorem marchal_property (hErank : 2 ≤ Module.finrank ℝ E) (m : Fin N → ℝ) (hm : ∀ i, 0 < m i)
    {h : ℝ} (hpos : 0 < h) : MarchalProperty (E := E) m h := by
  intro γ a b hab hac hmin
  by_cases hN : N ≤ 1
  · intro t _ i j hij
    exact absurd (Fin.ext (by omega)) hij
  · have hN1 : 0 < N := by omega
    obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) hN1 hm hpos.le
    have hfin : ∀ x y : EN E N, actionPot m h x y < ⊤ :=
      fun x y => lt_of_le_of_lt (hest x y) ENNReal.ofReal_lt_top
    intro t ht
    by_contra hcoll
    have hOn : actionOn m h γ a b < ⊤ := hmin.symm ▸ hfin (γ a) (γ b)
    have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ s) :=
      ae_withoutCollisions_of_actionOn_lt_top hac hOn
    obtain ⟨c, hc, hc'⟩ := exists_withoutCollisions_mem_Ioc_left (γ := γ) (a := a) (b := b)
      (t := t) hae ht.1 (le_of_lt ht.2)
    have hae' : ∀ᵐ s ∂(volume.restrict (Set.Ioc a ((t + b) / 2))), WithoutCollisions (γ s) :=
      ae_restrict_of_ae_restrict_of_subset
        (show Set.Ioc a ((t + b) / 2) ⊆ Set.Ioc a b from
          fun s hs => ⟨hs.1, by linarith [hs.2, ht.2]⟩) hae
    obtain ⟨d, hd, hd'⟩ := exists_withoutCollisions_mem_Ioc_right (γ := γ) (a := a)
      (b := (t + b) / 2) (t := t) hae' (le_of_lt ht.1) (by linarith [ht.2])
    have hct : c < t := by
      rcases lt_trichotomy c t with h | h | h
      · exact h
      · rw [h] at hc'
        exact absurd hc' hcoll
      · exact absurd (lt_of_lt_of_le h hc.2) (lt_irrefl t)
    have hcIoo : c ∈ Ioo a t := ⟨hc.1, hct⟩
    have hdIoo : d ∈ Ioo t b := ⟨hd.1, by linarith [hd.2, ht.2]⟩
    have hcd : c < d := lt_trans hcIoo.2 hdIoo.1
    have hsub : Icc c d ⊆ Ioo a b := fun s hs =>
      ⟨lt_of_lt_of_le hcIoo.1 hs.1, lt_of_le_of_lt hs.2 hdIoo.2⟩
    obtain ⟨t₁, ht₁, hcoll₁, hrest⟩ := exists_isolated_collision_multi hm hpos hab hcd hac hmin
      hfin hsub ⟨t, ⟨hcIoo.2.le, hdIoo.1.le⟩, hcoll⟩
    obtain ⟨η, hηpos, _hηle, hiso⟩ := hrest
    have ht₁c : c < t₁ := by
      rcases lt_or_eq_of_le ht₁.1 with h | h
      · exact h
      · rw [h] at hc'
        exact absurd hc' hcoll₁
    have ht₁d : t₁ < d := by
      rcases lt_or_eq_of_le ht₁.2 with h | h
      · exact h
      · rw [← h] at hd'
        exact absurd hd' hcoll₁
    have ht₁Ioo : t₁ ∈ Ioo a b := hsub ht₁
    have hcontab : ContinuousOn γ (Icc a b) := by
      have h := hac.continuousOn
      rwa [Set.uIcc_of_le hab.le] at h
    obtain ⟨ν, hνpos, ε₀, hε₀pos, hsep⟩ :=
      exists_separation_of_collClasses (γ := γ) (a := a) (b := b) (t₀ := t₁) hcontab ht₁Ioo
    obtain ⟨i₀, j₀, hij₀, heq₀⟩ : ∃ i j, i ≠ j ∧ γ t₁ i = γ t₁ j := by
      by_contra hcon
      push Not at hcon
      exact hcoll₁ (fun i j hij => by
        intro hrij
        have heq : γ t₁ i = γ t₁ j := by
          rw [r_eq_norm_sub] at hrij
          exact sub_eq_zero.mp (norm_eq_zero.mp hrij)
        exact hcon i j hij heq)
    have hkcard : 1 < (collClass γ t₁ i₀).card := by
      rw [Finset.one_lt_card]
      exact ⟨i₀, mem_collClass_self γ t₁ i₀, j₀, mem_collClass.mpr heq₀.symm, hij₀⟩
    have hkcard2 : 2 ≤ (collClass γ t₁ i₀).card := by have := hkcard; omega
    have hk_mem : collClass γ t₁ i₀ ∈ collClasses γ t₁ := mem_collClasses.mpr ⟨i₀, rfl, hkcard2⟩
    have hI0_0 : clusterInertia m (collClass γ t₁ i₀) (γ t₁) = 0 :=
      clusterInertia_collClass_eq_zero
        (clusterMass_pos hm (Finset.card_pos.mp (by have := hkcard; omega))).ne'
    set k : Finset (Fin N) := collClass γ t₁ i₀ with hkdef
    have hk2 : 2 ≤ k.card := collClasses_card hk_mem
    have hI0 : clusterInertia m k (γ t₁) = 0 := hI0_0
    set ε₂ : ℝ := min (min η (min (t₁ - c) (d - t₁)))
      (min ε₀ (min ((t₁ - a) / 2) ((b - t₁) / 2))) with hε₂def
    have hε₂pos : 0 < ε₂ := by
      rw [hε₂def]
      exact lt_min (lt_min hηpos (lt_min (by linarith) (by linarith)))
        (lt_min hε₀pos (lt_min (by linarith [ht₁Ioo.1]) (by linarith [ht₁Ioo.2])))
    have hε₂η : ε₂ ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
    have hε₂c : ε₂ ≤ t₁ - c :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε₂d : ε₂ ≤ d - t₁ :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hε₂₀ : ε₂ ≤ ε₀ := le_trans (min_le_right _ _) (min_le_left _ _)
    have hε₂a : ε₂ ≤ (t₁ - a) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hε₂b : ε₂ ≤ (b - t₁) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hmemcd : ∀ s : ℝ, t₁ < s → s < t₁ + ε₂ → s ∈ Icc c d := fun s hs1 hs2 =>
      ⟨(lt_trans ht₁c hs1).le, by linarith [hs2, hε₂d]⟩
    have hmemcdL : ∀ s : ℝ, t₁ - ε₂ < s → s < t₁ → s ∈ Icc c d := fun s hs1 hs2 =>
      ⟨by linarith [hs1, hε₂c], (lt_trans hs2 ht₁d).le⟩
    have hncR : ∀ s ∈ Ioo t₁ (t₁ + ε₂), WithoutCollisions (γ s) := by
      intro s hs
      refine hiso s (hmemcd s hs.1 hs.2) ?_ ?_
      · rw [abs_of_pos (sub_pos.mpr hs.1)]
        exact lt_of_lt_of_le (by linarith [hs.2]) hε₂η
      · exact ne_of_gt hs.1
    have hncL : ∀ s ∈ Ioo (t₁ - ε₂) t₁, WithoutCollisions (γ s) := by
      intro s hs
      refine hiso s (hmemcdL s hs.1 hs.2) ?_ ?_
      · rw [abs_of_neg (sub_neg.mpr hs.2)]
        exact lt_of_lt_of_le (by linarith [hs.1]) hε₂η
      · exact ne_of_lt hs.2
    have hmemsepR : ∀ s ∈ Ioo t₁ (t₁ + ε₂), s ∈ Ioo (t₁ - ε₀) (t₁ + ε₀) := fun s hs =>
      ⟨by linarith [hs.1, hε₂₀], by linarith [hs.2, hε₂₀]⟩
    have hmemsepL : ∀ s ∈ Ioo (t₁ - ε₂) t₁, s ∈ Ioo (t₁ - ε₀) (t₁ + ε₀) := fun s hs =>
      ⟨by linarith [hs.1, hε₂₀], by linarith [hs.2, hε₂₀]⟩
    have hsepwR : ∀ s ∈ Ioo t₁ (t₁ + ε₂), ClusterSeparatedWeak k (γ s) ν := fun s hs =>
      (hsep s (hmemsepR s hs)).1 k hk_mem
    have hsepwL : ∀ s ∈ Ioo (t₁ - ε₂) t₁, ClusterSeparatedWeak k (γ s) ν := fun s hs =>
      (hsep s (hmemsepL s hs)).1 k hk_mem
    exact isHMinimizer_false_of_isolated_collision (m := m) (h := h) (γ := γ) (a := a) (b := b)
      (t₀ := t₁) (k := k) hm hpos hab hErank hk2 hac hmin hfin ht₁Ioo hε₂pos
      (by linarith [hε₂a]) (by linarith [hε₂b]) hncR hncL hcoll₁ hνpos hsepwR hsepwL hI0

end Submission.NBody
