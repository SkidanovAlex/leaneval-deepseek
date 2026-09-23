import Mathlib
import Submission.Commons.Topology.Order.strictMonoOn_of_left_lt
import Submission.Commons.Topology.Order.Ioo_mem_nhdsWithin_lt
import Submission.Commons.Topology.Order.Ioo_mem_nhdsWithin_gt
import Submission.Commons.Topology.homeo_level_times_of_flow_crossing

/-!
# The level-set (crossing) structure of a function without critical points

Abstract topological engine behind Grove--Shiohama's step 3(b).  Let `X` be a compact Hausdorff
space, `f : X → ℝ` continuous, and `φ` a continuous flow on `X` (`φ x 0 = x`, the semigroup law)
which is *strictly increasing* along `f` on the region `T = {a' ≤ f ≤ b'}`: at every point `y ∈ T`
the backward trajectory lowers `f`:
`∃ δ > 0, ∀ s ∈ (0,δ), f (φ y (-s)) < f y`.

Then, for levels `a' < a < b < b'`, every level `ℓ ∈ [a,b]` is crossed exactly once by the
trajectory of every point of the slab `{a ≤ f ≤ b}`, and the crossing times are uniformly bounded.

The mathematical content is the classical "no critical point" argument; the only non-elementary
ingredient is the barrier lemma (`barrier`), which forbids returning to a level from above.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Set Function Filter
open scoped Topology

namespace Submission.GSCross

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
variable {f : X → ℝ} {φ : X → ℝ → X} {a' b' : ℝ}

/-- The trajectory of a point is continuous. -/
lemma continuous_traj (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2) (x : X) :
    Continuous fun t : ℝ => φ x t :=
  hφcont.comp (continuous_const.prodMk continuous_id)

section Basic

variable (hf : Continuous f) (hφ0 : ∀ x : X, φ x 0 = x)
variable (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
variable (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
variable (hT : ∀ y : X, a' ≤ f y → f y ≤ b' →
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ, f (φ y (-s)) < f y)

include hf hφ0 hφadd hφcont hT

/-- **Strict monotonicity along a trajectory inside the region.** -/
lemma strictMonoOn_traj {x : X} {u v : ℝ} (huv : u ≤ v)
    (hW : ∀ t ∈ Icc u v, a' ≤ f (φ x t) ∧ f (φ x t) ≤ b') :
    StrictMonoOn (fun t : ℝ => f (φ x t)) (Icc u v) := by
  refine Commons.Topology.Order.strictMonoOn_of_left_lt huv ?_ ?_
  · exact (hf.comp (continuous_traj hφcont x)).continuousOn
  · intro t ht
    obtain ⟨δ, hδ, hδ'⟩ := hT (φ x t) (hW t ht).1 (hW t ht).2
    refine ⟨δ, hδ, fun ε hε => ?_⟩
    have h1 : f (φ (φ x t) (-ε)) < f (φ x t) := hδ' ε hε
    have h2 : φ (φ x t) (-ε) = φ x (t - ε) := by
      rw [hφadd x t (-ε), sub_eq_add_neg]
    rw [h2] at h1
    exact h1

/-- **The barrier lemma**: a trajectory cannot be above a level `c ∈ [a',b']` at some time and at
or below it at a later time.  Equivalently, the set `{t | c < f (φ x t)}` is an upper ray. -/
lemma barrier {c : ℝ} (hc : a' ≤ c) (hc' : c ≤ b') {x : X} {t t' : ℝ} (htt : t < t')
    (h1 : c < f (φ x t)) (h2 : f (φ x t') ≤ c) : False := by
  -- the first time after `t` at which the trajectory is at or below `c`
  set S : Set ℝ := {s : ℝ | t ≤ s ∧ f (φ x s) ≤ c} with hSdef
  have hSne : S.Nonempty := ⟨t', htt.le, h2⟩
  have hSbdd : BddBelow S := ⟨t, fun s hs => hs.1⟩
  have hSclosed : IsClosed S := by
    rw [hSdef]
    exact isClosed_Ici.inter
      (isClosed_le ((hf.comp (continuous_traj hφcont x)).comp continuous_id) continuous_const)
  have hw : sInf S ∈ S := hSclosed.csInf_mem hSne hSbdd
  obtain ⟨hwt, hwf⟩ : t ≤ sInf S ∧ f (φ x (sInf S)) ≤ c := hw
  have hwgt : t < sInf S := by
    rcases lt_or_eq_of_le hwt with h | h
    · exact h
    · exfalso; rw [← h] at hwf; exact absurd h1 (not_lt.mpr hwf)
  -- from the left, the trajectory is strictly above `c`
  have hleft : ∀ s ∈ Ioo t (sInf S), c < f (φ x s) := by
    intro s hs
    by_contra hcon
    have hsR : s ∈ S := ⟨hs.1.le, not_lt.mp hcon⟩
    have := csInf_le hSbdd hsR
    exact absurd this (not_le.mpr hs.2)
  have heq : f (φ x (sInf S)) = c := by
    refine le_antisymm hwf ?_
    have htend : Filter.Tendsto (fun s : ℝ => f (φ x s)) (𝓝[<] (sInf S))
        (𝓝 (f (φ x (sInf S)))) :=
      ((hf.comp (continuous_traj hφcont x)).continuousAt).tendsto.mono_left inf_le_left
    have hge : ∀ᶠ s in 𝓝[<] (sInf S), c ≤ f (φ x s) := by
      filter_upwards [Commons.Topology.Order.Ioo_mem_nhdsWithin_lt hwgt] with s hs
      exact le_of_lt (hleft s hs)
    exact ge_of_tendsto htend hge
  -- the local ascent condition at the crossing point
  have hmem : a' ≤ f (φ x (sInf S)) ∧ f (φ x (sInf S)) ≤ b' := by
    rw [heq]; exact ⟨hc, hc'⟩
  obtain ⟨δ, hδ, hδ'⟩ := hT (φ x (sInf S)) hmem.1 hmem.2
  set ε : ℝ := min δ (sInf S - t) / 2 with hεdef
  have hεpos : 0 < ε := by
    have : 0 < min δ (sInf S - t) := lt_min hδ (by linarith)
    simp only [hεdef]; linarith
  have hεδ : ε < δ := by
    have : min δ (sInf S - t) ≤ δ := min_le_left _ _
    simp only [hεdef]; linarith
  have hεt : ε < sInf S - t := by
    have : min δ (sInf S - t) ≤ sInf S - t := min_le_right _ _
    simp only [hεdef]; linarith
  have hlt : f (φ x (sInf S - ε)) < c := by
    have h1' : f (φ (φ x (sInf S)) (-ε)) < f (φ x (sInf S)) := hδ' ε ⟨hεpos, hεδ⟩
    have h2 : φ (φ x (sInf S)) (-ε) = φ x (sInf S - ε) := by
      rw [hφadd x (sInf S) (-ε), sub_eq_add_neg]
    rw [h2, heq] at h1'
    exact h1'
  have hgt : c < f (φ x (sInf S - ε)) :=
    hleft _ ⟨by linarith, by linarith⟩
  linarith

end Basic

section Basic2

variable (hf : Continuous f) (hφ0 : ∀ x : X, φ x 0 = x)
variable (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
variable (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
variable (hT : ∀ y : X, a' ≤ f y → f y ≤ b' →
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ, f (φ y (-s)) < f y)
variable (ha'b' : a' < b')

include hf hφ0 hφadd hφcont hT ha'b'

/-- **The lower barrier**: if `a' < f x` then the trajectory of `x` never goes below `a'`. -/
lemma le_a'_forward {x : X} (hx : a' < f x) : ∀ t : ℝ, 0 ≤ t → a' ≤ f (φ x t) := by
  intro t ht
  by_contra hcon
  have hlt : f (φ x t) < a' := lt_of_not_ge hcon
  have ht0 : 0 < t := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso; rw [← h, hφ0] at hlt; linarith
  exact barrier hf hφ0 hφadd hφcont hT (le_refl a') ha'b'.le ht0
    (by rw [hφ0]; exact hx) (le_of_lt hlt)

/-- **The upper barrier, backwards**: if `f x ≤ b'` then the trajectory of `x` was never above
`b'` in the past. -/
lemma le_b'_backward {x : X} (hx : f x ≤ b') : ∀ t : ℝ, t ≤ 0 → f (φ x t) ≤ b' := by
  intro t ht
  by_contra hcon
  have hlt : b' < f (φ x t) := lt_of_not_ge hcon
  have ht0 : t < 0 := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso; rw [h, hφ0] at hlt; linarith
  exact barrier hf hφ0 hφadd hφcont hT ha'b'.le (le_refl b') ht0 hlt (by rw [hφ0]; exact hx)

/-- **Once above `b'`, always above `b'`.** -/
lemma gt_b'_forward {x : X} {t₁ t₂ : ℝ} (h : t₁ < t₂) (h1 : b' ≤ f (φ x t₁)) :
    b' < f (φ x t₂) := by
  by_contra hcon
  have h2 : f (φ x t₂) ≤ b' := le_of_not_gt hcon
  have hW : ∀ t ∈ Icc t₁ t₂, a' ≤ f (φ x t) ∧ f (φ x t) ≤ b' := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have hlt : a' < f (φ x t₁) := lt_of_lt_of_le ha'b' h1
      have hb1 := le_a'_forward hf hφ0 hφadd hφcont hT ha'b' hlt (t - t₁) (by linarith [ht.1])
      rwa [hφadd, add_sub_cancel] at hb1
    · have hb2 := le_b'_backward hf hφ0 hφadd hφcont hT ha'b' h2 (t - t₂) (by linarith [ht.2])
      rwa [hφadd, add_sub_cancel] at hb2
  have hmono := strictMonoOn_traj hf hφ0 hφadd hφcont hT h.le hW
  have := hmono (left_mem_Icc.mpr h.le) (right_mem_Icc.mpr h.le) h
  linarith

/-- **The trajectory escapes the region downwards in finite time.**  For `f x ≤ b'` there is a
past time at which the trajectory is at or below `a'`. -/
lemma exists_le_a'_backward {x : X} (hx : f x ≤ b') : ∃ t : ℝ, t ≤ 0 ∧ f (φ x t) ≤ a' := by
  by_contra hcon
  push Not at hcon
  set S : Set X := {y : X | ∃ t : ℝ, t ≤ 0 ∧ φ x t = y} with hSdef
  have hxS : x ∈ S := ⟨0, le_refl 0, hφ0 x⟩
  set K : Set X := closure S with hKdef
  have hKcomp : IsCompact K := by rw [hKdef]; exact isClosed_closure.isCompact
  have hKne : K.Nonempty := ⟨x, by rw [hKdef]; exact subset_closure hxS⟩
  obtain ⟨w, hwK, hwmin⟩ := hKcomp.exists_isMinOn hKne hf.continuousOn
  have hKsub : K ⊆ f ⁻¹' Ici a' := by
    rw [hKdef]
    refine closure_minimal (fun y hy => ?_) (isClosed_Ici.preimage hf)
    obtain ⟨t, ht, rfl⟩ := hy
    exact le_of_lt (hcon t ht)
  have hwx : f w ≤ f x := hwmin (by rw [hKdef]; exact subset_closure hxS)
  have hwb' : f w ≤ b' := le_trans hwx hx
  -- backward invariance of `K`
  have hback : ∀ s : ℝ, s ≤ 0 → φ w s ∈ K := by
    intro s hs
    have hcont' : Continuous fun y : X => φ y s :=
      hφcont.comp (continuous_id.prodMk continuous_const)
    have hmaps : MapsTo (fun y : X => φ y s) S S := by
      rintro y ⟨t, ht, rfl⟩
      refine ⟨t + s, by linarith, ?_⟩
      show φ x (t + s) = φ (φ x t) s
      rw [hφadd]
    exact (MapsTo.closure hmaps hcont' hwK : φ w s ∈ closure S)
  have hW : ∀ t ∈ Icc (-1) (0 : ℝ), a' ≤ f (φ w t) ∧ f (φ w t) ≤ b' := by
    intro t ht
    exact ⟨hKsub (hback t ht.2), le_b'_backward hf hφ0 hφadd hφcont hT ha'b' hwb' t ht.2⟩
  have hmono := strictMonoOn_traj hf hφ0 hφadd hφcont hT (by norm_num : (-1:ℝ) ≤ 0) hW
  have hlt := hmono (by norm_num : (-1:ℝ) ∈ Icc (-1) 0) (by norm_num : (0:ℝ) ∈ Icc (-1) 0)
    (by norm_num : (-1:ℝ) < 0)
  have hmin := hwmin (hback (-1) (by norm_num))
  have hlt' : f (φ w (-1)) < f w := by simpa [hφ0 w] using hlt
  exact not_lt_of_ge hmin hlt'

/-- **The trajectory reaches level `b'` in finite forward time.**  For `a' < f x` there is a
forward time at which the trajectory is at or above `b'`. -/
lemma exists_ge_b'_forward {x : X} (hx : a' < f x) : ∃ t : ℝ, 0 ≤ t ∧ b' ≤ f (φ x t) := by
  by_contra hcon
  push Not at hcon
  set S : Set X := {y : X | ∃ t : ℝ, 0 ≤ t ∧ φ x t = y} with hSdef
  have hxS : x ∈ S := ⟨0, le_refl 0, hφ0 x⟩
  set K : Set X := closure S with hKdef
  have hKcomp : IsCompact K := by rw [hKdef]; exact isClosed_closure.isCompact
  have hKne : K.Nonempty := ⟨x, by rw [hKdef]; exact subset_closure hxS⟩
  obtain ⟨w, hwK, hwmax⟩ := hKcomp.exists_isMaxOn hKne hf.continuousOn
  have hKsub : K ⊆ f ⁻¹' Iic b' := by
    rw [hKdef]
    refine closure_minimal (fun y hy => ?_) (isClosed_Iic.preimage hf)
    obtain ⟨t, ht, rfl⟩ := hy
    exact le_of_lt (hcon t ht)
  have hwx : f x ≤ f w := hwmax (by rw [hKdef]; exact subset_closure hxS)
  have haw : a' < f w := lt_of_lt_of_le hx hwx
  -- forward invariance of `K`
  have hfwd : ∀ s : ℝ, 0 ≤ s → φ w s ∈ K := by
    intro s hs
    have hcont' : Continuous fun y : X => φ y s :=
      hφcont.comp (continuous_id.prodMk continuous_const)
    have hmaps : MapsTo (fun y : X => φ y s) S S := by
      rintro y ⟨t, ht, rfl⟩
      refine ⟨t + s, by linarith, ?_⟩
      show φ x (t + s) = φ (φ x t) s
      rw [hφadd]
    exact (MapsTo.closure hmaps hcont' hwK : φ w s ∈ closure S)
  have hW : ∀ t ∈ Icc (0 : ℝ) 1, a' ≤ f (φ w t) ∧ f (φ w t) ≤ b' := by
    intro t ht
    exact ⟨le_a'_forward hf hφ0 hφadd hφcont hT ha'b' haw t ht.1, hKsub (hfwd t ht.1)⟩
  have hmono := strictMonoOn_traj hf hφ0 hφadd hφcont hT (by norm_num : (0:ℝ) ≤ 1) hW
  have hlt := hmono (by norm_num : (0:ℝ) ∈ Icc 0 1) (by norm_num : (1:ℝ) ∈ Icc 0 1)
    (by norm_num : (0:ℝ) < 1)
  have hmax := hwmax (hfwd 1 (by norm_num))
  have hlt' : f w < f (φ w 1) := by simpa [hφ0 w] using hlt
  exact not_lt_of_ge hmax hlt'

end Basic2

section Structure

variable (hf : Continuous f) (hφ0 : ∀ x : X, φ x 0 = x)
variable (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
variable (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
variable (hT : ∀ y : X, a' ≤ f y → f y ≤ b' →
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ, f (φ y (-s)) < f y)
variable (ha'b' : a' < b')

include hf hφ0 hφadd hφcont hT ha'b'

/-- **Downward closure**: if the trajectory is at or below a level `c ∈ [a',b']` at time `t`, then
it was at or below `c` at every earlier time. -/
lemma barrier_down {c : ℝ} (hc : a' ≤ c) (hc' : c ≤ b') {x : X} {s t : ℝ} (hst : s ≤ t)
    (h : f (φ x t) ≤ c) : f (φ x s) ≤ c := by
  rcases lt_or_eq_of_le hst with hlt | heq
  · by_contra hcon
    exact barrier hf hφ0 hφadd hφcont hT hc hc' hlt (lt_of_not_ge hcon) h
  · rw [heq]; exact h

/-- **The hitting time of the lower level `a'`.**  If `f x ≤ b'` and `a' < f x` then there is a
last time `α ≤ 0` at which the trajectory of `x` is at or below `a'`; there `f (φ x α) = a'`, the
trajectory was at or below `a'` before `α` and strictly above `a'` after `α`. -/
lemma exists_hit_a' {x : X} (hx : f x ≤ b') (hx' : a' < f x) :
    ∃ α : ℝ, α ≤ 0 ∧ f (φ x α) = a' ∧ (∀ t : ℝ, t ≤ α → f (φ x t) ≤ a') ∧
      (∀ t : ℝ, α < t → a' < f (φ x t)) := by
  obtain ⟨t₀, ht₀, ht₀'⟩ := exists_le_a'_backward hf hφ0 hφadd hφcont hT ha'b' hx
  set A : Set ℝ := {t : ℝ | f (φ x t) ≤ a'} with hAdef
  have hAmem : ∀ t : ℝ, t ∈ A ↔ f (φ x t) ≤ a' := fun t => Iff.rfl
  have hAne : A.Nonempty := ⟨t₀, ht₀'⟩
  have hdown : ∀ {s t : ℝ}, s ≤ t → f (φ x t) ≤ a' → f (φ x s) ≤ a' :=
    fun hst h => barrier_down hf hφ0 hφadd hφcont hT ha'b' (le_refl a') ha'b'.le hst h
  have hnotpos : ∀ t ∈ A, t ≤ 0 := by
    intro t ht
    by_contra hcon
    have h0 : (0:ℝ) ∈ A := hdown (le_of_lt (lt_of_not_ge hcon)) ((hAmem t).mp ht)
    have h0' : f (φ x 0) ≤ a' := (hAmem 0).mp h0
    rw [hφ0] at h0'
    linarith
  have hAbdd : BddAbove A := ⟨0, hnotpos⟩
  have hAclosed : IsClosed A := by
    rw [hAdef]
    exact isClosed_le (hf.comp (continuous_traj hφcont x)) continuous_const
  have hsupA : sSup A ∈ A := hAclosed.csSup_mem hAne hAbdd
  have hαle : sSup A ≤ 0 := hnotpos _ hsupA
  have hαf : f (φ x (sSup A)) ≤ a' := (hAmem _).mp hsupA
  have hαlt : sSup A < 0 := lt_of_le_of_ne hαle (fun h => by
    have h0 : f (φ x 0) ≤ a' := h ▸ hαf
    rw [hφ0] at h0
    linarith)
  have hαeq : f (φ x (sSup A)) = a' := by
    refine le_antisymm hαf ?_
    have htend : Filter.Tendsto (fun t : ℝ => f (φ x t)) (𝓝[>] (sSup A))
        (𝓝 (f (φ x (sSup A)))) :=
      ((hf.comp (continuous_traj hφcont x)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have hge : ∀ᶠ t in 𝓝[>] (sSup A), a' ≤ f (φ x t) := by
      filter_upwards [Commons.Topology.Order.Ioo_mem_nhdsWithin_gt hαlt] with t ht
      have hnot : t ∉ A := fun hmem => absurd (le_csSup hAbdd hmem) (not_le.mpr ht.1)
      by_contra hcon
      exact hnot ((hAmem t).mpr (le_of_lt (lt_of_not_ge hcon)))
    exact ge_of_tendsto htend hge
  refine ⟨sSup A, hαle, hαeq, fun t ht => hdown ht (le_of_eq hαeq), ?_⟩
  intro t ht
  by_contra hcon
  exact absurd (le_csSup hAbdd ((hAmem t).mpr (le_of_not_gt hcon))) (not_le.mpr ht)

/-- **The hitting time of the upper level `b'`.**  If `a' < f x < b'` then there is a first time
`β ≥ 0` at which the trajectory of `x` reaches `b'`; there `f (φ x β) = b'`, the trajectory was at
or below `b'` before `β` and strictly above `b'` after `β`. -/
lemma exists_hit_b' {x : X} (hx' : a' < f x) (hx'' : f x < b') :
    ∃ β : ℝ, 0 ≤ β ∧ f (φ x β) = b' ∧ (∀ t : ℝ, t ≤ β → f (φ x t) ≤ b') ∧
      (∀ t : ℝ, β < t → b' < f (φ x t)) := by
  obtain ⟨t₀, ht₀, ht₀'⟩ := exists_ge_b'_forward hf hφ0 hφadd hφcont hT ha'b' hx'
  set B : Set ℝ := {t : ℝ | b' ≤ f (φ x t)} with hBdef
  have hBmem : ∀ t : ℝ, t ∈ B ↔ b' ≤ f (φ x t) := fun t => Iff.rfl
  have hBne : B.Nonempty := ⟨t₀, ht₀'⟩
  have hBclosed : IsClosed B := by
    rw [hBdef]
    exact isClosed_le continuous_const (hf.comp (continuous_traj hφcont x))
  have hBnn : ∀ t ∈ B, 0 ≤ t := by
    intro t ht
    by_contra hcon
    have hgt : b' < f (φ x 0) :=
      gt_b'_forward hf hφ0 hφadd hφcont hT ha'b' (lt_of_not_ge hcon) ((hBmem t).mp ht)
    rw [hφ0] at hgt
    linarith
  have hBbdd : BddBelow B := ⟨0, hBnn⟩
  have hβmem : sInf B ∈ B := hBclosed.csInf_mem hBne hBbdd
  have hβge : 0 ≤ sInf B := hBnn _ hβmem
  have hβf : b' ≤ f (φ x (sInf B)) := (hBmem _).mp hβmem
  have hβgt : 0 < sInf B := lt_of_le_of_ne hβge (fun h => by
    have h0 : b' ≤ f (φ x 0) := h ▸ hβf
    rw [hφ0] at h0
    linarith)
  have hβeq : f (φ x (sInf B)) = b' := by
    refine le_antisymm ?_ hβf
    have htend : Filter.Tendsto (fun t : ℝ => f (φ x t)) (𝓝[<] (sInf B))
        (𝓝 (f (φ x (sInf B)))) :=
      ((hf.comp (continuous_traj hφcont x)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have hle : ∀ᶠ t in 𝓝[<] (sInf B), f (φ x t) ≤ b' := by
      filter_upwards [Commons.Topology.Order.Ioo_mem_nhdsWithin_lt hβgt] with t ht
      have hnot : t ∉ B := fun hmem => absurd (csInf_le hBbdd hmem) (not_le.mpr ht.2)
      by_contra hcon
      exact hnot ((hBmem t).mpr (le_of_lt (lt_of_not_ge hcon)))
    exact le_of_tendsto htend hle
  have hβright : ∀ t : ℝ, sInf B < t → b' < f (φ x t) := fun t ht =>
    gt_b'_forward hf hφ0 hφadd hφcont hT ha'b' ht hβf
  refine ⟨sInf B, hβge, hβeq, fun t ht => ?_, hβright⟩
  by_cases hmem : t ∈ B
  · have h1 : sInf B ≤ t := csInf_le hBbdd hmem
    have h2 : t = sInf B := le_antisymm ht h1
    rw [h2, hβeq]
  · by_contra hcon
    exact hmem ((hBmem t).mpr (le_of_lt (lt_of_not_ge hcon)))

end Structure

section Slab

variable (hf : Continuous f) (hφ0 : ∀ x : X, φ x 0 = x)
variable (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
variable (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
variable (hT : ∀ y : X, a' ≤ f y → f y ≤ b' →
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ, f (φ y (-s)) < f y)
variable (ha'b' : a' < b') {a b : ℝ} (ha'a : a' < a) (hab : a < b) (hbb' : b < b')

include hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb'

/-- **No return to a level once above it.**  If the trajectory crosses the level `c ∈ (a',b']` at
time `t₀` and is at or below `c` at a later time, we have a contradiction. -/
lemma gt_level_of_crossing {c : ℝ} (ha'c : a' < c) (hcb' : c ≤ b') {x : X} {t₀ t : ℝ}
    (ht₀ : f (φ x t₀) = c) (htt : t₀ < t) (hfc : f (φ x t) ≤ c) : False := by
  have hle_c : ∀ s ∈ Icc t₀ t, f (φ x s) ≤ c := fun s hs =>
    barrier_down hf hφ0 hφadd hφcont hT ha'b' ha'c.le hcb' hs.2 hfc
  have hge_a' : ∀ s ∈ Icc t₀ t, a' ≤ f (φ x s) := by
    intro s hs
    have h0 : a' < f (φ x t₀) := by rw [ht₀]; exact ha'c
    have h1 := le_a'_forward hf hφ0 hφadd hφcont hT ha'b' h0 (s - t₀) (by linarith [hs.1])
    have h2 : φ (φ x t₀) (s - t₀) = φ x s := by
      rw [hφadd]
      congr 1
      ring
    rwa [h2] at h1
  have hmono := strictMonoOn_traj hf hφ0 hφadd hφcont hT htt.le
    (fun s hs => ⟨hge_a' s hs, le_trans (hle_c s hs) hcb'⟩)
  have hthis : f (φ x t₀) < f (φ x t) :=
    hmono (left_mem_Icc.mpr htt.le) (right_mem_Icc.mpr htt.le) htt
  rw [ht₀] at hthis
  linarith

end Slab
section Slab2

variable (hf : Continuous f) (hφ0 : ∀ x : X, φ x 0 = x)
variable (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
variable (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
variable (hT : ∀ y : X, a' ≤ f y → f y ≤ b' →
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ, f (φ y (-s)) < f y)
variable (ha'b' : a' < b') {a b : ℝ} (ha'a : a' < a) (hab : a < b) (hbb' : b < b')

include hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb'

/-- **The crossing structure of a trajectory through the slab `{a ≤ f ≤ b}`.**  There are times
`ta ≤ 0 ≤ tb` at which the trajectory is at level `a` resp. `b`; `f ∘ φ x` is strictly increasing on
`[ta,tb]`, is at or below `a` before `ta` and strictly above `b` after `tb`, and every time at which
the trajectory is in `[a,b]` lies in `[ta,tb]`. -/
lemma crossing_structure {x : X} (hx1 : a ≤ f x) (hx2 : f x ≤ b) :
    ∃ ta tb : ℝ, ta ≤ 0 ∧ 0 ≤ tb ∧ f (φ x ta) = a ∧ f (φ x tb) = b ∧
      StrictMonoOn (fun t : ℝ => f (φ x t)) (Icc ta tb) ∧
      (∀ t : ℝ, t < ta → f (φ x t) ≤ a) ∧
      (∀ t : ℝ, tb < t → b < f (φ x t)) ∧
      (∀ t : ℝ, a ≤ f (φ x t) → f (φ x t) ≤ b → ta ≤ t ∧ t ≤ tb) := by
  have hxlt : a' < f x := lt_of_lt_of_le ha'a hx1
  have hx'' : f x < b' := lt_of_le_of_lt hx2 hbb'
  have hxb' : f x ≤ b' := le_trans hx2 hbb'.le
  obtain ⟨α, hαle, hαeq, hαleft, hαright⟩ :=
    exists_hit_a' hf hφ0 hφadd hφcont hT ha'b' hxb' hxlt
  obtain ⟨β, hβge, hβeq, hβleft, hβright⟩ :=
    exists_hit_b' hf hφ0 hφadd hφcont hT ha'b' hxlt hx''
  -- monotonicity on the whole window `[α, β]`
  have hmonoαβ : StrictMonoOn (fun t : ℝ => f (φ x t)) (Icc α β) := by
    refine strictMonoOn_traj hf hφ0 hφadd hφcont hT (le_trans hαle hβge) (fun t ht => ?_)
    refine ⟨?_, hβleft t ht.2⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hαeq]
    · exact le_of_lt (hαright t h)
  -- the two crossing times
  obtain ⟨ta, hta_mem, hta_val⟩ : ∃ t ∈ Icc α 0, f (φ x t) = a := by
    have hcont : ContinuousOn (fun t : ℝ => f (φ x t)) (Icc α 0) :=
      (hf.comp (continuous_traj hφcont x)).continuousOn
    exact (intermediate_value_Icc hαle hcont)
      ⟨by rw [hαeq]; exact ha'a.le, by rw [hφ0]; exact hx1⟩
  obtain ⟨tb, htb_mem, htb_val⟩ : ∃ t ∈ Icc 0 β, f (φ x t) = b := by
    have hcont : ContinuousOn (fun t : ℝ => f (φ x t)) (Icc 0 β) :=
      (hf.comp (continuous_traj hφcont x)).continuousOn
    exact (intermediate_value_Icc hβge hcont)
      ⟨by rw [hφ0]; exact hx2, by rw [hβeq]; exact hbb'.le⟩
  have htale : ta ≤ 0 := hta_mem.2
  have htbge : 0 ≤ tb := htb_mem.1
  have htab : ta ≤ tb := le_trans htale htbge
  -- monotonicity on `[ta,tb]`
  have hW : ∀ t ∈ Icc ta tb, a' ≤ f (φ x t) ∧ f (φ x t) ≤ b' := by
    intro t ht
    have htα : α ≤ t := le_trans hta_mem.1 ht.1
    have htβ : t ≤ β := le_trans ht.2 htb_mem.2
    refine ⟨?_, hβleft t htβ⟩
    rcases eq_or_lt_of_le htα with h | h
    · rw [← h, hαeq]
    · exact le_of_lt (hαright t h)
  have hmono : StrictMonoOn (fun t : ℝ => f (φ x t)) (Icc ta tb) :=
    strictMonoOn_traj hf hφ0 hφadd hφcont hT htab hW
  -- before `ta` the trajectory is at or below `a`
  have hle_a : ∀ t : ℝ, t < ta → f (φ x t) ≤ a := by
    intro t ht
    rcases le_or_gt α t with h | h
    · have h1 : f (φ x t) < f (φ x ta) :=
        hmonoαβ ⟨h, le_trans ht.le (le_trans hta_mem.2 hβge)⟩
          ⟨hta_mem.1, le_trans hta_mem.2 hβge⟩ ht
      rw [hta_val] at h1
      exact le_of_lt h1
    · exact le_trans (hαleft t h.le) ha'a.le
  -- after `tb` the trajectory is strictly above `b`
  have hgt_b : ∀ t : ℝ, tb < t → b < f (φ x t) := by
    intro t ht
    by_contra hcon
    exact gt_level_of_crossing hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb'
      (lt_trans ha'a hab) hbb'.le htb_val ht (le_of_not_gt hcon)
  refine ⟨ta, tb, htale, htbge, hta_val, htb_val, hmono, hle_a, hgt_b, ?_⟩
  intro t h1 h2
  refine ⟨?_, le_of_not_gt (fun hcon => absurd (hgt_b t hcon) (not_lt.mpr h2))⟩
  by_contra hcon
  have hlt : t < ta := lt_of_not_ge hcon
  rcases lt_or_ge t α with h | h
  · exact absurd (lt_of_le_of_lt (hαleft t h.le) ha'a) (not_lt_of_ge h1)
  · have h3 : f (φ x t) < f (φ x ta) :=
      hmonoαβ ⟨h, le_trans hlt.le (le_trans hta_mem.2 hβge)⟩
        ⟨hta_mem.1, le_trans hta_mem.2 hβge⟩ hlt
    rw [hta_val] at h3
    linarith

end Slab2
section Slab3

variable (hf : Continuous f) (hφ0 : ∀ x : X, φ x 0 = x)
variable (hφadd : ∀ (x : X) (s t : ℝ), φ (φ x s) t = φ x (s + t))
variable (hφcont : Continuous fun p : X × ℝ => φ p.1 p.2)
variable (hT : ∀ y : X, a' ≤ f y → f y ≤ b' →
  ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ, f (φ y (-s)) < f y)
variable (ha'b' : a' < b') {a b : ℝ} (ha'a : a' < a) (hab : a < b) (hbb' : b < b')

include hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb'

/-- **Uniqueness of the crossing of a level in `[a,b]`.** -/
lemma crossing_unique {x : X} (hx1 : a ≤ f x) (hx2 : f x ≤ b) {ℓ : ℝ} (hℓ : ℓ ∈ Icc a b)
    {t t' : ℝ} (ht : f (φ x t) = ℓ) (ht' : f (φ x t') = ℓ) : t = t' := by
  obtain ⟨ta, tb, htale, htbge, hta_val, htb_val, hmono, hle_a, hgt_b, hrange⟩ :=
    crossing_structure hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2
  have h1 := hrange t (by rw [ht]; exact hℓ.1) (by rw [ht]; exact hℓ.2)
  have h2 := hrange t' (by rw [ht']; exact hℓ.1) (by rw [ht']; exact hℓ.2)
  rcases lt_trichotomy t t' with h | h | h
  · have hthis : f (φ x t) < f (φ x t') := hmono ⟨h1.1, h1.2⟩ ⟨h2.1, h2.2⟩ h
    rw [ht, ht'] at hthis
    exact absurd hthis (lt_irrefl ℓ)
  · exact h
  · have hthis : f (φ x t') < f (φ x t) := hmono ⟨h2.1, h2.2⟩ ⟨h1.1, h1.2⟩ h
    rw [ht, ht'] at hthis
    exact absurd hthis (lt_irrefl ℓ)

/-- **Existence and uniqueness of the crossing of a level in `[a,b]`.** -/
lemma crossing_existsUnique {x : X} (hx1 : a ≤ f x) (hx2 : f x ≤ b) {ℓ : ℝ}
    (hℓ : ℓ ∈ Icc a b) : ∃! t : ℝ, f (φ x t) = ℓ := by
  obtain ⟨ta, tb, htale, htbge, hta_val, htb_val, hmono, hle_a, hgt_b, hrange⟩ :=
    crossing_structure hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2
  have hcont : ContinuousOn (fun t : ℝ => f (φ x t)) (Icc ta tb) :=
    (hf.comp (continuous_traj hφcont x)).continuousOn
  have hmem : ℓ ∈ Icc (f (φ x ta)) (f (φ x tb)) := by
    rw [hta_val, htb_val]; exact hℓ
  obtain ⟨t, -, hval⟩ := (intermediate_value_Icc (le_trans htale htbge) hcont) hmem
  exact ⟨t, hval, fun t' ht' =>
    crossing_unique hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2 hℓ ht' hval⟩

/-- **The crossing time of the lower level `a`** (with all the properties needed later). -/
lemma exists_cross_a {x : X} (hx1 : a ≤ f x) (hx2 : f x ≤ b) :
    ∃ ta : ℝ, ta ≤ 0 ∧ f (φ x ta) = a ∧ (∀ t : ℝ, t < ta → f (φ x t) ≤ a) ∧
      (∀ t : ℝ, a ≤ f (φ x t) → f (φ x t) ≤ b → ta ≤ t) ∧
      (∀ t : ℝ, f (φ x t) = a → t = ta) := by
  obtain ⟨ta, tb, htale, htbge, hta_val, htb_val, hmono, hle_a, hgt_b, hrange⟩ :=
    crossing_structure hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2
  exact ⟨ta, htale, hta_val, hle_a, fun t h1 h2 => (hrange t h1 h2).1,
    fun t ht => crossing_unique hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2
      ⟨le_refl a, hab.le⟩ ht hta_val⟩

/-- **The crossing time of the upper level `b`** (with all the properties needed later). -/
lemma exists_cross_b {x : X} (hx1 : a ≤ f x) (hx2 : f x ≤ b) :
    ∃ tb : ℝ, 0 ≤ tb ∧ f (φ x tb) = b ∧ (∀ t : ℝ, tb < t → b < f (φ x t)) ∧
      (∀ t : ℝ, a ≤ f (φ x t) → f (φ x t) ≤ b → t ≤ tb) ∧
      (∀ t : ℝ, f (φ x t) = b → t = tb) := by
  obtain ⟨ta, tb, htale, htbge, hta_val, htb_val, hmono, hle_a, hgt_b, hrange⟩ :=
    crossing_structure hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2
  exact ⟨tb, htbge, htb_val, hgt_b, fun t h1 h2 => (hrange t h1 h2).2,
    fun t ht => crossing_unique hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2
      ⟨hab.le, le_refl b⟩ ht htb_val⟩

/-- **The crossing times of the levels `a` and `b` are uniformly bounded.**

The proof is the classical compactness argument: the crossing time of `b` depends
"continuously enough" on the starting point, and the slab is compact. -/
theorem exists_uniform_bound :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : X, a ≤ f x → f x ≤ b → ∀ ℓ ∈ Icc a b, ∀ t : ℝ,
      f (φ x t) = ℓ → t ∈ Icc (-N) N := by
  classical
  set K : Set X := {x : X | a ≤ f x ∧ f x ≤ b} with hKdef
  have hKmem : ∀ x : X, x ∈ K ↔ a ≤ f x ∧ f x ≤ b := fun x => Iff.rfl
  by_cases hKne : K.Nonempty
  · have hKcomp : IsCompact K := (isClosed_Icc.preimage hf).isCompact
    have hexa : ∀ y : K, ∃ ta : ℝ, ta ≤ 0 ∧ f (φ y.1 ta) = a ∧
        (∀ t : ℝ, t < ta → f (φ y.1 t) ≤ a) ∧
        (∀ t : ℝ, a ≤ f (φ y.1 t) → f (φ y.1 t) ≤ b → ta ≤ t) ∧
        (∀ t : ℝ, f (φ y.1 t) = a → t = ta) := fun y =>
      exists_cross_a hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb'
        ((hKmem y.1).mp y.2).1 ((hKmem y.1).mp y.2).2
    have hexb : ∀ y : K, ∃ tb : ℝ, 0 ≤ tb ∧ f (φ y.1 tb) = b ∧
        (∀ t : ℝ, tb < t → b < f (φ y.1 t)) ∧
        (∀ t : ℝ, a ≤ f (φ y.1 t) → f (φ y.1 t) ≤ b → t ≤ tb) ∧
        (∀ t : ℝ, f (φ y.1 t) = b → t = tb) := fun y =>
      exists_cross_b hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb'
        ((hKmem y.1).mp y.2).1 ((hKmem y.1).mp y.2).2
    choose Ta hTa using hexa
    choose Tb hTb using hexb
    -- the two open covers of the slab
    have hopen1 : ∀ i : K, IsOpen {y : X | b < f (φ y (Tb i + 1))} := fun i =>
      isOpen_lt continuous_const (hf.comp (hφcont.comp
        (continuous_id.prodMk continuous_const)))
    have hcover1 : K ⊆ ⋃ i : K, {y : X | b < f (φ y (Tb i + 1))} := by
      intro y hy
      refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
      exact (hTb ⟨y, hy⟩).2.2.1 (Tb ⟨y, hy⟩ + 1) (by linarith [(hTb ⟨y, hy⟩).1])
    obtain ⟨s, hs⟩ := hKcomp.elim_finite_subcover
      (fun i : K => {y : X | b < f (φ y (Tb i + 1))}) hopen1 hcover1
    have hsne : s.Nonempty := by
      obtain ⟨y, hy⟩ := hKne
      obtain ⟨i, his, -⟩ := mem_iUnion₂.mp (hs hy)
      exact ⟨i, his⟩
    set N₁ : ℝ := s.sup' hsne (fun i => Tb i + 1) with hN₁def
    have hN₁spec : ∀ i ∈ s, Tb i + 1 ≤ N₁ := by
      intro i hi
      rw [hN₁def]
      exact Finset.le_sup' (fun i => Tb i + 1) hi
    have hN₁nn : 0 ≤ N₁ := by
      obtain ⟨i, hi⟩ := hsne
      exact le_trans (by linarith [(hTb i).1]) (hN₁spec i hi)
    have hopen2 : ∀ i : K, IsOpen {y : X | f (φ y (Ta i - 1)) < a} := fun i =>
      isOpen_lt (hf.comp (hφcont.comp (continuous_id.prodMk continuous_const)))
        continuous_const
    have hcover2 : K ⊆ ⋃ i : K, {y : X | f (φ y (Ta i - 1)) < a} := by
      intro y hy
      refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
      have hle := (hTa ⟨y, hy⟩).2.2.1 (Ta ⟨y, hy⟩ - 1) (by linarith [(hTa ⟨y, hy⟩).1])
      have hne : f (φ y (Ta ⟨y, hy⟩ - 1)) ≠ a := fun hcon =>
        absurd ((hTa ⟨y, hy⟩).2.2.2.2 (Ta ⟨y, hy⟩ - 1) hcon) (by linarith)
      exact lt_of_le_of_ne hle hne
    obtain ⟨s₂, hs₂⟩ := hKcomp.elim_finite_subcover
      (fun i : K => {y : X | f (φ y (Ta i - 1)) < a}) hopen2 hcover2
    have hs₂ne : s₂.Nonempty := by
      obtain ⟨y, hy⟩ := hKne
      obtain ⟨i, his, -⟩ := mem_iUnion₂.mp (hs₂ hy)
      exact ⟨i, his⟩
    set N₂ : ℝ := s₂.sup' hs₂ne (fun i => 1 - Ta i) with hN₂def
    have hN₂spec : ∀ i ∈ s₂, 1 - Ta i ≤ N₂ := by
      intro i hi
      rw [hN₂def]
      exact Finset.le_sup' (fun i => 1 - Ta i) hi
    refine ⟨max N₁ N₂, le_max_of_le_left hN₁nn, fun x hx1 hx2 ℓ hℓ t ht => ?_⟩
    have hxK : x ∈ K := (hKmem x).mpr ⟨hx1, hx2⟩
    have hTa_spec := hTa ⟨x, hxK⟩
    have hTb_spec := hTb ⟨x, hxK⟩
    have hℓ1 : a ≤ f (φ x t) := by rw [ht]; exact hℓ.1
    have hℓ2 : f (φ x t) ≤ b := by rw [ht]; exact hℓ.2
    have ht_le : t ≤ Tb ⟨x, hxK⟩ := hTb_spec.2.2.2.1 t hℓ1 hℓ2
    have ht_ge : Ta ⟨x, hxK⟩ ≤ t := hTa_spec.2.2.2.1 t hℓ1 hℓ2
    constructor
    · -- lower bound: the crossing of `a` for `x` is at least `Ta i - 1` for some `i ∈ s₂`
      obtain ⟨i, his, hiV⟩ := mem_iUnion₂.mp (hs₂ hxK)
      have hle : Ta i - 1 ≤ Tb ⟨x, hxK⟩ := by linarith [hTb_spec.1, (hTa i).1]
      have hmem : a ∈ Icc (f (φ x (Ta i - 1))) (f (φ x (Tb ⟨x, hxK⟩))) :=
        ⟨le_of_lt hiV, by rw [hTb_spec.2.1]; exact hab.le⟩
      obtain ⟨t', ht'mem, ht'val⟩ := (intermediate_value_Icc hle
        (hf.comp (continuous_traj hφcont x)).continuousOn) hmem
      have heq : t' = Ta ⟨x, hxK⟩ := hTa_spec.2.2.2.2 t' ht'val
      have h2 : Ta i - 1 ≤ Ta ⟨x, hxK⟩ := by rw [← heq]; exact ht'mem.1
      have h3 : -N₂ ≤ Ta i - 1 := by linarith [hN₂spec i his]
      linarith [ht_ge, h2, h3, neg_le_neg (le_max_right N₁ N₂)]
    · -- upper bound
      obtain ⟨i, his, hiV⟩ := mem_iUnion₂.mp (hs hxK)
      have hle : Ta ⟨x, hxK⟩ ≤ Tb i + 1 := by linarith [hTa_spec.1, (hTb i).1]
      have hmem : b ∈ Icc (f (φ x (Ta ⟨x, hxK⟩))) (f (φ x (Tb i + 1))) :=
        ⟨by rw [hTa_spec.2.1]; exact hab.le, le_of_lt hiV⟩
      obtain ⟨t', ht'mem, ht'val⟩ := (intermediate_value_Icc hle
        (hf.comp (continuous_traj hφcont x)).continuousOn) hmem
      have heq : t' = Tb ⟨x, hxK⟩ := hTb_spec.2.2.2.2 t' ht'val
      have h2 : Tb ⟨x, hxK⟩ ≤ Tb i + 1 := by rw [← heq]; exact ht'mem.2
      have h3 : Tb i + 1 ≤ N₁ := hN₁spec i his
      linarith [ht_le, h2, h3, le_max_left N₁ N₂]
  · refine ⟨0, le_refl 0, fun x hx1 hx2 ℓ hℓ t ht => ?_⟩
    exact absurd ⟨x, (hKmem x).mpr ⟨hx1, hx2⟩⟩ hKne

/-- **The level sets of `f` on the slab are "stacked" along the flow.**  For every point `x` of the
slab `{a ≤ f ≤ b}` and every level `ℓ ∈ [a,b]` there is a unique time `t ∈ [-N,N]` at which the
trajectory of `x` crosses the level `ℓ`. -/
theorem exists_unique_crossing :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : X, a ≤ f x → f x ≤ b → ∀ ℓ ∈ Icc a b,
      ∃! t : ℝ, t ∈ Icc (-N) N ∧ f (φ x t) = ℓ := by
  obtain ⟨N, hN, hbound⟩ :=
    exists_uniform_bound hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb'
  refine ⟨N, hN, fun x hx1 hx2 ℓ hℓ => ?_⟩
  obtain ⟨t, ht, htuniq⟩ :=
    crossing_existsUnique hf hφ0 hφadd hφcont hT ha'b' ha'a hab hbb' hx1 hx2 hℓ
  exact ⟨t, ⟨hbound x hx1 hx2 ℓ hℓ t ht, ht⟩, fun t' ht' => htuniq t' ht'.2⟩

end Slab3

end Submission.GSCross
