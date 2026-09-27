import Mathlib
import Submission.Work.EKLC6Core.shell_radius_two_sided
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.frontier_Vball_null_of_continuousAt
import Submission.Work.EKLC6Core.exists_null_frontier_Vball_radius_between
import Submission.Work.EKLC6Core.shell_sum_le
import Submission.Work.EKLC6Core.exists_disjoint_ball_subfamily

/-!
# A shell radius of null frontier with a two-sided linear shell bound

This file proves `Work.EKLC6Core.shell_radius_nullfrontier`: for every finite measure `μ` on
`X₃ = SL₃(ℝ)/SL₃(ℤ)`, every `x : X₃` and every `0 < β < γ` there is a radius `s ∈ [β, γ]` with

* `μ (frontier (Vball s x)) = 0`, and
* the relative shell measures around `s` are linearly bounded:
  `μ (Vball (s(1+δ)) x) - μ (Vball (s(1-δ)) x) ≤ (16γ/(γ-β))·δ·μ (Vball (2γ) x)` for
  every `δ ∈ (0,1]`.

The null-frontier part is supplied by the continuity of `t ↦ μ (Vball t x)` (a monotone function
has a co-countable set of continuity points) via `frontier_Vball_null_of_continuousAt`.

The shell bound is reduced to the purely real-analytic statement `exists_shell_radius_good`
about a monotone nonnegative `f : ℝ → ℝ`: among the radii of `[β, γ]` one can find a continuity
point at which the *relative* shells `f(s(1+δ)) - f(s(1-δ))` are controlled by `δ`.  The proof
is a covering argument.  Write `M = f(2γ)`, `C = 16γ/(γ-β)` and call `s` **bad** when some
`δ ∈ (0,1]` satisfies `f(s(1+δ)) - f(s(1-δ)) > C δ M`.  To each bad `s` one associates the
interval `J_s = (s(1-δ), s(1+δ))`; the "mass" `f(s(1+δ)) - f(s(1-δ))` of `J_s` is large
compared with its length, because `s ≤ γ`.  Extracting from a finite subcover a pairwise
disjoint subfamily (`exists_disjoint_ball_subfamily`, the finite Vitali lemma) and using that
the total mass over disjoint intervals inside `[0, 2γ]` is at most `M`
(`shell_sum_le`, a telescoping estimate for monotone functions) shows that any compact subset of
the bad set has Lebesgue measure at most `3(γ-β)/8`.  Since the discontinuities of the monotone
`f` form a countable — hence null — set, inner regularity of Lebesgue measure produces a compact
subset `K` of `[β,γ]` minus that null set of measure `> (γ-β)/2`; it cannot lie in the bad set,
so it contains a good continuity point.
-/

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

/-- Two disjoint open balls in `ℝ` are ordered: one lies entirely to the left of the other. -/
private theorem disjoint_ball_le {x y r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : Disjoint (Metric.ball x r) (Metric.ball y s)) : x + r ≤ y - s ∨ y + s ≤ x - r := by
  rw [Set.disjoint_left] at h
  by_contra hc
  rw [not_or] at hc
  obtain ⟨hc1, hc2⟩ := hc
  rw [not_le] at hc1 hc2
  set z : ℝ := (max (x - r) (y - s) + min (x + r) (y + s)) / 2 with hz
  have hlt : max (x - r) (y - s) < min (x + r) (y + s) :=
    lt_min (max_lt (by linarith) hc1) (max_lt hc2 (by linarith))
  have hzg : max (x - r) (y - s) < z := by rw [hz]; linarith
  have hzl : z < min (x + r) (y + s) := by rw [hz]; linarith
  have hz1 : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hzg, le_max_left (x - r) (y - s), hzl, min_le_left (x + r) (y + s)]
  have hz2 : z ∈ Metric.ball y s := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hzg, le_max_right (x - r) (y - s), hzl, min_le_right (x + r) (y + s)]
  exact h hz1 hz2

set_option maxHeartbeats 1600000 in
/-- **Core real-analytic statement.**  For a monotone nonnegative `f : ℝ → ℝ` and `0 < β < γ`
there is a point `s ∈ [β, γ]` at which `f` is continuous and such that every relative shell
around `s` is bounded by `(16γ/(γ-β))·δ·f(2γ)`. -/
theorem exists_shell_radius_good (f : ℝ → ℝ) (hf : Monotone f) (hfnn : ∀ t : ℝ, 0 ≤ f t)
    {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ) :
    ∃ s ∈ Set.Icc β γ, ContinuousAt f s ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      f (s * (1 + δ)) - f (s * (1 - δ)) ≤ (16 * γ / (γ - β)) * δ * f (2 * γ) := by
  set M : ℝ := f (2 * γ) with hM
  set C : ℝ := 16 * γ / (γ - β) with hC
  have hγβ : 0 < γ - β := sub_pos.mpr hβγ
  have hγpos : 0 < γ := lt_trans hβ hβγ
  have hCpos : 0 < C := by rw [hC]; positivity
  have hMnonneg : 0 ≤ M := by rw [hM]; exact hfnn _
  set Bad : Set ℝ := {s : ℝ | s ∈ Set.Icc β γ ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ f (s * (1 + δ)) - f (s * (1 - δ)) > C * δ * M} with hBad
  have hkey : ∀ K : Set ℝ, IsCompact K → K ⊆ Bad →
      volume K ≤ ENNReal.ofReal (3 * (γ - β) / 8) := by
    intro K hKc hKB
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · rw [hKe]; simp
    by_cases hM0 : M = 0
    · exfalso
      obtain ⟨a, haK⟩ := hKne
      have haB := hKB haK
      obtain ⟨δ, hδ0, hδ1, hδgt⟩ := haB.2
      have hapos : 0 < a := lt_of_lt_of_le hβ haB.1.1
      have h1 : f (a * (1 + δ)) ≤ 0 := by
        have hle : a * (1 + δ) ≤ 2 * γ := by nlinarith [haB.1.2, hδ1, hapos]
        calc f (a * (1 + δ)) ≤ f (2 * γ) := hf hle
          _ = M := hM.symm
          _ = 0 := hM0
      have h2 : 0 ≤ f (a * (1 - δ)) := hfnn _
      rw [hM0, mul_zero] at hδgt
      linarith
    · have hMpos : 0 < M := lt_of_le_of_ne hMnonneg (Ne.symm hM0)
      let dltK : K → ℝ := fun a => Classical.choose (hKB a.2).2
      have hdltK : ∀ a : K, 0 < dltK a ∧ dltK a ≤ 1 ∧
          f ((a:ℝ) * (1 + dltK a)) - f ((a:ℝ) * (1 - dltK a)) > C * dltK a * M :=
        fun a => Classical.choose_spec (hKB a.2).2
      have hposK : ∀ a : K, 0 < (a:ℝ) * dltK a := fun a =>
        mul_pos (lt_of_lt_of_le hβ (hKB a.2).1.1) (hdltK a).1
      have hcov : K ⊆ ⋃ a : K, Metric.ball (a:ℝ) ((a:ℝ) * dltK a) := by
        intro x hx
        refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
        rw [Metric.mem_ball, dist_self]
        exact hposK ⟨x, hx⟩
      obtain ⟨T, hTcov⟩ := hKc.elim_finite_subcover
        (fun a : K => Metric.ball (a:ℝ) ((a:ℝ) * dltK a)) (fun _ => Metric.isOpen_ball) hcov
      obtain ⟨u, huT, hudisj, hucov⟩ := exists_disjoint_ball_subfamily T
        (fun a : K => (a:ℝ)) (fun a : K => (a:ℝ) * dltK a)
        (fun a _ => hposK a)
      have hKsub : K ⊆ ⋃ b ∈ u, Metric.ball (b:ℝ) (3 * ((b:ℝ) * dltK b)) := by
        intro x hx
        obtain ⟨a, haT, hxa⟩ := Set.mem_iUnion₂.mp (hTcov hx)
        obtain ⟨b, hbu, hb⟩ := hucov a haT
        exact Set.mem_iUnion₂.mpr ⟨b, hbu, hb hxa⟩
      have hune : u.Nonempty := by
        rcases Finset.eq_empty_or_nonempty u with h | h
        · exfalso
          obtain ⟨x, hx⟩ := hKne
          have := hKsub hx
          rw [h] at this
          simp at this
        · exact h
      have hshell : ∑ b ∈ u, (f ((b:ℝ) * (1 + dltK b)) - f ((b:ℝ) * (1 - dltK b)))
            ≤ f (2*γ) - f 0 := by
        refine shell_sum_le f hf hfnn u (fun b : K => (b:ℝ)*(1 - dltK b))
          (fun b : K => (b:ℝ)*(1 + dltK b)) 0 (2*γ) (by linarith) ?_ ?_ ?_ ?_
        · intro b hb
          have hspec := hdltK b
          have hbpos : (0:ℝ) < b := lt_of_lt_of_le hβ (hKB b.2).1.1
          nlinarith [hspec.1, hbpos, hspec.2.1]
        · intro b hb
          have hspec := hdltK b
          have hbB := hKB b.2
          have hbpos : (0:ℝ) < b := lt_of_lt_of_le hβ hbB.1.1
          nlinarith [hspec.2.1, hbpos, hspec.1]
        · intro b hb b' hb' hne
          have hd := hudisj b hb b' hb' hne
          rcases disjoint_ball_le (hposK b) (hposK b') hd with hh | hh
          · left; nlinarith [hh]
          · right; nlinarith [hh]
        · intro b hb
          have hspec := hdltK b
          have hbB := hKB b.2
          nlinarith [hspec.2.1, hbB.1.2, hβ]
      have hterm : ∀ b ∈ u, (C * M / γ) * ((b:ℝ) * dltK b) <
            f ((b:ℝ) * (1 + dltK b)) - f ((b:ℝ) * (1 - dltK b)) := by
        intro b hb
        have hspec := hdltK b
        have hbB := hKB b.2
        have hMb : (M / γ) * (b:ℝ) ≤ M := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hγpos]
          nlinarith [hMpos.le, hbB.1.2]
        have hle : (C * M / γ) * ((b:ℝ) * dltK b) ≤ C * dltK b * M := by
          calc (C * M / γ) * ((b:ℝ) * dltK b) = C * dltK b * ((M/γ) * (b:ℝ)) := by ring
            _ ≤ C * dltK b * M :=
                mul_le_mul_of_nonneg_left hMb (mul_nonneg hCpos.le hspec.1.le)
        linarith [hspec.2.2, hle]
      have hsum_lower : ∑ b ∈ u, (C*M/γ) * ((b:ℝ) * dltK b) <
            ∑ b ∈ u, (f ((b:ℝ) * (1 + dltK b)) - f ((b:ℝ) * (1 - dltK b))) :=
        Finset.sum_lt_sum_of_nonempty hune (fun b hb => hterm b hb)
      have hstrict : (C*M/γ) * (∑ b ∈ u, ((b:ℝ) * dltK b)) < M := by
        rw [Finset.mul_sum]
        calc ∑ b ∈ u, (C*M/γ) * ((b:ℝ) * dltK b)
            < ∑ b ∈ u, (f ((b:ℝ)*(1+dltK b)) - f ((b:ℝ)*(1-dltK b))) := hsum_lower
          _ ≤ f (2*γ) - f 0 := hshell
          _ ≤ M := by rw [← hM]; linarith [hfnn 0]
      have hsumr_lt : ∑ b ∈ u, ((b:ℝ) * dltK b) < γ / C := by
        have hCMg : 0 < C*M/γ := div_pos (mul_pos hCpos hMpos) hγpos
        have h1 : (∑ b ∈ u, ((b:ℝ) * dltK b)) < M / (C*M/γ) :=
          (lt_div_iff₀ hCMg).mpr (by rw [mul_comm]; exact hstrict)
        have h2 : M / (C*M/γ) = γ / C := by field_simp
        rwa [h2] at h1
      have hvolK : volume K ≤ ∑ b ∈ u, volume (Metric.ball (b:ℝ) (3 * ((b:ℝ) * dltK b))) := by
        calc volume K ≤ volume (⋃ b ∈ u, Metric.ball (b:ℝ) (3 * ((b:ℝ) * dltK b))) :=
              measure_mono hKsub
          _ ≤ ∑ b ∈ u, volume (Metric.ball (b:ℝ) (3 * ((b:ℝ) * dltK b))) :=
              measure_biUnion_finset_le u _
      have hvolball : ∀ b ∈ u, volume (Metric.ball (b:ℝ) (3 * ((b:ℝ) * dltK b)))
            = ENNReal.ofReal (6 * ((b:ℝ) * dltK b)) := by
        intro b hb
        rw [Real.volume_ball, show 2 * (3 * ((b:ℝ) * dltK b)) = 6 * ((b:ℝ) * dltK b) by ring]
      have hvolsum : ∑ b ∈ u, volume (Metric.ball (b:ℝ) (3 * ((b:ℝ) * dltK b)))
            = ENNReal.ofReal (6 * ∑ b ∈ u, ((b:ℝ) * dltK b)) := by
        rw [Finset.sum_congr rfl hvolball]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun b hb => by
          have hbp := hposK b
          nlinarith [hbp])]
        rw [Finset.mul_sum]
      have hfinal : 6 * ∑ b ∈ u, ((b:ℝ) * dltK b) < 3 * (γ - β) / 8 := by
        have hCe : 6 * (γ / C) = 3 * (γ - β) / 8 := by rw [hC]; field_simp; ring
        have h6 : 6 * (∑ b ∈ u, ((b:ℝ) * dltK b)) < 6 * (γ / C) :=
          mul_lt_mul_of_pos_left hsumr_lt (by norm_num)
        linarith [h6, hCe]
      calc volume K ≤ ∑ b ∈ u, volume (Metric.ball (b:ℝ) (3 * ((b:ℝ) * dltK b))) := hvolK
        _ = ENNReal.ofReal (6 * ∑ b ∈ u, ((b:ℝ) * dltK b)) := hvolsum
        _ ≤ ENNReal.ofReal (3 * (γ - β) / 8) := ENNReal.ofReal_le_ofReal hfinal.le
  have hDcount : ({s : ℝ | ¬ ContinuousAt f s}).Countable := hf.countable_not_continuousAt
  by_contra hno
  have hsub : Set.Icc β γ \ {s : ℝ | ¬ ContinuousAt f s} ⊆ Bad := by
    intro s hs
    have hsCont : ContinuousAt f s := not_not.mp hs.2
    refine ⟨hs.1, ?_⟩
    by_contra hbad
    exact hno ⟨s, hs.1, hsCont, fun δ hδ0 hδ1 =>
      le_of_not_gt fun hlt => hbad ⟨δ, hδ0, hδ1, hlt⟩⟩
  set A : Set ℝ := Set.Icc β γ \ {s : ℝ | ¬ ContinuousAt f s} with hA
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact measurableSet_Icc.diff (hDcount.measurableSet)
  have hAvol : volume A = ENNReal.ofReal (γ - β) := by
    rw [hA, measure_sdiff_null (hDcount.measure_zero volume)]
    exact Real.volume_Icc
  obtain ⟨K, hKA, hKc, hKvol⟩ := hAmeas.exists_lt_isCompact_of_ne_top
    (by rw [hAvol]; exact ENNReal.ofReal_ne_top)
    (r := ENNReal.ofReal ((γ - β) / 2)) (by
      rw [hAvol, ENNReal.ofReal_lt_ofReal_iff hγβ]; linarith)
  have h1 := hkey K hKc (hKA.trans hsub)
  have hc2 : ENNReal.ofReal ((γ - β) / 2) < ENNReal.ofReal (3 * (γ - β) / 8) :=
    lt_of_lt_of_le hKvol h1
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at hc2
  linarith

open Work.EKLContract Work.EKLComp in
/-- For every finite measure `μ` on `X₃`, every `x : X₃` and every `0 < β < γ` there is a
radius `s ∈ [β, γ]` whose ball has `μ`-null frontier and whose relative shells are linearly
bounded by `(16γ/(γ-β))·δ·μ (Vball (2γ) x)`. -/
theorem shell_radius_nullfrontier (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] (x : Work.EKLContract.X3)
    {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ) :
    ∃ s : ℝ, β ≤ s ∧ s ≤ γ ∧ μ (frontier (Work.EKLComp.Vball s x)) = 0 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        (μ (Work.EKLComp.Vball (s * (1 + δ)) x)).toReal -
          (μ (Work.EKLComp.Vball (s * (1 - δ)) x)).toReal
        ≤ (16 * γ / (γ - β)) * δ * (μ (Work.EKLComp.Vball (2 * γ) x)).toReal := by
  have hmono : Monotone (fun t : ℝ => (μ (Work.EKLComp.Vball t x)).toReal) := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Work.Misiurewicz.Vball_mono x hab))
  have hnn : ∀ t : ℝ, 0 ≤ (μ (Work.EKLComp.Vball t x)).toReal := fun _ => ENNReal.toReal_nonneg
  obtain ⟨s, hsIcc, hcont, hbound⟩ :=
    exists_shell_radius_good (fun t : ℝ => (μ (Work.EKLComp.Vball t x)).toReal) hmono hnn hβ hβγ
  exact ⟨s, hsIcc.1, hsIcc.2,
    Work.EKLC6Core.frontier_Vball_null_of_continuousAt μ x (lt_of_lt_of_le hβ hsIcc.1) hcont,
    fun δ hδ0 hδ1 => hbound δ hδ0 hδ1⟩

end

end Work.EKLC6Core
