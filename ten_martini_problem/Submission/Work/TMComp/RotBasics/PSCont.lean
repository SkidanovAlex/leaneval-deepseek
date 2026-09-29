import Submission.Work.TMComp.RotBasics.PS

/-!
# Continuity of `pruferStep`

`pruferStep` is continuous on `ℝ × ℝ`.  The only delicate points are the half-integers
`t = m - 1/2`, where the floor jump and the jump of `arctan ∘ tan` cancel: the value there is
`m`, and both one-sided limits are `m` as well (because `arctan (tan x - a) → ±π/2` as
`x → ±π/2`).  The two auxiliary lemmas `exists_tan_lt` / `exists_tan_gt` supply the
one-sided bounds on `tan`.
-/

namespace Work.TMComp.RotBasics

open Work.TMContract

open Filter
open scoped Topology

noncomputable section

/-- For every bound `C` there are arbitrarily small `δ > 0` with `tan (π (δ - 1/2)) < C`,
because `tan x → -∞` as `x → -(π/2)⁺`. -/
theorem exists_tan_lt (C : ℝ) : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
    Real.tan (Real.pi * (δ - 1 / 2)) < C := by
  have hmem : {x : ℝ | x < C} ∈ Filter.atBot :=
    Filter.mem_of_superset (Filter.Iic_mem_atBot (C - 1))
      (fun x hx => by simp only [Set.mem_Iic] at hx; simp only [Set.mem_setOf_eq]; linarith)
  have h1 : ∀ᶠ x in 𝓝[>] (-(Real.pi / 2)), Real.tan x < C :=
    Real.tendsto_tan_neg_pi_div_two.eventually hmem
  have h2 : ∀ᶠ x in 𝓝[>] (-(Real.pi / 2)), -(Real.pi / 2) < x := self_mem_nhdsWithin
  have h3 : ∀ᶠ x in 𝓝[>] (-(Real.pi / 2)), x < -(Real.pi / 4) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith [Real.pi_pos]))
  obtain ⟨x₀, hx₀⟩ := (h1.and (h2.and h3)).exists
  refine ⟨(x₀ + Real.pi / 2) / Real.pi, ?_, ?_, ?_⟩
  · apply div_pos _ Real.pi_pos
    linarith [hx₀.2.1]
  · rw [div_lt_iff₀ Real.pi_pos]
    linarith [hx₀.2.2]
  · rw [show Real.pi * ((x₀ + Real.pi / 2) / Real.pi - 1 / 2) = x₀ by
      field_simp
      ring]
    exact hx₀.1

/-- For every bound `C` there are arbitrarily small `δ > 0` (indeed `< 1/4`) with
`C < tan (π (1/2 - δ))`, because `tan x → +∞` as `x → (π/2)⁻`. -/
theorem exists_tan_gt (C : ℝ) : ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧
    C < Real.tan (Real.pi * (1 / 2 - δ)) := by
  have hmem : {x : ℝ | C < x} ∈ Filter.atTop :=
    Filter.mem_of_superset (Filter.Ici_mem_atTop (C + 1))
      (fun x hx => by simp only [Set.mem_Ici] at hx; simp only [Set.mem_setOf_eq]; linarith)
  have h1 : ∀ᶠ x in 𝓝[<] (Real.pi / 2), C < Real.tan x :=
    Real.tendsto_tan_pi_div_two.eventually hmem
  have h2 : ∀ᶠ x in 𝓝[<] (Real.pi / 2), x < Real.pi / 2 := self_mem_nhdsWithin
  have h3 : ∀ᶠ x in 𝓝[<] (Real.pi / 2), Real.pi / 4 < x :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos]))
  obtain ⟨x₀, hx₀⟩ := (h1.and (h2.and h3)).exists
  refine ⟨(Real.pi / 2 - x₀) / Real.pi, ?_, ?_, ?_⟩
  · apply div_pos _ Real.pi_pos
    linarith [hx₀.2.1]
  · rw [div_lt_iff₀ Real.pi_pos]
    linarith [hx₀.2.2]
  · rw [show Real.pi * (1 / 2 - (Real.pi / 2 - x₀) / Real.pi) = x₀ by
      field_simp
      ring]
    exact hx₀.1

theorem pruferStep_continuousAt_of_floor {a₀ t₀ : ℝ}
    (h : t₀ - ((⌊t₀ + 1 / 2⌋ : ℤ) : ℝ) ≠ -1 / 2) :
    ContinuousAt (fun p : ℝ × ℝ => pruferStep p.1 p.2) (a₀, t₀) := by
  set m : ℤ := ⌊t₀ + 1 / 2⌋ with hm
  have hm' : ⌊t₀ + 1 / 2⌋ = m := hm.symm
  have hh : t₀ - (m : ℝ) ≠ -1 / 2 := by rw [← hm']; exact h
  have hmem : t₀ ∈ Set.Ioo ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2) := by
    have h1 := Int.floor_le (t₀ + 1 / 2)
    have h2 := Int.lt_floor_add_one (t₀ + 1 / 2)
    rw [hm'] at h1 h2
    constructor
    · have hle : (m : ℝ) - 1 / 2 ≤ t₀ := by linarith
      exact lt_of_le_of_ne hle (fun hc => hh (by linarith))
    · linarith
  have hopen : Set.Ioo ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2) ∈ 𝓝 t₀ :=
    isOpen_Ioo.mem_nhds hmem
  have hcos : Real.cos (Real.pi * (t₀ - (m : ℝ))) ≠ 0 := by
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos, hmem.1, hmem.2]
  have htan_cont : ContinuousAt (fun p : ℝ × ℝ => Real.tan (Real.pi * (p.2 - (m : ℝ)))) (a₀, t₀) := by
    have hpt : ContinuousAt (fun p : ℝ × ℝ => Real.pi * (p.2 - (m : ℝ))) (a₀, t₀) := by fun_prop
    have hmem2 : {x : ℝ | Real.cos x ≠ 0} ∈ 𝓝 (Real.pi * (t₀ - (m : ℝ))) := by
      apply IsOpen.mem_nhds
      · exact isOpen_compl_singleton.preimage Real.continuous_cos
      · simpa using hcos
    exact ContinuousAt.comp (g := Real.tan)
      (f := fun p : ℝ × ℝ => Real.pi * (p.2 - (m : ℝ)))
      (x := (a₀, t₀)) (Real.continuousOn_tan.continuousAt hmem2) hpt
  have hg : ContinuousAt (fun p : ℝ × ℝ =>
      (m : ℝ) + 1 / 2 + Real.arctan (Real.tan (Real.pi * (p.2 - (m : ℝ))) - p.1) / Real.pi)
      (a₀, t₀) := by
    have hsub : ContinuousAt (fun p : ℝ × ℝ =>
        Real.tan (Real.pi * (p.2 - (m : ℝ))) - p.1) (a₀, t₀) :=
      htan_cont.sub (continuousAt_fst : ContinuousAt (fun p : ℝ × ℝ => p.1) (a₀, t₀))
    have h2 : ContinuousAt (fun p : ℝ × ℝ =>
        Real.arctan (Real.tan (Real.pi * (p.2 - (m : ℝ))) - p.1)) (a₀, t₀) :=
      Real.continuous_arctan.continuousAt.comp hsub
    exact continuousAt_const.add ((h2.div_const Real.pi))
  refine hg.congr ?_
  have hpr : ∀ᶠ p : ℝ × ℝ in 𝓝 (a₀, t₀), p.2 ∈ Set.Ioo ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2) :=
    (continuousAt_snd : ContinuousAt (fun p : ℝ × ℝ => p.2) (a₀, t₀)).preimage_mem_nhds hopen
  filter_upwards [hpr] with p hp
  have hfloor : ⌊p.2 + 1 / 2⌋ = m := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith [hp.1, hp.2]
  have hne : p.2 - (m : ℝ) ≠ -1 / 2 := by linarith [hp.1]
  rw [pruferStep_eq_of_floor hfloor hne]

theorem pruferStep_continuousAt_half (a₀ : ℝ) (m : ℤ) :
    ContinuousAt (fun p : ℝ × ℝ => pruferStep p.1 p.2) (a₀, (m : ℝ) - 1 / 2) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hbase_gen : ∀ a : ℝ, pruferStep a ((m : ℝ) - 1 / 2) = (m : ℝ) := by
    intro a
    refine pruferStep_eq_of_floor_special (n := m) ?_ ?_
    · rw [show (m : ℝ) - 1 / 2 + 1 / 2 = (m : ℝ) by ring, Int.floor_intCast]
    · ring
  have hbase : pruferStep a₀ ((m : ℝ) - 1 / 2) = (m : ℝ) := hbase_gen a₀
  have hbase' : ∀ a : ℝ, pruferStep a ((m : ℝ) - 1 / 2) = (m : ℝ) := hbase_gen
  set ε' : ℝ := min ε 1 / 2 with hε'def
  have hε'pos : 0 < ε' := by
    have : 0 < min ε 1 := lt_min hε one_pos
    rw [hε'def]; linarith
  have hε'lt : ε' < 1 := by
    have : min ε 1 ≤ 1 := min_le_right _ _
    rw [hε'def]; linarith
  have hε'le : ε' ≤ ε := by
    have : min ε 1 ≤ ε := min_le_left _ _
    rw [hε'def]; linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁4, hδ₁⟩ := exists_tan_lt (Real.tan (Real.pi * (ε' - 1 / 2)) + a₀ - 1)
  obtain ⟨δ₂, hδ₂pos, hδ₂4, hδ₂⟩ := exists_tan_gt (Real.tan (Real.pi * (1 / 2 - ε')) + a₀ + 1)
  set δ : ℝ := min (min δ₁ δ₂) (min ε' (1 / 4)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle₁ : δ ≤ δ₁ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδleε : δ ≤ ε' := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδle4 : δ ≤ 1 / 4 := by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hπpos : 0 < Real.pi := Real.pi_pos
  have hπδpos : 0 < Real.pi * δ := mul_pos hπpos hδpos
  have hπδ₂pos : 0 < Real.pi * δ₂ := mul_pos hπpos hδ₂pos
  have hπδ₁pos : 0 < Real.pi * δ₁ := mul_pos hπpos hδ₁pos
  have hπδhalf : Real.pi * δ < Real.pi / 2 := by
    have h : δ < 1 / 2 := by linarith [hδle4]
    have := mul_lt_mul_of_pos_left h hπpos
    linarith
  have hπδ₁half : Real.pi * δ₁ < Real.pi / 2 := by
    have h : δ₁ < 1 / 2 := by linarith [hδ₁4]
    have := mul_lt_mul_of_pos_left h hπpos
    linarith
  have hπδ₂half : Real.pi * δ₂ < Real.pi / 2 := by
    have h : δ₂ < 1 / 2 := by linarith [hδ₂4]
    have := mul_lt_mul_of_pos_left h hπpos
    linarith
  have hπε'pos : 0 < Real.pi * ε' := mul_pos hπpos hε'pos
  have hπε'lt : Real.pi * ε' < Real.pi := by
    have := mul_lt_mul_of_pos_left hε'lt hπpos
    linarith
  -- the four half-turn arguments, written so that the products stay on one side
  have hIδ : Real.pi * (1 / 2 - δ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [mul_sub, mul_one_div]
    exact ⟨by linarith [hπδpos], by linarith [hπδhalf]⟩
  have hIδ₂ : Real.pi * (1 / 2 - δ₂) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [mul_sub, mul_one_div]
    exact ⟨by linarith [hπδ₂pos], by linarith [hπδ₂half]⟩
  have hIε' : Real.pi * (1 / 2 - ε') ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [mul_sub, mul_one_div]
    exact ⟨by linarith [hπε'lt, hπpos], by linarith [hπε'pos]⟩
  have hJδ : Real.pi * (δ - 1 / 2) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [mul_sub, mul_one_div]
    exact ⟨by linarith [hπδpos], by linarith [hπδhalf]⟩
  have hJδ₁ : Real.pi * (δ₁ - 1 / 2) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [mul_sub, mul_one_div]
    exact ⟨by linarith [hπδ₁pos], by linarith [hπδ₁half]⟩
  have hJε' : Real.pi * (ε' - 1 / 2) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [mul_sub, mul_one_div]
    exact ⟨by linarith [hπε'lt, hπpos], by linarith [hπε'pos]⟩
  refine ⟨δ, hδpos, ?_⟩
  intro p hp
  have hp' : max (dist p.1 a₀) (dist p.2 ((m : ℝ) - 1 / 2)) < δ := by
    simpa only [Prod.dist_eq, Prod.fst, Prod.snd] using hp
  rw [max_lt_iff] at hp'
  obtain ⟨hpa, hpt⟩ := hp'
  rw [Real.dist_eq] at hpa hpt
  have hpa' : a₀ - 1 < p.1 ∧ p.1 < a₀ + 1 := by
    rw [abs_lt] at hpa
    constructor <;> linarith
  rcases lt_trichotomy p.2 ((m : ℝ) - 1 / 2) with hlt | heq | hgt
  · -- below the half integer: the previous cell
    have hle : p.2 < ((m : ℝ) - 1 / 2) ∧ ((m : ℝ) - 1 / 2) - δ < p.2 := by
      rw [abs_lt] at hpt
      exact ⟨hlt, by linarith [hpt.1]⟩
    have hmono1 : pruferStep p.1 (((m : ℝ) - 1 / 2) - δ) ≤ pruferStep p.1 p.2 :=
      pruferStep_mono _ (by linarith [hle.2])
    have hmono2 : pruferStep p.1 p.2 ≤ pruferStep p.1 ((m : ℝ) - 1 / 2) :=
      pruferStep_mono _ (le_of_lt hle.1)
    have hval : pruferStep p.1 (((m : ℝ) - 1 / 2) - δ) = (m : ℝ) - 1 / 2 +
        Real.arctan (Real.tan (Real.pi * (1 / 2 - δ)) - p.1) / Real.pi := by
      have hfl : ⌊(((m : ℝ) - 1 / 2) - δ) + 1 / 2⌋ = m - 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith [hδle4]
      have hne : (((m : ℝ) - 1 / 2) - δ) - ((m - 1 : ℤ) : ℝ) ≠ -1 / 2 := by
        push_cast; linarith [hδpos]
      have harg : Real.pi * ((((m : ℝ) - 1 / 2) - δ) - ((m - 1 : ℤ) : ℝ))
          = Real.pi * (1 / 2 - δ) := by
        push_cast; ring
      rw [pruferStep_eq_of_floor hfl hne, harg]
      push_cast
      ring
    have hbound : (m : ℝ) - ε' < pruferStep p.1 (((m : ℝ) - 1 / 2) - δ) := by
      rw [hval]
      have hleπ : Real.pi * (1 / 2 - δ₂) ≤ Real.pi * (1 / 2 - δ) := by
        have hp : Real.pi * δ ≤ Real.pi * δ₂ :=
          mul_le_mul_of_nonneg_left hδle₂ (le_of_lt hπpos)
        rw [mul_sub, mul_sub, mul_one_div]
        linarith [hp]
      have htanle : Real.tan (Real.pi * (1 / 2 - δ₂)) ≤ Real.tan (Real.pi * (1 / 2 - δ)) :=
        Real.strictMonoOn_tan.monotoneOn hIδ₂ hIδ hleπ
      have harg : Real.tan (Real.pi * (1 / 2 - ε')) <
          Real.tan (Real.pi * (1 / 2 - δ)) - p.1 := by
        linarith [htanle, hδ₂, hpa'.2]
      have harct : Real.pi * (1 / 2 - ε') <
          Real.arctan (Real.tan (Real.pi * (1 / 2 - δ)) - p.1) := by
        have h1 := Real.arctan_lt_arctan_iff.mpr harg
        rwa [Real.arctan_tan hIε'.1 hIε'.2] at h1
      have h2 : 1 / 2 - ε' <
          Real.arctan (Real.tan (Real.pi * (1 / 2 - δ)) - p.1) / Real.pi := by
        have h3 : (Real.pi * (1 / 2 - ε')) / Real.pi <
            Real.arctan (Real.tan (Real.pi * (1 / 2 - δ)) - p.1) / Real.pi :=
          div_lt_div_of_pos_right harct hπpos
        rwa [mul_div_cancel_left₀ _ (ne_of_gt hπpos)] at h3
      linarith
    have hdist : dist (pruferStep p.1 p.2) (pruferStep a₀ ((m : ℝ) - 1 / 2)) < ε := by
      rw [Real.dist_eq, hbase, abs_lt]
      have hm2 : pruferStep p.1 p.2 ≤ (m : ℝ) := by
        rw [← hbase' p.1]; exact hmono2
      exact ⟨by linarith [hbound, hmono1, hε'le], by linarith [hm2, hε'pos]⟩
    exact hdist
  · -- exactly at the half integer
    rw [heq, hbase, hbase' p.1, Real.dist_eq, sub_self, abs_zero]
    exact hε
  · -- above the half integer: the current cell
    have hle : ((m : ℝ) - 1 / 2) < p.2 ∧ p.2 < ((m : ℝ) - 1 / 2) + δ := by
      rw [abs_lt] at hpt
      exact ⟨hgt, by linarith [hpt.2]⟩
    have hmono1 : pruferStep p.1 ((m : ℝ) - 1 / 2) ≤ pruferStep p.1 p.2 :=
      pruferStep_mono _ (le_of_lt hle.1)
    have hmono2 : pruferStep p.1 p.2 ≤ pruferStep p.1 (((m : ℝ) - 1 / 2) + δ) :=
      pruferStep_mono _ (le_of_lt hle.2)
    have hval : pruferStep p.1 (((m : ℝ) - 1 / 2) + δ) = (m : ℝ) + 1 / 2 +
        Real.arctan (Real.tan (Real.pi * (δ - 1 / 2)) - p.1) / Real.pi := by
      have hfl : ⌊(((m : ℝ) - 1 / 2) + δ) + 1 / 2⌋ = m := by
        rw [Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith [hδle4]
      have hne : (((m : ℝ) - 1 / 2) + δ) - (m : ℝ) ≠ -1 / 2 := by linarith [hδpos]
      have harg : Real.pi * ((((m : ℝ) - 1 / 2) + δ) - (m : ℝ)) = Real.pi * (δ - 1 / 2) := by
        ring
      rw [pruferStep_eq_of_floor hfl hne, harg]
    have hbound : pruferStep p.1 (((m : ℝ) - 1 / 2) + δ) < (m : ℝ) + ε' := by
      rw [hval]
      have hleπ : Real.pi * (δ - 1 / 2) ≤ Real.pi * (δ₁ - 1 / 2) := by
        have hp : Real.pi * δ ≤ Real.pi * δ₁ :=
          mul_le_mul_of_nonneg_left hδle₁ (le_of_lt hπpos)
        rw [mul_sub, mul_sub, mul_one_div]
        linarith [hp]
      have htanle : Real.tan (Real.pi * (δ - 1 / 2)) ≤ Real.tan (Real.pi * (δ₁ - 1 / 2)) :=
        Real.strictMonoOn_tan.monotoneOn hJδ hJδ₁ hleπ
      have harg : Real.tan (Real.pi * (δ - 1 / 2)) - p.1 < Real.tan (Real.pi * (ε' - 1 / 2)) := by
        linarith [htanle, hδ₁, hpa'.1]
      have harct : Real.arctan (Real.tan (Real.pi * (δ - 1 / 2)) - p.1) <
          Real.pi * (ε' - 1 / 2) := by
        have h1 := Real.arctan_lt_arctan_iff.mpr harg
        rwa [Real.arctan_tan hJε'.1 hJε'.2] at h1
      have h2 : Real.arctan (Real.tan (Real.pi * (δ - 1 / 2)) - p.1) / Real.pi
          < ε' - 1 / 2 := by
        have h3 : Real.arctan (Real.tan (Real.pi * (δ - 1 / 2)) - p.1) / Real.pi <
            (Real.pi * (ε' - 1 / 2)) / Real.pi :=
          div_lt_div_of_pos_right harct hπpos
        rwa [mul_div_cancel_left₀ _ (ne_of_gt hπpos)] at h3
      linarith
    have hdist : dist (pruferStep p.1 p.2) (pruferStep a₀ ((m : ℝ) - 1 / 2)) < ε := by
      rw [Real.dist_eq, hbase, abs_lt]
      have hm1 : (m : ℝ) ≤ pruferStep p.1 p.2 := by
        rw [← hbase' p.1]; exact hmono1
      exact ⟨by linarith [hm1, hε'pos], by linarith [hmono2, hbound, hε'le]⟩
    exact hdist

theorem pruferStep_continuous : Continuous (fun p : ℝ × ℝ => pruferStep p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a₀, t₀⟩
  by_cases h : t₀ - ((⌊t₀ + 1 / 2⌋ : ℤ) : ℝ) = -1 / 2
  · have hlt : t₀ = ((⌊t₀ + 1 / 2⌋ : ℤ) : ℝ) - 1 / 2 := by linarith
    rw [hlt]
    exact pruferStep_continuousAt_half a₀ ⌊t₀ + 1 / 2⌋
  · exact pruferStep_continuousAt_of_floor h

end

end Work.TMComp.RotBasics
