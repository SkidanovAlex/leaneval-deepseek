import Mathlib
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.JordanSeparation.frontier_eq_trace

/-!
# A proper subcontinuum of a simple closed curve is an arc

`Work.Smooth.JordanSeparation.subcontinuum_trace_interval`: if `S` is a compact connected proper
subset of the trace of a simple closed plane curve `c`, then `S` is the image of a closed parameter
interval of length `< 2π`.  In particular `S` is a point or an arc, and `c.γ` is injective on that
interval.

The proof shifts the parametrisation so that the value at `0` lies outside `S`, so that the
parameter set `B = γ⁻¹(S) ∩ [0, 2π]` is contained in the open interval `(0, 2π)`, where `γ` is
injective.  Then `γ` identifies `B` with `S`, so `B` is an interval, and `B = [sInf B, sSup B]`.
-/

open Set Metric
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- The parameter of a curve point, reduced to `[0, 2π)`. -/
theorem gamma_sub_floor_eq (c : PlaneCurve) (t : ℝ) :
    c.γ (t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)) = c.γ t := by
  have h := c.apply_add_int_mul (t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi))
    ⌊t / (2 * Real.pi)⌋
  rw [show t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)
      + ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) = t from by ring] at h
  exact h.symm

theorem mem_Ico_floor (t : ℝ) :
    t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ∈ Set.Ico 0 (2 * Real.pi) := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · have := (le_div_iff₀ hpos).mp (Int.floor_le (t / (2 * Real.pi))); linarith
  · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (t / (2 * Real.pi))); linarith

/-- An integer multiple of `2π` of modulus `< 2π` is zero. -/
theorem int_eq_zero_of_mul_two_pi_abs_lt (k : ℤ) (h : |(k : ℝ) * (2 * Real.pi)| < 2 * Real.pi) :
    k = 0 := by
  have h2 : |(k : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
  have h3 : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos, h2]
  have h4 : |k| < 1 := by exact_mod_cast h3
  have h5 := abs_lt.mp h4
  omega

theorem subcontinuum_trace_interval (c : PlaneCurve) (hs : c.IsSimple) {S : Set ℂ}
    (hS : S ⊆ c.trace) (hSc : IsConnected S) (hScomp : IsCompact S) (hSne : S ≠ c.trace) :
    ∃ a b : ℝ, a ≤ b ∧ b - a < 2 * Real.pi ∧ S = c.γ '' (Set.Icc a b) := by
  -- a point of the trace outside `S`, and a parameter for it
  obtain ⟨p, hpK, hpS⟩ := Set.exists_of_ssubset (lt_of_le_of_ne hS hSne)
  rw [PlaneCurve.trace_eq_image_Ico] at hpK
  obtain ⟨τ₀, -, hτ₀val⟩ := hpK
  -- the shifted curve: its value at `0` is outside `S`
  set c' : PlaneCurve :=
    { γ := fun t => c.γ (t + τ₀)
      cont := c.cont.comp (continuous_id.add continuous_const)
      periodic := fun t => by
        show c.γ (t + 2 * Real.pi + τ₀) = c.γ (t + τ₀)
        rw [show t + 2 * Real.pi + τ₀ = (t + τ₀) + 2 * Real.pi from by ring, c.periodic_apply] }
    with hc'
  have hc'γ : c'.γ = fun t => c.γ (t + τ₀) := rfl
  have htrace : c'.trace = c.trace := by
    ext z; constructor
    · rintro ⟨t, rfl⟩; exact ⟨t + τ₀, rfl⟩
    · rintro ⟨t, rfl⟩; exact ⟨t - τ₀, by simp only [hc'γ]; ring_nf⟩
  have hsimp : c'.IsSimple := by
    intro a ha b hb hab
    obtain ⟨k, hk⟩ := PlaneCurve.IsSimple.eq_mod_period hs
      (show c.γ (a + τ₀) = c.γ (b + τ₀) from hab)
    have hk' : b - a = (k : ℝ) * (2 * Real.pi) := by linarith [hk]
    have h2 : |b - a| < 2 * Real.pi := by
      rw [abs_lt]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, Real.pi_pos]
    rw [hk'] at h2
    have hk0 : k = 0 := int_eq_zero_of_mul_two_pi_abs_lt k h2
    rw [hk0, Int.cast_zero, zero_mul] at hk'; linarith
  -- the parameter set
  set B : Set ℝ := {t : ℝ | c'.γ t ∈ S ∧ t ∈ Set.Icc 0 (2 * Real.pi)} with hBdef
  have hBcomp : IsCompact B := by
    have hclosed : IsClosed B := by
      rw [hBdef]
      exact (hScomp.isClosed.preimage c'.cont).inter isClosed_Icc
    exact (isCompact_Icc (a := (0:ℝ)) (b := 2 * Real.pi)).of_isClosed_subset hclosed
      (by intro t ht; rw [hBdef] at ht; exact ht.2)
  have hmemB_iff : ∀ t : ℝ, t ∈ B ↔ c'.γ t ∈ S ∧ t ∈ Set.Icc 0 (2 * Real.pi) := by
    intro t; rw [hBdef]; exact Iff.rfl
  have hB_mem : ∀ {t : ℝ}, c'.γ t ∈ S → t ∈ Set.Icc 0 (2 * Real.pi) → t ∈ B :=
    fun h1 h2 => (hmemB_iff _).mpr ⟨h1, h2⟩
  have hBne : B.Nonempty := by
    obtain ⟨x, hx⟩ := hSc.1
    have hx' : x ∈ c'.trace := htrace ▸ hS hx
    obtain ⟨t, ht⟩ := hx'
    refine ⟨t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi), hB_mem ?_ ?_⟩
    · rw [gamma_sub_floor_eq]; rw [ht]; exact hx
    · exact ⟨(mem_Ico_floor t).1, (mem_Ico_floor t).2.le⟩
  have hBsub : B ⊆ Set.Ioo 0 (2 * Real.pi) := by
    intro t ht
    obtain ⟨htS, htI⟩ := (hmemB_iff t).mp ht
    have hγ0 : c'.γ 0 = p := by simp only [hc'γ]; rw [zero_add]; exact hτ₀val
    have hγ2 : c'.γ (2 * Real.pi) = p := by
      simp only [hc'γ]
      rw [show 2 * Real.pi + τ₀ = τ₀ + 2 * Real.pi from by ring, c.periodic_apply]
      exact hτ₀val
    rw [Set.mem_Ioo]
    refine ⟨?_, ?_⟩
    · rcases lt_or_eq_of_le htI.1 with h | h
      · exact h
      · exact absurd (hγ0 ▸ (h ▸ htS)) hpS
    · rcases lt_or_eq_of_le htI.2 with h | h
      · exact h
      · exact absurd (hγ2 ▸ (h ▸ htS)) hpS
  have hinj : Set.InjOn c'.γ B := by
    intro a ha b hb hab
    obtain ⟨k, hk⟩ := PlaneCurve.IsSimple.eq_mod_period hsimp hab
    have hk' : b - a = (k : ℝ) * (2 * Real.pi) := by linarith [hk]
    have haI := hBsub ha
    have hbI := hBsub hb
    have h2 : |b - a| < 2 * Real.pi := by
      rw [abs_lt]; constructor <;> linarith [haI.1, haI.2, hbI.1, hbI.2]
    rw [hk'] at h2
    have hk0 : k = 0 := int_eq_zero_of_mul_two_pi_abs_lt k h2
    rw [hk0, Int.cast_zero, zero_mul] at hk'; linarith
  have himage : c'.γ '' B = S := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩; exact (hmemB_iff t).mp ht |>.1
    · intro z hz
      have hz' : z ∈ c'.trace := htrace ▸ hS hz
      obtain ⟨t, ht⟩ := hz'
      have hmem : c'.γ (t - ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi)) ∈ c'.γ '' B :=
        Set.mem_image_of_mem c'.γ (hB_mem (by rw [gamma_sub_floor_eq]; rw [ht]; exact hz)
          ⟨(mem_Ico_floor t).1, (mem_Ico_floor t).2.le⟩)
      rwa [gamma_sub_floor_eq, ht] at hmem
  -- `B` is an interval
  have hord : B.OrdConnected := by
    refine ⟨?_⟩
    rintro a ha b hb z hz
    rw [Set.mem_Icc] at hz
    obtain ⟨haz, hzb⟩ := hz
    by_contra hzB
    have hne1 : (c'.γ '' (B ∩ Set.Iic z)).Nonempty := ⟨c'.γ a, a, ⟨ha, haz⟩, rfl⟩
    have hne2 : (c'.γ '' (B ∩ Set.Ici z)).Nonempty := ⟨c'.γ b, b, ⟨hb, hzb⟩, rfl⟩
    have hcov : S ⊆ c'.γ '' (B ∩ Set.Iic z) ∪ c'.γ '' (B ∩ Set.Ici z) := by
      intro z hz
      rw [← himage] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      rcases le_total t z with h | h
      · exact Or.inl ⟨t, ⟨ht, h⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨ht, h⟩, rfl⟩
    have hdisj : Disjoint (c'.γ '' (B ∩ Set.Iic z)) (c'.γ '' (B ∩ Set.Ici z)) := by
      rw [Set.disjoint_left]
      rintro z ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, h₂⟩
      have heq : t₁ = t₂ := hinj ht₁.1 ht₂.1 h₂.symm
      have hcx : t₁ = z := le_antisymm ht₁.2 (heq ▸ ht₂.2)
      exact hzB (hcx ▸ ht₁.1)
    have hcl1 : IsClosed (c'.γ '' (B ∩ Set.Iic z)) :=
      ((hBcomp.inter_right isClosed_Iic).image c'.cont).isClosed
    have hcl2 : IsClosed (c'.γ '' (B ∩ Set.Ici z)) := by
      rw [Set.inter_comm]
      exact ((hBcomp.inter_left isClosed_Ici).image c'.cont).isClosed
    have hdisj' : S ∩ ((c'.γ '' (B ∩ Set.Iic z)) ∩ (c'.γ '' (B ∩ Set.Ici z))) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hz1, hz2⟩
      exact Set.disjoint_left.mp hdisj hz1 hz2
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hSc.2)
      (c'.γ '' (B ∩ Set.Iic z)) (c'.γ '' (B ∩ Set.Ici z)) hcl1 hcl2 hcov hdisj' with h | h
    · obtain ⟨w, hw⟩ := hne2
      rw [Set.mem_image] at hw
      obtain ⟨s, hsX, hsw⟩ := hw
      have hwS : w ∈ S := hsw ▸ (hmemB_iff s).mp hsX.1 |>.1
      have hwY : w ∈ c'.γ '' (B ∩ Set.Ici z) := ⟨s, hsX, hsw⟩
      exact absurd hwY (Set.disjoint_left.mp hdisj (h hwS))
    · obtain ⟨w, hw⟩ := hne1
      rw [Set.mem_image] at hw
      obtain ⟨s, hsX, hsw⟩ := hw
      have hwS : w ∈ S := hsw ▸ (hmemB_iff s).mp hsX.1 |>.1
      have hwX : w ∈ c'.γ '' (B ∩ Set.Iic z) := ⟨s, hsX, hsw⟩
      exact absurd hwX (Set.disjoint_right.mp hdisj (h hwS))
  obtain ⟨a, haB, haleast⟩ := hBcomp.exists_isLeast hBne
  obtain ⟨b, hbB, hbgreatest⟩ := hBcomp.exists_isGreatest hBne
  have hBeq : B = Set.Icc a b := by
    apply Set.Subset.antisymm
    · intro x hx; exact ⟨haleast hx, hbgreatest hx⟩
    · intro x hx; exact hord.out' haB hbB ⟨hx.1, hx.2⟩
  have hab : a ≤ b := haleast hbB
  refine ⟨τ₀ + a, τ₀ + b, by linarith, ?_, ?_⟩
  · have h1 := (hBsub haB).1
    have h2 := (hBsub hbB).2
    linarith
  · rw [← himage, hBeq]
    rw [show c'.γ = fun t => c.γ (t + τ₀) from rfl, ← Set.image_image]
    congr 1
    ext t
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨s, ⟨h1, h2⟩, rfl⟩; exact ⟨by linarith, by linarith⟩
    · intro h; exact ⟨t - τ₀, ⟨by linarith [h.1], by linarith [h.2]⟩, by ring⟩

end

end Work.Smooth.JordanSeparation
