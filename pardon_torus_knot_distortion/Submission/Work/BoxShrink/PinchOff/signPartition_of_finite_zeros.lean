import Mathlib

namespace Work.BoxShrink.PinchOff

open Set

noncomputable section

/-!
# The sign partition of a continuous `2π`-periodic function with finitely many zeros

The main result `signPartition_of_finite_zeros` splits the circle of a continuous `2π`-periodic
real function `g` with finitely many zeros (in one period) into finitely many alternating
monochromatic arcs, starting with a nonnegative one, unless `g` is everywhere nonnegative or
everywhere nonpositive.

The proof works with the *crossings* of `g`: points where `g` vanishes with a definite one-sided
sign on each side (`Up`: negative left, positive right; `Down`: positive left, negative right).
Starting from a crossing of type `Up` the *walk* alternates between `g` and `-g`; each step is the
end of the current monochromatic run (`nxtUp`).  Because there are only finitely many zeros in a
period, the walk returns to its starting point after a whole period, and the visited crossings give
the required partition.
-/

/-- `Up g z`: `g` is negative on a left-neighbourhood and positive on a right-neighbourhood of `z`. -/
def Up (g : ℝ → ℝ) (z : ℝ) : Prop :=
  ∃ ε > 0, (∀ x, z - ε < x → x < z → g x < 0) ∧ (∀ x, z < x → x < z + ε → 0 < g x)

/-- `Down g z`: `g` is positive on a left-neighbourhood and negative on a right-neighbourhood of `z`. -/
def Down (g : ℝ → ℝ) (z : ℝ) : Prop :=
  ∃ ε > 0, (∀ x, z - ε < x → x < z → 0 < g x) ∧ (∀ x, z < x → x < z + ε → g x < 0)

/-- A point where the sign of `g` flips. -/
def Cross (g : ℝ → ℝ) (z : ℝ) : Prop := Up g z ∨ Down g z

/-- The points strictly to the right of `x` where `g` is negative. -/
def negTail (g : ℝ → ℝ) (x : ℝ) : Set ℝ := {t | x < t ∧ g t < 0}

/-- The first point to the right of `x` where `g` becomes negative. -/
def nxtUp (g : ℝ → ℝ) (x : ℝ) : ℝ := sInf (negTail g x)

/-! ## Elementary facts about the crossings -/

lemma Up_zero {g : ℝ → ℝ} (hg : Continuous g) {z : ℝ} (h : Up g z) : g z = 0 := by
  obtain ⟨ε, hε, hleft, hright⟩ := h
  have hleft' : g (z - ε/2) < 0 := hleft _ (by linarith) (by linarith)
  have hright' : 0 < g (z + ε/2) := hright _ (by linarith) (by linarith)
  apply le_antisymm
  · by_contra hcon
    push Not at hcon
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo (show z - ε/2 ≤ z by linarith) hg.continuousOn
      (show (0:ℝ) ∈ Ioo (g (z - ε/2)) (g z) from ⟨hleft', hcon⟩)
    exact absurd hc0 (ne_of_lt (hleft c (by linarith [hc.1]) hc.2))
  · by_contra hcon
    push Not at hcon
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo (show z ≤ z + ε/2 by linarith) hg.continuousOn
      (show (0:ℝ) ∈ Ioo (g z) (g (z + ε/2)) from ⟨hcon, hright'⟩)
    exact absurd hc0 (ne_of_gt (hright c hc.1 (by linarith [hc.2])))

lemma Up_neg {g : ℝ → ℝ} {z : ℝ} : Up (fun t => -g t) z ↔ Down g z := by
  constructor
  · rintro ⟨ε, hε, hl, hr⟩
    exact ⟨ε, hε, fun x h1 h2 => neg_lt_zero.mp (hl x h1 h2), fun x h1 h2 => neg_pos.mp (hr x h1 h2)⟩
  · rintro ⟨ε, hε, hl, hr⟩
    exact ⟨ε, hε, fun x h1 h2 => neg_lt_zero.mpr (hl x h1 h2), fun x h1 h2 => neg_pos.mpr (hr x h1 h2)⟩

lemma Down_neg {g : ℝ → ℝ} {z : ℝ} : Down (fun t => -g t) z ↔ Up g z := by
  constructor
  · rintro ⟨ε, hε, hl, hr⟩
    exact ⟨ε, hε, fun x h1 h2 => neg_pos.mp (hl x h1 h2), fun x h1 h2 => neg_lt_zero.mp (hr x h1 h2)⟩
  · rintro ⟨ε, hε, hl, hr⟩
    exact ⟨ε, hε, fun x h1 h2 => neg_pos.mpr (hl x h1 h2), fun x h1 h2 => neg_lt_zero.mpr (hr x h1 h2)⟩

lemma Cross_neg {g : ℝ → ℝ} {z : ℝ} : Cross (fun t => -g t) z ↔ Cross g z := by
  constructor
  · rintro (h | h)
    · exact Or.inr (Up_neg.mp h)
    · exact Or.inl (Down_neg.mp h)
  · rintro (h | h)
    · exact Or.inr (Down_neg.mpr h)
    · exact Or.inl (Up_neg.mpr h)

lemma Down_zero {g : ℝ → ℝ} (hg : Continuous g) {z : ℝ} (h : Down g z) : g z = 0 := by
  have h1 : Up (fun t => -g t) z := Up_neg.mpr h
  have h2 := Up_zero hg.neg h1
  simpa using h2

lemma Up_not_down {g : ℝ → ℝ} {z : ℝ} (hu : Up g z) (hd : Down g z) : False := by
  obtain ⟨ε, hε, hl, hr⟩ := hu
  obtain ⟨ε', hε', hl', hr'⟩ := hd
  have hm : (0:ℝ) < min ε ε' := lt_min hε hε'
  have h1 : g (z - min ε ε' / 2) < 0 :=
    hl _ (by linarith [hm, min_le_left ε ε']) (by linarith [hm])
  have h2 : 0 < g (z - min ε ε' / 2) :=
    hl' _ (by linarith [hm, min_le_right ε ε']) (by linarith [hm])
  linarith

/-! ## Periodicity -/

lemma Up_add_period {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t) (z : ℝ) :
    Up g (z + 2 * Real.pi) ↔ Up g z := by
  have hperx : ∀ x : ℝ, g (x - 2 * Real.pi) = g x := by
    intro x
    have h' := hper (x - 2 * Real.pi)
    rw [show x - 2 * Real.pi + 2 * Real.pi = x by ring] at h'
    exact h'.symm
  constructor
  · rintro ⟨ε, hε, hl, hr⟩
    refine ⟨ε, hε, ?_, ?_⟩
    · intro x h1 h2
      have h := hl (x + 2 * Real.pi) (by linarith) (by linarith)
      rwa [hper x] at h
    · intro x h1 h2
      have h := hr (x + 2 * Real.pi) (by linarith) (by linarith)
      rwa [hper x] at h
  · rintro ⟨ε, hε, hl, hr⟩
    refine ⟨ε, hε, ?_, ?_⟩
    · intro x h1 h2
      have h := hl (x - 2 * Real.pi) (by linarith) (by linarith)
      rwa [hperx x] at h
    · intro x h1 h2
      have h := hr (x - 2 * Real.pi) (by linarith) (by linarith)
      rwa [hperx x] at h

lemma Up_int_period {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t) (z : ℝ) (m : ℤ) :
    Up g (z + (m : ℝ) * (2 * Real.pi)) ↔ Up g z := by
  have hp : Function.Periodic g (2 * Real.pi) := hper
  have hint : ∀ t : ℝ, g (t + (m : ℝ) * (2 * Real.pi)) = g t := fun t => hp.int_mul m t
  constructor
  · rintro ⟨ε, hε, hl, hr⟩
    refine ⟨ε, hε, ?_, ?_⟩
    · intro x h1 h2
      have h := hl (x + (m : ℝ) * (2 * Real.pi)) (by linarith) (by linarith)
      rwa [hint x] at h
    · intro x h1 h2
      have h := hr (x + (m : ℝ) * (2 * Real.pi)) (by linarith) (by linarith)
      rwa [hint x] at h
  · rintro ⟨ε, hε, hl, hr⟩
    have hperx : ∀ x : ℝ, g (x - (m : ℝ) * (2 * Real.pi)) = g x := by
      intro x
      have h' := hint (x - (m : ℝ) * (2 * Real.pi))
      rw [show x - (m : ℝ) * (2 * Real.pi) + (m : ℝ) * (2 * Real.pi) = x by ring] at h'
      exact h'.symm
    refine ⟨ε, hε, ?_, ?_⟩
    · intro x h1 h2
      have h := hl (x - (m : ℝ) * (2 * Real.pi)) (by linarith) (by linarith)
      rwa [hperx x] at h
    · intro x h1 h2
      have h := hr (x - (m : ℝ) * (2 * Real.pi)) (by linarith) (by linarith)
      rwa [hperx x] at h

/-! ## The first point where `g` becomes negative

`nxtUp g x` is the right end of the monochromatic run of `g` starting at `x` whenever `Up g x`. -/

lemma negTail_nonempty {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hneg : ∃ q : ℝ, g q < 0) (x : ℝ) : (negTail g x).Nonempty := by
  obtain ⟨q, hq⟩ := hneg
  have hp : Function.Periodic g (2 * Real.pi) := hper
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((x - q) / (2 * Real.pi))
  refine ⟨q + (n:ℝ) * (2 * Real.pi), ?_, ?_⟩
  · have h1 : (x - q) / (2 * Real.pi) < (n:ℝ) := hn
    rw [div_lt_iff₀ hpi] at h1
    linarith
  · rw [hp.nat_mul n q]; exact hq

lemma negTail_bddBelow (g : ℝ → ℝ) (x : ℝ) : BddBelow (negTail g x) :=
  bddBelow_Ioi.mono (fun t ht => ht.1)

lemma lt_nxtUp {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hneg : ∃ q : ℝ, g q < 0) {x : ℝ} (hx : Up g x) : x < nxtUp g x := by
  obtain ⟨ε, hε, hl, hr⟩ := hx
  have hne := negTail_nonempty hper hneg x
  have hkey : x + ε ≤ nxtUp g x := by
    refine le_csInf hne ?_
    intro b hb
    rcases hb with ⟨hxb, hfb⟩
    by_contra hcon
    push Not at hcon
    exact absurd (hr b hxb hcon) (not_lt.mpr (le_of_lt hfb))
  linarith

lemma nonneg_nxtUp {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hneg : ∃ q : ℝ, g q < 0) (hg : Continuous g) {x : ℝ} (hx : Up g x) :
    ∀ y ∈ Icc x (nxtUp g x), 0 ≤ g y := by
  have hne := negTail_nonempty hper hneg x
  have hbdd := negTail_bddBelow g x
  have hxlt := lt_nxtUp hper hneg hx
  have hx0 := Up_zero hg hx
  have hsInf_notmem : nxtUp g x ∉ negTail g x := by
    intro hmem
    have hopen : IsOpen (negTail g x) := by
      have heq : negTail g x = Ioi x ∩ g ⁻¹' (Iio 0) := by
        ext t; simp [negTail]
      rw [heq]
      exact isOpen_Ioi.inter (hg.isOpen_preimage _ isOpen_Iio)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen _ hmem
    have h2 : nxtUp g x - δ/2 ∈ negTail g x :=
      hδ (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have h3 := csInf_le hbdd h2
    simp only [nxtUp] at h3
    linarith
  intro y hy
  rcases hy with ⟨hyx, hyu⟩
  rcases lt_or_eq_of_le hyu with hylt | hyeq
  · by_contra hcon
    push Not at hcon
    rcases lt_or_eq_of_le hyx with hxylt | hxyeq
    · have hmem : y ∈ negTail g x := ⟨hxylt, hcon⟩
      have h3 := csInf_le hbdd hmem
      simp only [nxtUp] at h3 hyu hylt
      linarith
    · rw [← hxyeq] at hcon; linarith
  · rw [hyeq]
    by_contra hcon
    push Not at hcon
    exact hsInf_notmem ⟨hxlt, hcon⟩

lemma nxtUp_zero {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hneg : ∃ q : ℝ, g q < 0) (hg : Continuous g) {x : ℝ} (hx : Up g x) :
    g (nxtUp g x) = 0 := by
  have hne := negTail_nonempty hper hneg x
  have hbdd := negTail_bddBelow g x
  have hxlt := lt_nxtUp hper hneg hx
  have hge : 0 ≤ g (nxtUp g x) := nonneg_nxtUp hper hneg hg hx _ ⟨le_of_lt hxlt, le_refl _⟩
  apply le_antisymm _ hge
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ t in nhds (nxtUp g x), 0 < g t :=
    hg.continuousAt.eventually (isOpen_Ioi.mem_nhds hcon)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  obtain ⟨b, hb, hblt⟩ := (csInf_lt_iff hbdd hne).mp (show nxtUp g x < nxtUp g x + δ by linarith)
  have hsle : nxtUp g x ≤ b := csInf_le hbdd hb
  have hbgt : nxtUp g x < b := by
    refine lt_of_le_of_ne hsle ?_
    rintro rfl
    exact absurd hb.2 (not_lt.mpr (le_of_lt hcon))
  have : dist b (nxtUp g x) < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  exact absurd (hδ this) (not_lt.mpr (le_of_lt hb.2))

/-! ## Finiteness and isolation of the zeros -/

lemma zeros_sym_finite {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) :
    ({t : ℝ | t ∈ Icc (-(2 * Real.pi)) (4 * Real.pi) ∧ g t = 0}).Finite := by
  have h1 : ({t : ℝ | t ∈ Icc (2 * Real.pi) (4 * Real.pi) ∧ g t = 0}).Finite := by
    have hper' : ∀ t : ℝ, g (t - 2 * Real.pi) = g t := by
      intro t
      have h' := hper (t - 2 * Real.pi)
      rw [show t - 2 * Real.pi + 2 * Real.pi = t by ring] at h'
      exact h'.symm
    refine Set.Finite.subset (hfin.image (fun t => t + 2 * Real.pi)) ?_
    rintro t ⟨htI, htf⟩
    refine ⟨t - 2 * Real.pi, ?_, by ring⟩
    exact ⟨⟨by linarith [htI.1], by linarith [htI.2]⟩, by rwa [hper' t]⟩
  have h2 : ({t : ℝ | t ∈ Icc (-(2 * Real.pi)) 0 ∧ g t = 0}).Finite := by
    refine Set.Finite.subset (hfin.image (fun t => t - 2 * Real.pi)) ?_
    rintro t ⟨htI, htf⟩
    refine ⟨t + 2 * Real.pi, ?_, by ring⟩
    exact ⟨⟨by linarith [htI.1], by linarith [htI.2]⟩, by rw [hper]; exact htf⟩
  refine Set.Finite.subset ((h2.union hfin).union h1) ?_
  rintro t ⟨htI, htf⟩
  rcases htI with ⟨ht1, ht2⟩
  rcases lt_or_ge t 0 with h | h
  · exact Or.inl (Or.inl ⟨⟨ht1, le_of_lt h⟩, htf⟩)
  · rcases lt_or_ge (2 * Real.pi) t with h' | h'
    · exact Or.inr ⟨⟨le_of_lt h', ht2⟩, htf⟩
    · exact Or.inl (Or.inr ⟨⟨h, h'⟩, htf⟩)

lemma zero_isolated {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) {z : ℝ} (hz : g z = 0) :
    ∃ ε > 0, ∀ w : ℝ, g w = 0 → |w - z| < ε → w = z := by
  have hp : Function.Periodic g (2 * Real.pi) := hper
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hS := zeros_sym_finite hper hfin
  set m : ℤ := ⌊z / (2 * Real.pi)⌋ with hm
  have hmle : (m:ℝ) * (2 * Real.pi) ≤ z := by
    have h := Int.floor_le (z / (2 * Real.pi))
    rw [hm]
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hpi)
    rwa [div_mul_cancel₀ z (ne_of_gt hpi)] at h2
  have hmlt : z < ((m:ℝ) + 1) * (2 * Real.pi) := by
    have h := Int.lt_floor_add_one (z / (2 * Real.pi))
    rw [hm]
    have h2 := mul_lt_mul_of_pos_right h hpi
    rwa [div_mul_cancel₀ z (ne_of_gt hpi)] at h2
  set z' : ℝ := z - (m:ℝ) * (2 * Real.pi) with hz'def
  have hz'0 : g z' = 0 := by
    have h := hp.int_mul m (z - (m:ℝ)*(2*Real.pi))
    rw [show z - (m:ℝ)*(2*Real.pi) + (m:ℝ)*(2*Real.pi) = z by ring] at h
    rw [hz'def, ← h]; exact hz
  have hz'ge : 0 ≤ z' := by rw [hz'def]; linarith
  have hz'lt : z' < 2 * Real.pi := by rw [hz'def]; linarith
  have hS' : (({t : ℝ | t ∈ Icc (-(2*Real.pi)) (4*Real.pi) ∧ g t = 0}) \ {z'}).Finite :=
    hS.subset (fun t ht => ht.1)
  have hopen : IsOpen (({t : ℝ | t ∈ Icc (-(2*Real.pi)) (4*Real.pi) ∧ g t = 0} \ {z'})ᶜ) :=
    isOpen_compl_iff.mpr hS'.isClosed
  have hz'mem : z' ∈ (({t : ℝ | t ∈ Icc (-(2*Real.pi)) (4*Real.pi) ∧ g t = 0} \ {z'})ᶜ) := by
    simp
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := Metric.isOpen_iff.mp hopen z' hz'mem
  refine ⟨min ε₀ (2 * Real.pi), lt_min hε₀pos hpi, ?_⟩
  intro w hw0 hwlt
  set w' : ℝ := w - (m:ℝ) * (2 * Real.pi) with hw'def
  have hw'0 : g w' = 0 := by
    have h := hp.int_mul m (w - (m:ℝ)*(2*Real.pi))
    rw [show w - (m:ℝ)*(2*Real.pi) + (m:ℝ)*(2*Real.pi) = w by ring] at h
    rw [hw'def, ← h]; exact hw0
  have hwd : w' - z' = w - z := by rw [hw'def, hz'def]; ring
  have hdist : dist w' z' < ε₀ := by
    rw [Real.dist_eq, hwd]
    exact lt_of_lt_of_le hwlt (min_le_left _ _)
  have hmem : w' ∈ Metric.ball z' ε₀ := by rwa [Metric.mem_ball]
  have hnotmem := hε₀ hmem
  have hw'abs : |w' - z'| < 2 * Real.pi := by
    rw [hwd]; exact lt_of_lt_of_le hwlt (min_le_right _ _)
  have hw'I : w' ∈ Icc (-(2*Real.pi)) (4*Real.pi) := by
    constructor
    · have h3 : z' - 2 * Real.pi < w' := by linarith [(abs_lt.mp hw'abs).1]
      linarith
    · have h3 : w' < z' + 2 * Real.pi := by linarith [(abs_lt.mp hw'abs).2]
      linarith
  have hw'S : w' ∈ ({t : ℝ | t ∈ Icc (-(2*Real.pi)) (4*Real.pi) ∧ g t = 0}) := ⟨hw'I, hw'0⟩
  have hw'eq : w' = z' := by
    by_contra hne
    exact hnotmem ⟨hw'S, hne⟩
  rw [hw'def, hz'def] at hw'eq
  linarith

/-! ## The run end `nxtUp` -/

lemma down_nxtUp {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) (hg : Continuous g)
    (hneg : ∃ q : ℝ, g q < 0) {x : ℝ} (hx : Up g x) : Down g (nxtUp g x) := by
  have hs0 : g (nxtUp g x) = 0 := nxtUp_zero hper hneg hg hx
  have hxlt : x < nxtUp g x := lt_nxtUp hper hneg hx
  have hnn := nonneg_nxtUp hper hneg hg hx
  obtain ⟨εiso, hεisopos, hiso⟩ := zero_isolated hper hfin hs0
  have hne := negTail_nonempty hper hneg x
  have hbdd := negTail_bddBelow g x
  have hηpos : (0:ℝ) < min εiso (nxtUp g x - x) := lt_min hεisopos (by linarith)
  refine ⟨min εiso (nxtUp g x - x), hηpos, ?_, ?_⟩
  · intro y hy1 hy2
    have hyge : x ≤ y := by
      have h1 : min εiso (nxtUp g x - x) ≤ nxtUp g x - x := min_le_right _ _
      linarith
    have h1 := hnn y ⟨hyge, le_of_lt hy2⟩
    by_contra hcon
    push Not at hcon
    have hy0 : g y = 0 := le_antisymm hcon h1
    have hys : |y - nxtUp g x| < εiso := by
      rw [abs_of_neg (by linarith)]
      have h2 : min εiso (nxtUp g x - x) ≤ εiso := min_le_left _ _
      linarith
    have h3 := hiso y hy0 hys
    linarith
  · intro y hy1 hy2
    have hyabs : |y - nxtUp g x| < εiso := by
      rw [abs_of_pos (by linarith)]
      have h2 : min εiso (nxtUp g x - x) ≤ εiso := min_le_left _ _
      linarith
    obtain ⟨b, hb, hblt⟩ :=
      (csInf_lt_iff hbdd hne).mp (show nxtUp g x < nxtUp g x + min εiso (nxtUp g x - x) by
        linarith [hηpos])
    have hsle : nxtUp g x ≤ b := csInf_le hbdd hb
    have hbgt : nxtUp g x < b := by
      refine lt_of_le_of_ne hsle ?_
      rintro rfl
      linarith [hs0, hb.2]
    by_contra hcon
    push Not at hcon
    have hzero : ∃ c, g c = 0 ∧ nxtUp g x < c ∧ c < nxtUp g x + min εiso (nxtUp g x - x) := by
      rcases lt_trichotomy y b with h | h | h
      · rcases eq_or_lt_of_le hcon with hy0 | hypos
        · exact ⟨y, hy0.symm, hy1, hy2⟩
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' (le_of_lt h) hg.continuousOn
            (show (0:ℝ) ∈ Ioo (g b) (g y) from ⟨hb.2, hypos⟩)
          exact ⟨c, hc0, by linarith [hy1, hc.1], by linarith [hblt, hc.2]⟩
      · rw [h] at hcon; exact absurd hb.2 (not_lt.mpr hcon)
      · rcases eq_or_lt_of_le hcon with hy0 | hypos
        · exact ⟨y, hy0.symm, hy1, hy2⟩
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo (le_of_lt h) hg.continuousOn
            (show (0:ℝ) ∈ Ioo (g b) (g y) from ⟨hb.2, hypos⟩)
          exact ⟨c, hc0, by linarith [hbgt, hc.1], by linarith [hy2, hc.2]⟩
    obtain ⟨c, hc0, hc1, hc2⟩ := hzero
    have hcabs : |c - nxtUp g x| < εiso := by
      rw [abs_of_pos (by linarith)]
      have h2 : min εiso (nxtUp g x - x) ≤ εiso := min_le_left _ _
      linarith
    have h4 := hiso c hc0 hcabs
    linarith

lemma no_cross_nxtUp {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hneg : ∃ q : ℝ, g q < 0) (hg : Continuous g) {x : ℝ} (hx : Up g x) :
    ∀ w, x < w → w < nxtUp g x → ¬ Cross g w := by
  have hnn := nonneg_nxtUp hper hneg hg hx
  intro w hw1 hw2 hcross
  rcases hcross with hu | hd
  · obtain ⟨ε, hε, hl, hr⟩ := hu
    have hmp : (0:ℝ) < min ε (w - x) := lt_min hε (by linarith)
    have hc1 : x < w - min ε (w - x)/2 := by
      have h := min_le_right ε (w - x); linarith
    have hc2 : w - min ε (w - x)/2 < w := by linarith
    have hc3 : w - ε < w - min ε (w - x)/2 := by
      have h := min_le_left ε (w - x); linarith
    have hmem : w - min ε (w - x)/2 ∈ Icc x (nxtUp g x) :=
      ⟨le_of_lt hc1, le_of_lt (lt_trans hc2 hw2)⟩
    have hpos := hnn _ hmem
    have hneg' := hl _ hc3 hc2
    linarith
  · obtain ⟨ε, hε, hl, hr⟩ := hd
    have hmp : (0:ℝ) < min ε (nxtUp g x - w) := lt_min hε (by linarith)
    have hc1 : w < w + min ε (nxtUp g x - w)/2 := by linarith
    have hc2 : w + min ε (nxtUp g x - w)/2 < nxtUp g x := by
      have h := min_le_right ε (nxtUp g x - w); linarith
    have hc3 : w + min ε (nxtUp g x - w)/2 < w + ε := by
      have h := min_le_left ε (nxtUp g x - w); linarith
    have hmem : w + min ε (nxtUp g x - w)/2 ∈ Icc x (nxtUp g x) :=
      ⟨by linarith, le_of_lt hc2⟩
    have hpos := hnn _ hmem
    have hneg' := hr _ hc1 hc3
    linarith

/-! ## Existence of a crossing of type `Up` -/

lemma sign_const_of_no_zero {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Ioo a b, g x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < g x) ∨ (∀ x ∈ Ioo a b, g x < 0) := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · exact Or.inl (by intro x hx; exact absurd hx (by simp))
  · by_cases hex : ∃ x ∈ Ioo a b, 0 < g x
    · left
      intro y hy
      by_contra hcon
      push Not at hcon
      obtain ⟨x, hx, hxpos⟩ := hex
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · rcases eq_or_lt_of_le hcon with hy0 | hyneg
        · exact h y hy hy0
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' (le_of_lt hxy) hg.continuousOn
            (show (0:ℝ) ∈ Ioo (g y) (g x) from ⟨hyneg, hxpos⟩)
          exact h c ⟨lt_trans hx.1 hc.1, lt_trans hc.2 hy.2⟩ hc0
      · rw [hxy] at hxpos; linarith [hcon, hxpos]
      · rcases eq_or_lt_of_le hcon with hy0 | hyneg
        · exact h y hy hy0
        · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo (le_of_lt hxy) hg.continuousOn
            (show (0:ℝ) ∈ Ioo (g y) (g x) from ⟨hyneg, hxpos⟩)
          exact h c ⟨lt_trans hy.1 hc.1, lt_trans hc.2 hx.2⟩ hc0
    · right
      push Not at hex
      intro y hy
      rcases lt_trichotomy (g y) 0 with hh | hh | hh
      · exact hh
      · exact absurd hh (h y hy)
      · exact absurd hh (not_lt.mpr (hex y hy))

lemma exists_Up {g : ℝ → ℝ} (hg : Continuous g)
    (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite)
    {a b : ℝ} (hab : a < b) (hb : 0 < g b) (ha : g a < 0) :
    ∃ z, a < z ∧ z ≤ b ∧ Up g z := by
  set A : Set ℝ := {t | a < t ∧ t ≤ b ∧ 0 < g t} with hAdef
  have hbA : b ∈ A := ⟨hab, le_refl b, hb⟩
  have hAne : A.Nonempty := ⟨b, hbA⟩
  have hAbdd : BddBelow A := ⟨a, fun t ht => le_of_lt ht.1⟩
  have hzb : sInf A ≤ b := csInf_le hAbdd hbA
  have hza : a ≤ sInf A := le_csInf hAne (fun t ht => le_of_lt ht.1)
  have hpoint : ∀ η > 0, ∃ t ∈ A, sInf A ≤ t ∧ t < sInf A + η := by
    intro η hη
    obtain ⟨t, htA, htlt⟩ :=
      (csInf_lt_iff hAbdd hAne).mp (show sInf A < sInf A + η by linarith)
    exact ⟨t, htA, csInf_le hAbdd htA, htlt⟩
  have hgz_ge : 0 ≤ g (sInf A) := by
    by_contra hcon
    push Not at hcon
    have hev : ∀ᶠ t in nhds (sInf A), g t < 0 :=
      hg.continuousAt.eventually (isOpen_Iio.mem_nhds hcon)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    obtain ⟨t, htA, hzt, htlt⟩ := hpoint δ hδpos
    have : dist t (sInf A) < δ := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    exact absurd (hδ this) (not_lt.mpr (le_of_lt htA.2.2))
  have hznotA : sInf A ∉ A := by
    intro hmem
    have hzgt_a : a < sInf A := hmem.1
    have hev : ∀ᶠ t in nhds (sInf A), 0 < g t :=
      hg.continuousAt.eventually (isOpen_Ioi.mem_nhds hmem.2.2)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    have hminpos : (0:ℝ) < min δ (sInf A - a) := lt_min hδpos (by linarith)
    set c : ℝ := sInf A - min δ (sInf A - a) / 2 with hcdef
    have hca : a < c := by
      have h := min_le_right δ (sInf A - a); rw [hcdef]; linarith
    have hcz : c < sInf A := by rw [hcdef]; linarith
    have hcb : c ≤ b := le_trans (le_of_lt hcz) hzb
    have hcg : 0 < g c := by
      apply hδ
      rw [Real.dist_eq, abs_of_neg (by rw [hcdef]; linarith)]
      have h := min_le_left δ (sInf A - a); rw [hcdef]; linarith
    have hcA : c ∈ A := ⟨hca, hcb, hcg⟩
    have h4 := csInf_le hAbdd hcA
    linarith
  have hgz_le : g (sInf A) ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hza' : a < sInf A := by
      rcases lt_or_eq_of_le hza with h | h
      · exact h
      · exact absurd (h ▸ hcon) (not_lt.mpr (le_of_lt ha))
    exact hznotA ⟨hza', hzb, hcon⟩
  have hgz : g (sInf A) = 0 := le_antisymm hgz_le hgz_ge
  have hzgt : a < sInf A := by
    rcases lt_or_eq_of_le hza with h | h
    · exact h
    · exfalso; rw [← h] at hgz; linarith
  obtain ⟨εiso, hεisopos, hiso⟩ := zero_isolated hper hfin hgz
  -- right-hand side: `g > 0` on a right-neighbourhood of `sInf A`
  have hright : ∀ x, sInf A < x → x < sInf A + min εiso (b + 1 - sInf A) → 0 < g x := by
    intro x hx1 hx2
    have hε : (0:ℝ) < min εiso (b + 1 - sInf A) := lt_min hεisopos (by linarith)
    have hnozero : ∀ y ∈ Ioo (sInf A) (sInf A + min εiso (b + 1 - sInf A)), g y ≠ 0 := by
      intro y hy hy0
      have hys : |y - sInf A| < εiso := by
        rw [abs_of_pos (by linarith [hy.1])]
        have h2 := min_le_left εiso (b + 1 - sInf A); linarith [hy.2]
      have h3 := hiso y hy0 hys
      linarith [h3, hy.1]
    rcases sign_const_of_no_zero hg (by linarith) hnozero with hpos | hneg
    · exact hpos x ⟨hx1, hx2⟩
    · exfalso
      obtain ⟨t, htA, hzt, htlt⟩ := hpoint (min εiso (b + 1 - sInf A)) hε
      exact absurd (hneg t ⟨lt_of_le_of_ne hzt (by rintro rfl; exact hznotA htA), htlt⟩)
        (not_lt.mpr (le_of_lt htA.2.2))
  -- left-hand side: `g < 0` on a left-neighbourhood of `sInf A`
  have hleft : ∀ x, sInf A - min εiso (sInf A - a) < x → x < sInf A → g x < 0 := by
    intro x hx1 hx2
    have hnozero : ∀ y ∈ Ioo (sInf A - min εiso (sInf A - a)) (sInf A), g y ≠ 0 := by
      intro y hy hy0
      have hys : |y - sInf A| < εiso := by
        rw [abs_of_neg (by linarith [hy.2])]
        have h2 := min_le_left εiso (sInf A - a); linarith [hy.1]
      have h3 := hiso y hy0 hys
      linarith [h3, hy.2]
    have hle : ∀ y ∈ Ioo (sInf A - min εiso (sInf A - a)) (sInf A), g y ≤ 0 := by
      intro y hy
      by_contra hcon
      push Not at hcon
      have hyt : y ∈ A :=
        ⟨by linarith [hy.1, min_le_right εiso (sInf A - a)], le_trans (le_of_lt hy.2) hzb, hcon⟩
      have h5 := csInf_le hAbdd hyt
      linarith [h5, hy.2]
    rcases sign_const_of_no_zero hg (by linarith) hnozero with hpos | hneg2
    · exact absurd (hpos x ⟨hx1, hx2⟩) (not_lt.mpr (hle x ⟨hx1, hx2⟩))
    · exact hneg2 x ⟨hx1, hx2⟩
  set ε : ℝ := min εiso (min 1 (sInf A - a)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hεisopos (lt_min zero_lt_one (by linarith))
  have hε1 : ε ≤ min εiso (b + 1 - sInf A) := by
    rw [hεdef]
    exact le_min (min_le_left _ _)
      (le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith))
  have hε2 : ε ≤ min εiso (sInf A - a) := by
    rw [hεdef]
    exact le_min (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  exact ⟨sInf A, hzgt, hzb, ε, hεpos,
    fun x hx1 hx2 => hleft x (by linarith [hε2]) hx2,
    fun x hx1 hx2 => hright x hx1 (by linarith [hε1])⟩

/-! ## The walk -/

/-- The sign `(-1)^n`. -/
def sgn (n : ℕ) : ℝ := (-1 : ℝ)^n

/-- `g` or `-g` according to the parity of `n`. -/
def gs (g : ℝ → ℝ) (n : ℕ) : ℝ → ℝ := fun t => sgn n * g t

/-- The walk: from a crossing of type `Up` for `g`, run to the end of the current monochromatic
arc, alternating between `g` and `-g`. -/
def signWalk (g : ℝ → ℝ) (s0 : ℝ) : ℕ → ℝ
  | 0 => s0
  | (n + 1) => nxtUp (gs g n) (signWalk g s0 n)

lemma signWalk_zero_apply (g : ℝ → ℝ) (s0 : ℝ) : signWalk g s0 0 = s0 := rfl

lemma signWalk_succ_apply (g : ℝ → ℝ) (s0 : ℝ) (n : ℕ) :
    signWalk g s0 (n + 1) = nxtUp (gs g n) (signWalk g s0 n) := rfl

lemma sgn_ne_zero (n : ℕ) : sgn n ≠ 0 := by
  unfold sgn; exact pow_ne_zero n (by norm_num)

lemma sgn_even {n : ℕ} (h : Even n) : sgn n = 1 := by unfold sgn; exact h.neg_one_pow

lemma sgn_odd {n : ℕ} (h : Odd n) : sgn n = -1 := by unfold sgn; exact h.neg_one_pow

lemma gs_zero_iff (g : ℝ → ℝ) (n : ℕ) (t : ℝ) : gs g n t = 0 ↔ g t = 0 := by
  unfold gs; rw [mul_eq_zero]; simp [sgn_ne_zero n]

lemma gs_continuous (g : ℝ → ℝ) (hg : Continuous g) (n : ℕ) : Continuous (gs g n) :=
  continuous_const.mul hg

lemma gs_periodic (g : ℝ → ℝ) (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t) (n : ℕ) :
    ∀ t : ℝ, gs g n (t + 2 * Real.pi) = gs g n t := by
  intro t; unfold gs; rw [hper t]

lemma gs_neg_val (g : ℝ → ℝ) (hpos : ∃ t : ℝ, 0 < g t) (hneg : ∃ t : ℝ, g t < 0) (n : ℕ) :
    ∃ q, gs g n q < 0 := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨q, hq⟩ := hneg
    exact ⟨q, by unfold gs; rw [sgn_even hn, one_mul]; exact hq⟩
  · obtain ⟨q, hq⟩ := hpos
    exact ⟨q, by unfold gs; rw [sgn_odd hn, neg_one_mul]; exact neg_lt_zero.mpr hq⟩

lemma gs_fin (g : ℝ → ℝ) (n : ℕ)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) :
    {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ gs g n t = 0}.Finite :=
  hfin.subset (fun t ht => ⟨ht.1, (gs_zero_iff g n t).mp ht.2⟩)

lemma gs_succ (g : ℝ → ℝ) (n : ℕ) : gs g (n + 1) = fun t => -(gs g n t) := by
  funext t; unfold gs sgn; rw [pow_succ]; ring

lemma gs_zero (g : ℝ → ℝ) : gs g 0 = g := by
  funext t; unfold gs sgn; simp

lemma Cross_gs (g : ℝ → ℝ) (n : ℕ) (w : ℝ) : Cross (gs g n) w ↔ Cross g w := by
  rcases Nat.even_or_odd n with hn | hn
  · have hg : gs g n = g := by funext t; unfold gs; rw [sgn_even hn, one_mul]
    rw [hg]
  · have hg : gs g n = fun t => -g t := by funext t; unfold gs; rw [sgn_odd hn, neg_one_mul]
    rw [hg, Cross_neg]

lemma signWalk_up {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) (hg : Continuous g)
    (hpos : ∃ t : ℝ, 0 < g t) (hneg : ∃ t : ℝ, g t < 0) {s0 : ℝ} (hs0 : Up g s0) :
    ∀ n, Up (gs g n) (signWalk g s0 n) := by
  intro n
  induction n with
  | zero => rw [gs_zero, signWalk_zero_apply]; exact hs0
  | succ n ih =>
    have hdn : Down (gs g n) (signWalk g s0 (n + 1)) := by
      rw [signWalk_succ_apply]
      exact down_nxtUp (gs_periodic g hper n) (gs_fin g n hfin) (gs_continuous g hg n)
        (gs_neg_val g hpos hneg n) ih
    rw [gs_succ g n]
    exact Up_neg.mpr hdn

lemma signWalk_lt {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) (hg : Continuous g)
    (hpos : ∃ t : ℝ, 0 < g t) (hneg : ∃ t : ℝ, g t < 0) {s0 : ℝ} (hs0 : Up g s0) (n : ℕ) :
    signWalk g s0 n < signWalk g s0 (n + 1) := by
  have hup := signWalk_up hper hfin hg hpos hneg hs0 n
  have hlt := lt_nxtUp (gs_periodic g hper n) (gs_neg_val g hpos hneg n) hup
  rw [signWalk_succ_apply]; exact hlt

lemma signWalk_mono {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) (hg : Continuous g)
    (hpos : ∃ t : ℝ, 0 < g t) (hneg : ∃ t : ℝ, g t < 0) {s0 : ℝ} (hs0 : Up g s0) :
    StrictMono (signWalk g s0) := by
  exact strictMono_nat_of_lt_succ (fun n => signWalk_lt hper hfin hg hpos hneg hs0 n)

lemma signWalk_zero {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) (hg : Continuous g)
    (hpos : ∃ t : ℝ, 0 < g t) (hneg : ∃ t : ℝ, g t < 0) {s0 : ℝ} (hs0 : Up g s0) (n : ℕ) :
    g (signWalk g s0 n) = 0 := by
  have hup := signWalk_up hper hfin hg hpos hneg hs0 n
  have hz := Up_zero (gs_continuous g hg n) hup
  exact (gs_zero_iff g n _).mp hz

/-- The walk closes up after a whole period, with an even number of steps. -/
lemma signWalk_closes {g : ℝ → ℝ} (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) (hg : Continuous g)
    (hpos : ∃ t : ℝ, 0 < g t) (hneg : ∃ t : ℝ, g t < 0) {s0 : ℝ} (hs0 : Up g s0)
    (hs0I : s0 ∈ Ico 0 (2 * Real.pi)) :
    ∃ N : ℕ, signWalk g s0 N = s0 + 2 * Real.pi ∧ Even N := by
  have hmono := signWalk_mono hper hfin hg hpos hneg hs0
  have hZ4 : {t : ℝ | t ∈ Icc 0 (4 * Real.pi) ∧ g t = 0}.Finite :=
    (zeros_sym_finite hper hfin).subset
      (fun t ht => ⟨⟨by linarith [ht.1.1, Real.pi_pos], ht.1.2⟩, ht.2⟩)
  have hex : ∃ n, s0 + 2 * Real.pi ≤ signWalk g s0 n := by
    by_contra hcon
    push Not at hcon
    have hsub : Set.range (signWalk g s0) ⊆ {t : ℝ | t ∈ Icc 0 (4 * Real.pi) ∧ g t = 0} := by
      rintro t ⟨n, rfl⟩
      refine ⟨⟨?_, ?_⟩, signWalk_zero hper hfin hg hpos hneg hs0 n⟩
      · have h0 : signWalk g s0 0 = s0 := signWalk_zero_apply g s0
        have hm := hmono.monotone (Nat.zero_le n)
        linarith [hs0I.1, hm, h0]
      · linarith [hcon n, hs0I.2]
    have hfinrange : (Set.range (signWalk g s0)).Finite := hZ4.subset hsub
    exact (Set.infinite_range_of_injective hmono.injective).not_finite hfinrange
  set N := Nat.find hex with hN
  have hNspec : s0 + 2 * Real.pi ≤ signWalk g s0 N := Nat.find_spec hex
  have hNmin : ∀ m, m < N → signWalk g s0 m < s0 + 2 * Real.pi :=
    fun m hm => not_le.mp (Nat.find_min hex hm)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h, signWalk_zero_apply] at hNspec
      linarith [Real.pi_pos]
    · exact h
  have hNle : signWalk g s0 N ≤ s0 + 2 * Real.pi := by
    by_contra hcon
    push Not at hcon
    have hprev : signWalk g s0 (N - 1) < s0 + 2 * Real.pi := hNmin (N - 1) (by omega)
    have hstep : signWalk g s0 N = nxtUp (gs g (N - 1)) (signWalk g s0 (N - 1)) := by
      conv_lhs => rw [show N = (N - 1) + 1 by omega]
      exact signWalk_succ_apply g s0 (N - 1)
    have hnc := no_cross_nxtUp (gs_periodic g hper (N - 1)) (gs_neg_val g hpos hneg (N - 1))
      (gs_continuous g hg (N - 1))
      (signWalk_up hper hfin hg hpos hneg hs0 (N - 1))
    have hcross : Cross g (s0 + 2 * Real.pi) := Or.inl ((Up_add_period hper s0).mpr hs0)
    exact (hnc (s0 + 2 * Real.pi) hprev (by rw [← hstep]; exact hcon))
      ((Cross_gs g (N - 1) (s0 + 2 * Real.pi)).mpr hcross)
  have hNval : signWalk g s0 N = s0 + 2 * Real.pi := le_antisymm hNle hNspec
  refine ⟨N, hNval, ?_⟩
  rcases Nat.even_or_odd N with hEven | hOdd
  · exact hEven
  · exfalso
    have hupN := signWalk_up hper hfin hg hpos hneg hs0 N
    have hgN : gs g N = fun t => -g t := by funext t; unfold gs; rw [sgn_odd hOdd, neg_one_mul]
    rw [hgN] at hupN
    have hdown : Down g (signWalk g s0 N) := Up_neg.mp hupN
    have hup : Up g (signWalk g s0 N) := by rw [hNval]; exact (Up_add_period hper s0).mpr hs0
    exact Up_not_down hup hdown

/-! ## The main result -/

/-- A continuous `2π`-periodic real function whose zero set in `[0, 2π]` is finite is either
nonnegative everywhere, nonpositive everywhere, or its circle is split into finitely many
alternating monochromatic arcs starting with a nonnegative one. -/
theorem signPartition_of_finite_zeros
    (g : ℝ → ℝ) (hg : Continuous g) (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (hfin : {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite) :
    (∀ t : ℝ, 0 ≤ g t) ∨ (∀ t : ℝ, g t ≤ 0) ∨
      ∃ (k : ℕ) (_ : 0 < k) (s : ℕ → ℝ),
        s 0 ∈ Set.Ico 0 (2 * Real.pi) ∧ s (2 * k) = s 0 + 2 * Real.pi ∧
        (∀ i j, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j) ∧
        (∀ i, i ≤ 2 * k → g (s i) = 0) ∧
        (∀ j, j < k → ∀ t : ℝ, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → 0 ≤ g t) ∧
        (∀ j, j < k → ∀ t : ℝ, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → g t ≤ 0) := by
  classical
  by_cases h1 : ∀ t : ℝ, 0 ≤ g t
  · exact Or.inl h1
  · by_cases h2 : ∀ t : ℝ, g t ≤ 0
    · exact Or.inr (Or.inl h2)
    · right; right
      have hnegp : ∃ t : ℝ, g t < 0 := by
        by_contra hc; push Not at hc; exact h1 hc
      have hposp : ∃ t : ℝ, 0 < g t := by
        by_contra hc; push Not at hc; exact h2 hc
      obtain ⟨r₀, hr₀⟩ := hnegp
      obtain ⟨p, hp⟩ := hposp
      have hneg : ∃ t : ℝ, g t < 0 := ⟨r₀, hr₀⟩
      have hpos : ∃ t : ℝ, 0 < g t := ⟨p, hp⟩
      have hpi : (0:ℝ) < 2 * Real.pi := by positivity
      obtain ⟨n, hn⟩ := exists_nat_gt ((r₀ - p) / (2 * Real.pi))
      rw [div_lt_iff₀ hpi] at hn
      have hrn : g (r₀ - (n:ℝ) * (2 * Real.pi)) = g r₀ := by
        have hp' : Function.Periodic g (2 * Real.pi) := hper
        have hh := hp'.nat_mul n (r₀ - (n:ℝ) * (2*Real.pi))
        rw [show r₀ - (n:ℝ)*(2*Real.pi) + (n:ℝ)*(2*Real.pi) = r₀ by ring] at hh
        exact hh.symm
      have hrp : r₀ - (n:ℝ) * (2 * Real.pi) < p := by linarith
      obtain ⟨z, _hzgt, _hzb, hzUp⟩ := exists_Up hg hper hfin hrp hp (by rw [hrn]; exact hr₀)
      -- reduce `z` into `[0, 2π)`
      set s0 : ℝ := z - ((⌊z / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) with hs0def
      have hs0Up : Up g s0 := by
        have h := (Up_int_period hper z (-⌊z / (2 * Real.pi)⌋)).mpr hzUp
        rw [hs0def]
        convert h using 2
        push_cast; ring
      have hs0I : s0 ∈ Ico 0 (2 * Real.pi) := by
        have h1' := Int.floor_le (z / (2 * Real.pi))
        have h2' := Int.lt_floor_add_one (z / (2 * Real.pi))
        constructor
        · rw [hs0def]
          have h := mul_le_mul_of_nonneg_right h1' (le_of_lt hpi)
          rw [div_mul_cancel₀ z (ne_of_gt hpi)] at h
          linarith
        · rw [hs0def]
          have h := mul_lt_mul_of_pos_right h2' hpi
          rw [div_mul_cancel₀ z (ne_of_gt hpi)] at h
          linarith
      obtain ⟨N, hNval, hNeven⟩ := signWalk_closes hper hfin hg hpos hneg hs0Up hs0I
      obtain ⟨k, hk⟩ := hNeven
      have hk2 : 2 * k = N := by omega
      have hNpos : 1 ≤ N := by
        rcases Nat.eq_zero_or_pos N with h | h
        · exfalso
          rw [h, signWalk_zero_apply] at hNval
          linarith [Real.pi_pos]
        · exact h
      have hkpos : 0 < k := by omega
      refine ⟨k, hkpos, signWalk g s0, hs0I, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk2]
        rw [show signWalk g s0 0 = s0 from signWalk_zero_apply g s0]
        exact hNval
      · intro i j _ _ hij
        exact signWalk_mono hper hfin hg hpos hneg hs0Up hij
      · intro i _
        exact signWalk_zero hper hfin hg hpos hneg hs0Up i
      · intro j _ t ht1 ht2
        have hup := signWalk_up hper hfin hg hpos hneg hs0Up (2 * j)
        have hnonneg := nonneg_nxtUp (gs_periodic g hper (2*j)) (gs_neg_val g hpos hneg (2*j))
          (gs_continuous g hg (2*j)) hup
        have hmem : t ∈ Icc (signWalk g s0 (2*j)) (nxtUp (gs g (2*j)) (signWalk g s0 (2*j))) :=
          ⟨ht1, by rw [← signWalk_succ_apply]; exact ht2⟩
        have h3 := hnonneg t hmem
        unfold gs at h3
        rw [sgn_even (even_two_mul j), one_mul] at h3
        exact h3
      · intro j _ t ht1 ht2
        have hup := signWalk_up hper hfin hg hpos hneg hs0Up (2 * j + 1)
        have hnonneg := nonneg_nxtUp (gs_periodic g hper (2*j+1)) (gs_neg_val g hpos hneg (2*j+1))
          (gs_continuous g hg (2*j+1)) hup
        have hstep : signWalk g s0 (2*j+2)
            = nxtUp (gs g (2*j+1)) (signWalk g s0 (2*j+1)) := by
          rw [show 2*j+2 = (2*j+1)+1 by omega, signWalk_succ_apply]
        have hmem : t ∈ Icc (signWalk g s0 (2*j+1))
            (nxtUp (gs g (2*j+1)) (signWalk g s0 (2*j+1))) := ⟨ht1, by rw [← hstep]; exact ht2⟩
        have h3 := hnonneg t hmem
        unfold gs at h3
        rw [sgn_odd (odd_two_mul_add_one j), neg_one_mul] at h3
        linarith

end

end Work.BoxShrink.PinchOff
