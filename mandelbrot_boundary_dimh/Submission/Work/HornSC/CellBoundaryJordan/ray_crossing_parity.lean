import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.RayDefs

/-!
# Parity of the number of crossings of an interval by a predicate

If `P : ℝ → Prop` is locally constant on the closed interval `[a,b]` except on a finite set `S`,
and `P` flips across every element of `S`, then the truth value of `P` at the two endpoints differs
exactly when `S` has odd cardinality.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

lemma iff_of_decide_eq {p q : Prop} [Decidable p] [Decidable q] (h : decide p = decide q) :
    (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-- A proposition-valued function that is locally constant on `Icc a b` is constant there. -/
lemma eq_of_locally_constant_Icc {a b : ℝ} (hab : a ≤ b) {P : ℝ → Prop}
    (hloc : ∀ t ∈ Set.Icc a b, ∃ δ > 0, ∀ s, |s - t| < δ → (P s ↔ P t)) :
    ∀ s ∈ Set.Icc a b, P s ↔ P a := by
  classical
  intro s hs
  let f : ↥(Set.Icc a b) → Bool := fun x => decide (P x.1)
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨δ, hδpos, hδ⟩ := hloc x.1 x.2
    refine ⟨Subtype.val ⁻¹' Metric.ball x.1 δ,
      Metric.isOpen_ball.preimage continuous_subtype_val, ?_, ?_⟩
    · simp [Metric.mem_ball, hδpos]
    · intro x' hx'
      have h : P x'.1 ↔ P x.1 := hδ x'.1 (by simpa [Metric.mem_ball, Real.dist_eq, Subtype.dist_eq] using hx')
      simp only [f]
      rw [h]
  have hcont : Continuous f := hf.continuous
  have hpre : PreconnectedSpace ↥(Set.Icc a b) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have haX : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
  have hfx : f ⟨a, haX⟩ = f ⟨s, hs⟩ := PreconnectedSpace.constant hpre hcont
  have h' : P a ↔ P s := iff_of_decide_eq (show decide (P a) = decide (P s) from hfx)
  exact h'.symm

/-- Parity of the number of crossings of `[a,b]` by a predicate `P` that is locally constant off
the finite set `S` and flips across each point of `S`. -/
theorem even_card_iff_parity {S : Finset ℝ} {a b : ℝ} (hab : a < b) {P : ℝ → Prop}
    (hS : ∀ t ∈ S, a < t ∧ t < b)
    (hloc : ∀ t ∈ Set.Icc a b, t ∉ S → ∃ δ > 0, ∀ s, |s - t| < δ → (P s ↔ P t))
    (hflip : ∀ t ∈ S, ∃ δ > 0, ∀ s, 0 < s → s < δ → (P (t + s) ↔ ¬ P (t - s))) :
    ((P a ↔ P b) ↔ Even S.card) := by
  classical
  have H : ∀ n, ∀ (T : Finset ℝ), ∀ (a b : ℝ), ∀ (P : ℝ → Prop), T.card = n → a < b →
      (∀ t ∈ T, a < t ∧ t < b) →
      (∀ t ∈ Set.Icc a b, t ∉ T → ∃ δ > 0, ∀ s, |s - t| < δ → (P s ↔ P t)) →
      (∀ t ∈ T, ∃ δ > 0, ∀ s, 0 < s → s < δ → (P (t + s) ↔ ¬ P (t - s))) →
      ((P a ↔ P b) ↔ Even T.card) := by
    intro n
    induction n with
    | zero =>
      intro T a b P hcard hab hT hloc hflip
      have hTe : T = ∅ := Finset.card_eq_zero.mp hcard
      have hconst : ∀ s ∈ Set.Icc a b, P s ↔ P a :=
        eq_of_locally_constant_Icc (a := a) (b := b) (le_of_lt hab) (P := P)
          (fun t ht => hloc t ht (by rw [hTe]; exact Finset.notMem_empty t))
      have hb : P b ↔ P a := hconst b (right_mem_Icc.mpr (le_of_lt hab))
      rw [hcard]
      exact ⟨fun _ => Even.zero, fun _ => hb.symm⟩
    | succ k ih =>
      intro T a b P hcard hab hT hloc hflip
      rcases T.eq_empty_or_nonempty with rfl | hne
      · simp at hcard
      · set m := T.min' hne with hm
        have hmT : m ∈ T := by rw [hm]; exact Finset.min'_mem T hne
        have hle : ∀ t ∈ T, m ≤ t := by
          intro t ht; rw [hm]; exact T.min'_le t ht
        have ham : a < m := (hT m hmT).1
        have hmb : m < b := (hT m hmT).2
        obtain ⟨δ, hδpos, hδflip⟩ := hflip m hmT
        have hcard' : (T.erase m).card = k := by
          rw [Finset.card_erase_of_mem hmT, hcard]; omega
        set g : ℝ := if h : (T.erase m).Nonempty then (T.erase m).min' h else b with hg
        have hmg : m < g := by
          rw [hg]; split_ifs with h
          · have hmem := (Finset.mem_erase.mp ((T.erase m).min'_mem h))
            have h1 : m ≤ (T.erase m).min' h := hle _ hmem.2
            exact lt_of_le_of_ne h1 hmem.1.symm
          · exact hmb
        have hgb : g ≤ b := by
          rw [hg]; split_ifs with h
          · have hmem := (Finset.mem_erase.mp ((T.erase m).min'_mem h))
            exact le_of_lt (hT _ hmem.2).2
          · exact le_refl b
        have hgt : ∀ t ∈ T.erase m, g ≤ t := by
          intro t ht
          rw [hg]; split_ifs with h
          · exact (T.erase m).min'_le t ht
          · exact absurd ⟨t, ht⟩ h
        set s₀ : ℝ := min (min (g - m) δ) (m - a) / 2 with hs₀
        have hs₀pos : 0 < s₀ := by
          rw [hs₀]
          have h1 : 0 < min (min (g - m) δ) (m - a) :=
            lt_min (lt_min (by linarith) hδpos) (by linarith)
          linarith
        have hs₀δ : s₀ < δ := by
          rw [hs₀]
          have h1 : min (min (g - m) δ) (m - a) ≤ δ :=
            le_trans (min_le_left _ _) (min_le_right _ _)
          linarith
        have hs₀gm : s₀ < g - m := by
          rw [hs₀]
          have h1 : min (min (g - m) δ) (m - a) ≤ g - m :=
            le_trans (min_le_left _ _) (min_le_left _ _)
          linarith
        have hs₀ma : s₀ ≤ (m - a) / 2 := by
          rw [hs₀]
          have h1 : min (min (g - m) δ) (m - a) ≤ m - a := min_le_right _ _
          linarith
        set c : ℝ := m + s₀ with hc
        have hcm : m < c := by rw [hc]; linarith
        have hcb : c < b := by
          have h1 : c < g := by rw [hc]; linarith
          linarith
        have hab1 : a ≤ m - s₀ := by linarith [hs₀ma, ham]
        have hms0 : P (m - s₀) ↔ P a := by
          exact eq_of_locally_constant_Icc (a := a) (b := m - s₀) hab1 (P := P) (fun t ht => by
            have ht2 : t ∈ Set.Icc a b := ⟨ht.1, by linarith [ht.2, hs₀pos, hmb]⟩
            have htT : t ∉ T := by
              intro htT
              have h2 := hle t htT
              linarith [ht.2, h2, hs₀pos]
            exact hloc t ht2 htT) (m - s₀) ⟨hab1, le_refl _⟩
        have hca : P c ↔ ¬ P a := by
          rw [hc]
          exact (hδflip s₀ hs₀pos hs₀δ).trans (not_congr hms0)
        have hS' : ∀ t ∈ T.erase m, c < t ∧ t < b := by
          intro t ht
          have htT : t ∈ T := Finset.mem_of_mem_erase ht
          exact ⟨by have h1 := hgt t ht; rw [hc]; linarith, (hT t htT).2⟩
        have hloc' : ∀ t ∈ Set.Icc c b, t ∉ T.erase m →
            ∃ δ > 0, ∀ s, |s - t| < δ → (P s ↔ P t) := by
          intro t ht htT'
          rw [hc] at ht
          have hmt : m < t := by linarith [ht.1, hs₀pos]
          have htT : t ∉ T := by
            intro htT
            exact htT' (Finset.mem_erase.mpr ⟨ne_of_gt hmt, htT⟩)
          exact hloc t ⟨by linarith [ht.1, ham, hs₀pos], ht.2⟩ htT
        have hflip' : ∀ t ∈ T.erase m, ∃ δ > 0, ∀ s, 0 < s → s < δ →
            (P (t + s) ↔ ¬ P (t - s)) :=
          fun t ht => hflip t (Finset.mem_of_mem_erase ht)
        have hres := ih (T.erase m) c b P hcard' hcb hS' hloc' hflip'
        have hres' : (P c ↔ P b) ↔ Even k := by rw [hcard'] at hres; exact hres
        rw [hcard, Nat.even_add_one, ← hres', hca]
        tauto
  exact H S.card S a b P rfl hab hS hloc hflip

/-- The number of crossings of `[a,b]` is odd when `P` is true at the left end and false at the
right end. -/
lemma odd_card_of_flip {S : Finset ℝ} {a b : ℝ} (hab : a < b) {P : ℝ → Prop}
    (hS : ∀ t ∈ S, a < t ∧ t < b)
    (hloc : ∀ t ∈ Set.Icc a b, t ∉ S → ∃ δ > 0, ∀ s, |s - t| < δ → (P s ↔ P t))
    (hflip : ∀ t ∈ S, ∃ δ > 0, ∀ s, 0 < s → s < δ → (P (t + s) ↔ ¬ P (t - s)))
    (ha : P a) (hb : ¬ P b) : Odd S.card := by
  have h := even_card_iff_parity (S := S) hab hS hloc hflip
  have h1 : ¬ (P a ↔ P b) := fun hiff => hb (hiff.mp ha)
  have h2 : ¬ Even S.card := fun he => h1 (h.mpr he)
  exact Nat.not_even_iff_odd.mp h2

end Work.HornSC.CellBoundaryJordan
