import Submission.Work.Deep.Nibble.r2_setup

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of kept blockers chosen by `witF` with a prescribed value is at most `r`. -/
lemma witF_fiber_card_le (𝓖 : Set (Set V)) {r : ℕ} (hr : 1 ≤ r) (hlin : HLin 𝓖)
    (huni : HUnif 𝓖 r)
    (ω : 𝓖 → Bool) (v : V) (f : 𝓖) :
    ((thruF 𝓖 v).filter (fun e => witF 𝓖 ω v e = f)).card ≤ r := by
  classical
  set S := (thruF 𝓖 v).filter (fun e => witF 𝓖 ω v e = f) with hS
  by_cases hvf : v ∈ (f : Set V)
  · have hsub : S ⊆ {f} := by
      intro e he
      rw [Finset.mem_singleton]
      by_contra hef
      by_cases h : ∃ g ∈ Bset 𝓖 v e, ω g = true
      · have hmem : f ∈ Bset 𝓖 v e := by
          rw [← (Finset.mem_filter.mp he).2]
          exact witF_mem 𝓖 h
        exact ((mem_Bset (𝓖 := 𝓖)).mp hmem).2 hvf
      · have hwit : witF 𝓖 ω v e = e := by rw [witF, dif_neg h]
        exact hef (by rw [← hwit]; exact (Finset.mem_filter.mp he).2)
    calc S.card ≤ ({f} : Finset 𝓖).card := Finset.card_le_card hsub
      _ ≤ r := by
          rw [Finset.card_singleton]
          exact hr
  · have hnon : ∀ e ∈ S, ∃ g ∈ Bset 𝓖 v e, ω g = true := by
      intro e he
      by_contra h
      have hwit : witF 𝓖 ω v e = e := by rw [witF, dif_neg h]
      have hef : e = f := by rw [← hwit]; exact (Finset.mem_filter.mp he).2
      have hT : e ∈ thruF 𝓖 v := (Finset.mem_filter.mp he).1
      exact hvf (hef ▸ (mem_thruF (𝓖 := 𝓖)).mp hT)
    have hne : ∀ e ∈ S, ((f : Set V) ∩ (e : Set V)).Nonempty := by
      intro e he
      have hmem : f ∈ Bset 𝓖 v e := by
        rw [← (Finset.mem_filter.mp he).2]
        exact witF_mem 𝓖 (hnon e he)
      exact ((mem_Bset (𝓖 := 𝓖)).mp hmem).1
    haveI : Nonempty V := ⟨v⟩
    let pt : 𝓖 → V := fun e =>
      if h : ((f : Set V) ∩ (e : Set V)).Nonempty then Classical.choose h else Classical.arbitrary V
    have hpt_mem : ∀ e ∈ S, pt e ∈ (f : Set V) := by
      intro e he
      have hspec := Classical.choose_spec (hne e he)
      simp only [pt, dif_pos (hne e he)]
      exact hspec.1
    have hpt_ne : ∀ e ∈ S, pt e ≠ v := by
      intro e he
      have hspec := Classical.choose_spec (hne e he)
      simp only [pt, dif_pos (hne e he)]
      exact fun h => hvf (h ▸ hspec.1)
    have hpt_mem' : ∀ e ∈ S, pt e ∈ (e : Set V) := by
      intro e he
      have hspec := Classical.choose_spec (hne e he)
      simp only [pt, dif_pos (hne e he)]
      exact hspec.2
    have hinj : Set.InjOn pt (↑S : Set 𝓖) := by
      intro e he e' he' heq
      by_contra hne'
      have hx : pt e ∈ (e : Set V) ∩ (e' : Set V) :=
        ⟨hpt_mem' e he, by rw [heq]; exact hpt_mem' e' he'⟩
      have hv : v ∈ (e : Set V) ∩ (e' : Set V) :=
        ⟨(mem_thruF (𝓖 := 𝓖)).mp (Finset.mem_filter.mp he).1,
          (mem_thruF (𝓖 := 𝓖)).mp (Finset.mem_filter.mp he').1⟩
      have hsub := hlin e.2 e'.2 (fun h => hne' (Subtype.ext h))
      exact hpt_ne e he (hsub hx hv)
    have hmaps : Set.MapsTo pt (↑S : Set 𝓖) (↑(eFin 𝓖 f) : Set V) := by
      intro e he
      rw [eFin]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpt_mem e he⟩
    calc S.card ≤ (eFin 𝓖 f).card := Finset.card_le_card_of_injOn pt hmaps hinj
      _ = Nat.card {x : V // x ∈ (f : Set V)} := by
          rw [eFin]
          exact (natCard_subtype_eq_filter_card (fun x : V => x ∈ (f : Set V))).symm
      _ = (f : Set V).ncard := Nat.card_coe_set_eq _
      _ = r := huni f f.2

/-- **The `(s,c)`-certificate for the residual degree at `v`**: `Wv` cannot increase much when
only a few coordinates of the certificate set `certSet 𝓖 ω v` are changed. -/
lemma Wv_certificate (𝓖 : Set (Set V)) {r : ℕ} (hr : 1 ≤ r) (hlin : HLin 𝓖) (huni : HUnif 𝓖 r)
    (ω : 𝓖 → Bool) (v : V) (u : ℝ) (hu : 0 < u) :
    ∃ I : Finset 𝓖, I.card ≤ (thruF 𝓖 v).card ∧
      ∀ ω' : 𝓖 → Bool, ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (r : ℝ) →
        ((Wv 𝓖 ω' v : ℕ) : ℝ) < ((Wv 𝓖 ω v : ℕ) : ℝ) + u := by
  classical
  refine ⟨certSet 𝓖 ω v, certSet_card_le 𝓖 ω v, fun ω' hD => ?_⟩
  have hA : Wv 𝓖 ω' v = ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false)).card := rfl
  have hB : Wv 𝓖 ω v = ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)).card := rfl
  have hmap : ∀ e ∈ (thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
      ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)),
      witF 𝓖 ω v e ∈ (certSet 𝓖 ω v).filter (fun i => ω i ≠ ω' i) := by
    intro e he
    obtain ⟨heA, heB⟩ := Finset.mem_sdiff.mp he
    have hT : e ∈ thruF 𝓖 v := (Finset.mem_filter.mp heA).1
    have hex : ∃ g ∈ Bset 𝓖 v e, ω g = true := by
      by_contra h
      refine heB (Finset.mem_filter.mpr ⟨hT, fun g hg => ?_⟩)
      by_contra hgc
      exact h ⟨g, hg, by simpa using hgc⟩
    refine Finset.mem_filter.mpr ⟨witF_mem_certSet 𝓖 hT, ?_⟩
    have h1 : ω (witF 𝓖 ω v e) = true := witF_kept 𝓖 hex
    have h2 : ω' (witF 𝓖 ω v e) = false := (Finset.mem_filter.mp heA).2 _ (witF_mem 𝓖 hex)
    rw [h1, h2]
    simp
  have hfib : ∀ f ∈ ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
        ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).image (witF 𝓖 ω v),
      ((((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
        ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).filter
          (fun e => witF 𝓖 ω v e = f)).card) ≤ r := by
    intro f hf
    calc _ ≤ ((thruF 𝓖 v).filter (fun e => witF 𝓖 ω v e = f)).card := by
          refine Finset.card_le_card ?_
          intro e he
          rw [Finset.mem_filter] at he ⊢
          exact ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp he.1).1).1, he.2⟩
      _ ≤ r := witF_fiber_card_le 𝓖 hr hlin huni ω v f
  have hmaps : Set.MapsTo (witF 𝓖 ω v)
      ↑((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
        ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)))
      ↑(((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
        ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).image (witF 𝓖 ω v)) :=
    fun e he => Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hcard : (((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
        ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).card)
      ≤ ((certSet 𝓖 ω v).filter (fun i => ω i ≠ ω' i)).card * r := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc (∑ b ∈ ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
            ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).image (witF 𝓖 ω v),
          (((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
            ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).filter
              (fun e => witF 𝓖 ω v e = b)).card)
        ≤ ∑ _b ∈ ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
            ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).image (witF 𝓖 ω v), r :=
          Finset.sum_le_sum (fun b hb => hfib b hb)
      _ = (((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
            ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).image
              (witF 𝓖 ω v)).card * r := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ((certSet 𝓖 ω v).filter (fun i => ω i ≠ ω' i)).card * r := by
          apply Nat.mul_le_mul_right
          refine Finset.card_le_card ?_
          intro f hf
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
          exact hmap e he
  have hAB : ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false)).card
      ≤ ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)).card
        + (((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
            ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).card) := by
    have hsub : (thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false)
        ⊆ ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))
          ∪ (((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
              ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)))) := by
      intro e he
      by_cases h : e ∈ (thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)
      · exact Finset.mem_union.mpr (Or.inl h)
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨he, h⟩))
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  rw [hA, hB]
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hDcard : (((certSet 𝓖 ω v).filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (r : ℝ) := hD
  have hmul : ((((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
        ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).card : ℕ) : ℝ)
      ≤ (((certSet 𝓖 ω v).filter (fun i => ω i ≠ ω' i)).card : ℝ) * (r : ℝ) := by
    exact_mod_cast hcard
  have hlt : ((((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
        ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).card : ℕ) : ℝ) < u := by
    calc _ ≤ _ := hmul
      _ < (u / (r : ℝ)) * (r : ℝ) := mul_lt_mul_of_pos_right hDcard hrpos
      _ = u := by field_simp
  have h2 : ((((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false)).card : ℕ) : ℝ)
      ≤ ((((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false)).card : ℕ) : ℝ)
        + ((((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω' f = false) \
            ((thruF 𝓖 v).filter (fun e => ∀ f ∈ Bset 𝓖 v e, ω f = false))).card : ℕ) : ℝ) := by
    exact_mod_cast hAB
  linarith

end Work.Deep.Nibble
