import Submission.Work.Deep.Nibble.r2_own_d
import Submission.Work.Deep.Nibble.r2_comb_count

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Bound on the size of the coordinate set `Nset`. -/
lemma Nset_card_le (𝓖 : Set (Set V)) {r : ℕ} (hr : 1 ≤ r) (hlin : HLin 𝓖) (huni : HUnif 𝓖 r)
    {ε D : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hD : 1 ≤ D)
    (hdeg : ∀ w : V, (hd 𝓖 w : ℝ) ≤ (1 + ε) * D) (v : V) :
    ((Nset 𝓖 v).card : ℝ) ≤ 10 * (r : ℝ) * D ^ 2 := by
  classical
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hthru : ((thruF 𝓖 v).card : ℝ) ≤ (1 + ε) * D := by
    rw [← hd_eq_card_thruF 𝓖 v]; exact hdeg v
  have hbi : ∀ e ∈ thruF 𝓖 v, ((Bset 𝓖 v e).card : ℝ) ≤ (r : ℝ) * (2 * D) := by
    intro e he
    have hb := (r2_comb_count 𝓖 hr hlin huni).2.2.1 v e ((mem_thruF (𝓖 := 𝓖)).mp he) ε D hε0 hdeg
    have h1 : ((r : ℝ) - 1) * ((1 + ε) * D) ≤ (r : ℝ) * (2 * D) := by nlinarith
    linarith
  have h2 : ((Nset 𝓖 v).card : ℝ)
      ≤ (((thruF 𝓖 v).biUnion (fun e => Bset 𝓖 v e)).card : ℝ) + ((thruF 𝓖 v).card : ℝ) := by
    rw [Nset]
    exact_mod_cast Finset.card_union_le _ _
  have h3 : ((((thruF 𝓖 v).biUnion (fun e => Bset 𝓖 v e)).card : ℕ) : ℝ)
      ≤ ∑ e ∈ thruF 𝓖 v, (r : ℝ) * (2 * D) := by
    calc _ ≤ ((∑ e ∈ thruF 𝓖 v, (Bset 𝓖 v e).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ e ∈ thruF 𝓖 v, ((Bset 𝓖 v e).card : ℝ) := Nat.cast_sum _ _
      _ ≤ ∑ e ∈ thruF 𝓖 v, (r : ℝ) * (2 * D) := Finset.sum_le_sum hbi
  have h4 : (∑ e ∈ thruF 𝓖 v, (r : ℝ) * (2 * D)) = ((thruF 𝓖 v).card : ℝ) * (r * (2 * D)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h5 : ((Nset 𝓖 v).card : ℝ)
      ≤ ((thruF 𝓖 v).card : ℝ) * (r * (2 * D)) + ((thruF 𝓖 v).card : ℝ) := by linarith
  have hcard2 : ((thruF 𝓖 v).card : ℝ) ≤ 2 * D := by nlinarith [hthru, hε1]
  have h6 : ((thruF 𝓖 v).card : ℝ) * (r * (2 * D)) + ((thruF 𝓖 v).card : ℝ)
      ≤ 10 * (r : ℝ) * D ^ 2 := by
    have h1 : ((thruF 𝓖 v).card : ℝ) * ((r : ℝ) * (2 * D)) ≤ (2 * D) * ((r : ℝ) * (2 * D)) :=
      mul_le_mul_of_nonneg_right hcard2 (by positivity)
    have h1' : (2 * D) * ((r : ℝ) * (2 * D)) = 4 * (r : ℝ) * D ^ 2 := by ring
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h3 : 2 * D ≤ 6 * (r : ℝ) * D ^ 2 := by nlinarith [hr1, hD, sq_nonneg D]
    linarith [h1, h1']
  linarith

/-- For a fixed edge `f`, the number of `w` with `f ∈ Nset w` is at most `3 r² D`. -/
lemma Nset_fiber_card_le (𝓖 : Set (Set V)) {r : ℕ} (hr : 1 ≤ r) (hlin : HLin 𝓖) (huni : HUnif 𝓖 r)
    {ε D : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hD : 1 ≤ D)
    (hdeg : ∀ w : V, (hd 𝓖 w : ℝ) ≤ (1 + ε) * D) (f : 𝓖) :
    ((Finset.univ.filter (fun w : V => f ∈ Nset 𝓖 w)).card : ℝ) ≤ 3 * (r : ℝ) ^ 2 * D := by
  classical
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hD1 : (1 : ℝ) ≤ D := by linarith
  set fset : Finset V := Finset.univ.filter (fun x : V => x ∈ (f : Set V)) with hfset
  set Nbh : Finset V := fset.biUnion
      (fun x => (thruF 𝓖 x).biUnion (fun e => Finset.univ.filter (fun w : V => w ∈ (e : Set V))))
    with hNbh
  have hcount : ∀ x : V,
      (((thruF 𝓖 x).biUnion (fun e => Finset.univ.filter (fun w : V => w ∈ (e : Set V)))).card : ℝ)
        ≤ (r : ℝ) * ((1 + ε) * D) := by
    intro x
    have hstep : ∀ e : 𝓖, ((Finset.univ.filter (fun w : V => w ∈ (e : Set V))).card : ℝ) ≤ (r : ℝ) := by
      intro e
      have : (Finset.univ.filter (fun w : V => w ∈ (e : Set V))).card ≤ r := by
        calc (Finset.univ.filter (fun w : V => w ∈ (e : Set V))).card
            ≤ Nat.card {y : V // y ∈ (e : Set V)} := by rw [natCard_subtype_eq_filter_card]
          _ = (e : Set V).ncard := Nat.card_coe_set_eq _
          _ = r := huni e e.2
      exact_mod_cast this
    calc (((thruF 𝓖 x).biUnion (fun e => Finset.univ.filter (fun w : V => w ∈ (e : Set V)))).card : ℝ)
        ≤ ((∑ e ∈ thruF 𝓖 x,
            (Finset.univ.filter (fun w : V => w ∈ (e : Set V))).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ e ∈ thruF 𝓖 x, ((Finset.univ.filter (fun w : V => w ∈ (e : Set V))).card : ℝ) :=
          Nat.cast_sum _ _
      _ ≤ ∑ _e ∈ thruF 𝓖 x, (r : ℝ) := Finset.sum_le_sum (fun e _ => hstep e)
      _ = ((thruF 𝓖 x).card : ℝ) * (r : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((1 + ε) * D) * (r : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hr0
          rw [← hd_eq_card_thruF 𝓖 x]; exact hdeg x
      _ = (r : ℝ) * ((1 + ε) * D) := by ring
  have hNbh_card : (Nbh.card : ℝ) ≤ (r : ℝ) * ((r : ℝ) * ((1 + ε) * D)) := by
    calc (Nbh.card : ℝ)
        ≤ ((∑ x ∈ fset, ((thruF 𝓖 x).biUnion
            (fun e => Finset.univ.filter (fun w : V => w ∈ (e : Set V)))).card : ℕ) : ℝ) := by
          rw [hNbh]
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ x ∈ fset, (((thruF 𝓖 x).biUnion
            (fun e => Finset.univ.filter (fun w : V => w ∈ (e : Set V)))).card : ℝ) :=
          Nat.cast_sum _ _
      _ ≤ ∑ _x ∈ fset, (r : ℝ) * ((1 + ε) * D) := Finset.sum_le_sum (fun x _ => hcount x)
      _ = (fset.card : ℝ) * ((r : ℝ) * ((1 + ε) * D)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (r : ℝ) * ((r : ℝ) * ((1 + ε) * D)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : fset.card ≤ r := by
            rw [hfset]
            calc (Finset.univ.filter (fun x : V => x ∈ (f : Set V))).card
                ≤ Nat.card {y : V // y ∈ (f : Set V)} := by rw [natCard_subtype_eq_filter_card]
              _ = (f : Set V).ncard := Nat.card_coe_set_eq _
              _ = r := huni f f.2
          exact_mod_cast this
  have hsplit : Finset.univ.filter (fun w : V => f ∈ Nset 𝓖 w) ⊆ fset ∪ Nbh := by
    intro w hw
    rw [Finset.mem_filter] at hw
    have hmem := hw.2
    rw [Nset] at hmem
    rcases Finset.mem_union.mp hmem with h | h
    · obtain ⟨e, he, hfe⟩ := Finset.mem_biUnion.mp h
      have hB := (mem_Bset (𝓖 := 𝓖)).mp hfe
      obtain ⟨x, hx⟩ := hB.1
      refine Finset.mem_union.mpr (Or.inr ?_)
      rw [hNbh, Finset.mem_biUnion]
      refine ⟨x, ?_, ?_⟩
      · rw [hfset, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hx.1⟩
      · rw [Finset.mem_biUnion]
        exact ⟨e, (mem_thruF (𝓖 := 𝓖)).mpr hx.2, by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, (mem_thruF (𝓖 := 𝓖)).mp he⟩⟩
    · refine Finset.mem_union.mpr (Or.inl ?_)
      rw [hfset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (mem_thruF (𝓖 := 𝓖)).mp h⟩
  have hf_card : (fset.card : ℝ) ≤ (r : ℝ) := by
    have : fset.card ≤ r := by
      rw [hfset]
      calc (Finset.univ.filter (fun x : V => x ∈ (f : Set V))).card
          ≤ Nat.card {y : V // y ∈ (f : Set V)} := by rw [natCard_subtype_eq_filter_card]
        _ = (f : Set V).ncard := Nat.card_coe_set_eq _
        _ = r := huni f f.2
    exact_mod_cast this
  have htot : ((Finset.univ.filter (fun w : V => f ∈ Nset 𝓖 w)).card : ℝ)
      ≤ (r : ℝ) + (r : ℝ) * ((r : ℝ) * ((1 + ε) * D)) := by
    calc _ ≤ ((fset ∪ Nbh).card : ℝ) := by exact_mod_cast Finset.card_le_card hsplit
      _ ≤ (fset.card : ℝ) + (Nbh.card : ℝ) := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ _ := by linarith [hNbh_card, hf_card]
  have hpos : (0 : ℝ) ≤ (r : ℝ) ^ 2 * D := by positivity
  nlinarith [htot, hε1, hr1, hD1, hpos]

/-- The dependency degree of the per-vertex events is at most `100 r³ D³`. -/
lemma dep_card_le (𝓖 : Set (Set V)) {r : ℕ} (hr : 1 ≤ r) (hlin : HLin 𝓖) (huni : HUnif 𝓖 r)
    {ε D : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hD : 1 ≤ D)
    (hdeg : ∀ w : V, (hd 𝓖 w : ℝ) ≤ (1 + ε) * D) (v : V) :
    ((Finset.univ.filter (fun w : V => ((Nset 𝓖 v) ∩ (Nset 𝓖 w)).Nonempty)).card : ℝ)
      ≤ 100 * (r : ℝ) ^ 3 * D ^ 3 := by
  classical
  have hN := Nset_card_le 𝓖 hr hlin huni hε0 hε1 hD hdeg v
  have hsub : (Finset.univ.filter (fun w : V => ((Nset 𝓖 v) ∩ (Nset 𝓖 w)).Nonempty))
      ⊆ (Nset 𝓖 v).biUnion (fun f => Finset.univ.filter (fun w : V => f ∈ Nset 𝓖 w)) := by
    intro w hw
    obtain ⟨-, hne⟩ := Finset.mem_filter.mp hw
    obtain ⟨f, hf⟩ := hne
    exact Finset.mem_biUnion.mpr ⟨f, (Finset.mem_inter.mp hf).1, by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Finset.mem_inter.mp hf).2⟩⟩
  have hfib := fun f => Nset_fiber_card_le 𝓖 hr hlin huni hε0 hε1 hD hdeg f
  calc ((Finset.univ.filter (fun w : V => ((Nset 𝓖 v) ∩ (Nset 𝓖 w)).Nonempty)).card : ℝ)
      ≤ (((Nset 𝓖 v).biUnion (fun f => Finset.univ.filter (fun w : V => f ∈ Nset 𝓖 w))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ f ∈ Nset 𝓖 v,
          (Finset.univ.filter (fun w : V => f ∈ Nset 𝓖 w)).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ f ∈ Nset 𝓖 v, ((Finset.univ.filter (fun w : V => f ∈ Nset 𝓖 w)).card : ℝ) :=
        Nat.cast_sum _ _
    _ ≤ ∑ _f ∈ Nset 𝓖 v, 3 * (r : ℝ) ^ 2 * D := Finset.sum_le_sum (fun f _ => hfib f)
    _ = ((Nset 𝓖 v).card : ℝ) * (3 * (r : ℝ) ^ 2 * D) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (10 * (r : ℝ) * D ^ 2) * (3 * (r : ℝ) ^ 2 * D) := by
        apply mul_le_mul_of_nonneg_right hN; positivity
    _ ≤ 100 * (r : ℝ) ^ 3 * D ^ 3 := by
        have h1 : (10 * (r:ℝ) * D^2) * (3 * (r:ℝ)^2 * D) = 30 * (r:ℝ)^3 * D^3 := by ring
        have h2 : (0:ℝ) ≤ 30 * (r:ℝ)^3 * D^3 := by positivity
        nlinarith [h1, h2]

end Work.Deep.Nibble
