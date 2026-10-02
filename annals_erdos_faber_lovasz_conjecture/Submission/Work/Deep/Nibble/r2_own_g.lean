import Submission.Work.Deep.Nibble.r2_own_e
import Submission.Work.Deep.Nibble.bj_talagrand
import Submission.Work.Deep.Nibble.r2_own_a
import Submission.Work.Deep.Nibble.r2_own_b
import Submission.Work.Deep.Nibble.r2_own_c

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The tail bound for the residual-degree variable `Wv`, from `bj_talagrand`. -/
theorem r2_Wv_tail (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ) {D : ℕ}
    (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) < 1)
    (hlin : HLin 𝓖) (huni : HUnif 𝓖 r)
    (hdeg : ∀ v : V, (hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ))
    {ε' D' : ℝ} (hε' : 0 < ε') (hD' : 0 < D')
    (hthr : 50 * (r : ℝ) * Real.sqrt (2 * (D : ℝ)) < ε' * D' / 2) (v : V) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
        {ω : 𝓖 → Bool | ε' * D' / 2 ≤ |((Wv 𝓖 ω v : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))|}
      ≤ 4 * Real.exp (-(ε' * D' / 2) ^ 2 / (16 * (r : ℝ) ^ 2 * (2 * (D : ℝ)))) := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hp1' : θ / (D : ℝ) < 1 := hp1
  have hfull : ∀ (i : 𝓖) (x : Bool), 0 < (boolProb (θ / (D : ℝ)) hp0 hp1.le).wt x := by
    intro i x
    cases x with
    | true => simpa using (div_pos hθ0 hDpos)
    | false =>
        simp only [boolProb_wt_false]
        rw [sub_pos]
        exact hp1'
  have hle : ∀ ω : 𝓖 → Bool, ((Wv 𝓖 ω v : ℕ) : ℝ) ≤ 2 * (D : ℝ) := by
    intro ω
    have h1 : Wv 𝓖 ω v ≤ (thruF 𝓖 v).card := by
      rw [Wv]; exact Finset.card_filter_le _ _
    have h2 : ((thruF 𝓖 v).card : ℝ) = (hd 𝓖 v : ℝ) := by rw [hd_eq_card_thruF]
    calc ((Wv 𝓖 ω v : ℕ) : ℝ) ≤ ((thruF 𝓖 v).card : ℝ) := by exact_mod_cast h1
      _ = (hd 𝓖 v : ℝ) := h2
      _ ≤ 2 * (D : ℝ) := hdeg v
  have hcert : ∀ u : ℝ, 0 < u → ∀ ω : 𝓖 → Bool, ω ∉ (∅ : Set (𝓖 → Bool)) →
      ∃ I : Finset 𝓖, I.card ≤ 2 * D ∧
        ∀ ω' : 𝓖 → Bool, ω' ∉ (∅ : Set (𝓖 → Bool)) →
          ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (r : ℝ) →
            ((Wv 𝓖 ω' v : ℕ) : ℝ) < ((Wv 𝓖 ω v : ℕ) : ℝ) + u := by
    intro u hu ω _
    obtain ⟨I, hI, hI'⟩ := Wv_certificate 𝓖 (by omega) hlin huni ω v u hu
    have hcard2 : (thruF 𝓖 v).card ≤ 2 * D := by
      have h := hdeg v
      rw [hd_eq_card_thruF 𝓖 v] at h
      exact_mod_cast h
    exact ⟨I, le_trans hI hcard2, fun ω' _ h => hI' ω' h⟩
  have hmain := bj_talagrand (μ := fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le) hfull
    (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ)) (2 * (D : ℝ)) (by
      have : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
      linarith)
    (fun ω => by rw [abs_of_nonneg (by positivity)]; exact hle ω)
    (r : ℝ) (by exact_mod_cast (by omega : 1 ≤ r)) (2 * D) (by omega) (∅ : Set (𝓖 → Bool))
    (by rw [FinProb.prob_empty]; positivity) hcert (ε' * D' / 2) (by
      have h2D : ((2 * D : ℕ) : ℝ) = 2 * (D : ℝ) := by push_cast; ring
      rw [h2D]
      exact hthr)
  rw [FinProb.prob_empty, mul_zero, add_zero] at hmain
  have h2D : (((2 * D : ℕ)) : ℝ) = 2 * (D : ℝ) := by push_cast; ring
  have hfin : (FinProb.pi fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le).prob
        {ω : 𝓖 → Bool | ε' * D' / 2 ≤ |((Wv 𝓖 ω v : ℕ) : ℝ)
          - (FinProb.pi fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le).exp
              (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))|}
      ≤ 4 * Real.exp (-(ε' * D' / 2) ^ 2 / (16 * (r : ℝ) ^ 2 * (((2 * D : ℕ)) : ℝ))) := hmain
  rw [h2D] at hfin
  exact hfin

/-- The elementary bound on `k ↦ k·1[k ≥ 2]`. -/
lemma phi_sub_le (a b : ℕ) (h : a = b ∨ a = b + 1 ∨ a + 1 = b) :
    |(((if 2 ≤ a then a else 0 : ℕ)) : ℝ) - (((if 2 ≤ b then b else 0 : ℕ)) : ℝ)| ≤ 2 := by
  rcases h with h | h | h
  · subst h; simp
  · subst h
    by_cases hb : 2 ≤ b
    · have ha : 2 ≤ b + 1 := by omega
      rw [if_pos ha, if_pos hb]
      push_cast
      norm_num
    · have hb1 : b ≤ 1 := by omega
      interval_cases b <;> norm_num
  · subst h
    by_cases ha : 2 ≤ a
    · have hb : 2 ≤ a + 1 := by omega
      rw [if_pos hb, if_pos ha]
      push_cast
      norm_num
    · have ha1 : a ≤ 1 := by omega
      interval_cases a <;> norm_num

/-- Changing one coordinate changes `collMult` by at most `2r`. -/
lemma collMult_update_le (𝓖 : Set (Set V)) {r : ℕ} (huni : HUnif 𝓖 r) (f : 𝓖 → Bool)
    (e : 𝓖) (x : Bool) :
    |(((collMult 𝓖 (Function.update f e x) : ℕ) : ℝ)) - ((collMult 𝓖 f : ℕ) : ℝ)| ≤ 2 * r := by
  classical
  have hpt : ∀ ω ω' : 𝓖 → Bool, (∀ g : 𝓖, g ≠ e → ω' g = ω g) →
      |((collMult 𝓖 ω' : ℕ) : ℝ) - ((collMult 𝓖 ω : ℕ) : ℝ)| ≤ 2 * r := by
    intro ω ω' h
    have hkv : ∀ v : V, v ∉ (e : Set V) → kAtF 𝓖 ω' v = kAtF 𝓖 ω v := by
      intro v hv
      have hf : (thruF 𝓖 v).filter (fun g => ω' g = true)
          = (thruF 𝓖 v).filter (fun g => ω g = true) := by
        refine Finset.filter_congr ?_
        intro g hg
        rw [h g (fun hge => hv (hge ▸ (mem_thruF (𝓖 := 𝓖)).mp hg))]
      rw [kAtF, kAtF, hf]
    have hkv1F : ∀ v : V, kAtF 𝓖 ω' v = kAtF 𝓖 ω v ∨ kAtF 𝓖 ω' v = kAtF 𝓖 ω v + 1
        ∨ kAtF 𝓖 ω' v + 1 = kAtF 𝓖 ω v := by
      intro v
      have hsub1 : (thruF 𝓖 v).filter (fun g => ω' g = true)
          ⊆ insert e ((thruF 𝓖 v).filter (fun g => ω g = true)) := by
        intro g hg
        rw [Finset.mem_filter] at hg
        by_cases hge : g = e
        · rw [Finset.mem_insert]; exact Or.inl hge
        · rw [Finset.mem_insert]
          exact Or.inr (Finset.mem_filter.mpr ⟨hg.1, by rw [← h g hge]; exact hg.2⟩)
      have hsub2 : (thruF 𝓖 v).filter (fun g => ω g = true)
          ⊆ insert e ((thruF 𝓖 v).filter (fun g => ω' g = true)) := by
        intro g hg
        rw [Finset.mem_filter] at hg
        by_cases hge : g = e
        · rw [Finset.mem_insert]; exact Or.inl hge
        · rw [Finset.mem_insert]
          exact Or.inr (Finset.mem_filter.mpr ⟨hg.1, by rw [h g hge]; exact hg.2⟩)
      have h1 : ((thruF 𝓖 v).filter (fun g => ω' g = true)).card
          ≤ ((thruF 𝓖 v).filter (fun g => ω g = true)).card + 1 := by
        calc ((thruF 𝓖 v).filter (fun g => ω' g = true)).card
            ≤ (insert e ((thruF 𝓖 v).filter (fun g => ω g = true))).card :=
              Finset.card_le_card hsub1
          _ ≤ ((thruF 𝓖 v).filter (fun g => ω g = true)).card + 1 := Finset.card_insert_le _ _
      have h2 : ((thruF 𝓖 v).filter (fun g => ω g = true)).card
          ≤ ((thruF 𝓖 v).filter (fun g => ω' g = true)).card + 1 := by
        calc ((thruF 𝓖 v).filter (fun g => ω g = true)).card
            ≤ (insert e ((thruF 𝓖 v).filter (fun g => ω' g = true))).card :=
              Finset.card_le_card hsub2
          _ ≤ ((thruF 𝓖 v).filter (fun g => ω' g = true)).card + 1 := Finset.card_insert_le _ _
      have hk1 : kAtF 𝓖 ω' v ≤ kAtF 𝓖 ω v + 1 := by simpa [kAtF] using h1
      have hk2 : kAtF 𝓖 ω v ≤ kAtF 𝓖 ω' v + 1 := by simpa [kAtF] using h2
      omega
    have hkv1 : ∀ v : V, kAt 𝓖 ω' v = kAt 𝓖 ω v ∨ kAt 𝓖 ω' v = kAt 𝓖 ω v + 1
        ∨ kAt 𝓖 ω' v + 1 = kAt 𝓖 ω v := by
      intro v
      have h := hkv1F v
      rw [kAt_eq_kAtF 𝓖 ω' v, kAt_eq_kAtF 𝓖 ω v]
      exact h
    have hsum : ∀ ω'' : 𝓖 → Bool, ((collMult 𝓖 ω'' : ℕ) : ℝ)
        = ∑ v : V, (((if 2 ≤ kAt 𝓖 ω'' v then kAt 𝓖 ω'' v else 0 : ℕ)) : ℝ) := by
      intro ω''
      rw [collMult, Nat.cast_sum]
    rw [hsum ω', hsum ω]
    rw [← Finset.sum_sub_distrib]
    have hnil : ∀ v ∈ (Finset.univ : Finset V),
        v ∉ Finset.univ.filter (fun v : V => v ∈ (e : Set V)) →
          ((((if 2 ≤ kAt 𝓖 ω' v then kAt 𝓖 ω' v else 0 : ℕ)) : ℝ)
            - (((if 2 ≤ kAt 𝓖 ω v then kAt 𝓖 ω v else 0 : ℕ)) : ℝ)) = 0 := by
      intro v _ hv
      have hv' : v ∉ (e : Set V) := by simpa using hv
      have h1 : kAt 𝓖 ω' v = kAt 𝓖 ω v := by
        rw [kAt_eq_kAtF, kAt_eq_kAtF]; exact hkv v hv'
      rw [h1]
      ring
    rw [← Finset.sum_subset (Finset.subset_univ _) hnil]
    calc |∑ v ∈ Finset.univ.filter (fun v : V => v ∈ (e : Set V)),
            ((((if 2 ≤ kAt 𝓖 ω' v then kAt 𝓖 ω' v else 0 : ℕ)) : ℝ)
              - (((if 2 ≤ kAt 𝓖 ω v then kAt 𝓖 ω v else 0 : ℕ)) : ℝ))|
        ≤ ∑ v ∈ Finset.univ.filter (fun v : V => v ∈ (e : Set V)),
            |((((if 2 ≤ kAt 𝓖 ω' v then kAt 𝓖 ω' v else 0 : ℕ)) : ℝ)
              - (((if 2 ≤ kAt 𝓖 ω v then kAt 𝓖 ω v else 0 : ℕ)) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ Finset.univ.filter (fun v : V => v ∈ (e : Set V)), (2 : ℝ) := by
          refine Finset.sum_le_sum fun v _ => ?_
          exact phi_sub_le _ _ (hkv1 v)
      _ = 2 * (((Finset.univ.filter (fun v : V => v ∈ (e : Set V))).card : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ = 2 * (r : ℝ) := by
          have hc : (Finset.univ.filter (fun v : V => v ∈ (e : Set V))).card = r := by
            rw [← natCard_subtype_eq_filter_card (fun x : V => x ∈ (e : Set V))]
            exact huni e e.2
          rw [hc]
  have := hpt f (Function.update f e x) (fun g hg => Function.update_of_ne hg x f)
  simpa using this

/-- The tail bound for the collision multiplicity `collMult`, from bounded differences. -/
theorem r2_S_tail (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) (huni : HUnif 𝓖 r)
    {θ : ℝ} {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hG : 𝓖.Nonempty) {t : ℝ} (ht : 100 * (r : ℝ) * Real.sqrt (Nat.card 𝓖 : ℝ) < t) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | t ≤ |((collMult 𝓖 ω : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))|}
      ≤ 4 * Real.exp (-t ^ 2 / (16 * (2 * (r : ℝ)) ^ 2 * (Nat.card 𝓖 : ℝ))) := by
  classical
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have htpos : 0 < t := by
    have : (0:ℝ) ≤ Real.sqrt (Nat.card 𝓖 : ℝ) := Real.sqrt_nonneg _
    nlinarith [ht, this, hr1]
  have htail := Work.Deep.Reed.Prob.hoeffding_bounded_differences
    (μ := fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)
    (X := fun ω => ((collMult 𝓖 ω : ℕ) : ℝ)) (c := fun _ => (2 * (r : ℝ)))
    (fun _ => by positivity)
    (fun i f x => collMult_update_le 𝓖 huni f i x) (t := t / 2) (by linarith)
  have hsum : (∑ i : 𝓖, (2 * (r : ℝ)) ^ 2) = (Nat.card 𝓖 : ℝ) * (2 * (r : ℝ)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  rw [hsum] at htail
  have hsub : {ω : 𝓖 → Bool | t ≤ |((collMult 𝓖 ω : ℕ) : ℝ)
        - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))|}
      ⊆ {ω : 𝓖 → Bool | t / 2 < |((collMult 𝓖 ω : ℕ) : ℝ)
        - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
            (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))|} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω ⊢
    have h1 : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))
        = (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
            (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ)) := rfl
    rw [h1] at hω
    linarith
  have hstep : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | t / 2 < |((collMult 𝓖 ω : ℕ) : ℝ)
          - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
              (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))|}
      ≤ 2 * Real.exp (-(2 * (t / 2) ^ 2) / ((Nat.card 𝓖 : ℝ) * (2 * (r : ℝ)) ^ 2)) := htail
  have hfinal : 2 * Real.exp (-(2 * (t / 2) ^ 2) / ((Nat.card 𝓖 : ℝ) * (2 * (r : ℝ)) ^ 2))
      ≤ 4 * Real.exp (-t ^ 2 / (16 * (2 * (r : ℝ)) ^ 2 * (Nat.card 𝓖 : ℝ))) := by
    have hN : (0:ℝ) < (Nat.card 𝓖 : ℝ) := by
      obtain ⟨x, hx⟩ := hG
      haveI : Nonempty 𝓖 := ⟨⟨x, hx⟩⟩
      exact_mod_cast Nat.card_pos
    have hkey : t ^ 2 * ((Nat.card 𝓖 : ℝ) * (2 * (r : ℝ)) ^ 2)
        ≤ 2 * (t / 2) ^ 2 * (16 * (2 * (r : ℝ)) ^ 2 * (Nat.card 𝓖 : ℝ)) := by
      have hpos : (0:ℝ) ≤ (Nat.card 𝓖 : ℝ) * (2 * (r:ℝ))^2 := by positivity
      have h8 : t^2 ≤ t^2/2 * 16 := by nlinarith [sq_nonneg t]
      calc t^2 * ((Nat.card 𝓖 : ℝ) * (2*(r:ℝ))^2)
          ≤ (t^2/2 * 16) * ((Nat.card 𝓖 : ℝ) * (2*(r:ℝ))^2) :=
            mul_le_mul_of_nonneg_right h8 hpos
        _ = 2 * (t / 2) ^ 2 * (16 * (2 * (r : ℝ)) ^ 2 * (Nat.card 𝓖 : ℝ)) := by ring
    have h2 : Real.exp (-(2 * (t / 2) ^ 2) / ((Nat.card 𝓖 : ℝ) * (2 * (r : ℝ)) ^ 2))
        ≤ Real.exp (-t ^ 2 / (16 * (2 * (r : ℝ)) ^ 2 * (Nat.card 𝓖 : ℝ))) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hkey]
    linarith [Real.exp_pos (-t ^ 2 / (16 * (2 * (r : ℝ)) ^ 2 * (Nat.card 𝓖 : ℝ))), h2]
  exact le_trans (le_trans (FinProb.prob_mono _ hsub) hstep) hfinal

end Work.Deep.Nibble