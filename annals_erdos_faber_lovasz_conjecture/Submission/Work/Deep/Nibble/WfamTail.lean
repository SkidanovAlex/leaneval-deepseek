import Submission.Work.Deep.Nibble.FamTailDefs
import Submission.Work.Deep.Nibble.r2_Mfam_tail
import Submission.Work.Deep.Nibble.r2_Yfam_tail

/-!
# The waste tail of one wasteful round

This module proves `Work.Deep.Nibble.r2_Wfam_tail`: the upper tail of the
edge-charged waste

    badSum 𝓖 ω S = ∑_{e bad in ω} |e ∩ S|

of one round, around its mean `≤ 2 r θ² |S|`.

The statistic is *not* monotone in the kept set, so `bj_talagrand` is applied to
`X := -badSum`: the certificate must control the *decrease* of `badSum`.  The
certificate of an outcome `ω` is

* the bad kept edges of `ω` meeting `S` (`I0F`), whose number is at most
  `badSum ≤ Zsum ≤ 4θ|S|` off the exceptional event `{4θ|S| < Zsum}`, together
  with
* one kept witness `witE 𝓖 ω e` of each of them (`certW`).

If `ω'` disagrees with `ω` in fewer than `u/(2r²)` coordinates of `certW`, then
`badSum ω - badSum ω' < u`: an edge of `I0F` that is bad in `ω` but not in `ω'`
is either unkept in `ω'` (a disagreement), or kept in `ω'`, in which case its
chosen witness is unkept in `ω'` (again a disagreement).  The edges of the second
kind whose witness is a fixed `g` are pairwise disjoint — they are kept in `ω'`
and none of them is bad in `ω'` — and all meet `g`, so there are at most
`|g| = r` of them, each contributing at most `r`; whence the factor `2 r²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bad kept edges of `ω` meeting `S`. -/
noncomputable def I0F (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : Finset 𝓖 := by
  classical
  exact Finset.univ.filter (fun e => badAt 𝓖 ω e ∧ ((e : Set V) ∩ (S : Set V)).Nonempty)

/-- The certificate of the waste count: the bad kept edges meeting `S`, plus one
kept witness of each. -/
noncomputable def certW (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) : Finset 𝓖 := by
  classical
  exact I0F 𝓖 ω S ∪ (I0F 𝓖 ω S).image (witE 𝓖 ω)

lemma mem_I0F {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {S : Finset V} {e : 𝓖} :
    e ∈ I0F 𝓖 ω S ↔ badAt 𝓖 ω e ∧ ((e : Set V) ∩ (S : Set V)).Nonempty := by
  classical
  simp only [I0F, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_certW {𝓖 : Set (Set V)} {ω : 𝓖 → Bool} {S : Finset V} {e : 𝓖} :
    e ∈ certW 𝓖 ω S ↔ e ∈ I0F 𝓖 ω S ∨ ∃ f ∈ I0F 𝓖 ω S, witE 𝓖 ω f = e := by
  classical
  simp only [certW, Finset.mem_union, Finset.mem_image]

/-- The edge-charged waste as a sum over the bad kept edges meeting `S`. -/
lemma badSum_eq_sum_I0F (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    badSum 𝓖 ω S = ∑ e ∈ I0F 𝓖 ω S, ((e : Set V) ∩ (S : Set V)).ncard := by
  classical
  rw [badSum, I0F, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : badAt 𝓖 ω e
  · by_cases h2 : ((e : Set V) ∩ (S : Set V)).Nonempty
    · rw [if_pos h, if_pos ⟨h, h2⟩]
    · have hz : ((e : Set V) ∩ (S : Set V)).ncard = 0 := by
        rw [Set.ncard_eq_toFinset_card]
        have hempty : ((e : Set V) ∩ (S : Set V)) = ∅ := Set.not_nonempty_iff_eq_empty.mp h2
        simp [hempty]
      rw [if_pos h, if_neg (fun hc => h2 hc.2), hz]
  · rw [if_neg h, if_neg (fun hc => h hc.1)]

/-- The bad kept edges meeting `S` are dominated by the weighted kept count. -/
lemma I0F_card_le_Zsum (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    (I0F 𝓖 ω S).card ≤ Zsum 𝓖 ω S := by
  classical
  have h1 : (I0F 𝓖 ω S).card = ∑ _e ∈ I0F 𝓖 ω S, (1 : ℕ) := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  have h2 : ∑ _e ∈ I0F 𝓖 ω S, (1 : ℕ)
      ≤ ∑ e ∈ I0F 𝓖 ω S, ((e : Set V) ∩ (S : Set V)).ncard := by
    refine Finset.sum_le_sum fun e he => ?_
    exact (Set.ncard_pos (s := ((e : Set V) ∩ (S : Set V)))).mpr (mem_I0F.mp he).2
  have h3 : ∑ e ∈ I0F 𝓖 ω S, ((e : Set V) ∩ (S : Set V)).ncard ≤ Zsum 𝓖 ω S := by
    have h3' : ∑ e ∈ I0F 𝓖 ω S, ((e : Set V) ∩ (S : Set V)).ncard
        = ∑ e ∈ I0F 𝓖 ω S,
            (if ω e then ((e : Set V) ∩ (S : Set V)).ncard else 0) := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [if_pos (mem_I0F.mp he).1.1]
    rw [h3', Zsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
      (fun e _ _ => by split_ifs <;> omega)
  omega

/-- The certificate has at most `2 * Zsum` elements. -/
lemma certW_card_le (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) (S : Finset V) :
    (certW 𝓖 ω S).card ≤ 2 * Zsum 𝓖 ω S := by
  classical
  have h1 : (certW 𝓖 ω S).card
      ≤ (I0F 𝓖 ω S).card + ((I0F 𝓖 ω S).image (witE 𝓖 ω)).card := by
    rw [certW]; exact Finset.card_union_le _ _
  have h2 : ((I0F 𝓖 ω S).image (witE 𝓖 ω)).card ≤ (I0F 𝓖 ω S).card :=
    Finset.card_image_le
  have h3 := I0F_card_le_Zsum 𝓖 ω S
  omega

/-- **The certificate inequality for the waste.**  If `ω'` disagrees with `ω` in
fewer than `u/(2r²)` coordinates of the certificate `certW 𝓖 ω S`, then the waste
decreases by less than `u`. -/
lemma badSum_cert {𝓖 : Set (Set V)} {r : ℕ} (hr : 1 ≤ r) (huni : HUnif 𝓖 r)
    (S : Finset V) (ω ω' : 𝓖 → Bool) {u : ℝ}
    (hlt : (((certW 𝓖 ω S).filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (2 * (r : ℝ) ^ 2)) :
    -(((badSum 𝓖 ω' S : ℕ) : ℝ)) < -(((badSum 𝓖 ω S : ℕ) : ℝ)) + u := by
  classical
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  set B : Finset 𝓖 := I0F 𝓖 ω S with hB
  set Dd : Finset 𝓖 := (certW 𝓖 ω S).filter (fun i => ω i ≠ ω' i) with hDd
  set B1 : Finset 𝓖 := B.filter (fun e => ω' e = true ∧ badAt 𝓖 ω' e) with hB1
  set A : Finset 𝓖 := B \ B1 with hA
  set A0 : Finset 𝓖 := A.filter (fun e => ω' e = false) with hA0
  set A1 : Finset 𝓖 := A.filter (fun e => ω' e = true) with hA1
  have hBmem : ∀ e, e ∈ B ↔ badAt 𝓖 ω e ∧ ((e : Set V) ∩ (S : Set V)).Nonempty := by
    intro e; rw [hB]; exact mem_I0F
  have hB1mem : ∀ e, e ∈ B1 ↔ e ∈ B ∧ ω' e = true ∧ badAt 𝓖 ω' e := by
    intro e; rw [hB1]; exact Finset.mem_filter
  have hAmem : ∀ e, e ∈ A ↔ e ∈ B ∧ e ∉ B1 := by
    intro e; rw [hA]; exact Finset.mem_sdiff
  have hA1mem : ∀ e, e ∈ A1 ↔ e ∈ A ∧ ω' e = true := by
    intro e; rw [hA1]; exact Finset.mem_filter
  have hA0mem : ∀ e, e ∈ A0 ↔ e ∈ A ∧ ω' e = false := by
    intro e; rw [hA0]; exact Finset.mem_filter
  have hDdmem : ∀ e, e ∈ Dd ↔ e ∈ certW 𝓖 ω S ∧ ω e ≠ ω' e := by
    intro e; rw [hDd]; exact Finset.mem_filter
  have hB1sub : B1 ⊆ B := Finset.filter_subset _ _
  have hAsub : A ⊆ B := Finset.sdiff_subset
  -- (L1) `badSum ω` is the sum over `B`
  have hL1 : ((badSum 𝓖 ω S : ℕ) : ℝ)
      = ∑ e ∈ B, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by
    rw [badSum_eq_sum_I0F 𝓖 ω S, ← hB, Nat.cast_sum]
  -- (L2) `badSum ω'` dominates the sum over `B1`
  have hL2 : ∑ e ∈ B1, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
      ≤ ((badSum 𝓖 ω' S : ℕ) : ℝ) := by
    have h1 : ((badSum 𝓖 ω' S : ℕ) : ℝ)
        = ∑ e : 𝓖, ((if badAt 𝓖 ω' e
            then ((e : Set V) ∩ (S : Set V)).ncard else 0 : ℕ) : ℝ) := by
      rw [badSum, Nat.cast_sum]
    rw [h1]
    have h2 : (∑ e ∈ B1, ((e : Set V) ∩ (S : Set V)).ncard : ℕ)
        ≤ ∑ e : 𝓖, (if badAt 𝓖 ω' e then ((e : Set V) ∩ (S : Set V)).ncard else 0) := by
      have h2' : ∑ e ∈ B1, ((e : Set V) ∩ (S : Set V)).ncard
          = ∑ e ∈ B1,
              (if badAt 𝓖 ω' e then ((e : Set V) ∩ (S : Set V)).ncard else 0) := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [if_pos ((hB1mem e).mp he).2.2]
      rw [h2']
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => Finset.mem_univ _)
        (fun e _ _ => by split_ifs <;> omega)
    exact_mod_cast h2
  -- every edge of `A` contributes at most `r`
  have hncard_le_r : ∀ e ∈ A, ((e : Set V) ∩ (S : Set V)).ncard ≤ r := by
    intro e he
    have heB : e ∈ B := hAsub he
    have h1 : ((e : Set V) ∩ (S : Set V)).ncard ≤ (e : Set V).ncard :=
      Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
    have h2 : ((e : Set V) : Set V).ncard = r := huni (e : Set V) e.2
    omega
  -- the case-(a) edges are disagreements
  have hA0sub : A0 ⊆ Dd := by
    intro e he
    obtain ⟨heA, hfalse⟩ := (hA0mem e).mp he
    have heB : e ∈ B := hAsub heA
    have hbad : badAt 𝓖 ω e := (hBmem e).mp heB |>.1
    refine (hDdmem e).mpr ⟨mem_certW.mpr (Or.inl heB), ?_⟩
    simp [hbad.1, hfalse]
  -- the case-(b) edges are counted by their witness
  have hfib : A1.card ≤ r * Dd.card := by
    have hmaps : Set.MapsTo (witE 𝓖 ω) ↑A1 ↑Dd := by
      intro e he
      rw [Finset.mem_coe] at he
      obtain ⟨heA, htrue'⟩ := (hA1mem e).mp he
      obtain ⟨heB, hnotB1⟩ := (hAmem e).mp heA
      have hbad : badAt 𝓖 ω e := (hBmem e).mp heB |>.1
      have hwit := witE_spec hbad
      refine (hDdmem _).mpr ⟨mem_certW.mpr (Or.inr ⟨e, heB, rfl⟩), ?_⟩
      intro heq
      have htrue : ω' (witE 𝓖 ω e) = true := by rw [← heq]; exact hwit.2.1
      have hbad' : badAt 𝓖 ω' e := ⟨htrue', ⟨witE 𝓖 ω e, hwit.1, htrue, hwit.2.2⟩⟩
      exact hnotB1 ((hB1mem e).mpr ⟨heB, htrue', hbad'⟩)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib_disj : ∀ g, ∀ e ∈ A1.filter (fun e => witE 𝓖 ω e = g),
        ∀ f ∈ A1.filter (fun e => witE 𝓖 ω e = g), e ≠ f →
          Disjoint (e : Set V) (f : Set V) := by
      intro g e he f hf hef
      obtain ⟨he1, -⟩ := Finset.mem_filter.mp he
      obtain ⟨hf1, -⟩ := Finset.mem_filter.mp hf
      obtain ⟨heA, hte⟩ := (hA1mem e).mp he1
      obtain ⟨hfA, htf⟩ := (hA1mem f).mp hf1
      obtain ⟨heB, hnotB1⟩ := (hAmem e).mp heA
      by_contra hnot
      rw [Set.not_disjoint_iff] at hnot
      obtain ⟨x, hx1, hx2⟩ := hnot
      have hbad' : badAt 𝓖 ω' e := ⟨hte, ⟨f, hef.symm, htf, ⟨x, hx2, hx1⟩⟩⟩
      exact hnotB1 ((hB1mem e).mpr ⟨heB, hte, hbad'⟩)
    have hfib_meet : ∀ g, ∀ e ∈ A1.filter (fun e => witE 𝓖 ω e = g),
        ((e : Set V) ∩ (g : Set V)).Nonempty := by
      intro g e he
      obtain ⟨he1, hwg⟩ := Finset.mem_filter.mp he
      obtain ⟨heA, -⟩ := (hA1mem e).mp he1
      obtain ⟨heB, -⟩ := (hAmem e).mp heA
      have hbad : badAt 𝓖 ω e := (hBmem e).mp heB |>.1
      have hmeet : ((e : Set V) ∩ (witE 𝓖 ω e : Set V)).Nonempty := by
        rw [Set.inter_comm]
        exact (witE_spec hbad).2.2
      rwa [hwg] at hmeet
    calc ∑ g ∈ Dd, (A1.filter (fun e => witE 𝓖 ω e = g)).card
        ≤ ∑ _g ∈ Dd, r := by
          refine Finset.sum_le_sum fun g _ => ?_
          exact card_le_eFin_card_of_pairwiseDisjoint_meets huni (hfib_disj g) (hfib_meet g)
      _ = Dd.card * r := Finset.sum_const_nat (fun _ _ => rfl)
      _ = r * Dd.card := Nat.mul_comm _ _
  -- the split of `A`
  have hAcard : A.card ≤ A0.card + A1.card := by
    have h1 : A = A0 ∪ A1 := by
      ext e
      rw [hA0, hA1]
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro he
        by_cases h : ω' e = false
        · exact Or.inl ⟨he, h⟩
        · exact Or.inr ⟨he, by simpa using h⟩
      · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
    rw [h1]
    exact Finset.card_union_le _ _
  have hsumA : ∑ e ∈ A, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) ≤ (r : ℝ) * A.card := by
    calc ∑ e ∈ A, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
        ≤ ∑ _e ∈ A, (r : ℝ) := by
          refine Finset.sum_le_sum fun e he => ?_
          exact_mod_cast hncard_le_r e he
      _ = (r : ℝ) * A.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- the decrease is at most the sum over `A`
  have hdec : ((badSum 𝓖 ω S : ℕ) : ℝ) - ((badSum 𝓖 ω' S : ℕ) : ℝ)
      ≤ ∑ e ∈ A, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by
    have hsplit : ∑ e ∈ B, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
        = ∑ e ∈ B1, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
          + ∑ e ∈ A, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by
      have h1 : B1 ∪ A = B := by
        rw [hA]; exact Finset.union_sdiff_of_subset hB1sub
      have h2 : Disjoint B1 A := by
        rw [hA]; exact Finset.disjoint_sdiff
      have h3 : ∑ e ∈ B1 ∪ A, (((e : Set V) ∩ (S : Set V)).ncard : ℝ)
          = ∑ e ∈ B, (((e : Set V) ∩ (S : Set V)).ncard : ℝ) := by rw [h1]
      rw [← h3, Finset.sum_union h2]
    rw [hL1, hsplit]
    linarith [hL2]
  -- final arithmetic
  have hDdR : ((Dd.card : ℕ) : ℝ) < u / (2 * (r : ℝ) ^ 2) := by
    rw [hDd]; exact hlt
  have hDdR' : (Dd.card : ℝ) * (2 * (r : ℝ) ^ 2) < u :=
    (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (r : ℝ) ^ 2)).mp hDdR
  have hDd0 : (0 : ℝ) ≤ (Dd.card : ℝ) := Nat.cast_nonneg _
  have hA0R : ((A0.card : ℕ) : ℝ) ≤ (Dd.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hA0sub
  have hA1R : ((A1.card : ℕ) : ℝ) ≤ (r : ℝ) * (Dd.card : ℝ) := by
    exact_mod_cast hfib
  have hAcR : ((A.card : ℕ) : ℝ) ≤ (A0.card : ℝ) + (A1.card : ℝ) := by
    exact_mod_cast hAcard
  have hle : ((badSum 𝓖 ω S : ℕ) : ℝ) - ((badSum 𝓖 ω' S : ℕ) : ℝ)
      ≤ (r : ℝ) * (A.card : ℝ) := le_trans hdec hsumA
  nlinarith [hle, hAcR, hA0R, hA1R, hDdR', hDd0, hr1R]

/-! ## The tail bound -/

/-- A random variable constant on all outcomes deviates from its mean by nothing. -/
private lemma prob_le_of_const' {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (X : Ω → ℝ) (c : ℝ)
    (hX : X = fun _ => c) {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C) :
    μ.prob {ω | t ≤ |X ω - μ.exp X|} ≤ C := by
  classical
  have hexp : μ.exp X = c := by rw [hX, FinProb.exp_const]
  have hempty : {ω | t ≤ |X ω - μ.exp X|} = ∅ := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have h1 : X ω = c := congr_fun hX ω
    rw [hexp, h1, sub_self, abs_zero]
    exact not_le.mpr ht
  rw [hempty, FinProb.prob_empty]
  exact hC

theorem r2_Wfam_tail {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {r : ℕ}
    (hr : 1 ≤ r) (huni : HUnif 𝓖 r) {θ δ ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) < 1)
    (hdeg : ∀ v : V, |((hd 𝓖 v : ℝ)) - (D : ℝ)| ≤ ε * (D : ℝ))
    (S : Finset V)
    (hmean : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
      (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))
        ≤ 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))
    {exc : ℝ}
    (hexc : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
      {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} ≤ exc)
    (hexcM : exc ≤ 1 / (2 * (D : ℝ) * (S.card : ℝ) + 1) ^ 2)
    (hSlarge : 10 ^ 6 * (r : ℝ) ^ 2 ≤ θ ^ 3 * δ ^ 2 * (S.card : ℝ)) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
      {ω : 𝓖 → Bool | (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
        < ((badSum 𝓖 ω S : ℕ) : ℝ)}
      ≤ 4 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (512 * (r : ℝ) ^ 2)) + 4 * exc := by
  classical
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hp_pos : 0 < θ / (D : ℝ) := div_pos hθ0 hDpos
  have hδnn : 0 ≤ δ := le_of_lt hδ0
  have hexc0 : 0 ≤ exc := le_trans (FinProb.prob_nonneg _ _) hexc
  have htarget : (0 : ℝ) ≤ 4 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (512 * (r : ℝ) ^ 2))
      + 4 * exc := by
    have h1 : (0 : ℝ) ≤ Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (512 * (r : ℝ) ^ 2)) :=
      Real.exp_nonneg _
    nlinarith [h1, hexc0]
  rcases Nat.eq_zero_or_pos S.card with hS0 | hSpos
  · -- `S = ∅`: the event is empty
    have hSempty : S = ∅ := Finset.card_eq_zero.mp hS0
    have hz : ∀ ω : 𝓖 → Bool, badSum 𝓖 ω S = 0 := by
      intro ω
      rw [badSum_eq_sum_I0F 𝓖 ω S, hSempty]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [Finset.coe_empty, Set.inter_empty, Set.ncard_empty]
    have hempty : {ω : 𝓖 → Bool | (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
        < ((badSum 𝓖 ω S : ℕ) : ℝ)} = ∅ := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [hz ω]
      simp only [Nat.cast_zero]
      have h1 : (0 : ℝ) ≤ (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ) := by
        have h2 : 0 ≤ 1 + δ := by linarith
        have h3 : 0 ≤ 2 * (r : ℝ) * θ ^ 2 := by positivity
        have h4 : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
        exact mul_nonneg (mul_nonneg h2 h3) h4
      exact not_lt.mpr h1
    rw [hempty, FinProb.prob_empty]
    exact htarget
  · -- non-degenerate
    set M : ℝ := 2 * (D : ℝ) * (S.card : ℝ) + 1 with hMdef
    have hM1 : 1 ≤ M := by
      rw [hMdef]
      have h0 : (0 : ℝ) ≤ 2 * (D : ℝ) * (S.card : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hDpos)) (Nat.cast_nonneg _)
      linarith
    have hsup : ∀ ω : 𝓖 → Bool, |(-(((badSum 𝓖 ω S : ℕ) : ℝ)))| ≤ M := by
      intro ω
      have h1 : badSum 𝓖 ω S ≤ 2 * D * S.card := badSum_le_two_mul_D hε1 hdeg ω S
      have h2 : ((badSum 𝓖 ω S : ℕ) : ℝ) ≤ 2 * (D : ℝ) * (S.card : ℝ) := by
        have h3 : ((badSum 𝓖 ω S : ℕ) : ℝ) ≤ ((2 * D * S.card : ℕ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h3
        linarith
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _), hMdef]
      linarith
    have hfull : ∀ i : 𝓖, ∀ x : Bool,
        0 < ((fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le) i).wt x := by
      intro i x
      cases x with
      | true => simpa using hp_pos
      | false => simpa using (show (0 : ℝ) < 1 - θ / (D : ℝ) by linarith)
    -- the certificate and its size
    have hcert : ∀ u : ℝ, 0 < u → ∀ ω : 𝓖 → Bool, ω ∉ {ω : 𝓖 → Bool |
        4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} →
        ∃ I : Finset 𝓖, I.card ≤ Nat.ceil (8 * θ * (S.card : ℝ)) + 1 ∧
          ∀ ω' : 𝓖 → Bool, ω' ∉ {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ)
              < ((Zsum 𝓖 ω S : ℕ) : ℝ)} →
            ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / (2 * (r : ℝ) ^ 2) →
              (-(((badSum 𝓖 ω' S : ℕ) : ℝ))) < (-(((badSum 𝓖 ω S : ℕ) : ℝ))) + u := by
      intro u hu ω hω
      refine ⟨certW 𝓖 ω S, ?_, fun ω' _ hlt => badSum_cert hr huni S ω ω' hlt⟩
      have hZle : ((Zsum 𝓖 ω S : ℕ) : ℝ) ≤ 4 * θ * (S.card : ℝ) := not_lt.mp hω
      have h1 : (certW 𝓖 ω S).card ≤ 2 * Zsum 𝓖 ω S := certW_card_le 𝓖 ω S
      have h2 : ((certW 𝓖 ω S).card : ℝ) ≤ 8 * θ * (S.card : ℝ) := by
        have h3 : ((2 * Zsum 𝓖 ω S : ℕ) : ℝ) ≤ 2 * (4 * θ * (S.card : ℝ)) := by
          push_cast
          linarith
        have h4 : ((certW 𝓖 ω S).card : ℝ) ≤ ((2 * Zsum 𝓖 ω S : ℕ) : ℝ) := by
          exact_mod_cast h1
        linarith
      have h3 : (certW 𝓖 ω S).card ≤ Nat.ceil (8 * θ * (S.card : ℝ)) := by
        have h4 : ((certW 𝓖 ω S).card : ℝ) ≤ (Nat.ceil (8 * θ * (S.card : ℝ)) : ℝ) :=
          le_trans h2 (Nat.le_ceil _)
        exact_mod_cast h4
      omega
    have hcs : 50 * (2 * (r : ℝ) ^ 2)
        * Real.sqrt ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)
        < δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)) := by
      have hs : ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ) ≤ 9 * (θ * (S.card : ℝ)) := by
        have h1 : (Nat.ceil (8 * θ * (S.card : ℝ)) : ℝ) ≤ 8 * θ * (S.card : ℝ) + 1 :=
          le_of_lt (Nat.ceil_lt_add_one (by positivity))
        have h2 : 2 ≤ θ * (S.card : ℝ) := by
          have h3 : θ ^ 3 * δ ^ 2 ≤ θ := by
            have h4 : θ ^ 2 * δ ^ 2 ≤ 1 := by
              have h5 : θ ^ 2 ≤ 1 := by nlinarith [hθ0, hθ1]
              have h6 : δ ^ 2 ≤ 1 := by nlinarith [hδ0, hδ1]
              nlinarith [h5, h6]
            have h7 : θ ^ 3 * δ ^ 2 = θ * (θ ^ 2 * δ ^ 2) := by ring
            rw [h7]
            exact mul_le_of_le_one_right (le_of_lt hθ0) h4
          have h8 : θ ^ 3 * δ ^ 2 * (S.card : ℝ) ≤ θ * (S.card : ℝ) :=
            mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
          have h9 : (10 : ℝ) ^ 6 * (r : ℝ) ^ 2 ≤ θ * (S.card : ℝ) := le_trans hSlarge h8
          have h10 : (2 : ℝ) ≤ (10 : ℝ) ^ 6 * (r : ℝ) ^ 2 := by
            have h11 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [hr1R]
            nlinarith [h11]
          linarith
        push_cast
        linarith
      have hsqrt9 : Real.sqrt ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)
          ≤ 3 * Real.sqrt (θ * (S.card : ℝ)) := by
        have hsq : ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)
            ≤ (3 * Real.sqrt (θ * (S.card : ℝ))) ^ 2 := by
          have h2 : (3 * Real.sqrt (θ * (S.card : ℝ))) ^ 2 = 9 * (θ * (S.card : ℝ)) := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
            norm_num
          rw [h2]
          exact hs
        calc Real.sqrt ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)
            ≤ Real.sqrt ((3 * Real.sqrt (θ * (S.card : ℝ))) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = 3 * Real.sqrt (θ * (S.card : ℝ)) := Real.sqrt_sq (by positivity)
      have hstep : 50 * (2 * (r : ℝ) ^ 2)
            * Real.sqrt ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)
          ≤ 300 * (r : ℝ) ^ 2 * Real.sqrt (θ * (S.card : ℝ)) := by
        have h1 := mul_le_mul_of_nonneg_left hsqrt9
          (by positivity : (0 : ℝ) ≤ 50 * (2 * (r : ℝ) ^ 2))
        have h2 : 50 * (2 * (r : ℝ) ^ 2) * (3 * Real.sqrt (θ * (S.card : ℝ)))
            = 300 * (r : ℝ) ^ 2 * Real.sqrt (θ * (S.card : ℝ)) := by ring
        linarith [h1, h2]
      have hs2 : 1 ≤ θ * (S.card : ℝ) := by
        have h3 : θ ^ 3 * δ ^ 2 ≤ θ := by
          have h4 : θ ^ 2 * δ ^ 2 ≤ 1 := by
            have h5 : θ ^ 2 ≤ 1 := by nlinarith [hθ0, hθ1]
            have h6 : δ ^ 2 ≤ 1 := by nlinarith [hδ0, hδ1]
            nlinarith [h5, h6]
          have h7 : θ ^ 3 * δ ^ 2 = θ * (θ ^ 2 * δ ^ 2) := by ring
          rw [h7]
          exact mul_le_of_le_one_right (le_of_lt hθ0) h4
        have h8 : θ ^ 3 * δ ^ 2 * (S.card : ℝ) ≤ θ * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
        have h9 : (1 : ℝ) ≤ (10 : ℝ) ^ 6 * (r : ℝ) ^ 2 := by
          have h11 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [hr1R]
          nlinarith [h11]
        linarith [hSlarge, h8, h9]
      have hkey : 300 * (r : ℝ) ^ 2 * Real.sqrt (θ * (S.card : ℝ))
          < δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)) := by
        have htsq : (δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2
            = 4 * δ ^ 2 * (r : ℝ) ^ 2 * θ ^ 4 * (S.card : ℝ) ^ 2 := by ring
        have hrsq : (300 * (r : ℝ) ^ 2 * Real.sqrt (θ * (S.card : ℝ))) ^ 2
            = 90000 * (r : ℝ) ^ 4 * (θ * (S.card : ℝ)) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          ring
        have hcoef : 22500 * (r : ℝ) ^ 2 < δ ^ 2 * θ ^ 3 * (S.card : ℝ) := by
          have h1 : (22500 : ℝ) < 10 ^ 6 := by norm_num
          have h2 : 0 < (r : ℝ) ^ 2 := by positivity
          nlinarith [hSlarge, h1, h2]
        have hpos : 0 < θ * (S.card : ℝ) := by linarith [hs2, hθ0]
        have hb : 0 < δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)) := by positivity
        have hlt : (300 * (r : ℝ) ^ 2 * Real.sqrt (θ * (S.card : ℝ))) ^ 2
            < (δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2 := by
          rw [hrsq, htsq]
          have hcast : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hSpos
          have hfac : 0 < 4 * (r : ℝ) ^ 2 * (θ * (S.card : ℝ)) := by positivity
          have hmul := mul_lt_mul_of_pos_left hcoef hfac
          have heq1 : (22500 * (r : ℝ) ^ 2) * (4 * (r : ℝ) ^ 2 * (θ * (S.card : ℝ)))
              = 90000 * (r : ℝ) ^ 4 * (θ * (S.card : ℝ)) := by ring
          have heq2 : (δ ^ 2 * θ ^ 3 * (S.card : ℝ)) * (4 * (r : ℝ) ^ 2 * (θ * (S.card : ℝ)))
              = 4 * δ ^ 2 * (r : ℝ) ^ 2 * θ ^ 4 * (S.card : ℝ) ^ 2 := by ring
          linarith [hmul, heq1, heq2]
        have h0 : 0 ≤ 300 * (r : ℝ) ^ 2 * Real.sqrt (θ * (S.card : ℝ)) := by positivity
        have habs := sq_lt_sq.mp hlt
        rwa [abs_of_nonneg h0, abs_of_nonneg (le_of_lt hb)] at habs
      linarith [hstep, hkey]
    -- the exceptional event
    have hexcBJ : (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).prob
        {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} ≤ 1 / M ^ 2 := by
      have h2 : exc ≤ 1 / M ^ 2 := by rw [hMdef]; exact hexcM
      have h3 : (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).prob
          {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} ≤ exc := by
        simpa only [edgeMeasure] using hexc
      linarith [h3, h2]
    have hBJ := bj_talagrand (μ := fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le) hfull
      (fun ω : 𝓖 → Bool => -(((badSum 𝓖 ω S : ℕ) : ℝ))) M hM1 hsup
      (2 * (r : ℝ) ^ 2) (by nlinarith [hr1R]) (Nat.ceil (8 * θ * (S.card : ℝ)) + 1)
      (by omega) {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} hexcBJ
      hcert (δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) hcs
    -- the event is contained in a deviation event
    have hsub : {ω : 𝓖 → Bool | (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
          < ((badSum 𝓖 ω S : ℕ) : ℝ)}
        ⊆ {ω : 𝓖 → Bool | δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))
          ≤ |(-(((badSum 𝓖 ω S : ℕ) : ℝ)))
            - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).exp
                (fun ω => -(((badSum 𝓖 ω S : ℕ) : ℝ)))|} := by
      intro ω hω
      rw [Set.mem_ofPred_eq] at hω ⊢
      have hEX : (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).exp
          (fun ω => -(((badSum 𝓖 ω S : ℕ) : ℝ)))
          = -((edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
              (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))) := by
        have h := FinProb.exp_mul_left
          (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)) (-1)
          (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))
        simp only [edgeMeasure]
        simpa using h
      rw [hEX]
      have h1 : δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))
          ≤ ((badSum 𝓖 ω S : ℕ) : ℝ) - 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ) := by
        have h2 : (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
            = 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)
              + δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)) := by ring
        linarith [hω, h2]
      have h3 : 2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ) ≥
          (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
            (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ)) := hmean
      have h4 : 0 ≤ ((badSum 𝓖 ω S : ℕ) : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
              (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ)) := by
        have h6 : 0 ≤ δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ)) := by positivity
        linarith [h1, h3, h6]
      have h5 : -(((badSum 𝓖 ω S : ℕ) : ℝ))
          - -((edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
              (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ)))
          = -(((badSum 𝓖 ω S : ℕ) : ℝ)
              - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).exp
                  (fun ω => ((badSum 𝓖 ω S : ℕ) : ℝ))) := by ring
      rw [h5, abs_neg, abs_of_nonneg h4]
      linarith
    -- the two exponential terms
    have hpos : (θ ^ 3 * δ ^ 2 * (S.card : ℝ))
          * (16 * (2 * (r : ℝ) ^ 2) ^ 2
            * ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ))
        ≤ (δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2 * (512 * (r : ℝ) ^ 2) := by
      have hs : ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ) ≤ 9 * (θ * (S.card : ℝ)) := by
        have h1 : (Nat.ceil (8 * θ * (S.card : ℝ)) : ℝ) ≤ 8 * θ * (S.card : ℝ) + 1 :=
          le_of_lt (Nat.ceil_lt_add_one (by positivity))
        have h2 : 2 ≤ θ * (S.card : ℝ) := by
          have h3 : θ ^ 3 * δ ^ 2 ≤ θ := by
            have h4 : θ ^ 2 * δ ^ 2 ≤ 1 := by
              have h5 : θ ^ 2 ≤ 1 := by nlinarith [hθ0, hθ1]
              have h6 : δ ^ 2 ≤ 1 := by nlinarith [hδ0, hδ1]
              nlinarith [h5, h6]
            have h7 : θ ^ 3 * δ ^ 2 = θ * (θ ^ 2 * δ ^ 2) := by ring
            rw [h7]
            exact mul_le_of_le_one_right (le_of_lt hθ0) h4
          have h8 : θ ^ 3 * δ ^ 2 * (S.card : ℝ) ≤ θ * (S.card : ℝ) :=
            mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
          have h9 : (10 : ℝ) ^ 6 * (r : ℝ) ^ 2 ≤ θ * (S.card : ℝ) := le_trans hSlarge h8
          have h10 : (2 : ℝ) ≤ (10 : ℝ) ^ 6 * (r : ℝ) ^ 2 := by
            have h11 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [hr1R]
            nlinarith [h11]
          linarith
        push_cast
        linarith
      have h1 : 16 * (2 * (r : ℝ) ^ 2) ^ 2 = 64 * (r : ℝ) ^ 4 := by ring
      have h2 : (δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2
          = 4 * δ ^ 2 * (r : ℝ) ^ 2 * θ ^ 4 * (S.card : ℝ) ^ 2 := by ring
      rw [h1, h2]
      have h3 : 0 ≤ 64 * (r : ℝ) ^ 4 * (θ ^ 3 * δ ^ 2 * (S.card : ℝ)) := by
        have h4 : 0 ≤ θ ^ 3 * δ ^ 2 * (S.card : ℝ) := by positivity
        exact mul_nonneg (by positivity) h4
      have h4 := mul_le_mul_of_nonneg_left hs h3
      have h5 : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hSpos
      nlinarith [h4, h5, hθ0, hδ0, hrR, Nat.cast_nonneg (α := ℝ) S.card, sq_nonneg θ]
    have hexp : 4 * Real.exp (-(δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2
          / (16 * (2 * (r : ℝ) ^ 2) ^ 2
            * ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)))
        ≤ 4 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (512 * (r : ℝ) ^ 2)) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e1 : (-((δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2))
            * (512 * (r : ℝ) ^ 2)
          = -((δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2 * (512 * (r : ℝ) ^ 2)) := by ring
      have e2 : (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)))
            * (16 * (2 * (r : ℝ) ^ 2) ^ 2
              * ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ))
          = -((θ ^ 3 * δ ^ 2 * (S.card : ℝ))
              * (16 * (2 * (r : ℝ) ^ 2) ^ 2
                * ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ))) := by ring
      rw [e1, e2]
      linarith [hpos]
    have hstep1 : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
        {ω : 𝓖 → Bool | (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
          < ((badSum 𝓖 ω S : ℕ) : ℝ)}
        ≤ 4 * Real.exp (-(δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2
            / (16 * (2 * (r : ℝ) ^ 2) ^ 2
              * ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)))
          + 4 * (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).prob
              {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} := by
      have h1 : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
          {ω : 𝓖 → Bool | (1 + δ) * (2 * (r : ℝ) * θ ^ 2) * (S.card : ℝ)
            < ((badSum 𝓖 ω S : ℕ) : ℝ)}
          ≤ (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
              {ω : 𝓖 → Bool | δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))
                ≤ |(-(((badSum 𝓖 ω S : ℕ) : ℝ)))
                  - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).exp
                      (fun ω => -(((badSum 𝓖 ω S : ℕ) : ℝ)))|} :=
        FinProb.prob_mono _ hsub
      have h2 : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1.le).prob
              {ω : 𝓖 → Bool | δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))
                ≤ |(-(((badSum 𝓖 ω S : ℕ) : ℝ)))
                  - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).exp
                      (fun ω => -(((badSum 𝓖 ω S : ℕ) : ℝ)))|}
          ≤ 4 * Real.exp (-(δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2
              / (16 * (2 * (r : ℝ) ^ 2) ^ 2
                * ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)))
            + 4 * (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).prob
                {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} := by
        simpa only [edgeMeasure] using hBJ
      linarith [h1, h2]
    have hstep2 : 4 * Real.exp (-(δ * (2 * (r : ℝ) * θ ^ 2 * (S.card : ℝ))) ^ 2
            / (16 * (2 * (r : ℝ) ^ 2) ^ 2
              * ((Nat.ceil (8 * θ * (S.card : ℝ)) + 1 : ℕ) : ℝ)))
          + 4 * (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).prob
              {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)}
        ≤ 4 * Real.exp (-(θ ^ 3 * δ ^ 2 * (S.card : ℝ)) / (512 * (r : ℝ) ^ 2)) + 4 * exc := by
      have h2 : (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1.le)).prob
          {ω : 𝓖 → Bool | 4 * θ * (S.card : ℝ) < ((Zsum 𝓖 ω S : ℕ) : ℝ)} ≤ exc := by
        simpa only [edgeMeasure] using hexc
      linarith [hexp, h2]
    linarith [hstep1, hstep2]

end Work.Deep.Nibble
