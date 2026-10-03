import Mathlib
import Submission.Work.Peluse.LadderP.stepBadDefs
import Submission.Work.Peluse.LadderP.cardLinEqLe
import Submission.Work.Peluse.LadderP.cardLeMulCardOfFiber
import Submission.Work.Peluse.LadderP.cardLeOfNormLt

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-! ## Elementary counting lemmas -/

/-- Reindexing a sum over `[1,M]` as a sum over `Fin M` via `k ↦ k+1`. -/
lemma sum_Icc_one_eq_sum_fin {M : ℕ} (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 M, f a) = ∑ k : Fin M, f (k + 1) := by
  have h1 : Finset.Icc 1 M = (Finset.range M).image (fun k => k + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro h
      exact ⟨a - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [h1, Finset.sum_image (fun a _ b _ h => by omega)]
  rw [Fin.sum_univ_eq_sum_range (fun k => f (k + 1)) M]

/-- Aggregation of a triple sum over a product of finite types. -/
lemma sum_sum_sum_eq_sum_product {α β γ : Type*} [Fintype α] [Fintype β] (T : Finset γ)
    (P : α → β → γ → Prop) [∀ (a : α) (b : β), DecidablePred (P a b)] :
    (∑ a : α, ∑ b : β, ∑ c ∈ T, (if P a b c then (1:ℝ) else 0))
      = ∑ t ∈ (Finset.univ : Finset α) ×ˢ ((Finset.univ : Finset β) ×ˢ T),
          (if P t.1 t.2.1 t.2.2 then (1:ℝ) else 0) := by
  trans ∑ a : α, ∑ t ∈ (Finset.univ : Finset β) ×ˢ T,
      (if P a t.1 t.2 then (1:ℝ) else 0)
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    exact (Finset.sum_product (Finset.univ : Finset β) T
      (fun x : β × γ => (if P a x.1 x.2 then (1:ℝ) else 0))).symm
  · exact (Finset.sum_product (Finset.univ : Finset α)
      ((Finset.univ : Finset β) ×ˢ T)
      (fun z : α × (β × γ) => (if P z.1 z.2.1 z.2.2 then (1:ℝ) else 0))).symm

/-- Cardinality form of the aggregation. -/
lemma card_filter_prod_eq {α β γ : Type*} [Fintype α] [Fintype β] (T : Finset γ)
    (P : α → β → γ → Prop) [∀ (a : α) (b : β), DecidablePred (P a b)] :
    ((∑ a : α, ∑ b : β, (((T.filter (fun c => P a b c)).card : ℕ) : ℝ)))
      = ((((Finset.univ : Finset α) ×ˢ ((Finset.univ : Finset β) ×ˢ T)).filter
          (fun t => P t.1 t.2.1 t.2.2)).card : ℝ) := by
  have hL : (∑ a : α, ∑ b : β, (((T.filter (fun c => P a b c)).card : ℕ) : ℝ))
      = ∑ a : α, ∑ b : β, ∑ c ∈ T, (if P a b c then (1:ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases h : P a b c <;> simp [h]
  have hR : (((((Finset.univ : Finset α) ×ˢ ((Finset.univ : Finset β) ×ˢ T)).filter
          (fun t => P t.1 t.2.1 t.2.2)).card : ℕ) : ℝ)
      = ∑ t ∈ (Finset.univ : Finset α) ×ˢ ((Finset.univ : Finset β) ×ˢ T),
          (if P t.1 t.2.1 t.2.2 then (1:ℝ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases h : P c.1 c.2.1 c.2.2 <;> simp [h]
  rw [hL, hR, sum_sum_sum_eq_sum_product T P]

/-- The number of `a ∈ [1,M₁]` at which some `|a + b i| < r`. -/
lemma card_sizeBad_le {m M₁ : ℕ} (b : Fin m → ℤ) {r : ℝ} (hr : 0 < r) :
    ((((Finset.Icc 1 M₁).filter (fun a : ℕ => ∃ i : Fin m,
        ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)).card : ℕ) : ℝ) ≤ m * (2 * r + 3) := by
  classical
  have hstep : ∀ i : Fin m, ((((Finset.Icc 1 M₁).filter
      (fun a : ℕ => ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)).card : ℕ) : ℝ) ≤ 2 * r + 3 := by
    intro i
    have himg : (((Finset.Icc 1 M₁).filter
        (fun a : ℕ => ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)).image (fun a : ℕ => (a : ℤ) + b i))
        = ((Finset.Icc 1 M₁).image (fun a : ℕ => (a : ℤ) + b i)).filter
            (fun y : ℤ => |(y : ℝ)| < r) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨a, ⟨ha, hcond⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, by simpa only [Int.cast_abs] using hcond⟩
      · rintro ⟨⟨a, ha, rfl⟩, hcond⟩
        exact ⟨a, ⟨ha, by simpa only [Int.cast_abs] using hcond⟩, rfl⟩
    have hcard : (((Finset.Icc 1 M₁).filter
        (fun a : ℕ => ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)).card : ℕ)
        = (((Finset.Icc 1 M₁).image (fun a : ℕ => (a : ℤ) + b i)).filter
            (fun y : ℤ => |(y : ℝ)| < r)).card := by
      rw [← himg, Finset.card_image_of_injective]
      intro a a' haa'
      have h : (a : ℤ) + b i = (a' : ℤ) + b i := haa'
      omega
    rw [hcard]
    exact cardLeOfNormLt hr _ (fun y hy => (Finset.mem_filter.mp hy).2)
  have hsub : (Finset.Icc 1 M₁).filter (fun a : ℕ => ∃ i : Fin m,
        ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)
      ⊆ (Finset.univ : Finset (Fin m)).biUnion (fun i : Fin m =>
          (Finset.Icc 1 M₁).filter (fun a : ℕ => ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨h1, h2⟩ := ha
    rw [Finset.mem_biUnion]
    obtain ⟨i, hi⟩ := h2
    exact ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨h1, hi⟩⟩
  calc ((((Finset.Icc 1 M₁).filter (fun a : ℕ => ∃ i : Fin m,
          ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)).card : ℕ) : ℝ)
      ≤ ((((Finset.univ : Finset (Fin m)).biUnion (fun i : Fin m =>
          (Finset.Icc 1 M₁).filter (fun a : ℕ => ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r))).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ i : Fin m, ((((Finset.Icc 1 M₁).filter
          (fun a : ℕ => ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r)).card : ℕ) : ℝ) := by
        have h := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m)))
          (t := fun i : Fin m => (Finset.Icc 1 M₁).filter (fun a : ℕ => ((|((a : ℤ) + b i)| : ℤ) : ℝ) < r))
        rw [← Nat.cast_sum]
        exact_mod_cast h
    _ ≤ ∑ _i : Fin m, (2 * r + 3) := Finset.sum_le_sum (fun i _ => hstep i)
    _ = (m : ℝ) * (2 * r + 3) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Distributing a difference inside a weighted sum. -/
lemma sum_mul_sub {j : ℕ} (w f g : Fin j → ℤ) :
    (∑ i, w i * (f i - g i)) = (∑ i, w i * f i) - ∑ i, w i * g i := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The negation of a weighted sum. -/
lemma sum_neg_mul {j : ℕ} (w f : Fin j → ℤ) :
    (∑ i, (-w i) * f i) = -(∑ i, w i * f i) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Counting the pairs `(A,B)` with a fixed value of a linear form `w·(A-B)`, where `w` has a unit
coefficient. -/
lemma pairDiff_card_le {j M₁ : ℕ} (hM₁ : 1 ≤ M₁) {w : Fin j → ℤ}
    (hw : ∃ i₀ : Fin j, w i₀ = 1 ∨ w i₀ = -1) (c : ℤ) :
    ((Finset.univ.filter (fun z : (Fin j → Fin M₁) × (Fin j → Fin M₁) =>
        (∑ i, w i * ((z.1 i : ℤ) - (z.2 i : ℤ))) = c)).card) ≤ M₁ ^ (2 * j - 1) := by
  classical
  set S : Finset ((Fin j → Fin M₁) × (Fin j → Fin M₁)) :=
    Finset.univ.filter (fun z => (∑ i, w i * ((z.1 i : ℤ) - (z.2 i : ℤ))) = c) with hS
  have hmain : S.card ≤ M₁ ^ (2 * j - 1) := by
    obtain ⟨i₀, hi₀ | hi₀⟩ := hw
    · have hfib : ∀ B : Fin j → Fin M₁, (S.filter (fun z => z.2 = B)).card ≤ M₁ ^ (j - 1) := by
        intro B
        have h1 : (S.filter (fun z => z.2 = B)).card
            ≤ (Finset.univ.filter (fun A : Fin j → Fin M₁ =>
                (∑ i, w i * (A i : ℤ)) = c + ∑ i, w i * (B i : ℤ))).card := by
          refine Finset.card_le_card_of_injOn (fun z => z.1) ?_ ?_
          · intro z hz
            rw [Finset.mem_coe, Finset.mem_filter] at hz
            obtain ⟨hzS, hzB⟩ := hz
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [hS, Finset.mem_filter] at hzS
            obtain ⟨-, hzS⟩ := hzS
            rw [hzB, sum_mul_sub] at hzS
            linarith
          · intro z hz z' hz' heq
            rw [Finset.mem_coe, Finset.mem_filter] at hz hz'
            exact Prod.ext heq (by rw [hz.2, hz'.2])
        exact le_trans h1 (cardLinEqLe w i₀ hi₀ _)
      have h2 := cardLeMulCardOfFiber (s := S) (f := Prod.snd)
        (T := (Finset.univ : Finset (Fin j → Fin M₁))) (K := M₁ ^ (j - 1))
        (fun x _ => Finset.mem_univ _) (fun B _ => hfib B)
      refine le_trans h2 ?_
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have hexp : j - 1 + j = 2 * j - 1 := by omega
      rw [← pow_add, hexp]
    · have hfib : ∀ B : Fin j → Fin M₁, (S.filter (fun z => z.2 = B)).card ≤ M₁ ^ (j - 1) := by
        intro B
        have h1 : (S.filter (fun z => z.2 = B)).card
            ≤ (Finset.univ.filter (fun A : Fin j → Fin M₁ =>
                (∑ i, (-w i) * (A i : ℤ)) = -(c + ∑ i, w i * (B i : ℤ)))).card := by
          refine Finset.card_le_card_of_injOn (fun z => z.1) ?_ ?_
          · intro z hz
            rw [Finset.mem_coe, Finset.mem_filter] at hz
            obtain ⟨hzS, hzB⟩ := hz
            rw [Finset.mem_coe, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [hS, Finset.mem_filter] at hzS
            obtain ⟨-, hzS⟩ := hzS
            rw [hzB] at hzS
            rw [sum_mul_sub] at hzS
            rw [sum_neg_mul]
            linarith
          · intro z hz z' hz' heq
            rw [Finset.mem_coe, Finset.mem_filter] at hz hz'
            exact Prod.ext heq (by rw [hz.2, hz'.2])
        exact le_trans h1 (cardLinEqLe (-w) i₀ (by simp [hi₀]) _)
      have h2 := cardLeMulCardOfFiber (s := S) (f := Prod.snd)
        (T := (Finset.univ : Finset (Fin j → Fin M₁))) (K := M₁ ^ (j - 1))
        (fun x _ => Finset.mem_univ _) (fun B _ => hfib B)
      refine le_trans h2 ?_
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have hexp : j - 1 + j = 2 * j - 1 := by omega
      rw [← pow_add, hexp]
  exact hmain

/-! ## The per-pair count -/

/-- The fibre of the map `redPair ω ω'` has at most `M₁ ^ (2j+1)` points. -/
lemma redPair_fibre_card_le {j M₁ : ℕ} (hM₁ : 1 ≤ M₁) (hj : 1 ≤ j)
    {ω ω' : Fin j → Bool} (hne : ω ≠ ω') (z : ℤ × ℤ) :
    ((Finset.univ : Finset (RedIdx j M₁)).filter
        (fun t => redPair ω ω' t = z)).card ≤ M₁ ^ (2 * j + 1) := by
  classical
  have hwne : ∃ i₀ : Fin j, (patZ ω' i₀ - patZ ω i₀) = 1 ∨ (patZ ω' i₀ - patZ ω i₀) = -1 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    funext i
    have h := hcon i
    have hval : patZ ω' i - patZ ω i = 0 ∨ patZ ω' i - patZ ω i = 1
        ∨ patZ ω' i - patZ ω i = -1 := by
      simp only [patZ]
      rcases Bool.eq_false_or_eq_true (ω i) with hω | hω <;>
        rcases Bool.eq_false_or_eq_true (ω' i) with hω' | hω' <;> simp [hω, hω']
    rcases hval with h0 | h1 | h1
    · have hz : patZ ω i = patZ ω' i := by linarith
      simp only [patZ] at hz
      by_cases hω : ω i <;> by_cases hω' : ω' i <;> simp_all
    · exact absurd h1 h.1
    · exact absurd h1 h.2
  set Sz : Finset ((Fin j → Fin M₁) × (Fin j → Fin M₁)) :=
    Finset.univ.filter (fun y => (∑ i, (patZ ω' i - patZ ω i) * ((y.1 i : ℤ) - (y.2 i : ℤ)))
      = z.2 - z.1) with hSz
  have hmem : ∀ t ∈ (Finset.univ : Finset (RedIdx j M₁)).filter (fun t => redPair ω ω' t = z),
      (t.m, t.r, t.A, t.B) ∈
        (Finset.univ : Finset (Fin M₁)) ×ˢ
          ((Finset.univ : Finset (Fin M₁)) ×ˢ Sz) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨-, htz⟩ := ht
    have h1 : stepLin ω t.A t.B t.m ((t.a : ℕ) + 1) = z.1 := by
      have hh := congrArg Prod.fst htz
      rwa [redPair] at hh
    have h2 : stepLin ω' t.A t.B t.m ((t.a : ℕ) + 1) = z.2 := by
      have hh := congrArg Prod.snd htz
      rwa [redPair] at hh
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
      ⟨Finset.mem_univ _, ?_⟩⟩
    rw [hSz, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsd := stepLin_sub ω ω' t.A t.B t.m ((t.a : ℕ) + 1)
    rw [h1, h2] at hsd
    exact hsd.symm
  have hinj : Set.InjOn (fun t : RedIdx j M₁ => (t.m, t.r, t.A, t.B))
      ↑((Finset.univ : Finset (RedIdx j M₁)).filter (fun t => redPair ω ω' t = z)) := by
    intro t ht t' ht' heq
    rw [Finset.mem_coe, Finset.mem_filter] at ht ht'
    obtain ⟨-, htz⟩ := ht
    obtain ⟨-, ht'z⟩ := ht'
    have heq' : (t.m, t.r, t.A, t.B) = (t'.m, t'.r, t'.A, t'.B) := heq
    have hm : t.m = t'.m := congrArg Prod.fst heq'
    have hr : t.r = t'.r := congrArg Prod.fst (congrArg Prod.snd heq')
    have hA : t.A = t'.A := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd heq'))
    have hB : t.B = t'.B := congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd heq'))
    have ha : t.a = t'.a := by
      have h1 : stepLin ω t.A t.B t.m ((t.a : ℕ) + 1) = z.1 := by
        have hh := congrArg Prod.fst htz
        rwa [redPair] at hh
      have h2 : stepLin ω t'.A t'.B t'.m ((t'.a : ℕ) + 1) = z.1 := by
        have hh := congrArg Prod.fst ht'z
        rwa [redPair] at hh
      have h3 := h1.trans h2.symm
      rw [hA, hB, hm] at h3
      have h4 : (t.a : ℕ) + 1 = (t'.a : ℕ) + 1 := stepLin_inj ω t'.A t'.B (t'.m : ℕ) h3
      exact Fin.ext (by omega)
    exact RedIdx.ext' hA hr hB hm ha
  have h1 := Finset.card_le_card_of_injOn (fun t : RedIdx j M₁ => (t.m, t.r, t.A, t.B)) hmem hinj
  have h2 : ((Finset.univ : Finset (Fin M₁)) ×ˢ
        ((Finset.univ : Finset (Fin M₁)) ×ˢ Sz)).card = M₁ * (M₁ * Sz.card) := by
    rw [Finset.card_product, Finset.card_product]
    simp [Fintype.card_fin]
  have h3 : Sz.card ≤ M₁ ^ (2 * j - 1) := pairDiff_card_le hM₁ hwne (z.2 - z.1)
  have h4 : M₁ * (M₁ * M₁ ^ (2 * j - 1)) = M₁ ^ (2 * j + 1) := by
    have hexp : 2 * j + 1 = 1 + 1 + (2 * j - 1) := by omega
    simp only [hexp, pow_add, pow_one]
    ring
  calc ((Finset.univ : Finset (RedIdx j M₁)).filter (fun t => redPair ω ω' t = z)).card
      ≤ ((Finset.univ : Finset (Fin M₁)) ×ˢ
          ((Finset.univ : Finset (Fin M₁)) ×ˢ Sz)).card := h1
    _ = M₁ * (M₁ * Sz.card) := h2
    _ ≤ M₁ * (M₁ * M₁ ^ (2 * j - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
    _ = M₁ ^ (2 * j + 1) := h4

/-- The per-pair bound for a pair of distinct sign patterns. -/
lemma pairAgg_card_le {j M₁ : ℕ} (hM₁ : 1 ≤ M₁) {Q : ℝ} (hQ : 1 ≤ Q)
    (ω ω' : Fin j → Bool) (hne : ω ≠ ω') :
    (((Finset.univ : Finset (Fin (j+1) → Fin M₁)) ×ˢ
        ((Finset.univ : Finset (Fin (j+1) → Fin M₁)) ×ˢ
          (Finset.univ : Finset (Fin M₁)))).filter
      (fun t => Q < ((Int.gcd (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω)
                                    (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω') : ℕ) : ℝ))).card
      ≤ M₁ ^ (2 * j + 1) * (badBox ((j + 1) * M₁) Q).card := by
  classical
  have hj : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj
    · exfalso
      apply hne
      subst hj0
      funext i
      exact i.elim0
    · exact hj
  set Agg : Finset ((Fin (j+1) → Fin M₁) × ((Fin (j+1) → Fin M₁) × Fin M₁)) :=
    (Finset.univ : Finset (Fin (j+1) → Fin M₁)) ×ˢ
      ((Finset.univ : Finset (Fin (j+1) → Fin M₁)) ×ˢ
        (Finset.univ : Finset (Fin M₁))) with hAgg
  set Red : Finset (RedIdx j M₁) :=
    Finset.univ.filter (fun t => Q < ((Int.gcd (redPair ω ω' t).1 (redPair ω ω' t).2 : ℕ) : ℝ))
    with hRed
  have hbij : (Agg.filter (fun t => Q < ((Int.gcd (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω)
                                    (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω') : ℕ) : ℝ))).card
      = Red.card := by
    refine Finset.card_bij
      (fun t _ => ⟨Fin.init t.1, t.1 (Fin.last j), Fin.init t.2.1, t.2.1 (Fin.last j), t.2.2⟩)
      ?_ ?_ ?_
    · intro t ht
      rw [Finset.mem_filter] at ht
      obtain ⟨-, hgcd⟩ := ht
      rw [hRed, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω)
          = (redPair ω ω' ⟨Fin.init t.1, t.1 (Fin.last j), Fin.init t.2.1, t.2.1 (Fin.last j),
              t.2.2⟩).1 := by
        rw [redPair]
        have hh := add_stepShift_eq_stepLin t.1 t.2.1 ω ((t.2.2 : ℕ) + 1)
        rw [headPart_eq_init] at hh
        exact hh
      have h2 : (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω')
          = (redPair ω ω' ⟨Fin.init t.1, t.1 (Fin.last j), Fin.init t.2.1, t.2.1 (Fin.last j),
              t.2.2⟩).2 := by
        rw [redPair]
        have hh := add_stepShift_eq_stepLin t.1 t.2.1 ω' ((t.2.2 : ℕ) + 1)
        rw [headPart_eq_init] at hh
        exact hh
      rw [← h1, ← h2]
      exact hgcd
    · intro t ht t' ht' heq
      have hA : Fin.init t.1 = Fin.init t'.1 := congrArg RedIdx.A heq
      have hAlast : t.1 (Fin.last j) = t'.1 (Fin.last j) := congrArg RedIdx.r heq
      have hB : Fin.init t.2.1 = Fin.init t'.2.1 := congrArg RedIdx.B heq
      have hBlast : t.2.1 (Fin.last j) = t'.2.1 (Fin.last j) := congrArg RedIdx.m heq
      have ha : t.2.2 = t'.2.2 := congrArg RedIdx.a heq
      have h1 : t.1 = t'.1 := by
        conv_lhs => rw [← Fin.snoc_init_self t.1]
        conv_rhs => rw [← Fin.snoc_init_self t'.1]
        rw [hA, hAlast]
      have h2 : t.2.1 = t'.2.1 := by
        conv_lhs => rw [← Fin.snoc_init_self t.2.1]
        conv_rhs => rw [← Fin.snoc_init_self t'.2.1]
        rw [hB, hBlast]
      exact Prod.ext h1 (Prod.ext h2 ha)
    · intro y hy
      rw [hRed, Finset.mem_filter] at hy
      refine ⟨(Fin.snoc y.A y.r, (Fin.snoc y.B y.m, y.a)), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [hAgg]
          exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
            Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
        · have h1 : (((y.a : ℕ) + 1 : ℤ) + stepShift (Fin.snoc y.A y.r) (Fin.snoc y.B y.m) ω)
              = (redPair ω ω' y).1 := by
            rw [redPair]
            exact stepShift_snoc_eq y ω
          have h2 : (((y.a : ℕ) + 1 : ℤ) + stepShift (Fin.snoc y.A y.r) (Fin.snoc y.B y.m) ω')
              = (redPair ω ω' y).2 := by
            rw [redPair]
            exact stepShift_snoc_eq y ω'
          rw [h1, h2]
          exact hy.2
      · refine RedIdx.ext' ?_ ?_ ?_ ?_ ?_ <;> simp [Fin.init_snoc, Fin.snoc_last]
  have hmem : ∀ t ∈ Red, redPair ω ω' t ∈ badBox ((j + 1) * M₁) Q := by
    intro t ht
    rw [hRed, Finset.mem_filter] at ht
    obtain ⟨-, hgcd⟩ := ht
    rw [badBox, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hgcd⟩
    · rw [Finset.mem_Icc]
      exact abs_le.mp (stepLin_abs_le ω t.A t.B (t.m : ℕ) ((t.a : ℕ) + 1) (by omega)
        (by have := t.a.isLt; omega) t.m.isLt)
    · rw [Finset.mem_Icc]
      exact abs_le.mp (stepLin_abs_le ω' t.A t.B (t.m : ℕ) ((t.a : ℕ) + 1) (by omega)
        (by have := t.a.isLt; omega) t.m.isLt)
  have hmain := cardLeMulCardOfFiber (s := Red) (f := redPair ω ω')
    (T := badBox ((j + 1) * M₁) Q) (K := M₁ ^ (2 * j + 1)) hmem
    (fun z _ => le_trans
      (Finset.card_le_card (Finset.filter_subset_filter (fun t => redPair ω ω' t = z)
        (Finset.subset_univ Red)))
      (redPair_fibre_card_le hM₁ hj hne z))
  rw [hbij]
  exact hmain

end

/-- The cardinality of a finset of naturals contained in `[1,M]`, as a sum of indicators. -/
lemma card_eq_sum_indicator {M : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 M) :
    ((S.card : ℕ) : ℝ) = ∑ a ∈ Finset.Icc 1 M, (if a ∈ S then (1:ℝ) else 0) := by
  have h1 : (Finset.Icc 1 M).filter (fun a => a ∈ S) = S := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hcard : ((S.card : ℕ) : ℝ) = (((Finset.Icc 1 M).filter (fun a => a ∈ S)).card : ℝ) := by
    rw [h1]
  rw [hcard, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases ha : a ∈ S <;> simp [ha]

/-- The cardinality of a filtered finset, as a sum of indicators. -/
lemma card_eq_sum_ite {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ) = ∑ x ∈ s, (if P x then (1:ℝ) else 0) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : P x <;> simp [h]

/-- Reindexing a filtered `Fin M`-set as a filtered `[1,M]`-set. -/
lemma card_fin_filter_eq_card_Icc_filter {M : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (Fin M)).filter (fun k : Fin M => P ((k : ℕ) + 1))).card
      = ((Finset.Icc 1 M).filter P).card := by
  have h1 : (((Finset.univ : Finset (Fin M)).filter (fun k : Fin M => P ((k : ℕ) + 1))).card : ℝ)
      = ∑ k : Fin M, (if P ((k : ℕ) + 1) then (1:ℝ) else 0) := card_eq_sum_ite _ _
  have h2 : (((Finset.Icc 1 M).filter P).card : ℝ)
      = ∑ a ∈ Finset.Icc 1 M, (if P a then (1:ℝ) else 0) := card_eq_sum_ite _ _
  have h3 : (∑ k : Fin M, (if P ((k : ℕ) + 1) then (1:ℝ) else 0))
      = ∑ a ∈ Finset.Icc 1 M, (if P a then (1:ℝ) else 0) :=
    (sum_Icc_one_eq_sum_fin (fun a => (if P a then (1:ℝ) else 0))).symm
  have h4 : (((Finset.univ : Finset (Fin M)).filter (fun k : Fin M => P ((k : ℕ) + 1))).card : ℝ)
      = (((Finset.Icc 1 M).filter P).card : ℝ) := by rw [h1, h3, ← h2]
  exact_mod_cast h4

/-- The size-failure condition of the aggregate, at a fixed pattern. -/
def aggSzPat {j M₁ : ℕ} (η : ℝ)
    (t : (Fin (j+1) → Fin M₁) × ((Fin (j+1) → Fin M₁) × Fin M₁)) (ω : Fin j → Bool) : Prop :=
  ((|(((((t.2.2 : ℕ) + 1 : ℕ)) : ℤ) + stepShift t.1 t.2.1 ω)| : ℤ) : ℝ) < η * (M₁ : ℝ)

/-- The gcd-failure condition of the aggregate, at a fixed pair of patterns. -/
def aggGdPat {j M₁ : ℕ} (Q : ℝ)
    (t : (Fin (j+1) → Fin M₁) × ((Fin (j+1) → Fin M₁) × Fin M₁))
    (ω ω' : Fin j → Bool) : Prop :=
  Q < ((Int.gcd (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω)
                (((t.2.2 : ℕ) + 1 : ℤ) + stepShift t.1 t.2.1 ω') : ℕ) : ℝ)

/-- The size-failure condition of the aggregate. -/
def aggSz {j M₁ : ℕ} (η : ℝ) (E : Fin (2^j) ≃ (Fin j → Bool))
    (t : (Fin (j+1) → Fin M₁) × ((Fin (j+1) → Fin M₁) × Fin M₁)) (i : Fin (2^j)) : Prop :=
  aggSzPat η t (E i)

/-- The gcd-failure condition of the aggregate. -/
def aggGd {j M₁ : ℕ} (Q : ℝ) (E : Fin (2^j) ≃ (Fin j → Bool))
    (t : (Fin (j+1) → Fin M₁) × ((Fin (j+1) → Fin M₁) × Fin M₁)) (i k : Fin (2^j)) : Prop :=
  aggGdPat Q t (E i) (E k)

/-- The size-failure term is bounded by the number of tuples times `2^j (2ηM₁+3)`. -/
lemma aggSz_card_le {j M₁ : ℕ} (hM₁ : 1 ≤ M₁) {η : ℝ} (hη : 0 < η)
    (E : Fin (2^j) ≃ (Fin j → Bool))
    (h h' : Fin (j+1) → Fin M₁) :
    (((Finset.univ : Finset (Fin M₁)).filter (fun k : Fin M₁ => ∃ i : Fin (2^j),
        ((|(((((k : ℕ) + 1 : ℕ)) : ℤ) + stepShiftE E h h' i)| : ℤ) : ℝ) < η * (M₁ : ℝ))).card : ℝ)
      ≤ (2:ℝ)^j * (2*(η*(M₁:ℝ)) + 3) := by
  rw [card_fin_filter_eq_card_Icc_filter (P := fun a => ∃ i : Fin (2^j),
    ((|((a : ℤ) + stepShiftE E h h' i)| : ℤ) : ℝ) < η * (M₁ : ℝ))]
  have hb := card_sizeBad_le (M₁ := M₁) (b := fun i => stepShiftE E h h' i)
    (r := η * (M₁:ℝ)) (mul_pos hη (by exact_mod_cast (by omega : 0 < M₁)))
  simpa using hb

theorem stepBadCount (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₁ : ℕ), 1 ≤ M₁ → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ (E : Fin (2^j) ≃ (Fin j → Bool)),
        ((M₁ : ℝ))⁻¹ ^ (2 * (j + 1)) *
          ∑ h : Fin (j + 1) → Fin M₁, ∑ h' : Fin (j + 1) → Fin M₁,
            ((Work.Peluse.LadderP.stepBad j M₁ η E h h').card : ℝ)
        ≤ C * (M₁ * η + Real.log ((j : ℝ) + 2)) := by
  classical
  have hlog : 0 < Real.log ((j : ℝ) + 2) := by
    apply Real.log_pos
    have h : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  set K1 : ℝ := (2:ℝ)^(j+1) + ((2:ℝ)^j)^2 * (36 * ((j:ℝ)+1)^2) with hK1
  set K0 : ℝ := 3 * (2:ℝ)^j + 1 with hK0
  refine ⟨K1 + K0 / Real.log ((j:ℝ)+2) + 1, ?_, ?_⟩
  · have h1 : 0 < K1 := by rw [hK1]; positivity
    have h0 : 0 ≤ K0 := by rw [hK0]; positivity
    have h2 : 0 ≤ K0 / Real.log ((j:ℝ)+2) := div_nonneg h0 hlog.le
    linarith
  intro M₁ hM₁ η hη0 hη1 E
  set Q : ℝ := 1 / η with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ]; exact one_le_one_div hη0 hη1
  have hQinv : (1:ℝ) / Q = η := by rw [hQ]; field_simp
  set Agg : Finset ((Fin (j+1) → Fin M₁) × ((Fin (j+1) → Fin M₁) × Fin M₁)) :=
    (Finset.univ : Finset (Fin (j+1) → Fin M₁)) ×ˢ
      ((Finset.univ : Finset (Fin (j+1) → Fin M₁)) ×ˢ
        (Finset.univ : Finset (Fin M₁))) with hAgg
  -- Step 1: the sum of cardinalities is the aggregate of the indicators
  have hstep1 : (∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
        ((stepBad j M₁ η E h h').card : ℝ))
      = ∑ t ∈ Agg, (if (t.2.2 : ℕ) + 1 ∈ stepBad j M₁ η E t.1 t.2.1 then (1:ℝ) else 0) := by
    have h1 : ∀ h h', ((stepBad j M₁ η E h h').card : ℝ)
        = ∑ k : Fin M₁, (if ((k : ℕ) + 1) ∈ stepBad j M₁ η E h h' then (1:ℝ) else 0) := by
      intro h h'
      rw [card_eq_sum_indicator (S := stepBad j M₁ η E h h')
        (Finset.filter_subset _ _ : stepBad j M₁ η E h h' ⊆ Finset.Icc 1 M₁)]
      exact sum_Icc_one_eq_sum_fin _
    rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => h1 h h')), hAgg]
    exact sum_sum_sum_eq_sum_product (Finset.univ : Finset (Fin M₁))
      (fun u u' c => ((c : ℕ) + 1) ∈ stepBad j M₁ η E u u')
  -- Step 2: split the bad tuples into the size-failures and the gcd-failures
  have hsplit : (∑ t ∈ Agg, (if (t.2.2 : ℕ) + 1 ∈ stepBad j M₁ η E t.1 t.2.1 then (1:ℝ) else 0))
      ≤ (∑ t ∈ Agg, (if ∃ i : Fin (2^j), aggSz η E t i then (1:ℝ) else 0))
        + (∑ t ∈ Agg, (if ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k then (1:ℝ) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun t _ => ?_)
    by_cases hbad : (t.2.2 : ℕ) + 1 ∈ stepBad j M₁ η E t.1 t.2.1
    · have hmem := hbad
      rw [stepBad, Finset.mem_filter] at hmem
      obtain ⟨-, hnot⟩ := hmem
      rw [not_and_or] at hnot
      rcases hnot with hnot | hnot
      · have hgood : (if ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k then (1:ℝ) else 0) = 1 := by
          rw [if_pos]
          push Not at hnot
          obtain ⟨i, k, hik, hgt⟩ := hnot
          refine ⟨i, k, hik, ?_⟩
          rw [hQ]
          simp only [aggGd, aggGdPat, stepShiftE] at hgt ⊢
          push_cast at hgt ⊢
          exact hgt
        rw [if_pos hbad, hgood]
        have h1 : (0:ℝ) ≤ (if ∃ i : Fin (2^j), aggSz η E t i then (1:ℝ) else 0) := by
          split <;> norm_num
        linarith
      · have hgood : (if ∃ i : Fin (2^j), aggSz η E t i then (1:ℝ) else 0) = 1 := by
          rw [if_pos]
          push Not at hnot
          obtain ⟨i, hlt⟩ := hnot
          refine ⟨i, ?_⟩
          simp only [aggSz, aggSzPat, stepShiftE] at hlt ⊢
          push_cast at hlt ⊢
          exact hlt
        rw [if_pos hbad, hgood]
        have h2 : (0:ℝ) ≤ (if ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k then (1:ℝ) else 0) := by
          split <;> norm_num
        linarith
    · rw [if_neg hbad]
      have h1 : 0 ≤ (if ∃ i : Fin (2^j), aggSz η E t i then (1:ℝ) else 0) := by split <;> norm_num
      have h2 : 0 ≤ (if ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k then (1:ℝ) else 0) := by
        split <;> norm_num
      linarith
  -- Step 3: bound the size-failure term
  have hsize : (∑ t ∈ Agg, (if ∃ i : Fin (2^j), aggSz η E t i then (1:ℝ) else 0))
      ≤ (M₁:ℝ)^(2*j+2) * ((2:ℝ)^(j+1) * ((M₁:ℝ)*η) + 3 * (2:ℝ)^j) := by
    have hcalc : (∑ t ∈ Agg, (if ∃ i : Fin (2^j), aggSz η E t i then (1:ℝ) else 0))
        ≤ (M₁:ℝ)^(j+1) * ((M₁:ℝ)^(j+1) * ((2:ℝ)^j * (2*(η*(M₁:ℝ)) + 3))) := by
      rw [hAgg, ← sum_sum_sum_eq_sum_product (Finset.univ : Finset (Fin M₁))
        (fun u u' c => ∃ i : Fin (2^j), aggSz η E (u, (u', c)) i)]
      calc (∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁, ∑ k : Fin M₁,
              (if ∃ i : Fin (2^j), aggSz η E (h, (h', k)) i then (1:ℝ) else 0))
          = ∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
              (((Finset.univ : Finset (Fin M₁)).filter
                (fun k => ∃ i : Fin (2^j), aggSz η E (h, (h', k)) i)).card : ℝ) := by
            refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
            exact (card_eq_sum_ite _ _).symm
        _ ≤ ∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
              ((2:ℝ)^j * (2*(η*(M₁:ℝ)) + 3)) := by
            refine Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => ?_))
            show (((Finset.univ : Finset (Fin M₁)).filter (fun k : Fin M₁ => ∃ i : Fin (2^j),
                ((|(((((k : ℕ) + 1 : ℕ)) : ℤ) + stepShiftE E h h' i)| : ℤ) : ℝ) < η * (M₁ : ℝ))).card : ℝ) ≤ _
            exact aggSz_card_le hM₁ hη0 E h h'
        _ = (M₁:ℝ)^(j+1) * ((M₁:ℝ)^(j+1) * ((2:ℝ)^j * (2*(η*(M₁:ℝ)) + 3))) := by
            have hcard : (Fintype.card (Fin (j+1) → Fin M₁) : ℝ) = (M₁:ℝ)^(j+1) := by
              rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
              push_cast
              ring
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [hcard]
    refine le_trans hcalc (le_of_eq ?_)
    have hp : (M₁:ℝ)^(j+1) * (M₁:ℝ)^(j+1) = (M₁:ℝ)^(2*j+2) := by
      rw [← pow_add]
      congr 1
      omega
    have hc : ((2:ℝ)^j * (2*(η*(M₁:ℝ)) + 3)) = (2:ℝ)^(j+1) * ((M₁:ℝ)*η) + 3 * (2:ℝ)^j := by
      rw [show (2:ℝ)^(j+1) = (2:ℝ)^j * 2 by rw [pow_succ]]
      ring
    rw [show (M₁:ℝ)^(j+1) * ((M₁:ℝ)^(j+1) * ((2:ℝ)^j * (2*(η*(M₁:ℝ)) + 3)))
        = ((M₁:ℝ)^(j+1) * (M₁:ℝ)^(j+1)) * ((2:ℝ)^j * (2*(η*(M₁:ℝ)) + 3)) from by ring,
      hp, hc]
  -- Step 4: bound the gcd-failure term
  have hgcd : (∑ t ∈ Agg, (if ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k then (1:ℝ) else 0))
      ≤ (M₁:ℝ)^(2*j+2) * (((2:ℝ)^j)^2 * ((36 * ((j:ℝ)+1)^2) * ((M₁:ℝ)*η))) := by
    have hcalc : (∑ t ∈ Agg, (if ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k then (1:ℝ) else 0))
        ≤ ((2:ℝ)^j)^2 * ((M₁:ℝ)^(2*j+1) * (36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q)) := by
      rw [← card_eq_sum_ite]
      have hsub : Agg.filter (fun t => ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k)
          ⊆ ((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter (fun p => p.1 ≠ p.2)).biUnion
              (fun p => Agg.filter (fun t => aggGdPat Q t (E p.1) (E p.2))) := by
        intro t ht
        rw [Finset.mem_filter] at ht
        obtain ⟨htA, i, k, hik, hgk⟩ := ht
        rw [Finset.mem_biUnion]
        refine ⟨(i, k), ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hik⟩
        · rw [Finset.mem_filter]
          exact ⟨htA, by simpa only [aggGd] using hgk⟩
      calc ((Agg.filter (fun t => ∃ i k : Fin (2^j), i ≠ k ∧ aggGd Q E t i k)).card : ℝ)
          ≤ ((((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter
              (fun p => p.1 ≠ p.2)).biUnion
              (fun p => Agg.filter (fun t => aggGdPat Q t (E p.1) (E p.2)))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ∑ p ∈ ((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter (fun p => p.1 ≠ p.2)),
              ((Agg.filter (fun t => aggGdPat Q t (E p.1) (E p.2))).card : ℝ) := by
            have hb := Finset.card_biUnion_le
              (s := (Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter (fun p => p.1 ≠ p.2))
              (t := fun p => Agg.filter (fun t => aggGdPat Q t (E p.1) (E p.2)))
            rw [← Nat.cast_sum]
            exact_mod_cast hb
        _ ≤ ∑ p ∈ ((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter (fun p => p.1 ≠ p.2)),
              ((M₁:ℝ)^(2*j+1) * (36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q)) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
            have hω : E p.1 ≠ E p.2 := fun h => hpne (E.injective h)
            have h1 := pairAgg_card_le (j := j) (M₁ := M₁) hM₁ hQ1 (E p.1) (E p.2) hω
            have h2 : ((Agg.filter (fun t => aggGdPat Q t (E p.1) (E p.2))).card : ℝ)
                ≤ (M₁:ℝ)^(2*j+1) * ((badBox ((j + 1) * M₁) Q).card : ℝ) := by
              exact_mod_cast h1
            refine le_trans h2 (mul_le_mul_of_nonneg_left ?_ (by positivity))
            have hD1 : 1 ≤ (j + 1) * M₁ := Nat.mul_pos (Nat.succ_pos j) (by omega : 0 < M₁)
            have h4 := badBox_card_le (D := (j + 1) * M₁) hD1 hQ1
            calc (((badBox ((j + 1) * M₁) Q).card : ℕ) : ℝ)
                ≤ 36 * (((j + 1) * M₁ : ℕ) : ℝ) ^ 2 / Q := h4
              _ = 36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q := by push_cast; ring
        _ ≤ ((2:ℝ)^j)^2 * ((M₁:ℝ)^(2*j+1) * (36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q)) := by
            have hcard : (((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter
                (fun p => p.1 ≠ p.2)).card : ℝ) ≤ ((2:ℝ)^j)^2 := by
              have hb := Finset.card_filter_le (Finset.univ : Finset (Fin (2^j) × Fin (2^j)))
                (fun p => p.1 ≠ p.2)
              have hcast : ((((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter
                  (fun p => p.1 ≠ p.2)).card : ℕ) : ℝ)
                  ≤ (Fintype.card (Fin (2^j) × Fin (2^j)) : ℝ) := by
                rw [← Finset.card_univ]
                exact_mod_cast hb
              refine le_trans hcast (le_of_eq ?_)
              rw [Fintype.card_prod, Fintype.card_fin]
              push_cast
              ring
            calc (∑ p ∈ ((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter (fun p => p.1 ≠ p.2)),
                  ((M₁:ℝ)^(2*j+1) * (36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q)))
                = (((Finset.univ : Finset (Fin (2^j) × Fin (2^j))).filter
                    (fun p => p.1 ≠ p.2)).card : ℝ) * ((M₁:ℝ)^(2*j+1) * (36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q)) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ((2:ℝ)^j)^2 * ((M₁:ℝ)^(2*j+1) * (36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q)) :=
                  mul_le_mul_of_nonneg_right hcard (by positivity)
    refine le_trans hcalc (le_of_eq ?_)
    have hQ' : (36 * (((j:ℝ)+1)*(M₁:ℝ))^2 / Q) = 36 * (((j:ℝ)+1)*(M₁:ℝ))^2 * η := by
      rw [div_eq_mul_one_div, hQinv]
    have hsq : (((j:ℝ)+1)*(M₁:ℝ))^2 = ((j:ℝ)+1)^2 * (M₁:ℝ)^2 := by ring
    have hpw : (M₁:ℝ)^(2*j+1) * (M₁:ℝ)^2 = (M₁:ℝ)^(2*j+3) := by
      conv_rhs =>
        rw [show 2*j+3 = (2*j+1)+2 by omega]
        rw [pow_add]
      try ring
    have hpw2 : (M₁:ℝ)^(2*j+3) = (M₁:ℝ)^(2*j+2) * (M₁:ℝ) := by
      conv_lhs => rw [show 2*j+3 = (2*j+2)+1 by omega]
      rw [pow_succ']
      try ring
    rw [hQ', hsq]
    calc ((2:ℝ)^j)^2 * ((M₁:ℝ)^(2*j+1) * (36 * (((j:ℝ)+1)^2 * (M₁:ℝ)^2) * η))
        = ((2:ℝ)^j)^2 * ((M₁:ℝ)^(2*j+1) * (M₁:ℝ)^2 * (36 * ((j:ℝ)+1)^2) * η) := by ring
      _ = ((2:ℝ)^j)^2 * ((M₁:ℝ)^(2*j+3) * (36 * ((j:ℝ)+1)^2) * η) := by rw [hpw]
      _ = ((2:ℝ)^j)^2 * (((M₁:ℝ)^(2*j+2) * (M₁:ℝ)) * (36 * ((j:ℝ)+1)^2) * η) := by rw [hpw2]
      _ = (M₁:ℝ)^(2*j+2) * (((2:ℝ)^j)^2 * ((36 * ((j:ℝ)+1)^2) * ((M₁:ℝ)*η))) := by ring
  -- Step 5: assemble
  have hfinal : (∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
        ((stepBad j M₁ η E h h').card : ℝ))
      ≤ (M₁:ℝ)^(2*j+2) *
          ((2:ℝ)^(j+1) * ((M₁:ℝ)*η) + 3 * (2:ℝ)^j
            + ((2:ℝ)^j)^2 * ((36 * ((j:ℝ)+1)^2) * ((M₁:ℝ)*η))) := by
    refine le_trans (le_of_eq hstep1) ?_
    refine le_trans hsplit ?_
    refine le_trans (add_le_add hsize hgcd) ?_
    rw [← mul_add]
  have hkey : ((M₁ : ℝ))⁻¹ ^ (2 * (j + 1)) *
      (∑ h : Fin (j+1) → Fin M₁, ∑ h' : Fin (j+1) → Fin M₁,
        ((stepBad j M₁ η E h h').card : ℝ))
      ≤ (K1 + K0 / Real.log ((j:ℝ)+2) + 1) * (M₁ * η + Real.log ((j:ℝ) + 2)) := by
    have hJ1 : ((M₁:ℝ)⁻¹)^(2*(j+1)) * ((M₁:ℝ)^(2*j+2)) = 1 := by
      have h1 : ((M₁:ℝ)⁻¹)^(2*(j+1)) = (((M₁:ℝ)⁻¹)^(j+1))^2 := by
        rw [show 2*(j+1) = (j+1)*2 by ring, pow_mul]
      have h2 : (M₁:ℝ)^(2*j+2) = ((M₁:ℝ)^(j+1))^2 := by
        rw [← pow_mul]
        congr 1
        ring
      have h3 : ((M₁:ℝ)⁻¹)^(j+1) * (M₁:ℝ)^(j+1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (by positivity : (M₁:ℝ) ≠ 0), one_pow]
      rw [h1, h2, ← mul_pow, h3, one_pow]
    have hbound : ((M₁:ℝ)⁻¹)^(2*(j+1)) * (∑ h : Fin (j+1) → Fin M₁,
          ∑ h' : Fin (j+1) → Fin M₁, ((stepBad j M₁ η E h h').card : ℝ))
        ≤ ((M₁:ℝ)⁻¹)^(2*(j+1)) * ((M₁:ℝ)^(2*j+2) *
          ((2:ℝ)^(j+1) * ((M₁:ℝ)*η) + 3 * (2:ℝ)^j
            + ((2:ℝ)^j)^2 * ((36 * ((j:ℝ)+1)^2) * ((M₁:ℝ)*η)))) :=
      mul_le_mul_of_nonneg_left hfinal (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg M₁)) _)
    refine le_trans hbound ?_
    rw [← mul_assoc, hJ1, one_mul]
    have hexp : (2:ℝ)^(j+1) * ((M₁:ℝ)*η) + 3 * (2:ℝ)^j
          + ((2:ℝ)^j)^2 * ((36 * ((j:ℝ)+1)^2) * ((M₁:ℝ)*η))
        = K1 * (M₁*η) + 3 * (2:ℝ)^j := by
      rw [hK1]
      ring
    rw [hexp]
    have hK1n : (0:ℝ) ≤ K1 := by rw [hK1]; positivity
    have hK0n : (0:ℝ) ≤ K0 := by rw [hK0]; positivity
    have h1 : (0:ℝ) ≤ M₁*η := mul_nonneg (Nat.cast_nonneg M₁) hη0.le
    have h2 : (0:ℝ) ≤ Real.log ((j:ℝ)+2) := hlog.le
    have h3 : (0:ℝ) ≤ K0 / Real.log ((j:ℝ)+2) := div_nonneg hK0n hlog.le
    have hexpand : (K1 + K0 / Real.log ((j:ℝ)+2) + 1) * (M₁*η + Real.log ((j:ℝ)+2))
        = K1*(M₁*η) + K1*Real.log ((j:ℝ)+2) + (K0 / Real.log ((j:ℝ)+2))*(M₁*η)
          + K0 + (M₁*η) + Real.log ((j:ℝ)+2) := by
      field_simp
      ring
    rw [hexpand]
    have h5 : (0:ℝ) ≤ K1*Real.log ((j:ℝ)+2) := mul_nonneg hK1n h2
    have h6 : (0:ℝ) ≤ (K0 / Real.log ((j:ℝ)+2))*(M₁*η) := mul_nonneg h3 h1
    have h7 : (3:ℝ) * (2:ℝ)^j + 1 ≤ K0 := by rw [hK0]
    linarith
  exact hkey

end Work.Peluse.LadderP
