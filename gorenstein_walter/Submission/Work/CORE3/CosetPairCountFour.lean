import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.Case1bFive
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.CosetPairCaseA
import Submission.Work.CORE3.CosetFourUCase

/-!
# `Work.CORE3.CosetPairCountFour`

Bender 1981 §3, pp. 223–224, (7)/(8): a coset `y Ĥ` (with `y ∉ Ĥ` an involution) containing
exactly four involutions contributes exactly six ordered pairs of distinct commuting involutions,
i.e. the commuting graph on those four involutions is a star `K_{1,3}`.

The proof splits into

* a self-contained counting lemma `pairSet_ncard_six`: for a finite group `Q`, a normal subgroup
  `N ⊴ Q` with `|Q : N| = 6` and a `4`-element set `I ⊆ Q` containing `1`, disjoint from `N`,
  closed under inversion, squaring, conjugation by its own elements and products of commuting
  elements, exactly `6` ordered pairs of distinct `x, y ∈ I` satisfy `(x⁻¹ * y)² = 1`;
* the verification that the four coset involutions produce such a set with
  `N = O₂(Ĥ) · O(Ĥ)` (index `6` by Bender's Theorem 2.6, and `I ∩ N = {1}` by Bender's (5));
* the translation to `cosetPairCount` through the dictionary of
  `Submission.Work.CORE3.Case1bEightNineDefs`.
-/

namespace Work.CORE3

open Work.GW2 Subgroup

/-! ## Arithmetic in groups of order six -/

section Six

variable {Q : Type*} [Group Q]

/-- A group of order `6` has no element of order `4`. -/
theorem orderOf_ne_four_of_card_six [Finite Q] (hQ : Nat.card Q = 6) (x : Q) :
    orderOf x ≠ 4 := by
  intro h4
  have hdvd : orderOf x ∣ Nat.card Q := orderOf_dvd_natCard x
  rw [h4, hQ] at hdvd
  omega

/-- **A group of order `6` contains no Klein four-group.**  Three distinct nonidentity
involutions `u`, `v`, `u * v` generate a subgroup of order `4`. -/
theorem not_klein_of_card_six [Finite Q] (hQ : Nat.card Q = 6) {u v : Q}
    (hu : u * u = 1) (hv : v * v = 1) (huv : (u * v) * (u * v) = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv1 : u * v ≠ 1) : False := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have huv' : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huv
  have hcomm : u * v = v * u := by rw [← huv', mul_inv_rev, hu', hv']
  have hcomm' : v * u = u * v := hcomm.symm
  have hvu : (u * v) * u = v := by
    have h := congrArg (fun z => z * v) huv
    simpa only [mul_assoc, hv, mul_one, one_mul] using h
  have huvv : (u * v) * v = u := by rw [mul_assoc, hv, mul_one]
  have huuv : u * (u * v) = v := by rw [← mul_assoc, hu, one_mul]
  have hvuv : v * (u * v) = u := by rw [← mul_assoc, hcomm', mul_assoc, hv, mul_one]
  let K : Subgroup Q :=
    { carrier := ({1, u, v, u * v} : Set Q)
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
        all_goals simp [hu, hv, huv, huuv, huvv, hvu, hvuv, hcomm']
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · exact Or.inl inv_one
        · exact Or.inr (Or.inl hu')
        · exact Or.inr (Or.inr (Or.inl hv'))
        · exact Or.inr (Or.inr (Or.inr huv')) }
  have hcardK : Nat.card ↥K = 4 := by
    change (K : Set Q).ncard = 4
    rw [Set.ncard_eq_four]
    exact ⟨1, u, v, u * v,
      fun h => hu1 h.symm,
      fun h => hv1 h.symm,
      fun h => huv1 h.symm,
      fun h => huv1 (by rw [← h, hu]),
      fun h => hv1 (mul_left_cancel (a := u) (by rw [mul_one]; exact h)).symm,
      fun h => by
        have h' := congrArg (fun z => z * v) h.symm
        exact hu1 (by simpa only [huvv, hv, mul_one] using h'),
      rfl⟩
  have hdvd : 4 ∣ Nat.card Q := by
    rw [← hcardK]
    exact ⟨K.index, (Subgroup.card_mul_index K).symm⟩
  rw [hQ] at hdvd
  omega

end Six

variable {Q : Type} [Group Q]

/-! ## The star lemma -/

/-- If `c ∈ I` is adjacent to every other element of `I` and no two distinct elements of
`I \ {c}` are adjacent, then the number of ordered pairs of distinct elements of `I` whose
"product" is an involution is `2 * |I \ {c}|`. -/
theorem pairSet_ncard_of_star [Finite Q] (I : Set Q) (c : Q) (hc : c ∈ I)
    (hcard : I.ncard = 4)
    (hcI : ∀ x ∈ I, x ≠ c → (c⁻¹ * x) * (c⁻¹ * x) = 1)
    (hrest : ∀ x ∈ I, ∀ y ∈ I, x ≠ c → y ≠ c → x ≠ y →
      (x⁻¹ * y) * (x⁻¹ * y) ≠ 1) :
    {p : Q × Q | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧
      (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}.ncard = 6 := by
  have hT : (I \ {c}).ncard = I.ncard - 1 := Set.ncard_sdiff_singleton_of_mem hc
  have hT3 : (I \ {c}).ncard = 3 := by rw [hT, hcard]
  have hsym : ∀ a b : Q, (a⁻¹ * b) * (a⁻¹ * b) = 1 ↔ (b⁻¹ * a) * (b⁻¹ * a) = 1 := by
    intro a b
    constructor <;> intro h
    · have h' := congrArg Inv.inv h
      simpa only [mul_inv_rev, inv_inv, inv_one] using h'
    · have h' := congrArg Inv.inv h
      simpa only [mul_inv_rev, inv_inv, inv_one] using h'
  have hEq : {p : Q × Q | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧
      (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}
      = (({c} : Set Q) ×ˢ (I \ {c})) ∪ ((I \ {c}) ×ˢ ({c} : Set Q)) := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hy, hne, hadj⟩
      by_cases hxc : x = c
      · exact Or.inl ⟨hxc, hy, fun hyc => hne (by rw [hxc, hyc])⟩
      · exact Or.inr ⟨⟨hx, hxc⟩, by
          by_contra hyc
          exact hrest x hx y hy hxc hyc hne hadj⟩
    · rintro (h | h)
      · obtain ⟨hxc, hy, hyc⟩ := h
        refine ⟨?_, hy, ?_, ?_⟩
        · rw [hxc]; exact hc
        · rintro h; exact hyc (h.symm.trans hxc)
        · rw [hxc]; exact hcI y hy hyc
      · obtain ⟨⟨hx, hxc⟩, hyc⟩ := h
        refine ⟨hx, ?_, ?_, ?_⟩
        · rw [hyc]; exact hc
        · rintro h; exact hxc (h.trans hyc)
        · rw [hyc]; exact (hsym x c).mpr (hcI x hx hxc)
  rw [hEq]
  have hdisj : Disjoint (({c} : Set Q) ×ˢ (I \ {c})) ((I \ {c}) ×ˢ ({c} : Set Q)) := by
    rw [Set.disjoint_left]
    rintro ⟨a, b⟩ hab hba
    simp only [Set.mem_prod, Set.mem_sdiff, Set.mem_singleton_iff] at hab hba
    exact hab.2.2 hba.2
  rw [Set.ncard_union_eq hdisj (by toFinite_tac) (by toFinite_tac), Set.ncard_prod,
    Set.ncard_prod, Set.ncard_singleton, hT3]

/-! ## Case (B): `I = {1, b₁, b₂, b₃}` with three pairwise non-commuting involutions -/

/-- The `(2,2)`-involutions case of the counting lemma (the star is centred at `1`). -/
theorem pairSet_ncard_caseB [Finite Q] (I : Set Q) (b₁ b₂ b₃ : Q)
    (hI : I = ({1, b₁, b₂, b₃} : Set Q)) (hcard : I.ncard = 4)
    (h1 : b₁ * b₁ = 1) (h2 : b₂ * b₂ = 1) (h3 : b₃ * b₃ = 1)
    (h12 : (b₁ * b₂) * (b₁ * b₂) ≠ 1) (h13 : (b₁ * b₃) * (b₁ * b₃) ≠ 1)
    (h23 : (b₂ * b₃) * (b₂ * b₃) ≠ 1) :
    {p : Q × Q | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧
      (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}.ncard = 6 := by
  have h1I : (1 : Q) ∈ I := by rw [hI]; exact Or.inl rfl
  have hmem : ∀ x : Q, x ∈ I ↔ x = 1 ∨ x = b₁ ∨ x = b₂ ∨ x = b₃ := by
    intro x; rw [hI]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  refine pairSet_ncard_of_star I 1 h1I hcard ?_ ?_
  · intro x hx hx1
    rw [inv_one, one_mul]
    rw [hmem] at hx
    rcases hx with h | h | h | h
    · exact absurd h hx1
    · rw [h]; exact h1
    · rw [h]; exact h2
    · rw [h]; exact h3
  · intro x hx y hy hx1 hy1 hne hadj
    rw [hmem] at hx hy
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy
    · exact absurd hx hx1
    · exact absurd hx hx1
    · exact absurd hx hx1
    · exact absurd hx hx1
    · exact absurd hy hy1
    · exact absurd (hx.trans hy.symm) hne
    · rw [hx, hy] at hadj
      rw [inv_eq_of_mul_eq_one_right h1] at hadj
      exact h12 hadj
    · rw [hx, hy] at hadj
      rw [inv_eq_of_mul_eq_one_right h1] at hadj
      exact h13 hadj
    · exact absurd hy hy1
    · rw [hx, hy] at hadj
      rw [inv_eq_of_mul_eq_one_right h2] at hadj
      exact h12 (by
        have h := congrArg Inv.inv hadj
        simpa only [mul_inv_rev, inv_inv, inv_one, inv_eq_of_mul_eq_one_right h1,
          inv_eq_of_mul_eq_one_right h2] using h)
    · exact absurd (hx.trans hy.symm) hne
    · rw [hx, hy] at hadj
      rw [inv_eq_of_mul_eq_one_right h2] at hadj
      exact h23 hadj
    · exact absurd hy hy1
    · rw [hx, hy] at hadj
      rw [inv_eq_of_mul_eq_one_right h3] at hadj
      exact h13 (by
        have h := congrArg Inv.inv hadj
        simpa only [mul_inv_rev, inv_inv, inv_one, inv_eq_of_mul_eq_one_right h1,
          inv_eq_of_mul_eq_one_right h3] using h)
    · rw [hx, hy] at hadj
      rw [inv_eq_of_mul_eq_one_right h3] at hadj
      exact h23 (by
        have h := congrArg Inv.inv hadj
        simpa only [mul_inv_rev, inv_inv, inv_one, inv_eq_of_mul_eq_one_right h2,
          inv_eq_of_mul_eq_one_right h3] using h)
    · exact absurd (hx.trans hy.symm) hne

/-! ## The counting lemma -/

set_option maxHeartbeats 4000000 in
theorem pairSet_ncard_six [Finite Q] (N : Subgroup Q) [N.Normal] (I : Set Q)
    (h1 : (1 : Q) ∈ I) (hcard : I.ncard = 4)
    (hinv : ∀ x ∈ I, x⁻¹ ∈ I) (hsq : ∀ x ∈ I, x * x ∈ I)
    (hconj : ∀ x ∈ I, ∀ x' ∈ I, x * x' * x ∈ I)
    (hmul : ∀ x ∈ I, ∀ x' ∈ I, x * x' = x' * x → x * x' ∈ I)
    (hN : ∀ x ∈ I, x ∈ N → x = 1)
    (hQ : Nat.card (Q ⧸ N) = 6) :
    {p : Q × Q | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧
      (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}.ncard = 6 := by
  classical
  have hI1 : (I \ {1}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem h1, hcard]
  obtain ⟨α, β, γ, hαβ, hαγ, hβγ, hset⟩ := Set.ncard_eq_three.mp hI1
  have hI : I = ({1, α, β, γ} : Set Q) := by
    have h2 : (insert (1 : Q) (I \ {1}) : Set Q) = I := by
      rw [Set.insert_sdiff_singleton, Set.insert_eq_self.mpr h1]
    rw [← h2, hset]
  have hmem : ∀ x : Q, x ∈ I ↔ x = 1 ∨ x = α ∨ x = β ∨ x = γ := by
    intro x
    rw [hI]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hαin : α ∈ I \ {1} := by rw [hset]; exact Or.inl rfl
  have hβin : β ∈ I \ {1} := by rw [hset]; exact Or.inr (Or.inl rfl)
  have hγin : γ ∈ I \ {1} := by rw [hset]; exact Or.inr (Or.inr rfl)
  have hαI : α ∈ I := hαin.1
  have hβI : β ∈ I := hβin.1
  have hγI : γ ∈ I := hγin.1
  have hα1 : α ≠ 1 := fun h => hαin.2 (Set.mem_singleton_iff.mpr h)
  have hβ1 : β ≠ 1 := fun h => hβin.2 (Set.mem_singleton_iff.mpr h)
  have hγ1 : γ ≠ 1 := fun h => hγin.2 (Set.mem_singleton_iff.mpr h)
  have hαinv : α⁻¹ = α ∨ α⁻¹ = β ∨ α⁻¹ = γ := by
    have h := hinv α hαI
    rw [hmem] at h
    rcases h with h | h | h | h
    · exact absurd (inv_eq_one.mp h) hα1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hβinv : β⁻¹ = β ∨ β⁻¹ = α ∨ β⁻¹ = γ := by
    have h := hinv β hβI
    rw [hmem] at h
    rcases h with h | h | h | h
    · exact absurd (inv_eq_one.mp h) hβ1
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hγinv : γ⁻¹ = γ ∨ γ⁻¹ = α ∨ γ⁻¹ = β := by
    have h := hinv γ hγI
    rw [hmem] at h
    rcases h with h | h | h | h
    · exact absurd (inv_eq_one.mp h) hγ1
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  -- the Klein-four argument, in the quotient `Q ⧸ N`
  have hklein : ∀ u v : Q, u ∈ I → v ∈ I → u * u = 1 → v * v = 1 →
      (u * v) * (u * v) = 1 → u ≠ 1 → v ≠ 1 → u * v ≠ 1 → False := by
    intro u v huI hvI hu hv huv hu1 hv1 huv1
    have hcomm : u * v = v * u := by
      rw [← inv_eq_of_mul_eq_one_right huv, mul_inv_rev,
        inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hv]
    have huvI : u * v ∈ I := hmul u huI v hvI hcomm
    refine not_klein_of_card_six (Q := Q ⧸ N) hQ
      (u := QuotientGroup.mk' N u) (v := QuotientGroup.mk' N v) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← map_mul, hu, map_one]
    · rw [← map_mul, hv, map_one]
    · rw [← map_mul, ← map_mul, huv, map_one]
    · intro h
      have h' := h
      rw [QuotientGroup.mk'_apply] at h'
      exact hu1 (hN u huI ((QuotientGroup.eq_one_iff u).mp h'))
    · intro h
      have h' := h
      rw [QuotientGroup.mk'_apply] at h'
      exact hv1 (hN v hvI ((QuotientGroup.eq_one_iff v).mp h'))
    · intro h
      have h' := h
      rw [QuotientGroup.mk'_apply] at h'
      exact huv1 (hN (u * v) huvI ((QuotientGroup.eq_one_iff (u * v)).mp h'))
  -- the `S₃`-type case
  have caseA : ∀ ι κ : Q, I = ({1, ι, ι⁻¹, κ} : Set Q) → ι ∈ I → κ ∈ I → ι⁻¹ ∈ I →
      ι ≠ 1 → κ ≠ 1 → ι ≠ κ → ι⁻¹ ≠ κ → ι * ι ≠ 1 → κ * κ = 1 →
      {p : Q × Q | p.1 ∈ I ∧ p.2 ∈ I ∧ p.1 ≠ p.2 ∧
        (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}.ncard = 6 := by
    intro ι κ hIκ hιI hκI hιiI hι1 hκ1 hικ hιiκ hι2 hκ2
    have hmemκ : ∀ x : Q, x ∈ I ↔ x = 1 ∨ x = ι ∨ x = ι⁻¹ ∨ x = κ := by
      intro x
      rw [hIκ]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have h2I : ι * ι ∈ I := hsq ι hιI
    -- `ι ^ 3 = 1`
    have hι3 : ι * ι * ι = 1 := by
      have h2I' : ι * ι ∈ I := h2I
      rw [hmemκ] at h2I'
      rcases h2I' with h | h | h | h
      · exact absurd h hι2
      · exact absurd (mul_right_cancel (b := ι) (by rw [h, one_mul] : ι * ι = 1 * ι)) hι1
      · rw [h, inv_mul_cancel]
      · exfalso
        have hpow : (QuotientGroup.mk' N ι) ^ 4 = 1 := by
          have hι4 : ι ^ 4 = 1 := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, h, hκ2]
          rw [← map_pow, hι4, map_one]
        have hdvd : orderOf (QuotientGroup.mk' N ι) ∣ 2 := by
          have h₁ : orderOf (QuotientGroup.mk' N ι) ∣ 4 :=
            orderOf_dvd_iff_pow_eq_one.mpr hpow
          have h₂ : orderOf (QuotientGroup.mk' N ι) ∣ Nat.card (Q ⧸ N) :=
            orderOf_dvd_natCard _
          rw [hQ] at h₂
          have h₃ : orderOf (QuotientGroup.mk' N ι) ∣ Nat.gcd 4 6 := Nat.dvd_gcd h₁ h₂
          norm_num at h₃
          exact h₃
        have hmemN : ι * ι ∈ N := by
          have h5 : (QuotientGroup.mk' N ι) ^ 2 = 1 :=
            orderOf_dvd_iff_pow_eq_one.mp hdvd
          refine (QuotientGroup.eq_one_iff (ι * ι)).mp ?_
          rw [pow_two, ← map_mul] at h5
          exact h5
        exact hκ1 (h.symm.trans (hN (ι * ι) h2I hmemN))
    have hιi : ι⁻¹ * ι⁻¹ = ι := by
      have hιinv : ι⁻¹ = ι * ι :=
        inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hι3)
      rw [hιinv, ← mul_assoc, hι3, one_mul]
    -- `κ * ι * κ = ι⁻¹`
    have hκι : κ * ι * κ = ι⁻¹ := by
      have hm : ι * κ * ι ∈ I := hconj ι hιI κ hκI
      have hm' : ι * κ * ι ∈ I := hm
      rw [hmemκ] at hm'
      rcases hm' with h | h | h | h
      · exfalso
        have h2 : ι * κ = ι⁻¹ := eq_inv_of_mul_eq_one_left h
        have h3 : κ = ι⁻¹ * (ι * κ) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        have h1 : κ = ι⁻¹ * ι⁻¹ := by rw [h3, h2]
        exact hικ (h1.trans hιi).symm
      · exfalso
        have h1 : ι * κ = 1 := mul_right_cancel (b := ι) (by rw [h, one_mul] : ι * κ * ι = 1 * ι)
        have h3 : κ = ι⁻¹ * (ι * κ) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        have h2 : κ = ι⁻¹ := by rw [h3, h1, mul_one]
        exact hιiκ h2.symm
      · exfalso
        have h2 : (ι * κ * ι) * ι⁻¹ = ι⁻¹ * ι⁻¹ := congrArg (fun z => z * ι⁻¹) h
        rw [mul_assoc, mul_inv_cancel, mul_one, hιi] at h2
        exact hκ1 (mul_left_cancel (by rw [h2, mul_one] : ι * κ = ι * 1))
      · have h2 : ι⁻¹ * (ι * κ * ι) = ι⁻¹ * κ := congrArg (fun z => ι⁻¹ * z) h
        rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at h2
        rw [h2, mul_assoc, hκ2, mul_one]
    exact CosetPairCaseA (Q := Q) I ι κ hIκ hcard hι3 hκ2 hκι
  by_cases hB : α * α = 1 ∧ β * β = 1 ∧ γ * γ = 1
  · obtain ⟨hα2, hβ2, hγ2⟩ := hB
    refine pairSet_ncard_caseB I α β γ hI hcard hα2 hβ2 hγ2 ?_ ?_ ?_
    · intro hab
      exact hklein α β hαI hβI hα2 hβ2 hab hα1 hβ1 (by
        intro h1
        exact hαβ (by rw [← inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hα2]))
    · intro hac
      exact hklein α γ hαI hγI hα2 hγ2 hac hα1 hγ1 (by
        intro h1
        exact hαγ (by rw [← inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hα2]))
    · intro hbc
      exact hklein β γ hβI hγI hβ2 hγ2 hbc hβ1 hγ1 (by
        intro h1
        exact hβγ (by rw [← inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hβ2]))
  · rcases hαinv with hα | hα | hα
    · have hα2 : α * α = 1 := by
        have h := mul_inv_cancel α
        rw [hα] at h
        exact h
      rcases hβinv with hβ | hβ | hβ
      · have hβ2 : β * β = 1 := by
          have h := mul_inv_cancel β
          rw [hβ] at h
          exact h
        have hγ2 : γ * γ = 1 := by
          rcases hγinv with h | h | h
          · have h' := mul_inv_cancel γ
            rw [h] at h'
            exact h'
          · exfalso
            exact absurd (by rw [← inv_inv γ, h, hα] : α = γ) hαγ
          · exfalso
            exact absurd (by rw [← inv_inv γ, h, hβ] : β = γ) hβγ
        exact absurd ⟨hα2, hβ2, hγ2⟩ hB
      · exfalso
        exact absurd (by rw [← inv_inv β, hβ, hα] : α = β) hαβ
      · refine caseA β α ?_ hβI hαI ?_ hβ1 hα1 (fun hh => hαβ hh.symm) ?_ ?_ hα2
        · rw [hI, ← hβ] <;> (ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
        · rw [hβ]; exact hγI
        · intro hh
          exact hαγ (by rw [← hh, hβ] : α = γ)
        · intro hh
          exact hβγ ((inv_eq_of_mul_eq_one_right hh).symm.trans hβ)
    · refine caseA α γ ?_ hαI hγI ?_ hα1 hγ1 hαγ ?_ ?_ ?_
      · rw [hI, ← hα] <;> (ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
      · rw [hα]; exact hβI
      · intro hh
        exact hβγ (hα.symm.trans hh)
      · intro hh
        exact hαβ ((inv_eq_of_mul_eq_one_right hh).symm.trans hα)
      · rcases hγinv with h | h | h
        · have h' := mul_inv_cancel γ
          rw [h] at h'
          exact h'
        · exfalso
          exact absurd (by rw [← hα, ← h, inv_inv] : β = γ) hβγ
        · exfalso
          have h2 : β⁻¹ = α := by rw [← hα, inv_inv]
          exact hαγ (by rw [← inv_inv γ, h, h2] : γ = α).symm
    · refine caseA α β ?_ hαI hβI ?_ hα1 hβ1 hαβ ?_ ?_ ?_
      · rw [hI, ← hα] <;> (ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto)
      · rw [hα]; exact hγI
      · intro hh
        exact hβγ (by rw [← hh, hα] : β = γ)
      · intro hh
        exact hαγ ((inv_eq_of_mul_eq_one_right hh).symm.trans hα)
      · rcases hβinv with h | h | h
        · have h' := mul_inv_cancel β
          rw [h] at h'
          exact h'
        · exfalso
          exact absurd (by rw [← inv_inv β, h, hα] : β = γ) hβγ
        · exfalso
          have h2 : γ⁻¹ = α := by rw [← hα, inv_inv]
          exact hαβ (by rw [← inv_inv β, h, h2] : β = α).symm

set_option maxHeartbeats 4000000 in
theorem CosetPairCountFour (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat → Work.GW2.cosetInvCount B.Hhat y = 4 →
      {p : G × G | p.1 ∈ {x : G | orderOf x = 2 ∧ y⁻¹ * x ∈ B.Hhat} ∧
        p.2 ∈ {x : G | orderOf x = 2 ∧ y⁻¹ * x ∈ B.Hhat} ∧
        p.1 ≠ p.2 ∧ p.1 * p.2 = p.2 * p.1}.ncard = 6 := by
  intro y hy2 hyH hcnt
  classical
  show Work.CORE3.cosetPairCount B.Hhat y = 6
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy2, pow_two] at h
    exact h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hI4 : (invSetIn B.Hhat y).ncard = 4 := by
    rw [ncard_invSetIn_eq_cosetInvCount B.Hhat y hyy hyH]
    exact hcnt
  -- ## Bender's Theorem 2.6
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hUeq : Work.GW2.oddCoreIn B.Hhat = B.U := h26.1
  have hSV : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) = pCoreIn 2 B.Hhat :=
    h26.2.1
  have hVH : pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hUH : B.U ≤ B.Hhat := Work.CORE2A.bSetup_U_le_Hhat B
  have hrel6 : (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := by
    rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, h6, -⟩
    · exact absurd (Work.CORE3.isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
        (Work.CORE3.not_isCyclic_of_isFourGroup' D.four)
    · exact h6
  have hVnorm : ∀ k ∈ B.Hhat, ∀ v ∈ pCoreIn 2 B.Hhat, k * v * k⁻¹ ∈ pCoreIn 2 B.Hhat := by
    intro k hk v hv
    exact ((Subgroup.mem_normalizer_iff.mp
      (Work.CORE3.le_normalizer_map_subtype B.Hhat (pCore 2 ↥B.Hhat) hk)) v).mp hv
  have hUnorm : ∀ k ∈ B.Hhat, ∀ u ∈ B.U, k * u * k⁻¹ ∈ B.U := by
    intro k hk u hu
    rw [← hUeq] at hu ⊢
    exact ((Subgroup.mem_normalizer_iff.mp
      (Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat) hk)) u).mp hu
  -- ## Bender (5): `y` inverts no nonidentity element of `O₂(Ĥ) · O(Ĥ)`
  have hNtriv : ∀ x : G, x ∈ pCoreIn 2 B.Hhat ⊔ B.U → y * x * y = x⁻¹ → x = 1 := by
    intro x hxN hxy
    by_contra hx1
    obtain ⟨v, hv, u, hu, rfl⟩ :=
      Work.CORE3.exists_mul_of_mem_sup_of_normal hVH hUH hVnorm hUnorm x hxN
    have hpow : ∀ m : ℕ, y * (v * u) ^ m * y = ((v * u)⁻¹) ^ m := by
      intro m
      have h1 := map_pow (MulAut.conj y) (v * u) m
      simp only [MulAut.conj_apply, hyinv] at h1
      rw [h1, hxy]
    have hcu : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
      rw [← hSV]; exact inf_le_right
    have hcomm : v * u = u * v := (Subgroup.mem_centralizer_iff.mp (hcu hv) u hu).symm
    have hv2 : v * v = 1 := by rw [← pow_two]; exact D.four.2 v hv
    have huv : (v * u) ^ Nat.card B.U = v := by
      rw [((commute_iff_eq v u).mpr hcomm).mul_pow (Nat.card B.U)]
      have hu1 : u ^ Nat.card B.U = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B.U hu)
      have hvu : v ^ Nat.card B.U = v := by
        obtain ⟨t, ht⟩ := Work.CORE2A.bSetup_U_odd B
        rw [ht, pow_succ, pow_mul, pow_two, hv2, one_pow, one_mul]
      rw [hvu, hu1, mul_one]
    have h2 : ((v * u)⁻¹) ^ Nat.card B.U = v := by
      have h1 : ((v * u) ^ Nat.card B.U)⁻¹ = ((v * u)⁻¹) ^ Nat.card B.U := by rw [inv_pow]
      rw [← h1, huv, inv_eq_of_mul_eq_one_right hv2]
    have hyv : y * v * y = v := by
      have h1 := hpow (Nat.card B.U)
      rw [huv, h2] at h1
      exact h1
    have hyc : y * v = v * y := by
      have h1 := congrArg (fun z => z * y) hyv
      simpa only [mul_assoc, hyy, mul_one] using h1
    have hv1 : v = 1 := by
      by_contra hvne
      exact hyH ((Work.CORE3.centralizer_le_Hhat_of_mem_pCoreIn_two
        G h B I.T.fus h26 D.four hv hvne)
        (Subgroup.mem_centralizer_iff.mpr (by
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact hyc.symm)))
    have hxU : v * u ∈ B.U := by rw [hv1, one_mul]; exact hu
    exact Work.CORE3.CosetFourUCase I h B h1 D (v * u) y hxU hx1 hy2 hyH (by rw [hyinv]; exact hxy)
  -- ## the counting lemma in the group `↥Ĥ`
  set N' : Subgroup ↥B.Hhat := (pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat with hN'def
  have hVN' : ((pCoreIn 2 B.Hhat).subgroupOf B.Hhat).Normal :=
    (Subgroup.normal_subgroupOf_iff hVH).mpr (fun h k hH hK => hVnorm k hK h hH)
  have hUN' : ((B.U).subgroupOf B.Hhat).Normal :=
    (Subgroup.normal_subgroupOf_iff hUH).mpr (fun h k hH hK => hUnorm k hK h hH)
  haveI hN'normal : N'.Normal := by
    haveI := hVN'
    haveI := hUN'
    rw [hN'def, Subgroup.subgroupOf_sup hVH hUH]
    infer_instance
  have hQ : Nat.card (↥B.Hhat ⧸ N') = 6 := by
    rw [← Subgroup.index_eq_card]
    rw [hN'def]
    exact hrel6
  set I' : Set ↥B.Hhat := {z | (z : G) ∈ invSetIn B.Hhat y} with hI'def
  have hI'card : I'.ncard = 4 := by
    have hbij : I'.ncard = (invSetIn B.Hhat y).ncard :=
      Set.ncard_congr'
        { toFun := fun z => ⟨(z.1 : G), z.2⟩
          invFun := fun w => ⟨⟨(w.1), invSetIn_subset B.Hhat y w.2⟩, w.2⟩
          left_inv := fun z => by ext; rfl
          right_inv := fun w => by ext; rfl }
    rw [hbij, hI4]
  have hI'1 : (1 : ↥B.Hhat) ∈ I' := one_mem_invSetIn (Hh := B.Hhat) hyy
  have hI'inv : ∀ z ∈ I', z⁻¹ ∈ I' := fun z hz => inv_mem_invSetIn (Hh := B.Hhat) hyy hz
  have hI'sq : ∀ z ∈ I', z * z ∈ I' := by
    intro z hz
    show ((z : G)) * ((z : G)) ∈ invSetIn B.Hhat y
    simpa only [pow_two] using pow_mem_invSetIn (Hh := B.Hhat) hyy hz 2
  have hI'conj : ∀ z ∈ I', ∀ z' ∈ I', z * z' * z ∈ I' :=
    fun z hz z' hz' => mul_mem_invSetIn_conj (Hh := B.Hhat) hyy hz hz'
  have hI'mul : ∀ z ∈ I', ∀ z' ∈ I', z * z' = z' * z → z * z' ∈ I' := by
    intro z hz z' hz' hc
    exact mul_mem_invSetIn (Hh := B.Hhat) hyy hz hz' (by simpa using congrArg Subtype.val hc)
  have hI'N : ∀ z ∈ I', z ∈ N' → z = 1 := by
    intro z hz hzN
    have hzg : (z : G) ∈ pCoreIn 2 B.Hhat ⊔ B.U := by
      rw [hN'def, Subgroup.mem_subgroupOf] at hzN
      exact hzN
    exact Subtype.ext (hNtriv (z : G) hzg (by simpa using hz.2))
  have hcombi : {p : ↥B.Hhat × ↥B.Hhat | p.1 ∈ I' ∧ p.2 ∈ I' ∧ p.1 ≠ p.2 ∧
      (p.1⁻¹ * p.2) * (p.1⁻¹ * p.2) = 1}.ncard = 6 :=
    pairSet_ncard_six N' I' hI'1 hI'card hI'inv hI'sq hI'conj hI'mul hI'N hQ
  -- ## transfer the count to `G`
  rw [cosetPairCount_eq_ncard_invSetPairSet B.Hhat y hyy hyH]
  refine (Set.ncard_congr (fun p hp => (⟨p.1, invSetIn_subset B.Hhat y hp.1⟩,
      ⟨p.2, invSetIn_subset B.Hhat y hp.2.1⟩)) ?_ ?_ ?_).trans hcombi
  · rintro ⟨a, b⟩ ⟨ha, hb, hne, hc⟩
    refine ⟨ha, hb, ?_, ?_⟩
    · rintro h
      exact hne (congrArg Subtype.val h)
    · exact Subtype.ext hc
  · rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb hab
    have h1 : a₁ = b₁ := congrArg (fun z : ↥B.Hhat => (z : G)) (congrArg Prod.fst hab)
    have h2 : a₂ = b₂ := congrArg (fun z : ↥B.Hhat => (z : G)) (congrArg Prod.snd hab)
    exact Prod.ext h1 h2
  · rintro ⟨c₁, c₂⟩ ⟨hc1, hc2, hne, hc⟩
    refine ⟨((c₁ : G), (c₂ : G)), ⟨hc1, hc2, ?_, ?_⟩, ?_⟩
    · rintro h
      exact hne (Subtype.ext h)
    · exact Subtype.ext_iff.mp hc
    · exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)

end Work.CORE3
