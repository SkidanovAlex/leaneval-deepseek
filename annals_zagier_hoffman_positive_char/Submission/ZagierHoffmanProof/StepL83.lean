import Submission.ZagierHoffmanProof.StepL35
import Submission.ZagierHoffmanProof.StepL32
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L83: level-3 CASE-1 per-member 2-admissibility (type-1/type-2, j=1/j=2)

SESSIONS 231/232 (probe_l3shape) proved the TYPE-3 members of the level-3 (k=3)
CASE-1 Prop-2.12 chains 2-admissible; this module adds the type-1 (a-side, i₀ ≠ u)
and type-2 (b-side inl) families at both j = 1 (s₁ = q) and j = 2 (s₁ < q).  With
the type-3 facts this closes "every level-3 CASE-1 Step-1 member is 2-admissible"
— the (β)-branch (¬2-adm members → A(2)) is vacuous in MAIN(3)'s CASE-1, so the
main3 recursion dispatches members by 3-adm (admExpT_self) / ¬3-adm (recursion).

MEMBER SHAPES (from ofBstarOver + BCqIter + the StepL27/30/31/32 value lemmas):
  front positions 0..j−1 of every member equal s₀..s_{j−1}
    (member_prefix_pos at < j−1; type1/type2_sj_at_jm1 at j−1);
  type-1 j=1: position-1 = the iterate's leading q (type1_pad0_shift +
    BCqIter_cA_pad0_front);  type-1 j=2: position-1 = s₁ (front);
  type-2 j=1: position-1 = the leading 1 of D.cB (type2_pad0_shift +
    BCqIter_head_one_data);  type-2 j=2: position-1 = s₁ (front).
  depth ≥ 3 (depA i₀ ≥ 1 with k=3; j + depB ≥ 3) ⟹ the depth-2 (·, q) cond2₂
  witness is impossible.  cond1₂: positions 0,1 ≤ q (front ≤ q by s 2-adm; the
  q/1 entries).  The wrapper twoAdm_of_pad0_le turns (depth ≥ 3, pad0 0/1 ≤ q)
  into kAdmissible-2.

These are ∃-style (rcase prop212_step1 internally, mirroring level3_j1/j2_type3_
twoAdm of probe_l3shape); main3's splice will restate them in the "_of" form
(taking the R0/u/hbhd package data as input), per the StepL71/72 pattern.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]



/-- cond1₂ + depth ≥ 3 ⟹ 2-admissible (generic wrapper). -/
lemma twoAdm_of_pad0_le {r : ℕ} (q : ℕ) (t : Fin r → ℕ+) (hr : 3 ≤ r)
    (h0 : pad0 t 0 ≤ q) (h1 : pad0 t 1 ≤ q) : kAdmissible q t 2 := by
  constructor
  · intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x; exact h0
    · subst x; exact h1
  · intro hform
    rcases hform with ⟨hr1, hdep2, hall, hlast⟩
    omega

/-- Type-1 members of the (k=3, j=1) chain are 2-adm (natural session-231 shape). -/
theorem level3_j1_type1_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) = Nat.card F) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 1 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
          (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i₀ : R0.ιA, i₀ ≠ u →
        kAdmissible (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 2 := by
  classical
  have hmid : ∀ i : Fin r, (1 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 2 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    have hiv : (i : ℕ) = 1 := by omega
    have hidx : i = ⟨1, (by omega : 1 < r)⟩ := by
      apply Fin.ext
      exact hiv
    rw [hidx]
    exact hs1q
  have hsleq : ∀ x : ℕ, x < 2 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      rw [hp]
      omega
    · subst x
      have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      rw [hp]
      rw [hs1q]
  rcases prop212_step1 F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 3 - 1) hbig hs0q hmid hsleq with
    ⟨R0, u, hbhd, ha, hdep0, hc0, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, u, hbhd, ?_⟩
  intro D Bs Q i₀ hi
  -- depth ≥ 3
  have hdepge : 3 ≤ Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) := by
    have hQd : Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) =
        D.depA (RelData.iterIdx F 1 (toData F R0) i₀) + 1 + 0 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 1 (by omega) (by omega))
        (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))
      have h2 : Bs.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) =
          D.depA (RelData.iterIdx F 1 (toData F R0) i₀) + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 1 (by omega) (by omega)).length = 0 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hd := RelData.BCqIter_depA_at F 1 (toData F R0) i₀
    rw [hd]
    have hda : 0 < (toData F R0).depA i₀ := by
      change 0 < R0.depA i₀
      exact R0.hdepA i₀
    omega
  refine twoAdm_of_pad0_le (Nat.card F)
    (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) hdepge ?_ ?_
  · -- entry-0 = s⟨0⟩ ≤ q
    have he0 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 0 =
        (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) := by omega
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) hQ0]
      have hv := type1_sj_at_jm1 F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
        (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd
        (RelData.iterIdx F 1 (toData F R0) i₀)
        (show 1 - 1 < Q.dep (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀)) by simpa using hQ0)
      simpa using hv
    rw [he0]
    omega
  · -- entry-1 = q ≤ q
    have he1 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 1 =
        Nat.card F := by
      have hsh' : pad0 (Q.c (Sum.inl (RelData.iterIdx F 1 (toData F R0) i₀))) 1 =
          pad0 ((RelData.BCqIter F 1 (toData F R0)).cA
            (RelData.iterIdx F 1 (toData F R0) i₀)) 0 := by
        simpa using (type1_pad0_shift F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
          (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd
          (RelData.iterIdx F 1 (toData F R0) i₀) 1 (by omega))
      rw [hsh']
      have hf := BCqIter_cA_pad0_front F 1 R0 i₀ 0 (by omega)
      rw [hf]
    rw [he1]


/-- Type-2 members of the (k=3, j=1) chain are 2-adm. -/
theorem level3_j1_type2_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0q : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) = Nat.card F) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 1 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 R0 e)
          (RelData.iterate_merge_hv F 1 R0 (s ⟨0, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 1 (by omega) (by omega))
      ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 2 := by
  classical
  have hmid : ∀ i : Fin r, (1 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 2 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    have hiv : (i : ℕ) = 1 := by omega
    have hidx : i = ⟨1, (by omega : 1 < r)⟩ := by
      apply Fin.ext
      exact hiv
    rw [hidx]
    exact hs1q
  have hsleq : ∀ x : ℕ, x < 2 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      rw [hp]
      omega
    · subst x
      have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      rw [hp]
      rw [hs1q]
  rcases prop212_step1 F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 3 - 1) hbig hs0q hmid hsleq with
    ⟨R0, u, hbhd, ha, hdep0, hc0, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, u, hbhd, ?_⟩
  intro D Bs Q i
  have hdepge : 3 ≤ Q.dep (Sum.inr (Sum.inl i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 + 0 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 1 (by omega) (by omega))
        (Sum.inr (Sum.inl i))
      have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 1 (by omega) (by omega)).length = 0 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  refine twoAdm_of_pad0_le (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) hdepge ?_ ?_
  · have he0 : pad0 (Q.c (Sum.inr (Sum.inl i))) 0 = (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hQ0]
      have hv := type2_sj_at_jm1 F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
        (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd i
        (show 1 - 1 < Q.dep (Sum.inr (Sum.inl i)) by simpa using hQ0)
      simpa using hv
    rw [he0]
    omega
  · have he1 : pad0 (Q.c (Sum.inr (Sum.inl i))) 1 = 1 := by
      have hsh' : pad0 (Q.c (Sum.inr (Sum.inl i))) 1 = pad0 (D.cB i) 0 := by
        simpa using (type2_pad0_shift F r s 3 1 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 1)
          (by omega : 1 ≤ 3 - 1) hbig hs0q R0 hbhd i 0)
      rw [hsh']
      have hh := BCqIter_head_one_data F 1 R0 hbhd i
      rw [pad0_of_lt (D.cB i) (D.hdepB i)]
      exact hh
    rw [he1]
    have hq1 : 1 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    exact hq1


/-- Type-1 members of the (k=3, j=2) chain are 2-adm. -/
theorem level3_j2_type1_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0 : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
      ∀ i₀ : R0.ιA, i₀ ≠ u →
        kAdmissible (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 2 := by
  classical
  have hmid : ∀ i : Fin r, (2 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 2 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    omega
  have hsleq : ∀ x : ℕ, x < 2 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      rw [hp]
      exact hs0
    · subst x
      have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      rw [hp]
      omega
  rcases prop212_step1 F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 3 - 1) hbig hs1q hmid hsleq with
    ⟨R0, u, hbhd, ha, hdep0, hc0, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, u, hbhd, ?_⟩
  intro D Bs Q i₀ hi
  have hdepge : 3 ≤ Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) := by
    have hQd : Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) =
        D.depA (RelData.iterIdx F 0 (toData F R0) i₀) + 1 + 1 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 2 (by omega) (by omega))
        (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))
      have h2 : Bs.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) =
          D.depA (RelData.iterIdx F 0 (toData F R0) i₀) + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 2 (by omega) (by omega)).length = 1 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hd := RelData.BCqIter_depA_at F 0 (toData F R0) i₀
    rw [hd]
    have hda : 0 < (toData F R0).depA i₀ := by
      change 0 < R0.depA i₀
      exact R0.hdepA i₀
    omega
  refine twoAdm_of_pad0_le (Nat.card F)
    (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hdepge ?_ ?_
  · have he0 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 0 =
      (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) := by omega
      have hv := member_prefix_pos F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd
        (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) 0 (by omega) hQ0
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hQ0]
      simpa using (congrArg (fun t : ℕ+ => (t : ℕ)) hv)
    rw [he0]
    exact hs0
  · have he1 : pad0 (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) 1 =
      (s ⟨1, by omega⟩ : ℕ) := by
      have hQ1 : 1 < Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) := by omega
      have hv := type1_sj_at_jm1 F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd
        (RelData.iterIdx F 0 (toData F R0) i₀) hQ1
      rw [pad0_of_lt (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀))) hQ1]
      simpa using hv
    rw [he1]
    omega

/-- Type-2 members of the (k=3, j=2) chain are 2-adm. -/
theorem level3_j2_type2_twoAdm (r : ℕ) (s : Fin r → ℕ+) (hr3 : 3 ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0 : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA)
      (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1),
      let D := RelData.BCqIter F 0 (toData F R0)
      let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
          (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
      let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
      ∀ i : D.ιB, kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 2 := by
  classical
  have hmid : ∀ i : Fin r, (2 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 2 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    omega
  have hsleq : ∀ x : ℕ, x < 2 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      rw [hp]
      exact hs0
    · subst x
      have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      rw [hp]
      omega
  rcases prop212_step1 F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 3 - 1) hbig hs1q hmid hsleq with
    ⟨R0, u, hbhd, ha, hdep0, hc0, hrel, ht1, ht2, ht3⟩
  refine ⟨R0, u, hbhd, ?_⟩
  intro D Bs Q i
  have hdepge : 3 ≤ Q.dep (Sum.inr (Sum.inl i)) := by
    have hQd : Q.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 + 1 := by
      have h1 := FixedOver.prependList_dep F Bs (sPrefix r s 2 (by omega) (by omega))
        (Sum.inr (Sum.inl i))
      have h2 : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
        dsimp [Bs, ofBstarOver]
      have hlen : (sPrefix r s 2 (by omega) (by omega)).length = 1 := by
        rw [sPrefix_length]
      rw [h1, h2, hlen]
    rw [hQd]
    have hb := D.hB2 i
    omega
  refine twoAdm_of_pad0_le (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) hdepge ?_ ?_
  · have he0 : pad0 (Q.c (Sum.inr (Sum.inl i))) 0 = (s ⟨0, by omega⟩ : ℕ) := by
      have hQ0 : 0 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      have hv := member_prefix_pos F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd
        (Sum.inr (Sum.inl i)) 0 (by omega) hQ0
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hQ0]
      simpa using (congrArg (fun t : ℕ+ => (t : ℕ)) hv)
    rw [he0]
    exact hs0
  · have he1 : pad0 (Q.c (Sum.inr (Sum.inl i))) 1 = (s ⟨1, by omega⟩ : ℕ) := by
      have hQ1 : 1 < Q.dep (Sum.inr (Sum.inl i)) := by omega
      have hv := type2_sj_at_jm1 F r s 3 2 (by omega : 1 ≤ 3) hr3 (by omega : 1 ≤ 2)
        (by omega : 2 ≤ 3 - 1) hbig hs1q R0 hbhd i hQ1
      rw [pad0_of_lt (Q.c (Sum.inr (Sum.inl i))) hQ1]
      simpa using hv
    rw [he1]
    omega

end ZagierHoffmanPositiveChar
