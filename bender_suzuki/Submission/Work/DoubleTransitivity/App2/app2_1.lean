import Mathlib
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App2.SylowAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Appendix II (1)

`app2_1`: if `P` is a `p`-subgroup of a finite group `X` acting on a finite set `E` whose set of
fixed points is exactly `{a, b}` (`a ≠ b`), then `P` is contained in a `p`-Sylow `Q` of the
stabiliser `X_a` of `a` with the same two fixed points; moreover, if `p > 2` then `Q` is a
`p`-Sylow of `X`.

The proof follows Peterfalvi's:

* take a `p`-Sylow `Q` of `D = X_a ∩ X_b` containing `P` (so `Q` still fixes exactly `a` and `b`);
* `N_H(Q)` (`H = X_a`) fixes `a` and acts on the two fixed points `{a, b}` of `Q`, so it fixes
  both, i.e. `N_H(Q) ≤ D`; as `Q` is a Sylow of `D` it is a Sylow of its normalizer in `H`, hence
  (Sylow-of-normalizer lemma) a Sylow of `H`;
* if `p > 2`: `N_X(Q)` also acts on `{a, b}`, so `[N_X(Q) : N_X(Q) ∩ H] ≤ 2` is prime to `p`, and
  `Q` is a Sylow of `N_X(Q)`, hence of `X`.
-/

namespace Work.DoubleTransitivity.App2

open Work.DoubleTransitivity

/-- **Construction step.** If a `p`-subgroup `P` of the finite group `X` has exactly the fixed
points `a ≠ b` on `E`, then there is a `p`-subgroup `Q` containing `P` and contained in
`X_a ⊓ X_b`, which is a `p`-Sylow of `X_a ⊓ X_b` (in the sense that `p` does not divide the
relative index of `Q` in `X_a ⊓ X_b`). -/
theorem exists_sylow_le_inf_stabilizers {X E : Type} [Group X] [MulAction X E] [Finite X]
    {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsPGroup p P) {a b : E} (hab : a ≠ b)
    (hfix : fixedBySub P = {a, b}) :
    ∃ Q : Subgroup X, P ≤ Q ∧ Q ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b ∧
      IsPGroup p Q ∧
      ¬ p ∣ Q.relIndex (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b) := by
  set D : Subgroup X := MulAction.stabilizer X a ⊓ MulAction.stabilizer X b with hD
  have ha : a ∈ fixedBySub P := by rw [hfix]; simp
  have hb : b ∈ fixedBySub P := by rw [hfix]; simp
  have hPS : P ≤ MulAction.stabilizer X a :=
    fun q hq => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp ha) q hq)
  have hPT : P ≤ MulAction.stabilizer X b :=
    fun q hq => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hb) q hq)
  have hPD : P ≤ D := le_inf hPS hPT
  have hP' : IsPGroup p (P.subgroupOf D) := hP.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hP'.exists_le_sylow
  refine ⟨(Q₀ : Subgroup ↥D).map D.subtype, ?_, ?_, ?_, ?_⟩
  · have h1 : (P.subgroupOf D).map D.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD]
    rw [← h1]
    exact Subgroup.map_mono hQ₀
  · exact Subgroup.map_subtype_le (Q₀ : Subgroup ↥D)
  · exact Q₀.isPGroup'.map D.subtype
  · have hQsub : ((Q₀ : Subgroup ↥D).map D.subtype).subgroupOf D = Q₀ := by
      show Subgroup.comap D.subtype ((Q₀ : Subgroup ↥D).map D.subtype) = Q₀
      exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective (Q₀ : Subgroup ↥D)
    have hrel : ((Q₀ : Subgroup ↥D).map D.subtype).relIndex D = Q₀.index := by
      show (((Q₀ : Subgroup ↥D).map D.subtype).subgroupOf D).index = Q₀.index
      rw [hQsub]
    rw [hrel]
    exact Sylow.not_dvd_index Q₀

/-- **Step towards being a Sylow of `X_a`.** If `Q` is a `p`-subgroup whose fixed points are
exactly `a ≠ b`, and `Q` is a Sylow of `X_a ⊓ X_b`, then `Q` is a Sylow of the stabiliser `X_a`.
The key point is that `N_{X_a}(Q) ≤ X_a ⊓ X_b`. -/
theorem not_dvd_index_subgroupOf_stab {X E : Type} [Group X] [MulAction X E] [Finite X]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup X} {a b : E} (hab : a ≠ b)
    (hfix : fixedBySub Q = {a, b}) (hQ : IsPGroup p Q)
    (hsyl : ¬ p ∣ Q.relIndex (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b)) :
    ¬ p ∣ (Q.subgroupOf (MulAction.stabilizer X a)).index := by
  set S : Subgroup X := MulAction.stabilizer X a with hS
  set D : Subgroup X := S ⊓ MulAction.stabilizer X b with hD
  have ha : a ∈ fixedBySub Q := by rw [hfix]; simp
  have hb : b ∈ fixedBySub Q := by rw [hfix]; simp
  have hQS : Q ≤ S := fun q hq => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp ha) q hq)
  have hQN : Q ≤ Subgroup.normalizer (Q : Set X) ⊓ S := le_inf Subgroup.le_normalizer hQS
  -- `N_H(Q) = N_X(Q) ⊓ S` is contained in `D = S ⊓ X_b`
  have hND : Subgroup.normalizer (Q : Set X) ⊓ S ≤ D := by
    refine le_inf inf_le_right ?_
    intro y hy
    have hyn : y ∈ Subgroup.normalizer (Q : Set X) := hy.1
    have hyS : y ∈ S := hy.2
    have hfixed : y • b ∈ fixedBySub Q := by
      intro m hm
      have hcomm : y⁻¹ * m * y ∈ Q := ((Subgroup.mem_normalizer_iff''.mp hyn) m).mp hm
      calc m • (y • b) = (m * y) • b := (mul_smul m y b).symm
        _ = (y * (y⁻¹ * m * y)) • b := by
              rw [show y * (y⁻¹ * m * y) = m * y from by group]
        _ = y • ((y⁻¹ * m * y) • b) := mul_smul y _ b
        _ = y • b := by rw [(mem_fixedBySub.mp hb) _ hcomm]
    rw [hfix] at hfixed
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfixed
    rcases hfixed with h | h
    · exfalso
      have hyb : y • b = y • a := by rw [h, MulAction.mem_stabilizer_iff.mp hyS]
      exact hab (MulAction.injective y hyb).symm
    · exact MulAction.mem_stabilizer_iff.mpr h
  have hrelN : ¬ p ∣ Q.relIndex (Subgroup.normalizer (Q : Set X) ⊓ S) := by
    intro h
    exact hsyl (by
      rw [← Subgroup.relIndex_mul_relIndex Q (Subgroup.normalizer (Q : Set X) ⊓ S) D hQN hND]
      exact dvd_mul_of_dvd_left h _)
  have hQpg : IsPGroup p (Q.subgroupOf S) := hQ.comap_subtype
  have hmain : ¬ p ∣ (Q.subgroupOf S).relIndex
      (Subgroup.normalizer (Q.subgroupOf S : Set ↥S)) := by
    have heq : (Q.subgroupOf S).relIndex
        (Subgroup.normalizer (Q.subgroupOf S : Set ↥S)) =
        Q.relIndex (Subgroup.normalizer (Q : Set X) ⊓ S) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hQS,
          ← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (Q : Set X)) S,
          Subgroup.relIndex_subgroupOf (H := Q) (K := Subgroup.normalizer (Q : Set X) ⊓ S)
            (L := S) inf_le_right]
    rw [heq]
    exact hrelN
  exact not_dvd_index_of_not_dvd_relIndex_normalizer hQpg hmain

/-- **The `p > 2` step.** If `Q` is a `p`-subgroup with fixed points exactly `a ≠ b` which is a
Sylow `p`-subgroup of the stabiliser `X_a`, then for `p > 2` it is a Sylow `p`-subgroup of `X`. -/
theorem not_dvd_index_of_sylow_stab {X E : Type} [Group X] [MulAction X E] [Finite X]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup X} {a b : E} (hab : a ≠ b)
    (hfix : fixedBySub Q = {a, b}) (hQS : Q ≤ MulAction.stabilizer X a) (hQ : IsPGroup p Q)
    (hsyl : ¬ p ∣ (Q.subgroupOf (MulAction.stabilizer X a)).index) (hp : 2 < p) :
    ¬ p ∣ Q.index := by
  set S : Subgroup X := MulAction.stabilizer X a with hS
  set Y : Subgroup X := Subgroup.normalizer (Q : Set X) with hY
  have hQS' : ¬ p ∣ Q.relIndex S := hsyl
  have hQY : Q ≤ Y := Subgroup.le_normalizer
  have hQYS : Q ≤ Y ⊓ S := le_inf hQY hQS
  have hle2 : (Y ⊓ S).relIndex Y ≤ 2 := by
    have h := relIndex_normalizer_inf_stabilizer_le_two (Q := Q) hab hfix
    simpa only [hY, hS] using h
  have hne0 : (Y ⊓ S).relIndex Y ≠ 0 := by
    show ((Y ⊓ S).subgroupOf Y).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hnotdvd : ¬ p ∣ (Y ⊓ S).relIndex Y := by
    intro hd
    have h2 : (Y ⊓ S).relIndex Y < p := lt_of_le_of_lt hle2 hp
    exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) hd) (not_le.mpr h2)
  have hrelYS : ¬ p ∣ Q.relIndex (Y ⊓ S) := by
    intro h
    exact hQS' (by
      rw [← Subgroup.relIndex_mul_relIndex Q (Y ⊓ S) S hQYS inf_le_right]
      exact dvd_mul_of_dvd_left h _)
  have hrel : ¬ p ∣ Q.relIndex Y := by
    intro hd
    rw [← Subgroup.relIndex_mul_relIndex Q (Y ⊓ S) Y hQYS inf_le_left] at hd
    rcases (Fact.out : p.Prime).dvd_mul.mp hd with h1 | h2
    · exact hrelYS h1
    · exact hnotdvd h2
  exact not_dvd_index_of_not_dvd_relIndex_normalizer hQ (by simpa only [hY] using hrel)

theorem app2_1 {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsPGroup p P) {a b : E} (hab : a ≠ b)
    (hfix : fixedBySub P = {a, b}) :
    ∃ Q : Subgroup X, P ≤ Q ∧ IsSylowSubgroupOf p Q (MulAction.stabilizer X a) ∧
      fixedBySub Q = {a, b} ∧ (2 < p → IsSylowSub p Q) := by
  obtain ⟨Q, hPQ, hQD, hQpg, hQSylD⟩ := exists_sylow_le_inf_stabilizers hP hab hfix
  have hQS : Q ≤ MulAction.stabilizer X a := le_trans hQD inf_le_left
  -- the two-point set is exactly the fixed point set of `X_a ⊓ X_b` as well
  have haP : a ∈ fixedBySub P := by rw [hfix]; simp
  have hbP : b ∈ fixedBySub P := by rw [hfix]; simp
  have hPS : P ≤ MulAction.stabilizer X a :=
    fun q hq => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp haP) q hq)
  have hPT : P ≤ MulAction.stabilizer X b :=
    fun q hq => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hbP) q hq)
  have hPD : P ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b := le_inf hPS hPT
  have hfixD : fixedBySub (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b) = {a, b} := by
    apply le_antisymm
    · rw [← hfix]; exact fixedBySub_antitone hPD
    · intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · intro m hm; exact MulAction.mem_stabilizer_iff.mp hm.1
      · intro m hm; exact MulAction.mem_stabilizer_iff.mp hm.2
  have hfixQ : fixedBySub Q = {a, b} := by
    apply le_antisymm
    · rw [← hfix]; exact fixedBySub_antitone hPQ
    · rw [← hfixD]; exact fixedBySub_antitone hQD
  have hSylH : ¬ p ∣ (Q.subgroupOf (MulAction.stabilizer X a)).index :=
    not_dvd_index_subgroupOf_stab hab hfixQ hQpg hQSylD
  refine ⟨Q, hPQ, ⟨hQS, hQpg, hSylH⟩, hfixQ, fun hp => ⟨hQpg, ?_⟩⟩
  exact not_dvd_index_of_sylow_stab hab hfixQ hQS hQpg hSylH hp

end Work.DoubleTransitivity.App2
