import Submission.ZagierHoffmanProof.StepL174
import Submission.ZagierHoffmanProof.StepL147
import Submission.ZagierHoffmanProof.StepL148

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L175: ★★ the CASE-2 AMBIENT STEPS (the route-(C) measure descent)

For the CASE-2 chain `maink_case2_j` (StepL147, from `prop213_step1`, StepL44) and the
all-`q` leaf `maink_case2_qqq` (StepL148) this module establishes, for EVERY member
family, the ambient measure descent
  `ambNu Λ (Nat.card F) w m < ambNu Λ (Nat.card F) w s`   (`Λ ≥ k`),
which is what the ambient chain ports (StepL166's recipe) consume:
  • ★ type-2: the strict prefix-`k` drop forces `depth m > k`, so the DEPTH component
    decides (the prefix bound is trivial: `s` has depth `k ≤ Λ`, hence `psum s Λ = w`
    and every member has weight `w`);
  • ★★ type-3: the depth fact `k ≤ Q.dep (inr (inr i))` is PROVED here from
    `BCqIter_fiber_dep_ge` (StepL174) — the iterate's `b`-fiber has depth `≥ k−j`, so
    the prepended prefix (length `j−1`) makes the type-3 member's depth `≥ k` (the
    paper's Prop-2.13 conclusion `depth(u) ≥ depth(s)`).  At strict depth the depth
    component decides; at equal depth the chain's `InitLt` gives the `Init`-growth
    component;
  • ★ the all-`q` leaf: the same argument from its (reproved) strict prefix-`k` drop.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## The CASE-2 type-3 DEPTH fact -/

/-- ★★ Every type-3 member of the CASE-2 chain has depth at least `k` (paper
Prop 2.13: `depth(u) ≥ depth(s)`), via the iterate fiber depth bound of StepL174. -/
theorem maink_case2_j_type3_dep (k : ℕ) (s : Fin k → ℕ+) (j : ℕ) (hk1 : 1 ≤ k) (hj1 : 1 ≤ j)
    (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega)
          (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, k ≤ Q.dep (Sum.inr (Sum.inr i)) := by
  classical
  intro D Bs Q i
  have h1 := FixedOver.prependList_dep F Bs (sPrefix k s j (by omega) (by omega))
    (Sum.inr (Sum.inr i))
  have h2 : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver]
  have hlen : (sPrefix k s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length k s j (by omega) (by omega)
  have hfib : (k - j - 1) + 2 ≤ D.depB i := by
    dsimp only [D]
    exact BCqIter_fiber_dep_ge F (k - j - 1) i
  rw [h1, h2, hlen]
  have hjle : j ≤ k := by omega
  have hkj : k - j - 1 + 2 ≤ k - j + 1 := by omega
  omega

/-! ## The CASE-2 `prop213_step1` ambient steps -/

/-- ★ CASE-2 type-2 ambient step. -/
theorem maink_case2_j_type2_amb_step (w k : ℕ) (s : Fin k → ℕ+) (hw : weight k s = w)
    (j : ℕ) (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega)
          (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (Λ : ℕ), k ≤ Λ →
      ambNu Λ (Nat.card F) w (Q.c (Sum.inr (Sum.inl i))) < ambNu Λ (Nat.card F) w s := by
  classical
  intro D Bs Q i Λ hΛ
  have hT := prop213_step1 F k s j hk1 hj1 hjk hsj hqend hsleq
  obtain ⟨-, hT2, -⟩ := hT
  have hmw : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w :=
    (hT2 i).1.trans hw
  have hdrop := (hT2 i).2
  have hpsk : psum s k = w := by
    rw [psum_ge_depth s (le_refl k)]
    exact hw
  have hmd_le : Q.dep (Sum.inr (Sum.inl i)) ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : k ≤ w := by
    rw [← hw]
    exact weight_ge_depth k s
  have hle : psum (Q.c (Sum.inr (Sum.inl i))) Λ ≤ psum s Λ := by
    calc
      psum (Q.c (Sum.inr (Sum.inl i))) Λ ≤ weight (Q.dep (Sum.inr (Sum.inl i)))
          (Q.c (Sum.inr (Sum.inl i))) := psum_le_weight _ _
      _ = w := hmw
      _ = psum s Λ := by rw [psum_ge_depth s hΛ, hw]
  have hlt : k < Q.dep (Sum.inr (Sum.inl i)) := by
    by_contra hcon
    push Not at hcon
    have hpk : psum (Q.c (Sum.inr (Sum.inl i))) k =
        weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) :=
      psum_ge_depth _ hcon
    rw [hpk, hmw, hpsk] at hdrop
    exact absurd hdrop (lt_irrefl w)
  exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hlt hle

/-- ★★ CASE-2 type-3 ambient step. -/
theorem maink_case2_j_type3_amb_step (w k : ℕ) (s : Fin k → ℕ+) (hw : weight k s = w)
    (j : ℕ) (hk1 : 1 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega)
          (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB, ∀ (Λ : ℕ), k ≤ Λ →
      ambNu Λ (Nat.card F) w (Q.c (Sum.inr (Sum.inr i))) < ambNu Λ (Nat.card F) w s := by
  classical
  intro D Bs Q i Λ hΛ
  have hT := prop213_step1 F k s j hk1 hj1 hjk hsj hqend hsleq
  obtain ⟨-, -, hT3⟩ := hT
  have hmw : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w :=
    (hT3 i).1.trans hw
  have hinit := (hT3 i).2.2
  have hdep := maink_case2_j_type3_dep F k s j hk1 hj1 hjk hsj hqend hsleq i
  have hmd_le : Q.dep (Sum.inr (Sum.inr i)) ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : k ≤ w := by
    rw [← hw]
    exact weight_ge_depth k s
  have hle : psum (Q.c (Sum.inr (Sum.inr i))) Λ ≤ psum s Λ := by
    calc
      psum (Q.c (Sum.inr (Sum.inr i))) Λ ≤ weight (Q.dep (Sum.inr (Sum.inr i)))
          (Q.c (Sum.inr (Sum.inr i))) := psum_le_weight _ _
      _ = w := hmw
      _ = psum s Λ := by rw [psum_ge_depth s hΛ, hw]
  rcases lt_or_eq_of_le hdep with hlt | heq
  · exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hlt hle
  · have hdeple : Q.dep (Sum.inr (Sum.inr i)) ≤ Λ := by
      rw [← heq]
      exact hΛ
    have hpsum : psum (Q.c (Sum.inr (Sum.inr i))) Λ = psum s Λ := by
      rw [psum_ge_depth (Q.c (Sum.inr (Sum.inr i))) hdeple, hmw]
      exact ((psum_ge_depth s hΛ).trans hw).symm
    have hd : k = Q.dep (Sum.inr (Sum.inr i)) := heq
    exact ambNu_lt_of_initVal Λ (Nat.card F) w s _ hw hmw hpsum hd
      (initVal_lex_lt (Nat.card F) w s hw _ hmw hinit)


/-! ## The all-`q` CASE-2 leaf (`maink_case2_qqq`) ambient step -/

/-- ★ The `R1`-iterate's `b`-fibers drop strictly at `k` for the all-`q` input. -/
lemma maink_case2_qqq_hdrop (k : ℕ) (s : Fin k → ℕ+) (hk1 : 1 ≤ k)
    (hallq : ∀ i : Fin k, (s i : ℕ) = Nat.card F) :
    ∀ p : (RelData.BCqIter F (k - 1) (toData F (r1Rel F))).ιB,
      psum ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p) k < psum s k := by
  classical
  intro p
  have hg : ∀ j : (toData F (r1Rel F)).ιB, ∀ m : ℕ,
      psum ((toData F (r1Rel F)).cB j) m ≤
        (if m = 0 then 0 else if m ≤ 1 then m else Nat.card F) := by
    intro j m
    cases j
    change psum (pair oneExp (qMinusExp F)) m ≤
      (if m = 0 then 0 else if m ≤ 1 then m else Nat.card F)
    rcases m with _ | _ | m
    · rw [psum_zero, if_pos rfl]
    · rw [if_neg (by omega : ¬ ((1 : ℕ) = 0)), if_pos (by omega : (1 : ℕ) ≤ 1)]
      rw [show (1 : ℕ) = 0 + 1 by omega,
        psum_succ (pair oneExp (qMinusExp F)) 0, psum_zero, pad0_pair_zero]
      change (1 : ℕ) ≤ 1
      omega
    · rw [if_neg (by omega : ¬ (m + 2 = 0)), if_neg (by omega : ¬ (m + 2 ≤ 1))]
      rw [psum_ge_depth (pair oneExp (qMinusExp F)) (by omega : 2 ≤ m + 2), weight_pair]
      change 1 + (Nat.card F - 1) ≤ Nat.card F
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
  have hchain : RelData.BCqIterO F (k - 1) (toData F (r1Rel F)) =
      RelData.BCqIter F (k - 1) (toData F (r1Rel F)) :=
    RelData.BCqIterO_eq_BCqIter F (k - 1) (toData F (r1Rel F))
  have hps := RelData.psum_cB_eq_of_eq F hchain p k
  have hO := RelData.BCqIterO_cB_psum_le F (k - 1) (toData F (r1Rel F))
    (fun m => (if m = 0 then 0 else if m ≤ 1 then m else Nat.card F)) hg
    (hchain.symm ▸ p) k (by omega)
  rw [hps] at hO
  have hidx : k - (k - 1) = 1 := by omega
  rw [hidx] at hO
  have hgone : (if (1 : ℕ) = 0 then 0 else if (1 : ℕ) ≤ 1 then 1 else Nat.card F) = 1 := by
    rw [if_neg (by omega : ¬ ((1 : ℕ) = 0)), if_pos (by omega : (1 : ℕ) ≤ 1)]
  rw [hgone] at hO
  have hpsk : psum s k = k * Nat.card F := by
    change (∑ j ∈ Finset.range k, pad0 s j) = k * Nat.card F
    rw [Finset.sum_congr rfl (fun j hj => ?_)]
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]
    · rw [pad0_of_lt s (Finset.mem_range.mp hj)]
      exact hallq _
  rw [hpsk]
  have h2 : 2 ≤ Nat.card F := card_ge_two F
  have hksub : (k - 1) * Nat.card F + 1 < k * Nat.card F := by
    have hk : k = (k - 1) + 1 := by omega
    have hks : k * Nat.card F = (k - 1) * Nat.card F + Nat.card F := by
      conv_lhs => rw [hk]
      rw [Nat.succ_mul]
    rw [hks]
    omega
  omega

/-- ★ The `R1`-iterate's `b`-fibers have weight `w = k·q` for the all-`q` input. -/
lemma maink_case2_qqq_weight (w k : ℕ) (s : Fin k → ℕ+) (hw : weight k s = w) (hk1 : 1 ≤ k)
    (hallq : ∀ i : Fin k, (s i : ℕ) = Nat.card F) :
    ∀ p : (RelData.BCqIter F (k - 1) (toData F (r1Rel F))).ιB,
      weight ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).depB p)
        ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p) = w := by
  classical
  intro p
  have hbasW : ∀ j : (toData F (r1Rel F)).ιB,
      weight ((toData F (r1Rel F)).depB j) ((toData F (r1Rel F)).cB j) = Nat.card F := by
    intro j
    change weight 2 (pair oneExp (qMinusExp F)) = Nat.card F
    rw [weight_pair]
    change 1 + (Nat.card F - 1) = Nat.card F
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hO := RelData.BCqIterO_cB_weight F (k - 1) (toData F (r1Rel F)) (Nat.card F) hbasW
  have hchain : RelData.BCqIterO F (k - 1) (toData F (r1Rel F)) =
      RelData.BCqIter F (k - 1) (toData F (r1Rel F)) :=
    RelData.BCqIterO_eq_BCqIter F (k - 1) (toData F (r1Rel F))
  have hwT := RelData.cB_weight_eq_of_eq F hchain p
  rw [← hwT, hO (hchain.symm ▸ p)]
  have hkq : w = k * Nat.card F := by
    rw [← hw, weight, Finset.sum_congr rfl (fun i _ => hallq i)]
    simp
  have hqm : (k - 1) * Nat.card F + Nat.card F = k * Nat.card F := by
    have hk : k = (k - 1) + 1 := by omega
    conv_rhs => rw [hk]
    rw [Nat.succ_mul]
  rw [hkq]
  exact hqm

/-- ★ The all-`q` CASE-2 leaf ambient step. -/
theorem maink_case2_qqq_amb_step (w k : ℕ) (s : Fin k → ℕ+) (hw : weight k s = w)
    (hk1 : 1 ≤ k) (hallq : ∀ i : Fin k, (s i : ℕ) = Nat.card F) :
    ∀ p : (RelData.BCqIter F (k - 1) (toData F (r1Rel F))).ιB, ∀ (Λ : ℕ), k ≤ Λ →
      ambNu Λ (Nat.card F) w
          ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p)
        < ambNu Λ (Nat.card F) w s := by
  classical
  intro p Λ hΛ
  have hmw := maink_case2_qqq_weight F w k s hw hk1 hallq p
  have hdrop := maink_case2_qqq_hdrop F k s hk1 hallq p
  have hpsk : psum s k = w := (psum_ge_depth s (le_refl k)).trans hw
  have hmd_le : (RelData.BCqIter F (k - 1) (toData F (r1Rel F))).depB p ≤ w := by
    rw [← hmw]
    exact weight_ge_depth _ _
  have hs_le : k ≤ w := by
    rw [← hw]
    exact weight_ge_depth k s
  have hle : psum ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p) Λ ≤ psum s Λ := by
    calc
      psum ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p) Λ
          ≤ weight ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).depB p)
              ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p) := psum_le_weight _ _
      _ = w := hmw
      _ = psum s Λ := by rw [psum_ge_depth s hΛ, hw]
  have hlt : k < (RelData.BCqIter F (k - 1) (toData F (r1Rel F))).depB p := by
    by_contra hcon
    push Not at hcon
    have hpk : psum ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p) k =
        weight ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).depB p)
          ((RelData.BCqIter F (k - 1) (toData F (r1Rel F))).cB p) :=
      psum_ge_depth _ hcon
    rw [hpk, hmw, hpsk] at hdrop
    exact absurd hdrop (lt_irrefl w)
  exact ambNu_lt_of_depth_gt Λ (Nat.card F) w s _ hs_le hmd_le hlt hle

end ZagierHoffmanPositiveChar
