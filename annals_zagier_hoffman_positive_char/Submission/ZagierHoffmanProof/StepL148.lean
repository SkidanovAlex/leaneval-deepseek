import Submission.ZagierHoffmanProof.StepL147
import Submission.ZagierHoffmanProof.StepL31
set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L148: ★★ `maink_case2_qqq` — the all-q CASE-2 leaf at symbolic `k`
(SESSION 260) — the second half of StepL115 obligation (5)

The depth-`k` all-q tuple `s = (q,…,q)` (weight `k·q`, in-domain at every level)
expands at level `k` in ORDERED form, via the `R1`-chain
`E := BCqIter F (k−1) (toData r1Rel)` (whose leading `a`-tuple IS `(q,…,q)`, by
`BCqIter_cA_at` + `value_qsTuple`).

  • `RelData.sum_ιA_iterIdx` — the general reindexing of an `ιA`-sum along the
    iterate (`iterIdx` is a bijection, `Eq.mpr`-roundtrip);
  • `BCqIter_r1_cA_value` — every entry of the `R1`-iterate's leading `a`-tuple is
    `q`;
  • ★ `BCqIter_r1_cA_zeta` — `ζ_A` of that leading tuple is `ζ_A s` for every
    all-q `s` (`ζ_A_eq_of_reindex` + `hallq`);
  • the chain ζ-identity (`BCqIter_zeta_zero` + `toBinaryRel_zeta_eq`) collapses
    the `a`-side to `ζ_A s`, giving `ζ_A s + Σ_p aB_p ζ_A(cB_p) = 0`;
  • per-member: weight `= k·q = w` (`BCqIterO_cB_weight`, base weight `q`), the
    STRICT prefix-`k` drop (`BCqIterO_cB_psum_le` with the base's own prefix bound
    ⇒ `≤ (k−1)q + 1 < k·q`), order by weight saturation;
  • single-family fold + `admExpT_combine`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ Reindex an `ιA`-sum along the iterate: `iterIdx` is a bijection
(`Eq.mpr`-roundtrip). -/
lemma RelData.sum_iterIdx (n : ℕ) (D : RelData F) {M : Type*} [AddCommMonoid M]
    (g : (RelData.BCqIter F n D).ιA → M) :
    (∑ i : D.ιA, g (RelData.iterIdx F n D i)) =
      ∑ i : (RelData.BCqIter F n D).ιA, g i := by
  classical
  refine Fintype.sum_bijective (RelData.iterIdx F n D) ?_
    (fun i : D.ιA => g (RelData.iterIdx F n D i)) g ?_
  · constructor
    · intro i j hij
      have h := congrArg (Eq.mpr (RelData.BCqIter_ιA F n D).symm) hij
      dsimp only [RelData.iterIdx] at h
      rwa [eq_mpr_symm_id (RelData.BCqIter_ιA F n D).symm i,
        eq_mpr_symm_id (RelData.BCqIter_ιA F n D).symm j] at h
    · intro i
      exact ⟨Eq.mpr (RelData.BCqIter_ιA F n D).symm i, RelData.BCqIter_index_cast F n D i⟩
  · intro x
    rfl

/-- Every entry of the `R1`-iterate's leading `a`-tuple is `q`. -/
lemma BCqIter_r1_cA_value (n : ℕ)
    (x : Fin ((toData F (r1Rel F)).depA PUnit.unit + n)) :
    (((RelData.BCqIter F n (toData F (r1Rel F))).cA
      (RelData.iterIdx F n (toData F (r1Rel F)) PUnit.unit)
      (Fin.cast (RelData.BCqIter_depA_at F n (toData F (r1Rel F)) PUnit.unit).symm x) : ℕ+) =
      qExp F) := by
  classical
  rw [RelData.BCqIter_cA_value F n (toData F (r1Rel F)) PUnit.unit x]
  by_cases hx : (x : ℕ) < n
  · simp [hx]
  · simp only [hx, dif_neg, not_false_iff]
    rfl

/-- ★ `ζ_A` of the `R1`-iterate's leading `a`-tuple is `ζ_A s` for every all-q `s`. -/
lemma BCqIter_r1_cA_zeta (n : ℕ) (m : ℕ)
    (hm : (toData F (r1Rel F)).depA PUnit.unit + n = m)
    (s : Fin m → ℕ+) (hallq : ∀ i : Fin m, (s i : ℕ) = Nat.card F) :
    ζ_A F ((RelData.BCqIter F n (toData F (r1Rel F))).cA
      (RelData.iterIdx F n (toData F (r1Rel F)) PUnit.unit)) = ζ_A F s := by
  classical
  have hcast := RelData.BCqIter_depA_at F n (toData F (r1Rel F)) PUnit.unit
  have htot : (RelData.BCqIter F n (toData F (r1Rel F))).depA
      (RelData.iterIdx F n (toData F (r1Rel F)) PUnit.unit) = m := hcast.trans hm
  refine ζ_A_eq_of_reindex F htot _ s ?_
  intro i
  have hii : Fin.cast hcast.symm (Fin.cast hcast i) = i := by
    apply Fin.ext
    simp
  rw [← hii, BCqIter_r1_cA_value F n (Fin.cast hcast i)]
  exact (Subtype.ext (hallq ⟨(i : ℕ), by simpa [htot] using i.isLt⟩)).symm

/-- ★★ The all-q CASE-2 leaf at symbolic `k`: the depth-`k` tuple `(q,…,q)`
expands at level `k` via the `R1`-chain. -/
theorem maink_case2_qqq (w : ℕ) (k : ℕ) (s : Fin k → ℕ+) (hw : weight k s = w)
    (hk1 : 1 ≤ k) (hk2 : 2 ≤ k)
    (hallq : ∀ i : Fin k, (s i : ℕ) = Nat.card F)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      MainkStep3 k (Nat.card F) w s m → ¬ kAdmissible (Nat.card F) m k → AdmExpT F w k m) :
    AdmExpT F w k s := by
  classical
  let D := toData F (r1Rel F)
  let E := RelData.BCqIter F (k - 1) D
  let u : D.ιA := PUnit.unit
  let uE : E.ιA := RelData.iterIdx F (k - 1) D u
  have hdep1 : (toData F (r1Rel F)).depA PUnit.unit = 1 := rfl
  have hEqdep : E.depA uE = k := by
    dsimp [uE, u, E, D]
    rw [RelData.BCqIter_depA_at F (k - 1) (toData F (r1Rel F)) PUnit.unit, hdep1]
    omega
  -- (1) the ζ-identity with the collapsed a-side
  have haz : ζ_A F (E.cA uE) = ζ_A F s := by
    dsimp [uE, u, E, D]
    exact BCqIter_r1_cA_zeta F (k - 1) k (by rw [hdep1]; omega) s hallq
  have hz0 : (∑ i : E.ιA, (((E.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA i))) +
      (∑ p : E.ιB, (((E.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cB p))) = 0 := by
    have hz := BCqIter_zeta_zero F (k - 1) (r1Rel F)
    rw [toBinaryRel_zeta_eq F E (BCqIter_valid F (k - 1) (r1Rel F))] at hz
    simpa [E, D] using hz
  have ha : (∑ i : E.ιA, (((E.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA i)))
      = ζ_A F s := by
    rw [← RelData.sum_iterIdx F (k - 1) D
      (fun i => (((E.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA i)))]
    have hcollapse : (∑ i : D.ιA, (((E.aA (RelData.iterIdx F (k - 1) D i) : RatFunc F) :
            RatFunc.CompletionAtInfty F) * ζ_A F (E.cA (RelData.iterIdx F (k - 1) D i))))
        = (((E.aA uE : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cA uE)) := by
      haveI : Subsingleton D.ιA := ⟨fun a b => by cases a; cases b; rfl⟩
      have h := Fintype.sum_subsingleton (f := fun i : D.ιA =>
        (((E.aA (RelData.iterIdx F (k - 1) D i) : RatFunc F) :
            RatFunc.CompletionAtInfty F) * ζ_A F (E.cA (RelData.iterIdx F (k - 1) D i)))) u
      simpa [uE] using h
    rw [hcollapse]
    have ha1 : (E.aA uE : RatFunc F) = 1 := by
      dsimp [uE, u]
      rw [RelData.BCqIter_aA_at F (k - 1) D PUnit.unit]
      rfl
    rw [ha1, haz]
    simp [completion_coe_one]
  have hrel : ζ_A F s +
      (∑ p : E.ιB, (((E.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cB p))) = 0 := by
    rw [← ha]
    simpa using hz0
  -- (2) the member facts
  have hbasW : ∀ j : D.ιB, weight (D.depB j) (D.cB j) = Nat.card F := by
    intro j
    change weight 2 (pair oneExp (qMinusExp F)) = Nat.card F
    rw [weight_pair]
    change 1 + (Nat.card F - 1) = Nat.card F
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hwt : ∀ p : E.ιB, weight (E.depB p) (E.cB p) = w := by
    intro p
    have hO := RelData.BCqIterO_cB_weight F (k - 1) D (Nat.card F) hbasW
    have hchain : RelData.BCqIterO F (k - 1) D = E := RelData.BCqIterO_eq_BCqIter F (k - 1) D
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
  have hg : ∀ j : D.ιB, ∀ m : ℕ,
      psum (D.cB j) m ≤ (if m = 0 then 0 else if m ≤ 1 then m else Nat.card F) := by
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
  have hdrop : ∀ p : E.ιB, psum (E.cB p) k < psum s k := by
    intro p
    have hchain : RelData.BCqIterO F (k - 1) D = E := RelData.BCqIterO_eq_BCqIter F (k - 1) D
    have hps := RelData.psum_cB_eq_of_eq F hchain p k
    have hO := RelData.BCqIterO_cB_psum_le F (k - 1) D
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
  -- (3) the fold and the dispatch
  let mdep (p : E.ιB) : ℕ := E.depB p
  let mhdep (p : E.ιB) : 0 < mdep p := E.hdepB p
  let mc (p : E.ιB) : Fin (mdep p) → ℕ+ := E.cB p
  let ma (p : E.ιB) : RatFunc F := -(E.aB p)
  have hid : ζ_A F s = ∑ p : E.ιB,
      (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    have h' : ζ_A F s = -(∑ p : E.ιB,
        (((E.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (E.cB p))) :=
      eq_neg_of_add_eq_zero_left hrel
    rw [h', ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [ma, mc]
    exact (neg_coe_mul_zeta F (E.aB p) (E.cB p)).symm
  have horder : ∀ p : E.ιB, ∀ ℓ : ℕ, k ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    rw [psum_ge_depth s hℓ]
    calc
      psum (mc p) ℓ ≤ weight (mdep p) (mc p) := psum_le_weight (mc p) ℓ
      _ = w := by
            dsimp [mdep, mc]
            exact hwt p
      _ = weight k s := hw.symm
  have e : ∀ p : E.ιB, AdmExpT F w k (mc p) := by
    intro p
    have hwv : weight (mdep p) (mc p) = w := by
      dsimp [mdep, mc]
      exact hwt p
    by_cases hkadm : kAdmissible (Nat.card F) (mc p) k
    · exact admExpT_self F w k (mhdep p) (mc p) hwv hkadm
    · refine rec (mdep p) (mc p) hwv (Or.inl ?_) hkadm
      exact hdrop p
  exact admExpT_combine F w k s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar