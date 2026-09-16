import Submission.ZagierHoffmanProof.StepL181
import Submission.ZagierHoffmanProof.StepL51
import Submission.ZagierHoffmanProof.StepL50

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L182: THE DEPTH-INVARIANT — the paper's Remark, and the level-1 base's `(1 :: cb j)` case

The last lever identified in PLAN SESSION 272 is the DEPTH-INVARIANT OF EXPANSIONS: every output
`c` of an expansion of `t` has `depth c ≥ depth t`.  Its engine is the paper's own Remark
(`/tmp/nd21paper.tex`, `rmk: compa depth`): equal weights plus prefix dominance force the depth,
because otherwise the shallower tuple's weight would be reached strictly below the deeper one's:

  ★★★ `dep_ge_of_weight_eq_of_psum_le` — `weight c = weight t` and `∀ m, psum c m ≤ psum t m`
      imply `depth t ≤ depth c`.

This module then discharges the ONE base case flagged in the PLAN — the level-1 base `H1_expT`
in the `s₁ > q` branch (`StepL51`, from `lemma_2_9_zeta`):
  • ★★ `level1_bMember_dep_ge` — the `b`-members `(1 :: cb j)` have depth `≥ depth s` (in fact
    `depb j + 1 ≥ r`, via `bMember_order` at `ℓ ≥ 1` + the weight identity
    `weight (1 :: cb j) = 1 + (w − 1) = w`);
  • ★★ `level1_aMember_dep_ge` — the `a`-members `ca i` have depth `≥ depth s` (via
    `aSide_order` + `weight (ca i) = q + w1 + weight (expTail s) = w`);
  • ★★★ `level1_dep_invariant` — the combined statement: in the `s₁ > q` branch of the level-1
    base, EVERY output of `H1_expT`'s expansion is at least as deep as the input.  (The other
    branch of the level-1 base is `admExpT_self` — equal depths — except the `(q)` case whose
    R1-output `(1, q−1)` has depth `2 > 1 = depth (q)` ✓, and `pair_one_qminus_order` supplies
    the order there.)
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★ THE PAPER'S REMARK (`rmk: compa depth`): equal weights plus prefix dominance force the
depth.  (If `depth c < depth t`, then `weight c = psum c (depth c) ≤ psum t (depth c)
< psum t (depth t) = weight t`.) -/
theorem dep_ge_of_weight_eq_of_psum_le {rc rt : ℕ} (c : Fin rc → ℕ+) (t : Fin rt → ℕ+)
    (hw : weight rc c = weight rt t) (hle : ∀ m : ℕ, psum c m ≤ psum t m) :
    rt ≤ rc := by
  by_contra hcon
  push Not at hcon
  have h1 : psum c rc = weight rc c := psum_ge_depth c (le_refl rc)
  have h2 : psum t rc < psum t rt := psum_lt_psum_of_lt t hcon (le_refl rt)
  have h3 : psum t rt = weight rt t := psum_ge_depth t (le_refl rt)
  have h4 := hle rc
  omega

/-- ★ `psum (ca i) m ≤ psum s m` for ALL `m`, from the `ℓ ≥ 1` order. -/
lemma aMember_psum_all_le {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depa : ι → ℕ) (hdepa : ∀ i, 0 < depa i) (ca : ∀ i, Fin (depa i) → ℕ+)
    (hleA : ∀ i, LePad (ca i) (single (qExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s)) ∧
        ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) +
          ((s ⟨0, hr⟩ : ℕ) - Nat.card F)) :
    ∀ i, ∀ m : ℕ, psum (ca i) m ≤ psum s m := by
  intro i m
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [psum_zero, psum_zero]
  · exact aSide_order F hr s hgt depa hdepa ca hleA i m hm

/-- ★ `psum (consVec oneExp (cb j)) m ≤ psum s m` for ALL `m`, from the `ℓ ≥ 1` order. -/
lemma bMember_psum_all_le {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depb : ι → ℕ) (hdepb : ∀ j, 0 < depb j) (cb : ∀ j, Fin (depb j) → ℕ+)
    (hleB : ∀ j, LePad (cb j) (single (qMinusExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s))) :
    ∀ j, ∀ m : ℕ, psum (consVec oneExp (cb j)) m ≤ psum s m := by
  intro j m
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [psum_zero, psum_zero]
  · exact bMember_order F hr s hgt depb hdepb cb hleB j m hm

/-- The tail-weight identity `weight (expTail s) = weight s − s₁`. -/
lemma level1_tail_weight {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) :
    weight (r - 1) (expTail s) = weight r s - (s ⟨0, hr⟩ : ℕ) := by
  have ht := psum_s_tail_split hr s (r - 1)
  have h1 : 1 + (r - 1) = r := by omega
  rw [h1] at ht
  have h2 : psum s r = weight r s := psum_ge_depth s (le_refl r)
  have h3 : psum (expTail s) (r - 1) = weight (r - 1) (expTail s) :=
    psum_ge_depth (expTail s) (le_refl (r - 1))
  rw [h2, h3] at ht
  omega

/-- The first entry is at most the weight. -/
lemma first_le_weight {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) :
    (s ⟨0, hr⟩ : ℕ) ≤ weight r s := by
  have h := psum_mono s (by omega : 1 ≤ r)
  have h1 : psum s 1 = (s ⟨0, hr⟩ : ℕ) := by
    change (∑ x ∈ Finset.range 1, pad0 s x) = (s ⟨0, hr⟩ : ℕ)
    rw [Finset.sum_range_one]
    exact pad0_of_lt s hr
  rw [h1, psum_ge_depth s (le_refl r)] at h
  exact h

/-- ★★ The level-1 base's `b`-members `(1 :: cb j)` are at least as deep as the input `s`
(the case flagged in PLAN SESSION 272). -/
theorem level1_bMember_dep_ge {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depb : ι → ℕ) (hdepb : ∀ j, 0 < depb j) (cb : ∀ j, Fin (depb j) → ℕ+)
    (hleB : ∀ j, LePad (cb j) (single (qMinusExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s))) :
    ∀ j, r ≤ depb j + 1 := by
  classical
  intro j
  have hle := bMember_psum_all_le F hr s hgt depb hdepb cb hleB j
  have hwt : weight (depb j + 1) (consVec oneExp (cb j)) = weight r s := by
    have h1 : weight 1 (single (qMinusExp F)) = (qMinusExp F : ℕ) := weight_single (qMinusExp F)
    have h2 : weight (r - 1 + 1) (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
          (expTail s)) = ((s ⟨0, hr⟩ : ℕ) - Nat.card F) + weight (r - 1) (expTail s) :=
      weight_consVec _ _
    have h3 := level1_tail_weight hr s
    have hB : weight (depb j) (cb j) = (qMinusExp F : ℕ) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F) +
        (weight r s - (s ⟨0, hr⟩ : ℕ)) := by
      rw [(hleB j).1, h1, h2, h3]
      omega
    rw [weight_consVec, hB]
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
    rw [hq]
    have hq1 : 1 ≤ Nat.card F := by have h := card_ge_two F; omega
    have hlt : Nat.card F < (s ⟨0, hr⟩ : ℕ) := hgt
    have hpos : 1 ≤ (s ⟨0, hr⟩ : ℕ) := (s ⟨0, hr⟩).pos
    have hsle := first_le_weight hr s
    have hstep : (Nat.card F - 1) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F) +
        (weight r s - (s ⟨0, hr⟩ : ℕ)) = weight r s - 1 := by omega
    have hw1 : 1 ≤ weight r s := by omega
    rw [hstep]
    exact Nat.add_sub_cancel' hw1
  exact dep_ge_of_weight_eq_of_psum_le (consVec oneExp (cb j)) s hwt hle

/-- ★★ The level-1 base's `a`-members `ca i` are at least as deep as the input `s`. -/
theorem level1_aMember_dep_ge {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depa : ι → ℕ) (hdepa : ∀ i, 0 < depa i) (ca : ∀ i, Fin (depa i) → ℕ+)
    (hleA : ∀ i, LePad (ca i) (single (qExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s)) ∧
        ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) +
          ((s ⟨0, hr⟩ : ℕ) - Nat.card F)) :
    ∀ i, r ≤ depa i := by
  classical
  intro i
  have hle := aMember_psum_all_le F hr s hgt depa hdepa ca hleA i
  have hwt : weight (depa i) (ca i) = weight r s := by
    have h1 : weight 1 (single (qExp F)) = (qExp F : ℕ) := weight_single (qExp F)
    have h2 : weight (r - 1 + 1) (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
          (expTail s)) = ((s ⟨0, hr⟩ : ℕ) - Nat.card F) + weight (r - 1) (expTail s) :=
      weight_consVec _ _
    have h3 := level1_tail_weight hr s
    have hB : weight (depa i) (ca i) = (qExp F : ℕ) + ((s ⟨0, hr⟩ : ℕ) - Nat.card F) +
        (weight r s - (s ⟨0, hr⟩ : ℕ)) := by
      rw [(hleA i).1.1, h1, h2, h3]
      omega
    rw [hB]
    have hq : (qExp F : ℕ) = Nat.card F := rfl
    rw [hq]
    have hq1 : 1 ≤ Nat.card F := by have h := card_ge_two F; omega
    have hlt : Nat.card F < (s ⟨0, hr⟩ : ℕ) := hgt
    have hpos : 1 ≤ (s ⟨0, hr⟩ : ℕ) := (s ⟨0, hr⟩).pos
    have hsle := first_le_weight hr s
    have hstep : Nat.card F + ((s ⟨0, hr⟩ : ℕ) - Nat.card F) +
        (weight r s - (s ⟨0, hr⟩ : ℕ)) = weight r s - 1 + 1 := by omega
    have hw1 : 1 ≤ weight r s := by omega
    rw [hstep]
    exact Nat.sub_add_cancel hw1
  exact dep_ge_of_weight_eq_of_psum_le (ca i) s hwt hle

end ZagierHoffmanPositiveChar
