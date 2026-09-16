import Submission.ZagierHoffmanProof.StepL49
import Submission.ZagierHoffmanProof.StepL37

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L50: the H₁ re-run order payload — depth-1 reference computations and
per-member prefix-orders

The strengthened H₁ (`H1_expT`, StepL51) must carry per-output prefix-orders
`psum c ℓ ≤ psum s ℓ` (`ℓ ≥ 1`).  For the `s₁ > q` branch the Lemma-2.9 CW outputs
are bounded by the reference tuples `(q, w1, expTail s)` (a-side, `hleA`) and
`(q−1, w1, expTail s)` (b-side tails, `hleB`).  These two references telescope into
`s`-prefixes EXACTLY (index 0 = q+w1 = s₁ / (q−1)+w1 = s₁−1; index 1+t =
pad0 (expTail s) t = pad0 s (1+t)):
  psumSeq (tupPadSum (single qExp) (consVec w1 (expTail s))) ℓ = psum s ℓ
  psumSeq (tupPadSum (single qMinusExp) (consVec w1 (expTail s))) m = psum s m − 1
giving ★ `aSide_order` (psum(ca i) ℓ ≤ psum s ℓ) and ★ `bMember_order`
(psum (1::cb j) ℓ ≤ psum s ℓ) — the member-order hypotheses of the H₁ splice.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `s`-prefixes split at the head: `psum s (1+m) = s₁ + psum (expTail s) m`. -/
lemma psum_s_tail_split {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) (m : ℕ) :
    psum s (1 + m) = (s ⟨0, hr⟩ : ℕ) + psum (expTail s) m := by
  classical
  change (∑ x ∈ Finset.range (1 + m), pad0 s x) =
    (s ⟨0, hr⟩ : ℕ) + (∑ x ∈ Finset.range m, pad0 (expTail s) x)
  rw [Finset.sum_range_add]
  have h1 : (∑ x ∈ Finset.range 1, pad0 s x) = (s ⟨0, hr⟩ : ℕ) := by
    rw [Finset.sum_range_one]
    exact pad0_of_lt s hr
  have h2 : (∑ t ∈ Finset.range m, pad0 s (1 + t)) = (∑ t ∈ Finset.range m, pad0 (expTail s) t) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact (expTail_pad0 r hr s t).symm
  rw [h1, h2]

/-- `psum (consVec x t) ℓ = x + psum t (ℓ−1)` for `ℓ ≥ 1`. -/
lemma psum_consVec_sub_one (x : ℕ+) {m : ℕ} (t : Fin m → ℕ+) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    psum (consVec x t) ℓ = (x : ℕ) + psum t (ℓ - 1) := by
  classical
  have hℓ' : ℓ = (ℓ - 1) + 1 := by omega
  rw [hℓ']
  simpa using (psum_consVec x t (ℓ - 1))

/-- The `(q, w1, expTail s)` reference-prefix at `ℓ ≥ 1` is exactly `psum s ℓ`. -/
lemma ref_q_cons_tail_psumSeq {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) (w1 : ℕ+)
    (hw1add : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨0, hr⟩ : ℕ))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    psumSeq (tupPadSum (single (qExp F)) (consVec w1 (expTail s))) ℓ = psum s ℓ := by
  classical
  have hq := psum_single_of_pos (qExp F) hℓ
  calc
    psumSeq (tupPadSum (single (qExp F)) (consVec w1 (expTail s))) ℓ
        = psum (single (qExp F)) ℓ + psum (consVec w1 (expTail s)) ℓ :=
          psumSeq_tupPadSum_split (single (qExp F)) (consVec w1 (expTail s)) ℓ
    _ = (qExp F : ℕ) + psum (consVec w1 (expTail s)) ℓ := by rw [hq]
    _ = (qExp F : ℕ) + ((w1 : ℕ) + psum (expTail s) (ℓ - 1)) := by
          rw [psum_consVec_sub_one w1 (expTail s) ℓ hℓ]
    _ = ((qExp F : ℕ) + (w1 : ℕ)) + psum (expTail s) (ℓ - 1) := by omega
    _ = (s ⟨0, hr⟩ : ℕ) + psum (expTail s) (ℓ - 1) := by rw [hw1add]
    _ = psum s (1 + (ℓ - 1)) := by rw [psum_s_tail_split hr s (ℓ - 1)]
    _ = psum s ℓ := by
          have hℓ2 : 1 + (ℓ - 1) = ℓ := by omega
          rw [hℓ2]

/-- The `(q−1, w1, expTail s)` reference-prefix at `m ≥ 1` is exactly `psum s m − 1`. -/
lemma ref_qminus_cons_tail_psumSeq {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+) (w1 : ℕ+)
    (hw1add : (qMinusExp F : ℕ) + (w1 : ℕ) = (s ⟨0, hr⟩ : ℕ) - 1)
    (m : ℕ) (hm : 1 ≤ m) :
    psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 (expTail s))) m = psum s m - 1 := by
  classical
  have hq := psum_single_of_pos (qMinusExp F) hm
  have hs1 : 1 ≤ (s ⟨0, hr⟩ : ℕ) := (s ⟨0, hr⟩).pos
  calc
    psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 (expTail s))) m
        = psum (single (qMinusExp F)) m + psum (consVec w1 (expTail s)) m :=
          psumSeq_tupPadSum_split (single (qMinusExp F)) (consVec w1 (expTail s)) m
    _ = (qMinusExp F : ℕ) + psum (consVec w1 (expTail s)) m := by rw [hq]
    _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + psum (expTail s) (m - 1)) := by
          rw [psum_consVec_sub_one w1 (expTail s) m hm]
    _ = ((qMinusExp F : ℕ) + (w1 : ℕ)) + psum (expTail s) (m - 1) := by omega
    _ = ((s ⟨0, hr⟩ : ℕ) - 1) + psum (expTail s) (m - 1) := by rw [hw1add]
    _ = psum s m - 1 := by
          have ht := psum_s_tail_split hr s (m - 1)
          have hm2 : 1 + (m - 1) = m := by omega
          rw [hm2] at ht
          omega


/-- ★ The `a`-side members of the depth-1 CW satisfy `psum (ca i) ℓ ≤ psum s ℓ` for
`ℓ ≥ 1` (the `hleA` reference telescopes to `psum s ℓ`). -/
lemma aSide_order {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depa : ι → ℕ) (hdepa : ∀ i, 0 < depa i) (ca : ∀ i, Fin (depa i) → ℕ+)
    (hleA : ∀ i, LePad (ca i) (single (qExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s)) ∧
        ((ca i) ⟨0, hdepa i⟩ : ℕ) < (qExp F : ℕ) +
          ((s ⟨0, hr⟩ : ℕ) - Nat.card F)) :
    ∀ i, ∀ (ℓ : ℕ), 1 ≤ ℓ → psum (ca i) ℓ ≤ psum s ℓ := by
  classical
  intro i ℓ hℓ
  let w1 : ℕ+ := ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
  let B : Fin (r - 1) → ℕ+ := expTail s
  have hleA' : LePad (ca i) (single (qExp F)) (consVec w1 B) := by
    simpa [w1, B] using (hleA i).1
  have hb := hleA'.2 ℓ
  have hw1 : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨0, hr⟩ : ℕ) := by
    have hq : (qExp F : ℕ) = Nat.card F := by rfl
    rw [hq]
    dsimp [w1]
    omega
  have href := ref_q_cons_tail_psumSeq F hr s w1 hw1 ℓ hℓ
  calc
    psum (ca i) ℓ ≤ psumSeq (tupPadSum (single (qExp F)) (consVec w1 B)) ℓ := by
          simpa [B] using hb
    _ = psumSeq (tupPadSum (single (qExp F)) (consVec w1 (expTail s))) ℓ := by
          rfl
    _ = psum s ℓ := href

/-- ★ The `b`-members `(1 :: cb j)` of the depth-1 CW satisfy
`psum (consVec oneExp (cb j)) ℓ ≤ psum s ℓ` for `ℓ ≥ 1` (via the `hleB` reference,
`psum (1::cb) ℓ = 1 + psum cb (ℓ−1) ≤ 1 + (psum s (ℓ−1) − 1) = psum s (ℓ−1) ≤ psum s ℓ`). -/
lemma bMember_order {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ)) {ι : Type} [Fintype ι]
    (depb : ι → ℕ) (hdepb : ∀ j, 0 < depb j) (cb : ∀ j, Fin (depb j) → ℕ+)
    (hleB : ∀ j, LePad (cb j) (single (qMinusExp F))
      (consVec ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩ (expTail s))) :
    ∀ j, ∀ (ℓ : ℕ), 1 ≤ ℓ → psum (consVec oneExp (cb j)) ℓ ≤ psum s ℓ := by
  classical
  intro j ℓ hℓ
  let w1 : ℕ+ := ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
  let B : Fin (r - 1) → ℕ+ := expTail s
  have hleB' : LePad (cb j) (single (qMinusExp F)) (consVec w1 B) := by
    simpa [w1, B] using hleB j
  have hw1 : (qMinusExp F : ℕ) + (w1 : ℕ) = (s ⟨0, hr⟩ : ℕ) - 1 := by
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := by rfl
    have hq1 : 1 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    rw [hq]
    dsimp [w1]
    omega
  by_cases hℓ1 : ℓ = 1
  · subst ℓ
    -- psum (1::cb j) 1 = 1 ≤ psum s 1 = s₁
    have h1m : psum (consVec oneExp (cb j)) 1 = 1 := by
      change (∑ x ∈ Finset.range 1, pad0 (consVec oneExp (cb j)) x) = 1
      rw [Finset.sum_range_one]
      have h00 : 0 < depb j + 1 := by omega
      have hp : pad0 (consVec oneExp (cb j)) 0 =
          ((consVec oneExp (cb j)) ⟨0, h00⟩ : ℕ) := pad0_of_lt (consVec oneExp (cb j)) h00
      rw [hp]
      have hc := congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero oneExp (cb j))
      rw [hc]
      rfl
    have hps : psum s 1 = (s ⟨0, hr⟩ : ℕ) := by
      change (∑ x ∈ Finset.range 1, pad0 s x) = (s ⟨0, hr⟩ : ℕ)
      rw [Finset.sum_range_one]
      exact pad0_of_lt s hr
    rw [h1m, hps]
    exact (s ⟨0, hr⟩).pos
  · have hℓge : 2 ≤ ℓ := by omega
    have hℓ1' : 1 ≤ ℓ - 1 := by omega
    have hb := (hleB'.2) (ℓ - 1)
    have href := ref_qminus_cons_tail_psumSeq F hr s w1 hw1 (ℓ - 1) hℓ1'
    have hp1 := psum_consVec_sub_one oneExp (cb j) ℓ hℓ
    calc
      psum (consVec oneExp (cb j)) ℓ = (oneExp : ℕ) + psum (cb j) (ℓ - 1) := by
            rw [hp1]
      _ = 1 + psum (cb j) (ℓ - 1) := by rfl
      _ ≤ 1 + psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 B)) (ℓ - 1) := by
            exact Nat.add_le_add_left (by simpa [B] using hb) 1
      _ = 1 + (psum s (ℓ - 1) - 1) := by
            have hre' : psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 B)) (ℓ - 1) =
                psum s (ℓ - 1) - 1 := by
              simpa [B] using href
            rw [hre']
      _ ≤ psum s (ℓ - 1) := by
            have hs1 : 1 ≤ psum s (ℓ - 1) := by
              have hmono : psum s 1 ≤ psum s (ℓ - 1) := psum_mono s (by omega)
              have hpos : 1 ≤ (s ⟨0, hr⟩ : ℕ) := (s ⟨0, hr⟩).pos
              have hps : psum s 1 = (s ⟨0, hr⟩ : ℕ) := by
                change (∑ x ∈ Finset.range 1, pad0 s x) = (s ⟨0, hr⟩ : ℕ)
                rw [Finset.sum_range_one]
                exact pad0_of_lt s hr
              omega
            omega
      _ ≤ psum s ℓ := psum_mono s (by omega)

/-- Transport of a strengthened expansion along a weight equality. -/
lemma admExpT_weight_transport (w w' k : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (h : AdmExpT F w' k s) (hww : w' = w) : AdmExpT F w k s := by
  classical
  rcases h with ⟨ι, fin, dep, hdep, c, a, hwt, hadm, horder, hid⟩
  refine ⟨ι, fin, dep, hdep, c, a, ?_, hadm, horder, hid⟩
  intro i
  rw [← hww]
  exact hwt i
end ZagierHoffmanPositiveChar
