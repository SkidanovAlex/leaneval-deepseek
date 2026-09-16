import Submission.ZagierHoffmanProof.StepL32

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L34: the Lemma-2.9 data at the Prop-2.12 configuration (weight/head glue)

`lemma_2_9_config_data` instantiates `lemma_2_9_rel` (StepL5) at the Prop-2.12
configuration: for `r s k` with `1 ≤ k ≤ r` and `s_k > q` (`hbig`), the Lemma-2.9
relation at `W := (s_k − q, s_{k+1}, …, s_r)` (= `w1Of` :: `sTail`) provides
`R0 = BinaryRel`, distinguished `u` with coefficient `1`, `depA u = (r−k)+1` and
tuple `bstarBase` (= `(s_k, …, s_r)`) — exactly zeta_214's data hypotheses — together
with the per-member bound hypotheses the Step-1 assembly needs:
  • non-leading `a`-members: weight = `psum s r − psum s (k−1)` (= `s_k+…+s_r`), head
    `< s_k`  [feeds `type1_weight_eq` (hwtA) and `type1_psum_lt_k` (hhead)];
  • `b`-members: `weight (depB−1) (expTail cB) = psum s r − psum s (k−1) − 1`
    [feeds `type2/3_weight_eq` (hXw)].
Supporting tuple bookkeeping: `pad0_sTail`, `weight_sTail` (the tail weight
`weight (r−k) (sTail r s k) = psum s r − psum s k`), `psum_last`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
/-- Padding a tail tuple: `pad0 (sTail r s k hkr) x = pad0 s (k + x)`. -/
lemma pad0_sTail (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hkr : k ≤ r) (x : ℕ) :
    pad0 (sTail r s k hkr) x = pad0 s (k + x) := by
  classical
  by_cases hx : x < r - k
  · have hxr' : x < r - k := hx
    have hkxl : k + x < r := by omega
    have hs : (sTail r s k hkr) ⟨x, hxr'⟩ = s ⟨k + x, hkxl⟩ := by
      dsimp [sTail]
    rw [pad0_of_lt (sTail r s k hkr) hxr', hs, pad0_of_lt s hkxl]
  · have hge : r - k ≤ x := le_of_not_gt hx
    have hge' : r ≤ k + x := by omega
    rw [pad0_of_ge (sTail r s k hkr) hge, pad0_of_ge s hge']

/-- The weight of the tail `(s_{k+1}, …, s_r)` equals `psum s r − psum s k`. -/
lemma weight_sTail (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hkr : k ≤ r) :
    weight (r - k) (sTail r s k hkr) = psum s r - psum s k := by
  classical
  have hkr' : k + (r - k) = r := Nat.add_sub_of_le hkr
  have h1 : psum s (k + (r - k)) = psum s r := congrArg (fun m : ℕ => psum s m) hkr'
  have hsr : (∑ x ∈ Finset.range (k + (r - k)), pad0 s x) =
      (∑ x ∈ Finset.range k, pad0 s x) + (∑ x ∈ Finset.range (r - k), pad0 s (k + x)) := by
    simpa using (Finset.sum_range_add (f := pad0 s) k (r - k))
  have hsplit : psum s r = psum s k + (∑ x ∈ Finset.range (r - k), pad0 s (k + x)) := by
    rw [← h1]
    change (∑ x ∈ Finset.range (k + (r - k)), pad0 s x) =
      (∑ x ∈ Finset.range k, pad0 s x) + (∑ x ∈ Finset.range (r - k), pad0 s (k + x))
    exact hsr
  have hrest : (∑ x ∈ Finset.range (r - k), pad0 s (k + x)) = psum s r - psum s k := by
    omega
  calc
    weight (r - k) (sTail r s k hkr) = psum (sTail r s k hkr) (r - k) := by
          exact (psum_self (sTail r s k hkr)).symm
    _ = (∑ x ∈ Finset.range (r - k), pad0 s (k + x)) := by
          change (∑ x ∈ Finset.range (r - k), pad0 (sTail r s k hkr) x) =
            (∑ x ∈ Finset.range (r - k), pad0 s (k + x))
          apply Finset.sum_congr rfl
          intro x hx
          exact pad0_sTail r s k hkr x
    _ = psum s r - psum s k := hrest

/-- Prefix sum at the last position `m`: `psum s m = psum s (m−1) + s_{m−1}`. -/
lemma psum_last (r : ℕ) (s : Fin r → ℕ+) (m : ℕ) (hm1 : 1 ≤ m) (hmr : m ≤ r) :
    psum s m = psum s (m - 1) + (s ⟨m - 1, by omega⟩ : ℕ) := by
  have hsu := psum_succ s (m - 1)
  have hmm : (m - 1) + 1 = m := by omega
  rw [hmm] at hsu
  rw [hsu]
  rw [pad0_of_lt s (by omega : m - 1 < r)]

/-- ★ The Lemma-2.9 data at the Prop-2.12 configuration, with the weight/head bounds
in the `s/k`-notation: `R0 = lemma_2_9_rel F (r−k) (w1Of …) (sTail …)`, `u` its
distinguished output.  Produces exactly zeta_214's hypotheses plus the `hleA`-weight
(`psum r − psum(k−1)` per non-leading `a`-member), the `hleA`-head
(`< s_k`), and the `hleB`-weight (`psum r − psum(k−1) − 1` per `b`-member). -/
theorem lemma_2_9_config_data (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA),
      R0.depA u = (r - k) + 1 ∧ R0.aA u = 1 ∧
      (∀ hd : R0.depA u = (r - k) + 1,
        (fun x : Fin ((r - k) + 1) => R0.cA u (Fin.cast hd.symm x)) =
          bstarBase F r s k hk1 hkr hbig) ∧
      (∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) ∧
      (∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1)) ∧
      (∀ i : R0.ιA, i ≠ u →
        ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) ∧
      (∀ j' : R0.ιB,
        weight (R0.depB j' - 1) (expTail (R0.cB j')) = psum s r - psum s (k - 1) - 1) ∧
      (∀ j' : R0.ιB, ∀ m : ℕ,
        psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
          (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) := by
  classical
  let w1 : ℕ+ := w1Of F r s k hk1 hkr hbig
  let B : Fin (r - k) → ℕ+ := sTail r s k hkr
  rcases lemma_2_9_rel F (r - k) w1 B with ⟨R0, u, hdep, ha, hc, hleA, hbhd, hleB, hvalid⟩
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hsum : psum s k = psum s (k - 1) + (s ⟨k - 1, by omega⟩ : ℕ) :=
    psum_last r s k hk1 hkr
  have hmono : psum s k ≤ psum s r := psum_mono s hkr
  refine ⟨R0, u, hdep, ha, ?hc0, hbhd, ?hwtA, ?hhead, ?hXw, ?hbndB⟩
  · intro hd
    simpa [bstarBase, w1, B] using hc hd
  · intro i hi
    have hL := hleA i hi
    have hw' : (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depA i) (R0.cA i)
          = weight 1 (single (qExp F)) + weight ((r - k) + 1) (consVec w1 B) := hL.1.1
      _ = (qExp F : ℕ) + ((w1 : ℕ) + weight (r - k) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = Nat.card F + ((w1 : ℕ) + (psum s r - psum s k)) := by
            rw [show (qExp F : ℕ) = Nat.card F by rfl]
            rw [weight_sTail r s k hkr]
      _ = psum s r - psum s (k - 1) := by
            rw [hw']
            omega
  · intro i hi
    have hL2 := (hleA i hi).2
    have hwadd : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) := by
      dsimp [w1]
      exact w1Of_add F r s k hk1 hkr hbig
    simpa [hwadd] using hL2
  · intro j'
    have hL := hleB j'
    have hw' : (w1 : ℕ) = (s ⟨k - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depB j' - 1) (expTail (R0.cB j'))
          = weight 1 (single (qMinusExp F)) + weight ((r - k) + 1) (consVec w1 B) := hL.1
      _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + weight (r - k) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = (Nat.card F - 1) + ((w1 : ℕ) + (psum s r - psum s k)) := by
            rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
            rw [weight_sTail r s k hkr]
      _ = psum s r - psum s (k - 1) - 1 := by
            rw [hw']
            omega
  · intro j' m
    have hL := hleB j'
    simpa [w1, B] using (hL.2 m)

end ZagierHoffmanPositiveChar
