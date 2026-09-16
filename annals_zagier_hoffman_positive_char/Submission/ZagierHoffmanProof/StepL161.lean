import Submission.ZagierHoffmanProof.StepL48
import Submission.ZagierHoffmanProof.StepL32
import Submission.ZagierHoffmanProof.StepL28
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L161: the member DEPTH invariants of the (k,j)-chains (paper Prop 2.12:
`depth(t) ≥ depth(s)`) — the missing half of the paper's member conclusions

The Lean chains state their member facts only through the prefix-sum order `LePad`
(cumulative bounds), which is *weaker* than the paper's entrywise bounds.  The paper's
Prop 2.12 conclusion `depth(t) ≥ depth(s)` is nevertheless recoverable: a member of weight
`w` whose prefix sums are bounded by the saturated template must have length at least the
input's, because every entry of the template's tail is positive.

This module records the three member depth invariants for the generic `(k,j)` CASE-1
chain:
  • `type1_dep_ge` : `r ≤ depth(type-1 member)`;
  • `type2_dep_gt` : `r < depth(type-2 member)`      (paper: `depth ≥ r+1`);
  • `type3_dep_ge` : `r ≤ depth(type-3 member)`.
They are exactly the hypotheses under which the ambient-level measure
`(psum·k, M − depth, …)` of route (Γ′) decreases along every chain member call.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `psum s k = psum s (k-1) + s_k` (for `1 ≤ k ≤ r`). -/
lemma psum_last_eq (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) :
    psum s k = psum s (k - 1) + (s ⟨k - 1, by omega⟩ : ℕ) := by
  have hsu := psum_succ s (k - 1)
  have hkk : (k - 1) + 1 = k := by omega
  rw [hkk] at hsu
  rw [hsu, pad0_of_lt s (by omega : k - 1 < r)]

/-- Prefix sums strictly increase below the depth (entries are positive). -/
lemma psum_lt_psum_of_lt {r : ℕ} (s : Fin r → ℕ+) {m n : ℕ} (hmn : m < n) (hn : n ≤ r) :
    psum s m < psum s n := by
  classical
  change (∑ j ∈ Finset.range m, pad0 s j) < (∑ j ∈ Finset.range n, pad0 s j)
  have hn' : n = m + (n - m) := (Nat.add_sub_of_le (le_of_lt hmn)).symm
  rw [hn', Finset.sum_range_add]
  have hpos : 0 < ∑ x ∈ Finset.range (n - m), pad0 s (m + x) := by
    apply Finset.sum_pos'
    · intro x hx
      exact Nat.zero_le _
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      rw [pad0_of_lt s (by omega : m + 0 < r)]
      exact (s ⟨m + 0, by omega⟩).pos
  omega

/-- ★ Type-1 member depth: at least `depth s`.  (Paper Prop 2.12.) -/
lemma type1_dep_ge (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      (weight (R0.depA i₀) (R0.cA i₀) = psum s r - psum s (k - 1)) →
      (∀ m : ℕ, psum (R0.cA i₀) m ≤ psumSeq (tupPadSum (single (qExp F))
          (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      r ≤ Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) := by
  classical
  intro D Bs Q i₀ hwtA hpref
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) =
      Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) +
        (sPrefix r s j (by omega) (by omega)).length :=
    FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) _
  have hBsdep : Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) =
      D.depA (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) + 1 := by
    dsimp [Bs, ofBstarOver, D]
  have hDdep : D.depA (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) =
      R0.depA i₀ + (k - j - 1) := by
    dsimp [D]
    exact RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
  have hdep : Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) =
      R0.depA i₀ + (k - 1) := by
    rw [hQdep, hBsdep, hDdep, hlen]
    omega
  rw [hdep]
  by_contra hcon
  have hle : R0.depA i₀ ≤ r - k := by omega
  have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
  -- the template telescope
  let w1 : ℕ+ := w1Of F r s k hk1 hkr hbig
  let B : Fin (r - k) → ℕ+ := sTail r s k hkr
  let X : ℕ → ℕ := tupPadSum (single (qExp F)) (consVec w1 B)
  have htel := lemma29_qExp_telescope F r s k hk1 hkr hbig (R0.depA i₀) hpos
  -- hpref at the depth
  have h1 := hpref (R0.depA i₀)
  have h2 : psum (R0.cA i₀) (R0.depA i₀) = weight (R0.depA i₀) (R0.cA i₀) :=
    psum_ge_depth (R0.cA i₀) (le_refl _)
  rw [h2, hwtA] at h1
  -- h1 : psum s r - psum s (k-1) ≤ psumSeq X (depA)
  -- and psumSeq X (depA) = s_k + (psum s (k + depA - 1) - psum s k)
  have h3 : psumSeq X (R0.depA i₀) =
      (s ⟨k - 1, by omega⟩ : ℕ) + (psum s (k + R0.depA i₀ - 1) - psum s k) := by
    have := htel
    simpa [w1, B] using this
  rw [h3] at h1
  have hpk := psum_last_eq r s k hk1 hkr
  have hkm : k + R0.depA i₀ - 1 ≤ r - 1 := by omega
  have hmono : psum s (k + R0.depA i₀ - 1) ≤ psum s (r - 1) := psum_mono s hkm
  have hpk1 : psum s (k - 1) ≤ psum s r := psum_mono s (by omega)
  have hlt : psum s (r - 1) < psum s r := psum_lt_psum_of_lt s (by omega) (le_refl r)
  -- assemble: psum s r = psum s (k-1) + weight(cA) ≤ psum s (k-1) + psumSeq X (depA)
  --           = psum s (k + depA - 1) ≤ psum s (r-1) < psum s r
  have hkey : psum s (k - 1) + (psum s r - psum s (k - 1)) ≤
      psum s (k - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) +
        (psum s (k + R0.depA i₀ - 1) - psum s k)) := Nat.add_le_add_left h1 _
  rw [Nat.add_sub_cancel' hpk1] at hkey
  have hsk : psum s (k - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) +
      (psum s (k + R0.depA i₀ - 1) - psum s k)) = psum s (k + R0.depA i₀ - 1) := by
    have hle' : psum s k ≤ psum s (k + R0.depA i₀ - 1) := psum_mono s (by omega)
    omega
  rw [hsk] at hkey
  omega

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The fiber-tail depth lower bound (shared by the type-2 and type-3 members):
if the fiber tail's weight is `n·q + Xw` with `Xw ≥ 2` (which holds for `s_k > q ≥ 1`)
and its prefix sums are bounded by the saturated template, then its depth is `≥ r−j`. -/
lemma fiber_dep_ge (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    ∀ i : D.ιB,
      weight (D.depB i - 1) (expTail (D.cB i)) =
        (k - j - 1) * Nat.card F + (psum s r - psum s (k - 1) - 1) →
      (∀ j' : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum
          (single (qMinusExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      r - j ≤ D.depB i - 1 := by
  classical
  intro D i hwid hbndB
  let w1 : ℕ+ := w1Of F r s k hk1 hkr hbig
  let B : Fin (r - k) → ℕ+ := sTail r s k hkr
  let X : ℕ → ℕ := fun m => psumSeq (tupPadSum (single (qMinusExp F)) (consVec w1 B)) m
  have hq2 : 2 ≤ Nat.card F := card_ge_two F
  -- Xw ≥ 2
  have hpk := psum_last_eq r s k hk1 hkr
  have hskbig : 2 ≤ (s ⟨k - 1, by omega⟩ : ℕ) := by omega
  have hXw2 : 2 ≤ psum s r - psum s (k - 1) := by
    have hmono : psum s k ≤ psum s r := psum_mono s hkr
    omega
  -- weight(expTail) ≥ n*q + 1
  have hbigger : (k - j - 1) * Nat.card F + 1 ≤ weight (D.depB i - 1) (expTail (D.cB i)) := by
    omega
  have hdpos : 0 < D.depB i := D.hdepB i
  -- the lifted fiber bound
  have hfib : ∀ m : ℕ, psum (expTail (D.cB i)) m ≤
      (k - j - 1) * Nat.card F + X (m - (k - j - 1)) :=
    BCq_fiber_prefix_X F (k - j - 1) R0 hbhd X hbndB i
  have hwe : weight (D.depB i - 1) (expTail (D.cB i)) =
      psum (expTail (D.cB i)) (D.depB i - 1) :=
    (psum_ge_depth (expTail (D.cB i)) (le_refl _)).symm
  by_cases hcase : D.depB i - 1 ≤ k - j - 1
  · exfalso
    have hb := hfib (k - j - 1)
    have hsub : (k - j - 1) - (k - j - 1) = 0 := by omega
    rw [hsub] at hb
    have hX0 : X 0 = 0 := by
      simp [X, psumSeq]
    rw [hX0, Nat.add_zero] at hb
    have hmono : psum (expTail (D.cB i)) (D.depB i - 1) ≤
        psum (expTail (D.cB i)) (k - j - 1) := psum_mono (expTail (D.cB i)) hcase
    rw [← hwe] at hmono
    omega
  · have hgt : k - j - 1 < D.depB i - 1 := lt_of_not_ge hcase
    have hb := hfib (D.depB i - 1)
    have hsub : (D.depB i - 1) - (k - j - 1) = D.depB i + j - k := by omega
    rw [hsub] at hb
    have ht1 : 1 ≤ D.depB i + j - k := by omega
    have htel := lemma29_X_telescope F r s k hk1 hkr hbig (D.depB i + j - k) ht1
    have hidx : k + (D.depB i + j - k) - 1 = D.depB i - 1 + j := by omega
    have hXeq : X (D.depB i + j - k) = psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) (D.depB i + j - k) := rfl
    rw [hXeq, htel, hidx] at hb
    -- hb : psum (expTail) (depB-1) ≤ n*q + ((s_k - 1) + (psum s (depB-1+j) - psum s k))
    rw [← hwe, hwid] at hb
    have hklt : k ≤ D.depB i - 1 + j := by omega
    have hpk' : psum s k = psum s (k - 1) + (s ⟨k - 1, by omega⟩ : ℕ) := hpk
    have hmono : psum s (k - 1) ≤ psum s r := psum_mono s (by omega)
    have hmono2 : psum s k ≤ psum s r := psum_mono s hkr
    have hle1 : psum s k ≤ psum s (D.depB i - 1 + j) := psum_mono s hklt
    by_contra hcon2
    have hltidx : D.depB i - 1 + j < r := by omega
    have hstrict := psum_lt_psum_of_lt s hltidx (le_refl r)
    omega

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ Type-2 member depth: strictly greater than `depth s` (paper Prop 2.12:
`depth(t') ≥ r+1`). -/
lemma type2_dep_gt (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      (∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
          psum s r - psum s (k - 1) - 1) →
      (∀ j' : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum
          (single (qMinusExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      r < Q.dep (Sum.inr (Sum.inl i)) := by
  classical
  intro D Bs Q i hXw hbndB
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inl i)) =
      Bs.dep (Sum.inr (Sum.inl i)) + (sPrefix r s j (by omega) (by omega)).length :=
    FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) _
  have hBsdep : Bs.dep (Sum.inr (Sum.inl i)) = D.depB i + 1 := by
    dsimp [Bs, ofBstarOver, D]
  have hdep : Q.dep (Sum.inr (Sum.inl i)) = j + D.depB i := by
    rw [hQdep, hBsdep, hlen]
    omega
  rw [hdep]
  have hwid : weight (D.depB i - 1) (expTail (D.cB i)) =
      (k - j - 1) * Nat.card F + (psum s r - psum s (k - 1) - 1) :=
    BCq_fiber_weight_X F (k - j - 1) R0 hbhd (psum s r - psum s (k - 1) - 1)
      (fun j' => hXw j') i
  have hfiber := fiber_dep_ge F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hwid hbndB
  simp only [D] at hfiber hdep
  omega

/-- ★ Type-3 member depth: at least `depth s` (paper Prop 2.12). -/
lemma type3_dep_ge (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      (∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
          psum s r - psum s (k - 1) - 1) →
      (∀ j' : R0.ιB, ∀ m : ℕ, psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum
          (single (qMinusExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) →
      r ≤ Q.dep (Sum.inr (Sum.inr i)) := by
  classical
  intro D Bs Q i hXw hbndB
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inr (Sum.inr i)) =
      Bs.dep (Sum.inr (Sum.inr i)) + (sPrefix r s j (by omega) (by omega)).length :=
    FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) _
  have hBsdep : Bs.dep (Sum.inr (Sum.inr i)) = D.depB i := by
    dsimp [Bs, ofBstarOver, D]
  have hdep : Q.dep (Sum.inr (Sum.inr i)) = (j - 1) + D.depB i := by
    rw [hQdep, hBsdep, hlen]
    omega
  rw [hdep]
  have hwid : weight (D.depB i - 1) (expTail (D.cB i)) =
      (k - j - 1) * Nat.card F + (psum s r - psum s (k - 1) - 1) :=
    BCq_fiber_weight_X F (k - j - 1) R0 hbhd (psum s r - psum s (k - 1) - 1)
      (fun j' => hXw j') i
  have hfiber := fiber_dep_ge F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hwid hbndB
  simp only [D] at hfiber hdep
  omega

end ZagierHoffmanPositiveChar
