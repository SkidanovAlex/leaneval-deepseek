import Submission.ZagierHoffmanProof.StepL191
import Submission.ZagierHoffmanProof.StepL49
import Submission.ZagierHoffmanProof.StepL51

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L192: the level-1 chain as an AMBIENT port

`maink_case1_level1_amb`: an input `s` with `q < s_1` expands at EVERY ambient level
`Lam >= 1`, given the ambient recursion hypothesis for chain members that are not
`Lam`-admissible.  The chain is Lemma 2.9's at `(r-1, s_1 - q, s_2..s_r)` (the
`s_1 > q` branch of `H1_expT`), its members are the `a`-members `ca i` and the
`b`-members `1 :: cb j`, their prefix orders at `ell >= 1` are `aSide_order` /
`bMember_order`, and their ambient descents are StepL191's two lemmas.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The level-1 chain at an ambient level: a tuple whose head exceeds `q` expands at
every ambient level `Lam >= 1`. -/
theorem maink_case1_level1_amb (w : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+)
    (hw : weight r s = w) (hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ))
    (Lam : ℕ) (hLam : 1 ≤ Lam)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      ambNu Lam (Nat.card F) w m < ambNu Lam (Nat.card F) w s →
        ¬ kAdmissible (Nat.card F) m Lam → AdmExpT F w Lam m) :
    AdmExpT F w Lam s := by
  classical
  let w1 : ℕ+ := ⟨(s ⟨0, hr⟩ : ℕ) - Nat.card F, by omega⟩
  rcases lemma_2_9_zeta F (r - 1) w1 (expTail s) with
    ⟨ιa, fina, depa, hdepa, ca, aA, ιb, finb, depb, hdepb, cb, bB, hleA, hleB, hid⟩
  letI : Fintype ιa := fina
  letI : Fintype ιb := finb
  have hlead : ζ_A F (consVec ⟨(qExp F : ℕ) + (w1 : ℕ),
      Nat.add_pos_left (PNat.pos (qExp F)) (w1 : ℕ)⟩ (expTail s)) = ζ_A F s := by
    simpa [w1] using (zeta_leading_eq_s F r hr s hgt)
  have hid0 : ζ_A F s +
      (∑ i : ιa, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) +
      (∑ j : ιb, (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (consVec oneExp (cb j)))) = 0 := by
    rw [hlead] at hid
    simpa [w1] using hid
  have hneg : ζ_A F s = -((∑ i : ιa, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) +
      (∑ j : ιb, (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (consVec oneExp (cb j))))) := by
    have hz := eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hid0)
    exact hz
  let ιc : Type := ιa ⊕ ιb
  letI : Fintype ιc := inferInstance
  let depc : ιc → ℕ := fun p => match p with | Sum.inl i => depa i | Sum.inr j => depb j + 1
  have hdepc : ∀ p : ιc, 0 < depc p := by
    intro p
    cases p with
    | inl i => dsimp [depc]; exact hdepa i
    | inr j => dsimp [depc]; omega
  let cc : ∀ p : ιc, Fin (depc p) → ℕ+ := fun p => match p with
    | Sum.inl i => ca i
    | Sum.inr j => consVec oneExp (cb j)
  let ac : ιc → RatFunc F := fun p => match p with
    | Sum.inl i => -(aA i)
    | Sum.inr j => -(bB j)
  have hidc : ζ_A F s = ∑ p : ιc, (((ac p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (cc p)) := by
    rw [Fintype.sum_sum_type]
    dsimp [ac, cc]
    rw [hneg]
    rw [neg_add]
    congr 2
    · calc
        -((∑ i : ιa, (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))))
            = (∑ i : ιa, -(((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) := by
              exact (Finset.sum_neg_distrib (s := Finset.univ) (fun i : ιa =>
                (((aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i)))).symm
        _ = (∑ i : ιa, (((-aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (ca i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hcast : (((-aA i : RatFunc F) : RatFunc.CompletionAtInfty F) =
                  -((aA i : RatFunc F) : RatFunc.CompletionAtInfty F)) := by
                change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-aA i)) =
                  -(algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (aA i))
                rw [map_neg]
              rw [hcast]
              ring
    · calc
        -((∑ j : ιb, (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (consVec oneExp (cb j)))))
            = (∑ j : ιb, -(((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                ζ_A F (consVec oneExp (cb j)))) := by
              exact (Finset.sum_neg_distrib (s := Finset.univ) (fun j : ιb =>
                (((bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
                  ζ_A F (consVec oneExp (cb j))))).symm
        _ = (∑ j : ιb, (((-bB j : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (consVec oneExp (cb j)))) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hcast : (((-bB j : RatFunc F) : RatFunc.CompletionAtInfty F) =
                  -((bB j : RatFunc F) : RatFunc.CompletionAtInfty F)) := by
                change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-bB j)) =
                  -(algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (bB j))
                rw [map_neg]
              rw [hcast]
              ring
  have horder : ∀ p : ιc, ∀ (ℓ : ℕ), Lam ≤ ℓ → psum (cc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    have h1 : 1 ≤ ℓ := le_trans hLam hℓ
    cases p with
    | inl i => exact aSide_order F hr s hgt depa hdepa ca hleA i ℓ h1
    | inr j => exact bMember_order F hr s hgt depb hdepb cb hleB j ℓ h1
  have e : ∀ p : ιc, AdmExpT F w Lam (cc p) := by
    intro p
    cases p with
    | inl i =>
        have hw' : weight (depa i) (ca i) = w :=
          (aSide_weight_lt F r hr s hgt depa hdepa ca hleA i).1.trans hw
        by_cases hk : kAdmissible (Nat.card F) (ca i) Lam
        · exact admExpT_self F w Lam (hdepa i) (ca i) hw' hk
        · exact rec (depa i) (ca i) hw'
            (level1_aMember_amb_step F Lam w hLam hr s hw hgt depa hdepa ca hleA i) hk
    | inr j =>
        have hw' : weight (depb j + 1) (consVec oneExp (cb j)) = w :=
          (head_one_weight F r hr s hgt depb hdepb cb hleB j).trans hw
        by_cases hk : kAdmissible (Nat.card F) (consVec oneExp (cb j)) Lam
        · exact admExpT_self F w Lam (by omega : 0 < depb j + 1) (consVec oneExp (cb j)) hw' hk
        · exact rec (depb j + 1) (consVec oneExp (cb j)) hw'
            (level1_bMember_amb_step F Lam w hLam hr s hw hgt depb hdepb cb hleB j) hk
  exact admExpT_combine F w Lam s depc hdepc cc ac hidc horder e

end ZagierHoffmanPositiveChar
