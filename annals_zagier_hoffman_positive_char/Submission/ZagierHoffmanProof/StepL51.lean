import Submission.ZagierHoffmanProof.StepL50

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L51: H1_expT — the strengthened H₁ (R(1)) with per-output prefix-orders

`H1_expT` is StepL37's `H1_exp` re-run at the `AdmExpT` level: every tuple `s` of
positive depth has a level-`1` expansion whose outputs `c` are `1`-admissible of
weight `weight r s` AND satisfy `psum c ℓ ≤ psum s ℓ` for every `ℓ ≥ 1` (the base
`R(1)` of the strengthened `(H'_k)` hierarchy).  Structure mirrors `H1_exp`:
strong induction on `s₁`; `s₁ ≤ q`: admissible (self) except the depth-1 `(q)`
case resolved by R1 (`(1,q−1)` output — its prefix-`ℓ ≥ 1` order vs `(q)` is
`pair_one_qminus_order`); `s₁ > q`: the Lemma-2.9 CW with the `a`-members expanded
by the IH and the `b`-members `(1::cb j)` by `admExpT_self`, spliced by
`admExpT_combine` with the per-member orders `aSide_order`/`bMember_order`
(StepL50).  The R1-output order works even though the R1-output Init is smaller
(SESSION-190): the prefix-`ℓ` sums are `1 ≤ q` at `ℓ=1` and `q = q` beyond.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The R1 output `(1,q−1)` is prefix-`≤` the input `(q)` at every `ℓ ≥ 1`. -/
lemma pair_one_qminus_order (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    psum (pair oneExp (qMinusExp F)) ℓ ≤ psum (single (qExp F)) ℓ := by
  classical
  have hq := psum_single_of_pos (qExp F) hℓ
  by_cases h1 : ℓ = 1
  · subst ℓ
    rw [hq]
    have hp1 : psum (pair oneExp (qMinusExp F)) 1 = 1 := by
      change (∑ x ∈ Finset.range 1, pad0 (pair oneExp (qMinusExp F)) x) = 1
      rw [Finset.sum_range_one]
      have h00 : 0 < 2 := by omega
      have hp : pad0 (pair oneExp (qMinusExp F)) 0 =
          ((pair oneExp (qMinusExp F)) ⟨0, h00⟩ : ℕ) := pad0_of_lt (pair oneExp (qMinusExp F)) h00
      rw [hp]
      have hc := congrArg (fun t : ℕ+ => (t : ℕ)) (pair_zero oneExp (qMinusExp F))
      rw [hc]
      rfl
    rw [hp1]
    have hq1 : 1 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    have hqe : (qExp F : ℕ) = Nat.card F := by rfl
    rw [hqe]
    omega
  · have hℓ2 : 2 ≤ ℓ := by omega
    rw [hq]
    have hd : psum (pair oneExp (qMinusExp F)) ℓ =
        weight 2 (pair oneExp (qMinusExp F)) := psum_ge_depth (pair oneExp (qMinusExp F)) hℓ2
    rw [hd]
    have hw := weight_pair oneExp (qMinusExp F)
    have hq1 : 1 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := card_ge_two F
      omega
    have hw' : weight 2 (pair oneExp (qMinusExp F)) = Nat.card F := by
      rw [hw]
      rw [show (oneExp : ℕ) = 1 by rfl]
      rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
      omega
    rw [hw']
    rfl

/-- ★ Prop 3.2 at k = 1, strengthened: every tuple has a level-1 expansion whose
outputs are prefix-`≤` it at every `ℓ ≥ 1`. -/
theorem H1_expT (r : ℕ) (hr : 0 < r) (s : Fin r → ℕ+) : AdmExpT F (weight r s) 1 s := by
  classical
  have hmainT : ∀ (v : ℕ) {r : ℕ} (hr : 0 < r) (s : Fin r → ℕ+),
      (s ⟨0, hr⟩ : ℕ) = v → AdmExpT F (weight r s) 1 s := by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih =>
        intro r hr s hv
        let q : ℕ := Nat.card F
        let s1 : ℕ := (s ⟨0, hr⟩ : ℕ)
        have hq1 : 1 ≤ q := by
          have h2 : 2 ≤ Nat.card F := card_ge_two F
          omega
        by_cases hle : s1 ≤ q
        · by_cases hdq : r = 1 ∧ s1 = q
          · -- s = (q): R1, output (1,q−1) with its prefix-order
            have hr1 : r = 1 := hdq.1
            have hq' : (s ⟨0, hr⟩ : ℕ) = q := hdq.2
            subst r
            have hmain1 : AdmExpT F q 1 (single (qExp F)) := by
              have hdepP : ∀ i : PUnit, 0 < (2 : ℕ) := fun i => by omega
              refine ⟨PUnit, inferInstance, (fun _ : PUnit => 2), hdepP,
                (fun _ : PUnit => pair oneExp (qMinusExp F)), (fun _ : PUnit => -D1rat F), ?_, ?_, ?_, ?_⟩
              · intro i
                rw [weight_pair]
                rw [show (oneExp : ℕ) = 1 by rfl]
                rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
                have hq1' : 1 ≤ Nat.card F := by
                  have h2 : 2 ≤ Nat.card F := card_ge_two F
                  omega
                omega
              · intro i
                exact kAdm1_pair_one (Nat.card F) (qMinusExp F) (by
                  have h2 : 2 ≤ Nat.card F := card_ge_two F
                  omega)
              · intro i ℓ hℓ
                exact pair_one_qminus_order F ℓ hℓ
              · have hcast : (((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) =
                    -(D1rat F : RatFunc.CompletionAtInfty F)) := by
                  change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (-D1rat F)) =
                    -(algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (D1rat F))
                  rw [map_neg]
                have hmain1c : ζ_A F (single (qExp F)) =
                    ((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
                      ζ_A F (pair oneExp (qMinusExp F)) := by
                  calc
                    ζ_A F (single (qExp F))
                        = -(D1c F * ζ_A F (pair oneExp (qMinusExp F))) := by
                          exact eq_neg_of_add_eq_zero_left (zeta_R1 F)
                    _ = ((-D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
                          ζ_A F (pair oneExp (qMinusExp F)) := by
                          rw [hcast]
                          have hd : (D1rat F : RatFunc.CompletionAtInfty F) = D1c F := D1c_eq_D1rat F
                          rw [hd]
                          ring
                simpa using hmain1c
            have hw' : weight 1 s = q := by
              change (∑ i : Fin 1, (s i : ℕ)) = q
              rw [Finset.sum_fin_eq_sum_range]
              rw [Finset.sum_range_one]
              simpa using hq'
            have hsingle : ζ_A F s = ζ_A F (single (qExp F)) := by
              apply congrArg (ζ_A F)
              funext i
              change s i = qExp F
              apply Subtype.ext
              have hqexp : (qExp F : ℕ) = Nat.card F := by rfl
              have hs : (s i : ℕ) = (qExp F : ℕ) := by
                have hi0 : i = ⟨0, by omega⟩ := by
                  apply Fin.ext
                  simp
                rw [hi0]
                rw [hqexp]
                simpa [q] using hq'
              exact hs
            have hseq : s = single (qExp F) := by
              funext i
              apply Subtype.ext
              have hi0 : i = ⟨0, by omega⟩ := by
                apply Fin.ext
                simp
              rw [hi0]
              change (s ⟨0, hr⟩ : ℕ) = (qExp F : ℕ)
              have hqe : (qExp F : ℕ) = Nat.card F := by rfl
              rw [hqe]
              dsimp [q] at hq'
              simpa using hq'
            have hqs : ∀ (ℓ : ℕ), 1 ≤ ℓ → psum (single (qExp F)) ℓ = psum s ℓ := by
              intro ℓ hℓ
              rw [hseq]
            have htrans : AdmExpT F q 1 s := by
              rcases hmain1 with ⟨ι, fin, dep, hdep, c, a, hwt, hadm, horder, hid⟩
              refine ⟨ι, fin, dep, hdep, c, a, hwt, hadm, ?_, ?_⟩
              · intro i ℓ hℓ
                exact le_trans (horder i ℓ hℓ) (le_of_eq (hqs ℓ hℓ))
              · rw [hsingle]
                exact hid
            exact admExpT_weight_transport F (weight 1 s) q 1 s rfl htrans hw'.symm
          · -- s₁ ≤ q and not (r=1 ∧ s₁=q): s is 1-admissible
            have hadm : kAdmissible (Nat.card F) s 1 := by
              constructor
              · intro x hx
                have hx0 : x = 0 := by omega
                subst x
                change pad0 s 0 ≤ Nat.card F
                have hp : pad0 s 0 = (s ⟨0, hr⟩ : ℕ) := pad0_of_lt s hr
                rw [hp]
                dsimp [s1, q] at hle
                exact hle
              · intro hc2
                rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
                apply hdq
                constructor
                · omega
                · dsimp [s1, q]
                  have hr1' : r = 1 := by omega
                  subst r
                  simpa using hlast
            exact admExpT_self F (weight r s) 1 hr s rfl hadm
        · -- q < s₁
          have hgt : (Nat.card F : ℕ) < (s ⟨0, hr⟩ : ℕ) := by
            dsimp [q, s1] at hle
            omega
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
          -- per-member strengthened expansions
          have e : ∀ p : ιc, AdmExpT F (weight r s) 1 (cc p) := by
            intro p
            cases p with
            | inl i =>
                have ha := aSide_weight_lt F r hr s hgt depa hdepa ca hleA i
                have hfirst : ((ca i) ⟨0, hdepa i⟩ : ℕ) < v := by
                  simpa [hv] using ha.2
                have hw' : weight (depa i) (ca i) = weight r s := ha.1
                have hih := ih (((ca i) ⟨0, hdepa i⟩ : ℕ)) hfirst (r := depa i) (hdepa i) (ca i) rfl
                exact admExpT_weight_transport F (weight r s) (weight (depa i) (ca i)) 1 (ca i) hw' hih hw'
            | inr j =>
                have hwj := head_one_weight F r hr s hgt depb hdepb cb hleB j
                have h1ad : kAdmissible (Nat.card F) (consVec oneExp (cb j)) 1 := by
                  constructor
                  · intro x hx
                    have hx0 : x = 0 := by omega
                    subst x
                    change pad0 (consVec oneExp (cb j)) 0 ≤ Nat.card F
                    have h00 : 0 < depb j + 1 := by omega
                    have hp : pad0 (consVec oneExp (cb j)) 0 =
                        ((consVec oneExp (cb j)) ⟨0, h00⟩ : ℕ) :=
                      pad0_of_lt (consVec oneExp (cb j)) h00
                    rw [hp]
                    have hc := congrArg (fun t : ℕ+ => (t : ℕ)) (consVec_zero oneExp (cb j))
                    rw [hc]
                    exact hq1
                  · intro hc2
                    rcases hc2 with ⟨hr1, hrk, hall, hlast⟩
                    have hd := hdepb j
                    omega
                exact admExpT_self F (weight r s) 1 (by omega : 0 < depb j + 1) (consVec oneExp (cb j)) hwj h1ad
          -- per-member prefix-orders vs s
          have horder : ∀ p : ιc, ∀ (ℓ : ℕ), 1 ≤ ℓ → psum (cc p) ℓ ≤ psum s ℓ := by
            intro p ℓ hℓ
            cases p with
            | inl i => exact aSide_order F hr s hgt depa hdepa ca hleA i ℓ hℓ
            | inr j => exact bMember_order F hr s hgt depb hdepb cb hleB j ℓ hℓ
          -- assemble
          exact admExpT_combine F (weight r s) 1 s depc hdepc cc ac hidc horder e
  exact hmainT (s ⟨0, hr⟩ : ℕ) hr s rfl

end ZagierHoffmanPositiveChar
