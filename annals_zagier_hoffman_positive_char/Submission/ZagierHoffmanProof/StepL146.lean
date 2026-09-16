import Submission.ZagierHoffmanProof.StepL145
import Submission.ZagierHoffmanProof.StepL108
set_option autoImplicit false
set_option maxHeartbeats 8000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L146: ★★ `maink_case1_j0` — the G5 (all-q-front) CASE-1 splice at symbolic `k`
(SESSION 259y) — StepL115 obligation (4)

Every weight-`w` in-domain tuple `s` with the all-q CASE-1 shape
(`pad0 s x = q` for all `x < k−1`, `s⟨k−1⟩ > q`, `k ≤ r`, `2 ≤ k`) expands at
level `k` in ORDERED form, given the WIDENED (β)-recursion hypothesis
`rec : MainkStep3 k q w s m → ¬(k-adm m) → (psum m k < psum s k ∨ k-adm m (k−1))
       → AdmExpT F w k m`
(SESSION 265 route (α)): the extra DISJUNCTION is discharged by this body for BOTH
member families from the strict prefix-`k` drops it already proves
(`maink_g5_aSide_prefix_drop` / `maink_g5_bSide_psum_lt`), i.e. the `Or.inl` side.

STRUCTURE (the generic-k port of StepL104's `g5T_case1` / StepL86's
`g53_case1_step`):
  • ONE `rcases maink_config_full` (StepL108) gives the full config package;
  • `D := BCqIter F (k−1) (toData R0)` and the chain ζ-identity `hid0` from
    `maink_g5_zeta_core` (StepL138) — `D.cA u' = s` (the leading a-member);
  • the two-family fold `ι₁ ⊕ D.ιB` (`sum_guarded_subtype'` +
    `Fintype.sum_sum_type` + `neg_coe_mul_zeta`) gives the members/coefficients
    (`ma = −aA`, `−aB`);
  • `horder` (prefix `≤ s` for all `ℓ ≥ k`) from `maink_g5_aSide_order`
    (StepL145) / `maink_g5_bSide_order` (StepL144);
  • per-member expansion `e`: k-adm → `admExpT_self`; else `rec` with
    `MainkStep3` from the strict prefix drop at `k`
    (`maink_g5_aSide_prefix_drop` StepL141 / `maink_g5_bSide_psum_lt` StepL144) —
    the DROP is the whole member analysis (no entry-level bounds needed);
  • splice by `admExpT_combine`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ The CASE-1 j = 0 (all-q front) splice at symbolic `k`: StepL115 obligation (4). -/
theorem maink_case1_j0 (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) (hkr : k ≤ r)
    (hbigv : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      MainkStep3 k (Nat.card F) w s m → ¬ kAdmissible (Nat.card F) m k →
      (psum m k < psum s k ∨ kAdmissible (Nat.card F) m (k - 1)) →
      AdmExpT F w k m) :
    AdmExpT F w k s := by
  classical
  rcases maink_config_full F k r s hk1 hkr hbigv with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB, hpref, _⟩
  let D := RelData.BCqIter F (k - 1) (toData F R0)
  let u' := RelData.iterIdx F (k - 1) (toData F R0) u
  have hid0 : ζ_A F s +
      (∑ i : D.ιA, (if i = u' then 0 else
        (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) +
      (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (D.cB p))) = 0 := by
    exact maink_g5_zeta_core F r s k hk1 hkr hallq hbigv R0 u hdepu hau hc0
  -- the two-family expansion carrier {a-members i ≠ u'} ⊕ {b-members}
  let ι₁ : Type := {i : D.ιA // i ≠ u'}
  letI : Fintype ι₁ :=
    Fintype.subtype ((Finset.univ : Finset D.ιA).filter (fun i => i ≠ u'))
      (by intro x; simp [Finset.mem_filter])
  let ι : Type := ι₁ ⊕ D.ιB
  letI : Fintype ι := inferInstance
  let mdep (q : ι) : ℕ := match q with
    | Sum.inl a => D.depA a.1
    | Sum.inr p => D.depB p
  let mhdep (q : ι) : 0 < mdep q := by
    cases q with
    | inl a => exact D.hdepA a.1
    | inr p => exact D.hdepB p
  let mc (q : ι) : Fin (mdep q) → ℕ+ := match q with
    | Sum.inl a => D.cA a.1
    | Sum.inr p => D.cB p
  let ma (q : ι) : RatFunc F := match q with
    | Sum.inl a => -(D.aA a.1)
    | Sum.inr p => -(D.aB p)
  let x₁ (a : ι₁) : RatFunc.CompletionAtInfty F :=
    (((D.aA a.1 : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA a.1))
  let x₂ (p : D.ιB) : RatFunc.CompletionAtInfty F :=
    (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cB p))
  have hgu : (∑ i : D.ιA, (if i = u' then 0 else
        (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) =
      (∑ a : ι₁, x₁ a) := by
    dsimp [x₁]
    exact sum_guarded_subtype' (u := u') (f := fun i : D.ιA =>
      (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))
  have h0z : ζ_A F s + ((∑ a : ι₁, x₁ a) + (∑ p : D.ιB, x₂ p)) = 0 := by
    rw [← hgu]
    simpa [add_assoc] using hid0
  have hneg : ζ_A F s = -((∑ a : ι₁, x₁ a) + (∑ p : D.ιB, x₂ p)) :=
    eq_neg_of_add_eq_zero_left h0z
  have hid : ζ_A F s = ∑ q : ι,
      (((ma q : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc q)) := by
    calc
      ζ_A F s = -(∑ a : ι₁, x₁ a) + -(∑ p : D.ιB, x₂ p) := by
        rw [hneg, neg_add]
      _ = ∑ q : ι, (match q with
            | Sum.inl a => -(x₁ a) | Sum.inr p => -(x₂ p)) := by
        rw [Fintype.sum_sum_type]
        simp [Finset.sum_neg_distrib]
      _ = ∑ q : ι, (((ma q : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc q)) := by
        apply Finset.sum_congr rfl
        intro q hq
        cases q with
        | inl a =>
            dsimp [x₁, ma, mc]
            exact (neg_coe_mul_zeta F (D.aA a.1) (D.cA a.1)).symm
        | inr p =>
            dsimp [x₂, ma, mc]
            exact (neg_coe_mul_zeta F (D.aB p) (D.cB p)).symm
  -- the per-member order condition
  have horder : ∀ q : ι, ∀ ℓ : ℕ, k ≤ ℓ → psum (mc q) ℓ ≤ psum s ℓ := by
    intro q ℓ hℓ
    cases q with
    | inl a =>
        exact maink_g5_aSide_order F r s k hk1 hkr hbigv hallq R0 u hpref a.1 a.2 ℓ hℓ
    | inr p =>
        exact maink_g5_bSide_order F r s k hk1 hkr hbigv hallq R0 hbhd hbndB p ℓ hℓ
  -- the per-member expansion
  have e : ∀ q : ι, AdmExpT F w k (mc q) := by
    intro q
    cases q with
    | inl a =>
        have hwk : weight (D.depA a.1) (D.cA a.1) = w := by
          have hwv := maink_g5_aSide_weight F r s k hk1 hkr hallq R0 u hwtA a.1 a.2
          rw [hwv]
          exact hw
        by_cases hkadm : kAdmissible (Nat.card F) (D.cA a.1) k
        · exact admExpT_self F w k (D.hdepA a.1) (D.cA a.1) hwk hkadm
        · refine rec (D.depA a.1) (D.cA a.1) hwk (Or.inl ?_) hkadm (Or.inl ?_)
          · exact maink_g5_aSide_prefix_drop F r s k hk1 hkr hallq R0 u hhead a.1 a.2
          · exact maink_g5_aSide_prefix_drop F r s k hk1 hkr hallq R0 u hhead a.1 a.2
    | inr p =>
        have hwk : weight (D.depB p) (D.cB p) = w := by
          have hwv := maink_g5_bSide_weight F r s k hk1 hkr hallq R0 hbhd hXw p
          rw [hwv]
          exact hw
        by_cases hkadm : kAdmissible (Nat.card F) (D.cB p) k
        · exact admExpT_self F w k (D.hdepB p) (D.cB p) hwk hkadm
        · refine rec (D.depB p) (D.cB p) hwk (Or.inl ?_) hkadm (Or.inl ?_)
          · exact maink_g5_bSide_psum_lt F r s k hk1 hkr hbigv hallq R0 hbhd hbndB p
          · exact maink_g5_bSide_psum_lt F r s k hk1 hkr hbigv hallq R0 hbhd hbndB p
  exact admExpT_combine F w k s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
