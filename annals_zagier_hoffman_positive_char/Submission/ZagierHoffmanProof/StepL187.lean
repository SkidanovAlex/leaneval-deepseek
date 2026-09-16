import Submission.ZagierHoffmanProof.StepL186
import Submission.ZagierHoffmanProof.StepL173
import Submission.ZagierHoffmanProof.StepL146

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L187: ★★ `maink_case1_j0_amb` — the G5 (all-`q` front) CASE-1 splice at an AMBIENT level

The third and last ambient chain port: the `maink_case1_j0` splice (StepL146) runs at its own
level `k` with `Λ`-admissible outputs and the AMBIENT `ambNu Λ` descent, supplied by
StepL172 (`maink_g5_aSide_amb_step`, depth `≥ r`, else prefix drop, else `InitLt`, else entry
drop) and StepL173 (`maink_g5_bSide_amb_step`, STRICTLY deeper members).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem maink_case1_j0_amb (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : 2 ≤ k) (hkr : k ≤ r)
    (hbigv : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (Λ : ℕ) (hΛ : k ≤ Λ)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (_hm : weight r' m = w),
      ¬ kAdmissible (Nat.card F) m Λ →
      (psum m k < psum s k ∨ kAdmissible (Nat.card F) m (k - 1)) →
      ambNu Λ (Nat.card F) w m < ambNu Λ (Nat.card F) w s →
      AdmExpT F w Λ m) :
    AdmExpT F w Λ s := by
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
  have horder : ∀ q : ι, ∀ ℓ : ℕ, Λ ≤ ℓ → psum (mc q) ℓ ≤ psum s ℓ := by
    intro q ℓ hℓ
    have hkℓ : k ≤ ℓ := le_trans hΛ hℓ
    cases q with
    | inl a =>
        exact maink_g5_aSide_order F r s k hk1 hkr hbigv hallq R0 u hpref a.1 a.2 ℓ hkℓ
    | inr p =>
        exact maink_g5_bSide_order F r s k hk1 hkr hbigv hallq R0 hbhd hbndB p ℓ hkℓ
  -- the per-member expansion
  have e : ∀ q : ι, AdmExpT F w Λ (mc q) := by
    intro q
    cases q with
    | inl a =>
        have hwk : weight (D.depA a.1) (D.cA a.1) = w := by
          have hwv := maink_g5_aSide_weight F r s k hk1 hkr hallq R0 u hwtA a.1 a.2
          rw [hwv]
          exact hw
        by_cases hkadm : kAdmissible (Nat.card F) (D.cA a.1) Λ
        · exact admExpT_self F w Λ (D.hdepA a.1) (D.cA a.1) hwk hkadm
        · refine rec (D.depA a.1) (D.cA a.1) hwk hkadm
            (Or.inl (maink_g5_aSide_prefix_drop F r s k hk1 hkr hallq R0 u hhead a.1 a.2)) ?_
          exact maink_g5_aSide_amb_step F r s k hk1 hkr hbigv hallq R0 u hhead hwtA hpref a.1 a.2
            w hw Λ hΛ
    | inr p =>
        have hwk : weight (D.depB p) (D.cB p) = w := by
          have hwv := maink_g5_bSide_weight F r s k hk1 hkr hallq R0 hbhd hXw p
          rw [hwv]
          exact hw
        by_cases hkadm : kAdmissible (Nat.card F) (D.cB p) Λ
        · exact admExpT_self F w Λ (D.hdepB p) (D.cB p) hwk hkadm
        · refine rec (D.depB p) (D.cB p) hwk hkadm
            (Or.inl (maink_g5_bSide_psum_lt F r s k hk1 hkr hbigv hallq R0 hbhd hbndB p)) ?_
          exact maink_g5_bSide_amb_step F r s k hk1 hkr hbigv hallq R0 hbhd hXw hbndB p w hw Λ hΛ
  exact admExpT_combine F w Λ s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
