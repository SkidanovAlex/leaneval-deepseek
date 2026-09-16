import Submission.ZagierHoffmanProof.StepL85
import Submission.ZagierHoffmanProof.StepL82
import Submission.ZagierHoffmanProof.StepL73
import Submission.ZagierHoffmanProof.StepL49
import Submission.ZagierHoffmanProof.StepL34
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L86: g53_case1_step — the level-3 j=0 (q,q)-front CASE-1 splice

SESSION 243.  ★ g53_case1_step: every in-domain (2-adm ∧ ¬3-adm) weight-w tuple
s with the all-q front s₀ = q ∧ s₁ = q and s₂ > q (3 ≤ r) expands at level 3
(AdmExpT F w 3 s), given the recursion hypothesis ih over Main3Step-smaller
in-domain weight-w tuples.  This is the CASE-1 j=0 step of main3 (prop212 has no
instance for the all-q front); main3's CASE-1 dispatch will call it in the
pad0 s 0 = q ∧ pad0 s 1 = q subcase.

STRUCTURE (StepL80's g5_case1_step script at k=3): rcases lemma_2_9_rel at
(r−3, w1, B) (w1 := w1Of, B := sTail — NOT lemma_2_9_config_data, which discards
the a-side LePad hleA needed for the a-member orders); derive the config-style
conjuncts (hc0 via bstarBase-simpa, hwtA/hhead/hXw via StepL34's calcs at k=3,
hbndB from hleB, the concrete a-prefix hpref from hleA); D := BCqIter F 2
(toData F R0); the chain ζ-identity hid0 via g53c1_zeta_core; the expansion
family {i : D.ιA // i ≠ u} ⊕ D.ιB with negated coefficients (the
sum_guarded_subtype' + Fintype.sum_sum_type fold); per-member: 3-adm →
admExpT_self (weights via g53c1_aSide_weight / g53c1_bSide_weight), ¬3-adm →
2-adm (g53c1_aSide_twoAdm / g53c1_bSide_twoAdm) + Main3Step (the strict prefix-3
drops) → ih; member orders horder from g53c1_aSide_order (hpref) and
g53c1_bSide_order (hbndB); splice by admExpT_combine.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]



/-! ## SESSION 243 — g53_case1_step: the level-3 j=0 (q,q)-front CASE-1 splice.

Mirror of StepL80's g5_case1_step at k=3: rcases lemma_2_9_rel at (r−3, w1, B)
(w1 := w1Of, B := sTail) so the a-side LePad hleA is retained; derive the
config-style conjuncts (hwtA/hhead/hXw/hbndB via StepL34's calcs) and the
concrete a-prefix hpref; D := BCqIter F 2 (toData F R0); hid0 via g53c1_zeta_core;
family {i : D.ιA // i ≠ u} ⊕ D.ιB with negated coefficients; per-member by_cases
3-adm → admExpT_self / ¬3-adm (2-adm + strict prefix-3 drop → Main3Step) → ih;
orders via g53c1_aSide_order / g53c1_bSide_order; splice by admExpT_combine. -/

/-- CASE-1 g53 step: in-domain head-(q,q) s with s₂ > q expands at level 3. -/
theorem g53_case1_step (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase3 : 3 ≤ r) (hbigp : (Nat.card F : ℕ) < pad0 s 2)
    (hs0p : pad0 s 0 = Nat.card F) (hs1p : pad0 s 1 = Nat.card F)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      Main3Step (Nat.card F) s m → kAdmissible (Nat.card F) m 2 →
      ¬ kAdmissible (Nat.card F) m 3 → AdmExpT F w 3 m) :
    AdmExpT F w 3 s := by
  classical
  have hs0v : (s ⟨0, by omega⟩ : ℕ) = Nat.card F := by
    have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    omega
  have hs1v : (s ⟨1, by omega⟩ : ℕ) = Nat.card F := by
    have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
    omega
  have hbigv : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ) := by
    have hp : pad0 s 2 = (s ⟨2, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 2 < r)
    omega
  have hsum : psum s 3 = psum s (3 - 1) + (s ⟨3 - 1, by omega⟩ : ℕ) := by
    exact psum_last r s 3 (by omega : 1 ≤ 3) hcase3
  have hmono : psum s 3 ≤ psum s r := psum_mono s hcase3
  have hmono2 : psum s (3 - 1) ≤ psum s r := psum_mono s (by omega : 3 - 1 ≤ r)
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  let w1 : ℕ+ := w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv
  let B : Fin (r - 3) → ℕ+ := sTail r s 3 hcase3
  rcases lemma_2_9_rel F (r - 3) w1 B with ⟨R0, u, hdep, ha, hc, hleA, hbhd, hleB, hvalid⟩
  have hdepu : R0.depA u = (r - 3) + 1 := hdep
  have hau : R0.aA u = 1 := ha
  have hc0 : ∀ hd : R0.depA u = (r - 3) + 1,
      (fun x : Fin ((r - 3) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv := by
    intro hd
    simpa [bstarBase, w1, B] using hc hd
  have hwtA : ∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) = psum s r - psum s (3 - 1) := by
    intro i hi
    have hL := hleA i hi
    have hw' : (w1 : ℕ) = (s ⟨3 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depA i) (R0.cA i)
          = weight 1 (single (qExp F)) + weight ((r - 3) + 1) (consVec w1 B) := hL.1.1
      _ = (qExp F : ℕ) + ((w1 : ℕ) + weight (r - 3) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = Nat.card F + ((w1 : ℕ) + (psum s r - psum s 3)) := by
            rw [show (qExp F : ℕ) = Nat.card F by rfl]
            rw [weight_sTail r s 3 hcase3]
      _ = psum s r - psum s (3 - 1) := by
            rw [hw']
            have hnorm : (s ⟨3 - 1, by omega⟩ : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨3 - 1, by omega⟩ : ℕ) := by
    intro i hi
    have hL2 := (hleA i hi).2
    have hwadd : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by
      dsimp [w1]
      exact w1Of_add F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv
    simpa [hwadd] using hL2
  have hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (3 - 1) - 1 := by
    intro j'
    have hL := hleB j'
    have hw' : (w1 : ℕ) = (s ⟨3 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depB j' - 1) (expTail (R0.cB j'))
          = weight 1 (single (qMinusExp F)) + weight ((r - 3) + 1) (consVec w1 B) := hL.1
      _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + weight (r - 3) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = (Nat.card F - 1) + ((w1 : ℕ) + (psum s r - psum s 3)) := by
            rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
            rw [weight_sTail r s 3 hcase3]
      _ = psum s r - psum s (3 - 1) - 1 := by
            rw [hw']
            have hnorm : (s ⟨3 - 1, by omega⟩ : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) m := by
    intro j' m
    have hL := hleB j'
    simpa [w1, B] using (hL.2 m)
  have hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) m := by
    intro i hi m
    have hL := (hleA i hi).1
    simpa [w1, B] using (hL.2 m)
  let D := RelData.BCqIter F 2 (toData F R0)
  have hid0 : ζ_A F s +
      (∑ i : D.ιA, (if i = u then 0 else
        (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) +
      (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (D.cB p))) = 0 := by
    exact g53c1_zeta_core F r s hcase3 hs0v hs1v hbigv R0 u hdepu hau hc0
  -- expansion family: a-members i ≠ u (subtype) ⊕ b-members
  let ι₁ : Type := {i : D.ιA // i ≠ u}
  letI : Fintype ι₁ :=
    Fintype.subtype ((Finset.univ : Finset D.ιA).filter (fun i => i ≠ u))
      (by intro x; simp [Finset.mem_filter])
  let ι : Type := ι₁ ⊕ D.ιB
  letI : Fintype ι := inferInstance
  let mdep (q : ι) : ℕ := match q with
    | Sum.inl a => D.depA a.1
    | Sum.inr p => D.depB p
  let mhdep (q : ι) : 0 < mdep q := by
    cases q with
    | inl a => dsimp [mdep]; exact D.hdepA a.1
    | inr p => dsimp [mdep]; exact D.hdepB p
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
  have hgu : (∑ i : D.ιA, (if i = u then 0 else
        (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) =
      (∑ a : ι₁, x₁ a) := by
    dsimp [x₁]
    exact sum_guarded_subtype' (u := u) (f := fun i : D.ιA =>
      (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))
  have h0z : ζ_A F s + ((∑ a : ι₁, x₁ a) + (∑ p : D.ιB, x₂ p)) = 0 := by
    rw [← hgu]
    simpa [add_assoc] using hid0
  have hneg : ζ_A F s = -((∑ a : ι₁, x₁ a) + (∑ p : D.ιB, x₂ p)) := by
    exact eq_neg_of_add_eq_zero_left h0z
  have hid : ζ_A F s = ∑ q : ι, (((ma q : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc q)) := by
    calc
      ζ_A F s = -(∑ a : ι₁, x₁ a) + -(∑ p : D.ιB, x₂ p) := by
        rw [hneg]
        rw [neg_add]
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
  -- per-member expansions
  have e : ∀ q : ι, AdmExpT F w 3 (mc q) := by
    intro q
    cases q with
    | inl a =>
        by_cases h3m : kAdmissible (Nat.card F) (D.cA a.1) 3
        · have hw1 : weight (D.depA a.1) (D.cA a.1) = w := by
            have hwv := g53c1_aSide_weight F r s hcase3 hs0v hs1v hbigv R0 u hau hwtA a.1 a.2
            rw [hwv]
            exact hw
          exact admExpT_self F w 3 (D.hdepA a.1) (D.cA a.1) hw1 h3m
        · have h2m : kAdmissible (Nat.card F) (D.cA a.1) 2 := by
            simpa using (g53c1_aSide_twoAdm F r s hcase3 hs0v hs1v hbigv R0 u a.1 a.2)
          have hstep : Main3Step (Nat.card F) s (D.cA a.1) := by
            have hpd' : psum (D.cA a.1) 3 < psum s 3 := by
              simpa using (g53c1_aSide_prefix_drop F r s hcase3 hs0v hs1v hbigv R0 u hhead a.1 a.2)
            exact Or.inl hpd'
          have hw1 : weight (D.depA a.1) (D.cA a.1) = w := by
            have hwv := g53c1_aSide_weight F r s hcase3 hs0v hs1v hbigv R0 u hau hwtA a.1 a.2
            rw [hwv]
            exact hw
          exact ih (D.depA a.1) (D.cA a.1) hw1 hstep h2m h3m
    | inr p =>
        by_cases h3m : kAdmissible (Nat.card F) (D.cB p) 3
        · have hw1 : weight (D.depB p) (D.cB p) = w := by
            have hwv := g53c1_bSide_weight F r s hcase3 hs0v hs1v hbigv R0 hbhd hXw p
            rw [hwv]
            exact hw
          exact admExpT_self F w 3 (D.hdepB p) (D.cB p) hw1 h3m
        · have h2m : kAdmissible (Nat.card F) (D.cB p) 2 := by
            simpa using (g53c1_bSide_twoAdm F r s hcase3 hs0v hs1v hbigv R0 hbhd hXw p)
          have hstep : Main3Step (Nat.card F) s (D.cB p) := by
            have hpd' : psum (D.cB p) 3 < psum s 3 := by
              simpa using (g53c1_bSide_prefix_drop F r s hcase3 hs0v hs1v hbigv R0 hbhd p)
            exact Or.inl hpd'
          have hw1 : weight (D.depB p) (D.cB p) = w := by
            have hwv := g53c1_bSide_weight F r s hcase3 hs0v hs1v hbigv R0 hbhd hXw p
            rw [hwv]
            exact hw
          exact ih (D.depB p) (D.cB p) hw1 hstep h2m h3m
  -- member orders ℓ ≥ 3
  have horder : ∀ q : ι, ∀ ℓ : ℕ, 3 ≤ ℓ → psum (mc q) ℓ ≤ psum s ℓ := by
    intro q ℓ hℓ
    cases q with
    | inl a =>
        have ho := g53c1_aSide_order F r s hcase3 hs0v hs1v hbigv R0 u hpref a.1 a.2 ℓ hℓ
        simpa using ho
    | inr p =>
        have ho := g53c1_bSide_order F r s hcase3 hs0v hs1v hbigv R0 hbhd hbndB p ℓ hℓ
        simpa using ho
  exact admExpT_combine F w 3 s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
