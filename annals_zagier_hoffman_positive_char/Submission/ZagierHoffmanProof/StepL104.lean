import Submission.ZagierHoffmanProof.StepL103
import Submission.ZagierHoffmanProof.StepL80
import Submission.ZagierHoffmanProof.StepL99
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L104: ★ g5T_case1 — the ORDERED (q, s₂>q, …) CASE-1 j=0 splice at
level 2 (SESSION 253)


theorem g5T_case1 (w r s hw) (hcase : 2 ≤ r) (hbigp : q < pad0 s 1)
(hs0p : pad0 s 0 = q) (ih : ∀ r' m hm, kAdm1 m → ¬ kAdm2 m → pad0 m 0 = q →
  l2μ q m < l2μ q s → AdmExpT F w 2 m) : AdmExpT F w 2 s
— the in-domain (q, s₂>q, …) weight-w tuple expands at level 2 WITH prefix
orders, via the j=0 chain D := BCqIter F 1 (toData R0) over ONE rcases of
lemma_2_9_rel at (r−2, w1Of-at-2, sTail-at-2) (keeps hleA/hleB; hsum/hmono/hq1
preamble + the StepL99 config-conjunct derivations hdepu..hpref);
hid via g5c1_zeta_core; the 2-family fold {i ≠ u} ⊕ D.ιB (hgu + eq_neg +
Fintype.sum_sum_type + neg_coe_mul_zeta); per-member e (AdmExpT dispatch: a-members
2-adm → admExpT_self / ¬2-adm → 1-adm (head-q + depth ≥ 2) + head-q +
g5c1_aSide_prefix_drop l2μ-drop → ih; b-members via g5c1_bSide_twoAdm →
admExpT_self; weights via g5c1_aSide_weight/g5c1_bSide_weight); horder (ℓ ≥ 2)
via StepL103's g5T1_aSide_order/bSide_order (ℓ ≤ r) + ℓ > r weight
saturation; splice by admExpT_combine F w 2 s.
NEXT: g5T_total := l2_induction (P incl. pad0 m 0 = q) with per-step inDomain2_cases
dispatch → g5T_case1 (CASE-1 j=0) / g5T_case2 (CASE-2 (q,q)) (mirror StepL80's
g5_total at the AdmExpT level), then main2T := main2T_of_g5T g5T_total, then
A2T_from_main2T/A3_from_main2T (StepL97) make A(1,2,3)@w UNCONDITIONAL.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem g5T_case1 (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigp : (Nat.card F : ℕ) < pad0 s 1) (hs0p : pad0 s 0 = Nat.card F)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      pad0 m 0 = Nat.card F → l2μ (Nat.card F) m < l2μ (Nat.card F) s →
      AdmExpT F w 2 m) :
    AdmExpT F w 2 s := by
  classical
  have hk1 : 1 ≤ 2 := by omega
  have hs0v : (s ⟨0, by omega⟩ : ℕ) = Nat.card F := by
    have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    omega
  have hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ) :=
    case1_pad0_big_of_value F s hcase hbigp
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hsum : psum s 2 = psum s (2 - 1) + (s ⟨1, by omega⟩ : ℕ) := by
    have hpl := psum_last r s 2 (by omega : 1 ≤ 2) hcase
    simpa using hpl
  have hmono : psum s 2 ≤ psum s r := psum_mono s hcase
  have hmono2 : psum s (2 - 1) ≤ psum s r := psum_mono s (by omega : 2 - 1 ≤ r)
  let w1 : ℕ+ := w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbigv
  let B : Fin (r - 2) → ℕ+ := sTail r s 2 hcase
  rcases lemma_2_9_rel F (r - 2) w1 B with ⟨R0, u, hdep, ha, hc, hleA, hbhd, hleB, hvalid⟩
  have hdepu : R0.depA u = (r - 2) + 1 := hdep
  have hau : R0.aA u = 1 := ha
  have hc0 : ∀ hd : R0.depA u = (r - 2) + 1,
      (fun x : Fin ((r - 2) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 2 (by omega : 1 ≤ 2) hcase hbigv := by
    intro hd
    simpa [bstarBase, w1, B] using hc hd
  have hwtA : ∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) = psum s r - psum s (2 - 1) := by
    intro i hi
    have hL := hleA i hi
    have hw' : (w1 : ℕ) = (s ⟨2 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depA i) (R0.cA i)
          = weight 1 (single (qExp F)) + weight ((r - 2) + 1) (consVec w1 B) := hL.1.1
      _ = (qExp F : ℕ) + ((w1 : ℕ) + weight (r - 2) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = Nat.card F + ((w1 : ℕ) + (psum s r - psum s 2)) := by
            rw [show (qExp F : ℕ) = Nat.card F by rfl]
            rw [weight_sTail r s 2 hcase]
      _ = psum s r - psum s (2 - 1) := by
            rw [hw']
            have hnorm : (s ⟨2 - 1, by omega⟩ : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨2 - 1, by omega⟩ : ℕ) := by
    intro i hi
    have hL2 := (hleA i hi).2
    have hwadd : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by
      dsimp [w1]
      exact w1Of_add F r s 2 (by omega : 1 ≤ 2) hcase hbigv
    have hL2' : ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨1, by omega⟩ : ℕ) := by
      simpa [hwadd] using hL2
    have hnorm : (s ⟨2 - 1, by omega⟩ : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by rfl
    rw [hnorm]
    exact hL2'
  have hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (2 - 1) - 1 := by
    intro j'
    have hL := hleB j'
    have hw' : (w1 : ℕ) = (s ⟨2 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depB j' - 1) (expTail (R0.cB j'))
          = weight 1 (single (qMinusExp F)) + weight ((r - 2) + 1) (consVec w1 B) := hL.1
      _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + weight (r - 2) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = (Nat.card F - 1) + ((w1 : ℕ) + (psum s r - psum s 2)) := by
            rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
            rw [weight_sTail r s 2 hcase]
      _ = psum s r - psum s (2 - 1) - 1 := by
            rw [hw']
            have hnorm : (s ⟨2 - 1, by omega⟩ : ℕ) = (s ⟨1, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbigv) (sTail r s 2 hcase))) m := by
    intro j' m
    have hL := hleB j'
    simpa [w1, B] using (hL.2 m)
  have hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 2 (by omega : 1 ≤ 2) hcase hbigv) (sTail r s 2 hcase))) m := by
    intro i hi m
    have hL := (hleA i hi).1
    simpa [w1, B] using (hL.2 m)
  
  let D := RelData.BCqIter F 1 (toData F R0)
  have hid0 : ζ_A F s +
      (∑ i : D.ιA, (if i = u then 0 else
        (((D.aA i : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cA i)))) +
      (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (D.cB p))) = 0 := by
    exact g5c1_zeta_core F r s hcase hs0v hbigv R0 u hdepu hau hc0
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
  -- the two K∞ sums of the identity (unguarded)
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
  have e : ∀ q : ι, AdmExpT F w 2 (mc q) := by
    intro q
    cases q with
    | inl a =>
        -- a-member: by_cases 2-adm
        by_cases h2m : kAdmissible (Nat.card F) (D.cA a.1) 2
        · have hd : 0 < D.depA a.1 := D.hdepA a.1
          have hw1 : weight (D.depA a.1) (D.cA a.1) = w := by
            have hwv := g5c1_aSide_weight F r s hcase hs0v hbigv R0 u hau hwtA a.1 a.2
            rw [hwv]
            exact hw
          exact admExpT_self F w 2 hd (D.cA a.1) hw1 h2m
        · -- ¬2-adm a-member: 1-adm + head q + prefix drop → ih
          have hqhead : pad0 (D.cA a.1) 0 = Nat.card F := by
            have hd : 0 < D.depA a.1 := D.hdepA a.1
            rw [pad0_of_lt (D.cA a.1) hd]
            have h0 : (D.cA a.1) ⟨0, hd⟩ = qExp F := by rfl
            rw [h0]
            rfl
          have h1m : kAdmissible (Nat.card F) (D.cA a.1) 1 := by
            constructor
            · intro x hx
              have hx0 : x = 0 := by omega
              subst x
              have hd : 0 < D.depA a.1 := D.hdepA a.1
              rw [pad0_of_lt (D.cA a.1) hd]
              -- head q ≤ q
              have hh0 : ((D.cA a.1) ⟨0, hd⟩ : ℕ) = Nat.card F := by
                have hp0 : pad0 (D.cA a.1) 0 = ((D.cA a.1) ⟨0, hd⟩ : ℕ) := pad0_of_lt (D.cA a.1) hd
                rw [← hp0]
                exact hqhead
              rw [hh0]
            · intro hw1
              rcases hw1 with ⟨hr1, hdep1, hall, hlast⟩
              -- member depth ≥ 2 (D.depA = R0.depA + 1 ≥ 2), so no depth-1 witness
              have hdep2 : 2 ≤ D.depA a.1 := by
                have hdep : D.depA a.1 = R0.depA a.1 + 1 := by
                  dsimp [D, RelData.BCqIter, RelData.BCq]
                  rfl
                have hpos : 0 < R0.depA a.1 := R0.hdepA a.1
                omega
              omega
          have hdrop : l2μ (Nat.card F) (D.cA a.1) < l2μ (Nat.card F) s := by
            have hpd := g5c1_aSide_prefix_drop F r s hcase hs0v hbigv R0 u hhead a.1 a.2
            dsimp [D] at hpd
            exact l2_member_lt (q := Nat.card F) s (D.cA a.1) (Or.inl hpd)
          have hw1 : weight (D.depA a.1) (D.cA a.1) = w := by
            have hwv := g5c1_aSide_weight F r s hcase hs0v hbigv R0 u hau hwtA a.1 a.2
            rw [hwv]
            exact hw
          exact ih (D.depA a.1) (D.cA a.1) hw1 h1m h2m hqhead hdrop
    | inr p =>
        -- b-member: 2-adm via g5c1_bSide_twoAdm
        have h2m : kAdmissible (Nat.card F) (D.cB p) 2 := by
          exact g5c1_bSide_twoAdm F r s hcase hs0v hbigv R0 hbhd hXw p
        have hd : 0 < D.depB p := D.hdepB p
        have hw1 : weight (D.depB p) (D.cB p) = w := by
          have hwv := g5c1_bSide_weight F r s hcase hs0v hbigv R0 hbhd hXw p
          rw [hwv]
          exact hw
        exact admExpT_self F w 2 hd (D.cB p) hw1 h2m
  -- member orders (ℓ ≥ 2): a-side/b-side via the j=0 order lemmas; ℓ > r by saturation
  have horder : ∀ q : ι, ∀ ℓ : ℕ, 2 ≤ ℓ → psum (mc q) ℓ ≤ psum s ℓ := by
    intro q ℓ hℓ
    by_cases hℓr : ℓ ≤ r
    · cases q with
      | inl a =>
          exact g5T1_aSide_order F r s hcase hs0v hbigv R0 u hpref a.1 a.2 ℓ hℓ
      | inr p =>
          exact g5T1_bSide_order F r s hcase hs0v hbigv R0 hbhd hbndB p ℓ hℓ
    · -- ℓ > r: saturation
      have hgt : r < ℓ := lt_of_not_ge hℓr
      have hwl := psum_le_weight (mc q) ℓ
      have hwm : weight (mdep q) (mc q) = weight r s := by
        cases q with
        | inl a => exact g5c1_aSide_weight F r s hcase hs0v hbigv R0 u hau hwtA a.1 a.2
        | inr p => exact g5c1_bSide_weight F r s hcase hs0v hbigv R0 hbhd hXw p
      have hpeq : weight r s = psum s ℓ := (psum_ge_depth s (le_of_lt hgt)).symm
      rw [hwm, hpeq] at hwl
      exact hwl
  exact admExpT_combine F w 2 s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
