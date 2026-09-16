import Submission.ZagierHoffmanProof.StepL79
import Submission.ZagierHoffmanProof.StepL54
import Submission.ZagierHoffmanProof.StepD
/-!
# Step L80: the G5 (j = 0) chains closed — MAIN(2)-weak and A(2)-weak unconditional

The two top-level j = 0 chain instances (the in-domain head-q tuples: CASE-1
(q, s₂>q, …, s_r) with r ≥ 2 and CASE-2 (q,q)) are closed:
  ★ g5_case1_step (w r s hw hcase hbigp hs0p ih) : AdmExp F w 2 s
      — the CASE-1 splice: `lemma_2_9_config_data` at k = 2 gives the empty-front
      BC-iterate D := BCqIter F 1 (toData F R0) with ζ-identity
      ζ(s) + (guarded a-sum) + (b-sum) = 0 (g5c1_zeta_core, StepL77).  Fold it by
      S1–S3 into ζ(s) = Σ_{i≠u ⊕ D.ιB} (−a)·ζ(member) (sum_guarded_subtype' +
      neg_sum_sum_pair' + neg_coe_mul_zeta — universe-polymorphic); per-member e:
      a-members i ≠ u are 1-adm with head q (weight w): 2-adm → admExp_self,
      ¬2-adm → the recursion ih (prefix-2 strict drop g5c1_aSide_prefix_drop ⇒
      l2_member_lt); b-members 2-adm (g5c1_bSide_twoAdm + g5c1_bSide_weight) →
      admExp_self.  Splice with admExp_combine.
  ★ g5_case2_step (w s hw hr2 hp1 hq0) : AdmExp F w 2 s — CASE-2: r = 2 ∧
      pad0 s 1 = q ∧ pad0 s 0 = q ⇒ s = pair q q via tuple_two_eq_of_pad0; transport
      g5_case2_qq (StepL75) across the weight equality w = q+q (weight_pair).
  ★ g5_total (w) : the full in-domain head-q handler matching StepL74's g5 signature
      — l2_induction over weight-w tuples; each step dispatches inDomain2_cases:
      CASE-1 (2 ≤ r ∧ q < pad0 s 1) → g5_case1_step; CASE-2 (r = 2 ∧ pad0 s 1 = q)
      → g5_case2_step.  The induction's IH covers recursion members (smaller l2μ).
  ★ MAIN2_weak_all (w) : ∀ in-domain weight-w s, AdmExp F w 2 s   [MAIN2_weak_of_g5]
  ★ A2_weak_all (w) (hw0 : 0 < w) : ∀ weight-w s, AdmExp F w 2 s  [A2_weak_of_g5]
      — H₂ (weak level-2 expansions) unconditional at every weight.
NEXT (beyond this session): the m ≥ 3 hierarchy (β design gap), theorem_B/D (ABP).
-/
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Universe-polymorphic S3 assembly for TWO parts (negated sums → sum-type sum). -/
lemma neg_sum_sum_pair' {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {K : Type*} [AddCommGroup K] (x₁ : ι₁ → K) (x₂ : ι₂ → K) :
    -(∑ i : ι₁, x₁ i) + -(∑ i : ι₂, x₂ i) =
      ∑ p : ι₁ ⊕ ι₂, (match p with
        | Sum.inl a => -(x₁ a) | Sum.inr b => -(x₂ b)) := by
  classical
  rw [Fintype.sum_sum_type]
  simp [Finset.sum_neg_distrib]

/-- CASE-1 g5 step: in-domain head-q s with s₂ > q expands via the empty-front chain
family; ¬2-adm a-members go to the recursion ih (strict prefix-2 drop), b-members
are 2-adm (self). -/
theorem g5_case1_step (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase : 2 ≤ r) (hbigp : (Nat.card F : ℕ) < pad0 s 1) (hs0p : pad0 s 0 = Nat.card F)
    (ih : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      kAdmissible (Nat.card F) m 1 → ¬ kAdmissible (Nat.card F) m 2 →
      pad0 m 0 = Nat.card F → l2μ (Nat.card F) m < l2μ (Nat.card F) s →
      AdmExp F w 2 m) :
    AdmExp F w 2 s := by
  classical
  have hk1 : 1 ≤ 2 := by omega
  have hs0v : (s ⟨0, by omega⟩ : ℕ) = Nat.card F := by
    have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
    omega
  have hbigv : (Nat.card F : ℕ) < (s ⟨1, by omega⟩ : ℕ) :=
    case1_pad0_big_of_value F s hcase hbigp
  rcases lemma_2_9_config_data F r s 2 hk1 hcase hbigv with ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB⟩
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
  have e : ∀ q : ι, AdmExp F w 2 (mc q) := by
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
          exact admExp_self F w 2 hd (D.cA a.1) hw1 h2m
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
        exact admExp_self F w 2 hd (D.cB p) hw1 h2m
  -- assemble by admExp_combine (members need only be AdmExp — ¬2-adm members are
  -- expanded by ih inside e)
  exact admExp_combine F w 2 s mdep mhdep mc ma hid e

/-- CASE-2 g5 step: the in-domain head-q depth-2 tuple (q,q) (r = 2, pad0 s 1 = q)
expands at level 2 via the (q,q) chain instance g5_case2_qq. -/
theorem g5_case2_step (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hr2 : r = 2) (hp1 : pad0 s 1 = Nat.card F) (hq0 : pad0 s 0 = Nat.card F) :
    AdmExp F w 2 s := by
  classical
  subst r
  have hp0' : pad0 s 0 = (qExp F : ℕ) := by
    change pad0 s 0 = Nat.card F
    exact hq0
  have hp1' : pad0 s 1 = (qExp F : ℕ) := by
    change pad0 s 1 = Nat.card F
    exact hp1
  have hseq : s = pair (qExp F) (qExp F) := tuple_two_eq_of_pad0 s (qExp F) (qExp F) hp0' hp1'
  have hw2 : weight 2 s = (qExp F : ℕ) + (qExp F : ℕ) := by
    rw [hseq]
    exact weight_pair (qExp F) (qExp F)
  have hweq : w = (qExp F : ℕ) + (qExp F : ℕ) := by
    rw [← hw2]
    exact hw.symm
  have hA : AdmExp F w 2 (pair (qExp F) (qExp F)) := by
    simpa [hweq] using g5_case2_qq F
  rw [hseq]
  exact hA

/-- ★ G5 TOTAL: the full in-domain head-q handler matching StepL74's g5 signature —
every in-domain weight-w tuple whose zero-padded first entry equals q expands at
level 2.  CASE-1 (2 ≤ r ∧ q < pad0 s 1) → g5_case1_step (recursion on the chain
members); CASE-2 (r = 2 ∧ pad0 s 1 = q) → g5_case2_step ((q,q)). -/
theorem g5_total (w : ℕ) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 →
      pad0 s 0 = Nat.card F → AdmExp F w 2 s := by
  classical
  let P : (r : ℕ) → (s : Fin r → ℕ+) → weight r s = w → Prop :=
    fun r s hw => kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 →
      pad0 s 0 = Nat.card F → AdmExp F w 2 s
  change ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), P r s hw
  refine l2_induction (Nat.card F) w P ?_
  intro r s hw rec h1 hn2 hq0
  have hcases := inDomain2_cases (Nat.card F) (card_ge_two F) s h1 hn2
  rcases hcases with hc1 | hc2
  · rcases hc1 with ⟨hcase, hbigp⟩
    exact g5_case1_step F w r s hw hcase hbigp hq0
      (fun r' m hm h1m h2m hq0m hμ => rec r' m hm hμ h1m h2m hq0m)
  · rcases hc2 with ⟨hr2, hp1⟩
    exact g5_case2_step F w s hw hr2 hp1 hq0

/-- ★ MAIN(2) unconditionally (no G5 hypothesis): every in-domain weight-w tuple
expands at level 2. -/
theorem MAIN2_weak_all (w : ℕ) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w),
      kAdmissible (Nat.card F) s 1 → ¬ kAdmissible (Nat.card F) s 2 → AdmExp F w 2 s := by
  exact MAIN2_weak_of_g5 F w (g5_total F w)

/-- ★ H₂ unconditionally at every weight (weak level-2 form): every weight-w tuple
expands at level 2. -/
theorem A2_weak_all (w : ℕ) (hw0 : 0 < w) :
    ∀ (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w), AdmExp F w 2 s := by
  exact A2_weak_of_g5 F w hw0 (g5_total F w)

end ZagierHoffmanPositiveChar
