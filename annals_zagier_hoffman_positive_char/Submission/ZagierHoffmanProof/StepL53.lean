import Submission.ZagierHoffmanProof.StepL52
import Submission.ZagierHoffmanProof.StepL44

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L53: the level-2 CASE-2 closed form (MAIN(2) component (a))

For a level-2 CASE-2 input `s = (s₁, q)` (`s₁ < q`) the Step-1 chain
(`k=2, j=1`, `n = 0` `BC_q`-steps, empty prefix) is the `B*_{s₁}`-over of the `R1`
relation itself: `D = toData (r1Rel F)` and `Q = Bs`.  This module unwinds the
chain lets (MAIN(2) component (a)): the three member tuples of the reduced chain
are explicit —
  ★ bstar_type1_tuple : the a-side member is `(s₁, q)` = `pair s₁ (qExp F)` (s itself);
  ★ bstar_type2_tuple : the type-2 member is `(s₁, 1, q−1)`;
  ★ bstar_type3_tuple : the type-3 member is `(s₁+1, q−1)`;
  ★ bstar_a_coeffs : the coefficients are `1` (a-side) and `D1rat` (both b-sides).
(`consVec_single_q_eq_pair` identifies `consVec s₁ (single qExp)` with the pair.)
With StepL52's 2-admissibility/weight facts these are the exact inputs of the
closed-form assembly
  ★ case2_level2 (s₁) (hs₁ : s₁ < q) : AdmExpT F (s₁+q) 2 (pair s₁ (qExp F)),
proved by: `zeta_fixed_bridge` to `Bs` gives the relation
`ζ(s₁,q) + D1·ζ(s₁,1,q−1) + D1·ζ(s₁+1,q−1) = 0` (the level-2 CASE-2 instance of
(2.10)); `triple_sum_split` splits the a/b sums; the PUnit-singleton sums are
collapsed with `sum_PUnit` after `Fintype.sum_sum_type`; the tuple/coeff rewrites
come from `bstar_type*_tuple` / `bstar_a_coeffs`; negating the collapsed relation
and rewriting the `ζ_A (pair s₁ (qExp F))` side yields the two-member
`AdmExpT`-witness (members `m2 = (s₁,1,q−1)` (depth 3) and `m3 = (s₁+1,q−1)`
(depth 2), both coefficients `−D1rat`, weights `s₁+q`, 2-admissible by
`twoAdm_s1_*` from StepL52, orders by `psum_le_weight` + the weight identities).
-/

universe u v

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `consVec s₁ (single qExp) = pair s₁ (qExp F)` — the type-1 member is `s` itself. -/
lemma consVec_single_q_eq_pair (s₁ : ℕ+) :
    consVec s₁ (single (qExp F)) = pair s₁ (qExp F) := by
  classical
  funext j
  by_cases hj0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj0)
    rw [hj]
    rw [consVec_zero s₁ (single (qExp F))]
    rw [pair_zero]
  · have hj1 : (j : ℕ) = 1 := by
      have hlt : (j : ℕ) < 2 := j.isLt
      omega
    have hj : j = ⟨1, by omega⟩ := Fin.ext (by simpa using hj1)
    rw [hj]
    have hc := consVec_succ s₁ (single (qExp F)) ⟨0, by omega⟩
    -- consVec s₁ (single qExp) ⟨0+1⟩ = (single qExp) ⟨0⟩
    change (consVec s₁ (single (qExp F)) ⟨1, by omega⟩ : ℕ+) = pair s₁ (qExp F) ⟨1, by omega⟩
    rw [show (consVec s₁ (single (qExp F)) ⟨1, by omega⟩ : ℕ+) =
        (single (qExp F)) ⟨0, by omega⟩ by simpa using hc]
    rw [pair_one]
    rfl

/-- The type-2 member tuple of the reduced chain. -/
lemma bstar_type2_tuple (s₁ : ℕ+) (hs₁ : (s₁ : ℕ) < Nat.card F) :
    (ofBstarOver F (toData F (r1Rel F)) s₁
      (fun e => BCqIter_valid F 0 (r1Rel F) e)
      (RelData.iterate_merge_hv F 0 (r1Rel F) s₁ (by omega) (r1Rel_hbhd F))).c
        (Sum.inr (Sum.inl PUnit.unit)) = consVec s₁ (pair oneExp (qMinusExp F)) := by
  classical
  dsimp [ofBstarOver]
  rfl

/-- The type-3 member tuple of the reduced chain. -/
lemma bstar_type3_tuple (s₁ : ℕ+) (hs₁ : (s₁ : ℕ) < Nat.card F) :
    (ofBstarOver F (toData F (r1Rel F)) s₁
      (fun e => BCqIter_valid F 0 (r1Rel F) e)
      (RelData.iterate_merge_hv F 0 (r1Rel F) s₁ (by omega) (r1Rel_hbhd F))).c
        (Sum.inr (Sum.inr PUnit.unit)) =
      pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F) := by
  classical
  change headAdd s₁ ((toData F (r1Rel F)).hdepB PUnit.unit) ((toData F (r1Rel F)).cB PUnit.unit) =
    pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)
  change headAdd s₁ ((toData F (r1Rel F)).hdepB PUnit.unit) (pair oneExp (qMinusExp F)) =
    pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)
  ext j
  by_cases hj0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj0)
    rw [hj]
    dsimp [headAdd]
    apply Subtype.ext
    have hc0 := congrArg (fun t : ℕ+ => (t : ℕ)) (pair_zero oneExp (qMinusExp F))
    have hc1 : (oneExp : ℕ) = 1 := rfl
    change (s₁ : ℕ) + ((pair oneExp (qMinusExp F)) ⟨0, by omega⟩ : ℕ) = (s₁ : ℕ) + 1
    rw [hc0, hc1]
  · have hj1 : (j : ℕ) = 1 := by
      have hlt : (j : ℕ) < 2 := j.isLt
      omega
    have hj : j = ⟨1, by omega⟩ := Fin.ext (by simpa using hj1)
    rw [hj]
    dsimp [headAdd]
    rfl

/-- The type-1 member tuple of the reduced chain is `(s₁, q)`. -/
lemma bstar_type1_tuple (s₁ : ℕ+) (hs₁ : (s₁ : ℕ) < Nat.card F) :
    (ofBstarOver F (toData F (r1Rel F)) s₁
      (fun e => BCqIter_valid F 0 (r1Rel F) e)
      (RelData.iterate_merge_hv F 0 (r1Rel F) s₁ (by omega) (r1Rel_hbhd F))).c
        (Sum.inl PUnit.unit) = pair s₁ (qExp F) := by
  classical
  dsimp [ofBstarOver, r1Rel, toData]
  change consVec s₁ (single (qExp F)) = pair s₁ (qExp F)
  exact consVec_single_q_eq_pair F s₁


/-- The coefficients of the reduced chain: a-side 1, both b-sides `D1rat`. -/
lemma bstar_a_coeffs (s₁ : ℕ+) (hs₁ : (s₁ : ℕ) < Nat.card F) :
    (((ofBstarOver F (toData F (r1Rel F)) s₁
        (fun e => BCqIter_valid F 0 (r1Rel F) e)
        (RelData.iterate_merge_hv F 0 (r1Rel F) s₁ (by omega) (r1Rel_hbhd F))).a
          (Sum.inl PUnit.unit) : RatFunc F) = 1) ∧
    (((ofBstarOver F (toData F (r1Rel F)) s₁
        (fun e => BCqIter_valid F 0 (r1Rel F) e)
        (RelData.iterate_merge_hv F 0 (r1Rel F) s₁ (by omega) (r1Rel_hbhd F))).a
          (Sum.inr (Sum.inl PUnit.unit)) : RatFunc F) = D1rat F) ∧
    (((ofBstarOver F (toData F (r1Rel F)) s₁
        (fun e => BCqIter_valid F 0 (r1Rel F) e)
        (RelData.iterate_merge_hv F 0 (r1Rel F) s₁ (by omega) (r1Rel_hbhd F))).a
          (Sum.inr (Sum.inr PUnit.unit)) : RatFunc F) = D1rat F) := by
  classical
  constructor
  · dsimp [ofBstarOver, r1Rel, toData]
  · constructor
    · dsimp [ofBstarOver, r1Rel, toData]
    · dsimp [ofBstarOver, r1Rel, toData]


/-- PUnit-singleton sum (canonical `PUnit`): the sum is the single value. -/
lemma sum_PUnit {M : Type v} [AddCommMonoid M] (f : PUnit → M) :
    (∑ x : PUnit, f x) = f PUnit.unit := by
  simp

/-- Generic PUnit-singleton: a sum over any type equivalent to `PUnit` is its single
value at the transported element — instance-safe via `Fintype.sum_equiv` (tactic (i)
of PLAN SESSION 194: sums over `RelData`-wrapped `PUnit` indices collapse through an
explicit equivalence, not the fragile `change`+`simp` route).  KEY: the codomain must
be `PUnit.{u+1}` (a `Type u`) to match `α : Type u`; `PUnit.{u}` lives in `Sort u`
and has no `Fintype`. -/
lemma sum_equiv_punit {α : Type u} [Fintype α] {M : Type v} [AddCommMonoid M]
    (e : α ≃ PUnit.{u + 1}) (f : α → M) :
    (∑ x : α, f x) = f (e.symm PUnit.unit) := by
  classical
  have hsum : (∑ x : α, f x) = (∑ y : PUnit.{u + 1}, f (e.symm y)) :=
    Fintype.sum_equiv e (f := f) (g := fun y : PUnit.{u + 1} => f (e.symm y))
      (by intro x; exact (congrArg f (Equiv.symm_apply_apply e x)).symm)
  rw [hsum]
  simp

/-- ★ The level-2 CASE-2 closed form: `(s₁, q)` (s₁ < q) expands at level 2 with
2-admissible weight-`s₁+q` outputs. -/
theorem case2_level2 (s₁ : ℕ+) (hs₁ : (s₁ : ℕ) < Nat.card F) :
    AdmExpT F ((s₁ : ℕ) + Nat.card F) 2 (pair s₁ (qExp F)) := by
  classical
  let D : RelData F := toData F (r1Rel F)
  let Bs : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) :=
    ofBstarOver F D s₁ (fun e => BCqIter_valid F 0 (r1Rel F) e)
      (RelData.iterate_merge_hv F 0 (r1Rel F) s₁ (by omega) (r1Rel_hbhd F))
  let w : ℕ := (s₁ : ℕ) + Nat.card F
  let f : D.ιA ⊕ (D.ιB ⊕ D.ιB) → RatFunc.CompletionAtInfty F := fun p =>
    ((Bs.a p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Bs.c p)
  have hzeta : (∑ p : D.ιA ⊕ (D.ιB ⊕ D.ιB), f p) = 0 := by
    have hz := zeta_fixed_bridge F Bs.dep Bs.hdep Bs.c Bs.a
      (fun d : ℕ => by
        have hv' := FixedOver.valid Bs d
        simpa [FixedOver.level] using hv')
    dsimp [f]
    exact hz
  have hsplit := triple_sum_split F f
  rw [hsplit] at hzeta
  -- collapse the three PUnit-singleton sums and close the single terms at value level
  have hca1 : (((Bs.a (Sum.inl PUnit.unit) : RatFunc F)) : RatFunc.CompletionAtInfty F) = 1 := by
    have hc := (bstar_a_coeffs F s₁ hs₁).1
    -- hc : (Bs.a (inl unit) : RatFunc F) = 1 (up to Bs/D unfolding)
    have hc' : (((Bs.a (Sum.inl PUnit.unit) : RatFunc F)) : RatFunc.CompletionAtInfty F) =
        ((1 : RatFunc F) : RatFunc.CompletionAtInfty F) := by
      dsimp [Bs, D]
      rw [hc]
    rw [hc']
    simp [completion_coe_one]
  have ha : (∑ i : D.ιA, f (Sum.inl i)) = ζ_A F (pair s₁ (qExp F)) := by
    dsimp [f]
    -- collapse to the single element of D.ιA (defeq PUnit) and rewrite the tuple
    rw [show (∑ x : D.ιA, ((Bs.a (Sum.inl x) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Bs.c (Sum.inl x))) =
      ((Bs.a (Sum.inl PUnit.unit) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Bs.c (Sum.inl PUnit.unit)) by
          -- singleton over D.ιA: use sum_equiv_punit with e := Equiv.refl after defeq
          change (∑ x : PUnit, ((Bs.a (Sum.inl x) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Bs.c (Sum.inl x))) =
            ((Bs.a (Sum.inl PUnit.unit) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Bs.c (Sum.inl PUnit.unit))
          simp]
    -- single term: coeff 1, tuple (s₁,q)
    have hc1 : (((Bs.a (Sum.inl PUnit.unit) : RatFunc F)) : RatFunc.CompletionAtInfty F) = 1 := by
      have hc := (bstar_a_coeffs F s₁ hs₁).1
      have hc' : (((Bs.a (Sum.inl PUnit.unit) : RatFunc F)) : RatFunc.CompletionAtInfty F) =
          ((1 : RatFunc F) : RatFunc.CompletionAtInfty F) := by
        dsimp [Bs, D]
        rw [hc]
      rw [hc']
      simp [completion_coe_one]
    rw [hc1]
    simp [completion_coe_one]
    have ht := bstar_type1_tuple F s₁ hs₁
    -- congrArg on ζ: Bs.c (inl unit) = pair s₁ qExp
    have hz : ζ_A F (Bs.c (Sum.inl PUnit.unit)) = ζ_A F (pair s₁ (qExp F)) := by
      dsimp [Bs, D]
      exact congrArg (ζ_A F) ht
    rw [hz]
  have hrel0 : ζ_A F (pair s₁ (qExp F)) +
      (∑ i : D.ιB, f (Sum.inr (Sum.inl i))) +
      (∑ i : D.ιB, f (Sum.inr (Sum.inr i))) = 0 := by
    -- from hzeta with ha
    rw [ha] at hzeta
    simpa using hzeta
  -- leave: the type-2/type-3 sums to be handled in the next step
  have hrel2 : ζ_A F (pair s₁ (qExp F)) +
      ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (consVec s₁ (pair oneExp (qMinusExp F))) +
      ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) = 0 := by
    -- collapse the two b-sums (PUnit singletons) and rewrite coeffs/tuples
    rw [show (∑ i : D.ιB, f (Sum.inr (Sum.inl i))) =
        ((Bs.a (Sum.inr (Sum.inl PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Bs.c (Sum.inr (Sum.inl PUnit.unit))) by
          dsimp [f]
          change (∑ x : PUnit, ((Bs.a (Sum.inr (Sum.inl x)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Bs.c (Sum.inr (Sum.inl x)))) =
            ((Bs.a (Sum.inr (Sum.inl PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Bs.c (Sum.inr (Sum.inl PUnit.unit)))
          simp] at hrel0
    rw [show (∑ i : D.ιB, f (Sum.inr (Sum.inr i))) =
        ((Bs.a (Sum.inr (Sum.inr PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Bs.c (Sum.inr (Sum.inr PUnit.unit))) by
          dsimp [f]
          change (∑ x : PUnit, ((Bs.a (Sum.inr (Sum.inr x)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Bs.c (Sum.inr (Sum.inr x)))) =
            ((Bs.a (Sum.inr (Sum.inr PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Bs.c (Sum.inr (Sum.inr PUnit.unit)))
          simp] at hrel0
    have hc2 : (((Bs.a (Sum.inr (Sum.inl PUnit.unit)) : RatFunc F)) : RatFunc.CompletionAtInfty F) =
        ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) := by
      have hc := (bstar_a_coeffs F s₁ hs₁).2.1
      dsimp [Bs, D]
      rw [hc]
    have hc3 : (((Bs.a (Sum.inr (Sum.inr PUnit.unit)) : RatFunc F)) : RatFunc.CompletionAtInfty F) =
        ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) := by
      have hc := (bstar_a_coeffs F s₁ hs₁).2.2
      dsimp [Bs, D]
      rw [hc]
    have hz2 : ζ_A F (Bs.c (Sum.inr (Sum.inl PUnit.unit))) =
        ζ_A F (consVec s₁ (pair oneExp (qMinusExp F))) := by
      dsimp [Bs, D]
      exact congrArg (ζ_A F) (bstar_type2_tuple F s₁ hs₁)
    have hz3 : ζ_A F (Bs.c (Sum.inr (Sum.inr PUnit.unit))) =
        ζ_A F (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) := by
      dsimp [Bs, D]
      exact congrArg (ζ_A F) (bstar_type3_tuple F s₁ hs₁)
    rw [hc2, hc3, hz2, hz3] at hrel0
    exact hrel0
  -- negate and set up the two-member family
  have hneg : ζ_A F (pair s₁ (qExp F)) =
      -(((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (consVec s₁ (pair oneExp (qMinusExp F)))) +
        -(((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F))) := by
    have hz := eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hrel2)
    rw [hz]
    rw [neg_add]
  let m2 : Fin 3 → ℕ+ := consVec s₁ (pair oneExp (qMinusExp F))
  let m3 : Fin 2 → ℕ+ := pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)
  let depc : PUnit ⊕ PUnit → ℕ := fun p => match p with | Sum.inl _ => 3 | Sum.inr _ => 2
  have hdepc : ∀ p : PUnit ⊕ PUnit, 0 < depc p := by
    intro p
    cases p <;> dsimp [depc] <;> omega
  let cc : ∀ p : PUnit ⊕ PUnit, Fin (depc p) → ℕ+ := fun p => match p with
    | Sum.inl _ => m2 | Sum.inr _ => m3
  let ac : PUnit ⊕ PUnit → RatFunc F := fun p => match p with
    | Sum.inl _ => -D1rat F | Sum.inr _ => -D1rat F
  have hw2 : weight 3 m2 = w := by
    dsimp [m2, w]
    exact weight_s1_one_qminus F s₁
  have hw3 : weight 2 m3 = w := by
    dsimp [m3, w]
    exact weight_s1succ_qminus F s₁
  have ha2 : kAdmissible (Nat.card F) m2 2 := by
    dsimp [m2]
    exact twoAdm_s1_one_qminus F s₁ hs₁
  have ha3 : kAdmissible (Nat.card F) m3 2 := by
    dsimp [m3]
    exact twoAdm_s1succ_qminus F s₁ hs₁
  have hps : ∀ ℓ : ℕ, 2 ≤ ℓ → psum (pair s₁ (qExp F)) ℓ = w := by
    intro ℓ hℓ
    have hd := psum_ge_depth (pair s₁ (qExp F)) (by omega : 2 ≤ ℓ)
    rw [hd]
    dsimp [w]
    rw [weight_pair]
    change (s₁ : ℕ) + (qExp F : ℕ) = (s₁ : ℕ) + Nat.card F
    rfl
  have horder2 : ∀ ℓ : ℕ, 2 ≤ ℓ → psum m2 ℓ ≤ psum (pair s₁ (qExp F)) ℓ := by
    intro ℓ hℓ
    rw [hps ℓ hℓ]
    dsimp [m2]
    change psum (consVec s₁ (pair oneExp (qMinusExp F))) ℓ ≤ (s₁ : ℕ) + Nat.card F
    have h1 := psum_le_weight (consVec s₁ (pair oneExp (qMinusExp F))) ℓ
    rw [weight_s1_one_qminus F s₁] at h1
    exact h1
  have horder3 : ∀ ℓ : ℕ, 2 ≤ ℓ → psum m3 ℓ ≤ psum (pair s₁ (qExp F)) ℓ := by
    intro ℓ hℓ
    rw [hps ℓ hℓ]
    dsimp [m3]
    change psum (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) ℓ ≤ (s₁ : ℕ) + Nat.card F
    have h1 := psum_le_weight (pair ⟨(s₁ : ℕ) + 1, Nat.succ_pos (s₁ : ℕ)⟩ (qMinusExp F)) ℓ
    rw [weight_s1succ_qminus F s₁] at h1
    exact h1
  refine ⟨PUnit ⊕ PUnit, inferInstance, depc, hdepc, cc, ac, ?_, ?_, ?_, ?_⟩

  · intro p
    cases p with
    | inl _ => exact hw2
    | inr _ => exact hw3
  · intro p
    cases p with
    | inl _ => exact ha2
    | inr _ => exact ha3
  · intro p ℓ hℓ
    cases p with
    | inl _ => exact horder2 ℓ hℓ
    | inr _ => exact horder3 ℓ hℓ
  · -- hid: the sum over PUnit ⊕ PUnit collapses to hneg's RHS
    rw [hneg]
    rw [Fintype.sum_sum_type]
    dsimp [ac, cc, m2, m3, depc]
    rw [sum_PUnit, sum_PUnit]
    rw [ratFunc_coe_neg F (D1rat F)]
    ring
end ZagierHoffmanPositiveChar


