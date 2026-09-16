import Submission.ZagierHoffmanProof.StepL37

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L38: the R1 binary relation — the base data of the CASE-2 (Prop 2.13) chain

★ `r1Rel F` is the paper's (2.8) relation `R_ε` as a `BinaryRel`: a-side the single
depth-1 output `(q)` with coefficient `1`, b-side the depth-2 output `(1, q−1)` with
coefficient `D1` — valid at every level via `R1_all_unc` (StepK34).  This is the base
relation of the Prop-2.13 (CASE-2, `s_k = q`) chain: the analogue of the
`lemma_2_9_rel` data of CASE-1, with W empty.

Data facts (the R1-version of `lemma_2_9_config_data`):
  • r1Rel_aA_unit: the distinguished `a`-output has coefficient 1;
  • r1Rel_depA_unit / r1Rel_cA_unit: depth 1, tuple `(q)`;
  • r1Rel_hbhd: the `b`-tuple is `1`-headed;
  • ★ r1Rel_tail_weight: `weight (depB j' − 1) (expTail (cB j')) = q−1`
    [feeds the type-2/3 weight invariants of the CASE-2 chain: with depth(s)=k and
    s_k = q the level-0 Xw is `psum s r − psum s (k−1) − 1 = q − 1`];
  • r1Rel_tail_psum: `psum (expTail (cB j')) m ≤ q−1` [feeds the type-3 prefix-k
    bound of the CASE-2 chain, X m := q−1 with X 1 = s_k − 1 = q−1];
  • expTail_pair: `expTail (pair u v) = single v` (the tail of the depth-2 pair).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]
/-- The R1 binary relation (paper (2.8) / `R_ε`): a-side `(q)` with coefficient `1`,
b-side `(1, q−1)` with coefficient `D1` — valid at every level by `R1_all_unc`.
This is the base relation of the Prop-2.13 (CASE-2) chain. -/
noncomputable def r1Rel (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)] : BinaryRel F where
  ιA := PUnit
  finA := inferInstance
  depA := fun _ => 1
  hdepA := fun _ => by omega
  cA := fun _ => single (qExp F)
  aA := fun _ => 1
  ιB := PUnit
  finB := inferInstance
  depB := fun _ => 2
  hdepB := fun _ => by omega
  hB2 := fun _ => by omega
  cB := fun _ => pair oneExp (qMinusExp F)
  aB := fun _ => D1rat F
  valid := by
    intro e
    classical
    -- sums over PUnit collapse; identify the S-level terms with R1Prop
    have hS : S F 1 (by omega : 0 < 1) (single (qExp F)) e = P F e (qExp F) := by
      simpa [single] using (S_one_eq_P F e (by omega : 0 < 1) (single (qExp F)))
    simp [hS]
    rw [← D1c_eq_D1rat]
    exact R1_all_unc F e

/-- The distinguished `a`-output of `r1Rel` has coefficient 1. -/
lemma r1Rel_aA_unit : (r1Rel F).aA PUnit.unit = 1 := by rfl

/-- The `b`-tuples of `r1Rel` are `1`-headed. -/
lemma r1Rel_hbhd : ∀ j' : (r1Rel F).ιB,
    (((r1Rel F).cB j') ⟨0, (r1Rel F).hdepB j'⟩ : ℕ) = 1 := by
  intro j'
  have h02 : 0 < 2 := by omega
  change ((pair oneExp (qMinusExp F)) ⟨0, h02⟩ : ℕ) = 1
  rw [pair_zero]
  rfl

/-- The distinguished `a`-tuple of `r1Rel` is `(q)` of depth 1. -/
lemma r1Rel_cA_unit : (r1Rel F).cA PUnit.unit = single (qExp F) := by rfl

/-- The depth of the distinguished `a`-output is 1. -/
lemma r1Rel_depA_unit : (r1Rel F).depA PUnit.unit = 1 := by rfl

/-- The tail of a depth-2 pair is the singleton of its second entry. -/
lemma expTail_pair (u v : ℕ+) : expTail (pair u v) = single v := by
  funext j
  change pair u v ⟨(j : ℕ) + 1, by omega⟩ = v
  have hj0 : (j : ℕ) = 0 := by
    have hjlt : (j : ℕ) < 1 := by
      have : (j : ℕ) < 2 - 1 := j.isLt
      omega
    omega
  have hidx : (⟨(j : ℕ) + 1, by omega⟩ : Fin 2) = ⟨1, by omega⟩ := by
    apply Fin.ext
    simp [hj0]
  rw [hidx]
  exact pair_one u v

/-- The `b`-tail weight of `r1Rel`: `weight (depB j' − 1) (expTail (cB j')) = (qMinusExp F : ℕ)`. -/
lemma r1Rel_tail_weight (j' : (r1Rel F).ιB) :
    weight ((r1Rel F).depB j' - 1) (expTail ((r1Rel F).cB j')) = (qMinusExp F : ℕ) := by
  -- cB j' = pair oneExp (qMinusExp F), depB j' = 2 (definitional)
  change weight (2 - 1) (expTail (pair oneExp (qMinusExp F))) = (qMinusExp F : ℕ)
  rw [expTail_pair]
  change weight 1 (single (qMinusExp F)) = (qMinusExp F : ℕ)
  rw [weight_single]

/-- The `b`-tail prefix bound of `r1Rel` (hleB-style datum): `psum (expTail (cB j')) m ≤ q−1`. -/
lemma r1Rel_tail_psum (j' : (r1Rel F).ιB) (m : ℕ) :
    psum (expTail ((r1Rel F).cB j')) m ≤ (qMinusExp F : ℕ) := by
  change psum (expTail (pair oneExp (qMinusExp F))) m ≤ (qMinusExp F : ℕ)
  rw [expTail_pair]
  by_cases hm : 0 < m
  · rw [psum_single_of_pos (qMinusExp F) hm]
  · have hm0 : m = 0 := by omega
    subst m
    rw [psum_zero]
    exact le_of_lt (qMinusExp F).pos

end ZagierHoffmanPositiveChar
