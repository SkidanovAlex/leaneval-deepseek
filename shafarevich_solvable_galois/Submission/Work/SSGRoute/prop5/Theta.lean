import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Submission.Work.CohomologicalShrinking.nonempty_prop5Data_one_one
import Submission.Work.SSGRoute.prop5.Map
import Submission.Work.SSGRoute.prop5.valFn_update_commutator
import Submission.Work.SSGRoute.prop5.valFn_update_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement TensorProduct

set_option maxHeartbeats 1600000

namespace Work.SSGRoute.prop5

open Work.CohomologicalShrinking

noncomputable section

universe u v

/-! ## Getting rid of the `DecidableEq` instance of `Function.update`

The structure `MultilinearMap` carries a local `[DecidableEq ι]` instance, and `Function.update`
is *not* definitionally independent of that instance.  The lemmas `valFn_update_mul`,
`valFn_update_pow` and `valFn_update_commutator` were proved with the ambient instance, so we
provide instances-agnostic restatements (`…_gen`) by transporting along `update_decEq_congr`. -/

/-- `Function.update` does not depend on the chosen `DecidableEq` instance. -/
lemma update_decEq_congr {α : Sort u} {β : α → Sort v} (d d' : DecidableEq α)
    (f : (a : α) → β a) (a : α) (v : β a) :
    @Function.update α β d f a v = @Function.update α β d' f a v := by
  funext x
  by_cases h : x = a
  · rw [h]
    exact (@Function.update_self α β d a v f).trans (@Function.update_self α β d' a v f).symm
  · exact (@Function.update_of_ne α β d (a := x) (a' := a) h v f).trans
      (@Function.update_of_ne α β d' (a := x) (a' := a) h v f).symm

section Generic

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)

/-- Instance-agnostic form of `valFn_update_mul`. -/
lemma valFn_update_mul_gen [dec : DecidableEq (Fin j)]
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a b : Work.Shrinking.freeOperatorGroup G d) :
    valFn p G i j d hj hji (Function.update x k (a * b))
      = valFn p G i j d hj hji (Function.update x k a)
        + valFn p G i j d hj hji (Function.update x k b) := by
  rw [update_decEq_congr dec (instDecidableEqFin j) x k (a * b),
    update_decEq_congr dec (instDecidableEqFin j) x k a,
    update_decEq_congr dec (instDecidableEqFin j) x k b]
  exact valFn_update_mul p G i j d hj hji x k a b

/-- Instance-agnostic form of `valFn_update_pow_eq_nsmul`. -/
lemma valFn_update_pow_eq_nsmul_gen [dec : DecidableEq (Fin j)]
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a : Work.Shrinking.freeOperatorGroup G d) :
    ∀ n : ℕ, 1 ≤ n →
      valFn p G i j d hj hji (Function.update x k (a ^ n))
        = n • valFn p G i j d hj hji (Function.update x k a) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      rw [pow_succ, valFn_update_mul_gen p G i j d hj hji (dec := dec) x k (a ^ n) a, ih,
        succ_nsmul]

/-- `valFn` vanishes when the entry of the slot is `1`. -/
lemma valFn_update_one_gen [dec : DecidableEq (Fin j)]
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    valFn p G i j d hj hji
      (Function.update x k (1 : Work.Shrinking.freeOperatorGroup G d)) = 0 := by
  have h := valFn_update_mul_gen p G i j d hj hji (dec := dec) x k 1 1
  rw [mul_one] at h
  exact add_left_cancel (by rw [add_zero]; exact h.symm)

end Generic

/-! ## Descent of the slot maps to `F(d)/F(d)²` -/

/-- Shorthand for the top term `P₀ = ⊤` of the `p`-central series of `F(d)`. -/
abbrev Ptop (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    Subgroup (Work.Shrinking.freeOperatorGroup G d) :=
  Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 0

/-- Shorthand for the second term `P₁ = F(d)^p[F(d),F(d)]` of the `p`-central series of
`F(d)`. -/
abbrev Pone (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    Subgroup (Work.Shrinking.freeOperatorGroup G d) :=
  Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1

/-- The canonical map `F(d) → F(d)/F(d)² = F(d)/P₁`, in additive notation on the target. -/
def qmk (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (z : Work.Shrinking.freeOperatorGroup G d) : squareQuotient p G d :=
  Additive.ofMul (QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d))
    ⟨z, Subgroup.mem_top z⟩)

@[simp] lemma qmk_one (p : ℕ) (G : Type*) [Group G] (d : ℕ) :
    qmk p G d 1 = 0 := by
  show Additive.ofMul (QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d))
    ⟨(1 : Work.Shrinking.freeOperatorGroup G d), _⟩) = _
  rw [show (⟨(1 : Work.Shrinking.freeOperatorGroup G d), _⟩ :
      Ptop p G d) = 1 from Subtype.ext rfl, map_one, ofMul_one]

lemma qmk_mul (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (a b : Work.Shrinking.freeOperatorGroup G d) :
    qmk p G d (a * b) = qmk p G d a + qmk p G d b := by
  show Additive.ofMul (QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d))
      ⟨a * b, _⟩) = _
  rw [show (⟨a * b, _⟩ : Ptop p G d) = ⟨a, _⟩ * ⟨b, _⟩ from Subtype.ext rfl, map_mul,
    ofMul_mul]
  rfl

lemma qmk_inv (p : ℕ) (G : Type*) [Group G] (d : ℕ) (a : Work.Shrinking.freeOperatorGroup G d) :
    qmk p G d a⁻¹ = - qmk p G d a := by
  have h : qmk p G d a⁻¹ + qmk p G d a = 0 := by
    rw [add_comm, ← qmk_mul, mul_inv_cancel, qmk_one]
  exact eq_neg_of_add_eq_zero_left h

/-- The subgroup of `F(d)` on which the `k`-th slot map of `valFn` vanishes. -/
abbrev valKer (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    Subgroup (Work.Shrinking.freeOperatorGroup G d) :=
  { carrier := {a | valFn p G i j d hj hji (Function.update x k a) = 0}
    mul_mem' := by
      intro a b ha hb
      show valFn p G i j d hj hji (Function.update x k (a * b)) = 0
      rw [valFn_update_mul_gen p G i j d hj hji x k a b, ha, hb, add_zero]
    one_mem' := valFn_update_one_gen p G i j d hj hji x k
    inv_mem' := by
      intro a ha
      show valFn p G i j d hj hji (Function.update x k a⁻¹) = 0
      have h := valFn_update_mul_gen p G i j d hj hji x k a⁻¹ a
      rw [inv_mul_cancel, valFn_update_one_gen p G i j d hj hji x k, ha, add_zero] at h
      exact h.symm }

/-- The slot map kills the second term of the `p`-central series: it is additive in the slot,
kills `p`-th powers and kills commutators. -/
theorem pCentralSeries_one_le_valKer (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    (i j d : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1 ≤
      valKer p G i j d hj hji x k := by
  have hstep : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1
      = Work.Shrinking.pCentralStep p (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G d)) :=
    rfl
  rw [hstep, Work.Shrinking.pCentralStep]
  refine sup_le ?_ ?_
  · rw [Work.Shrinking.powSubgroup]
    refine (Subgroup.closure_le _).mpr ?_
    rintro a ⟨b, -, rfl⟩
    show valFn p G i j d hj hji (Function.update x k (b ^ p)) = 0
    exact valFn_update_pow p G i j d hj hji x k b
  · refine (Subgroup.commutator_le).mpr ?_
    intro a _ b _
    show valFn p G i j d hj hji (Function.update x k ⁅a, b⁆) = 0
    exact valFn_update_commutator p G i j d hj hji x k a b

/-- The `k`-th slot map of `valFn` as a homomorphism `F(d) →* Multiplicative E(d,τ)`. -/
def slotMul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    Work.Shrinking.freeOperatorGroup G d →* Multiplicative (E p G d i j) where
  toFun a := Multiplicative.ofAdd (valFn p G i j d hj hji (Function.update x k a))
  map_one' := by
    rw [valFn_update_one_gen p G i j d hj hji x k, ofAdd_zero]
  map_mul' a b :=
    congrArg Multiplicative.ofAdd (valFn_update_mul_gen p G i j d hj hji x k a b)

/-- The `k`-th slot map of `valFn`, descended to `F(d)/F(d)² →* Multiplicative E(d,τ)`. -/
def slotMulBar (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j) :
    Work.Shrinking.pCentralQuotient p (Work.Shrinking.freeOperatorGroup G d) 0 →*
      Multiplicative (E p G d i j) :=
  QuotientGroup.lift ((Pone p G d).subgroupOf (Ptop p G d))
    ((slotMul p G i j d hj hji x k).comp (Ptop p G d).subtype)
    (by
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      have hy' : (y : Work.Shrinking.freeOperatorGroup G d) ∈
          Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G d) 1 :=
        Subgroup.mem_subgroupOf.mp hy
      change Multiplicative.ofAdd
        (valFn p G i j d hj hji (Function.update x k (y : Work.Shrinking.freeOperatorGroup G d)))
        = 1
      have h0 : valFn p G i j d hj hji
          (Function.update x k (y : Work.Shrinking.freeOperatorGroup G d)) = 0 :=
        pCentralSeries_one_le_valKer p G i j d hj hji x k hy'
      rw [h0, ofAdd_zero])

lemma slotMulBar_mk (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    (a : Ptop p G d) :
    slotMulBar p G i j d hj hji x k
        (QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d)) a) =
      Multiplicative.ofAdd
        (valFn p G i j d hj hji
          (Function.update x k (a : Work.Shrinking.freeOperatorGroup G d))) := by
  rw [slotMulBar, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
  rfl

/-- **Well-definedness in one slot**: replacing the `k`-th entry of `x` by two elements with the
same image in `F(d)/F(d)²` does not change `valFn`. -/
theorem valFn_update_eq_of_qmk_eq (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    {a b : Work.Shrinking.freeOperatorGroup G d} (h : qmk p G d a = qmk p G d b) :
    valFn p G i j d hj hji (Function.update x k a)
      = valFn p G i j d hj hji (Function.update x k b) := by
  have h' : QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d))
      (⟨a, Subgroup.mem_top a⟩ : Ptop p G d)
      = QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d))
        (⟨b, Subgroup.mem_top b⟩ : Ptop p G d) := Additive.ofMul.injective h
  have h2 := congrArg (slotMulBar p G i j d hj hji x k) h'
  rw [slotMulBar_mk, slotMulBar_mk, Multiplicative.ofAdd.injective.eq_iff] at h2
  exact h2

/-- Instance-agnostic form of `valFn_update_eq_of_qmk_eq`. -/
theorem valFn_update_eq_of_qmk_eq_gen (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) [dec : DecidableEq (Fin j)]
    (x : Fin j → Work.Shrinking.freeOperatorGroup G d) (k : Fin j)
    {a b : Work.Shrinking.freeOperatorGroup G d} (h : qmk p G d a = qmk p G d b) :
    valFn p G i j d hj hji (Function.update x k a)
      = valFn p G i j d hj hji (Function.update x k b) := by
  rw [update_decEq_congr dec (instDecidableEqFin j) x k a,
    update_decEq_congr dec (instDecidableEqFin j) x k b]
  exact valFn_update_eq_of_qmk_eq p G i j d hj hji x k h

/-! ## Independence of representatives -/

/-- A representative in `F(d)` of an element of `F(d)/F(d)²`. -/
def repOf (p : ℕ) (G : Type*) [Group G] (d : ℕ) (z : squareQuotient p G d) :
    Work.Shrinking.freeOperatorGroup G d :=
  (Quotient.out (Additive.toMul z) : Ptop p G d)

lemma repOf_spec (p : ℕ) (G : Type*) [Group G] (d : ℕ) (z : squareQuotient p G d) :
    qmk p G d (repOf p G d z) = z := by
  have h : (⟨repOf p G d z, Subgroup.mem_top _⟩ : Ptop p G d)
      = Quotient.out (Additive.toMul z) := Subtype.ext rfl
  show Additive.ofMul (QuotientGroup.mk' ((Pone p G d).subgroupOf (Ptop p G d))
    ⟨repOf p G d z, _⟩) = _
  rw [h, QuotientGroup.mk'_apply]
  exact congrArg Additive.ofMul (QuotientGroup.out_eq' (Additive.toMul z))

/-- The value map is independent of the chosen representatives. -/
theorem valFn_congr (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i)
    {x y : Fin j → Work.Shrinking.freeOperatorGroup G d}
    (h : ∀ k, qmk p G d (x k) = qmk p G d (y k)) :
    valFn p G i j d hj hji x = valFn p G i j d hj hji y := by
  have key : ∀ (s : Finset (Fin j)) (u v : Fin j → Work.Shrinking.freeOperatorGroup G d),
      (∀ k ∈ s, qmk p G d (u k) = qmk p G d (v k)) → (∀ k ∉ s, u k = v k) →
      valFn p G i j d hj hji u = valFn p G i j d hj hji v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro u v _ h2
        congr 1
        funext k
        exact h2 k (by simp)
    | insert a s ha ih =>
        intro u v h1 h2
        set u' := Function.update u a (v a) with hu'
        have hstep1 : valFn p G i j d hj hji u = valFn p G i j d hj hji u' := by
          have hua : Function.update u a (u a) = u := by
            funext r
            rw [Function.update_apply]
            by_cases hr : r = a
            · rw [if_pos hr, hr]
            · rw [if_neg hr]
          rw [← hua, hu']
          exact valFn_update_eq_of_qmk_eq p G i j d hj hji u a
            (h1 a (Finset.mem_insert_self a s))
        have hstep2 : valFn p G i j d hj hji u' = valFn p G i j d hj hji v := by
          refine ih u' v ?_ ?_
          · intro k hk
            have hka : k ≠ a := fun hc => ha (hc ▸ hk)
            rw [hu', Function.update_apply, if_neg hka]
            exact h1 k (Finset.mem_insert_of_mem hk)
          · intro k hk
            by_cases hka : k = a
            · subst hka; rw [hu', Function.update_self]
            · rw [hu', Function.update_apply, if_neg hka]
              exact h2 k (by simp [hka, hk])
        exact hstep1.trans hstep2
  exact key Finset.univ x y (fun k _ => h k) (fun k hk => by simp at hk)

/-! ## The multilinear map and `θ` -/

def repTuple (p : ℕ) (G : Type*) [Group G] (d j : ℕ) (f : Fin j → squareQuotient p G d) :
    Fin j → Work.Shrinking.freeOperatorGroup G d :=
  fun k => repOf p G d (f k)

lemma repTuple_update (p : ℕ) (G : Type*) [Group G] (d j : ℕ) [dec : DecidableEq (Fin j)]
    (m : Fin j → squareQuotient p G d) (k : Fin j) (z : squareQuotient p G d) :
    repTuple p G d j (Function.update m k z)
      = Function.update (repTuple p G d j m) k (repOf p G d z) := by
  funext r
  show repOf p G d (Function.update m k z r)
      = Function.update (fun r => repOf p G d (m r)) k (repOf p G d z) r
  rw [Function.update_apply, Function.update_apply]
  by_cases hr : r = k <;> simp [hr]

def thetaFun (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (f : Fin j → squareQuotient p G d) : E p G d i j :=
  valFn p G i j d hj hji (repTuple p G d j f)

lemma thetaFun_eq (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j)
    (hji : j ≤ i) (f : Fin j → squareQuotient p G d) :
    thetaFun p G i j d hj hji f = valFn p G i j d hj hji (repTuple p G d j f) := rfl

lemma qmk_pow (p : ℕ) (G : Type*) [Group G] (d : ℕ)
    (z : Work.Shrinking.freeOperatorGroup G d) (n : ℕ) :
    qmk p G d (z ^ n) = n • qmk p G d z := by
  induction n with
  | zero => rw [pow_zero, qmk_one, zero_nsmul]
  | succ n ih =>
      rw [pow_succ, qmk_mul, ih, succ_nsmul]

def thetaMul (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    MultilinearMap (ZMod p) (fun _ : Fin j => squareQuotient p G d) (E p G d i j) where
  toFun f := thetaFun p G i j d hj hji f
  map_update_add' m k x y := by
    set X := repTuple p G d j m with hX
    have hL : thetaFun p G i j d hj hji (Function.update m k (x + y))
        = valFn p G i j d hj hji (Function.update X k (repOf p G d (x + y))) := by
      rw [thetaFun, repTuple_update, hX]
    have hR1 : thetaFun p G i j d hj hji (Function.update m k x)
        = valFn p G i j d hj hji (Function.update X k (repOf p G d x)) := by
      rw [thetaFun, repTuple_update, hX]
    have hR2 : thetaFun p G i j d hj hji (Function.update m k y)
        = valFn p G i j d hj hji (Function.update X k (repOf p G d y)) := by
      rw [thetaFun, repTuple_update, hX]
    have hrep : qmk p G d (repOf p G d (x + y))
        = qmk p G d (repOf p G d x * repOf p G d y) := by
      rw [qmk_mul, repOf_spec, repOf_spec, repOf_spec]
    have hstep : valFn p G i j d hj hji (Function.update X k (repOf p G d (x + y)))
        = valFn p G i j d hj hji (Function.update X k (repOf p G d x * repOf p G d y)) :=
      valFn_update_eq_of_qmk_eq_gen p G i j d hj hji X k hrep
    rw [hL, hR1, hR2, hstep,
      valFn_update_mul_gen p G i j d hj hji X k (repOf p G d x) (repOf p G d y)]
  map_update_smul' m k c x := by
    set X := repTuple p G d j m with hX
    have hL : thetaFun p G i j d hj hji (Function.update m k (c • x))
        = valFn p G i j d hj hji (Function.update X k (repOf p G d (c • x))) := by
      rw [thetaFun, repTuple_update, hX]
    have hR : c • thetaFun p G i j d hj hji (Function.update m k x)
        = c • valFn p G i j d hj hji (Function.update X k (repOf p G d x)) := by
      rw [thetaFun, repTuple_update, hX]
    have hcz : c • x = c.val • x := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul]
    have hrep : qmk p G d (repOf p G d (c • x)) = qmk p G d ((repOf p G d x) ^ c.val) := by
      rw [repOf_spec, qmk_pow, repOf_spec]
      exact hcz
    have hstep : valFn p G i j d hj hji (Function.update X k (repOf p G d (c • x)))
        = valFn p G i j d hj hji (Function.update X k ((repOf p G d x) ^ c.val)) :=
      valFn_update_eq_of_qmk_eq_gen p G i j d hj hji X k hrep
    rw [hL, hR, hstep]
    rcases Nat.eq_zero_or_pos c.val with h0 | hpos
    · rw [h0, pow_zero]
      have hc0 : c = 0 := by rw [← ZMod.natCast_zmod_val c, h0, Nat.cast_zero]
      rw [hc0, zero_smul]
      exact valFn_update_one_gen p G i j d hj hji X k
    · rw [valFn_update_pow_eq_nsmul_gen p G i j d hj hji X k (repOf p G d x) c.val hpos,
        ← Nat.cast_smul_eq_nsmul (ZMod p) c.val
          (valFn p G i j d hj hji (Function.update X k (repOf p G d x))),
        ZMod.natCast_zmod_val c]

/-- The `𝔽_p`-linear map `θ_τ(d) : (F(d)/F(d)²)^{⊗j} → E(d,τ)` of Proposition 5. -/
def thetaLin (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    (⨂[ZMod p]^j (squareQuotient p G d)) →ₗ[ZMod p] E p G d i j :=
  PiTensorProduct.lift (thetaMul p G i j d hj hji)

lemma thetaLin_tprod (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j)
    (hji : j ≤ i) (f : Fin j → squareQuotient p G d) :
    thetaLin p G i j d hj hji (PiTensorProduct.tprod (ZMod p) f)
      = thetaFun p G i j d hj hji f :=
  PiTensorProduct.lift.tprod f

/-- On the class of a tuple of group elements, `θ` is the paper's value map. -/
lemma thetaLin_tprod_qmk (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j d : ℕ) (hj : 1 ≤ j)
    (hji : j ≤ i) (x : Fin j → Work.Shrinking.freeOperatorGroup G d) :
    thetaLin p G i j d hj hji (PiTensorProduct.tprod (ZMod p) (fun k => qmk p G d (x k)))
      = valFn p G i j d hj hji x := by
  rw [thetaLin_tprod, thetaFun]
  exact valFn_congr p G i j d hj hji (fun k => by
    show qmk p G d (repOf p G d (qmk p G d (x k))) = qmk p G d (x k)
    rw [repOf_spec])

end

end Work.SSGRoute.prop5
