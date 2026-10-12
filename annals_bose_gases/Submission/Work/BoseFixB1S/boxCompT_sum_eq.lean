import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxSpectralDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxCompT_sum_eq` — the resolution of unity by the three-way box components

The **three-way joint components** of the commuting family of FS box projections

    ψ_{S,T} := (∏_{i∈S}Pᵢ)(∏_{j∈T}Qⱼ)(∏_{k∉S∪T}Rₖ) Φ ,   S ⊥ T ,

realised by the fold `boxCompT` over `List.finRange N` at the FS-faithful slot operators
`Pᵢ = Work.UBBInputs8.boxPInd` (`1_A(·ᵢ)·`mean over `A` in slot `i`), `Qᵢ = boxQInd` and the
complement multiplier `Rᵢ = boxOut = 1 − 1_A(·ᵢ)`
(`Submission/Work/BoseFixB1S/BoxSpectralDefs.lean`), resolve the identity:

    Σ_{(S,T), S ⊥ T} ψ_{S,T} = id .

This is the *third* member of the joint-component family that FS's sharp (operator-`√`) completion
of squares consumes; unlike the two-way `Σ_S boxComp_S = (∏ᵢ1_A(xᵢ))·id` (see
`Work.BoseFixB1S.boxComp_sum_eq`) the three-way family carries no box-indicator factor.

## Math

Everything is pointwise algebra.  FS `eq:HBU` give the slot projections

    PᵢΦ x = |A|⁻¹(∫_{z∈A} Φ(x|i↦z))·1_A(xᵢ) ,   QᵢΦ x = 1_A(xᵢ)·Φ x − PᵢΦ x ,   RᵢΦ x = (1−1_A(xᵢ))·Φ x

so at **every** point `x` and for **every** state `Φ` the three slot operators split the identity,

    PᵢΦ + QᵢΦ + RᵢΦ = Φ        (`boxPatOp_sum`),

the `Pᵢ`-term cancelling against the one *hidden inside* the definition of `Qᵢ` and leaving
`1_A(xᵢ)Φ x + (1−1_A(xᵢ))Φ x = Φ x`.  Expanding `∏ᵢ(Pᵢ + Qᵢ + Rᵢ) = ∏ᵢ 1 = 1` by distributivity gives
the resolution: the ways of choosing, slot by slot, one of `P, Q, R` are exactly the pairs of
*disjoint* finsets `(S,T)` (with `R` in the slots outside `S ∪ T`), and the fold `boxCompT` applies
them in the order of `List.finRange N`.

The two combinatorial ingredients are proved here from scratch (Mathlib has neither):

* `sumFilterDisjointFin3` — the disjoint pairs `(S,T)` biject with the maps `Fin N → Fin 3`
  (`0` on `S`, `1` on `T`, `2` outside), with inverse `c ↦ ({i | c i = 0}, {i | c i = 1})`;
* `sumFoldFinRangeTriple` — the abstract resolution of unity: for any slot-operator family
  `Op` with `Σ_{k<3} Op i k = id` pointwise, `Σ_{all choices} fold = id`.  The proof is an
  induction on `N` splitting the *first* slot of `List.finRange (N+1)`: the head operator is applied
  innermost, so the induction hypothesis is used with the state `Op 0 b Ψ` and **no linearity of the
  operators is ever needed**.

Consequences: no measure theory, no integrability, no continuity of `Φ` and no geometry (`hAc`, the
box `abox N ℓ`) enters — `boxCompT_sum_eq` is a *pointwise* identity holding for every `Φ` and every
`x`.  The hypotheses `hℓ, hvol, hA, hvolA, hAc, hΦc` of the statement are therefore unused; they are
kept verbatim because they are the ambient hypotheses of the caller's context.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. The combinatorial bijection: disjoint pairs of slot sets ↔ choices `Fin N → Fin 3` -/

/-- The **choice map** of a pair `(S,T)` of slot sets: `0` on `S`, `1` on `T` and `2` outside. -/
def choiceOf {N : ℕ} (p : Finset (Fin N) × Finset (Fin N)) : Fin N → Fin 3 :=
  fun i => if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2

/-- The choice map is `0` exactly on the first slot set (no disjointness needed). -/
lemma choiceOf_zero_iff {N : ℕ} (p : Finset (Fin N) × Finset (Fin N)) (i : Fin N) :
    choiceOf p i = 0 ↔ i ∈ p.1 := by
  unfold choiceOf
  by_cases h : i ∈ p.1
  · simp [h]
  · by_cases h2 : i ∈ p.2 <;> simp [h, h2]

/-- For a **disjoint** pair, the choice map is `1` exactly on the second slot set. -/
lemma choiceOf_one_iff {N : ℕ} {p : Finset (Fin N) × Finset (Fin N)} (hp : Disjoint p.1 p.2)
    (i : Fin N) : choiceOf p i = 1 ↔ i ∈ p.2 := by
  unfold choiceOf
  by_cases h : i ∈ p.1
  · have h2 : i ∉ p.2 := (Finset.disjoint_left.mp hp) h
    simp [h, h2]
  · by_cases h2 : i ∈ p.2 <;> simp [h, h2]

/-- The choice map recovers the value `b` from the three-way case split: the `0/1/2`-branch is the
identity on `Fin 3`. -/
lemma fin3_ite_self (b : Fin 3) :
    (if b = 0 then (0 : Fin 3) else if b = 1 then 1 else 2) = b := by
  fin_cases b <;> simp

/-- **Reindexing along the bijection.**  Summing an arbitrary `AddCommMonoid`-valued function of the
choice pattern over the *disjoint* pairs `(S,T)` is the same as summing it over all maps
`Fin N → Fin 3`.  The inverse map is `c ↦ ({i | c i = 0}, {i | c i = 1})`. -/
theorem sumFilterDisjointFin3 {N : ℕ} {α : Type*} [AddCommMonoid α]
    (F : (Fin N → Fin 3) → α) :
    (∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
        (fun p => Disjoint p.1 p.2),
      F (fun i => if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2))
      = ∑ c : Fin N → Fin 3, F c := by
  classical
  refine Finset.sum_bij (fun p _ => choiceOf p) (fun p _ => Finset.mem_univ _) ?_ ?_ ?_
  · -- injectivity of the choice map on disjoint pairs
    intro a ha b hb hab
    obtain ⟨-, hda⟩ := Finset.mem_filter.mp ha
    obtain ⟨-, hdb⟩ := Finset.mem_filter.mp hb
    have h1 : a.1 = b.1 := by
      ext i
      rw [← choiceOf_zero_iff a i, ← choiceOf_zero_iff b i, hab]
    have h2 : a.2 = b.2 := by
      ext i
      rw [← choiceOf_one_iff hda i, ← choiceOf_one_iff hdb i, hab]
    exact Prod.ext h1 h2
  · -- surjectivity: the disjoint pair of level sets of `c`
    intro c _
    refine ⟨(Finset.univ.filter (fun i => c i = 0), Finset.univ.filter (fun i => c i = 1)), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.disjoint_left]
      intro i hi hij
      rw [Finset.mem_filter] at hi hij
      rw [hi.2] at hij
      exact absurd hij.2 (by decide)
    · funext i
      show (if i ∈ Finset.univ.filter (fun i => c i = 0) then (0 : Fin 3)
          else if i ∈ Finset.univ.filter (fun i => c i = 1) then 1 else 2) = c i
      simpa [Finset.mem_filter] using fin3_ite_self (c i)
  · intro p hp
    rfl

/-! ## 2. The abstract resolution of unity for a fold over `List.finRange`

The slot operators are not assumed linear: only the pointwise three-term split is used.  At the
induction step for `N + 1`, `List.finRange (N+1) = 0 :: (List.finRange N).map Fin.succ`, and the head
slot is applied *innermost*, so the sum over the choice at the head slot is taken last and the
induction hypothesis is applied to the state `Op 0 b Ψ`. -/

theorem sumFoldFinRangeTriple {N : ℕ} {F : Type*} [AddCommMonoid F]
    (Op : Fin N → Fin 3 → F → F)
    (hOp : ∀ i (Ψ : F), Op i 0 Ψ + Op i 1 Ψ + Op i 2 Ψ = Ψ) (Ψ : F) :
    (∑ c : Fin N → Fin 3, (List.finRange N).foldl (fun g i => Op i (c i) g) Ψ) = Ψ := by
  revert Op hOp Ψ
  induction N with
  | zero =>
    intro Op hOp Ψ
    simp [Finset.sum_const]
  | succ N ih =>
    intro Op hOp Ψ
    have hbody : ∀ c : Fin (N + 1) → Fin 3,
        (List.finRange (N + 1)).foldl (fun g i => Op i (c i) g) Ψ
          = (List.finRange N).foldl (fun g j => Op (Fin.succ j) (c (Fin.succ j)) g)
              (Op 0 (c 0) Ψ) := by
      intro c
      rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    let G : (Fin (N + 1) → Fin 3) → F :=
      fun c => (List.finRange N).foldl (fun g j => Op (Fin.succ j) (c (Fin.succ j)) g)
        (Op 0 (c 0) Ψ)
    calc (∑ c : Fin (N + 1) → Fin 3, (List.finRange (N + 1)).foldl (fun g i => Op i (c i) g) Ψ)
        = ∑ c : Fin (N + 1) → Fin 3, G c := Finset.sum_congr rfl (fun c _ => hbody c)
      _ = ∑ q : Fin 3 × (Fin N → Fin 3),
            G ((Fin.consEquiv (fun _ : Fin (N + 1) => Fin 3)) q) := by
          rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 1) => Fin 3)) G]
      _ = ∑ b : Fin 3, ∑ c' : Fin N → Fin 3,
            (List.finRange N).foldl (fun g j => Op (Fin.succ j) (c' j) g) (Op 0 b Ψ) := by
          rw [Fintype.sum_prod_type]
          simp only [G, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      _ = ∑ b : Fin 3, Op 0 b Ψ := by
          apply Finset.sum_congr rfl
          intro b _
          exact ih (fun j k g => Op (Fin.succ j) k g) (fun j Υ => hOp (Fin.succ j) Υ) (Op 0 b Ψ)
      _ = Ψ := by
          rw [Fin.sum_univ_three]
          exact hOp 0 Ψ

/-! ## 3. The slot operator of `boxCompT` and the identification of the fold -/

/-- The operator attached to slot `i` by the **choice** `b ∈ {0,1,2}`: `0 ↦ Pᵢ`, `1 ↦ Qᵢ`,
`2 ↦ Rᵢ` (the same three branches as in `boxCompT`). -/
noncomputable def boxPatOp {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (b : Fin 3) :
    (X N → ℝ) → (X N → ℝ) :=
  if b = 0 then Work.UBBInputs8.boxPInd volA A i
  else if b = 1 then Work.UBBInputs8.boxQInd volA A i
  else boxOut A i

/-- **The three-term split at a slot**: `Pᵢ + Qᵢ + Rᵢ = 1`, pointwise for every state (the `Pᵢ`-term
cancels against the one inside the definition of `Qᵢ`). -/
theorem boxPatOp_sum {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (Ψ : X N → ℝ) :
    boxPatOp volA A i 0 Ψ + boxPatOp volA A i 1 Ψ + boxPatOp volA A i 2 Ψ = Ψ := by
  have h0 : boxPatOp volA A i 0 = Work.UBBInputs8.boxPInd volA A i := by simp [boxPatOp]
  have h1 : boxPatOp volA A i 1 = Work.UBBInputs8.boxQInd volA A i := by simp [boxPatOp]
  have h2 : boxPatOp volA A i 2 = boxOut A i := by simp [boxPatOp]
  rw [h0, h1, h2]
  funext x
  simp only [Pi.add_apply, Work.UBBInputs8.boxPInd, Work.UBBInputs8.boxQInd, boxOut]
  ring

/-- `boxCompT` is the fold of the slot operators selected by the choice pattern of `(S,T)`. -/
theorem boxCompT_eq_foldl {N : ℕ} (volA : ℝ) (A : Set E3) (S T : Finset (Fin N))
    (Φ : X N → ℝ) :
    boxCompT volA A S T Φ
      = (List.finRange N).foldl (fun g i =>
          boxPatOp volA A i (if i ∈ S then 0 else if i ∈ T then 1 else 2) g) Φ := by
  unfold boxCompT
  have hfun : (fun g i => (if i ∈ S then Work.UBBInputs8.boxPInd volA A i
        else if i ∈ T then Work.UBBInputs8.boxQInd volA A i else boxOut A i) g)
      = (fun g i => boxPatOp volA A i (if i ∈ S then 0 else if i ∈ T then 1 else 2) g) := by
    funext g i
    by_cases hS : i ∈ S
    · simp [boxPatOp, hS]
    · by_cases hT : i ∈ T
      · simp [boxPatOp, hS, hT]
      · simp [boxPatOp, hS, hT]
  rw [hfun]

/-! ## 4. The resolution of unity -/

theorem boxCompT_sum_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) {Φ : Submission.BoseGases.X N → ℝ}
    (hΦc : Continuous Φ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      (∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
          (fun p => Disjoint p.1 p.2),
        Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ x) = Φ x := by
  intro x hx
  have hsum : (∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
      (fun p => Disjoint p.1 p.2), Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ) = Φ := by
    calc (∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2), Work.BoseFixB1S.boxCompT volA A p.1 p.2 Φ)
        = ∑ p ∈ (Finset.univ : Finset (Finset (Fin N) × Finset (Fin N))).filter
            (fun p => Disjoint p.1 p.2),
            (List.finRange N).foldl (fun g i => boxPatOp volA A i
              (if i ∈ p.1 then 0 else if i ∈ p.2 then 1 else 2) g) Φ :=
          Finset.sum_congr rfl (fun p _ => boxCompT_eq_foldl volA A p.1 p.2 Φ)
      _ = ∑ c : Fin N → Fin 3, (List.finRange N).foldl (fun g i =>
            boxPatOp volA A i (c i) g) Φ :=
          sumFilterDisjointFin3 (fun c => (List.finRange N).foldl (fun g i =>
            boxPatOp volA A i (c i) g) Φ)
      _ = Φ := sumFoldFinRangeTriple (fun i b g => boxPatOp volA A i b g)
          (fun i Ψ => boxPatOp_sum volA A i Ψ) Φ
  simpa [Finset.sum_apply] using congr_fun hsum x

end Work.BoseFixB1S
