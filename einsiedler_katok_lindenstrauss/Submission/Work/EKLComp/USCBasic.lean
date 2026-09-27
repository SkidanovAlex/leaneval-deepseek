import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLRelCross.Instances

/-!
# C4b — upper semicontinuity of entropy on compacta (EKL §9)

Definitions and API for the proof of `Work.EKLContract.P_USC`.  The proof follows EKL §9
(Lemma 9.1, Prop 9.2, Cor 9.3) but is metric-free: "closeness" is always the relation
`y ∈ ball δ x` (`y = g • x`, `g ∈ V δ`), and instead of diameters of partition atoms we use
`AtomSmall K δ P`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-! ## 1. The centraliser of `aDiag t`, its powers and conjugation -/

/-- The centraliser of `aDiag t` (EKL's `C`): the "neutral" direction. -/
def Csub (t : Fin 3 → ℝ) : Subgroup SL3 := Subgroup.centralizer {aDiag t}

/-- `a^z` as an element of `SL₃(ℝ)`, `z : ℤ` (`aDiag` applied to `z • t`). -/
def aZ (t : Fin 3 → ℝ) (n : ℤ) : SL3 := aDiag (fun i => (n : ℝ) * t i)

/-- Conjugation by `a^z`. -/
def conjZ (t : Fin 3 → ℝ) (n : ℤ) (g : SL3) : SL3 := aZ t n * g * (aZ t n)⁻¹

theorem aZ_zero (t : Fin 3 → ℝ) : aZ t 0 = 1 := by
  rw [aZ]
  have h : (fun i : Fin 3 => (((0 : ℤ)) : ℝ) * t i) = 0 := by ext i; simp
  rw [h, aDiag_zero]

theorem aZ_add (t : Fin 3 → ℝ) (m n : ℤ) : aZ t (m + n) = aZ t m * aZ t n := by
  have h : (fun i : Fin 3 => (((m + n : ℤ)) : ℝ) * t i)
      = (fun i : Fin 3 => ((m : ℤ) : ℝ) * t i) + (fun i : Fin 3 => ((n : ℤ) : ℝ) * t i) := by
    ext i
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [aZ, aZ, aZ, h, aDiag_add]

theorem aZ_one (t : Fin 3 → ℝ) : aZ t 1 = aDiag t := by
  rw [aZ]
  congr 1
  ext i; simp

theorem aZ_nat (t : Fin 3 → ℝ) (n : ℕ) : aZ t (n : ℤ) = (aDiag t) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, aZ_zero, pow_zero]
  | succ k ih =>
      have h : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [h, aZ_add, ih, aZ_one, pow_succ]

theorem aZ_mul_neg (t : Fin 3 → ℝ) (n : ℤ) : aZ t n * aZ t (-n) = 1 := by
  rw [← aZ_add]
  have h : n + -n = (0 : ℤ) := by ring
  rw [h, aZ_zero]

theorem aZ_eq_inv (t : Fin 3 → ℝ) (n : ℤ) : aZ t (-n) = (aZ t n)⁻¹ :=
  eq_inv_of_mul_eq_one_right (aZ_mul_neg t n)

theorem aZ_eq_zpow (t : Fin 3 → ℝ) (n : ℤ) : aZ t n = (aDiag t) ^ n := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk, aZ_nat, zpow_natCast]
  · rw [hk, aZ_eq_inv, aZ_nat, zpow_neg, zpow_natCast]

theorem conjZ_zero (t : Fin 3 → ℝ) (g : SL3) : conjZ t 0 g = g := by
  rw [conjZ, aZ_zero, one_mul, inv_one, mul_one]

/-- The underlying matrix of `aZ t n`. -/
theorem toMat_aZ (t : Fin 3 → ℝ) (n : ℤ) :
    toMat (aZ t n) = Matrix.diagonal (fun i => Real.exp ((n : ℝ) * (t i - (∑ j, t j) / 3))) := by
  rw [aZ, toMat_aDiag]
  congr 1
  ext i
  rw [← Finset.mul_sum]
  ring

/-- Entries of `g * aDiag t`. -/
theorem toMat_mul_aDiag (t : Fin 3 → ℝ) (g : SL3) (i j : Fin 3) :
    toMat (g * aDiag t) i j = toMat g i j * Real.exp (t j - (∑ k, t k) / 3) := by
  rw [toMat_mul, toMat_aDiag, Matrix.mul_diagonal]

/-- Entries of `aDiag t * g`. -/
theorem toMat_aDiag_mul (t : Fin 3 → ℝ) (g : SL3) (i j : Fin 3) :
    toMat (aDiag t * g) i j = Real.exp (t i - (∑ k, t k) / 3) * toMat g i j := by
  rw [toMat_mul, toMat_aDiag, Matrix.diagonal_mul]

/-- **Entrywise conjugation formula.**  For all `i, j` and `n : ℤ`,
`(aⁿ g a⁻ⁿ)_{ij} = e^{n (t_i - t_j)} g_{ij}`. -/
theorem conjZ_apply (t : Fin 3 → ℝ) (n : ℤ) (g : SL3) (i j : Fin 3) :
    toMat (conjZ t n g) i j = Real.exp ((n : ℝ) * (t i - t j)) * toMat g i j := by
  have h2 : toMat ((aZ t n)⁻¹)
      = Matrix.diagonal (fun i => Real.exp ((-(n : ℝ)) * (t i - (∑ j, t j) / 3))) := by
    rw [← aZ_eq_inv, toMat_aZ]
    congr 1
    ext i
    push_cast
    ring
  have h1 : toMat (conjZ t n g) =
      toMat (aZ t n) * toMat g * toMat ((aZ t n)⁻¹) := by
    rw [conjZ, toMat_mul, toMat_mul]
  have hE : Real.exp ((n : ℝ) * (t i - (∑ j, t j) / 3))
        * Real.exp ((-(n : ℝ)) * (t j - (∑ j, t j) / 3))
      = Real.exp ((n : ℝ) * (t i - t j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h1, toMat_aZ, h2, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_assoc,
    mul_comm (toMat g i j), ← mul_assoc, hE]

/-- `conjZ` is an action of `ℤ`. -/
theorem conjZ_add (t : Fin 3 → ℝ) (m n : ℤ) (g : SL3) :
    conjZ t (m + n) g = conjZ t m (conjZ t n g) := by
  apply ext_apply
  intro i j
  change toMat (conjZ t (m + n) g) i j = toMat (conjZ t m (conjZ t n g)) i j
  rw [conjZ_apply, conjZ_apply, conjZ_apply, ← mul_assoc, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **The centraliser is the set of matrices with zero entries where `t i ≠ t j`.** -/
theorem mem_Csub_iff (t : Fin 3 → ℝ) (g : SL3) :
    g ∈ Csub t ↔ ∀ i j, t i ≠ t j → toMat g i j = 0 := by
  rw [Csub, Subgroup.mem_centralizer_iff]
  constructor
  · intro h i j hij
    have h' : Real.exp (t i - (∑ k, t k) / 3) * toMat g i j
        = toMat g i j * Real.exp (t j - (∑ k, t k) / 3) := by
      have hh := congrFun (congrFun (congrArg toMat (h (aDiag t) (Set.mem_singleton _))) i) j
      simpa only [toMat_aDiag_mul, toMat_mul_aDiag] using hh
    have hne : Real.exp (t i - (∑ k, t k) / 3) ≠ Real.exp (t j - (∑ k, t k) / 3) := by
      intro he
      exact hij (by have := Real.exp_injective he; linarith)
    by_contra hA
    have h2 : (Real.exp (t i - (∑ k, t k) / 3) - Real.exp (t j - (∑ k, t k) / 3)) * toMat g i j
        = 0 := by
      linear_combination h'
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hA))
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    apply ext_apply
    intro i j
    change toMat (aDiag t * g) i j = toMat (g * aDiag t) i j
    rw [toMat_aDiag_mul, toMat_mul_aDiag]
    by_cases hij : t i = t j
    · rw [hij]; ring
    · rw [h i j hij, mul_zero, zero_mul]

/-- Elements of the centraliser commute with `aZ t n`. -/
theorem Csub_comm (t : Fin 3 → ℝ) {c : SL3} (hc : c ∈ Csub t) (n : ℤ) :
    aZ t n * c = c * aZ t n := by
  have hbase : Commute (aDiag t) c :=
    (Subgroup.mem_centralizer_iff.mp hc) _ (Set.mem_singleton _)
  rw [aZ_eq_zpow]
  exact Commute.zpow_left hbase n

/-! ## 2. The metric-free closeness relation `ball δ x` -/

/-- `V δ` is monotone in `δ`. -/
theorem V_mono {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' :=
  fun _ hg i j => lt_of_lt_of_le (hg i j) h

theorem one_mem_V {δ : ℝ} (hδ : 0 < δ) : (1 : SL3) ∈ V δ := by
  intro i j
  have h1 : (1 : SL3) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := rfl
  rw [h1, sub_self, abs_zero]
  exact hδ

/-- `ball δ x = {y | y = g • x, g ∈ V δ}`: the metric-free `δ`-neighbourhood of `x`. -/
def ball (δ : ℝ) (x : X3) : Set X3 := (fun g : SL3 => g • x) '' (V δ)

theorem mem_ball {δ : ℝ} {x y : X3} : y ∈ ball δ x ↔ ∃ g ∈ V δ, g • x = y := Iff.rfl

theorem ball_mono {δ δ' : ℝ} (h : δ ≤ δ') (x : X3) : ball δ x ⊆ ball δ' x :=
  Set.image_mono (V_mono h)

theorem self_mem_ball {δ : ℝ} (hδ : 0 < δ) (x : X3) : x ∈ ball δ x :=
  ⟨1, one_mem_V hδ, one_smul _ _⟩

theorem isOpen_V__USCBasic (δ : ℝ) : IsOpen (V δ) := by
  rw [Work.EKLContract.Lemmas.V_eq_iInter]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_lt (by fun_prop) continuous_const

/-- `ball δ x` is open: `V δ` is open and the orbit map is an open quotient map. -/
theorem isOpen_ball (δ : ℝ) (x : X3) : IsOpen (ball δ x) := by
  induction x using Quotient.ind with
  | _ g₀ =>
      have hset : ball δ (QuotientGroup.mk g₀)
          = (QuotientGroup.mk '' ((fun g : SL3 => g * g₀) '' (V δ)) : Set X3) := by
        ext y
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact ⟨g * g₀, ⟨g, hg, rfl⟩, Work.EKLContract.Lemmas.mkX_mul g g₀⟩
        · rintro ⟨z, ⟨g, hg, rfl⟩, rfl⟩
          exact ⟨g, hg, (Work.EKLContract.Lemmas.mkX_mul g g₀).symm⟩
      rw [hset]
      have hopen : IsOpen ((fun g : SL3 => g * g₀) '' (V δ)) :=
        isOpenMap_mul_right g₀ (V δ) (isOpen_V__USCBasic δ)
      exact QuotientGroup.isOpenMap_coe _ hopen

/-- The product of two `V δ`-small elements is `V (5δ)`-small (`δ ≤ 1`). -/
theorem mul_mem_V {δ : ℝ} (hδ : 0 < δ) (h1 : δ ≤ 1/2) {g h : SL3} (hg : g ∈ V δ)
    (hh : h ∈ V δ) : g * h ∈ V (4 * δ) := by
  intro i j
  have hX : ∀ k l : Fin 3, |(toMat g - 1) k l| < δ := by
    intro k l
    rw [Matrix.sub_apply, Matrix.one_apply]
    exact hg k l
  have hY : ∀ k l : Fin 3, |(toMat h - 1) k l| < δ := by
    intro k l
    rw [Matrix.sub_apply, Matrix.one_apply]
    exact hh k l
  change |(toMat (g * h) - 1) i j| < 4 * δ
  have key : (toMat (g * h) - 1) i j
      = ((toMat g - 1) * (toMat h - 1)) i j + (toMat g - 1) i j + (toMat h - 1) i j := by
    have h2 : toMat (g * h) - 1
        = (toMat g - 1) * (toMat h - 1) + (toMat g - 1) + (toMat h - 1) := by
      rw [toMat_mul]
      noncomm_ring
    rw [h2, Matrix.add_apply, Matrix.add_apply]
  rw [key]
  have hXY : |((toMat g - 1) * (toMat h - 1)) i j| ≤ 3 * δ * δ := by
    rw [Matrix.mul_apply]
    calc |∑ k, (toMat g - 1) i k * (toMat h - 1) k j|
        ≤ ∑ k, |(toMat g - 1) i k * (toMat h - 1) k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3, δ * δ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul (le_of_lt (hX i k)) (le_of_lt (hY k j)) (abs_nonneg _) (le_of_lt hδ)
      _ = 3 * δ * δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num
          ring
  have h1' : |(toMat g - 1) i j| ≤ δ := le_of_lt (hX i j)
  have h2' : |(toMat h - 1) i j| ≤ δ := le_of_lt (hY i j)
  have : |((toMat g - 1) * (toMat h - 1)) i j + (toMat g - 1) i j + (toMat h - 1) i j|
      ≤ 3 * δ * δ + δ + δ := by
    calc |((toMat g - 1) * (toMat h - 1)) i j + (toMat g - 1) i j + (toMat h - 1) i j|
        ≤ |((toMat g - 1) * (toMat h - 1)) i j + (toMat g - 1) i j| + |(toMat h - 1) i j| :=
          abs_add_le _ _
      _ ≤ (|((toMat g - 1) * (toMat h - 1)) i j| + |(toMat g - 1) i j|) + |(toMat h - 1) i j| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ (3 * δ * δ + δ) + δ := by gcongr
  linarith [this, mul_le_mul_of_nonneg_left h1 hδ.le, hδ]

/-- Two successive `V δ`-displacements from the same point: entries add up. -/
theorem ball_trans {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) {x y z : X3}
    (hy : y ∈ ball δ x) (hz : z ∈ ball δ y) : z ∈ ball (4 * δ) x := by
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨h, hh, rfl⟩ := hz
  refine ⟨h * g, mul_mem_V hδ hδ1 hh hg, ?_⟩
  show (h * g) • x = h • (g • x)
  rw [mul_smul]

/-! ## 3. The join of two finite partitions -/

section Join

variable {X : Type*} [MeasurableSpace X]

/-- The common refinement (join) of two finite partitions, indexed via
`finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`. -/
def joinPart__USCBasic (P Q : FinPart X) : FinPart X where
  n := P.n * Q.n
  parts := fun k => P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2
  measurable := fun k => (P.measurable _).inter (Q.measurable _)
  disjoint := by
    rw [Pairwise]
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rw [Set.mem_inter_iff] at hx1 hx2
    by_cases h1 : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · have h2 : (finProdFinEquiv.symm k).2 ≠ (finProdFinEquiv.symm l).2 := by
        intro h2
        refine hkl ?_
        have hp : finProdFinEquiv.symm k = finProdFinEquiv.symm l := Prod.ext h1 h2
        rw [← Equiv.apply_symm_apply finProdFinEquiv k, ← Equiv.apply_symm_apply finProdFinEquiv l,
          hp]
      exact (Q.disjoint h2).le_bot ⟨hx1.2, hx2.2⟩
    · exact (P.disjoint h1).le_bot ⟨hx1.1, hx2.1⟩
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hxP : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact trivial
    have hxQ : x ∈ ⋃ j, Q.parts j := by rw [Q.cover]; exact trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxQ
    refine Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), ?_⟩
    have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
      Equiv.symm_apply_apply _ _
    rw [hk]
    exact ⟨hi, hj⟩

theorem joinPart_parts__USCBasic (P Q : FinPart X) (k : Fin (P.n * Q.n)) :
    (joinPart__USCBasic P Q).parts k
      = P.parts (finProdFinEquiv.symm k).1 ∩ Q.parts (finProdFinEquiv.symm k).2 := rfl

theorem Refines_joinPart_left (P Q : FinPart X) : Refines (joinPart__USCBasic P Q) P := by
  intro k
  exact ⟨_, Set.inter_subset_left⟩

theorem Refines_joinPart_right (P Q : FinPart X) : Refines (joinPart__USCBasic P Q) Q := by
  intro k
  exact ⟨_, Set.inter_subset_right⟩

theorem partSigma_joinPart_le (P Q : FinPart X) :
    partSigma (joinPart__USCBasic P Q) ≤ partSigma P ⊔ partSigma Q := by
  rw [partSigma]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨k, rfl⟩
  have hP : MeasurableSet[partSigma P] (P.parts (finProdFinEquiv.symm k).1) :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
  have hQ : MeasurableSet[partSigma Q] (Q.parts (finProdFinEquiv.symm k).2) :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)
  exact MeasurableSet.inter (MeasurableSpace.le_def.mp le_sup_left _ hP)
    (MeasurableSpace.le_def.mp le_sup_right _ hQ)

theorem partSigma_le_joinPart_left (P Q : FinPart X) : partSigma P ≤ partSigma (joinPart__USCBasic P Q) := by
  rw [partSigma]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, rfl⟩
  have h : P.parts i = ⋃ j : Fin Q.n, (joinPart__USCBasic P Q).parts (finProdFinEquiv (i, j)) := by
    ext x
    constructor
    · intro hx
      have hxQ : x ∈ ⋃ j, Q.parts j := by rw [Q.cover]; exact trivial
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxQ
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
        Equiv.symm_apply_apply _ _
      rw [joinPart_parts__USCBasic, hk]
      exact ⟨hx, hj⟩
    · intro hx
      obtain ⟨j, hx'⟩ := Set.mem_iUnion.mp hx
      have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
        Equiv.symm_apply_apply _ _
      rw [joinPart_parts__USCBasic, hk] at hx'
      exact hx'.1
  rw [h]
  refine MeasurableSet.iUnion fun j => ?_
  exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)

theorem partSigma_le_joinPart_right (P Q : FinPart X) : partSigma Q ≤ partSigma (joinPart__USCBasic P Q) := by
  rw [partSigma]
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨j, rfl⟩
  have h : Q.parts j = ⋃ i : Fin P.n, (joinPart__USCBasic P Q).parts (finProdFinEquiv (i, j)) := by
    ext x
    constructor
    · intro hx
      have hxP : x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxP
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
        Equiv.symm_apply_apply _ _
      rw [joinPart_parts__USCBasic, hk]
      exact ⟨hi, hx⟩
    · intro hx
      obtain ⟨i, hx'⟩ := Set.mem_iUnion.mp hx
      have hk : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
        Equiv.symm_apply_apply _ _
      rw [joinPart_parts__USCBasic, hk] at hx'
      exact hx'.2
  rw [h]
  refine MeasurableSet.iUnion fun i => ?_
  exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self _)

theorem partSigma_joinPart (P Q : FinPart X) :
    partSigma (joinPart__USCBasic P Q) = partSigma P ⊔ partSigma Q :=
  le_antisymm (partSigma_joinPart_le P Q)
    (sup_le (partSigma_le_joinPart_left P Q) (partSigma_le_joinPart_right P Q))

theorem Refines_of_joinPart {P Q R : FinPart X} (h : Refines R (joinPart__USCBasic P Q)) : Refines R P :=
  fun i => by
    obtain ⟨j, hj⟩ := h i
    obtain ⟨k, hk⟩ := Refines_joinPart_left P Q j
    exact ⟨k, hj.trans hk⟩

end Join

/-! ## 4. Atoms for an arbitrary σ-algebra, itinerary, orbit σ-algebra -/

/-- The atom of `x` for a σ-algebra `m` on an arbitrary measurable space
(generalises `Work.EKLContract.atom`, which is specialised to `X₃`). -/
def atomGen {X : Type*} [MeasurableSpace X] (m : MeasurableSpace X) (x : X) : Set X :=
  ⋂₀ {s : Set X | MeasurableSet[m] s ∧ x ∈ s}

theorem mem_atomGen {X : Type*} [MeasurableSpace X] (m : MeasurableSpace X) (x : X) :
    x ∈ atomGen m x :=
  Set.mem_sInter.mpr fun _ hs => hs.2

/-- `atomGen` is antitone in the σ-algebra. -/
theorem atomGen_anti {X : Type*} [MeasurableSpace X] {m m' : MeasurableSpace X} (h : m' ≤ m)
    (x : X) : atomGen m x ⊆ atomGen m' x := by
  intro y hy
  refine Set.mem_sInter.mpr ?_
  rintro s hs
  exact Set.mem_sInter.mp hy _ ⟨h s hs.1, hs.2⟩

/-- Atoms of a comap σ-algebra are preimages of atoms. -/
theorem atomGen_comap {X : Type*} [MeasurableSpace X] (f : X → X) (m : MeasurableSpace X)
    (x : X) : atomGen (MeasurableSpace.comap f m) x = f ⁻¹' atomGen m (f x) := by
  ext y
  constructor
  · intro hy
    refine Set.mem_sInter.mpr ?_
    rintro s hs
    have hmem : MeasurableSet[MeasurableSpace.comap f m] (f ⁻¹' s) :=
      (MeasurableSpace.measurableSet_comap).mpr ⟨s, hs.1, rfl⟩
    exact Set.mem_sInter.mp hy (f ⁻¹' s) ⟨hmem, hs.2⟩
  · intro hy
    refine Set.mem_sInter.mpr ?_
    rintro s hs
    obtain ⟨u, hu, rfl⟩ := (MeasurableSpace.measurableSet_comap).mp hs.1
    exact Set.mem_sInter.mp hy u ⟨hu, hs.2⟩

variable {t : Fin 3 → ℝ} {P : FinPart X3}

/-- Two points have the same itinerary for the partition `P` and the flow `aDiag t` when at every
integer time they lie in the same part of `P`. -/
def SameItin (t : Fin 3 → ℝ) (P : FinPart X3) (x y : X3) : Prop :=
  ∀ n : ℤ, ∃ i : Fin P.n, aZ t n • x ∈ P.parts i ∧ aZ t n • y ∈ P.parts i

/-- The σ-algebra generated by the `aDiag t`-orbit of `P`. -/
def orbitSigma (t : Fin 3 → ℝ) (P : FinPart X3) : MeasurableSpace X3 :=
  ⨆ n : ℤ, MeasurableSpace.comap (fun x : X3 => aZ t n • x) (partSigma P)

/-- Between any two points of an atom of `orbitSigma` and any `n : ℤ`, the points `aⁿx`, `aⁿy`
lie in the same atom of `P`; in particular they realise the same itinerary when `P` is "small". -/
theorem mem_same_part_of_mem_orbitAtom {x y : X3}
    (h : y ∈ Work.EKLContract.atom (orbitSigma t P) x) (n : ℤ) :
    ∃ i : Fin P.n, aZ t n • x ∈ P.parts i ∧ aZ t n • y ∈ P.parts i := by
  have hle : MeasurableSpace.comap (fun x : X3 => aZ t n • x) (partSigma P) ≤ orbitSigma t P :=
    le_iSup (fun n : ℤ => MeasurableSpace.comap (fun x : X3 => aZ t n • x) (partSigma P)) n
  have hy : y ∈ atomGen (MeasurableSpace.comap (fun x : X3 => aZ t n • x) (partSigma P)) x :=
    atomGen_anti hle x h
  obtain ⟨i, hi⟩ : ∃ i : Fin P.n, aZ t n • x ∈ P.parts i := by
    have hcover : aZ t n • x ∈ ⋃ i, P.parts i := by rw [P.cover]; exact trivial
    exact Set.mem_iUnion.mp hcover
  refine ⟨i, hi, ?_⟩
  have hPf : MeasurableSet[partSigma P] (P.parts i) :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)
  have hmem : MeasurableSet[MeasurableSpace.comap (fun x : X3 => aZ t n • x) (partSigma P)]
      ((fun x : X3 => aZ t n • x) ⁻¹' (P.parts i)) :=
    (MeasurableSpace.measurableSet_comap).mpr ⟨P.parts i, hPf, rfl⟩
  exact Set.mem_sInter.mp hy _ ⟨hmem, hi⟩

/-- Membership in an atom of `orbitSigma` forces equal itineraries. -/
theorem sameItin_of_mem_orbitAtom {x y : X3} (h : y ∈ Work.EKLContract.atom (orbitSigma t P) x) :
    SameItin t P x y :=
  fun n => mem_same_part_of_mem_orbitAtom h n

/-- `AtomSmall K δ P`: any two points of `K` in the same atom of `P` differ by an element of
`V δ`. -/
def AtomSmall (K : Set X3) (δ : ℝ) (P : FinPart X3) : Prop :=
  ∀ i (x : X3), x ∈ K → x ∈ P.parts i → ∀ y ∈ K, y ∈ P.parts i → y ∈ ball δ x

/-! ## 5. Topological instances for `X₃` -/

/-- `Γ₃` is closed in `SL₃(ℝ)` (it is discrete, being a lattice); needed for `T2Space X₃`. -/
instance instIsClosedΓ3 : IsClosed (Γ3 : Set SL3) := Lemmas.isClosed_Γ3

theorem x3_locallyCompact : LocallyCompactSpace X3 := inferInstance

theorem x3_t2 : T2Space X3 := inferInstance

theorem x3_regular : RegularSpace X3 := inferInstance

theorem x3_secondCountable : SecondCountableTopology X3 := inferInstance

theorem x3_sigmaCompact : SigmaCompactSpace X3 := inferInstance

/-- The topological facts about `X₃` used by the proof of `P_USC`. -/
theorem X3Top : LocallyCompactSpace SL3 ∧ LocallyCompactSpace X3 ∧ T2Space X3 ∧ RegularSpace X3 ∧
    SecondCountableTopology X3 :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-! ## 6. The separation lemma (EKL §9, Lemma 8.5/Prop 9.2 core) -/

/-- A constant dominating all differences `|t i - t j|`. -/
def tsum (t : Fin 3 → ℝ) : ℝ := (∑ p : Fin 3 × Fin 3, |t p.1 - t p.2|) + 1

theorem le_tsum (t : Fin 3 → ℝ) (i j : Fin 3) : |t i - t j| ≤ tsum t := by
  have h := Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
  simp only [tsum]
  linarith

theorem tsum_nonneg (t : Fin 3 → ℝ) : 0 ≤ tsum t := by
  have h : (0:ℝ) ≤ ∑ p : Fin 3 × Fin 3, |t p.1 - t p.2| := Finset.sum_nonneg fun p _ => abs_nonneg _
  simp only [tsum]; linarith

theorem exp_neg_tsum_le_one (t : Fin 3 → ℝ) : Real.exp (-(tsum t)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  linarith [tsum_nonneg t]

/-- If `t p < t q` then `p ≠ q`. -/
theorem ne_left_of_lt {t : Fin 3 → ℝ} {p q : Fin 3} (h : t p < t q) : p ≠ q := by
  intro hpq; rw [hpq] at h; exact lt_irrefl _ h

/-- If `t p > t q` then `p ≠ q`. -/
theorem ne_left_of_gt {t : Fin 3 → ℝ} {p q : Fin 3} (h : t p > t q) : p ≠ q := by
  intro hpq; rw [hpq] at h; exact lt_irrefl _ h

/-- Entering `V δ` means the entrywise bound. -/
theorem abs_offdiag_lt_of_mem_V {δ : ℝ} {g : SL3} (hg : g ∈ V δ) {i j : Fin 3} (hij : i ≠ j) :
    |toMat g i j| < δ := by
  have h := hg i j
  rw [Matrix.one_apply, if_neg hij, sub_zero] at h
  exact h

/-- The forward entrywise step of the conjugation: `entry (n+1) = e^{t_i - t_j} * entry n`. -/
theorem conjZ_step_apply (t : Fin 3 → ℝ) (n : ℤ) (g : SL3) (i j : Fin 3) :
    toMat (conjZ t (n + 1) g) i j
      = Real.exp (t i - t j) * toMat (conjZ t n g) i j := by
  have h1 : conjZ t (n + 1) g = conjZ t 1 (conjZ t n g) := by
    rw [← conjZ_add]
    congr 1
    ring
  rw [h1, conjZ_apply, conjZ_apply]
  have h2 : (((1 : ℤ)) : ℝ) = 1 := by norm_num
  rw [h2, one_mul]

/-- **Expanding case of the separation lemma.** -/
theorem conj_small_away_expanding {t : Fin 3 → ℝ} {g : SL3} (hg : g ∈ V (1/2))
    {i j : Fin 3} (hgt : t i > t j) (hne : toMat g i j ≠ 0) :
    ∃ n : ℤ, conjZ t n g ∈ V (1/2) ∧ conjZ t n g ∉ V (Real.exp (-(tsum t)) / 2) := by
  set Bad : ℕ → Prop := fun n => ∃ p q : Fin 3, t p > t q ∧
    (1/2 : ℝ) ≤ |toMat (conjZ t ((n : ℕ) : ℤ) g) p q| with hBaddef
  have hBadne : ∃ n, Bad n := by
    have hpos : 0 < t i - t j := sub_pos.mpr hgt
    have hne' : 0 < |toMat g i j| := abs_pos.mpr hne
    have h1 : Tendsto (fun n : ℕ => (t i - t j) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hpos
    have htend : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j))) atTop atTop :=
      Real.tendsto_exp_atTop.comp (h1.congr' (Eventually.of_forall fun n => by ring))
    obtain ⟨N, hN⟩ := (htend.eventually_ge_atTop ((1/2 : ℝ) / |toMat g i j|)).exists
    refine ⟨N, i, j, hgt, ?_⟩
    rw [conjZ_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc (1/2 : ℝ) = ((1/2 : ℝ) / |toMat g i j|) * |toMat g i j| := by field_simp
      _ ≤ Real.exp ((N : ℝ) * (t i - t j)) * |toMat g i j| :=
          mul_le_mul_of_nonneg_right hN (abs_nonneg _)
  have hBad0 : ¬ Bad 0 := by
    rintro ⟨p, q, hpq, hle⟩
    have hlt1 : |toMat g p q| < 1/2 :=
      abs_offdiag_lt_of_mem_V hg (ne_left_of_gt hpq)
    rw [Nat.cast_zero, conjZ_zero] at hle
    exact absurd hle (not_le.mpr hlt1)
  set k : ℕ := Nat.find hBadne with hkdef
  have hkspec : Bad k := Nat.find_spec hBadne
  have hkpos : 0 < k := by
    refine Nat.pos_of_ne_zero fun h => hBad0 ?_
    rw [← h]
    exact hkspec
  have hkmin : ¬ Bad (k - 1) := Nat.find_min hBadne (by omega)
  have hcast : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  refine ⟨(k : ℤ) - 1, ?_, ?_⟩
  · intro p q
    rw [hcast]
    change |toMat (conjZ t ((k - 1 : ℕ) : ℤ) g) p q
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < 1/2
    by_cases hpq : t p = t q
    · rw [conjZ_apply, hpq, sub_self, mul_zero, Real.exp_zero, one_mul]
      exact hg p q
    · rcases lt_or_gt_of_ne hpq with hlt | hlt
      · -- contracting position at a positive time
        have hne' : p ≠ q := ne_left_of_lt hlt
        have hb : Real.exp (((k - 1 : ℕ) : ℝ) * (t p - t q)) * |toMat g p q| ≤ |toMat g p q| := by
          have h1 : Real.exp (((k - 1 : ℕ) : ℝ) * (t p - t q)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr hlt.le)
          calc Real.exp (((k - 1 : ℕ) : ℝ) * (t p - t q)) * |toMat g p q|
              ≤ 1 * |toMat g p q| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = |toMat g p q| := one_mul _
        rw [conjZ_apply, Matrix.one_apply_ne hne', sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact lt_of_le_of_lt hb (abs_offdiag_lt_of_mem_V hg (ne_left_of_lt hlt))
      · -- expanding position: minimality of `k`
        have hne' : p ≠ q := ne_left_of_gt hlt
        have hlt1 : |toMat (conjZ t ((k - 1 : ℕ) : ℤ) g) p q| < 1/2 := by
          by_contra hc
          exact hkmin ⟨p, q, hlt, not_lt.mp hc⟩
        rw [conjZ_apply, Matrix.one_apply_ne hne', sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
        rwa [conjZ_apply, abs_mul, abs_of_pos (Real.exp_pos _)] at hlt1
  · intro hmem
    obtain ⟨p, q, hpq, hle⟩ := hkspec
    have hpne : p ≠ q := ne_left_of_gt hpq
    have hfwd := conjZ_step_apply t ((k : ℤ) - 1) g p q
    have harg : ((k : ℤ) - 1) + 1 = (k : ℤ) := by ring
    rw [harg] at hfwd
    have hbnd : Real.exp (-(tsum t)) / 2 ≤ |toMat (conjZ t ((k : ℤ) - 1) g) p q| := by
      have hd : Real.exp (-(tsum t)) ≤ Real.exp (-(t p - t q)) := by
        apply Real.exp_le_exp.mpr
        have h := le_tsum t p q
        rw [abs_le] at h
        linarith [h.2]
      have h1 : Real.exp (-(t p - t q)) * (1/2)
          ≤ Real.exp (-(t p - t q)) * (Real.exp (t p - t q)
            * |toMat (conjZ t ((k : ℤ) - 1) g) p q|) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [hfwd, abs_mul, abs_of_pos (Real.exp_pos _)] at hle
        exact hle
      have h2 : Real.exp (-(t p - t q)) * (Real.exp (t p - t q)
            * |toMat (conjZ t ((k : ℤ) - 1) g) p q|)
          = |toMat (conjZ t ((k : ℤ) - 1) g) p q| := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      calc Real.exp (-(tsum t)) / 2 = Real.exp (-(tsum t)) * (1/2) := by ring
        _ ≤ Real.exp (-(t p - t q)) * (1/2) := mul_le_mul_of_nonneg_right hd (by norm_num)
        _ ≤ |toMat (conjZ t ((k : ℤ) - 1) g) p q| := by rw [← h2]; exact h1
    have hh := hmem p q
    rw [Matrix.one_apply, if_neg hpne, sub_zero] at hh
    linarith

/-- **Contracting case of the separation lemma.** -/
theorem conj_small_away_contracting {t : Fin 3 → ℝ} {g : SL3} (hg : g ∈ V (1/2))
    {i j : Fin 3} (hlt : t i < t j) (hne : toMat g i j ≠ 0) :
    ∃ n : ℤ, conjZ t n g ∈ V (1/2) ∧ conjZ t n g ∉ V (Real.exp (-(tsum t)) / 2) := by
  set Bad : ℕ → Prop := fun n => ∃ p q : Fin 3, t p < t q ∧
    (1/2 : ℝ) ≤ |toMat (conjZ t (-(n : ℤ)) g) p q| with hBaddef
  have hBadne : ∃ n, Bad n := by
    have hpos : 0 < t j - t i := sub_pos.mpr hlt
    have hne' : 0 < |toMat g i j| := abs_pos.mpr hne
    have h1 : Tendsto (fun n : ℕ => (t j - t i) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hpos
    have htend : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t j - t i))) atTop atTop :=
      Real.tendsto_exp_atTop.comp (h1.congr' (Eventually.of_forall fun n => by ring))
    obtain ⟨N, hN⟩ := (htend.eventually_ge_atTop ((1/2 : ℝ) / |toMat g i j|)).exists
    refine ⟨N, i, j, hlt, ?_⟩
    rw [conjZ_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hcast : ((-(N : ℤ) : ℤ) : ℝ) = -(N : ℝ) := by push_cast; ring
    rw [hcast]
    have heqexp : Real.exp (-(N : ℝ) * (t i - t j)) = Real.exp ((N : ℝ) * (t j - t i)) := by
      congr 1; ring
    rw [heqexp]
    calc (1/2 : ℝ) = ((1/2 : ℝ) / |toMat g i j|) * |toMat g i j| := by field_simp
      _ ≤ Real.exp ((N : ℝ) * (t j - t i)) * |toMat g i j| :=
          mul_le_mul_of_nonneg_right hN (abs_nonneg _)
  have hBad0 : ¬ Bad 0 := by
    rintro ⟨p, q, hpq, hle⟩
    have hlt1 : |toMat g p q| < 1/2 := abs_offdiag_lt_of_mem_V hg (ne_left_of_lt hpq)
    rw [Nat.cast_zero, neg_zero, conjZ_zero] at hle
    exact absurd hle (not_le.mpr hlt1)
  set k : ℕ := Nat.find hBadne with hkdef
  have hkspec : Bad k := Nat.find_spec hBadne
  have hkpos : 0 < k := by
    refine Nat.pos_of_ne_zero fun h => hBad0 ?_
    rw [← h]
    exact hkspec
  have hkmin : ¬ Bad (k - 1) := Nat.find_min hBadne (by omega)
  refine ⟨-(((k - 1 : ℕ) : ℤ)), ?_, ?_⟩
  · intro p q
    change |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < 1/2
    rcases lt_trichotomy (t p) (t q) with hpq | heq | hpq
    · -- contracting direction: minimality
      have hlt1 : |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q| < 1/2 := by
        by_contra hc
        exact hkmin ⟨p, q, hpq, not_lt.mp hc⟩
      have hgoal : |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < 1/2 := by
        rw [Matrix.one_apply, if_neg (ne_left_of_lt hpq), sub_zero]
        exact hlt1
      exact hgoal
    · -- central direction
      rw [conjZ_apply, heq, sub_self, mul_zero, Real.exp_zero, one_mul]
      exact hg p q
    · -- expanding direction at negative time: entries shrink
      have hlt1 : |toMat g p q| < 1/2 := abs_offdiag_lt_of_mem_V hg (ne_left_of_gt hpq)
      have hle1 : Real.exp (-((k - 1 : ℕ) : ℝ) * (t p - t q)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
          (sub_nonneg.mpr hpq.le)
      rw [conjZ_apply, Matrix.one_apply, if_neg (ne_left_of_gt hpq), sub_zero,
        abs_mul, abs_of_pos (Real.exp_pos _)]
      push_cast
      calc Real.exp (-((k - 1 : ℕ) : ℝ) * (t p - t q)) * |toMat g p q|
          ≤ 1 * |toMat g p q| := mul_le_mul_of_nonneg_right hle1 (abs_nonneg _)
        _ = |toMat g p q| := one_mul _
        _ < 1/2 := hlt1
  · intro hmem
    obtain ⟨p, q, hpq, hle⟩ := hkspec
    have hpne : p ≠ q := ne_left_of_lt hpq
    have hfwd := conjZ_step_apply t (-((k : ℤ))) g p q
    have h3 : (((k - 1 : ℕ)) : ℤ) = ((k : ℕ) : ℤ) - 1 := Nat.cast_sub hkpos
    have harg : (-((k : ℤ))) + 1 = -(((k - 1 : ℕ) : ℤ)) := by
      rw [h3]; ring
    rw [harg] at hfwd
    have hbnd : Real.exp (-(tsum t)) / 2
        ≤ |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q| := by
      have hd : Real.exp (-(tsum t)) ≤ Real.exp (t p - t q) := by
        apply Real.exp_le_exp.mpr
        have h := le_tsum t p q
        rw [abs_le] at h
        linarith [h.1]
      have h1 : Real.exp (t p - t q) * (1/2)
          ≤ Real.exp (t p - t q) * |toMat (conjZ t (-((k : ℤ))) g) p q| :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      have h2 : |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q|
          = Real.exp (t p - t q) * |toMat (conjZ t (-((k : ℤ))) g) p q| := by
        rw [hfwd, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(tsum t)) / 2 = Real.exp (-(tsum t)) * (1/2) := by ring
        _ ≤ Real.exp (t p - t q) * (1/2) := mul_le_mul_of_nonneg_right hd (by norm_num)
        _ ≤ |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q| := by rw [h2]; exact h1
    have hh := hmem p q
    rw [Matrix.one_apply, if_neg hpne, sub_zero] at hh
    linarith

/-- **Separation lemma.** -/
theorem exists_conj_small_away (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) :
    ∃ r : ℝ, 0 < r ∧ ∃ β : ℝ, 0 < β ∧ β ≤ r ∧ ∀ g : SL3, g ∈ V r → g ∉ Csub t →
      ∃ n : ℤ, conjZ t n g ∈ V r ∧ conjZ t n g ∉ V β := by
  refine ⟨1/2, by norm_num, Real.exp (-(tsum t)) / 2, by positivity, ?_, ?_⟩
  · linarith [exp_neg_tsum_le_one t]
  · intro g hg hgn
    have hgn' : ¬ (∀ i j : Fin 3, t i ≠ t j → toMat g i j = 0) :=
      fun h => hgn ((mem_Csub_iff t g).mpr h)
    push Not at hgn'
    obtain ⟨i, j, hij, hne⟩ := hgn'
    rcases lt_trichotomy (t i) (t j) with hlt | heq | hgt
    · exact conj_small_away_contracting hg hlt hne
    · exact absurd heq hij
    · exact conj_small_away_expanding hg hgt hne

/-! ## 7. The core claim of EKL Prop 9.2 -/

/-- The separation lemma with explicit constants. -/
theorem exists_conj_small_away_expl (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) {g : SL3}
    (hg : g ∈ V (1/2)) (hgn : g ∉ Csub t) :
    ∃ n : ℤ, conjZ t n g ∈ V (1/2) ∧ conjZ t n g ∉ V (Real.exp (-(tsum t)) / 2) := by
  have hgn' : ¬ (∀ i j : Fin 3, t i ≠ t j → toMat g i j = 0) :=
    fun h => hgn ((mem_Csub_iff t g).mpr h)
  push Not at hgn'
  obtain ⟨i, j, hij, hne⟩ := hgn'
  rcases lt_trichotomy (t i) (t j) with hlt | heq | hgt
  · exact conj_small_away_contracting hg hlt hne
  · exact absurd heq hij
  · exact conj_small_away_expanding hg hgt hne

theorem inv_aDiag (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) :=
  inv_eq_of_mul_eq_one_right (aDiag_mul_neg t)

theorem aZ_comm (t : Fin 3 → ℝ) (m n : ℤ) : aZ t m * aZ t n = aZ t n * aZ t m := by
  rw [← aZ_add, ← aZ_add, add_comm]

/-- `K` is invariant under all integer powers of `aDiag t`. -/
theorem aZ_smul_mem {t : Fin 3 → ℝ} {K : Set X3}
    (hfwd : ∀ x ∈ K, aDiag t • x ∈ K) (hbwd : ∀ x ∈ K, aDiag (-t) • x ∈ K) :
    ∀ (n : ℤ) (z : X3), z ∈ K → aZ t n • z ∈ K := by
  intro n z hz
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
  · subst hm
    induction m with
    | zero => simpa [aZ_zero] using hz
    | succ j ih =>
        have h1 : aZ t (((j + 1 : ℕ)) : ℤ) = aZ t ((j : ℕ) : ℤ) * aDiag t := by
          rw [show (((j + 1 : ℕ)) : ℤ) = ((j : ℕ) : ℤ) + 1 from by push_cast; ring, aZ_add,
            aZ_one]
        have hcomm : aZ t ((j : ℕ) : ℤ) * aDiag t = aDiag t * aZ t ((j : ℕ) : ℤ) := by
          rw [← aZ_one]
          exact (aZ_comm t 1 ((j : ℕ) : ℤ)).symm
        rw [h1, hcomm, mul_smul]
        exact hfwd _ ih
  · subst hm
    have hgen : ∀ m : ℕ, (aDiag (-t)) ^ m • z ∈ K := by
      intro m
      induction m with
      | zero => simpa using hz
      | succ j ih =>
          rw [pow_succ', mul_smul]
          exact hbwd _ ih
    have h2 : aZ t (-(m : ℤ)) = ((aDiag (-t)) ^ m) := by
      rw [aZ_eq_inv, aZ_nat, ← inv_pow, inv_aDiag]
    rw [h2]
    exact hgen m

/-- **EKL Prop 9.2, core claim.**  If `x, y ∈ K` lie in the same atom of the orbit σ-algebra of a
partition whose atoms are `V δ`-small on `K`, then `y = c • x` for some `c` in the centraliser of
`aDiag t`. -/
theorem sameItin_central {t : Fin 3 → ℝ} {K : Set X3} {P : FinPart X3} {δ η : ℝ}
    (hfwd : ∀ x ∈ K, aDiag t • x ∈ K) (hbwd : ∀ x ∈ K, aDiag (-t) • x ∈ K)
    (hinj : ∀ x ∈ K, ∀ g h : SL3, g ∈ V η → h ∈ V η → g • x = h • x → g = h)
    (hδ1 : δ ≤ 1/2) (hδβ : δ ≤ Real.exp (-(tsum t)) / 2) (hδη : δ ≤ η)
    (hη : (1/2 : ℝ) ≤ η) (hsmall : AtomSmall K δ P)
    {x y : X3} (hx : x ∈ K) (hy : y ∈ K)
    (hitin : y ∈ Work.EKLContract.atom (orbitSigma t P) x) :
    ∃ c ∈ Csub t, y = c • x := by
  have hsame : ∀ n : ℤ, ∃ i : Fin P.n,
      aZ t n • x ∈ P.parts i ∧ aZ t n • y ∈ P.parts i :=
    fun n => mem_same_part_of_mem_orbitAtom hitin n
  have hKinv := aZ_smul_mem hfwd hbwd
  obtain ⟨i, hxi, hyi⟩ := hsame 0
  simp only [aZ_zero, one_smul] at hxi hyi
  obtain ⟨g, hgV, hgxy⟩ := hsmall i x hx hxi y hy hyi
  by_cases hgc : g ∈ Csub t
  · exact ⟨g, hgc, hgxy.symm⟩
  · exfalso
    by_cases ht : ∃ i j : Fin 3, t i ≠ t j
    · obtain ⟨n, hnV, hnβ⟩ := exists_conj_small_away_expl t ht (V_mono hδ1 hgV) hgc
      obtain ⟨j, hxj, hyj⟩ := hsame n
      have hnx : aZ t n • x ∈ K := hKinv n x hx
      have hny : aZ t n • y ∈ K := hKinv n y hy
      obtain ⟨k, hkV, hkxy⟩ := hsmall j (aZ t n • x) hnx hxj (aZ t n • y) hny hyj
      have hgrp : (aZ t n * g * (aZ t n)⁻¹) * aZ t n = aZ t n * g := by group
      have hgxy' : g • x = y := hgxy
      have hrel : (conjZ t n g) • (aZ t n • x) = k • (aZ t n • x) := by
        rw [conjZ, ← mul_smul, hgrp, mul_smul, hgxy']
        exact hkxy.symm
      have hkg : k = conjZ t n g :=
        (hinj (aZ t n • x) hnx (conjZ t n g) k (V_mono hη hnV) (V_mono hδη hkV) hrel).symm
      have hmemβ : conjZ t n g ∈ V (Real.exp (-(tsum t)) / 2) := by
        rw [← hkg]
        exact V_mono hδβ hkV
      exact hnβ hmemβ
    · -- `t` is constant: the centraliser is everything, contradicting `g ∉ Csub t`
      have htconst : ∀ i j : Fin 3, t i = t j := fun i j => by
        by_contra hcon
        exact ht ⟨i, j, hcon⟩
      exact hgc ((mem_Csub_iff t g).mpr fun p q hpq => absurd (htconst p q) hpq)


/-! ## ROADMAP — what is proved here and what remains

### Proved in this file (sorry-free)
* `Csub`, `aZ`, `conjZ`, `tsum`, `ball`, `joinPart__USCBasic`, `atomGen`, `SameItin`, `orbitSigma`,
  `AtomSmall` and their API (Sections 1–5).
* `X3Top` and the instances `LocallyCompactSpace X3`, `T2Space X3`, `RegularSpace X3`,
  `SecondCountableTopology X3`, `SigmaCompactSpace X3` (Section 5; `SL3`'s instances come from
  `Submission.Work.EKLRelCross.Instances`).
* `exists_conj_small_away` (Section 6): **separation lemma**.  If `g ∈ V (1/2)` is not in the
  centraliser of `aDiag t`, then some conjugate `aⁿ g a⁻ⁿ` is still in `V (1/2)` but not in
  `V (exp (-(tsum t)) / 2)`.  Entrywise conjugation is exact, so the proof is a threshold
  argument on the expanding (resp. contracting) entries.
* `sameItin_central` (Section 7): **the core claim of EKL Prop 9.2**.  If `x, y ∈ K` lie in the
  same atom of the orbit σ-algebra of a partition whose atoms are `V δ`-small on `K`, then
  `y = c • x` with `c` in the centraliser of `aDiag t`.  Otherwise the separation lemma produces
  a time at which the two points are not within `V δ`, contradicting the atom-smallness (using
  injectivity of the orbit map on `K`, `Work.EKLComp.uniform_inj_of_isCompact`).

### Pieces available elsewhere in the workspace (import, do not reprove)
* **Portmanteau**: `PseudoMetrizableSpace X3` and `HasOuterApproxClosed X3` are *inferable*
  from this file's imports (reviewers verified by elaboration), so the two portmanteau helpers
  `Work.EKLComp.limsup_measure_closed_le` (the (C)-condition for closed sets) and
  `Work.EKLComp.tendsto_measure_of_null_frontier_of_integral` (continuity sets) are short
  wrappers around `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` and
  `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` plus
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.  In particular part (ii) of `P_USC`
  needs no metric-free monotone-convergence trick: Mathlib's portmanteau applies directly.
* `Work.EKLComp.Core`, `Work.EKLComp.Entropy` (`Hfam` API, `hPart_eq_lim`, `joinSets` API,
  `Hfam_le_log_card`, subadditivity/Fekete).
* `Work.EKLC6Core.Hcond_mono` (`Hcond_mono_aux`, `Hcond_eq_sum_integral`).
* `Work.EKLComp.uniform_inj_of_isCompact`, `Work.EKLComp.inv_mem_V`,
  `Work.EKLComp.exists_bump`, `Work.EKLComp.exists_level_null`, `Work.EKLComp.Crat_dense`.
* `Work.EKLComp.hPart_Hcond` (E5), `Work.EKLComp.ent_generating` (E4): the two clauses of the
  frozen `P_EntropyBasics` that this component consumes (proved by the C3 fleet).
* `Work.EKLComp.Hcond_joinPart` (PROVED: chain rule for `Hcond` w.r.t. `joinPart__USCBasic`),
  `Work.EKLComp.Hcond_eq_zero_of_atom_subset` (PROVED: the atom criterion for `Hcond = 0`,
  **with the countable-generation hypothesis on the σ-algebra** — without it the statement is
  false, see the reviews),
  `Work.EKLComp.exists_small_part` (PROVED: `AtomSmall` + `μ`-null frontiers — this supplies the
  `Pstar` used in Steps 1–4 below),
  `Work.EKLComp.exists_part_seq` (refining generating sequence with `μ`-null frontiers;
  note: requiring the atoms to be *open* is impossible on the connected `X3`, so only the
  `μ`-null-frontier form is asked for).

### What remains, and the exact shape of the argument
1. **Vanishing of the relative entropy** (`Hcond_orbit_eq_zero`).  For `μ` a probability that is
   preserved by `x ↦ aDiag t • x`, `Q` a partition whose atoms are a.e. equal to open sets and
   `Pstar` an `AtomSmall K δ Pstar` partition, one must show
   `Hcond μ Q (orbitSigma t Pstar ⊔ ⋁_{n≥1} a^{-n}·partSigma Q) = 0`.
   *NOTE*: the σ-algebra must **not** contain `partSigma Q` itself (otherwise the statement is
   trivial, and — importantly — it is *not* the σ-algebra that the entropy chain rule uses).
   The proof is EKL's: for `y` in the same atom of that σ-algebra as `x`, `sameItin_central`
   gives `y = c • x` with `c ∈ Csub t`; a rational `g_C ≈ c` (from `Crat_dense`) and Poincaré
   recurrence for the sets `{x | ball (1/ℓ) x ⊆ Q_i ∩ g_C⁻¹ Q_j}` then give `i = j`, i.e. the
   atoms refine the `Q`-parts; conclude with `Hcond_eq_zero_of_atom_subset` (which needs
   countable generation of the σ-algebra; `orbitSigma`/`negOrbitSigma` are countable sups of
   comaps of finitely generated σ-algebras, so this holds).

   *CAUTION (the subtle point of the formalisation)*: EKL replace the partition by a
   "partition modulo μ into open sets" before running the recurrence, and the openness is used
   twice: to see that a point of an atom has a whole `V (1/ℓ)`-ball inside it, and to see that
   `g_C x ∈ Q_j` gives a neighbourhood of `g_C x` inside `Q_j`.  A `FinPart` must cover `X₃`
   exactly, and on the connected space `X₃` the open atoms can cover only a conull set, so the
   statement is safest when formulated for a family of open `U i` with
   `Q.parts i =ᵐ[μ] U i` **and** `Q.parts i ⊆ U i` (`i.e.` `μ (U i \ Q.parts i) = 0`), which is
   what a partition with `μ`-null frontiers produced from continuous "boxes" satisfies
   (`exists_small_part`).  With that data the recurrence must be run with the open `U`-sets and
   the σ-algebra above must be generated from the `Q`-parts (the two agree modulo `μ` on the
   relevant sets); carrying this out is the remaining formalisation work of Step 1 along with
   measurability of `{x | ∀ h ∈ V (1/ℓ), h • x ∈ A}` (use a countable dense `D ⊆ V (1/ℓ)` and
   `A` open: then `D • x ⊆ A` implies the `V (1/ℓ)`-ball condition when `A` is open *and*
   `x`'s relevant points are interior).
2. **EKL Prop 9.2** (`hPart_eq_hPart_of_atomSmall`).  With `𝒜 := orbitSigma t Pstar`:
   for every partition `Q`, `hPart μ a Q ≤ hPart μ a Pstar`.  Via `hPart_Hcond` (E5),
   `Hcond_joinPart`, `Hcond_mono_aux` (antitonicity) and Step 1:
   `hPart μ a (Pstar∨Q) = Hcond μ (Pstar∨Q) (⋁_{n≥1}a^{-n}partSigma(Pstar∨Q))`
   `≤ Hcond μ Pstar (⋁_{n≥1}a^{-n}partSigma Pstar) + Hcond μ Q (…) = hPart μ a Pstar + 0`.
3. **Finiteness on `K`** (part (i) of `P_USC`).  Take `Pstar` from `exists_small_part` with `δ`
   below the thresholds of `sameItin_central`, reduce `K` to `K' := ⋂_n aⁿK` (compact,
   bi-invariant, `ν K' = 1` for every `a`-invariant `ν` with `ν K = 1`), apply Step 2 to get
   `ent ν a = ENNReal.ofReal (hPart ν a Pstar) ≤ ENNReal.ofReal (Real.log Pstar.n)`
   (`hPart ≤ Hfam ≤ log n`).
4. **Upper semicontinuity** (part (ii)).  Given `νseq → νlim` weakly (tested against bounded
   continuous functions): `νlim` is `a`-invariant (Riesz uniqueness,
   `Measure.ext_of_integral_eq_on_compactlySupported`) and `νlim K = 1`
   (`limsup_measure_closed_le`, from the weak convergence and `X3`'s regularity).
   Fix `ε > 0` and `N` with `(1/N)·H_{νlim}(⋁_{k<N}a^{-k}Pstar) < ent νlim a + ε`
   (`hPart_eq_lim`), choose `Pstar` additionally with `νlim`-null frontiers
   (`exists_small_part`), and use the continuity-set convergence
   (`MeasureTheory.tendsto_measure_of_null_frontier`, which follows from
   `limsup_measure_closed_le` and Mathlib's portmanteau lemma
   `MeasureTheory.le_measure_compl_liminf_of_limsup_measure_le`) plus continuity of
   `x ↦ ∑ -x log x` on the simplex.
5. `prove_USC` is then the conjunction of (3) and (4).
-/


/-- The σ-algebra generated by the *backward* images of `Q`, i.e. the "past" σ-algebra
`⋁_{n≥1} T^{-n}·partSigma Q` appearing in `H_μ(Q | ⋁_{n≥1} T^{-n}Q ∨ 𝒜)` (`T = aDiag t •`).
Concretely `negOrbitSigma t Q = ⨆_{n : ℕ} comap (T^{n+1}) (partSigma Q)`: the pullbacks of
`partSigma Q` along the *forward* iterates of `T` are exactly the σ-algebras generated by the
partitions `T^{-(n+1)}Q`. -/
def negOrbitSigma (t : Fin 3 → ℝ) (Q : FinPart X3) : MeasurableSpace X3 :=
  ⨆ n : ℕ, MeasurableSpace.comap (fun x : X3 => aZ t ((n : ℤ) + 1) • x) (partSigma Q)

theorem negOrbitSigma_le (t : Fin 3 → ℝ) (Q : FinPart X3) :
    negOrbitSigma t Q ≤ orbitSigma t Q := by
  refine iSup_le fun n => ?_
  have hle : MeasurableSpace.comap (fun x : X3 => aZ t ((n : ℤ) + 1) • x) (partSigma Q)
      ≤ ⨆ m : ℤ, MeasurableSpace.comap (fun x : X3 => aZ t m • x) (partSigma Q) :=
    le_iSup (fun m : ℤ => MeasurableSpace.comap (fun x : X3 => aZ t m • x) (partSigma Q))
      ((n : ℤ) + 1)
  exact hle

/-! ## 8. The separation lemma and the core claim at a general radius

The scale `1/2` used in Section 6 is replaced by a general `r ≤ 1/2`; this is what the proof of
`P_USC` expends, because the injectivity radius on a compact set is not known to be `≥ 1/2`.
-/

/-- **Expanding case of the separation lemma, at a general radius.** -/
theorem conj_small_away_expanding_gen {t : Fin 3 → ℝ} {g : SL3} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1/2)
    (hg : g ∈ V r)
    {i j : Fin 3} (hgt : t i > t j) (hne : toMat g i j ≠ 0) :
    ∃ n : ℤ, conjZ t n g ∈ V r ∧ conjZ t n g ∉ V (r * Real.exp (-(tsum t)) / 2) := by
  set Bad : ℕ → Prop := fun n => ∃ p q : Fin 3, t p > t q ∧
    r ≤ |toMat (conjZ t ((n : ℕ) : ℤ) g) p q| with hBaddef
  have hBadne : ∃ n, Bad n := by
    have hpos : 0 < t i - t j := sub_pos.mpr hgt
    have hne' : 0 < |toMat g i j| := abs_pos.mpr hne
    have h1 : Tendsto (fun n : ℕ => (t i - t j) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hpos
    have htend : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j))) atTop atTop :=
      Real.tendsto_exp_atTop.comp (h1.congr' (Eventually.of_forall fun n => by ring))
    obtain ⟨N, hN⟩ := (htend.eventually_ge_atTop (r / |toMat g i j|)).exists
    refine ⟨N, i, j, hgt, ?_⟩
    rw [conjZ_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc r = (r / |toMat g i j|) * |toMat g i j| := by field_simp
      _ ≤ Real.exp ((N : ℝ) * (t i - t j)) * |toMat g i j| :=
          mul_le_mul_of_nonneg_right hN (abs_nonneg _)
  have hBad0 : ¬ Bad 0 := by
    rintro ⟨p, q, hpq, hle⟩
    have hlt1 : |toMat g p q| < r :=
      abs_offdiag_lt_of_mem_V hg (ne_left_of_gt hpq)
    rw [Nat.cast_zero, conjZ_zero] at hle
    exact absurd hle (not_le.mpr hlt1)
  set k : ℕ := Nat.find hBadne with hkdef
  have hkspec : Bad k := Nat.find_spec hBadne
  have hkpos : 0 < k := by
    refine Nat.pos_of_ne_zero fun h => hBad0 ?_
    rw [← h]
    exact hkspec
  have hkmin : ¬ Bad (k - 1) := Nat.find_min hBadne (by omega)
  have hcast : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  refine ⟨(k : ℤ) - 1, ?_, ?_⟩
  · intro p q
    rw [hcast]
    change |toMat (conjZ t ((k - 1 : ℕ) : ℤ) g) p q
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < r
    by_cases hpq : t p = t q
    · rw [conjZ_apply, hpq, sub_self, mul_zero, Real.exp_zero, one_mul]
      exact hg p q
    · rcases lt_or_gt_of_ne hpq with hlt | hlt
      · -- contracting position at a positive time
        have hne' : p ≠ q := ne_left_of_lt hlt
        have hb : Real.exp (((k - 1 : ℕ) : ℝ) * (t p - t q)) * |toMat g p q| ≤ |toMat g p q| := by
          have h1 : Real.exp (((k - 1 : ℕ) : ℝ) * (t p - t q)) ≤ 1 := by
            rw [Real.exp_le_one_iff]
            exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr hlt.le)
          calc Real.exp (((k - 1 : ℕ) : ℝ) * (t p - t q)) * |toMat g p q|
              ≤ 1 * |toMat g p q| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ = |toMat g p q| := one_mul _
        rw [conjZ_apply, Matrix.one_apply_ne hne', sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact lt_of_le_of_lt hb (abs_offdiag_lt_of_mem_V hg (ne_left_of_lt hlt))
      · -- expanding position: minimality of `k`
        have hne' : p ≠ q := ne_left_of_gt hlt
        have hlt1 : |toMat (conjZ t ((k - 1 : ℕ) : ℤ) g) p q| < r := by
          by_contra hc
          exact hkmin ⟨p, q, hlt, not_lt.mp hc⟩
        rw [conjZ_apply, Matrix.one_apply_ne hne', sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
        rwa [conjZ_apply, abs_mul, abs_of_pos (Real.exp_pos _)] at hlt1
  · intro hmem
    obtain ⟨p, q, hpq, hle⟩ := hkspec
    have hpne : p ≠ q := ne_left_of_gt hpq
    have hfwd := conjZ_step_apply t ((k : ℤ) - 1) g p q
    have harg : ((k : ℤ) - 1) + 1 = (k : ℤ) := by ring
    rw [harg] at hfwd
    have hbnd : r * Real.exp (-(tsum t)) / 2 ≤ |toMat (conjZ t ((k : ℤ) - 1) g) p q| := by
      have hd : Real.exp (-(tsum t)) ≤ Real.exp (-(t p - t q)) := by
        apply Real.exp_le_exp.mpr
        have h := le_tsum t p q
        rw [abs_le] at h
        linarith [h.2]
      have h1 : Real.exp (-(t p - t q)) * r
          ≤ Real.exp (-(t p - t q)) * (Real.exp (t p - t q)
            * |toMat (conjZ t ((k : ℤ) - 1) g) p q|) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        rw [hfwd, abs_mul, abs_of_pos (Real.exp_pos _)] at hle
        exact hle
      have h2 : Real.exp (-(t p - t q)) * (Real.exp (t p - t q)
            * |toMat (conjZ t ((k : ℤ) - 1) g) p q|)
          = |toMat (conjZ t ((k : ℤ) - 1) g) p q| := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      have hstep : r * Real.exp (-(tsum t)) / 2 ≤ Real.exp (-(t p - t q)) * r := by
        have hA : r * Real.exp (-(tsum t)) / 2 ≤ r * Real.exp (-(tsum t)) := by
          nlinarith [Real.exp_pos (-(tsum t))]
        have hB : r * Real.exp (-(tsum t)) ≤ Real.exp (-(t p - t q)) * r := by
          rw [mul_comm r (Real.exp (-(tsum t)))]
          exact mul_le_mul_of_nonneg_right hd hr.le
        linarith
      calc r * Real.exp (-(tsum t)) / 2 ≤ Real.exp (-(t p - t q)) * r := hstep
        _ ≤ |toMat (conjZ t ((k : ℤ) - 1) g) p q| := by rw [← h2]; exact h1
    have hh := hmem p q
    rw [Matrix.one_apply, if_neg hpne, sub_zero] at hh
    linarith


/-- **Contracting case of the separation lemma, at a general radius.** -/
theorem conj_small_away_contracting_gen {t : Fin 3 → ℝ} {g : SL3} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1/2)
    (hg : g ∈ V r)
    {i j : Fin 3} (hlt : t i < t j) (hne : toMat g i j ≠ 0) :
    ∃ n : ℤ, conjZ t n g ∈ V r ∧ conjZ t n g ∉ V (r * Real.exp (-(tsum t)) / 2) := by
  set Bad : ℕ → Prop := fun n => ∃ p q : Fin 3, t p < t q ∧
    r ≤ |toMat (conjZ t (-(n : ℤ)) g) p q| with hBaddef
  have hBadne : ∃ n, Bad n := by
    have hpos : 0 < t j - t i := sub_pos.mpr hlt
    have hne' : 0 < |toMat g i j| := abs_pos.mpr hne
    have h1 : Tendsto (fun n : ℕ => (t j - t i) * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hpos
    have htend : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t j - t i))) atTop atTop :=
      Real.tendsto_exp_atTop.comp (h1.congr' (Eventually.of_forall fun n => by ring))
    obtain ⟨N, hN⟩ := (htend.eventually_ge_atTop (r / |toMat g i j|)).exists
    refine ⟨N, i, j, hlt, ?_⟩
    rw [conjZ_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hcast : ((-(N : ℤ) : ℤ) : ℝ) = -(N : ℝ) := by push_cast; ring
    rw [hcast]
    have heqexp : Real.exp (-(N : ℝ) * (t i - t j)) = Real.exp ((N : ℝ) * (t j - t i)) := by
      congr 1; ring
    rw [heqexp]
    calc r = (r / |toMat g i j|) * |toMat g i j| := by field_simp
      _ ≤ Real.exp ((N : ℝ) * (t j - t i)) * |toMat g i j| :=
          mul_le_mul_of_nonneg_right hN (abs_nonneg _)
  have hBad0 : ¬ Bad 0 := by
    rintro ⟨p, q, hpq, hle⟩
    have hlt1 : |toMat g p q| < r := abs_offdiag_lt_of_mem_V hg (ne_left_of_lt hpq)
    rw [Nat.cast_zero, neg_zero, conjZ_zero] at hle
    exact absurd hle (not_le.mpr hlt1)
  set k : ℕ := Nat.find hBadne with hkdef
  have hkspec : Bad k := Nat.find_spec hBadne
  have hkpos : 0 < k := by
    refine Nat.pos_of_ne_zero fun h => hBad0 ?_
    rw [← h]
    exact hkspec
  have hkmin : ¬ Bad (k - 1) := Nat.find_min hBadne (by omega)
  refine ⟨-(((k - 1 : ℕ) : ℤ)), ?_, ?_⟩
  · intro p q
    change |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < r
    rcases lt_trichotomy (t p) (t q) with hpq | heq | hpq
    · -- contracting direction: minimality
      have hlt1 : |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q| < r := by
        by_contra hc
        exact hkmin ⟨p, q, hpq, not_lt.mp hc⟩
      have hgoal : |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) p q| < r := by
        rw [Matrix.one_apply, if_neg (ne_left_of_lt hpq), sub_zero]
        exact hlt1
      exact hgoal
    · -- central direction
      rw [conjZ_apply, heq, sub_self, mul_zero, Real.exp_zero, one_mul]
      exact hg p q
    · -- expanding direction at negative time: entries shrink
      have hlt1 : |toMat g p q| < r := abs_offdiag_lt_of_mem_V hg (ne_left_of_gt hpq)
      have hle1 : Real.exp (-((k - 1 : ℕ) : ℝ) * (t p - t q)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
          (sub_nonneg.mpr hpq.le)
      rw [conjZ_apply, Matrix.one_apply, if_neg (ne_left_of_gt hpq), sub_zero,
        abs_mul, abs_of_pos (Real.exp_pos _)]
      push_cast
      calc Real.exp (-((k - 1 : ℕ) : ℝ) * (t p - t q)) * |toMat g p q|
          ≤ 1 * |toMat g p q| := mul_le_mul_of_nonneg_right hle1 (abs_nonneg _)
        _ = |toMat g p q| := one_mul _
        _ < r := hlt1
  · intro hmem
    obtain ⟨p, q, hpq, hle⟩ := hkspec
    have hpne : p ≠ q := ne_left_of_lt hpq
    have hfwd := conjZ_step_apply t (-((k : ℤ))) g p q
    have h3 : (((k - 1 : ℕ)) : ℤ) = ((k : ℕ) : ℤ) - 1 := Nat.cast_sub hkpos
    have harg : (-((k : ℤ))) + 1 = -(((k - 1 : ℕ) : ℤ)) := by
      rw [h3]; ring
    rw [harg] at hfwd
    have hbnd : r * Real.exp (-(tsum t)) / 2
        ≤ |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q| := by
      have hd : Real.exp (-(tsum t)) ≤ Real.exp (t p - t q) := by
        apply Real.exp_le_exp.mpr
        have h := le_tsum t p q
        rw [abs_le] at h
        linarith [h.1]
      have h1 : Real.exp (t p - t q) * r
          ≤ Real.exp (t p - t q) * |toMat (conjZ t (-((k : ℤ))) g) p q| :=
        mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      have h2 : |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q|
          = Real.exp (t p - t q) * |toMat (conjZ t (-((k : ℤ))) g) p q| := by
        rw [hfwd, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hstep : r * Real.exp (-(tsum t)) / 2 ≤ Real.exp (t p - t q) * r := by
        have hA : r * Real.exp (-(tsum t)) / 2 ≤ r * Real.exp (-(tsum t)) := by
          nlinarith [Real.exp_pos (-(tsum t))]
        have hB : r * Real.exp (-(tsum t)) ≤ Real.exp (t p - t q) * r := by
          rw [mul_comm r (Real.exp (-(tsum t)))]
          exact mul_le_mul_of_nonneg_right hd hr.le
        linarith
      calc r * Real.exp (-(tsum t)) / 2 ≤ Real.exp (t p - t q) * r := hstep
        _ ≤ |toMat (conjZ t (-(((k - 1 : ℕ) : ℤ))) g) p q| := by rw [h2]; exact h1
    have hh := hmem p q
    rw [Matrix.one_apply, if_neg hpne, sub_zero] at hh
    linarith


/-- **Separation lemma at a general radius.**  If `0 < r ≤ 1/2` and `g ∈ V r` is not in the
centraliser of `aDiag t`, then some conjugate of `g` lies in `V r` but not in
`V (r * exp (-(tsum t)) / 2)`. -/
theorem exists_conj_small_away_gen (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1/2) {g : SL3} (hg : g ∈ V r) (hgn : g ∉ Csub t) :
    ∃ n : ℤ, conjZ t n g ∈ V r ∧ conjZ t n g ∉ V (r * Real.exp (-(tsum t)) / 2) := by
  have hgn' : ¬ (∀ i j : Fin 3, t i ≠ t j → toMat g i j = 0) :=
    fun h => hgn ((mem_Csub_iff t g).mpr h)
  push Not at hgn'
  obtain ⟨i, j, hij, hne⟩ := hgn'
  rcases lt_trichotomy (t i) (t j) with hlt | heq | hgt
  · exact conj_small_away_contracting_gen hr hr1 hg hlt hne
  · exact absurd heq hij
  · exact conj_small_away_expanding_gen hr hr1 hg hgt hne

/-- **EKL Prop 9.2, core claim, at a general radius.**  If `x, y ∈ K` lie in the same atom of the
orbit σ-algebra of a partition whose atoms are `V δ`-small on `K` (with `δ ≤ r` and
`δ ≤ r * exp (-(tsum t)) / 2`, where `V r` is the injectivity radius on `K`), then `y = c • x` for
some `c` in the centraliser of `aDiag t`. -/
theorem sameItin_central_gen {t : Fin 3 → ℝ} {K : Set X3} {P : FinPart X3} {δ r : ℝ}
    (hfwd : ∀ x ∈ K, aDiag t • x ∈ K) (hbwd : ∀ x ∈ K, aDiag (-t) • x ∈ K)
    (hinj : ∀ x ∈ K, ∀ g h : SL3, g ∈ V r → h ∈ V r → g • x = h • x → g = h)
    (hr : 0 < r) (hr1 : r ≤ 1/2) (hδr : δ ≤ r) (hδexp : δ ≤ r * Real.exp (-(tsum t)) / 2)
    (hsmall : AtomSmall K δ P)
    {x y : X3} (hx : x ∈ K) (hy : y ∈ K)
    (hitin : y ∈ Work.EKLContract.atom (orbitSigma t P) x) :
    ∃ c ∈ Csub t, y = c • x := by
  have hsame : ∀ n : ℤ, ∃ i : Fin P.n,
      aZ t n • x ∈ P.parts i ∧ aZ t n • y ∈ P.parts i :=
    fun n => mem_same_part_of_mem_orbitAtom hitin n
  have hKinv := aZ_smul_mem hfwd hbwd
  obtain ⟨i, hxi, hyi⟩ := hsame 0
  simp only [aZ_zero, one_smul] at hxi hyi
  obtain ⟨g, hgV, hgxy⟩ := hsmall i x hx hxi y hy hyi
  by_cases hgc : g ∈ Csub t
  · exact ⟨g, hgc, hgxy.symm⟩
  · exfalso
    by_cases ht : ∃ i j : Fin 3, t i ≠ t j
    · obtain ⟨n, hnV, hnβ⟩ := exists_conj_small_away_gen t ht hr hr1 (V_mono hδr hgV) hgc
      obtain ⟨j, hxj, hyj⟩ := hsame n
      have hnx : aZ t n • x ∈ K := hKinv n x hx
      have hny : aZ t n • y ∈ K := hKinv n y hy
      obtain ⟨k, hkV, hkxy⟩ := hsmall j (aZ t n • x) hnx hxj (aZ t n • y) hny hyj
      have hgrp : (aZ t n * g * (aZ t n)⁻¹) * aZ t n = aZ t n * g := by group
      have hgxy' : g • x = y := hgxy
      have hrel : (conjZ t n g) • (aZ t n • x) = k • (aZ t n • x) := by
        rw [conjZ, ← mul_smul, hgrp, mul_smul, hgxy']
        exact hkxy.symm
      have hkg : k = conjZ t n g :=
        (hinj (aZ t n • x) hnx (conjZ t n g) k hnV (V_mono hδr hkV) hrel).symm
      have hmemβ : conjZ t n g ∈ V (r * Real.exp (-(tsum t)) / 2) := by
        rw [← hkg]
        exact V_mono hδexp hkV
      exact hnβ hmemβ
    · have htconst : ∀ i j : Fin 3, t i = t j := fun i j => by
        by_contra hcon
        exact ht ⟨i, j, hcon⟩
      exact hgc ((mem_Csub_iff t g).mpr fun p q hpq => absurd (htconst p q) hpq)


