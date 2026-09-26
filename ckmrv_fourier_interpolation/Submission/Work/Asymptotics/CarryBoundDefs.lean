/-
# Componentwise operations on carries and the bound predicate `CB`

A *carry* is a triple `(a, b, c) ∈ R × R × R` with `carryComb a b c = rowDiff x i`.  The
recursion producing carries from the atom data uses the componentwise operations

* `triAdd` (addition of carries, from `rowDiff` additivity),
* `triSmul` (`ℂ`-scalar multiplication),
* `triMulOf` (right multiplication by a group element, from the cocycle law),
* `triSum` (finite sums),

and the bound predicate `CB p Cb K`, which says that all three components of `p` have
`coeffNorm` at most `Cb` and support Frobenius norm at most `K`.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryBoundBasic
import Submission.Work.Asymptotics.CarryWord

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The element of `R` multiplying the two halves of `Rneg - 1` commuting. -/
lemma mul_Rneg_sub_one_comm' (r : R) :
    r * (Work.Residues.Rneg - 1) = (Work.Residues.Rneg - 1) * r := by
  rw [mul_sub, sub_mul, Work.Residues.Rneg_comm r, mul_one, one_mul]

/-- Componentwise addition of carries. -/
def triAdd (p q : R × R × R) : R × R × R := (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2)

/-- Componentwise `ℂ`-scalar multiplication of carries. -/
def triSmul (c : ℂ) (p : R × R × R) : R × R × R := (c • p.1, c • p.2.1, c • p.2.2)

/-- Right multiplication of a carry by a group element. -/
def triMulOf (p : R × R × R) (g : SL(2,ℤ)) : R × R × R :=
  (p.1 * MonoidAlgebra.of ℂ SL(2,ℤ) g, p.2.1 * MonoidAlgebra.of ℂ SL(2,ℤ) g,
    p.2.2 * MonoidAlgebra.of ℂ SL(2,ℤ) g)

/-- Componentwise finite sum of carries. -/
def triSum {ι : Type*} (s : Finset ι) (f : ι → R × R × R) : R × R × R :=
  (∑ i ∈ s, (f i).1, ∑ i ∈ s, (f i).2.1, ∑ i ∈ s, (f i).2.2)

@[simp] lemma triAdd_fst (p q : R × R × R) : (triAdd p q).1 = p.1 + q.1 := rfl
@[simp] lemma triAdd_snd (p q : R × R × R) : (triAdd p q).2.1 = p.2.1 + q.2.1 := rfl
@[simp] lemma triAdd_thd (p q : R × R × R) : (triAdd p q).2.2 = p.2.2 + q.2.2 := rfl
@[simp] lemma triSmul_fst (c : ℂ) (p : R × R × R) : (triSmul c p).1 = c • p.1 := rfl
@[simp] lemma triSmul_snd (c : ℂ) (p : R × R × R) : (triSmul c p).2.1 = c • p.2.1 := rfl
@[simp] lemma triSmul_thd (c : ℂ) (p : R × R × R) : (triSmul c p).2.2 = c • p.2.2 := rfl
@[simp] lemma triSum_fst {ι : Type*} (s : Finset ι) (f : ι → R × R × R) :
    (triSum s f).1 = ∑ i ∈ s, (f i).1 := rfl
@[simp] lemma triSum_snd {ι : Type*} (s : Finset ι) (f : ι → R × R × R) :
    (triSum s f).2.1 = ∑ i ∈ s, (f i).2.1 := rfl
@[simp] lemma triSum_thd {ι : Type*} (s : Finset ι) (f : ι → R × R × R) :
    (triSum s f).2.2 = ∑ i ∈ s, (f i).2.2 := rfl

/-- `carryComb` is additive for `triAdd`. -/
lemma carryComb_triAdd (p q : R × R × R) :
    carryComb (triAdd p q).1 (triAdd p q).2.1 (triAdd p q).2.2
      = carryComb p.1 p.2.1 p.2.2 + carryComb q.1 q.2.1 q.2.2 :=
  carryComb_add _ _ _ _ _ _

/-- `carryComb` is `ℂ`-homogeneous for `triSmul`. -/
lemma carryComb_triSmul (c : ℂ) (p : R × R × R) :
    carryComb (triSmul c p).1 (triSmul c p).2.1 (triSmul c p).2.2
      = c • carryComb p.1 p.2.1 p.2.2 :=
  carryComb_smul c _ _ _

/-- `carryComb` interacts with `triMulOf` by right multiplication. -/
lemma carryComb_triMulOf (p : R × R × R) (g : SL(2,ℤ)) :
    carryComb (triMulOf p g).1 (triMulOf p g).2.1 (triMulOf p g).2.2
      = carryComb p.1 p.2.1 p.2.2 * MonoidAlgebra.of ℂ SL(2,ℤ) g :=
  carryComb_mul_mono _ _ _ g

/-- `carryComb` is additive for finite sums of carries. -/
lemma carryComb_triSum {ι : Type*} (s : Finset ι) (f : ι → R × R × R) :
    carryComb (∑ i ∈ s, (f i).1) (∑ i ∈ s, (f i).2.1) (∑ i ∈ s, (f i).2.2)
      = ∑ i ∈ s, carryComb (f i).1 (f i).2.1 (f i).2.2 := by
  classical
  induction s using Finset.induction with
  | empty => simp [carryComb_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi,
        carryComb_add, ih]

/-! ## The bound predicate -/

/-- `CB p Cb K` says that each component of the carry `p` has `coeffNorm` at most `Cb` and
support Frobenius norm at most `K`. -/
def CB (p : R × R × R) (Cb K : ℝ) : Prop :=
  coeffNorm p.1 ≤ Cb ∧ coeffNorm p.2.1 ≤ Cb ∧ coeffNorm p.2.2 ≤ Cb ∧
    supportFrobLe p.1 K ∧ supportFrobLe p.2.1 K ∧ supportFrobLe p.2.2 K

lemma CB_mono {p : R × R × R} {Cb Cb' K K' : ℝ} (h : CB p Cb K) (hC : Cb ≤ Cb')
    (hK : K ≤ K') : CB p Cb' K' :=
  ⟨le_trans h.1 hC, le_trans h.2.1 hC, le_trans h.2.2.1 hC,
    supportFrobLe_mono h.2.2.2.1 hK, supportFrobLe_mono h.2.2.2.2.1 hK,
    supportFrobLe_mono h.2.2.2.2.2 hK⟩

lemma CB_triSmul {p : R × R × R} {Cb K : ℝ} (c : ℂ) (h : CB p Cb K) :
    CB (triSmul c p) (‖c‖ * Cb) K :=
  ⟨le_trans (coeffNorm_smul_le c p.1) (mul_le_mul_of_nonneg_left h.1 (norm_nonneg c)),
    le_trans (coeffNorm_smul_le c p.2.1) (mul_le_mul_of_nonneg_left h.2.1 (norm_nonneg c)),
    le_trans (coeffNorm_smul_le c p.2.2) (mul_le_mul_of_nonneg_left h.2.2.1 (norm_nonneg c)),
    supportFrobLe_smul c h.2.2.2.1, supportFrobLe_smul c h.2.2.2.2.1,
    supportFrobLe_smul c h.2.2.2.2.2⟩

lemma CB_triAdd {p q : R × R × R} {Cb Cb' K K' : ℝ} (hp : CB p Cb K) (hq : CB q Cb' K') :
    CB (triAdd p q) (Cb + Cb') (max K K') :=
  ⟨le_trans (coeffNorm_add_le p.1 q.1) (add_le_add hp.1 hq.1),
    le_trans (coeffNorm_add_le p.2.1 q.2.1) (add_le_add hp.2.1 hq.2.1),
    le_trans (coeffNorm_add_le p.2.2 q.2.2) (add_le_add hp.2.2.1 hq.2.2.1),
    supportFrobLe_add hp.2.2.2.1 hq.2.2.2.1,
    supportFrobLe_add hp.2.2.2.2.1 hq.2.2.2.2.1,
    supportFrobLe_add hp.2.2.2.2.2 hq.2.2.2.2.2⟩

lemma CB_triMulOf {p : R × R × R} {Cb K : ℝ} (g : SL(2,ℤ)) (h : CB p Cb K) :
    CB (triMulOf p g) Cb (K * Frob g) :=
  ⟨le_trans (coeffNorm_mul_of_le p.1 g) h.1,
    le_trans (coeffNorm_mul_of_le p.2.1 g) h.2.1,
    le_trans (coeffNorm_mul_of_le p.2.2 g) h.2.2.1,
    supportFrobLe_mul_of h.2.2.2.1 g, supportFrobLe_mul_of h.2.2.2.2.1 g,
    supportFrobLe_mul_of h.2.2.2.2.2 g⟩

lemma CB_triSum {ι : Type*} (s : Finset ι) (f : ι → R × R × R) {Cb K : ℝ}
    (h : ∀ i ∈ s, CB (f i) Cb K) :
    CB (∑ i ∈ s, (f i).1, ∑ i ∈ s, (f i).2.1, ∑ i ∈ s, (f i).2.2) ((s.card : ℝ) * Cb) K := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc coeffNorm (∑ i ∈ s, (f i).1) ≤ ∑ i ∈ s, coeffNorm (f i).1 := coeffNorm_sum_le _ _
      _ ≤ ∑ i ∈ s, Cb := Finset.sum_le_sum fun i hi => (h i hi).1
      _ = (s.card : ℝ) * Cb := by rw [Finset.sum_const, nsmul_eq_mul]
  · calc coeffNorm (∑ i ∈ s, (f i).2.1) ≤ ∑ i ∈ s, coeffNorm (f i).2.1 := coeffNorm_sum_le _ _
      _ ≤ ∑ i ∈ s, Cb := Finset.sum_le_sum fun i hi => (h i hi).2.1
      _ = (s.card : ℝ) * Cb := by rw [Finset.sum_const, nsmul_eq_mul]
  · calc coeffNorm (∑ i ∈ s, (f i).2.2) ≤ ∑ i ∈ s, coeffNorm (f i).2.2 := coeffNorm_sum_le _ _
      _ ≤ ∑ i ∈ s, Cb := Finset.sum_le_sum fun i hi => (h i hi).2.2.1
      _ = (s.card : ℝ) * Cb := by rw [Finset.sum_const, nsmul_eq_mul]
  · exact supportFrobLe_sum s (fun i => (f i).1) (fun i hi => (h i hi).2.2.2.1)
  · exact supportFrobLe_sum s (fun i => (f i).2.1) (fun i hi => (h i hi).2.2.2.2.1)
  · exact supportFrobLe_sum s (fun i => (f i).2.2) (fun i hi => (h i hi).2.2.2.2.2)

end Work.Asymptotics
