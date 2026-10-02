import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Whitney.eSym_sum_subsets
import Submission.Work.Gen.LhCalc
import Submission.Work.Kunneth.PointDefs
import Submission.Work.Whitney.eSymC_remove
import Submission.Work.Gen.cupChern_zero_lhMap
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.LH
import Submission.Work.Gen.eSymClass
import Submission.Work.Gen.chernRoot_split

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# Auxiliary lemmas for `Work.Whitney.cruxOfPieces`

The assembly of the crux of the Whitney sum formula from the three pieces
(`Work.Whitney.cruxSummandSection`, `Work.Whitney.cruxDeltaForm`, `Work.Whitney.eSymC_remove`)
needs a number of elementary (de)normalisations of the classes involved.  This module collects them.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## `pow2` and `zPow` are the same series -/

theorem pow2_eq_zPow (t : Coh ℤ 2 B) : Work.Kunneth.pow2 t = ChernRel.zPow t := by
  funext i
  induction i with
  | zero => rw [Work.Kunneth.pow2_zero, ChernRel.zPow_zero, Work.Thom.cohTransport_rfl]
  | succ i ih => rw [Work.Kunneth.pow2_succ, ChernRel.zPow_succ, ih]

theorem pow2_apply_eq_zPow (t : Coh ℤ 2 B) (j : ℕ) :
    Work.Kunneth.pow2 t j = ChernRel.zPow t j :=
  congrFun (pow2_eq_zPow t) j

/-! ## Moving the signs `(-1)^m` out of the graded product -/

theorem cupChern_negOnePow_left (a b m : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    cupChern a b (((-1 : ℤ) ^ m) • x) y = ((-1 : ℤ) ^ m) • cupChern a b x y := by
  rcases Nat.even_or_odd m with he | ho
  · rw [Even.neg_one_pow he, one_zsmul, one_zsmul]
  · rw [Odd.neg_one_pow ho, neg_one_zsmul, neg_one_zsmul, ChernRel.cupChern_neg_left]

theorem cupChern_negOnePow_right (a b m : ℕ) (x : Coh ℤ (2 * a) B) (y : Coh ℤ (2 * b) B) :
    cupChern a b x (((-1 : ℤ) ^ m) • y) = ((-1 : ℤ) ^ m) • cupChern a b x y := by
  rcases Nat.even_or_odd m with he | ho
  · rw [Even.neg_one_pow he, one_zsmul, one_zsmul]
  · rw [Odd.neg_one_pow ho, neg_one_zsmul, neg_one_zsmul, ChernRel.cupChern_neg_right]

/-! ## `deltaCup` and `psiCoeff` in cup-product form -/

/-- `deltaCup N M δ` is `δ ⌣ eSym N M (N-1)`. -/
theorem deltaCup_eq {ι : Type} [Fintype ι] (N : ℕ)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (δ : Coh ℤ 0 B) :
    deltaCup N M δ
      = cohTransport (by omega : 2 * (0 + (N - 1)) = 2 * (N - 1))
          (cupChern 0 (N - 1) δ (Work.Gen.eSym N M (N - 1))) := by
  rw [deltaCup, cupChern_def, Work.Whitney.cohTransport_trans]

/-- `psiCoeff hN M δ j` is `(-1)^{j+1}·δ ⌣ eSym N M (N-2-j)`. -/
theorem psiCoeff_eq {ι : Type} [Fintype ι] {N : ℕ} (hN : 2 ≤ N)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (δ : Coh ℤ 0 B)
    (j : {j : Fin N // (j : ℕ) ≤ N - 2}) :
    psiCoeff hN M δ j
      = cohTransport (by omega : 2 * (0 + (N - 2 - (j : ℕ))) = 2 * (N - 2 - (j : ℕ)))
          (cupChern 0 (N - 2 - (j : ℕ)) (((-1 : ℤ) ^ ((j : ℕ) + 1)) • δ)
            (Work.Gen.eSym N M (N - 2 - (j : ℕ)))) := by
  rw [psiCoeff, cupChern_def, Work.Whitney.cohTransport_trans]

/-! ## Pulling `ζ`-powers and Leray–Hirsch combinations back along a section -/

theorem zetaPow_pull_section {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (s : C(B, Work.LerayHirsch.ProjSpace Z))
    (t : Coh ℤ 2 B) (ht : (CohMap s ℤ 2).hom (Work.LerayHirsch.zeta Z) = t) (i : ℕ) :
    (CohMap s ℤ (2 * i)).hom (Work.LerayHirsch.zetaPow Z i) = Work.Kunneth.pow2 t i := by
  rw [← Work.Kunneth.pow2_zeta Z i, Work.Kunneth.pow2_CohMap s (Work.LerayHirsch.zeta Z) i, ht]

theorem lhMap_pull_section {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (s : C(B, Work.LerayHirsch.ProjSpace Z))
    (hs : ∀ x, Work.LerayHirsch.projMap Z (s x) = x)
    (t : Coh ℤ 2 B) (ht : (CohMap s ℤ 2).hom (Work.LerayHirsch.zeta Z) = t)
    (k : ℕ) (F : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    (CohMap s ℤ (2 * k)).hom (Work.LerayHirsch.lhMap Z k F)
      = ∑ i : {i : Fin m // (i : ℕ) ≤ k},
          cohTransport (by omega : 2 * ((k - (i : ℕ)) + (i : ℕ)) = 2 * k)
            (cupChern (k - (i : ℕ)) (i : ℕ) (F i) (Work.Kunneth.pow2 t (i : ℕ))) := by
  have hpid : (Work.LerayHirsch.projMap Z).comp s = ContinuousMap.id B :=
    ContinuousMap.ext hs
  rw [Work.LerayHirsch.lhMap_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Work.LerayHirsch.lhTerm_def, Work.Whitney.cohTransport_CohMap, Work.Whitney.cupChern_CohMap]
  rw [Work.Thom.CohMap_comp_apply s (Work.LerayHirsch.projMap Z) ℤ (2 * (k - (i : ℕ))) (F i), hpid,
    Work.Thom.CohMap_id]
  simp only [ModuleCat.hom_id]
  rw [zetaPow_pull_section Z s t ht (i : ℕ)]
  exact Work.LerayHirsch.cohTransport_congr_proof _ _

/-! ## Reindexing the sum over `{j : Fin N // j ≤ N-2}` -/

/-- The inclusion `Fin (N-1) ↪ {j : Fin N // j ≤ N-2}`. -/
def finSubIncl {N : ℕ} (hN : 2 ≤ N) (i : Fin (N - 1)) : {j : Fin N // (j : ℕ) ≤ N - 2} :=
  ⟨⟨(i : ℕ), by omega⟩, by
    show (i : ℕ) ≤ N - 2
    omega⟩

/-- The increasing bijection `{j : Fin N // j ≤ N-2} ≃ Fin (N-1)`. -/
def finSubEquiv {N : ℕ} (hN : 2 ≤ N) :
    {j : Fin N // (j : ℕ) ≤ N - 2} ≃ Fin (N - 1) where
  toFun j := ⟨(j : ℕ), by
    have hj : (j : ℕ) ≤ N - 2 := j.2
    omega⟩
  invFun i := finSubIncl hN i
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv i := by
    apply Fin.ext
    rfl

theorem sum_subtype_fin {N : ℕ} (hN : 2 ≤ N) {M : Type} [AddCommMonoid M]
    (F : (j : {j : Fin N // (j : ℕ) ≤ N - 2}) → M) :
    (∑ j, F j) = ∑ i : Fin (N - 1), F (finSubIncl hN i) := by
  rw [← Equiv.sum_comp (finSubEquiv hN).symm F]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply congrArg F
  apply Subtype.ext
  apply Fin.ext
  rfl

/-! ## `skipIdx` depends only on its index -/

theorem skipIdx_congr {N : ℕ} (h h' : 1 ≤ N) (k : Fin N) :
    skipIdx h k = skipIdx h' k := by
  funext i
  apply Fin.ext
  rw [skipIdx_val]

/-! ## Multiplication by a degree-`0` class -/

/-- `δ ⌣ x` for `δ ∈ H⁰(B)` and `x ∈ H^{2m}(B)`, with the degree bookkeeping abstracted. -/
noncomputable def dcup (m : ℕ) (δ : Coh ℤ 0 B) (x : Coh ℤ (2 * m) B) : Coh ℤ (2 * m) B :=
  cohTransport (by omega : 2 * (0 + m) = 2 * m) (cupChern 0 m δ x)

theorem dcup_add (m : ℕ) (δ : Coh ℤ 0 B) (x y : Coh ℤ (2 * m) B) :
    dcup m δ (x + y) = dcup m δ x + dcup m δ y := by
  rw [dcup, dcup, dcup, ChernRel.cupChern_add_right]
  exact map_add (cohTransportLM (by omega : 2 * (0 + m) = 2 * m)) _ _

theorem dcup_neg (m : ℕ) (δ : Coh ℤ 0 B) (x : Coh ℤ (2 * m) B) :
    dcup m δ (-x) = -dcup m δ x := by
  rw [dcup, dcup, ChernRel.cupChern_neg_right]
  exact map_neg (cohTransportLM (by omega : 2 * (0 + m) = 2 * m)) _

/-- **`δ` commutes past a product**: `t ⌣ (δ ⌣ x) = δ ⌣ (x ⌣ t)`.  Stated with an arbitrary
number `j` of factors `t`: `(t^j) ⌣ (δ ⌣ x) = δ ⌣ (x ⌣ t^j)`. -/
theorem dcup_cupChern_gen (a j : ℕ) (δ : Coh ℤ 0 B) (t : Coh ℤ 2 B) (x : Coh ℤ (2 * a) B) :
    cupChern a j (dcup a δ x) (Work.Kunneth.pow2 t j)
      = dcup (a + j) δ (cupChern a j x (Work.Kunneth.pow2 t j)) := by
  rw [dcup, dcup]
  rw [Work.Gen.cupChern_cast_left (a := 0 + a) (a' := a) (b := j)
      (by omega : 2 * (0 + a) = 2 * a)]
  rw [Work.Gen.cupChern_assoc]
  simp only [Work.Whitney.cohTransport_trans]

/-- The degree cast commutes with the negation. -/
theorem cohTransport_neg {n n' : ℕ} (h : n = n') (x : Coh ℤ n B) :
    cohTransport h (-x) = -cohTransport h x :=
  map_neg (cohTransportLM h) x

/-- `(-1)^{i+1} • x = - ((-1)^i • x)`. -/
theorem negOnePow_succ_smul {n : ℕ} (i : ℕ) (x : Coh ℤ n B) :
    ((-1 : ℤ) ^ (i + 1)) • x = - (((-1 : ℤ) ^ i) • x) := by
  rcases Nat.even_or_odd i with hEven | hOdd
  · rw [Even.neg_one_pow hEven, one_zsmul,
      show (-1 : ℤ) ^ (i + 1) = -1 from
        Odd.neg_one_pow (Nat.odd_add_one.mpr (Nat.not_odd_iff_even.mpr hEven)),
      neg_one_zsmul]
  · rw [show (-1 : ℤ) ^ (i + 1) = 1 from
        Even.neg_one_pow (Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hOdd)),
      Odd.neg_one_pow hOdd, neg_one_zsmul, one_zsmul]
    exact (neg_neg x).symm

/-- **`dcup` and the signs `(-1)^m` in the second argument.** -/
theorem dcup_arg_negOnePow_smul (a m : ℕ) (δ : Coh ℤ 0 B) (x : Coh ℤ (2 * a) B) :
    dcup a δ (((-1 : ℤ) ^ m) • x) = ((-1 : ℤ) ^ m) • dcup a δ x := by
  rw [dcup, dcup, cupChern_negOnePow_right, Work.Thom.cohTransport_zsmul]

/-- **`dcup` commutes with the degree cast.** -/
theorem dcup_cast {a m : ℕ} (h : 2 * a = 2 * m) (δ : Coh ℤ 0 B) (x : Coh ℤ (2 * a) B) :
    dcup m δ (cohTransport h x) = cohTransport h (dcup a δ x) := by
  rw [dcup, dcup]
  rw [Work.Gen.cupChern_cast_right (a := 0) (b := m) (b' := a) h]
  simp only [Work.Whitney.cohTransport_trans]

/-- `dcup` is additive over a finite sum. -/
theorem dcup_sum {α : Type} [Fintype α] (m : ℕ) (δ : Coh ℤ 0 B)
    (f : α → Coh ℤ (2 * m) B) :
    dcup m δ (∑ i, f i) = ∑ i, dcup m δ (f i) := by
  simp only [dcup]
  rw [Work.Gen.cupChern_sum_right]
  exact Work.Gen.cohTransport_sum _ _

/-- **`δ` commutes past a single product**: `(δ ⌣ x) ⌣ t = δ ⌣ (x ⌣ t)`. -/
theorem dcup_cupChern_one (a : ℕ) (δ : Coh ℤ 0 B) (t : Coh ℤ 2 B) (x : Coh ℤ (2 * a) B) :
    cupChern a 1 (dcup a δ x) t = dcup (a + 1) δ (cupChern a 1 x t) := by
  rw [dcup, dcup]
  rw [Work.Gen.cupChern_cast_left (a := 0 + a) (a' := a) (b := 1)
      (by omega : 2 * (0 + a) = 2 * a)]
  rw [Work.Gen.cupChern_assoc]
  simp only [Work.Whitney.cohTransport_trans]

/-- **`dcup` and the signs `(-1)^m`.** -/
theorem dcup_negOnePow_smul (a m : ℕ) (δ : Coh ℤ 0 B) (x : Coh ℤ (2 * a) B) :
    dcup a (((-1 : ℤ) ^ m) • δ) x = ((-1 : ℤ) ^ m) • dcup a δ x := by
  rw [dcup, dcup, cupChern_negOnePow_left, Work.Thom.cohTransport_zsmul]


/-- `psiCoeff hN M δ j` is `δ' ⌣ eSym N M (N-2-j)` with `δ' = (-1)^{j+1}·δ`, in `dcup` form. -/
theorem psiCoeff_eq_dcup {ι : Type} [Fintype ι] {N : ℕ} (hN : 2 ≤ N)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (δ : Coh ℤ 0 B)
    (j : {j : Fin N // (j : ℕ) ≤ N - 2}) :
    psiCoeff hN M δ j
      = dcup (N - 2 - (j : ℕ)) (((-1 : ℤ) ^ ((j : ℕ) + 1)) • δ)
          (Work.Gen.eSym N M (N - 2 - (j : ℕ))) := by
  rw [psiCoeff, dcup, cupChern_def, Work.Whitney.cohTransport_trans]

/-- `deltaCup N M δ` is `δ ⌣ eSym N M (N-1)`, in `dcup` form. -/
theorem deltaCup_eq_dcup {ι : Type} [Fintype ι] (N : ℕ)
    (M : Fin N → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (δ : Coh ℤ 0 B) :
    deltaCup N M δ = dcup (N - 1) δ (Work.Gen.eSym N M (N - 1)) := by
  rw [deltaCup, dcup, cupChern_def, Work.Whitney.cohTransport_trans]

/-! ## The expansion of `convSeries E (zPow (-t))` -/

theorem convSeries_zPow_neg_expand (E : (i : ℕ) → Coh ℤ (2 * i) B) (t : Coh ℤ 2 B) (n : ℕ) :
    Work.LerayHirsch.convSeries E (ChernRel.zPow (-t)) n
      = ∑ i : Fin (n + 1),
          cohTransport (by have := i.isLt; omega : 2 * ((n - (i : ℕ)) + (i : ℕ)) = 2 * n)
            (((-1 : ℤ) ^ (i : ℕ)) • (cupChern (n - (i : ℕ)) (i : ℕ) (E (n - (i : ℕ)))
              (ChernRel.zPow t (i : ℕ)))) := by
  have key : Work.LerayHirsch.convSeries E (ChernRel.zPow (-t)) n
      = ∑ i ∈ Finset.range (n + 1), (if h : i ≤ n then
          cohTransport (by omega : 2 * ((n - i) + i) = 2 * n)
            (((-1 : ℤ) ^ i) • (cupChern (n - i) i (E (n - i)) (ChernRel.zPow t i)))
          else 0) := by
    rw [Work.Gen.zPow_neg t, Work.Whitney.convSeries_comm, Work.LerayHirsch.convSeries]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [dif_pos hi']
    rw [Work.Gen.convTerm_geo_eq hi' E t, Work.Thom.cohTransport_zsmul]
  rw [key]
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => if h : i ≤ n then
      cohTransport (by omega : 2 * ((n - i) + i) = 2 * n)
        (((-1 : ℤ) ^ i) • (cupChern (n - i) i (E (n - i)) (ChernRel.zPow t i)))
      else 0) (n + 1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos (by have := i.isLt; omega : (i : ℕ) ≤ n)]

end

end Work.Whitney
