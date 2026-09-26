import Mathlib
import Submission.Work.SG.SGsepDefs
import Submission.Work.SGsep.hand.HandDefs
import Submission.Work.SGsep.hand.HandDefs2
import Submission.Work.SGsep.hand.AxisTab
import Submission.Work.SGsep.hand.HandPrep
import Submission.Work.SGsep.hand.HandCore
import Submission.Work.SGsep.hand.HandValue
import Submission.Work.SGsep.hand.index_unique
import Submission.Work.SGsep.table_facts
import Submission.Work.SGsep.PairAux
import Submission.Work.SGsep.PairAux2

namespace Work.SGsep

open Work.SG
open Work.SGsep.Hand
open Work.SGsep.Hand.Data
open Work.SGsep.hand

/-- Counting transfer: if the positions of two tables are related by a bijection carrying equal
values, then the number of positions carrying any given value is the same. -/
theorem countP_eq_of_fin_map {β : Type*} [BEq β] (g : Option Data.HandCert → β)
    {ta tb : List (Option Data.HandCert)} {m n : Nat} (hm : ta.length = m) (hn : tb.length = n)
    (f : Fin m → Fin n) (hf : Function.Bijective f)
    (hval : ∀ i : Fin m, g (ta.getD i.val none) = g (tb.getD (f i).val none)) (v : β) :
    ta.countP (fun c => g c == v) = tb.countP (fun c => g c == v) := by
  have key : ∀ (l : List (Option Data.HandCert)) (M : Nat), l.length = M →
      l.countP (fun c => g c == v)
        = ((Finset.range M).filter (fun i => g (l.getD i none) == v)).card := by
    intro l M hM
    rw [← hM]
    calc l.countP (fun c => g c == v)
        = (l.map g).countP (fun c => c == v) := by
          show l.countP ((fun c => c == v) ∘ g) = (l.map g).countP (fun c => c == v)
          rw [← List.countP_map]
      _ = ((List.range l.length).map (fun i => g (l.getD i none))).countP
            (fun c => c == v) := by rw [PSep.map_eq_map_getD]
      _ = (List.range l.length).countP (fun i => g (l.getD i none) == v) :=
          List.countP_map (l := List.range l.length) (f := fun i => g (l.getD i none))
            (p := fun c => c == v)
      _ = ((List.range l.length).filter (fun i => g (l.getD i none) == v)).length := by
          rw [List.countP_eq_length_filter]
      _ = ((Finset.range l.length).filter (fun i => g (l.getD i none) == v)).card := by
          rw [← List.toFinset_card_of_nodup
            (List.Nodup.filter (fun i => g (l.getD i none) == v) List.nodup_range),
            List.toFinset_filter, List.toFinset_range]
  rw [key ta m hm, key tb n hn]
  refine Finset.card_bij (fun i hi =>
      (f ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩).val) ?_ ?_ ?_
  · intro i hi
    have hi' : i < m := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨(f ⟨i, hi'⟩).isLt, ?_⟩
    rw [← hval ⟨i, hi'⟩]
    exact hi.2
  · intro i1 h1 i2 h2 heq
    have h1' : i1 < m := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    have h2' : i2 < m := Finset.mem_range.mp (Finset.mem_filter.mp h2).1
    have hfin : (⟨i1, h1'⟩ : Fin m) = ⟨i2, h2'⟩ := hf.1 (Fin.ext heq)
    exact congrArg Fin.val hfin
  · intro j hj
    have hj' : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    obtain ⟨i, hi⟩ := hf.2 ⟨j, hj'⟩
    refine ⟨i.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨i.isLt, ?_⟩
      rw [hval i, show (f i).val = j from congrArg Fin.val hi]
      exact (Finset.mem_filter.mp hj).2
    · exact congrArg Fin.val hi

/-- The `hand` (handedness) invariant separates for `det U = 1`: if the number of rotations
(`det 1`, order `≥ 3`) with handedness value `(ord, h, j mod h)` differs over the *full* tables
(`ta.length = n`, `tb.length = n`, entrywise `Data.HandCert.chk`), then there is no integral
equivalence with `U.det = 1`.  Meaning of the check (`Data/SepCheck.lean`, `Data/HandCert`):
`c` is a primitive axis vector of `A` (`(A-1)c = 0`, `β·c = 1`), oriented so that
`det(e_q, A e_q, c) > 0`, `N_A = c wᵀ`, `h = gcd w` (so `N_A ℤ³ = h ℤ c`), and `v_A = j c`; the
value is `(ord A, h, j mod h)`.  Under `A ↦ U A U⁻¹` with `det U = 1`, `c ↦ Uc` (the
determinant condition is preserved since `det(Ux, UAx, Uc) = det U · det(x,Ax,c)`) and `h`,
`j mod h` are preserved (`vA_conj`); so the certificate value is determined by `(A, v_A)` and
the multiset of values is a conjugacy invariant. -/
theorem hand_separates (k l : Fin 230) (ord h : ℕ) (jm : ℤ) (ta tb : List (Option Data.HandCert))
    (hk : TauOnTable k) (hl : TauOnTable l)
    (hlk : ta.length = (Data.repArith k).n) (hll : tb.length = (Data.repArith l).n)
    (hka : ∀ i, i < ta.length → Data.HandCert.chk k i (ta.getD i none) = true)
    (hlb : ∀ i, i < tb.length → Data.HandCert.chk l i (tb.getD i none) = true)
    (hne : ta.countP (fun c => Data.handVal c == some (ord, h, jm)) ≠
           tb.countP (fun c => Data.handVal c == some (ord, h, jm))) :
    ¬ ∃ U : IMat, U.det = 1 ∧ ∃ s : Fin 3 → ℝ,
        IntEquiv (arithRep (sgArith k)) (sgTau k) (arithRep (sgArith l)) (sgTau l) U s := by
  rintro ⟨U, hUdet, s, hIE⟩
  classical
  have hU : IsUnit U.det := by rw [hUdet]; exact isUnit_one
  -- the integral equivalence in the `invMat` form
  have hIE1 : ∀ A, A ∈ arithRep (sgArith l) ↔
      ∃ B ∈ arithRep (sgArith k), A = U * B * invMat U := by
    intro A
    rw [hIE.1 A]
    constructor
    · rintro ⟨B, hB, h⟩
      exact ⟨B, hB, by rw [h, (misc_bridges.1 hU).symm]⟩
    · rintro ⟨B, hB, h⟩
      exact ⟨B, hB, by rw [h, (misc_bridges.1 hU).symm]⟩
  -- conjugation is injective as a map on matrices
  have hconj : ∀ A : IMat, invMat U * (U * A * invMat U) * U = A := by
    intro A
    calc invMat U * (U * A * invMat U) * U
        = (invMat U * U) * A * (invMat U * U) := by noncomm_ring
      _ = A := by rw [invMat_mul hU, one_mul, mul_one]
  have hconj_inj : ∀ {A B : IMat}, U * A * invMat U = U * B * invMat U → A = B := by
    intro A B h
    have h' := congrArg (fun M => invMat U * M * U) h
    rw [hconj A, hconj B] at h'
    exact h'
  -- the two tables have the same length
  have hcard : (Data.repArith k).n = (Data.repArith l).n := by
    rw [← card_Tk k, ← card_Tk l]
    refine Finset.card_bij (fun A _ => U * A * invMat U) ?_ ?_ ?_
    · intro A hA
      rw [mem_Tk_iff] at hA ⊢
      exact (hIE1 (U * A * invMat U)).mpr ⟨A, hA, rfl⟩
    · intro A1 _ A2 _ h
      exact hconj_inj h
    · intro B hB
      rw [mem_Tk_iff] at hB
      obtain ⟨A, hA, hAB⟩ := (hIE1 B).mp hB
      exact ⟨A, (mem_Tk_iff k A).mpr hA, hAB.symm⟩
  -- the index correspondence
  have hex : ∀ i : Fin (Data.repArith k).n,
      ∃ j : Fin (Data.repArith l).n,
        Ah l j.val = U * Ah k i.val * invMat U := by
    intro i
    have hA : Ah k i.val ∈ arithRep (sgArith k) := Ah_mem i.isLt
    have hB : U * Ah k i.val * invMat U ∈ arithRep (sgArith l) :=
      (hIE1 (U * Ah k i.val * invMat U)).mpr ⟨_, hA, rfl⟩
    obtain ⟨j, hj, -⟩ := index_unique hB
    exact ⟨⟨j, hj.1⟩, hj.2⟩
  let f : Fin (Data.repArith k).n → Fin (Data.repArith l).n := fun i => (hex i).choose
  have hf : ∀ i, Ah l (f i).val = U * Ah k i.val * invMat U := fun i => (hex i).choose_spec
  -- indices are determined by the element
  have hidx : ∀ {i1 i2 : Nat}, i1 < (Data.repArith k).n → i2 < (Data.repArith k).n →
      Ah k i1 = Ah k i2 → i1 = i2 := by
    intro i1 i2 h1 h2 heq
    exact PSep.elI_injOn k h1 h2 heq
  have hf_inj : Function.Injective f := by
    intro i1 i2 heq
    have hl_eq : U * Ah k i1.val * invMat U = U * Ah k i2.val * invMat U := by
      rw [← hf i1, ← hf i2, heq]
    exact Fin.ext (hidx i1.isLt i2.isLt (hconj_inj hl_eq))
  have hf_bij : Function.Bijective f := by
    have hf'_inj : Function.Injective (fun i : Fin (Data.repArith k).n =>
        Fin.cast hcard.symm (f i)) := fun i1 i2 h => hf_inj ((Fin.cast_injective hcard.symm) h)
    have hf'_surj := Finite.injective_iff_surjective.mp hf'_inj
    refine ⟨hf_inj, fun j => ?_⟩
    obtain ⟨i, hi⟩ := hf'_surj (Fin.cast hcard.symm j)
    exact ⟨i, (Fin.cast_injective hcard.symm) hi⟩
  -- corresponding positions carry equal values
  have hval_e : ∀ i : Fin (Data.repArith k).n,
      Data.handVal (ta.getD i.val none) = Data.handVal (tb.getD (f i).val none) := by
    intro i
    exact Work.SGsep.Hand.handVal_eq_of_corresponds U s hU hUdet hIE hk hl
      (i := i.val) (j := (f i).val)
      i.isLt (f i).isLt (hf i)
      (ta.getD i.val none) (by exact hka i.val (by rw [hlk]; exact i.isLt))
      (tb.getD (f i).val none) (by exact hlb (f i).val (by rw [hll]; exact (f i).isLt))
  exact hne (countP_eq_of_fin_map Data.handVal hlk hll f hf_bij hval_e (some (ord, h, jm)))

end Work.SGsep
