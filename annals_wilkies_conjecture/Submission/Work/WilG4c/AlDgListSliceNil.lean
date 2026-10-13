import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4c.SliceNilDefs
import Submission.Work.WilG4c.NilAux1
import Submission.Work.WilG4c.NilAux2
import Submission.Work.WilG4c.NilAux3
import Submission.Work.WilG4c.ZpData_good
import Submission.Work.WilG4c.ZpData_deg_le
import Submission.Work.WilG4c.inflated_mem_m

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

theorem AlDgListSliceNil (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f [] ∈
        S.Ω a (MvPolynomial.eval ![D, (0 : ℕ)] b) (p + (n + 1) + 1) := by
  obtain ⟨A, C, hInfl⟩ := inflated_mem_m S p n
  refine ⟨max F0 (Work.WilG0.oFmt F0 (ZpShape p n) + 1 + A + 1) + 1,
    MvPolynomial.C (18 + C) + MvPolynomial.C 3 * MvPolynomial.X 0, ?_⟩
  intro D f hf
  have hgood : (ZpShape p n).Good S F0 (ZpData p n f D) :=
    _root_.Work.WilG4c.ZpData_good p n F0 D f hf
  have hZp := Work.WilG0.realize_mem_Omega S (ZpShape p n) F0 (ZpData p n f D) hgood
  rw [ZpShape_realize p n f D] at hZp
  have hZ := S.proj hZp
  rw [projLast_ZpSet p n f] at hZ
  have hZ' : PtContLocus p n f ∈ S.Ω (Work.WilG0.oFmt F0 (ZpShape p n) + 1)
      ((ZpShape p n).deg (ZpData p n f D)) (p + (n + 1)) := hZ
  have hW : Infl.tgt p n (PtContLocus p n f) ∈
      S.Ω (Work.WilG0.oFmt F0 (ZpShape p n) + 1 + A)
        ((ZpShape p n).deg (ZpData p n f D) + C) (p + (n + 1)) :=
    hInfl _ _ _ hZ'
  have hW' := S.prod_right hW
  have hf' : famGraph f ∈ S.Ω F0 D (Nc p n + 1) := hf
  have hf'' : famGraph f ∈ S.Ω (max F0 (Work.WilG0.oFmt F0 (ZpShape p n) + 1 + A + 1)) D
      (Nc p n + 1) := Work.WilG0.Omega_mono_F (le_max_left _ _) hf'
  have hW'' : {z : Fin (Nc p n + 1) → ℝ | Fin.init z ∈ Infl.tgt p n (PtContLocus p n f)} ∈
      S.Ω (max F0 (Work.WilG0.oFmt F0 (ZpShape p n) + 1 + A + 1))
        ((ZpShape p n).deg (ZpData p n f D) + C) (Nc p n + 1) :=
    Work.WilG0.Omega_mono_F (le_max_right _ _) hW'
  have hInter := Work.WilG0.Omega_inter2 hf'' hW''
  have hset : AlDgListSlice p n f [] =
      famGraph f ∩ {z : Fin (Nc p n + 1) → ℝ |
        Fin.init z ∈ Infl.tgt p n (PtContLocus p n f)} := by
    rw [AlDgListSlice_nil_eq p n f, ← contDiffAt_zero_eq_infl p n f]
  rw [← hset] at hInter
  have hdeg : (ZpShape p n).deg (ZpData p n f D) ≤ 2 * D + 18 :=
    _root_.Work.WilG4c.ZpData_deg_le p n f D
  have hD : D + ((ZpShape p n).deg (ZpData p n f D) + C) ≤
      MvPolynomial.eval ![(D : ℕ), 0]
        (MvPolynomial.C (18 + C) + MvPolynomial.C 3 * MvPolynomial.X 0) := by
    simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    omega
  exact Work.WilG0.Omega_mono_FD le_rfl hD hInter

end Work.WilkG4c

/-! The directory-induced name `Work.WilG4c` of the same theorem (see `inflated_mem_m.lean`
and `ZpData_good.lean` for the same convention). -/
namespace Work.WilG4c

theorem AlDgListSliceNil (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice p n f [] ∈
        S.Ω a (MvPolynomial.eval ![D, (0 : ℕ)] b) (p + (n + 1) + 1) :=
  _root_.Work.WilkG4c.AlDgListSliceNil S hcd hder p n F0

end Work.WilG4c
