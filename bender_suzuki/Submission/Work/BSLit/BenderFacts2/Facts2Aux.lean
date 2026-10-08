import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2Defs
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.B_split_setup
import Submission.Work.Models.PSL2.involutions_B
import Submission.Work.Models.PSL2.ncard_involutions_B
import Submission.Work.Models.PSL2.U_facts
import Submission.Work.Models.PSL2.B_facts
import Submission.Work.Models.PSL2.stronglyEmbedded_eq_conj_B
import Submission.Work.Models.PSL2.pslEquiv
import Submission.Work.BSLit.BenderFacts2.sl2_mem_U_of_orderOf_eq_two_pow
import Submission.Work.BSLit.BenderFacts2.Facts2SL2Aux
import Submission.Work.BSLit.BenderFacts2.sl2_centralizer_isCyclic_of_trace_ne_zero
import Submission.Work.BSLit.BenderFacts2.benderFacts2For_map_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.BenderFacts2.Facts2Aux` — reduction of `BenderFacts2For` to the Borel

The three clauses are proved for `G = SL(2,F)` and the standard Borel `B ≤ G`, then transported
to an arbitrary strongly embedded subgroup `H` of `G` (a conjugate of `B`, by
`Work.Models.PSL2.stronglyEmbedded_eq_conj_B`) and finally to `PSL(2,2ⁿ)` along
`Work.Models.PSL2.pslEquiv`.

This file contains the two `SL(2,F)` steps:

* `unip_mul_involution_facts` — for `u = unip c` (`c ≠ 0`) and an involution `t ∉ B`, the element
  `x = u * t` has non-zero `(1,0)`-entry and non-zero trace, and `u` inverts it;
* `benderFacts2For_sl2_B` — the three clauses for the Borel `B` (using the delegated lemmas
  `sl2_mem_U_of_orderOf_eq_two_pow`, `sl2_conj_eq_inv_of_mem_centralizer` and
  `sl2_centralizer_isCyclic_of_trace_ne_zero`);
* `benderFacts2For_sl2` — the three clauses for an arbitrary strongly embedded subgroup of `G`.

The transport to `PSL(2,2ⁿ)` is in the deliverable file `pSL2_benderModelFacts2.lean`.
-/

set_option autoImplicit false

open Matrix

namespace Work.BSLit.BenderFacts2

open Work.Models Work.Models.PSL2

/-- **The coordinates of `u(c) * t`** for `u(c) = unip c` (`c ≠ 0`) and an involution `t ∉ B`:
the `(1,0)`-entry is `t₁₀ ≠ 0`, the trace is `c * t₁₀ ≠ 0`, and `u(c)` inverts `u(c) * t`. -/
theorem unip_mul_involution_facts {F : Type*} [Field F] [CharP F 2]
    {c : F} (hc : c ≠ 0) {t : Work.Models.SL2 F} (ht : orderOf t = 2)
    (htB : t ∉ Work.Models.PSL2.B (F := F)) :
    ((Work.Models.PSL2.unip c * t : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 ∧
    ((Work.Models.PSL2.unip c * t : Work.Models.SL2 F) :
        Matrix (Fin 2) (Fin 2) F).trace ≠ 0 ∧
    Work.Models.PSL2.unip c * (Work.Models.PSL2.unip c * t) *
        (Work.Models.PSL2.unip c)⁻¹ = (Work.Models.PSL2.unip c * t)⁻¹ := by
  have ht10 : (t : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := Work.Models.PSL2.t_mat_10_ne htB
  have hd : (t : Matrix (Fin 2) (Fin 2) F) 1 1 = (t : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    Work.Models.PSL2.t_mat_11_eq_00 ht htB
  have hcoe : ((Work.Models.PSL2.unip c * t : Work.Models.SL2 F) : Matrix (Fin 2) (Fin 2) F)
      = (Work.Models.PSL2.unip c : Matrix (Fin 2) (Fin 2) F)
        * (t : Matrix (Fin 2) (Fin 2) F) := Matrix.SpecialLinearGroup.coe_mul _ _
  have hunip : (Work.Models.PSL2.unip c : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] :=
    Work.Models.PSL2.unip_coe c
  have h01 : ((Work.Models.PSL2.unip c * t : Work.Models.SL2 F) :
      Matrix (Fin 2) (Fin 2) F) 1 0 = (t : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    rw [hcoe, hunip]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have htr : ((Work.Models.PSL2.unip c * t : Work.Models.SL2 F) :
      Matrix (Fin 2) (Fin 2) F).trace = c * (t : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    rw [hcoe, hunip, Matrix.trace_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.isValue,
      zero_mul, one_mul, add_zero, zero_add]
    rw [hd, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  refine ⟨by rw [h01]; exact ht10, by rw [htr]; exact mul_ne_zero hc ht10, ?_⟩
  have h1 : (Work.Models.PSL2.unip c)⁻¹ = Work.Models.PSL2.unip c :=
    inv_eq_of_mul_eq_one_right (Work.Models.PSL2.unip_mul_self c)
  have h2 : Work.Models.PSL2.unip c * (Work.Models.PSL2.unip c * t) * Work.Models.PSL2.unip c
      = t * Work.Models.PSL2.unip c := by
    rw [← mul_assoc, Work.Models.PSL2.unip_mul_self, one_mul]
  rw [h1, h2, _root_.mul_inv_rev, Work.Models.PSL2.inv_eq_self_of_orderOf_two ht, h1]

/-- **The three clauses for the standard Borel of `SL(2,2ⁿ)`.**

(1°) a `2`-element of `B` lies in the unipotent radical `U` (`sl2_mem_U_of_orderOf_eq_two_pow`),
and every element of `U` squares to `1` (`unip_mul_self`), so `x ^ 4 = 1`;
(2°) the involutions of `B` are the non-trivial elements of `U` (`involutions_B`), so
`u = u(c)` with `c ≠ 0`; for `x = u(c) * t` (`t` an involution outside `B`) the trace of `x` is
non-zero (`unip_mul_involution_facts`), so its centraliser is cyclic of order `≥ |F| - 1`
(`sl2_centralizer_isCyclic_of_trace_ne_zero`), and `u(c)` inverts it
(`bf2_sl2_conj_eq_inv_of_mem_centralizer`); the number of involutions of `B` is `|F| - 1`
(`ncard_involutions_B`), so `127 ≤ |Inv B|` gives `|F| ≥ 128` and the centraliser has at least
`6` elements. -/
theorem benderFacts2For_sl2_B (n : ℕ) :
    BenderFacts2For (Work.Models.SL2 (GaloisField 2 n))
      (Work.Models.PSL2.B (F := GaloisField 2 n)) := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  refine ⟨?_, ?_⟩
  · intro x hxB hpow
    have hxU : x ∈ Work.Models.PSL2.U (F := GaloisField 2 n) :=
      sl2_mem_U_of_orderOf_eq_two_pow hxB hpow
    obtain ⟨b, rfl⟩ := Work.Models.PSL2.mem_U_iff.mp hxU
    have h2 : Work.Models.PSL2.unip b ^ 2 = 1 := by
      rw [pow_two]; exact Work.Models.PSL2.unip_mul_self b
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]
  · intro u hu t ht htH
    rw [Work.Models.PSL2.involutions_B] at hu
    simp only [Set.mem_setOf_eq] at hu
    obtain ⟨huU, hu1⟩ := hu
    obtain ⟨c, rfl⟩ := Work.Models.PSL2.mem_U_iff.mp huU
    have hc : c ≠ 0 := fun hc0 =>
      hu1 (by rw [hc0, Work.Models.PSL2.unip_zero])
    obtain ⟨hx10, htr, hconj⟩ := unip_mul_involution_facts hc ht htH
    obtain ⟨hcyc, hcard⟩ := sl2_centralizer_isCyclic_of_trace_ne_zero htr
    refine ⟨hcyc, fun y hy => bf2_sl2_conj_eq_inv_of_mem_centralizer (y := y) hx10 hconj hy,
      fun h127 => ?_⟩
    have h128 : 127 ≤ Nat.card (GaloisField 2 n) - 1 := by
      simpa [Work.Models.PSL2.ncard_involutions_B] using h127
    omega

/-- **The three clauses for an arbitrary strongly embedded subgroup of `SL(2,2ⁿ)`**: such a
subgroup is a conjugate of the standard Borel (`stronglyEmbedded_eq_conj_B`), and the clauses
transport along the conjugating isomorphism (`benderFacts2For_map_mulEquiv`). -/
theorem benderFacts2For_sl2 (n : ℕ) :
    ∀ H : Subgroup (Work.Models.SL2 (GaloisField 2 n)),
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded H → BenderFacts2For _ H := by
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  intro H hH
  obtain ⟨g, hg⟩ := Work.Models.PSL2.stronglyEmbedded_eq_conj_B (F := GaloisField 2 n) H hH
  rw [hg]
  exact (benderFacts2For_map_mulEquiv (MulAut.conj g)
    (Work.Models.PSL2.B (F := GaloisField 2 n))).mpr (benderFacts2For_sl2_B n)

end Work.BSLit.BenderFacts2
