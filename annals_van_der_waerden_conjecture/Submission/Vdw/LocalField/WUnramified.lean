import Mathlib
import Submission.Vdw.LocalField.OWBasic
import Submission.Vdw.LocalField.TeichMinpoly
import Submission.Vdw.LocalField.TowerDegree

open Classical
open scoped NumberField Polynomial WithZero
open Finset

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3, (b2)): the ORDER-level mod-p independence core

This module proves the algebraic keystone of the unramifiedness
`e(W) = 1` (`𝔪_W = (p)·𝒪_W`, Roadmap Session-89/90): the reduction and
p-divisibility of elements of the Teichmüller order `ℤ_p[ζ] ⊆ 𝒪_W`.

Setup: `ζ := teich p P α` (a Teichmüller lift of `α ≠ 0`, a generator of
`κ^×` — `hgen : orderOf (mk0 α) = p^f − 1`, `f := P.inertiaDeg ℤ`).  For a
coefficient tuple `d : Fin f → QpInt p` the order element is

    u := orderSum p P α d = Σ_{i<f} (d_i : kpInt) · ζ^i ∈ kpInt.

The theorems:

* `mk_orderSum` — the reduction formula: `mk u = Σ_i (d̄_i : κ) · α^i`, where
  `d̄_i` is the mod-p reduction of `d_i` (`qpReductionHom : QpInt → ZMod p`,
  embedded into `κ` through the prime field).  (Composition of the quotient
  ring hom with `Polynomial.eval₂`-style arithmetic: `map_sum`/`map_mul`/
  `map_pow` on `mk`, `mk_teich`, and the coefficient triangle
  `qpReduction_eq_algebraMap_qpReductionHom`.)
* `orderSum_coeffs_of_mk_zero` — THE mod-p independence corollary:
  `mk u = 0 ⟹ ∀ i, d̄_i = 0`, from the keystone
  `kap_generator_powers_linearIndependent` (`α^0,…,α^{f−1}` independent over
  `𝔽_p`, via `Fintype.linearIndependent_iff` + `Algebra.smul_def`).
* `orderSum_norm_eq_one_of_unitCoeff` — if some `d̄_i ≠ 0` (a unit
  coefficient), then `u ∉ 𝔪` (reduction nonzero) and `‖u‖ = 1`
  (`eq_of_le_of_not_lt` with `norm_le_one` and
  `mem_maximalIdeal_iff_norm_lt_one`).
* `orderSum_p_dvd_of_mk_zero` — order-level p-divisibility: `mk u = 0 ⟹
  u = p · v` with `v` an order element (coefficientwise: `d̄_i = 0` gives
  `d_i ∈ mR = (p)` via `qpReduction_eq_zero_iff` +
  `qpIntMaximalIdeal_eq_span_p`, `Ideal.mem_span_singleton`, then
  distributivity of the `(p : kpInt)` scalar).

These are the `ℤ_p[ζ]`-level statements feeding the general argument of
`OW_ker ≤ Ideal.span {pOW}` (`e(W)=1`): with the `ℚ_p`-basis
`{1,…,ζ^{f−1}}` of `W` (PowerBasis from `teich_minpoly_natDegree_eq_inertiaDeg`),
an element `w ∈ 𝒪_W` is `Σ c_i ζ^i` (`c_i ∈ QpAdic`); integrality of `w`
forces each `c_i ∈ QpInt` (scale by a maximal-norm coefficient, use
`orderSum_norm_eq_one_of_unitCoeff`), and `resOW w = 0` then forces each
`c_i ∈ p·QpInt` (`orderSum_p_dvd_of_mk_zero`), giving `w = p·w'` — recorded
as the next session's target (the PowerBasis/scaling bookkeeping).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The Teichmüller-order element with coefficient tuple `d : Fin f → QpInt`:
`u := Σ_{i<f} d_i · ζ^i ∈ kpInt` (the `ℤ_p[ζ]`-order element whose reduction
will be `Σ d̄_i α^i`). -/
def orderSum (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (d : Fin (P.inertiaDeg ℤ) → QpInt p) : kpInt p P :=
  ∑ i : Fin (P.inertiaDeg ℤ),
    (algebraMap (QpInt p) (kpInt p P) (d i)) * (teich p P α ^ (i : ℕ))

/-- **Reduction of an order element**: `mk u = Σ_i (d̄_i : κ) · α^i` where
`d̄_i` is the mod-p reduction of `d_i` (through `qpReductionHom` into `ZMod p`
and the prime-field embedding). -/
theorem mk_orderSum (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (d : Fin (P.inertiaDeg ℤ) → QpInt p) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (orderSum p P α d)
      = ∑ i : Fin (P.inertiaDeg ℤ),
          (algebraMap (ZMod p) (kap p P) (qpReductionHom p (d i))) * (α ^ (i : ℕ)) := by
  classical
  let mkS : kpInt p P →+* kap p P :=
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
  let ζz : kpInt p P := teich p P α
  change mkS (∑ i : Fin (P.inertiaDeg ℤ),
      (algebraMap (QpInt p) (kpInt p P) (d i)) * (ζz ^ (i : ℕ)))
      = ∑ i : Fin (P.inertiaDeg ℤ),
          (algebraMap (ZMod p) (kap p P) (qpReductionHom p (d i))) * (α ^ (i : ℕ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hred : mkS ((algebraMap (QpInt p) (kpInt p P) (d i)) * (ζz ^ (i : ℕ)))
      = (qpReduction p P (d i)) * (α ^ (i : ℕ)) := by
    calc
      mkS ((algebraMap (QpInt p) (kpInt p P) (d i)) * (ζz ^ (i : ℕ)))
          = mkS (algebraMap (QpInt p) (kpInt p P) (d i)) * mkS (ζz ^ (i : ℕ)) := by
            rw [map_mul]
      _ = (qpReduction p P (d i)) * (mkS ζz) ^ (i : ℕ) := by
            rw [map_pow]
            rfl
      _ = (qpReduction p P (d i)) * (α ^ (i : ℕ)) := by
            rw [mk_teich]
  calc
    mkS ((algebraMap (QpInt p) (kpInt p P) (d i)) * (ζz ^ (i : ℕ)))
        = (qpReduction p P (d i)) * (α ^ (i : ℕ)) := hred
    _ = (algebraMap (ZMod p) (kap p P) (qpReductionHom p (d i))) * (α ^ (i : ℕ)) := by
          rw [qpReduction_eq_algebraMap_qpReductionHom]

/-- **The mod-p independence corollary**: if the reduction of an order element
vanishes, then every coefficient reduces to 0 modulo p: `mk u = 0 ⟹ ∀ i, d̄ i = 0`
(keystone: the residues `α^i` are independent over `𝔽_p`,
`kap_generator_powers_linearIndependent`). -/
theorem orderSum_coeffs_of_mk_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (d : Fin (P.inertiaDeg ℤ) → QpInt p)
    (h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
        (orderSum p P α d) = 0) :
    ∀ i : Fin (P.inertiaDeg ℤ), qpReductionHom p (d i) = 0 := by
  classical
  have hred := mk_orderSum (p := p) (P := P) (α := α) d
  have hsum0 : (∑ i : Fin (P.inertiaDeg ℤ),
      (algebraMap (ZMod p) (kap p P) (qpReductionHom p (d i))) * (α ^ (i : ℕ))) = 0 := by
    rw [← hred]
    exact h0
  have hsmul : (∑ i : Fin (P.inertiaDeg ℤ),
      (qpReductionHom p (d i)) • (α ^ (i : ℕ))) = 0 := by
    rw [← hsum0]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Algebra.smul_def]
  have hli := Fintype.linearIndependent_iff.mp
    (kap_generator_powers_linearIndependent (p := p) (P := P) (α := α) hα hgen)
    (fun i : Fin (P.inertiaDeg ℤ) => qpReductionHom p (d i)) hsmul
  exact hli

/-- **Order elements with a unit coefficient have norm 1**: for `u ∈ ℤ_p[ζ]`
whose coefficient tuple has at least one entry not divisible by `p`, the
reduction `mk u` is nonzero, so `u ∉ 𝔪` and `‖u‖ = 1`. -/
theorem orderSum_norm_eq_one_of_unitCoeff (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (d : Fin (P.inertiaDeg ℤ) → QpInt p)
    (h : ∃ i : Fin (P.inertiaDeg ℤ), qpReductionHom p (d i) ≠ 0) :
    ‖(orderSum p P α d : kpAdic p P)‖ = 1 := by
  classical
  let u : kpInt p P := orderSum p P α d
  have hle : ‖(u : kpAdic p P)‖ ≤ 1 := norm_le_one p P u
  have hnot : ¬ ‖(u : kpAdic p P)‖ < 1 := by
    intro hlt
    have hmem : u ∈ IsLocalRing.maximalIdeal (kpInt p P) :=
      (mem_maximalIdeal_iff_norm_lt_one p P u).mpr hlt
    have hmk0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) u = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I := IsLocalRing.maximalIdeal (kpInt p P))).mpr hmem
    have hall := orderSum_coeffs_of_mk_zero (p := p) (P := P) (α := α) hα hgen d hmk0
    rcases h with ⟨i, hi⟩
    exact hi (hall i)
  have heq : ‖(u : kpAdic p P)‖ = 1 := by
    exact eq_of_le_of_not_lt hle hnot
  simpa [u] using heq


/-- **Order-level p-divisibility**: if the reduction of an order element
`u = Σ d_i ζ^i` vanishes mod `𝔪`, then `u` is divisible by `p` in the order:
`∃ e, u = p · Σ e_i ζ^i`.  (Each coefficient `d_i` has zero mod-p reduction,
hence lies in the maximal ideal `(p)` of `QpInt p`, `qpIntMaximalIdeal_eq_span_p`.) -/
theorem orderSum_p_dvd_of_mk_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (d : Fin (P.inertiaDeg ℤ) → QpInt p)
    (h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
        (orderSum p P α d) = 0) :
    ∃ e : Fin (P.inertiaDeg ℤ) → QpInt p,
      orderSum p P α d = (p : kpInt p P) * orderSum p P α e := by
  classical
  have hall := orderSum_coeffs_of_mk_zero (p := p) (P := P) (α := α) hα hgen d h0
  have hdiv : ∀ i : Fin (P.inertiaDeg ℤ), ∃ c : QpInt p, d i = (p : QpInt p) * c := by
    intro i
    have hqi : qpReduction p P (d i) = 0 := by
      rw [qpReduction_eq_algebraMap_qpReductionHom]
      rw [hall i]
      simp
    have hmem : d i ∈ IsLocalRing.maximalIdeal (QpInt p) :=
      (qpReduction_eq_zero_iff p P (d i)).mp hqi
    have hsp : d i ∈ Ideal.span ({(p : QpInt p)} : Set (QpInt p)) := by
      rw [qpIntMaximalIdeal_eq_span_p p] at hmem
      exact hmem
    exact (Ideal.mem_span_singleton.mp hsp)
  let e : Fin (P.inertiaDeg ℤ) → QpInt p := fun i => Classical.choose (hdiv i)
  have hspec : ∀ i, d i = (p : QpInt p) * e i := by
    intro i
    exact Classical.choose_spec (hdiv i)
  refine ⟨e, ?_⟩
  calc
    orderSum p P α d
        = ∑ i : Fin (P.inertiaDeg ℤ),
            (algebraMap (QpInt p) (kpInt p P) (d i)) * (teich p P α ^ (i : ℕ)) := rfl
    _ = ∑ i : Fin (P.inertiaDeg ℤ),
            (algebraMap (QpInt p) (kpInt p P) ((p : QpInt p) * e i)) *
              (teich p P α ^ (i : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hspec i]
    _ = ∑ i : Fin (P.inertiaDeg ℤ),
            ((p : kpInt p P) * (algebraMap (QpInt p) (kpInt p P) (e i))) *
              (teich p P α ^ (i : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          rw [map_mul, map_natCast]
    _ = (p : kpInt p P) * orderSum p P α e := by
          rw [orderSum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring

end
end Submission.Vdw.LocalField
