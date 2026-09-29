import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.acl_a_local
import Submission.Work.C17.clear_denoms_LC
import Submission.Work.C17.DyIter_eq_cls
import Submission.Work.C17.pure_step
import Submission.Work.C17.order3_class_injective
import Submission.Work.C17.y1_periods_indep_gen
import Submission.Work.C17.riccati_no_rational_C
import Submission.Work.C17.adjoint_no_solution_C
import Submission.Work.C17.relation_to_LC

/-!
# Area C17, target lemma `Work.C17.seventeen_indep`

The definitions and the proved helper lemmas live in
`Submission.Work.C17.seventeen_defs` (module `Work.C17.seventeen_defs`), so that the delegated
lemmas below can import them without creating a cycle with this file.

## THE ARCHITECTURE IN FORCE (see `Submission/Work/C17/seventeen_indep.lean`'s git history /
`HANDOFF.md` for the full design)

* `acl_a_local` — the local structure `P = κ·y₁·log(x_s − ·) + hh` at the cusp, with
  `2δ ≤ x_s`, `2δ ≤ 1 − x_s`, for admissible `(a, b) = (2m+1, 2n+1)`.
* `relation_to_LC` — the log-coefficient functional `Λ` applied to the pulled-back relation:
  `Σ_{k<4} p_k(y)·D_y^k y₁ + Σ_{i<6} q_i(y)·J_{σ i} = 0` on the ball.
* `DyIter_eq_cls` + `clear_denoms_LC` — clearing denominators: the relation becomes a
  polynomial-coefficient relation among `y₁, y₁', J_0, …, J_5`, losslessly.
* `y1_periods_indep_gen` (with the `ℂ(x)` inputs `riccati_no_rational_C` and
  `adjoint_no_solution_C`) — the period independence
  `A y₁ + B y₁' + Σ C_i J_i = 0 ⟹ A = B = C = 0`, used through the private wrapper `y1_indep`.
* `order3_class_injective` — the class of `Σ_{k≤3} p_k(y)∂_y^k` modulo `M` is injective.
* `pure_step` — the surviving relation involves only the seven pure functions, so
  `hS : LemmaSeven` kills it.

-/

open Submission.CDTPlan
open Polynomial
open scoped BigOperators

namespace Work.C17

noncomputable section


/-- The period independence (IND), with the statement of `Work.C17.y1_periods_indep`, obtained
through the shared generic result `Work.GenShared.periods_indep_gen` (`Work.C17.y1_periods_indep_gen`)
with the `ℂ(x)` inputs `Work.C17.riccati_no_rational_C` and `Work.C17.adjoint_no_solution_C`.
This wrapper is the single point at which the main assembly consumes (IND), so that the route
(direct `y1_periods_indep` or generic `y1_periods_indep_gen`) can be swapped without touching it. -/
private theorem y1_indep (a b : ℚ) (hA : AdmQ a b)
    (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball (((xs a b : ℝ) : ℂ)) δ))
    (hy1ne : y1 (((xs a b : ℝ) : ℂ)) ≠ 0)
    (hode : ∀ z ∈ Metric.ball (((xs a b : ℝ) : ℂ)) δ,
      (P2x a b).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
        + (P1x a b).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (P0x a b).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0)
    (J : Fin 6 → ℂ → ℂ)
    (hJd : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball (((xs a b : ℝ) : ℂ)) δ))
    (hJ0 : ∀ i, J i (((xs a b : ℝ) : ℂ)) = 0)
    (hJderiv : ∀ i, ∀ z ∈ Metric.ball (((xs a b : ℝ) : ℂ)) δ,
      HasDerivAt (J i) (((yQ ^ ((i : ℤ) - 4) * dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
        / ((yQ ^ ((i : ℤ) - 4) * dyQ).denom.eval₂ (algebraMap ℚ ℂ) z) * y1 z) z)
    (A B : Polynomial ℚ) (C : Fin 6 → Polynomial ℚ)
    (hrel : ∀ z ∈ Metric.ball (((xs a b : ℝ) : ℂ)) δ,
      (A.eval₂ (algebraMap ℚ ℂ) z) * y1 z + (B.eval₂ (algebraMap ℚ ℂ) z) * deriv y1 z
        + ∑ i : Fin 6, ((C i).eval₂ (algebraMap ℚ ℂ) z) * J i z = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 :=
  y1_periods_indep_gen a b hA
    (fun u => riccati_no_rational_C a b hA.1 (le_trans hA.1 hA.2.1.le) (ne_of_lt hA.2.1) u)
    (adjoint_no_solution_C a b hA)
    y1 hδ hy1d hy1ne hode J hJd hJ0 hJderiv A B C hrel

/-- The `m < n` case of `seventeen_indep`: with the admissible pair ordered, the whole
`x`-side argument runs. -/
private theorem seventeen_indep_lt (hS : LemmaSeven) (m n : ℕ) (hm : 1 ≤ m) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n)
    (ra rb rab r0 : ℤ) (hrab : rab ≠ 0) (hrel : CRel m n ra rb rab r0)
    (P : Fin 17 → Polynomial ℚ)
    (hsum : ∑ i : Fin 17, (P i : PowerSeries ℚ) * seventeen m n ra rb rab r0 i = 0) :
    ∀ i, P i = 0 := by
  -- (0) the pair `(2m+1, 2n+1)` is admissible
  have hA : AdmQ (aOf m) (aOf n) := admQ_of_CAdm m n hm hlt hgap
  -- (1) `CRel` in the `beukersEta` normal form
  have hrel' : (ra : ℝ) * Submission.CDT.beukersEta (((aOf m : ℚ)) : ℝ)
      + (rb : ℝ) * Submission.CDT.beukersEta (((aOf n : ℚ)) : ℝ)
      + (rab : ℝ) * (Submission.CDT.beukersEta (((aOf m : ℚ)) : ℝ) *
          Submission.CDT.beukersEta (((aOf n : ℚ)) : ℝ)) = (r0 : ℝ) := by
    simpa only [CRel, aOf_cast] using hrel
  -- (2) the local structure of `P` at the cusp `x_s` (ACL-a)
  obtain ⟨δ, hδpos, hδ1, hδ2, κ, y1, hh, hκ, hy1ne, hy1d, hhd, hode, hloc⟩ :=
    acl_a_local (aOf m) (aOf n) hA ra rb rab r0 hrab hrel'
  -- (3) the same data in the `xsOf` normalisation used by `relation_to_LC`
  have hδ1x : 2 * δ ≤ xsOf m n := by rw [← xsOf_eq_xs]; exact hδ1
  have hδ2x : 2 * δ ≤ 1 - xsOf m n := by rw [← xsOf_eq_xs]; exact hδ2
  have hy1dx : DifferentiableOn ℂ y1 (Metric.ball ((xsOf m n : ℝ) : ℂ) δ) := by
    rw [← xsOf_eq_xs]; exact hy1d
  have hy1nex : y1 ((xsOf m n : ℝ) : ℂ) ≠ 0 := by rw [← xsOf_eq_xs]; exact hy1ne
  have hodex : ∀ z ∈ Metric.ball ((xsOf m n : ℝ) : ℂ) δ,
      (P2x (aOf m) (aOf n)).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y1) z
        + (P1x (aOf m) (aOf n)).eval₂ (algebraMap ℚ ℂ) z * deriv y1 z
        + (P0x (aOf m) (aOf n)).eval₂ (algebraMap ℚ ℂ) z * y1 z = 0 := by
    intro z hz
    exact hode z (by rwa [← xsOf_eq_xs] at hz)
  have hlocx : ∃ hh0 : ℂ → ℂ,
      DifferentiableOn ℂ hh0 (Metric.ball ((xsOf m n : ℝ) : ℂ) δ) ∧
      ∀ z ∈ Metric.ball ((xsOf m n : ℝ) : ℂ) δ ∩ Metric.ball (0 : ℂ) (xsOf m n),
        Pfun (aOf m) (aOf n) ra rb rab r0 z
          = κ * y1 z * Complex.log (((xsOf m n : ℝ) : ℂ) - z) + hh0 z := by
    refine ⟨hh, ?_, ?_⟩
    · rw [← xsOf_eq_xs]; exact hhd
    · intro z hz
      rw [← xsOf_eq_xs] at hz ⊢
      exact hloc z hz
  -- (4) the log-coefficient functional applied to the pulled-back relation
  obtain ⟨J, hJd, hJ0, hJderiv, hLC⟩ :=
    relation_to_LC m n hm (by omega) hlt hgap ra rb rab r0 P hsum y1 hδpos hδ1x hδ2x κ hκ
      hy1dx hy1nex hodex hlocx
  -- (5) back to the `xs` normalisation, for the clearing and the period independence
  have hLCx : ∀ z ∈ Metric.ball ((xs (aOf m) (aOf n) : ℝ) : ℂ) δ,
      (∑ k : Fin 4, pAtY (P ⟨5 + (k : ℕ), by omega⟩) z * DyIter (k : ℕ) y1 z)
        + (∑ i : Fin 6, pAtY (P ⟨11 + (i : ℕ), by omega⟩) z
            * J (jrev i) z) = 0 := by
    intro z hz
    exact hLC z (by rwa [xsOf_eq_xs] at hz)
  have hJd' : ∀ i, DifferentiableOn ℂ (J i) (Metric.ball ((xs (aOf m) (aOf n) : ℝ) : ℂ) δ) := by
    intro i
    rw [xsOf_eq_xs]
    exact hJd i
  have hJ0' : ∀ i, J i (((xs (aOf m) (aOf n) : ℝ) : ℂ)) = 0 := by
    intro i
    rw [xsOf_eq_xs]
    exact hJ0 i
  have hJderiv' : ∀ i, ∀ z ∈ Metric.ball ((xs (aOf m) (aOf n) : ℝ) : ℂ) δ,
      HasDerivAt (J i) (((yQ ^ ((i : ℤ) - 4) * dyQ).num.eval₂ (algebraMap ℚ ℂ) z)
        / ((yQ ^ ((i : ℤ) - 4) * dyQ).denom.eval₂ (algebraMap ℚ ℂ) z) * y1 z) z := by
    intro i z hz
    exact hJderiv i z (by rwa [xsOf_eq_xs] at hz)
  -- (6) the class reduction `D_y^k y₁ = (A_k y₁ + B_k y₁')/D`
  obtain ⟨D, hDne, hDk⟩ := DyIter_eq_cls (aOf m) (aOf n) y1 hδpos hy1d hode
  choose A B hAB using hDk
  -- (7) clearing denominators of the `(LC)` identity
  have hxsC : 0 < xs (aOf m) (aOf n) := by rw [xsOf_eq_xs]; exact xsOf_pos m n hm hlt
  obtain ⟨A0, B0, C, hiden, hA0cls, hB0cls, hCq⟩ :=
    clear_denoms_LC (aOf m) (aOf n) hδpos hxsC hδ2 y1 J D hDne A B hAB
      (fun k => P ⟨5 + (k : ℕ), by omega⟩) (fun i => P ⟨11 + (i : ℕ), by omega⟩) hLCx
  -- (8) period independence: the cleared relation has zero coefficients
  obtain ⟨hA0z, hB0z, hCz⟩ :=
    y1_indep (aOf m) (aOf n) hA y1 hδpos hy1d hy1ne hode J hJd' hJ0' hJderiv'
      A0 B0 C hiden
  -- (9) the class sum vanishes, so the four `G`-coefficients vanish
  have hcls : ((∑ k : Fin 4,
        ((P ⟨5 + (k : ℕ), by omega⟩).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ)
          * (cls (aOf m) (aOf n) k).1),
      (∑ k : Fin 4,
        ((P ⟨5 + (k : ℕ), by omega⟩).eval₂ (algebraMap ℚ (RatFunc ℚ)) yQ)
          * (cls (aOf m) (aOf n) k).2)) = (0, 0) := by
    rw [Prod.mk.injEq]
    exact ⟨hA0cls hA0z, hB0cls hB0z⟩
  have hp : (fun k : Fin 4 => P ⟨5 + (k : ℕ), by omega⟩) = 0 :=
    order3_class_injective (aOf m) (aOf n) hA _ hcls
  have hq : ∀ i : Fin 6, P ⟨11 + (i : ℕ), by omega⟩ = 0 :=
    fun i => hCq i (by simp [hCz])
  -- (10) the seven pure coefficients
  have h5 : P 5 = 0 := by simpa using congrFun hp (0 : Fin 4)
  have h6 : P 6 = 0 := by simpa using congrFun hp (1 : Fin 4)
  have h7 : P 7 = 0 := by simpa using congrFun hp (2 : Fin 4)
  have h8 : P 8 = 0 := by simpa using congrFun hp (3 : Fin 4)
  have h11 : P 11 = 0 := by simpa using hq (0 : Fin 6)
  have h12 : P 12 = 0 := by simpa using hq (1 : Fin 6)
  have h13 : P 13 = 0 := by simpa using hq (2 : Fin 6)
  have h14 : P 14 = 0 := by simpa using hq (3 : Fin 6)
  have h15 : P 15 = 0 := by simpa using hq (4 : Fin 6)
  have h16 : P 16 = 0 := by simpa using hq (5 : Fin 6)
  exact pure_step hS m n ra rb rab r0 P hsum h5 h6 h7 h8 h11 h12 h13 h14 h15 h16

theorem seventeen_indep (hS : LemmaSeven) : Seventeen := by
  intro m n ra rb rab r0 hAdm hRel hrab P hsum
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact seventeen_indep_lt hS m n hAdm.1 hlt hAdm.2.2.2 ra rb rab r0 hrab hRel P hsum
  · exact absurd heq hAdm.2.2.1
  · refine seventeen_indep_lt hS n m hAdm.2.1 hgt ?_ rb ra rab r0 hrab ?_ P ?_
    · have h := hAdm.2.2.2
      have h2 : ((m : ℤ) - n).natAbs = ((n : ℤ) - m).natAbs := by
        rw [show (m : ℤ) - n = -((n : ℤ) - m) by ring, Int.natAbs_neg]
      rw [h2] at h
      exact le_trans h (le_of_lt hgt)
    · have h := hRel
      rw [CRel] at h ⊢
      linear_combination h
    · rw [seventeen_swap n m rb ra rab r0]
      exact hsum

end

end Work.C17
