import Mathlib
import Submission.Work.MotAS.asW0Defs
import Submission.Work.MotAS.ASRulDefs
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Cert` §3 — the certificate against the AS Pfaffians, and independence

The linear functional `psiAS a b` annihilates the five coefficient vectors `cPAS a b g k` up to the
explicit multiple `5` of the characteristic (`cPAS_sum`/`psiAS` are honest integral identities with
the factor `5` written out), while its value on `cB a b g` is
`-2a²b(a²-ab-b²)` modulo the same explicit `5`-multiple.  Since `a² - ab - b² ≠ 0` in the
application, this exhibits `cB` as outside the span of the `cPAS k`, which (together with
`linearIndependent_cPAS` and the dimension count
`Work.MotK.TwRuling.SdWfour.finrank_ker`) identifies the kernel of the pair-multiplication map.

The five vectors `cPAS a b g k` are linearly independent as soon as `2 ≠ 0` and
`a² - ab - b² ≠ 0`: reading the identity `∑ k, c k • cPAS a b g k = 0` at the pairs
`(0,0)`, `(4,1)`, `(3,0)`, `(2,2)`, `(1,0)` makes the coefficient matrix triangular with diagonal
`α, 2α, α, 2α, α`, `α = a² - ab - b²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open Work.MotK.TwRuling.SdWfour

namespace Cert

/-- **The certificate against the AS Pfaffians.** -/
theorem psiAS_cPAS {S : Type*} [CommRing S] (a b g : S) (k : Fin 5) :
    (∑ q : Fin 5 × Fin 3, psiAS a b q * cPAS a b g k q) = 5 * psiASval a b g k := by
  fin_cases k <;>
  · rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_five, Fin.sum_univ_three]
    simp [psiAS, cPAS, cPASmat, psiASval] <;>
    first | refl_ring1 | ring

/-- **The certificate against `cB`**: the value is `-2a²b(a²-ab-b²)` up to the explicit
multiple `5·(2ab(a³+a²b-ab²-2b³))` of the characteristic. -/
theorem psiAS_cB {S : Type*} [CommRing S] (a b g : S) :
    (∑ q : Fin 5 × Fin 3, psiAS a b q * cB a b g q)
      = -2 * a ^ 2 * b * (a ^ 2 - a * b - b ^ 2)
        + 5 * (2 * a * b * (a ^ 3 + a ^ 2 * b - a * b ^ 2 - 2 * b ^ 3)) := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_five, Fin.sum_univ_three]
  simp [psiAS, cB] <;>
  first | refl_ring1 | ring

/-- **The five AS Pfaffian coefficient vectors are linearly independent.** -/
theorem linearIndependent_cPAS {K : Type*} [Field K] (a b g : K)
    (hα : a ^ 2 - a * b - b ^ 2 ≠ 0) (h2 : (2 : K) ≠ 0) :
    LinearIndependent K (cPAS a b g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ q : Fin 5 × Fin 3, (∑ k : Fin 5, c k * cPAS a b g k q) = 0 := by
    intro q
    have h := congrFun hc q
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using h
  have h0 : c 0 = 0 := by
    have h := key ((0 : Fin 5), (0 : Fin 3))
    rw [Fin.sum_univ_five] at h
    simp [cPAS, cPASmat] at h
    exact h.resolve_right hα
  have h1 : c 1 = 0 := by
    have h := key ((4 : Fin 5), (1 : Fin 3))
    rw [Fin.sum_univ_five] at h
    simp [cPAS, cPASmat] at h
    refine h.resolve_right (fun hh => mul_ne_zero h2 hα ?_)
    linear_combination (norm := first | refl_ring1 | ring1) hh
  have h2' : c 2 = 0 := by
    have h := key ((3 : Fin 5), (0 : Fin 3))
    rw [Fin.sum_univ_five] at h
    simp [cPAS, cPASmat, h0] at h
    exact h.resolve_right hα
  have h3 : c 3 = 0 := by
    have h := key ((2 : Fin 5), (2 : Fin 3))
    rw [Fin.sum_univ_five] at h
    simp [cPAS, cPASmat, h1] at h
    refine h.resolve_right (fun hh => mul_ne_zero h2 hα ?_)
    linear_combination (norm := first | refl_ring1 | ring1) hh
  have h4 : c 4 = 0 := by
    have h := key ((1 : Fin 5), (0 : Fin 3))
    rw [Fin.sum_univ_five] at h
    simp [cPAS, cPASmat, h0, h2'] at h
    exact h.resolve_right hα
  intro k
  fin_cases k
  exacts [h0, h1, h2', h3, h4]

end Cert

end Work.MotAS
