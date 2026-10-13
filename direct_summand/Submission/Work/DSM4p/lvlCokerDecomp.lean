import Mathlib
import Submission.Work.DSM4p.lvlCokerPre
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvlP_charP
import Submission.Work.DSM4p.chartLevel_perfect
import Submission.Work.DSM4p.lvl_exists_teich
import Submission.Work.DSM4p.chartRing_poly_expansion
import Submission.Work.DSM4p.teichmuller_sum_sub_mem_span_p

/-!
# `Work.DSM4p.lvlCokerDecomp` — splitting a level class into chart monomials modulo `p`

This module proves the cokernel *decomposition* of the untilted tower `lvl Q hgr N` that the
transfer of Bhatt's cokernel estimate (`Work.DSM4p.lvl_cokernel`) uses: every class
`y : lvl Q hgr N` is congruent modulo `p` to a sum of Teichmüller classes of *monomials* of the
characteristic-`p` chart level `lvlP Q hgr N`, in the collapsed form
`b₀ · x_J(N)^I` with `J = sup (support μ)` and `I = ∑_j μ_j p^{J-j}` (the exponent bookkeeping of
`Work.DSM4p.prod_gen_pow`), the coefficients `b₀` being the coefficients `P.coeff μ` of a
polynomial `P : MvPolynomial ℕ (PreTilt B p)`.

## The argument

* `Work.DSM4p.lvl_exists_teich` (step (2) of the Route U plan) produces `r : lvlP Q hgr N` with
  `y - mk (teichmuller p r) ∈ (p)`, where `mk = DSM5c.untiltOf.mk` is the quotient map defining
  the untilt;
* `Work.DSM4p.chartRing_poly_expansion` writes `r` as a finite polynomial combination
  `∑_μ algebraMap (P.coeff μ) · ∏_j x_j(N)^{μ_j}` of the chart generators `x_j(N) = gen Q hgr N j`
  of the level;
* `Work.DSM4p.teichmuller_sum_sub_mem_span_p` (Teichmüller is additive modulo `p`, because the
  constant-coefficient map `𝕎 R → R` is a ring homomorphism and `ker constantCoeff = (p)` for `R`
  perfect of characteristic `p`) compares `teichmuller (∑_μ X_μ)` with `∑_μ teichmuller (X_μ)`:
  their difference lies in `(p : 𝕎 R)`, and pushing it through `mk` gives a `p`-multiple in the
  level;
* `Work.DSM4p.prod_gen_pow` identifies each monomial `algebraMap (P.coeff μ) · ∏_j x_j(N)^{μ_j}`
  with the collapsed monomial `monoEl Q hgr N (P.coeff μ) (μ.support.sup id) (∑_j …)` of the
  statement.

Hence `y - (sum of the statement) ∈ (p : lvl Q hgr N)`, which is exactly the claimed
decomposition.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.DSM4p

theorem lvlCokerDecomp {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (N : ℕ) (y : Work.DSM4p.lvl Q hgr N) :
    ∃ (P : MvPolynomial ℕ (PreTilt B p)) (y₁ : Work.DSM4p.lvl Q hgr N),
      y = (∑ μ ∈ P.support,
              DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
                (WittVector.teichmuller p (Work.DSM4p.monoEl Q hgr N (P.coeff μ)
                  (μ.support.sup id) (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j)))))
          + (p : Work.DSM4p.lvl Q hgr N) * y₁ := by
  -- The characteristic-`p` chart level of `N` is perfect of characteristic `p` (`gr 0 ≠ 0`
  -- makes it nontrivial), which is what the Teichmüller-mod-`p` comparison needs.
  haveI hchar : CharP (lvlP Q hgr N) p := lvlP_charP Q hgr hgr0 N
  haveI hperf : PerfectRing (lvlP Q hgr N) p :=
    chartLevel_perfect (tiltTower_isRootSystem gr hgr) (tiltTower_isRootSystem Q.ϖ Q.root) N
  -- (PIECE 1) the Teichmüller representative of `y`, modulo `p`
  obtain ⟨r, hr⟩ := lvl_exists_teich Q hgr hgr0 N y
  -- (PIECE 2) `r` is a polynomial in the chart generators of the level `N`
  obtain ⟨P, hP⟩ := chartRing_poly_expansion (tiltTower_isRootSystem gr hgr)
    (tiltTower_isRootSystem Q.ϖ Q.root) N r
  -- The "expanded" monomials `X_μ = P.coeff μ · ∏_j x_j(N)^{μ_j}` of which `r` is the sum.
  -- (Note `gen Q hgr N j` is *definitionally* the subtype element
  -- `⟨chartGen … N j, chartGen_mem … N j⟩` of `lvlP Q hgr N` that `chartRing_poly_expansion`
  -- produces, so `hP` is used below in the form with `gen`.)
  set f : (ℕ →₀ ℕ) → lvlP Q hgr N :=
    fun μ => algebraMap (PreTilt B p) (lvlP Q hgr N) (P.coeff μ) *
      ∏ j ∈ μ.support, (gen Q hgr N j) ^ (μ j) with hf
  have hPf : ∑ μ ∈ P.support, f μ = r := by rw [hf]; exact hP.symm
  -- The sum of the statement, collapsed form.
  set S : lvl Q hgr N := ∑ μ ∈ P.support,
        DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
          (WittVector.teichmuller p (monoEl Q hgr N (P.coeff μ) (μ.support.sup id)
            (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j)))) with hS
  -- The collapsed form is the expanded form (`prod_gen_pow`).
  have hgoal : S = ∑ μ ∈ P.support,
      DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
        (WittVector.teichmuller p (f μ)) := by
    rw [hS]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hf]
    simp only [monoEl]
    rw [prod_gen_pow Q hgr N μ]
  -- The Teichmüller discrepancy is a multiple of `p`, hence so is its image under `mk`
  -- (Teichmüller is additive modulo `p`: `teichmuller_sum_sub_mem_span_p`).
  have hz : WittVector.teichmuller p (∑ μ ∈ P.support, f μ) -
      ∑ μ ∈ P.support, WittVector.teichmuller p (f μ) ∈
      Ideal.span {(p : WittVector p (lvlP Q hgr N))} := teichmuller_sum_sub_mem_span_p P.support f
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  -- `mk (teich r) - S` is such an image.
  have hsecond : DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
      (WittVector.teichmuller p r) - ∑ μ ∈ P.support,
        DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
          (WittVector.teichmuller p (f μ)) ∈ Ideal.span {(p : lvl Q hgr N)} := by
    rw [← hPf, ← map_sum, ← map_sub, hw, map_mul]
    refine Ideal.mem_span_singleton.mpr ⟨DSM5c.untiltOf.mk _ w, ?_⟩
    rw [map_natCast]
  -- Both summands of `y - S` are multiples of `p`.
  have hsmem : y - S ∈ Ideal.span {(p : lvl Q hgr N)} := by
    rw [hgoal]
    have hsplit : y - (∑ μ ∈ P.support,
        DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
          (WittVector.teichmuller p (f μ))) =
        (y - DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
          (WittVector.teichmuller p r)) +
        (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
          (WittVector.teichmuller p r) - ∑ μ ∈ P.support,
            DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
              (WittVector.teichmuller p (f μ))) := by ring
    rw [hsplit]
    exact Ideal.add_mem _ hr hsecond
  obtain ⟨y₁, hy₁⟩ := Ideal.mem_span_singleton.mp hsmem
  refine ⟨P, y₁, ?_⟩
  rw [← hS, ← hy₁]
  ring

end Work.DSM4p
