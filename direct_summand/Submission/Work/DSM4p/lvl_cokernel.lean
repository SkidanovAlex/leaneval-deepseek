import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.LvlMisc
import Submission.Work.DSM4p.cokerP_pow
import Submission.Work.DSM4p.lvlP_charP
import Submission.Work.DSM4p.chartLevel_perfect
import Submission.Work.DSM4p.lvlCokerPre
import Submission.Work.DSM4p.lvlCokerMonoAlt
import Submission.Work.DSM4p.lvlCokerDecomp

/-!
# DSM4p — Route U: the cokernel clause of `IsQRETp` for the untilted tower

This module proves `Work.DSM4p.lvl_cokernel`: the cokernel clause of the quantitative Riemann
extension theorem (Bhatt, arXiv:1608.08882, Theorem 3.1(2) together with Remark 3.2) for the
tower of *untilted* levels `D n = lvl Q hgr n` of the Route U transfer.

## The statement

For `B` a commutative ring, `p` prime with `[Fact ¬IsUnit (p : B)]` and
`[IsAdicComplete (Ideal.span {(p : B)}) B]`, `Q : PerfectoidData p B`, `gr` a compatible system
of `p`-power roots with `gr 0 ≠ 0`, and `m k : ℕ`, there is a uniform constant `c` such that for
every `n` and every `y` in the level `n + c` there is `x ∈ B` with

  `ϖ_k g_k · (iterTr tr n c y) ≡ x  mod p^m`  in `lvl Q hgr n`,

where `g_k = gr k`, `ϖ_k = Q.ϖ k`.

## Proof

We take `c = p^(k+1)·m` and prove, by induction on `m' ≤ m`, the statement

  `∀ n y : lvl (n + c), ∃ x : B, ϖ_k g_k · iterTr n c y - algebraMap x ∈ (p^m')`.

* **Induction step.**  Write `y = ∑_{μ ∈ P.support} mk (teich (monoEl …)) + p · y₁`
  (`Work.DSM4p.lvlCokerDecomp`): modulo `p`, every element of the level is a sum of Teichmüller
  lifts of *monomials* of the characteristic-`p` chart level.  Each summand is handled at *full*
  precision `p^(t+1)` by `Work.DSM4p.lvlCokerMono` (Bhatt's two-case monomial computation,
  transferred through `mk ∘ teich`: in the case where the monomial lands in `φ(B♭)` the
  Teichmüller class is literally `algebraMap (♯b)`, and in the other case the factor
  `(ϖ♭0)^{p(t+1)}` becomes `p^{t+1}` times a unit — this is where the exactness of the two-case
  split, and not only the `mod p` Teichmüller additivity, is used).  The remaining summand
  `p · y₁` is reduced to the induction hypothesis at `t`, and the two error terms are added.

* **Base case** `m' = 0` is trivial.

The reconciliation of the two error terms is additive: the sum of elements congruent to `image B`
modulo `p^(t+1)` is again congruent modulo `p^(t+1)`, and `p · (image B + p^t) ⊆ image B + p^(t+1)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open DSMap DSMap.Mix DSMap.Mix2

namespace Work.DSM4p

universe a

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
variable [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]

/-- The elementary membership step used to collect the error terms: if `z ∈ (p^t)` then
`p · z ∈ (p^(t+1))`. -/
theorem mul_mem_span_pow_succ {R : Type*} [CommRing R] {p : ℕ} (t : ℕ) {z : R}
    (hz : z ∈ Ideal.span {(p : R) ^ t}) : (p : R) * z ∈ Ideal.span {(p : R) ^ (t + 1)} := by
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.mp hz
  exact Ideal.mem_span_singleton.mpr ⟨w, by rw [pow_succ]; ring⟩

theorem lvl_cokernel {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (m k : ℕ) :
    ∃ c : ℕ, ∀ n (y : Work.DSM4p.lvl Q hgr (n + c)), ∃ x : B,
      algebraMap B (Work.DSM4p.lvl Q hgr n) (Q.ϖ k * gr k) *
          DSMap.Mix.iterTr (Work.DSM4p.lvlTrAlg Q hgr) n c y -
        algebraMap B (Work.DSM4p.lvl Q hgr n) x ∈
          Ideal.span {((p : Work.DSM4p.lvl Q hgr n)) ^ m} := by
  refine ⟨p ^ (k + 1) * m, ?_⟩
  intro n y
  have aux : ∀ m' ≤ m, ∀ n (y : Work.DSM4p.lvl Q hgr (n + p ^ (k + 1) * m)), ∃ x : B,
      algebraMap B (Work.DSM4p.lvl Q hgr n) (Q.ϖ k * gr k) *
          iterTr (lvlTrAlg Q hgr) n (p ^ (k + 1) * m) y -
        algebraMap B (Work.DSM4p.lvl Q hgr n) x ∈
          Ideal.span {((p : Work.DSM4p.lvl Q hgr n)) ^ m'} := by
    intro m'
    induction m' with
    | zero =>
      intro _ n y
      refine ⟨0, ?_⟩
      rw [pow_zero, map_zero, sub_zero]
      exact Ideal.mem_span_singleton.mpr (one_dvd _)
    | succ t ih =>
      intro ht n y
      obtain ⟨P, y₁, hy⟩ := lvlCokerDecomp (p := p) Q hgr hgr0
        (n + p ^ (k + 1) * m) y
      have hmono : ∀ μ : ℕ →₀ ℕ, ∃ x : B,
          algebraMap B (lvl Q hgr n) (Q.ϖ k * gr k) *
              iterTr (lvlTrAlg Q hgr) n (p ^ (k + 1) * m)
                (DSM5c.untiltOf.mk (algebraMap (PreTilt B p)
                    (lvlP Q hgr (n + p ^ (k + 1) * m)))
                  (WittVector.teichmuller p (monoEl Q hgr (n + p ^ (k + 1) * m)
                    (P.coeff μ) (μ.support.sup id)
                    (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j))))) -
            algebraMap B (lvl Q hgr n) x ∈
              Ideal.span {((p : lvl Q hgr n)) ^ (t + 1)} := fun μ =>
        lvlCokerMonoAlt (p := p) Q hgr k (t + 1) (p ^ (k + 1) * m) n
          (Nat.mul_le_mul_left _ ht) (P.coeff μ) (μ.support.sup id)
          (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j))
      choose xm hxm using hmono
      obtain ⟨x₁, hx₁⟩ := ih (Nat.le_of_succ_le ht) n y₁
      refine ⟨(∑ μ ∈ P.support, xm μ) + p * x₁, ?_⟩
      set A : lvl Q hgr (n + p ^ (k + 1) * m) → lvl Q hgr n := fun w =>
        algebraMap B (lvl Q hgr n) (Q.ϖ k * gr k) *
          iterTr (lvlTrAlg Q hgr) n (p ^ (k + 1) * m) w with hAdef
      have hAadd : ∀ u v, A (u + v) = A u + A v := by
        intro u v; simp only [hAdef, map_add, mul_add]
      have hAsum : A (∑ μ ∈ P.support,
            DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr (n + p ^ (k + 1) * m)))
              (WittVector.teichmuller p (monoEl Q hgr (n + p ^ (k + 1) * m)
                (P.coeff μ) (μ.support.sup id)
                (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j))))) =
          ∑ μ ∈ P.support, A (DSM5c.untiltOf.mk (algebraMap (PreTilt B p)
              (lvlP Q hgr (n + p ^ (k + 1) * m)))
            (WittVector.teichmuller p (monoEl Q hgr (n + p ^ (k + 1) * m)
              (P.coeff μ) (μ.support.sup id)
              (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j))))) := by
        simp only [hAdef, map_sum, Finset.mul_sum]
      have hAp : A ((p : lvl Q hgr (n + p ^ (k + 1) * m)) * y₁) =
          (p : lvl Q hgr n) * A y₁ := by
        simp only [hAdef, map_mul, map_natCast]
        ring
      have hdiff : A y - algebraMap B (lvl Q hgr n) ((∑ μ ∈ P.support, xm μ) + p * x₁) =
          (∑ μ ∈ P.support, (A (DSM5c.untiltOf.mk (algebraMap (PreTilt B p)
              (lvlP Q hgr (n + p ^ (k + 1) * m)))
            (WittVector.teichmuller p (monoEl Q hgr (n + p ^ (k + 1) * m)
              (P.coeff μ) (μ.support.sup id)
              (∑ j ∈ μ.support, μ j * p ^ (μ.support.sup id - j))))) -
            algebraMap B (lvl Q hgr n) (xm μ))) +
          (p : lvl Q hgr n) * (A y₁ - algebraMap B (lvl Q hgr n) x₁) := by
        rw [hy, hAadd, hAsum, hAp, map_add, map_mul, map_natCast, map_sum,
          Finset.sum_sub_distrib]
        ring
      rw [hdiff]
      refine Submodule.add_mem _ (Submodule.sum_mem _ ?_) ?_
      · intro μ _
        exact hxm μ
      · exact mul_mem_span_pow_succ t hx₁
  exact aux m le_rfl n y

end Work.DSM4p
