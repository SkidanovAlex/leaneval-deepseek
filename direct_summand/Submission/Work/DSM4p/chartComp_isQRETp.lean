import Mathlib
import Submission.Work.DSM4p.Completion
import Submission.Work.DSM4p.Reduction
import Submission.Work.DSM4p.Assembly
import Submission.Work.DSM4p.chartComp_modPow
import Submission.Work.DSM4p.chartComp_exists_tr
import Submission.Work.DSM4p.iterTr_chartComp_of

/-!
# DSM4p — the pro-uniform QRET condition for the tower of completed chart levels

The frozen node `DSMap.Mix2.area_M4p` asks for a tower `D 0 ← D 1 ← ⋯` of perfectoid
`B`-algebras with `D n = B⟨ϖ_0^{pn}/g⟩` carrying the pro-uniform almost-pro-isomorphism
condition `DSMap.Mix2.IsQRETp`.  The levels are the `p`-adic completions
`Work.DSM4p.chartComp hgr Q n` of Bhatt's chart levels
`Work.DSM4p.chartRing hgr Q.ϖ n ⊆ B[1/g]` (`DSM4p/Completion.lean`), and the transitions are
the maps of completions induced by the inclusions `chartTr` of the chart levels
(`Work.DSM4p.chartComp_exists_tr`).

This module proves `Work.DSM4p.chartComp_isQRETp`: **if the kernel clause of the chart tower
holds at every level** (`Work.DSM4p.ChartKernel`, the only input of the chart model that is not
established in this area — Bhatt's Theorem 3.1(1) together with the base change of
arXiv:1608.08882, Remark 3.2), then the completed tower satisfies `IsQRETp` with the uniform
constant `c = retC p k m = p^(k+1)·m`.

## The argument

Both clauses of `IsQRETAt` are transported from the chart tower to the completed tower along
the comparison "completion modulo `p^m` = chart level modulo `p^m`"
(`Work.DSM4p.ker_evalₐ_eq_pow`, `Work.DSM4p.chartComp_modPow`), and along the compatibility
`tr n ∘ of = of ∘ chartTr n` of the transitions (`Work.DSM4p.chartComp_exists_tr`), iterated in
`Work.DSM4p.iterTr_chartComp_of`:

* *kernel clause*: if `x ∈ B` dies modulo `p^m` in the completion `chartComp hgr Q (n+c)`, then
  applying `AdicCompletion.evalₐ` (whose kernel is exactly `p^m`) shows that `x` dies modulo
  `p^m` already in the chart level `chartRing hgr Q.ϖ (n+c)`, so the chart kernel clause
  (`Work.DSM4p.ChartKernel`) gives `ϖ_k g_k x ∈ p^m B`;
* *cokernel clause*: an element `y` of the completion `chartComp hgr Q (n+c)` is congruent
  modulo `p^m` to some `y₀` coming from the chart level (`Work.DSM4p.chartComp_exists_of_sub`),
  the difference `y - y₀` is killed by the transition modulo `p^m`, and the chart cokernel
  clause (`Work.DSM4p.chartCokernel`) supplies the element of `B` for `y₀`.

## Contents

* `chartComp_of_eq_algebraMap`, `chartComp_of_add/mul/sub/natCast/pow` — the canonical map
  `chartRing → chartComp` is the structure map, hence multiplicative (`AdicCompletion.of` is
  only recorded as a linear map in Mathlib);
* `chartComp_of_mem_pow` — `p^m`-divisibility is carried to the completion;
* `chartComp_map_mem_pow` — a `B`-algebra map of completed levels preserves `p^m`-divisibility;
* `chartComp_mem_pow_of_of_mem_pow` — `p^m`-divisibility of the image in the completion implies
  `p^m`-divisibility at the chart level;
* `chartComp_exists_of_sub` — every element of a completed level is congruent modulo `p^m` to
  an element of the chart level;
* `chartComp_isQRETp` — the statement.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

section Helpers

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] {gr : ℕ → B}

/-- The canonical map from a chart level to its `p`-adic completion is the structure map
(`AdicCompletion.algebraMap_apply`, which is `rfl`). -/
theorem chartComp_of_eq_algebraMap (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    (n : ℕ) (x : chartRing hgr Q.ϖ n) :
    AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) x
      = algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) x := rfl

/-- The canonical map to the completion is additive. -/
theorem chartComp_of_add (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    (n : ℕ) (a b : chartRing hgr Q.ϖ n) :
    AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) (a + b)
      = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) a
        + AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) b := by
  change algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) (a + b)
      = algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) a
        + algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) b
  exact map_add _ a b

/-- The canonical map to the completion is multiplicative. -/
theorem chartComp_of_mul (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    (n : ℕ) (a b : chartRing hgr Q.ϖ n) :
    AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) (a * b)
      = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) a
        * AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) b := by
  change algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) (a * b)
      = algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) a
        * algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) b
  exact map_mul _ a b

/-- The canonical map to the completion is compatible with subtraction. -/
theorem chartComp_of_sub (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    (n : ℕ) (a b : chartRing hgr Q.ϖ n) :
    AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) (a - b)
      = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) a
        - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) b := by
  change algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) (a - b)
      = algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) a
        - algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) b
  exact map_sub _ a b

/-- The canonical map to the completion is compatible with the natural numbers. -/
theorem chartComp_of_natCast (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    (n : ℕ) (k : ℕ) :
    AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n)
        (k : chartRing hgr Q.ϖ n)
      = (k : chartComp hgr Q n) := by
  change algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) (k : chartRing hgr Q.ϖ n)
      = algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) k
  exact map_natCast _ k

/-- The canonical map to the completion is compatible with powers. -/
theorem chartComp_of_pow (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    (n : ℕ) (a : chartRing hgr Q.ϖ n) (k : ℕ) :
    AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) (a ^ k)
      = (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) a) ^ k := by
  change algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) (a ^ k)
      = (algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n) a) ^ k
  exact map_pow _ a k

/-- `p^m`-divisibility of an element of a chart level is carried to its completion. -/
theorem chartComp_of_mem_pow (hgr : IsRootSystem p gr) (Q : PerfectoidData p B) {n m : ℕ}
    {t : chartRing hgr Q.ϖ n}
    (ht : t ∈ Ideal.span {((p : chartRing hgr Q.ϖ n))^m}) :
    AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) t
      ∈ Ideal.span {((p : chartComp hgr Q n))^m} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp ht
  rw [← hz, chartComp_of_eq_algebraMap hgr Q]
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- A `B`-algebra homomorphism between completed chart levels carries `p^m`-divisible elements
to `p^m`-divisible elements. -/
theorem chartComp_map_mem_pow (hgr : IsRootSystem p gr) (Q : PerfectoidData p B) {n n' m : ℕ}
    (ρ : chartComp hgr Q n →ₐ[B] chartComp hgr Q n') {w : chartComp hgr Q n}
    (hw : w ∈ Ideal.span {((p : chartComp hgr Q n))^m}) :
    ρ w ∈ Ideal.span {((p : chartComp hgr Q n'))^m} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hw
  rw [← hz, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- If the image of an element of a chart level in the completion is divisible by `p^m`, then
the element itself is divisible by `p^m`: the reduction modulo `p^m` of the completion is the
reduction modulo `p^m` of the chart level. -/
theorem chartComp_mem_pow_of_of_mem_pow (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    {n m : ℕ} {t : chartRing hgr Q.ϖ n}
    (h : AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) t
      ∈ Ideal.span {((p : chartComp hgr Q n))^m}) :
    t ∈ Ideal.span {((p : chartRing hgr Q.ϖ n))^m} := by
  have hker : RingHom.ker (AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m).toRingHom
      = Ideal.span {((p : chartComp hgr Q n))^m} := by
    rw [ker_evalₐ_eq_pow _ _ (Submodule.fg_span_singleton _) m, Ideal.map_span,
      Set.image_singleton, ← map_natCast (algebraMap (chartRing hgr Q.ϖ n) (chartComp hgr Q n)) p,
      Ideal.span_singleton_pow]
  have hmem : AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) t
      ∈ RingHom.ker (AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m).toRingHom := by
    rw [hker]
    exact h
  have h0 : AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m
      (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) t) = 0 :=
    RingHom.mem_ker.mp hmem
  rw [AdicCompletion.evalₐ_of] at h0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow] at h0
  exact h0

/-- Every element of a completed chart level is congruent modulo `p^m` to an element of the
chart level: the comparison `chartComp hgr Q n ⧸ p^m ≃ chartRing hgr Q.ϖ n ⧸ p^m` is
surjective. -/
theorem chartComp_exists_of_sub (hgr : IsRootSystem p gr) (Q : PerfectoidData p B)
    (n m : ℕ) (y : chartComp hgr Q n) :
    ∃ y₀ : chartRing hgr Q.ϖ n,
      y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) y₀
        ∈ Ideal.span {((p : chartComp hgr Q n))^m} := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m y)
  refine ⟨a, ?_⟩
  have hzero : AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m
      (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) a) = 0 := by
    rw [map_sub, AdicCompletion.evalₐ_of, ← ha, sub_self]
  have hmem : y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n) a
      ∈ RingHom.ker (AdicCompletion.evalₐ (Ideal.span {(p : chartRing hgr Q.ϖ n)}) m).toRingHom := by
    simpa using hzero
  have hker := ker_evalₐ_eq_pow (chartRing hgr Q.ϖ n) (Ideal.span {(p : chartRing hgr Q.ϖ n)})
    (Submodule.fg_span_singleton _) m
  have hmap : Ideal.map (algebraMap (chartRing hgr Q.ϖ n)
        (AdicCompletion (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n)))
        (Ideal.span {(p : chartRing hgr Q.ϖ n)})
      = Ideal.span {(p : AdicCompletion (Ideal.span {(p : chartRing hgr Q.ϖ n)})
          (chartRing hgr Q.ϖ n))} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [hker, hmap, Ideal.span_singleton_pow] at hmem
  exact hmem

end Helpers

theorem chartComp_isQRETp {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] {gr : ℕ → B}
    (hgr : Work.DSM4p.IsRootSystem p gr) (Q : DSMap.PerfectoidData p B)
    (hk : ∀ m k, Work.DSM4p.ChartKernel Q gr hgr m k) :
    ∃ tr : ∀ n, Work.DSM4p.chartComp hgr Q (n + 1) →ₐ[B] Work.DSM4p.chartComp hgr Q n,
      DSMap.Mix2.IsQRETp p B Q.ϖ gr (fun n => Work.DSM4p.chartComp hgr Q n) tr := by
  obtain ⟨tr, htr⟩ := chartComp_exists_tr hgr Q
  refine ⟨tr, ?_⟩
  rw [isQRETp_iff_isQRETAt]
  intro m k
  refine ⟨retC p k m, ?_, ?_⟩
  · -- kernel clause: reduce modulo `p^m` to the chart level and apply the chart kernel clause
    intro n x hx
    rw [AdicCompletion.algebraMap_apply] at hx
    exact hk m k n x (chartComp_mem_pow_of_of_mem_pow hgr Q hx)
  · -- cokernel clause
    intro n y
    -- an element of the chart level representing `y` modulo `p^m`
    obtain ⟨y₀, hy₀⟩ := chartComp_exists_of_sub hgr Q (n + retC p k m) m y
    -- the chart cokernel clause at `y₀`
    obtain ⟨x, hx⟩ := chartCokernel Q gr hgr m k n y₀
    refine ⟨x, ?_⟩
    -- the part of `y` killed by the transition
    have hW : iterTr tr n (retC p k m)
        (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
          (chartRing hgr Q.ϖ (n + retC p k m)) y₀)
        ∈ Ideal.span {((p : chartComp hgr Q n))^m} :=
      chartComp_map_mem_pow hgr Q (iterTr tr n (retC p k m)) hy₀
    have hB : algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) * iterTr tr n (retC p k m)
        (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
          (chartRing hgr Q.ϖ (n + retC p k m)) y₀)
        ∈ Ideal.span {((p : chartComp hgr Q n))^m} := by
      rw [AdicCompletion.algebraMap_apply]
      exact Ideal.mul_mem_left _ _ hW
    -- the transition is compatible with `chartTr` on the chart levels
    have hzC : iterTr tr n (retC p k m)
        (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
          (chartRing hgr Q.ϖ (n + retC p k m)) y₀)
        = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n)
            (iterTr (chartTr hgr Q.ϖ) n (retC p k m) y₀) :=
      iterTr_chartComp_of hgr Q tr htr n (retC p k m) y₀
    have hA2 : algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) * iterTr tr n (retC p k m)
          (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
            (chartRing hgr Q.ϖ (n + retC p k m)) y₀) -
          algebraMap B (chartComp hgr Q n) x
        = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n)
            (algebraMap B (chartRing hgr Q.ϖ n) (Q.ϖ k * gr k) *
                iterTr (chartTr hgr Q.ϖ) n (retC p k m) y₀ -
              algebraMap B (chartRing hgr Q.ϖ n) x) := by
      rw [hzC, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
      rw [← chartComp_of_mul hgr Q, ← chartComp_of_sub hgr Q]
    have key : algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) * iterTr tr n (retC p k m) y -
        algebraMap B (chartComp hgr Q n) x
        = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ n)}) (chartRing hgr Q.ϖ n)
            (algebraMap B (chartRing hgr Q.ϖ n) (Q.ϖ k * gr k) *
                iterTr (chartTr hgr Q.ϖ) n (retC p k m) y₀ -
              algebraMap B (chartRing hgr Q.ϖ n) x)
          + algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) * iterTr tr n (retC p k m)
              (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
                (chartRing hgr Q.ϖ (n + retC p k m)) y₀) := by
      have hydecomp : y = AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
          (chartRing hgr Q.ϖ (n + retC p k m)) y₀ +
            (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
              (chartRing hgr Q.ϖ (n + retC p k m)) y₀) := by abel
      have hItr : iterTr tr n (retC p k m) y
          = iterTr tr n (retC p k m)
              (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
                (chartRing hgr Q.ϖ (n + retC p k m)) y₀) +
            iterTr tr n (retC p k m)
              (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
                (chartRing hgr Q.ϖ (n + retC p k m)) y₀) := by
        conv_lhs => rw [hydecomp]
        rw [map_add]
      calc algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) * iterTr tr n (retC p k m) y -
            algebraMap B (chartComp hgr Q n) x
          = algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) *
              (iterTr tr n (retC p k m)
                  (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
                    (chartRing hgr Q.ϖ (n + retC p k m)) y₀) +
                iterTr tr n (retC p k m)
                  (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
                    (chartRing hgr Q.ϖ (n + retC p k m)) y₀)) -
            algebraMap B (chartComp hgr Q n) x := by rw [hItr]
        _ = (algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) *
                iterTr tr n (retC p k m)
                  (AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
                    (chartRing hgr Q.ϖ (n + retC p k m)) y₀) -
              algebraMap B (chartComp hgr Q n) x) +
            algebraMap B (chartComp hgr Q n) (Q.ϖ k * gr k) * iterTr tr n (retC p k m)
              (y - AdicCompletion.of (Ideal.span {(p : chartRing hgr Q.ϖ (n + retC p k m))})
                (chartRing hgr Q.ϖ (n + retC p k m)) y₀) := by ring
        _ = _ := by rw [hA2]
    rw [key]
    exact Ideal.add_mem _ (chartComp_of_mem_pow hgr Q hx) hB

end Work.DSM4p
