import Mathlib
import Submission.Work.DSM4p.lvlCokerPre
import Submission.Work.DSM4p.cokerMonoCases

/-!
# DSM4p — the monomial cokernel estimate of the untilted tower

This module proves the per-monomial step of the transfer of Bhatt's cokernel estimate
(Theorem 3.1(2) of arXiv:1608.08882) to the untilted levels `lvl Q hgr n` of the Route U
design: for a *monomial* `M = b₀ · x_J(N)^I` of the characteristic-`p` chart level of
`N = n + c` (a Teichmüller input),

  `ϖ_k g_k · iterTr n c (mk [M]) ≡ x  mod p^m`  in `lvl Q hgr n`,  for some `x ∈ B`,

provided `p^(k+1)·m ≤ c`.

## The transfer

The chart-level estimate (`Work.DSM4p.cokerMonoCases`, the two-case form of
`Work.DSM4p.cokerP_mono_pow`, Bhatt's monomial computation) says that in the ambient localisation
`B♭[1/g♭ 0]`

  `(ϖ♭k g♭k) · M`  is either `= φ(b)` for some `b : B♭`,  or `= φ((ϖ♭0)^(p m)) · s`

for some `s` in the level `n`.  The transfer through `mk ∘ teichmuller` uses two facts:

* `teichmuller` is *multiplicative*, and `mk` is a ring homomorphism, so the transfer is exact
  in both cases (this is why one must use the two-case form and not the sum decomposition:
  `teichmuller` is only additive modulo `p`, so a sum of the two cases would lose a factor `p^m`);
* in the first case `mk [φ b] = algebraMap (♯b)` (`mk_teich_algebraMap`) and in the second case
  `mk [φ((ϖ♭0)^(p m))] = (algebraMap (Q.ϖ 0))^(p m) = p^m · u` for a unit `u`
  (`mk_teich_varpi0_pow`, `varpi0_pow_pow`), which is the perfectoid relation
  `Q.ϖ 0 ^ p = p · v`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open DSMap DSMap.Mix DSMap.Mix2

namespace Work.DSM4p

universe a

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
variable [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]

/-- The `pm`-th power of the tilted pseudo-uniformiser, transported to the untilted level:
`mk [φ ((ϖ♭0)^(p m))] = (algebraMap (Q.ϖ 0))^(p m)`. -/
theorem mk_teich_varpi0_pow (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N m : ℕ) :
    (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N)))
        (WittVector.teichmuller p (algebraMap (PreTilt B p) (lvlP Q hgr N)
          (varpiSharp Q 0 ^ (p * m))))
      = (algebraMap B (lvl Q hgr N) (Q.ϖ 0)) ^ (p * m) := by
  rw [map_pow, map_pow, map_pow, mk_teich_tiltTower Q hgr N Q.root 0]

/-- **The monomial cokernel estimate of the untilted tower**: for the Teichmüller lift of a
monomial `b₀ · x_J(n+c)^I` of the characteristic-`p` chart level, multiplication by `ϖ_k g_k`
followed by the `c`-fold transition is congruent to an element of `B` modulo `p^m`. -/
theorem lvlCokerMonoAlt (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (k m c n : ℕ) (hc : p ^ (k + 1) * m ≤ c) (b0 : PreTilt B p) (J I : ℕ) :
    ∃ x : B,
      algebraMap B (lvl Q hgr n) (Q.ϖ k * gr k) *
          iterTr (lvlTrAlg Q hgr) n c
            (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr (n + c)))
              (WittVector.teichmuller p (monoEl Q hgr (n + c) b0 J I))) -
        algebraMap B (lvl Q hgr n) x ∈
          Ideal.span {((p : lvl Q hgr n)) ^ m} := by
  -- the transition fixes the Teichmüller class
  rw [iterTr_lvlTr_mk_teich Q hgr n c (monoEl Q hgr (n + c) b0 J I)]
  -- `ϖ_k g_k` is itself a Teichmüller class
  have hAlg : algebraMap B (lvl Q hgr n) (Q.ϖ k * gr k) =
      (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr n)))
        (WittVector.teichmuller p (algebraMap (PreTilt B p) (lvlP Q hgr n)
          (varpiSharp Q k * tiltTower gr hgr k))) := by
    rw [map_mul, ← mk_teich_tiltTower Q hgr n Q.root k, ← mk_teich_tiltTower Q hgr n hgr k,
      ← map_mul (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr n))),
      ← map_mul (WittVector.teichmuller p),
      ← map_mul (algebraMap (PreTilt B p) (lvlP Q hgr n))]
  rw [hAlg]
  -- multiply the two Teichmüller classes
  rw [← map_mul (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr n))),
    ← map_mul (WittVector.teichmuller p)]
  -- the argument of the Teichmüller lift
  set X : lvlP Q hgr n :=
    algebraMap (PreTilt B p) (lvlP Q hgr n) (varpiSharp Q k * tiltTower gr hgr k) *
      chartIterTr Q hgr n c (monoEl Q hgr (n + c) b0 J I) with hX
  have hXcoe : (X : ChartAmbient (tiltTower gr hgr)) =
      algebraMap (PreTilt B p) (ChartAmbient (tiltTower gr hgr))
          (varpiSharp Q k * tiltTower gr hgr k) *
        (monoEl Q hgr (n + c) b0 J I : ChartAmbient (tiltTower gr hgr)) := by
    rw [hX, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
      chartIterTr_coe_gen Q hgr n c (monoEl Q hgr (n + c) b0 J I)]
  have hXamb : (X : ChartAmbient (tiltTower gr hgr)) =
      algebraMap (PreTilt B p) (ChartAmbient (tiltTower gr hgr))
          (varpiSharp Q k * tiltTower gr hgr k) *
        (algebraMap (PreTilt B p) (ChartAmbient (tiltTower gr hgr)) b0 *
          (chartGen (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
            (varpiSharp Q) (n + c) J) ^ I) := by
    rw [hXcoe, monoEl_coe]
  -- Bhatt's two-case monomial computation at the characteristic-`p` level
  rcases cokerMonoCases (p := p) (R := PreTilt B p) (G := tiltTower gr hgr) (T := varpiSharp Q)
      (tiltTower_isRootSystem gr hgr) (varpiSharp_rs Q) k m c n J I hc b0 with
    ⟨b, hb⟩ | ⟨s', hs'mem, hs'eq⟩
  · -- first case: the monomial lands in `φ(B♭)`
    have hXb : X = algebraMap (PreTilt B p) (lvlP Q hgr n) b := by
      apply Subtype.ext
      rw [hXamb, hb, Subalgebra.coe_algebraMap]
    refine ⟨PreTilt.untilt b, ?_⟩
    rw [hXb, mk_teich_algebraMap Q hgr n b, sub_self]
    exact Submodule.zero_mem _
  · -- second case: the monomial is `φ((ϖ♭0)^(p m))` times a level element
    let s'' : lvlP Q hgr n := ⟨s', hs'mem⟩
    have hXs' : X = algebraMap (PreTilt B p) (lvlP Q hgr n) (varpiSharp Q 0 ^ (p * m)) * s'' := by
      apply Subtype.ext
      rw [hXamb, hs'eq, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, hXs', map_mul (WittVector.teichmuller p),
      map_mul (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr n))),
      mk_teich_varpi0_pow Q hgr n m]
    obtain ⟨u, hu⟩ := varpi0_pow_pow Q hgr n m
    rw [hu]
    exact Ideal.mem_span_singleton.mpr ⟨(u : lvl Q hgr n) *
      (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr n))
        (WittVector.teichmuller p s'')), by ring⟩

end Work.DSM4p
