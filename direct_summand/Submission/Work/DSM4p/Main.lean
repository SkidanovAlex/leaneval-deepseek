import Submission.Work.DSM4p.Basic
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.LvlMisc
import Submission.Work.DSM4p.LvlQRET
import Submission.Work.DSM4p.AreaM4pRouteU
import Submission.Work.DSM4p.areaM4p_isUnit
import Submission.Work.DSM4p.areaM4p_gr_zero
import Submission.Work.DSMap.Mix2

/-!
# DSM4p — the frozen node `DSMap.Mix2.area_M4p`, proved

This is the assembly module of the subproject `Submission/Work/DSM4p`.  It contains

  `DSMap.Mix2.area_M4p_proved`

whose type is *identical* (up to universe names) to the frozen node `DSMap.Mix2.area_M4p` of
`Submission/Work/DSMap/Mix2.lean`, and it is sorry-free and axiom-clean
(`#print axioms` gives `[propext, Classical.choice, Quot.sound]`).

## The route (Route U, the project lead's reviewed design)

The levels of the tower are the `p`-adic completions

  `D n := AdicCompletion (Ideal.span {(p : lvl Q hgr n)}) (lvl Q hgr n)`,

where `lvl Q hgr n := untiltOf (lvlP Q hgr n) (algebraMap B♭ (lvlP Q hgr n))` is the **untilt** of
the characteristic-`p` chart level `lvlP Q hgr n ⊆ B♭[1/g♭ 0]` built over the tilt
`B♭ = PreTilt B p` from the tilted root systems `g♭ = tiltTower gr hgr` and
`ϖ♭ = tiltTower Q.ϖ Q.root` (`Submission/Work/DSM4p/Lvl.lean`; the plan with the proof of every
transfer step is written out in `Submission/Work/DSM4p/Plan.lean`).  No comparison map
`chartLevel → D n` is needed: `IsQRETp` only sees `B → D n`.

The mathematics is Bhatt, *The direct summand conjecture and its derived variant*
(arXiv:1608.08882), Theorem 3.1 with the base-change argument of Remark 3.2, in the pro-uniform
form `DSMap.Mix2.IsQRETp`:

* **Characteristic `p`.**  The chart levels over the perfect ring `B♭` are perfect
  (`Work.DSM4p.chartLevel_perfect`), and Bhatt's two quantitative estimates hold on them: the
  kernel estimate `Work.DSM4p.kerP` (a two-chart Hartogs argument after Frobenius, with the
  *`p`-root* closure — not the integral closure — of a perfect ring in a localisation) and the
  cokernel estimate `Work.DSM4p.cokerP`, generalised to an arbitrary modulus and level shift in
  `Work.DSM4p.cokerP_pow` (the two-case monomial computation).
* **Transfer to the untilt.**  `Work.DSM4p.lvl_kernel` (the kernel clause, by a dévissage over the
  `p`-admissible filtration of `B`, using `Work.DSM4p.exists_untilt_lift` for the PB2 dictionary
  and `Work.DSM4p.lvl_teich_mem_span_p` for the mod-`p` comparison of the untilt) and
  `Work.DSM4p.lvl_cokernel` (the cokernel clause, via `cokerP_pow` and the Teichmüller calculus
  `Work.DSM4p.lvl_exists_teich`, `Work.DSM4p.lvl_teich_mem_span_p`, `Work.DSM4p.lvlTr_teich`).
  The constants of the two clauses are merged with `Work.DSM4p.qretKernel_mono` /
  `Work.DSM4p.qretCoker_mono` in `Work.DSM4p.lvl_isQRETp`
  (`Submission/Work/DSM4p/LvlQRET.lean`).
* **Completion.**  `Work.DSM4p.perfectoidData_adicCompletion` gives `PerfectoidData` on each
  `D n` with `(QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)`; its three inputs on the level `lvl Q hgr n`
  are `Work.DSM4p.lvl_torsionFree`, `Work.DSM4p.lvl_frobSurj` and `Work.DSM4p.lvl_frobInj`.
  `Work.DSM4p.isQRETp_adicCompletion` transfers `IsQRETp` to the completed tower, and
  `Work.DSM4p.lvl_dvd` gives `g ∣ p^n` (`g = gr 0`), transported along `AdicCompletion.of`; the
  assembly is `Work.DSM4p.areaM4p_notIsUnit` (`Submission/Work/DSM4p/AreaM4pRouteU.lean`).
* **Degenerate cases.**  `IsUnit (p : B)` forces `B` to be a subsingleton and `D n := B` works
  (`Work.DSM4p.areaM4p_isUnit`); `gr 0 = 0` forces `gr k = 0` for all `k`
  (`Work.DSM2p.isReduced Q`), and the zero-ring tower works
  (`Work.DSM4p.areaM4p_gr_zero`).

The check

  `example : @DSMap.Mix2.area_M4p_proved = @DSMap.Mix2.area_M4p := rfl`

at the end of this file verifies that the statement delivered here is the frozen one, up to
universe names.

## What is *not* used any more

The files `DSM4p/Completion.lean`, `DSM4p/Assembly.lean`, `DSM4p/Reduction.lean`,
`DSM4p/chartComp_*.lean`, `DSM4p/chartKernel*.lean`, `DSM4p/freeLevel_*.lean`,
`DSM4p/chartLevel_comap_span_p.lean`, `DSM4p/chartLevel_pIntClosed.lean` and the many `_*.lean`
probe files belong to the *superseded* presentation of the tower (`chartRing` itself, completed,
without the `frobInj` and kernel clauses) and to scratch work.  They are **retired**: they are not
imported by this module or by anything on the delivery path, and some of them still contain
`sorry`s.  See `Submission/Work/DSM4p/RETIRED.md`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace DSMap.Mix2

universe a

open DSMap DSMap.Mix

/-- **M4p** quantitative Riemann extension (Bhatt Thm 3.1 + Rmk 3.2) against the pro `IsQRETp`,
proved in `Submission/Work/DSM4p` (Route U: the levels are the `p`-adic completions of the
untilted characteristic-`p` chart levels). -/
theorem area_M4p_proved (p : ℕ) [Fact p.Prime] (B : Type a) [CommRing B]
    (Q : PerfectoidData p B) (gr : ℕ → B) (hgr : ∀ k, gr (k + 1) ^ p = gr k) :
    ∃ (D : ℕ → Type a) (_ : ∀ n, CommRing (D n)) (_ : ∀ n, Algebra B (D n))
      (QD : ∀ n, PerfectoidData p (D n)) (tr : ∀ n, D (n + 1) →ₐ[B] D n),
      (∀ n k, (QD n).ϖ k = algebraMap B (D n) (Q.ϖ k)) ∧
      (∀ n, ∃ y : D n, algebraMap B (D n) (gr 0) * y = (p : D n) ^ n) ∧
      IsQRETp p B Q.ϖ gr D tr := by
  by_cases h0 : gr 0 = 0
  · exact Work.DSM4p.areaM4p_gr_zero Q gr hgr h0
  · by_cases hu : IsUnit (p : B)
    · exact Work.DSM4p.areaM4p_isUnit Q gr hgr hu
    · exact Work.DSM4p.areaM4p_notIsUnit Q gr hgr h0 hu

end DSMap.Mix2

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

/-- Re-export of the node's statement as a proposition: `AreaM4p` is definitionally the
conclusion of the frozen `DSMap.Mix2.area_M4p`. -/
theorem areaM4p_iff_retTower (p : ℕ) [Fact p.Prime] (B : Type a) [CommRing B]
    (Q : PerfectoidData p B) (gr : ℕ → B) :
    AreaM4p p B Q gr ↔ Nonempty (RETTower p B Q gr) :=
  areaM4p_iff p B Q gr

end Work.DSM4p

/-- The delivered statement is the frozen node, up to universe names. -/
example : @DSMap.Mix2.area_M4p_proved = @DSMap.Mix2.area_M4p := rfl
