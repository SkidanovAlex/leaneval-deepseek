import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM5c.Regularity.tiltVarpi_isSMulRegular
import Submission.Work.DSM5c.G2.isSMulRegular_chartUntiltU
import Submission.Work.DSM4p.chartLevel_perfect

/-!
# DSM4p — the untilted levels are `p`-torsion-free

This is step **(1)** of the Route U plan (`Submission/Work/DSM4p/Plan.lean`): for

`B` a commutative ring, `p` prime with `[Fact ¬IsUnit (p : B)]` and
`[IsAdicComplete (Ideal.span {(p : B)}) B]`, `Q : DSMap.PerfectoidData p B`, `hgr : IsRootSystem p gr`
and `N : ℕ`, the untilted level

  `lvl Q hgr N = untiltOf (lvlP Q hgr N) (algebraMap B♭ (lvlP Q hgr N))`

is a `p`-torsion-free ring — that is, `p` is a non-zero-divisor of `lvl Q hgr N`.

Write `B♭ := PreTilt B p`, `g♭ := tiltTower gr hgr`, `ϖ♭ := tiltTower Q.ϖ Q.root`
(so `ϖ♭ 0 = DSM5c.tiltVarpi Q`) and `R_N := lvlP Q hgr N = chartRing g♭ ϖ♭ N ⊆ B♭[1/g♭ 0]`.
The proof is an immediate application of the general transfer
`Work.DSM5c.G2.U.isSMulRegular_untiltOf_of_regular`:

* `R_N` is *perfect* of characteristic `p` (`Work.DSM4p.chartLevel_perfect`) — in particular
  `(p : R_N) = 0`, which together with the explicit `Subsingleton` case inside
  `isSMulRegular_untiltOf_of_regular` handles the degenerate case `g♭ 0 = 0` (where `lvl` is the
  zero ring); **no hypothesis on `gr 0` is needed**;
* `φ (ϖ♭) = algebraMap B♭ R_N (ϖ♭)` is a non-zero-divisor of `R_N`: `ϖ♭` is a non-zero-divisor of
  `B♭` (`Work.DSM5c.Regularity.tiltVarpi_isSMulRegular`), hence so is its image in the localisation
  `B♭[1/g♭ 0]` (`IsSMulRegular.of_isLocalization`), hence so is its image in the subalgebra
  `R_N` (`Work.DSM5c.G2.isSMulRegular_subalgebra_algebraMap`), by
  `Work.DSM5c.G2.chartPhi_tiltVarpi_isSMulRegular` verbatim;
* `θ_B : 𝕎(B♭) ↠ B` is surjective (`Work.DSM4p.surjective_fontaineTheta`).

The `p`-th power of the last point is exactly the regularity hypothesis `hc` of
`isSMulRegular_untiltOf_of_regular` (`tiltVarpi Q` and `tiltTower Q.ϖ Q.root 0` agree by
`Work.DSM4p.tiltTower_zero`).
-/

set_option linter.style.haveILetI false

namespace Work.DSM4p

universe a

open DSMap

/-- **The untilted level `lvl Q hgr N` is `p`-torsion-free.**  This is step (1) of the Route U
plan: `lvl Q hgr N` is the untilt of the perfect characteristic-`p` chart level
`lvlP Q hgr N = chartRing (tiltTower gr hgr) (tiltTower Q.ϖ Q.root) N`, and
`isSMulRegular_untiltOf_of_regular` reduces its `p`-torsion-freeness to the two inputs supplied
below: `(p : lvlP Q hgr N) = 0` and the regularity of `algebraMap B♭ (lvlP Q hgr N) (tiltVarpi Q)`.
(No hypothesis on `gr 0` is needed: if `gr 0 = 0` the level is the zero ring, and the
`Subsingleton` case of `isSMulRegular_untiltOf_of_regular` applies.) -/
theorem lvl_torsionFree {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr) (N : ℕ) :
    IsSMulRegular (Work.DSM4p.lvl Q hgr N) (p : Work.DSM4p.lvl Q hgr N) := by
  -- `θ_B` is onto (integral perfectoidness of `B`).
  have hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := B)) :=
    DSM5c.G2.U.surjective_fontaineTheta_of_perfectoidData Q
  -- The characteristic-`p` level `lvlP Q hgr N` is perfect.
  have hperf : PerfectRing (lvlP Q hgr N) p :=
    chartLevel_perfect (tiltTower_isRootSystem gr hgr) (tiltTower_isRootSystem Q.ϖ Q.root) N
  -- In particular `p` vanishes there (this also covers the degenerate case `g♭ 0 = 0`).
  have hp0 : (p : lvlP Q hgr N) = 0 := by
    rw [← map_natCast (algebraMap (PreTilt B p) (lvlP Q hgr N)) p, CharP.cast_eq_zero, map_zero]
  -- `algebraMap B♭ (lvlP Q hgr N) (ϖ♭)^p` is a non-zero-divisor: `ϖ♭` is a non-zero-divisor of
  -- `B♭`, hence of the localisation `B♭[1/g♭ 0]` and hence of the subalgebra `lvlP Q hgr N`.
  have hc : IsSMulRegular (lvlP Q hgr N)
      (algebraMap (PreTilt B p) (lvlP Q hgr N) (DSM5c.tiltVarpi Q) ^ p) := by
    have hreg : IsSMulRegular (PreTilt B p) (DSM5c.tiltVarpi Q) := by
      rw [IsSMulRegular]
      intro x y hxy
      have h : DSM5c.tiltVarpi Q * (x - y) = 0 := by
        rw [mul_sub, show DSM5c.tiltVarpi Q * x = DSM5c.tiltVarpi Q * y from by
          simpa [smul_eq_mul] using hxy, sub_self]
      exact sub_eq_zero.mp (DSM5c.Regularity.tiltVarpi_isSMulRegular Q (x - y) h)
    have hloc : IsSMulRegular (ChartAmbient (B := PreTilt B p) (tiltTower gr hgr))
        (algebraMap (PreTilt B p) (ChartAmbient (B := PreTilt B p) (tiltTower gr hgr))
          (DSM5c.tiltVarpi Q)) :=
      IsSMulRegular.of_isLocalization _
        (Submonoid.powers (tiltTower gr hgr 0)) hreg
    exact (DSM5c.G2.isSMulRegular_subalgebra_algebraMap
      (chartLevel (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
        (tiltTower Q.ϖ Q.root) N) hloc).pow p
  exact DSM5c.G2.U.isSMulRegular_untiltOf_of_regular (p := p) (W := B)
    (R := lvlP Q hgr N) Q hθ (algebraMap (PreTilt B p) (lvlP Q hgr N)) hp0 hc

end Work.DSM4p
