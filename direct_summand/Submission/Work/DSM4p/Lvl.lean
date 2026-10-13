import Submission.Work.DSM4p.Basic
import Submission.Work.DSM4p.Chart
import Submission.Work.DSM5c.Charts
import Submission.Work.DSM5c.Basic
import Submission.Work.DSM5c.G2.isSMulRegular_chartUntiltU
import Submission.Work.DSM5c.Eta.U.TeichAlgebraMap
import Submission.Work.DSM5c.Eta.U.SharpChartTiltGen

/-!
# DSM4p — the untilted levels of the Riemann extension tower (Route U)

This module is the *definition layer* of the subproject `DSM4p`'s Route U (the project lead's
reviewed design, `sources/dsmap/direct_summand_m4p_design_REVIEW.md`, statements in
`sources/dsmap/M4pU.lean`).  The levels of the frozen node `DSMap.Mix2.area_M4p` are

  `D n := (lvl n)^` — the `p`-adic completion of the **untilt of the characteristic-`p` chart
  level** `lvlP n`,

where (with `B♭ := PreTilt B p` the tilt of the perfectoid ring `B`, `gr` a compatible system of
`p`-power roots of `g = gr 0`, and `ϖ = Q.ϖ` the pseudo-uniformiser of `Q : PerfectoidData p B`)

* `g♭ := tiltTower gr hgr`, `ϖ♭ := tiltTower Q.ϖ Q.root` are the tilts of the two root systems;
* `lvlP n := chartRing (B := B♭) hgr♭ ϖ♭ n` is `DSM4p`'s own chart level (`Chart.lean`) built over
  the *characteristic-`p`* ring `B♭` — note `tiltTower r hr 0 = tiltOf r hr`, so
  `ϖ♭ 0 = DSM5c.tiltVarpi Q` and `g♭ 0 = tiltOf gr hgr`;
* `lvl n := DSM5c.untiltOf (lvlP n) (algebraMap B♭ (lvlP n))` is the untilt
  `𝕎(R) ⧸ 𝕎(φ)(ker θ_B)` of that chart level, a `B`-algebra via `DSM5c.untiltOf.algebraMap hθ`,
  with transition `lvlTr n := DSM5c.untiltOf.map … (chartTr …)` and its `B`-linear version
  `lvlTrAlg`.

The characteristic-`p` chart levels are *perfect* (`Work.DSM4p.chartLevel_perfect`), which is what
makes both Bhatt estimates (`Work.DSM4p.kerP`, `Work.DSM4p.cokerP`) available on them; the untilt
transfers them to `B`, and the completion then provides the `PerfectoidData` structure
(`Work.DSM4p.perfectoidData_adicCompletion`) and the `IsQRETp` transfer
(`Work.DSM4p.isQRETp_adicCompletion`).  No comparison map `S_N → D_N` is needed: `IsQRETp` only
sees `B → D_n`.

## Universes

Everything here lives at `Type a` for `B : Type a`: the DSM5c tilt/untilt API used below exists in
universe-polymorphic form under `Work.DSM5c.Eta.U` / `Work.DSM5c.G2.U`.

## Contents

* `Work.DSM4p.tiltTower`, `tiltTower_isRootSystem`, `tiltTower_zero`, `tiltTower_succ`,
  `untilt_tiltTower` — the tilt of a root system is again one, and its untilt is the system;
* `Work.DSM4p.lvlP`, `lvl`, `lvlAlg` — the char-`p` and untilted levels and the `B`-algebra
  structure on the latter;
* `Work.DSM4p.lvlTr_compat`, `lvlTr`, `lvlTrAlg` — the transition maps.

The lemmas *about* these objects (perfectness/`CharP` of `lvlP`, torsion-freeness, the two
Teichmüller lemmas, the divisibility `g ∣ p^n`, the kernel and cokernel clauses and the resulting
`IsQRETp`) live in sibling modules of this directory and are collected in `DSM4p/Main.lean`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

/-! ## 1. The tilt of a root system -/

section Tilt

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] [Fact ¬IsUnit (p : B)]

/-- **The tilt of a compatible system of `p`-power roots**: the `k`-th entry is the `k`-th
`p`-power root of `tiltOf r hr` inside the tilt `PreTilt B p = Perfection (B ⧸ p) p`, i.e. the
tilt of the `k`-shifted tower `k ↦ r (n + k)`.  This is the natural home of the tilted chart
generators `g♭ k` and `ϖ♭ k` of Route U. -/
noncomputable def tiltTower (r : ℕ → B) (hr : IsRootSystem p r) : ℕ → PreTilt B p :=
  fun k => DSM5c.tiltOf (DSM5c.shiftTower r k) (DSM5c.shiftTower_compat r hr k)

/-- The `0`-th entry of the tilt tower is the tilt of the system itself. -/
theorem tiltTower_zero (r : ℕ → B) (hr : IsRootSystem p r) :
    tiltTower r hr 0 = DSM5c.tiltOf r hr :=
  DSM5c.tiltOf_congr (tr := DSM5c.shiftTower r 0) (tr' := r)
    (funext fun n => by rw [DSM5c.shiftTower, Nat.add_zero]) _ _

/-- **The tilt tower is again a compatible system of `p`-power roots**: `(g♭ (k+1))^p = g♭ k`.
This is `DSM5c.tiltOf_shiftTower` (the iterated `p`-th root of the tilt is the tilt of the shifted
tower) together with `frobeniusEquiv_def`. -/
theorem tiltTower_isRootSystem (r : ℕ → B) (hr : IsRootSystem p r) :
    IsRootSystem p (tiltTower r hr) := by
  have hcancel : ∀ y : PreTilt B p, ((frobeniusEquiv (PreTilt B p) p).symm y) ^ p = y := by
    intro y
    rw [← frobeniusEquiv_def (PreTilt B p) p ((frobeniusEquiv (PreTilt B p) p).symm y)]
    exact RingEquiv.apply_symm_apply _ y
  have key : ∀ k, tiltTower r hr (k + 1) =
      (frobeniusEquiv (PreTilt B p) p).symm (tiltTower r hr k) := by
    intro k
    have h1 := DSM5c.tiltOf_shiftTower r hr (k + 1)
    rw [Function.iterate_succ_apply'] at h1
    rw [DSM5c.tiltOf_shiftTower r hr k] at h1
    exact h1.symm
  intro k
  rw [key k]
  exact hcancel _

/-- The `k`-th entry of the tilt tower is a `p^k`-th root of the tilt. -/
theorem tiltTower_pow_pow (r : ℕ → B) (hr : IsRootSystem p r) (k : ℕ) :
    tiltTower r hr k ^ p ^ k = DSM5c.tiltOf r hr := by
  rw [← tiltTower_zero r hr]
  exact (tiltTower_isRootSystem r hr).pow_pow_zero k

/-- **The untilt of the tilt tower is the tower**: `♯(r♭ k) = r k`.  This is
`DSM5c.Eta.U.untilt_tiltOf` applied to the `k`-shifted tower. -/
theorem untilt_tiltTower [IsAdicComplete (Ideal.span {(p : B)}) B] (r : ℕ → B)
    (hr : IsRootSystem p r) (k : ℕ) : PreTilt.untilt (tiltTower r hr k) = r k := by
  rw [tiltTower]
  rw [DSM5c.Eta.U.untilt_tiltOf (DSM5c.shiftTower r k) (DSM5c.shiftTower_compat r hr k)]
  rw [DSM5c.shiftTower]
  simp only [Nat.zero_add]

end Tilt

/-! ## 2. The levels -/

section LvlP

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] [Fact ¬IsUnit (p : B)]

/-- **The characteristic-`p` chart level**: DSM4p's own `chartRing` built over the tilt `B♭` of
`B`, from the tilted root systems `g♭ = tiltTower gr hgr` and `ϖ♭ = tiltTower Q.ϖ Q.root`.  It is
a `B♭`-algebra, perfect of characteristic `p` (`Work.DSM4p.chartLevel_perfect`). -/
noncomputable abbrev lvlP (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) : Type a :=
  chartRing (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
    (tiltTower Q.ϖ Q.root) N

/-- The defining equation of `lvlP`: it is the chart ring of the tilted root systems. -/
theorem lvlP_def (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (N : ℕ) :
    lvlP Q hgr N = chartRing (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
      (tiltTower Q.ϖ Q.root) N := rfl

end LvlP

section Levels

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B] [Fact ¬IsUnit (p : B)]
variable [IsAdicComplete (Ideal.span {(p : B)}) B]

/-- **The untilted level** `D'_N = untiltOf (lvlP N) (algebraMap B♭ (lvlP N))`: the quotient of the
Witt vectors of the characteristic-`p` chart level by the image of the theta-kernel of `B`.  It is
the level `D_N` of the node before `p`-adic completion. -/
noncomputable abbrev lvl (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) : Type a :=
  DSM5c.untiltOf (p := p) (W := B) (lvlP Q hgr N)
    (algebraMap (PreTilt B p) (lvlP Q hgr N))

/-- The surjectivity of Fontaine's theta map for the perfectoid ring `B` — the input of every
`untiltOf` construction below. -/
theorem surjective_fontaineTheta (Q : PerfectoidData p B) :
    Function.Surjective (WittVector.fontaineTheta (p := p) (R := B)) :=
  DSM5c.G2.U.surjective_fontaineTheta_of_perfectoidData Q

/-- **The `B`-algebra structure on the untilted level**, induced by
`untiltOf.algebraMap` (which factors the surjection `θ_B : 𝕎(B♭) ↠ B` through the quotient
defining `lvl N`). -/
noncomputable def lvlAlg (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) : Algebra B (lvl Q hgr N) :=
  (DSM5c.untiltOf.algebraMap (p := p) (W := B) (surjective_fontaineTheta Q)
    (algebraMap (PreTilt B p) (lvlP Q hgr N))).toAlgebra

/-- The `B`-algebra structure of the untilted level, as a typeclass instance (the same term as
`lvlAlg`, so that `lvlAlg` remains available for explicit `letI` uses). -/
noncomputable instance lvlAlgebraInstance (Q : PerfectoidData p B) {gr : ℕ → B}
    (hgr : IsRootSystem p gr) (N : ℕ) : Algebra B (lvl Q hgr N) :=
  lvlAlg Q hgr N

/-- The transition maps of the chart tower are `B♭`-linear: this is the compatibility hypothesis
of `DSM5c.untiltOf.map` for the transition of the untilted tower.  (Stated as a closed lemma
rather than proved inline: an inline `ext; simp` diverges.) -/
theorem lvlTr_compat (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (N : ℕ) :
    (chartTr (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
        (tiltTower Q.ϖ Q.root) N).toRingHom.comp
        (algebraMap (PreTilt B p) (lvlP Q hgr (N + 1))) =
      algebraMap (PreTilt B p) (lvlP Q hgr N) :=
  RingHom.ext fun x =>
    (chartTr (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
      (tiltTower Q.ϖ Q.root) N).commutes x

/-- **The transition map of the untilted tower**: `untiltOf.map` of the chart transition. -/
noncomputable def lvlTr (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (N : ℕ) :
    lvl Q hgr (N + 1) →+* lvl Q hgr N :=
  DSM5c.untiltOf.map (p := p) (W := B)
    (algebraMap (PreTilt B p) (lvlP Q hgr (N + 1)))
    (algebraMap (PreTilt B p) (lvlP Q hgr N))
    (chartTr (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
      (tiltTower Q.ϖ Q.root) N).toRingHom
    (lvlTr_compat Q hgr N)

/-- The value of the transition on a class: `lvlTr` is induced by `𝕎(chartTr)`. -/
theorem lvlTr_apply (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (N : ℕ)
    (x : WittVector p (lvlP Q hgr (N + 1))) :
    lvlTr Q hgr N (DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr (N + 1))) x) =
      DSM5c.untiltOf.mk (algebraMap (PreTilt B p) (lvlP Q hgr N))
        (WittVector.map (chartTr (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
          (tiltTower Q.ϖ Q.root) N).toRingHom x) :=
  DSM5c.untiltOf.map_apply _ _ _ _ _

/-- `lvlTr` is `B`-linear: it fixes the image of `B` (this is `untiltOf.map_algebraMap`). -/
theorem lvlTr_algebraMap (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) (b : B) :
    lvlTr Q hgr N (algebraMap B (lvl Q hgr (N + 1)) b) = algebraMap B (lvl Q hgr N) b :=
  DSM5c.untiltOf.map_algebraMap (p := p) (W := B) (surjective_fontaineTheta Q)
    (algebraMap (PreTilt B p) (lvlP Q hgr (N + 1)))
    (algebraMap (PreTilt B p) (lvlP Q hgr N))
    (chartTr (gr := tiltTower gr hgr) (tiltTower_isRootSystem gr hgr)
      (tiltTower Q.ϖ Q.root) N).toRingHom
    (lvlTr_compat Q hgr N) b

/-- **The `B`-linear transition map** `lvl (N+1) →ₐ[B] lvl N` of the untilted tower.  Its
underlying ring hom is `lvlTr`; it is `B`-linear because `untiltOf.map` commutes with the
`B`-algebra structure (`untiltOf.map_algebraMap`). -/
noncomputable def lvlTrAlg (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr)
    (N : ℕ) :
    letI := lvlAlg Q hgr (N + 1); letI := lvlAlg Q hgr N
    lvl Q hgr (N + 1) →ₐ[B] lvl Q hgr N := by
  letI := lvlAlg Q hgr (N + 1)
  letI := lvlAlg Q hgr N
  exact { lvlTr Q hgr N with commutes' := lvlTr_algebraMap Q hgr N }

end Levels

end Work.DSM4p
