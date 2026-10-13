import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.chartLevel_perfect
import Submission.Work.DSPB5.Basic

/-!
# DSM4p — the characteristic-`p` chart levels `lvlP Q hgr N` are of characteristic `p`

This is step **(0)** of the Route U plan (`Submission/Work/DSM4p/Plan.lean`), the input of
`Work.DSM4p.lvl_torsionFree` and of the Teichmüller dictionary
(`DSM5c.mem_span_p_sup_map_ker_fontaineTheta`).

Write `B♭ := PreTilt B p`, `g♭ := tiltTower gr hgr`, `ϖ♭ := tiltTower Q.ϖ Q.root` and
`R_N := lvlP Q hgr N = chartRing g♭ ϖ♭ N ⊆ B♭[1/g♭ 0]`.  Then:

* `(p : R_N) = 0` because `R_N` is a `B♭`-subalgebra of the localisation `B♭[1/g♭ 0]` and
  `(p : B♭) = 0` (`PreTilt` is of characteristic `p`);
* `R_N` is **nontrivial** as soon as `gr 0 ≠ 0`: the tilt `g♭ 0` of the root system is then
  nonzero (apply `PreTilt.untilt`, which sends `0` to `0`, and `untilt_tiltTower`), so it is not
  nilpotent because the tilt `B♭` is reduced (a perfect ring of characteristic `p` is reduced,
  `DSMap.Mix.instIsReducedOfPerfectRing`); hence the localisation `B♭[1/g♭ 0]` — and with it every
  subalgebra containing `1` — is nontrivial.

The two together give `CharP R_N p` by `CharP.charP_iff_prime_eq_zero`.  The hypothesis `gr 0 ≠ 0`
is genuinely needed: for `gr 0 = 0` the level is the zero ring (`B♭[1/0] = 0`), in which `1 = 0`,
so that no prime is the characteristic.
-/

set_option linter.style.haveILetI false

namespace Work.DSM4p

universe a

open DSMap DSMap.Mix DSMap.Mix2

section Aux

variable {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]

/-- `PreTilt.untilt` carries `0` to `0`.  It is the Teichmüller map `Perfection.teichmuller`,
which is *multiplicative* only, so this is not `map_zero` of a `MonoidWithZeroHom` but the
statement `Perfection.teichmuller_zero`. -/
theorem untilt_zero [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B] :
    PreTilt.untilt (0 : PreTilt B p) = 0 :=
  Perfection.teichmuller_zero

/-- **The tilt of a nonzero root system is nonzero.**  If `g♭ 0 = 0`, then applying the
(multiplicative) map `PreTilt.untilt` gives `gr 0 = untilt (g♭ 0) = untilt 0 = 0`. -/
theorem tiltTower_zero_ne_zero [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    {gr : ℕ → B} (hgr : IsRootSystem p gr) (hgr0 : gr 0 ≠ 0) : tiltTower gr hgr 0 ≠ 0 := by
  intro h
  apply hgr0
  have h1 : PreTilt.untilt (tiltTower gr hgr 0) = PreTilt.untilt (0 : PreTilt B p) := by rw [h]
  rwa [untilt_tiltTower gr hgr 0, untilt_zero] at h1

/-- **The characteristic-`p` chart level `lvlP Q hgr N` is nontrivial** when `gr 0 ≠ 0`.

It is a subalgebra containing `1` of the localisation `B♭[1/g♭ 0]`, and the localisation of a
reduced ring (`B♭` is perfect of characteristic `p`) away from a non-nilpotent element
(`g♭ 0 ≠ 0`) is nontrivial. -/
theorem lvlP_nontrivial [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : PerfectoidData p B) {gr : ℕ → B} (hgr : IsRootSystem p gr) (hgr0 : gr 0 ≠ 0) (N : ℕ) :
    Nontrivial (lvlP Q hgr N) := by
  have hg : tiltTower gr hgr 0 ≠ 0 := tiltTower_zero_ne_zero hgr hgr0
  haveI hred : IsReduced (PreTilt B p) := inferInstance
  -- `g♭ 0` is not nilpotent, so the localisation away from it is nontrivial.
  have h0 : (0 : PreTilt B p) ∉ Submonoid.powers (tiltTower gr hgr 0) := by
    intro h
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (0 : PreTilt B p) (tiltTower gr hgr 0)).mp h
    exact hg (hred.eq_zero _ ⟨n, hn⟩)
  haveI hnt : Nontrivial (ChartAmbient (tiltTower gr hgr)) :=
    Submonoid.LocalizationMap.nontrivial
      (IsLocalization.toLocalizationMap (Submonoid.powers (tiltTower gr hgr 0))
        (Localization.Away (tiltTower gr hgr 0))) h0
  -- a subalgebra of a nontrivial ring is nontrivial (Mathlib's `Nontrivial ↥S` instance)
  exact inferInstance

end Aux

theorem lvlP_charP {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (N : ℕ) : CharP (Work.DSM4p.lvlP Q hgr N) p := by
  haveI : Nontrivial (lvlP Q hgr N) := lvlP_nontrivial Q hgr hgr0 N
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : Nat.Prime p)]
  rw [← map_natCast (algebraMap (PreTilt B p) (lvlP Q hgr N)) p, CharP.cast_eq_zero, map_zero]

end Work.DSM4p
