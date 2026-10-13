import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvl_exists_teich
import Submission.Work.DSM4p.lvl_teich_mem_span_p
import Submission.Work.DSM4p.chartLevel_perfect
import Submission.Work.DSM4p.lvlP_charP
import Submission.Work.DSM4p.lvl_mk_teich_tiltTower
import Submission.Work.DSM5c.Untilt.untilt_frobInj

/-!
# DSM4p — Frobenius injectivity mod `p` on the untilted levels (Route U)

This is step **(6)** of the Route U plan (`Submission/Work/DSM4p/Plan.lean`): the level
`lvl Q hgr N = untiltOf (lvlP Q hgr N) (algebraMap B♭ (lvlP Q hgr N))` of the Riemann extension
tower is `p`-integrally closed in the strict sense of the `frobInj` field of `PerfectoidData`:

  `y ^ p ∈ (p)  →  y ∈ (ϖ_0)`,   `ϖ_0 = algebraMap B (lvl Q hgr N) (Q.ϖ 0)`.

## The argument

Write `R := lvlP Q hgr N` (the characteristic-`p` chart level, perfect), `φ := algebraMap B♭ R` and
`ϖ♭ := DSM5c.tiltVarpi Q = tiltTower Q.ϖ Q.root 0` (the tilted pseudo-uniformiser).

1. **Teichmüller representatives** (`lvl_exists_teich`): `y ≡ [r] mod p` for some `r : R`.
2. Hence `[r] ^ p ≡ y ^ p ≡ 0 mod p`, i.e. `mk (teich (r ^ p)) ∈ (p : lvl Q hgr N)`; this is purely
   quotient algebra (`mk` kills the ideal `(p)` and is a ring homomorphism).
3. The Teichmüller dictionary `lvl_teich_mem_span_p` turns this into
   `r ^ p ∈ (φ ϖ♭) ^ p` in `R`.
4. `R` is perfect of characteristic `p`, so taking `p`-th roots
   (`Work.DSM5c.Untilt.mem_span_singleton_of_pow_mem_pow`: `x ↦ x ^ p` is a bijection) gives
   `r ∈ (φ ϖ♭)`, say `r = φ ϖ♭ · s`.
5. `mk [φ ϖ♭] = algebraMap (♯ ϖ♭) = algebraMap (Q.ϖ 0)` (`lvl_mk_teich_tiltTower`, using
   `♯(ϖ♭) = Q.ϖ 0`), so `[r] = algebraMap (Q.ϖ 0) · [s]` lies in `(algebraMap (Q.ϖ 0))`.
6. `(p) ⊆ (algebraMap (Q.ϖ 0))` because `Q.unit` gives `Q.ϖ 0 ^ p = p · v` with `v : Bˣ`, so
   `p = (algebraMap (Q.ϖ 0)) ^ p · (algebraMap v)⁻¹ = algebraMap (Q.ϖ 0) · …`.
7. `y = (y - [r]) + [r]` with both summands in the ideal.

No torsion-freeness of `lvl Q hgr N` and no completeness of the level is used; the only inputs are
the Teichmüller dictionary and the perfectness/characteristic of the chart level.
-/

set_option linter.style.haveILetI false

namespace Work.DSM4p

universe a

theorem lvl_frobInj {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr)
    (hgr0 : gr 0 ≠ 0) (N : ℕ) (y : Work.DSM4p.lvl Q hgr N)
    (hy : y ^ p ∈ Ideal.span {((p : Work.DSM4p.lvl Q hgr N))}) :
    y ∈ Ideal.span {(algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0))} := by
  haveI hchar : CharP (Work.DSM4p.lvlP Q hgr N) p := Work.DSM4p.lvlP_charP Q hgr hgr0 N
  haveI hperf : PerfectRing (Work.DSM4p.lvlP Q hgr N) p :=
    Work.DSM4p.chartLevel_perfect (Work.DSM4p.tiltTower_isRootSystem gr hgr)
      (Work.DSM4p.tiltTower_isRootSystem Q.ϖ Q.root) N
  -- ## Step (2): a Teichmüller representative modulo `p`
  obtain ⟨r, hr⟩ := Work.DSM4p.lvl_exists_teich Q hgr hgr0 N y
  -- ## Step (3): `mk [r] ^ p ∈ (p)`
  have hAp : (Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p r)) ^ p
      ∈ Ideal.span {((p : Work.DSM4p.lvl Q hgr N))} := by
    refine Ideal.Quotient.eq_zero_iff_mem.mp ?_
    have h0 : (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) (y -
        (Work.DSM5c.untiltOf.mk (p := p) (W := B)
          (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
          (WittVector.teichmuller p r))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hr
    have h1 : (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) (y -
        (Work.DSM5c.untiltOf.mk (p := p) (W := B)
          (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
          (WittVector.teichmuller p r))) =
        (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) y -
        (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))}))
          (Work.DSM5c.untiltOf.mk (p := p) (W := B)
            (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
            (WittVector.teichmuller p r)) :=
      map_sub (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) y _
    rw [h1] at h0
    have hq : (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) y =
        (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))}))
          (Work.DSM5c.untiltOf.mk (p := p) (W := B)
            (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
            (WittVector.teichmuller p r)) := sub_eq_zero.mp h0
    have h2 : (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))}))
        ((Work.DSM5c.untiltOf.mk (p := p) (W := B)
          (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
          (WittVector.teichmuller p r)) ^ p) =
        ((Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))}))
          (Work.DSM5c.untiltOf.mk (p := p) (W := B)
            (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
            (WittVector.teichmuller p r))) ^ p :=
      map_pow (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) _ p
    have h3 : (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) (y ^ p) =
        ((Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) y) ^ p :=
      map_pow (Ideal.Quotient.mk (Ideal.span {((p : Work.DSM4p.lvl Q hgr N))})) y p
    rw [h2, ← hq, ← h3]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  -- `mk [r] ^ p = mk [r ^ p]`
  have hAp' : Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p (r ^ p))
      ∈ Ideal.span {((p : Work.DSM4p.lvl Q hgr N))} := by
    have h1 : (Work.DSM5c.untiltOf.mk (p := p) (W := B)
          (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
          (WittVector.teichmuller p r)) ^ p =
        Work.DSM5c.untiltOf.mk (p := p) (W := B)
          (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
          (WittVector.teichmuller p (r ^ p)) := by
      rw [map_pow (WittVector.teichmuller p) r p, map_pow]
    rw [← h1]
    exact hAp
  -- ## Step (4): `r ^ p ∈ (φ (ϖ♭)) ^ p` in the characteristic-`p` level
  have hrp : r ^ p ∈ Ideal.span {((algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N)
      (DSM5c.tiltVarpi Q)) ^ p)} :=
    (Work.DSM4p.lvl_teich_mem_span_p Q hgr hgr0 N (r ^ p)).mp hAp'
  -- ## Step (5): perfectness of the level turns this into `r ∈ (φ (ϖ♭))`
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp
    (Work.DSM5c.Untilt.mem_span_singleton_of_pow_mem_pow (p := p)
      (t := algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N) (DSM5c.tiltVarpi Q))
      (s := r) hrp)
  -- ## Step (6): the Teichmüller class of `φ (ϖ♭)` is `algebraMap (Q.ϖ 0)`
  have hkey : Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N)
          (DSM5c.tiltVarpi Q))) =
      algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0) := by
    rw [show DSM5c.tiltVarpi Q = Work.DSM4p.tiltTower Q.ϖ Q.root 0 from
      (Work.DSM4p.tiltTower_zero Q.ϖ Q.root).symm]
    exact Work.DSM4p.lvl_mk_teich_tiltTower Q hgr N Q.root 0
  have hAr : Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p r)
      ∈ Ideal.span {algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)} := by
    have hrw : WittVector.teichmuller p r =
        WittVector.teichmuller p (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N)
          (DSM5c.tiltVarpi Q)) * WittVector.teichmuller p s := by
      rw [hs, map_mul (WittVector.teichmuller p)]
    rw [hrw, map_mul, hkey]
    exact Ideal.mem_span_singleton'.mpr
      ⟨Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p s), by ring⟩
  -- ## Step (7): `(p) ⊆ (algebraMap (Q.ϖ 0))`
  have hspan : Ideal.span {((p : Work.DSM4p.lvl Q hgr N))} ≤
      Ideal.span {algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)} := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    obtain ⟨v, hv⟩ := Q.unit
    set vA : (Work.DSM4p.lvl Q hgr N)ˣ :=
      Units.map (algebraMap B (Work.DSM4p.lvl Q hgr N)) v with hvA
    have hv' : (algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) ^ p =
        (p : Work.DSM4p.lvl Q hgr N) * (vA : Work.DSM4p.lvl Q hgr N) := by
      rw [← map_pow]
      have hvB : (algebraMap B (Work.DSM4p.lvl Q hgr N)) (Q.ϖ 0 ^ p) =
          (p : Work.DSM4p.lvl Q hgr N) * (vA : Work.DSM4p.lvl Q hgr N) := by
        rw [hv, map_mul, map_natCast, hvA]
        rfl
      rw [← hvB]
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
    refine Ideal.mem_span_singleton'.mpr
      ⟨(algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) ^ (p - 1) * ↑(vA⁻¹), ?_⟩
    calc ((algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) ^ (p - 1) * ↑(vA⁻¹)) *
          algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)
        = (algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) ^ (p - 1) *
            (↑(vA⁻¹) * algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) := by ring
      _ = (algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) ^ (p - 1) *
            (algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0) * ↑(vA⁻¹)) := by
          rw [mul_comm (↑(vA⁻¹) : Work.DSM4p.lvl Q hgr N) _]
      _ = ((algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) ^ (p - 1) *
            algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) * ↑(vA⁻¹) := by ring
      _ = (algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)) ^ p * ↑(vA⁻¹) := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
      _ = ((p : Work.DSM4p.lvl Q hgr N) * (vA : Work.DSM4p.lvl Q hgr N)) * ↑(vA⁻¹) := by
          rw [hv']
      _ = (p : Work.DSM4p.lvl Q hgr N) := by rw [mul_assoc, Units.mul_inv, mul_one]
  -- ## Assembly
  have h2 : y - Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p r)
      ∈ Ideal.span {algebraMap B (Work.DSM4p.lvl Q hgr N) (Q.ϖ 0)} := hspan hr
  have heq : y = (y - Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p r)) +
      Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr N))
        (WittVector.teichmuller p r) := by ring
  rw [heq]
  exact Ideal.add_mem _ h2 hAr

end Work.DSM4p
