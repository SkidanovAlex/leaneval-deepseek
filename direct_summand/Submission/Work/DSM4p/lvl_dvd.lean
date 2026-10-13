import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSM4p.Lvl
import Submission.Work.DSM4p.lvl_mk_teich_tiltTower
import Submission.Work.DSM4p.exists_mul_eq_pow_of_mul_eq

/-!
# DSM4p — the divisibility `g ∣ p ^ n` in the untilted levels (Route U, step (7))

This module proves step **(7)** of the Route U plan (`Submission/Work/DSM4p/Plan.lean`):

`Work.DSM4p.lvl_dvd`, the `dvd` clause of the frozen node `DSMap.Mix2.area_M4p` at the
*non-completed* untilted levels `lvl Q hgr n`: for every `n` there is `y : lvl Q hgr n` with

  `algebraMap B (lvl Q hgr n) (gr 0) * y = (p : lvl Q hgr n) ^ n`.

## The mathematics

Write `B♭ := PreTilt B p`, `g♭ := tiltTower gr hgr`, `ϖ♭ := tiltTower Q.ϖ Q.root`,
`R_n := lvlP Q hgr n = chartRing g♭ ϖ♭ n ⊆ B♭[1/g♭ 0]` (the characteristic-`p` chart level, a
`B♭`-subalgebra) and `D_n := lvl Q hgr n = untiltOf R_n (algebraMap B♭ R_n)`, with quotient map
`mk : 𝕎(R_n) →+* D_n` and `B`-algebra structure `algebraMap B D_n = untiltOf.algebraMap hθ φ`.

Three ingredients:

1. **The defining relation of the chart generator**, `Work.DSM4p.chartGen_mul_gr` at `k = 0`,
   read inside the subalgebra `R_n`:
   `φ (g♭ 0) * x♭_0(n) = φ ((ϖ♭ 0) ^ n)` where `x♭_0(n) = chartGen g♭ ϖ♭ n 0 ∈ R_n`.
2. **The Teichmüller dictionary** `Work.DSM4p.lvl_mk_teich_tiltTower` (which is
   `Work.DSM5c.Eta.U.teich_algebraMap` composed with `Work.DSM4p.untilt_tiltTower`, i.e.
   `♯ (tiltTower r hr k) = r k`): for a compatible system `r`,
   `mk (teichmuller p (φ (tiltTower r hr k))) = algebraMap B D_n (r k)`.  Applying it to `r = gr`
   and, after peeling off the powers (`mk` and `teichmuller` are multiplicative) to
   `r = Q.ϖ`, turns (1) into
   `algebraMap (gr 0) * mk (teich (x♭_0(n))) = algebraMap (Q.ϖ 0) ^ n` in `D_n`.
3. **The perfectoid relation** `Q.ϖ 0 ^ p = p · v` with `v : Bˣ` (`DSMap.PerfectoidData.unit`):
   transporting it along `algebraMap B D_n` gives `(p : D_n) = c * w ^ p` with
   `c := algebraMap (↑v⁻¹)` and `w := algebraMap (Q.ϖ 0)`.  Then
   `(p : D_n) ^ n = c ^ n * (w ^ n) ^ p = c ^ n * (a * z) ^ p = a * (c ^ n * a ^ (p-1) * z ^ p)`
   where `a := algebraMap (gr 0)`, `z := mk (teich (x♭_0(n)))`, which is the desired witness —
   the elementary factor-extraction lemma `Work.DSM4p.exists_mul_eq_pow_of_mul_eq` of the sibling
   module.

The only place where the chart presentation of `lvlP` enters is ingredient 1; everything else is
the functoriality of the untilt with respect to its `B♭`-algebra structure.
-/

set_option linter.style.haveILetI false

namespace Work.DSM4p

universe a

/-- **`g ∣ p ^ n` in the untilted level**: the divisibility clause of the Riemann extension tower
at the level `lvl Q hgr n` (Route U plan, step (7)). -/
theorem lvl_dvd {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) {gr : ℕ → B} (hgr : Work.DSM4p.IsRootSystem p gr) (n : ℕ) :
    ∃ y : Work.DSM4p.lvl Q hgr n,
      algebraMap B (Work.DSM4p.lvl Q hgr n) (gr 0) * y = (p : Work.DSM4p.lvl Q hgr n) ^ n := by
  -- The defining relation of the chart generator `x♭_0(n)`, read inside the subalgebra
  -- `R_n = lvlP Q hgr n` (the tilde is the structure map `B♭ → R_n`).
  have hrel : (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n)
        (Work.DSM4p.tiltTower gr hgr 0)) *
      (⟨Work.DSM4p.chartGen (Work.DSM4p.tiltTower_isRootSystem gr hgr)
          (Work.DSM4p.tiltTower Q.ϖ Q.root) n 0,
        Work.DSM4p.chartGen_mem (Work.DSM4p.tiltTower_isRootSystem gr hgr)
          (Work.DSM4p.tiltTower Q.ϖ Q.root) n 0⟩ : Work.DSM4p.lvlP Q hgr n)
      = algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n)
          ((Work.DSM4p.tiltTower Q.ϖ Q.root 0) ^ n) := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    exact Work.DSM4p.chartGen_mul_gr (Work.DSM4p.tiltTower_isRootSystem gr hgr)
      (Work.DSM4p.tiltTower Q.ϖ Q.root) n 0
  -- The Teichmüller avatar of `g = gr 0` (the `k = 0` case of the Teichmüller dictionary).
  have h2 := Work.DSM4p.lvl_mk_teich_tiltTower Q hgr n hgr 0
  -- The Teichmüller avatar of `ϖ_0 ^ n`: peel the powers off, then apply the dictionary.
  have h3 : (Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n)))
      (WittVector.teichmuller p (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n)
        ((Work.DSM4p.tiltTower Q.ϖ Q.root 0) ^ n)))
      = (algebraMap B (Work.DSM4p.lvl Q hgr n) (Q.ϖ 0)) ^ n := by
    rw [map_pow, map_pow, map_pow]
    exact congrArg (fun z => z ^ n)
      (Work.DSM4p.lvl_mk_teich_tiltTower Q hgr n Q.root 0)
  -- The avatar of the chart relation in `D_n = lvl Q hgr n`.
  have hz : algebraMap B (Work.DSM4p.lvl Q hgr n) (gr 0) *
      (Work.DSM5c.untiltOf.mk (p := p) (W := B)
        (algebraMap (PreTilt B p) (Work.DSM4p.lvlP Q hgr n))
        (WittVector.teichmuller p
          (⟨Work.DSM4p.chartGen (Work.DSM4p.tiltTower_isRootSystem gr hgr)
              (Work.DSM4p.tiltTower Q.ϖ Q.root) n 0,
            Work.DSM4p.chartGen_mem (Work.DSM4p.tiltTower_isRootSystem gr hgr)
              (Work.DSM4p.tiltTower Q.ϖ Q.root) n 0⟩ : Work.DSM4p.lvlP Q hgr n)))
      = (algebraMap B (Work.DSM4p.lvl Q hgr n) (Q.ϖ 0)) ^ n := by
    rw [← h2, ← h3, ← map_mul, ← map_mul]
    rw [hrel]
  -- The perfectoid relation `ϖ_0 ^ p = p · v`, transported to `D_n`.
  obtain ⟨v, hv⟩ := Q.unit
  have hcB : ((↑v⁻¹ : B)) * (Q.ϖ 0) ^ p = (p : B) := by
    calc (↑(v⁻¹) : B) * (Q.ϖ 0) ^ p
        = (↑(v⁻¹) : B) * ((p : B) * (v : B)) := by rw [hv]
      _ = (p : B) * ((↑(v⁻¹) : B) * (v : B)) := by ring
      _ = (p : B) := by rw [Units.inv_mul, mul_one]
  have hpc : (p : Work.DSM4p.lvl Q hgr n)
      = algebraMap B (Work.DSM4p.lvl Q hgr n) ↑(v⁻¹)
        * (algebraMap B (Work.DSM4p.lvl Q hgr n) (Q.ϖ 0)) ^ p := by
    rw [← map_natCast (algebraMap B (Work.DSM4p.lvl Q hgr n)) p, ← hcB, map_mul, map_pow]
  -- Elementary factor extraction: `a * z = w ^ n` and `p = c * w ^ p` give `a ∣ p ^ n`.
  exact Work.DSM4p.exists_mul_eq_pow_of_mul_eq (p := p) (n := n)
    (Fact.out : p.Prime).one_le hz hpc

end Work.DSM4p
