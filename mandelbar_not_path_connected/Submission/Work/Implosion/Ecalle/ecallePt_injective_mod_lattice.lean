import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Ecalle

open Complex

/-- The Écalle point map `ζ(u) = a·coth(a u)` is injective modulo the period
lattice `(πi/a)ℤ` of the Écalle cylinder: two points `u, v` which are not poles
of `ζ` (i.e. `ecalE a u ≠ 1`, `ecalE a v ≠ 1`) give the same point only if they
differ by an integer multiple of the period `πi/a`.

The proof is the observation that `m_a(ζ(u)) = s = e^{2au}` recovers the
multiplier coordinate: from `ζ(u) = ζ(v)` we get `e^{2au} = e^{2av}`, hence
`e^{2a(u−v)} = 1`, i.e. `u − v ∈ (πi/a)ℤ`. -/
theorem ecallePt_injective_mod_lattice (a u v : ℂ) (ha : a ≠ 0)
    (hu : ecalE a u ≠ 1) (hv : ecalE a v ≠ 1) (h : ecalPt a u = ecalPt a v) :
    ∃ k : ℤ, u = v + k * (Real.pi * I / a) := by
  -- The Möbius coordinate recovers the multiplier: `m_a(ζ(u)) = e^{2au}`.
  have hE : ecalE a u = ecalE a v := by
    rw [← mobius_ecalPt a u ha hu, h, mobius_ecalPt a v ha hv]
  have hE' : Complex.exp (2 * a * u) = Complex.exp (2 * a * v) := hE
  -- Hence `e^{2a(u−v)} = 1`, so `u − v` lies in the period lattice.
  have hmem : u - v ∈ periodLattice a := by
    show ecalE a (u - v) = 1
    rw [ecalE, show (2 : ℂ) * a * (u - v) = 2 * a * u - 2 * a * v by ring,
        Complex.exp_sub, hE', div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := (mem_periodLattice_iff a (u - v) ha).1 hmem
  refine ⟨n, ?_⟩
  rw [← hn]; ring

end Work.Implosion.Ecalle
