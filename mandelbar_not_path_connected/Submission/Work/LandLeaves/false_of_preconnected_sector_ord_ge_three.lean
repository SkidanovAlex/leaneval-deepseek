import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology

/-! ## The algebraic core: an orbit of a root of unity of order `≥ 3` is not in a half-plane

If `ζ` has finite multiplicative order `≥ 3` and `w ≠ 0`, then the orbit `k ↦ ζ ^ k * w` cannot
lie in the closed half-plane `{u : u.re ≤ 0}`.

The proof averages the `m = orderOf ζ` inequalities.  Since `ζ ^ m = 1` and `ζ ≠ 1`, the geometric
sum `∑_{k < m} ζ ^ k` vanishes; hence

`∑_{k < m} (ζ ^ k * w).re = ((∑_{k < m} ζ ^ k) * w).re = 0`,

a sum of nonpositive terms, so *every* term is `0`.  In particular `w` and `ζ * w` are purely
imaginary.  As `w ≠ 0` this forces `ζ.im = 0`, i.e. `ζ` is real; then `ζ ^ 2 = 1` (from `ζ` real,
`‖ζ‖ = 1`) so `orderOf ζ ∣ 2`, contradicting `3 ≤ orderOf ζ`.

This is the reusable heart of `false_of_preconnected_sector_ord_ge_three`. -/
theorem false_of_orbit_re_nonpos {ζ w : ℂ} (hζ1 : ζ ≠ 1) (hw : w ≠ 0)
    (hord : 3 ≤ orderOf ζ) (h : ∀ k, k < orderOf ζ → (ζ ^ k * w).re ≤ 0) : False := by
  set m := orderOf ζ with hm
  have hmne : m ≠ 0 := by omega
  have hζm : ζ ^ m = 1 := by rw [hm]; exact pow_orderOf_eq_one ζ
  -- the geometric sum `∑_{k < m} ζ ^ k` vanishes
  have hgeom : ∑ k ∈ Finset.range m, ζ ^ k = 0 := by
    rw [geom_sum_eq hζ1 m, hζm, sub_self, zero_div]
  -- hence the sum of the real parts vanishes
  have hsum : ∑ k ∈ Finset.range m, ((ζ ^ k) * w).re = 0 := by
    rw [← Complex.re_sum (Finset.range m) (fun k => ζ ^ k * w)]
    rw [← Finset.sum_mul]
    rw [hgeom, zero_mul, Complex.zero_re]
  have hle : ∀ k ∈ Finset.range m, ((ζ ^ k) * w).re ≤ 0 := by
    intro k hk
    exact h k (by rw [hm]; exact Finset.mem_range.mp hk)
  -- a sum of nonpositive terms which is `0` has all terms `0`
  have hall : ∀ k ∈ Finset.range m, ((ζ ^ k) * w).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (s := Finset.range m)
      (f := fun k => ((ζ ^ k) * w).re) hle).mp hsum
  have hw0 : w.re = 0 := by
    have := hall 0 (Finset.mem_range.mpr (by omega))
    simpa using this
  have hζw0 : (ζ * w).re = 0 := by
    have := hall 1 (Finset.mem_range.mpr (by omega))
    simpa using this
  -- `w ≠ 0` is purely imaginary, so `ζ` is real
  have hwim : w.im ≠ 0 := by
    intro h0
    exact hw (Complex.ext (by simpa using hw0) (by simpa using h0))
  have hζim : ζ.im = 0 := by
    have h1 : ζ.re * w.re - ζ.im * w.im = 0 := by
      rw [← Complex.mul_re]; exact hζw0
    have h2 : ζ.im * w.im = 0 := by rw [hw0] at h1; linarith
    exact (mul_eq_zero.mp h2).resolve_right hwim
  have hζeq : ζ = ↑ζ.re := Complex.ext (by simp) (by simp [hζim])
  -- `ζ` is a unit complex number, hence `ζ ^ 2 = 1`
  have hnorm : ‖ζ‖ = 1 := by
    have h' : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, hζm, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hmne).mp h'
  have hζ2 : ζ ^ 2 = 1 := by
    have hns : Complex.normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
    rw [Complex.normSq_apply] at hns
    have hre : ζ.re ^ 2 = 1 := by nlinarith [hns, hζim]
    rw [hζeq, ← Complex.ofReal_pow, hre, Complex.ofReal_one]
  -- so `orderOf ζ ∣ 2`, contradicting `3 ≤ orderOf ζ`
  have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hζ2
  have hle2 : orderOf ζ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- No nonempty preconnected set of unit complex numbers can be contained in the sector
`{d : (c * d ^ n).re ≤ 0}` and be invariant under a root of unity `z` with `orderOf (z ^ n) ≥ 3`.
Hint: with `w = c * d^n ≠ 0` (`d ∈ L` has `‖d‖ = 1` and `c ≠ 0`) and `m = orderOf (z ^ n)`, the
points `c * (z^k * d)^n = (z^n)^k * w` for `k < m` are `m ≥ 3` equally spaced nonzero points, whose
arguments cannot all lie in a closed half-plane; alternatively sum the inequalities
`Re ((z^n)^k * w) ≤ 0` over `k < m` to get each term `0`, which forces `w = 0` since `z^n ≠ ±1`. -/
theorem false_of_preconnected_sector_ord_ge_three {n : ℕ} {c z : ℂ} (hc : c ≠ 0)
    (hzn : z ^ n ≠ 1) (hord : 3 ≤ orderOf (z ^ n))
    {L : Set ℂ} (hLpre : IsPreconnected L) (hLne : L.Nonempty)
    (hLsph : L ⊆ Metric.sphere (0 : ℂ) 1)
    (hLsect : ∀ d ∈ L, (c * d ^ n).re ≤ 0) (hLinv : ∀ d ∈ L, z * d ∈ L) : False := by
  obtain ⟨d, hd⟩ := hLne
  -- `d` is a unit vector, so `w := c * d ^ n` is nonzero
  have hd1 : ‖d‖ = 1 := by
    have h := Metric.mem_sphere.mp (hLsph hd)
    simpa [dist_eq_norm] using h
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    norm_num at hd1
  have hw : c * d ^ n ≠ 0 := mul_ne_zero hc (pow_ne_zero n hd0)
  -- the whole `z`-orbit of `d` lies in `L`
  have horb : ∀ k : ℕ, z ^ k * d ∈ L := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
        have h' := hLinv (z ^ k * d) ih
        convert h' using 1
        rw [pow_succ]
        ring
  -- `(z ^ k * d) ^ n = (z ^ n) ^ k * d ^ n`
  have key : ∀ k : ℕ, (z ^ k * d) ^ n = (z ^ n) ^ k * d ^ n := by
    intro k
    have h1 : (z ^ k) ^ n = (z ^ n) ^ k := by
      rw [← pow_mul z k n, Nat.mul_comm k n, pow_mul z n k]
    rw [mul_pow, h1]
  have heq : ∀ k : ℕ, (z ^ n) ^ k * (c * d ^ n) = c * (z ^ k * d) ^ n := by
    intro k
    rw [key k]
    ring
  -- so the orbit of `w = c * d ^ n` under `z ^ n` lies in the sector, and the core applies
  exact false_of_orbit_re_nonpos hzn hw hord
    (fun k _ => by rw [heq k]; exact hLsect _ (horb k))

end Work.LandLeaves
