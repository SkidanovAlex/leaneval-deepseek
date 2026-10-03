import Mathlib
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm

set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The `w ≠ 0`, `Δ ≠ 0`, non-coprime count of *FI* (5.22)

This module only fixes the vocabulary in which `Work.FIArea1.offdiag_delta_ne_wne_le` (and the
lemmas it is assembled from) are stated:

* `WneLhs Pa φ` — the count itself (the left-hand side of the target statement);
* `WnePi Pa` — the set `Π` of common Gaussian prime divisors `π` with `gnorm π > Pz` lying in the
  box `gBox (KZ N)`, over which the union bound runs;
* `WneInner Pa π` — the `π`-th piece of that union bound, which is exactly the summand of
  `Work.FIArea1.offdiag_pi_range_le`.
-/

/-- The left-hand side of `Work.FIArea1.offdiag_delta_ne_wne_le`: the triples `(w, z₁, z₂)` with
`w ≠ 0` in the outer box `gBox (KR M)`, `z₁, z₂` in the polar box (5.14), the pair non-coprime in
`ℤ[i]` and `Δ(z₁,z₂) ≠ 0`, counted with multiplicity `Z(Re wz₁)·Z(Re wz₂)`. -/
def WneLhs (Pa : Work.FITop.Params) (φ : ℝ) : ℝ :=
  ∑ w ∈ (Work.FIPlan.gBox (KR Pa.M)).erase 0,
    ∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
      (if Work.FIPlan.Delta z1 z2 = 0 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))

/-- The index set `Π` of the union bound: the Gaussian primes `π` in the box `gBox (KZ N)` whose
norm exceeds the small-prime cutoff `Pz`.  Every non-coprime pair of points of the polar box has a
common divisor in `Π` (`Work.FIArea1.gauss_prime_common_divisor`, plus the box bound
`gnorm π ≤ 2N ≤ (KZ N)²`). -/
def WnePi (Pa : Work.FITop.Params) : Finset GaussianInt :=
  (Work.FIPlan.gBox (KZ Pa.N)).filter
    (fun π => Prime π ∧ Pa.Pz < Work.FIPlan.gnorm π)

/-- The `π`-th piece of the union bound: the `Δ ≠ 0` pairs both divisible by `π`, counted with
multiplicity `Z(Re wz₁)·Z(Re wz₂)`, the inner variables running over the *larger* set
`Zbox N ⊇ polarSupp Pa φ`.  This is exactly the summand of `Work.FIArea1.offdiag_pi_range_le`. -/
def WneInner (Pa : Work.FITop.Params) (π : GaussianInt) : ℝ :=
  ∑ w ∈ (Work.FIPlan.gBox (KR Pa.M)).erase 0,
    ∑ z1 ∈ Zbox Pa.N, ∑ z2 ∈ Zbox Pa.N,
      (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))

lemma mem_WnePi {Pa : Work.FITop.Params} {π : GaussianInt} :
    π ∈ WnePi Pa ↔ π ∈ Work.FIPlan.gBox (KZ Pa.N) ∧ Prime π
      ∧ Pa.Pz < Work.FIPlan.gnorm π := by
  rw [WnePi, Finset.mem_filter]

lemma WneInner_nonneg (Pa : Work.FITop.Params) (π : GaussianInt) : 0 ≤ WneInner Pa π := by
  rw [WneInner]
  refine Finset.sum_nonneg (fun w _ => Finset.sum_nonneg (fun z1 _ =>
    Finset.sum_nonneg (fun z2 _ => ?_)))
  by_cases h : Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2)
  · rw [if_pos h]
  · rw [if_neg h]; positivity

/-! ## Elementary facts about the polar box (5.14) -/

/-- `θ ≤ 1`: the polar box (5.14) is contained in the dyadic annulus `N < |z|² ≤ 2N`. -/
lemma wne_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx0 : (0:ℝ) < (Pa.x : ℝ) := by
    have : (0:ℕ) < Pa.x := by linarith [Pa.hx]
    exact_mod_cast this
  have hlog1 : (1:ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le hx0]
    have : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_three]
  have hA' : (0:ℝ) ≤ Pa.A' := by
    have h1 := Pa.hA'
    have hA0 : (0:ℝ) ≤ Pa.A := le_of_lt Pa.hA
    nlinarith [show (0:ℝ) < (2:ℝ)^(20:ℕ) by positivity]
  calc (Real.log (Pa.x : ℝ)) ^ (-Pa.A') ≤ (Real.log (Pa.x : ℝ)) ^ (0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    _ = 1 := Real.rpow_zero _

/-- `gnorm z ≤ 2N` for a point of the polar box (5.14). -/
lemma wne_gnorm_le_two_N {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
  rw [mem_polarSupp] at hz
  have h1 := hz.2.1.2.2.1
  have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by
    have := wne_theta_le_one Pa
    nlinarith [Pa.hN1]
  linarith

/-- The norm of a primary Gaussian integer is odd. -/
lemma wne_gnorm_odd_of_primary {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  rw [gnorm_coords]
  refine h.1.natAbs.pow.add_even ?_
  obtain ⟨k, hk⟩ := h.2.1.natAbs
  exact ⟨2 * k ^ 2, by rw [hk]; ring⟩

/-- A point of the polar box (5.14) is primitive (`(z, z̄) = 1`). -/
lemma wne_isPrimitive_of_polarSupp {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) : Work.FIPlan.IsPrimitive z := by
  rw [mem_polarSupp] at hz
  exact Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm hz.2.2.1
    (wne_gnorm_odd_of_primary hz.2.1.1)

/-- A point of the polar box (5.14) lies in `Zbox N`. -/
lemma wne_polarSupp_subset_Zbox (Pa : Work.FITop.Params) (φ : ℝ) :
    polarSupp Pa φ ⊆ Zbox Pa.N := by
  intro z hz
  rw [mem_polarSupp] at hz
  obtain ⟨hzbox, hpolar, hsq, hns⟩ := hz
  have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := wne_gnorm_le_two_N (by
    rw [mem_polarSupp]; exact ⟨hzbox, hpolar, hsq, hns⟩)
  have hcoord : (Work.FIPlan.gnorm z : ℝ) = (z.re.natAbs : ℝ)^2 + (z.im.natAbs : ℝ)^2 := by
    rw [gnorm_coords]; push_cast; ring
  rw [mem_Zbox_iff]
  refine ⟨?_, ?_, hpolar.2.1, hgn⟩
  · rw [Work.FIArea2.mem_gBox_iff]
    have hKZ : KZ Pa.N = ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := rfl
    constructor
    · rw [Finset.mem_Icc]
      have h1 : ((z.re.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
        have h2 : ((z.re.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
          nlinarith [hcoord, sq_nonneg (z.im.natAbs : ℝ), hgn]
        have h3 : ((z.re.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (z.re.natAbs : ℝ))]
          exact Real.sqrt_le_sqrt h2
        exact h3.trans (Nat.le_ceil _)
      have h4 : z.re.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1
      have h7 : |z.re| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h4
      simp only [hKZ]
      exact abs_le.mp h7
    · rw [Finset.mem_Icc]
      have h1 : ((z.im.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
        have h2 : ((z.im.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
          nlinarith [hcoord, sq_nonneg (z.re.natAbs : ℝ), hgn]
        have h3 : ((z.im.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (z.im.natAbs : ℝ))]
          exact Real.sqrt_le_sqrt h2
        exact h3.trans (Nat.le_ceil _)
      have h4 : z.im.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1
      have h7 : |z.im| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h4
      simp only [hKZ]
      exact abs_le.mp h7
  · exact wne_isPrimitive_of_polarSupp (by rw [mem_polarSupp]; exact ⟨hzbox, hpolar, hsq, hns⟩)

/-- `gnorm z ≤ 2N` for a point of `Zbox N`. -/
lemma wne_gnorm_le_of_mem_Zbox {N : ℝ} {z : GaussianInt} (hz : z ∈ Zbox N) :
    (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N := (mem_Zbox_iff.mp hz).2.2.2

end

end Work.FIArea1
