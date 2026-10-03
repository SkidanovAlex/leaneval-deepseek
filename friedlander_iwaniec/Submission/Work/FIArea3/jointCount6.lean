import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea3.JointCount.card_filter_le_le_pieces
import Submission.Work.FIArea3.JointCount.card_jointPieceLat_le
import Submission.Work.FIArea3.JointCount.maxPieceFinset_card_le
import Submission.Work.FIArea3.JointCount.GaussPieceMax_arith
import Submission.Work.FIArea3.JointCount.content_dvd_gnorm

namespace Work.FIArea3

open Finset Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-!
# `Work.FIArea3.jointCount6` — the joint count with the sharp `1 / lcm(d,e)` main term

The number of points of the polar box with `d ∣ |z|²` and `e ∣ Δ(z₁,z)` is at most

  `π u² · (τ(d)·gcd(d,e))/(d·e) + 80 u · τ(d)/√d + τ(d)`,   `u = θ√N`,  `τ(d) = d.divisors.card`.

Compared with `JointCount.card_filter_le_le_arith` (which has `τ(d)/d` in the main term) the gain
is the factor `gcd(d,e)/e = 1/lcm(d,e)`: for a maximal piece generator `w` of `{z | d ∣ |z|²}` the
joint piece lattice `jointPieceLat z₁ w e` has index `≥ lcm(d,e)`.

That index estimate is the only new input.  Writing `c = |w|²`, the index is
`c · (e / gcd(e, t))` with `t = gcd(|Re(z̄₁w)|, |Im(z̄₁w)|)`, and the divisibilities `d ∣ c` and
`t ∣ c` (the latter is `JointCount.content_dvd_gnorm`, using that `z₁` is primitive) give
`d · gcd(e,t) ≤ c · gcd(d,e)`, whence `lcm(d,e) ≤ c · (e / gcd(e,t))`.
-/

/-- **The pure `ℕ` gcd inequality.**  If `d ∣ M` and `t ∣ M` then `d · gcd(e,t) ≤ M · gcd(d,e)`.

Indeed `gcd(e,t) ∣ gcd(e,M)`, and for `M = d·q` one has
`gcd(e,d·q) ∣ gcd(e·q, d·q) = q · gcd(e,d) ≤ q · gcd(d,e)`. -/
lemma nat_key (d M t e : ℕ) (hM : 0 < M) (hdM : d ∣ M) (htM : t ∣ M) :
    d * Nat.gcd e t ≤ M * Nat.gcd d e := by
  obtain ⟨q, rfl⟩ := hdM
  have h1 : Nat.gcd e t ∣ Nat.gcd e (d * q) :=
    Nat.dvd_gcd (Nat.gcd_dvd_left e t) ((Nat.gcd_dvd_right e t).trans htM)
  have h2 : Nat.gcd e t ≤ Nat.gcd e (d * q) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right e hM) h1
  have h3 : Nat.gcd e (d * q) ≤ q * Nat.gcd d e := by
    have hdiv : Nat.gcd e (d * q) ∣ Nat.gcd (e * q) (d * q) :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left e (d * q)).trans (dvd_mul_right e q))
        (Nat.gcd_dvd_right e (d * q))
    have hpos : 0 < Nat.gcd (e * q) (d * q) := Nat.gcd_pos_of_pos_right (e * q) hM
    calc Nat.gcd e (d * q) ≤ Nat.gcd (e * q) (d * q) := Nat.le_of_dvd hpos hdiv
      _ = Nat.gcd e d * q := Nat.gcd_mul_right e q d
      _ = q * Nat.gcd d e := by rw [Nat.gcd_comm, Nat.mul_comm]
  calc d * Nat.gcd e t ≤ d * (q * Nat.gcd d e) := Nat.mul_le_mul_left d (le_trans h2 h3)
    _ = d * q * Nat.gcd d e := by ring

/-- For a maximal piece generator `w` of `d` and a primitive `z₁`, the index of the joint piece
lattice `jointPieceLat z₁ w e` is at least `lcm(d,e)`. -/
lemma index_ge_lcm (z₁ : GaussianInt) (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (hcop : Nat.Coprime z₁.re.natAbs z₁.im.natAbs) {w : GaussianInt}
    (hw : w ∈ Work.FIArea3.JointCount.maxPieceFinset d) :
    Nat.lcm d e ≤ (Work.FIArea3.JointCount.jointPieceLat z₁ w e).index := by
  have hS := Work.FIArea3.JointCount.IsSPt_of_mem_maxPieceFinset d hd hw
  have hdM : d ∣ Work.FIPlan.gnorm w := hS.2
  have hMpos : 0 < Work.FIPlan.gnorm w :=
    lt_of_lt_of_le (by omega : 0 < d) ((Work.FIArea3.JointCount.maxPieceFinset_card_le d hd).2 w hw)
  have htM : Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs ∣ Work.FIPlan.gnorm w :=
    Work.FIArea3.JointCount.content_dvd_gnorm z₁ w hcop
  have hw0 : w ≠ 0 := Work.FIArea3.JointCount.GaussPieceMax_ne_zero d hd
    (Finset.mem_filter.mp hw).2.1
  rw [Work.FIArea3.JointCount.index_jointPieceLat z₁ w e he hw0]
  set t := Nat.gcd (star z₁ * w).im.natAbs (star z₁ * w).re.natAbs with htdef
  set g := Nat.gcd e t with hgdef
  have hkey : d * g ≤ Work.FIPlan.gnorm w * Nat.gcd d e :=
    nat_key d (Work.FIPlan.gnorm w) t e hMpos hdM htM
  have hgpos : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_left t he
  have hgdvd : g ∣ e := by rw [hgdef]; exact Nat.gcd_dvd_left e t
  have hstep : Nat.lcm d e * g ≤ Work.FIPlan.gnorm w * e := by
    apply Nat.le_of_mul_le_mul_right (c := Nat.gcd d e) _ (Nat.gcd_pos_of_pos_left e hd)
    calc Nat.lcm d e * g * Nat.gcd d e = (Nat.gcd d e * Nat.lcm d e) * g := by ring
      _ = d * e * g := by rw [Nat.gcd_mul_lcm]
      _ = e * (d * g) := by ring
      _ ≤ e * (Work.FIPlan.gnorm w * Nat.gcd d e) := Nat.mul_le_mul_left e hkey
      _ = Work.FIPlan.gnorm w * e * Nat.gcd d e := by ring
  have hmul : Work.FIPlan.gnorm w * (e / g) * g = Work.FIPlan.gnorm w * e := by
    rw [mul_assoc, Nat.mul_comm (e / g) g, Nat.mul_div_cancel' hgdvd]
  have hfin : Nat.lcm d e ≤ Work.FIPlan.gnorm w * (e / g) := by
    apply Nat.le_of_mul_le_mul_right (c := g) _ hgpos
    rw [hmul]; exact hstep
  exact hfin

/-- Each maximal piece contributes at most `π u²/lcm(d,e) + 80 u/√d + 1` points of the polar box. -/
lemma card_jointPieceBox_le_lcm (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt) (d e : ℕ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hcop : Nat.Coprime z₁.re.natAbs z₁.im.natAbs) {w : GaussianInt}
    (hw : w ∈ Work.FIArea3.JointCount.maxPieceFinset d) :
    ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / (Nat.lcm d e : ℝ)
        + 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt (d : ℝ) + 1 := by
  have hdw : d ≤ Work.FIPlan.gnorm w :=
    (Work.FIArea3.JointCount.maxPieceFinset_card_le d hd).2 w hw
  have hw0 : w ≠ 0 := Work.FIArea3.JointCount.GaussPieceMax_ne_zero d hd
    (Finset.mem_filter.mp hw).2.1
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hu0 : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hlcm0 : (0 : ℝ) < (Nat.lcm d e : ℝ) := by
    exact_mod_cast Nat.lcm_pos (by omega) (by omega)
  have hidx : (Nat.lcm d e : ℝ) ≤ ((Work.FIArea3.JointCount.jointPieceLat z₁ w e).index : ℝ) := by
    exact_mod_cast index_ge_lcm z₁ d e hd he hcop hw
  have hbase := Work.FIArea3.JointCount.card_jointPieceLat_le Pa φ z₁ w e hw0 he
  have h1 : Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
        / ((Work.FIArea3.JointCount.jointPieceLat z₁ w e).index : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 / (Nat.lcm d e : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hlcm0 hidx
  have hgw : (d : ℝ) ≤ (Work.FIPlan.gnorm w : ℝ) := by exact_mod_cast hdw
  have h2 : 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt ((Work.FIPlan.gnorm w : ℝ))
      ≤ 80 * (Pa.θ * Real.sqrt Pa.N) / Real.sqrt (d : ℝ) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hu0) (Real.sqrt_pos.mpr hd0)
      (Real.sqrt_le_sqrt hgw)
  linarith

lemma jointCount6 (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt) (d e : ℕ)
    (hz₁ : z₁ ∈ Work.FIArea3.polarBoxFinset Pa φ)
    (hcop : Nat.Coprime z₁.re.natAbs z₁.im.natAbs) (hd : 1 ≤ d) (he : 1 ≤ e) :
    (((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => d ∣ Work.FIPlan.gnorm z ∧ e ∣ Work.FIPlan.absDelta z₁ z)).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2
            * (((d.divisors.card : ℝ) * ((Nat.gcd d e : ℕ) : ℝ)) / ((d : ℝ) * (e : ℝ)))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * ((d.divisors.card : ℝ)) / Real.sqrt (d : ℝ)
        + (d.divisors.card : ℝ) := by
  have hLHS : ((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => d ∣ Work.FIPlan.gnorm z ∧ e ∣ Work.FIPlan.absDelta z₁ z)).card
      = (Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card := rfl
  rw [hLHS]
  classical
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  set L : ℝ := (Nat.lcm d e : ℝ) with hL
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast Nat.lcm_pos (by omega) (by omega)
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  set C : ℝ := Real.pi * u ^ 2 / L + 80 * u / Real.sqrt (d : ℝ) + 1 with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have h1 : 0 ≤ Real.pi * u ^ 2 / L := div_nonneg (by positivity) hL0.le
    have h2 : 0 ≤ 80 * u / Real.sqrt (d : ℝ) :=
      div_nonneg (by linarith) (Real.sqrt_pos.mpr hd0).le
    linarith
  -- Step 1: the box is covered by the maximal pieces.
  have h1 : ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ ∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
          ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ) :=
    Work.FIArea3.JointCount.card_filter_le_le_pieces Pa φ z₁ d e hd
  -- Step 2: each piece contributes at most `C`.
  have h2 : (∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
        ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ))
      ≤ ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C := by
    calc (∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
          ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ))
        ≤ ∑ _w ∈ Work.FIArea3.JointCount.maxPieceFinset d, C := by
          refine Finset.sum_le_sum (fun w hw => ?_)
          have := card_jointPieceBox_le_lcm Pa φ z₁ d e hd he hcop hw
          rw [hC]
          rw [← hu, ← hL] at this
          exact this
      _ = ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 3: there are at most `τ(d)` maximal pieces.
  have h3 : ((Work.FIArea3.JointCount.maxPieceFinset d).card : ℝ) * C
      ≤ ((d.divisors.card : ℝ)) * C :=
    mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Work.FIArea3.JointCount.maxPieceFinset_card_le d hd).1) hC0
  have h4 : ((d.divisors.card : ℝ)) * C
      = Real.pi * u ^ 2
          * (((d.divisors.card : ℝ) * ((Nat.gcd d e : ℕ) : ℝ)) / ((d : ℝ) * (e : ℝ)))
        + 80 * u * ((d.divisors.card : ℝ)) / Real.sqrt (d : ℝ) + (d.divisors.card : ℝ) := by
    have hde : ((Nat.gcd d e : ℕ) : ℝ) * L = (d : ℝ) * (e : ℝ) := by
      rw [hL]; exact_mod_cast Nat.gcd_mul_lcm d e
    have hgcd0 : (0 : ℝ) < (Nat.gcd d e : ℝ) := by
      exact_mod_cast Nat.gcd_pos_of_pos_left e (by omega : 0 < d)
    have hLde : L = (d : ℝ) * (e : ℝ) / ((Nat.gcd d e : ℕ) : ℝ) := by
      rw [eq_div_iff (ne_of_gt hgcd0), mul_comm]
      exact hde
    rw [hC, hLde]
    field_simp
  have hfin : ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ Real.pi * u ^ 2
          * (((d.divisors.card : ℝ) * ((Nat.gcd d e : ℕ) : ℝ)) / ((d : ℝ) * (e : ℝ)))
        + 80 * u * ((d.divisors.card : ℝ)) / Real.sqrt (d : ℝ) + (d.divisors.card : ℝ) := by
    linarith [h1, h2, h3, h4.le, h4.ge]
  exact hfin

end

end Work.FIArea3
