/-
# Area 4 / HB §11: `mollSeries = L(w,χ) · F(w)`

`mollSeries q U V W χ w = Σ_n Ψ(n)Θ(n)χ(n) n^{-w}` (with `Ψ(n) = Σ_{d|n} ψ_d`,
`Θ(n) = Σ_{e|n} θ_e`) is the Dirichlet series of the mollified coefficients, while `lcmF` is the
finite weight `F(w) = Σ_{v ≤ V, e ≤ W} ψ_v θ_e χ([v,e]) [v,e]^{-w}` of HB §11 (11.8).

Because `χ` is completely multiplicative, expanding the two divisor sums and re-indexing
`n = [v,e]·m` gives
`Σ_n Ψ(n)Θ(n)χ(n)n^{-w} = Σ_{v,e} ψ_v θ_e χ([v,e])[v,e]^{-w} · Σ_m χ(m)m^{-w}`,
and the inner sum is exactly `L(w,χ)`.  This file assembles that identity from the per-`(v,e)`
computation and the finite re-indexing lemmas.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmSetup
import Submission.Work.LinnikAreas.Density4.tsum_ite_dvd
import Submission.Work.LinnikAreas.Density4.chi_LFunction_tsum
import Submission.Work.LinnikAreas.Density4.psiS_Icc_eq
import Submission.Work.LinnikAreas.Density4.thetaS_Icc_eq
import Submission.Work.LinnikAreas.Density4.summable_mollInner

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

/-- Distributing two finite sums and the scalar factors `c`, `d`. -/
private lemma mul_sumsum (s t : Finset ℕ) (fx gy : ℕ → ℂ) (c d : ℂ) :
    (∑ x ∈ s, fx x) * (∑ y ∈ t, gy y) * c * d
      = ∑ x ∈ s, ∑ y ∈ t, fx x * gy y * c * d := by
  have h1 : (∑ x ∈ s, fx x) * (∑ y ∈ t, gy y) = ∑ x ∈ s, ∑ y ∈ t, fx x * gy y := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.mul_sum ..
  calc (∑ x ∈ s, fx x) * (∑ y ∈ t, gy y) * c * d
      = ((∑ x ∈ s, fx x) * (∑ y ∈ t, gy y)) * (c * d) := by ring
    _ = (∑ x ∈ s, ∑ y ∈ t, fx x * gy y) * (c * d) := by rw [h1]
    _ = ∑ x ∈ s, (∑ y ∈ t, fx x * gy y) * (c * d) :=
          Finset.sum_mul s (fun x => ∑ y ∈ t, fx x * gy y) (c * d)
    _ = ∑ x ∈ s, ∑ y ∈ t, (fx x * gy y) * (c * d) := by
          exact Finset.sum_congr rfl fun x _ => Finset.sum_mul t (fun y => fx x * gy y) (c * d)
    _ = ∑ x ∈ s, ∑ y ∈ t, fx x * gy y * c * d := by
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **The per-`(d,e)` computation.**  For `d,e ≥ 1` the `n`-series of the localized coefficient
`[d|n]ψ_d · [e|n]θ_e · χ(n)n^{-w}` re-indexes over the multiples `l = [d,e]` and factors through
the complete multiplicativity of `χ` as `ψ_d θ_e χ([d,e])[d,e]^{-w} · L(w,χ)`. -/
private theorem mollInner_tsum_aux (q : ℕ) [NeZero q] {U V W : ℝ} (χ : DirichletCharacter ℂ q)
    {w : ℂ} (hw : 1 < w.re) {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (∑' n : ℕ, (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
        * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w))
      = (psiM U V d : ℂ) * (thetaM W e : ℂ) * (χ ((Nat.lcm d e : ℕ) : ZMod q))
        * (((Nat.lcm d e : ℕ) : ℂ) ^ (-w)) * DirichletCharacter.LFunction χ w := by
  set l : ℕ := Nat.lcm d e with hl
  have hlpos : 0 < l := by rw [hl]; exact Nat.lcm_pos (by omega) (by omega)
  have hkey : ∀ n : ℕ,
      (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
        * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w)
      = ((psiM U V d : ℂ) * (thetaM W e : ℂ))
          * ((if l ∣ n then (1 : ℂ) else 0) * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w))) := by
    intro n
    by_cases hdl : d ∣ n <;> by_cases hel : e ∣ n
    · have hll : l ∣ n := by rw [hl]; exact Nat.lcm_dvd hdl hel
      rw [if_pos hdl, if_pos hel, if_pos hll]; ring
    · have hll : ¬ l ∣ n := by
        intro h; rw [hl] at h; exact hel (dvd_trans (Nat.dvd_lcm_right d e) h)
      rw [if_pos hdl, if_neg hel, if_neg hll]; ring
    · have hll : ¬ l ∣ n := by
        intro h; rw [hl] at h; exact hdl (dvd_trans (Nat.dvd_lcm_left d e) h)
      rw [if_neg hdl, if_neg hll]; ring
    · have hll : ¬ l ∣ n := by
        intro h; rw [hl] at h; exact hdl (dvd_trans (Nat.dvd_lcm_left d e) h)
      rw [if_neg hdl, if_neg hll]; ring
  have h1 : (∑' n : ℕ, (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
        * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w))
      = ((psiM U V d : ℂ) * (thetaM W e : ℂ)) * (∑' n : ℕ,
          (if l ∣ n then (1 : ℂ) else 0) * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w))) := by
    rw [tsum_congr hkey, tsum_mul_left]
  have h2 : (∑' n : ℕ, (if l ∣ n then (1 : ℂ) else 0) * ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w)))
      = ∑' n : ℕ, (if l ∣ n then ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w)) else 0) := by
    refine tsum_congr fun n => ?_
    by_cases h : l ∣ n <;> simp [h]
  have h3 : (∑' n : ℕ, (if l ∣ n then ((χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w)) else 0))
      = ∑' m : ℕ, (χ ((l * m : ℕ) : ZMod q) : ℂ) * ((l * m : ℕ) : ℂ) ^ (-w) :=
    tsum_ite_dvd hlpos _
  have h4 : (∑' m : ℕ, (χ ((l * m : ℕ) : ZMod q) : ℂ) * ((l * m : ℕ) : ℂ) ^ (-w))
      = ((χ ((l : ℕ) : ZMod q) : ℂ) * (((l : ℕ) : ℂ) ^ (-w)))
          * DirichletCharacter.LFunction χ w := by
    have hpt : ∀ m : ℕ, (χ ((l * m : ℕ) : ZMod q) : ℂ) * ((l * m : ℕ) : ℂ) ^ (-w)
        = ((χ ((l : ℕ) : ZMod q) : ℂ) * (((l : ℕ) : ℂ) ^ (-w)))
            * ((χ ((m : ℕ) : ZMod q) : ℂ) * ((m : ℕ) : ℂ) ^ (-w)) := by
      intro m
      have hchi : (χ ((l * m : ℕ) : ZMod q) : ℂ)
          = (χ ((l : ℕ) : ZMod q) : ℂ) * (χ ((m : ℕ) : ZMod q) : ℂ) := by
        rw [Nat.cast_mul, map_mul]
      have hcp : ((l * m : ℕ) : ℂ) ^ (-w)
          = (((l : ℕ) : ℂ) ^ (-w)) * (((m : ℕ) : ℂ) ^ (-w)) := by
        rw [Nat.cast_mul]
        exact Complex.natCast_mul_natCast_cpow l m (-w)
      rw [hchi, hcp]; ring
    rw [tsum_congr hpt, tsum_mul_left, ← chi_LFunction_tsum q χ w hw]
  rw [h1, h2, h3, h4]
  ring

/-- **HB §11: the mollified Dirichlet series factors as `L(w,χ) · F(w)`.** -/
theorem mollSeries_eq (q : ℕ) [NeZero q] {U V W : ℝ} (hU : 0 < U) (hUV : U ≤ V) (hW : 0 < W)
    (χ : DirichletCharacter ℂ q) (w : ℂ) (hw : 1 < w.re) :
    mollSeries q U V W χ w = DirichletCharacter.LFunction χ w * lcmF q U V W χ w := by
  have hwne : w ≠ 0 := by
    intro h
    have h2 : w.re = 0 := by rw [h]; simp
    rw [h2] at hw
    norm_num at hw
  have hzw : (0 : ℂ) ^ (-w) = 0 := Complex.zero_cpow (neg_ne_zero.mpr hwne)
  -- the expansion of the summand into the two divisor sums
  have hpoint : ∀ n : ℕ,
      mollCoeff q U V W χ n * (n : ℂ) ^ (-w)
        = ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
              * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w) := by
    intro n
    rcases eq_or_ne n 0 with h0 | h0
    · subst h0
      simp [mollCoeff, psiS_zero, hzw]
    · rw [mollCoeff, psiS_Icc_eq U V hU hUV n h0, thetaS_Icc_eq W n h0]
      exact mul_sumsum _ _ _ _ _ _
  have hmoll : mollSeries q U V W χ w
      = ∑' n : ℕ, ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
              * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w) := by
    rw [mollSeries]
    exact tsum_congr hpoint
  -- pull the finite `(d,e)`-sums out of the `tsum` (absolute convergence in `n`)
  have hsum1 : (∑' n : ℕ, ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
              * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w))
      = ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑' n : ℕ, ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
              * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w) := by
    refine Summable.tsum_finsetSum (fun d _ => ?_)
    exact summable_sum (fun e _ => summable_mollInner q χ hw d e)
  calc mollSeries q U V W χ w
      = ∑' n : ℕ, ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
              * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w) := hmoll
    _ = ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑' n : ℕ, ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (if d ∣ n then (psiM U V d : ℂ) else 0) * (if e ∣ n then (thetaM W e : ℂ) else 0)
              * (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-w) := hsum1
    _ = ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (psiM U V d : ℂ) * (thetaM W e : ℂ) * (χ ((Nat.lcm d e : ℕ) : ZMod q))
              * (((Nat.lcm d e : ℕ) : ℂ) ^ (-w)) * DirichletCharacter.LFunction χ w := by
          refine Finset.sum_congr rfl fun d hd => ?_
          refine (Summable.tsum_finsetSum (fun e _ => summable_mollInner q χ hw d e)).trans ?_
          refine Finset.sum_congr rfl fun e he => ?_
          exact mollInner_tsum_aux q χ hw (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    _ = DirichletCharacter.LFunction χ w * ∑ d ∈ Finset.Icc 1 (Nat.ceil V),
            ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
            (psiM U V d : ℂ) * (thetaM W e : ℂ) * (χ ((Nat.lcm d e : ℕ) : ZMod q))
              * (((Nat.lcm d e : ℕ) : ℂ) ^ (-w)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
    _ = DirichletCharacter.LFunction χ w * lcmF q U V W χ w := by rw [lcmF]

end Work.LinnikAreas.Density4
