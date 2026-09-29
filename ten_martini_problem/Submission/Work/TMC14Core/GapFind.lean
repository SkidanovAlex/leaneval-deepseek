import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.ratDenomLarge
import Submission.Work.TMC14Core.ratGapEndpoints

/-!
# TMC14Core: the gap-finding argument (ROUTE_LEAD section 4 C14, items 14d and 14g)

This file assembles `P_GapBound` out of the three analytic ingredients of the rational
approximant (`RatIdsFlat`, `RatIdsVariation`, `RatGapBound`) together with the two inputs
they need from the general theory (`P_LEBasics`, `P_BJ`) and the two elementary facts about
the rational union spectrum proved in this chapter (`RatDenomLarge`, `RatGapEndpoints`).

The proof is ROUTE_LEAD 14d + 14g:

* Let `[c1,d1]` be the middle third of `[c,d]`.  `P_IDSSpectrum` + `P_RotBasics` give
  `kappa := N_alpha(d1) - N_alpha(c1) > 0`, and uniform continuity of `(alpha',E) |-> N_alpha'(E)`
  on the compact `[alpha-1,alpha+1] x [c,d]` turns this into `|N_{p/q}(E) - N_alpha(E)| < kappa/4`
  for `E` in `[c,d]` once `|p/q - alpha|` is small enough.
* If the whole middle third lay in `ratSpec p q lam`, `RatIdsVariation` would give
  `N_{p/q}(d1) - N_{p/q}(c1) <= 2/q' <= 2/Q0 <= kappa/4`, contradicting the lower bound
  `kappa/2`.  (`Q0 >= 8/kappa`, and `q' = q / gcd(p,q)` is large because `RatDenomLarge`
  rules out the bad rationals with small denominator.)
* So there is `E` in `(c1,d1)` outside `ratSpec p q lam`, and `RatGapEndpoints` gives a gap
  `(a1,b1)` containing `E`.  Cutting it with the window `[c,d]` produces `[u,v]` inside
  `[c,d]` whose interior avoids `ratSpec p q lam`, with `u < v`.
* If `u = c` or `v = d` the length is at least `(d-c)/3` for free; otherwise
  `u,v` lie in `ratSpec p q lam` and `RatGapBound` gives `v - u >= e^{-eps q} lam^{q/2}`.
* `RatIdsFlat` makes `N_{p/q}` constant on `[u,v]`, which is the conclusion of `P_GapBound`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-- Reduction of `p/q` by `gcd(p,q)`: the value of the rational is unchanged. -/
theorem rat_div_gcd (p : ℤ) {q : ℕ} (hq : 0 < q) :
    (p : ℝ) / (q : ℝ)
      = ((p / (Nat.gcd p.natAbs q : ℤ) : ℤ) : ℝ) / ((q / Nat.gcd p.natAbs q : ℕ) : ℝ) := by
  set g : ℕ := Nat.gcd p.natAbs q with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hq
  have hgdq : g ∣ q := Nat.gcd_dvd_right _ _
  have hgdp : (g : ℤ) ∣ p := by
    have h : g ∣ p.natAbs := Nat.gcd_dvd_left _ _
    exact Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.mpr h)
  have hqeq : (q : ℝ) = (g : ℝ) * ((q / g : ℕ) : ℝ) := by
    have h : g * (q / g) = q := Nat.mul_div_cancel' hgdq
    calc (q : ℝ) = ((g * (q / g) : ℕ) : ℝ) := by rw [h]
      _ = (g : ℝ) * ((q / g : ℕ) : ℝ) := by push_cast; ring
  have hpeq : (p : ℝ) = (g : ℝ) * (((p / (g : ℤ) : ℤ)) : ℝ) := by
    have h : (g : ℤ) * (p / (g : ℤ)) = p :=
      EuclideanDomain.mul_div_cancel' (a := p) (b := (g : ℤ)) (by omega : (g : ℤ) ≠ 0) hgdp
    calc (p : ℝ) = (((g : ℤ) * (p / (g : ℤ)) : ℤ) : ℝ) := by rw [h]
      _ = (g : ℝ) * (((p / (g : ℤ)) : ℤ) : ℝ) := by push_cast; ring
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hbR : ((q / g : ℕ) : ℝ) ≠ 0 := by
    have : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgdq) hgpos
    positivity
  rw [div_eq_div_iff hqR hbR, hqeq, hpeq]
  ring

/-- **(14d + 14g)** C14's gap bound, assembled from the rational-approximant inputs
`RatIdsFlat` (off-spectrum flatness), `RatIdsVariation` (variation inside the spectrum) and
`RatGapBound` (the CEY gap estimate), assuming the general theory `P_LEBasics` (14f) and
`P_BJ` (`L = 0` on the spectrum, 14f). -/
theorem p_gapBound_of (h4 : P_LEBasics) (h5 : P_RotBasics) (h6 : P_IDSSpectrum) (h7 : P_BJ)
    (hA : RatIdsFlat) (hB : RatIdsVariation) (hD : RatGapBound) : P_GapBound := by
  intro α lam c d hα hlam hlam1 hcd hspec ε hε
  set c1 : ℝ := c + (d - c) / 3 with hc1def
  set d1 : ℝ := c + 2 * (d - c) / 3 with hd1def
  have hc1lt : c < c1 := by rw [hc1def]; linarith
  have hc1d1 : c1 < d1 := by rw [hc1def, hd1def]; linarith
  have hd1lt : d1 < d := by rw [hd1def]; linarith
  have hc1mem : c1 ∈ Set.Icc c d := ⟨le_of_lt hc1lt, le_of_lt (lt_trans hc1d1 hd1lt)⟩
  have hd1mem : d1 ∈ Set.Icc c d := ⟨le_of_lt (lt_trans hc1lt hc1d1), le_of_lt hd1lt⟩
  set mid : ℝ := (c1 + d1) / 2 with hmiddef
  have hmidmem : mid ∈ Set.Icc c d := by
    rw [hmiddef]; exact ⟨by linarith, by linarith⟩
  have hmidpos : 0 < (d1 - c1) / 2 := by linarith
  have hκpos : 0 < ids α lam d1 - ids α lam c1 := by
    have h := h6 α lam hα mid (hspec hmidmem) ((d1 - c1) / 2) hmidpos
    have e1 : mid - (d1 - c1) / 2 = c1 := by rw [hmiddef]; ring
    have e2 : mid + (d1 - c1) / 2 = d1 := by rw [hmiddef]; ring
    rw [e1, e2] at h
    linarith
  set κ : ℝ := ids α lam d1 - ids α lam c1 with hκdef
  have hcont : Continuous fun p : ℝ × ℝ => ids p.1 lam p.2 := h5.2.2.1 lam
  have hK : IsCompact (Set.Icc (α - 1) (α + 1) ×ˢ Set.Icc c d) :=
    isCompact_Icc.prod isCompact_Icc
  have huc := hK.uniformContinuousOn_of_continuous hcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δu, hδupos, hδu⟩ := huc (κ / 4) (by linarith)
  have hδ0ex : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ α' E : ℝ, |α' - α| < δ0 → E ∈ Set.Icc c d →
      |ids α' lam E - ids α lam E| < κ / 4 := by
    refine ⟨min δu 1, lt_min hδupos one_pos, ?_⟩
    intro α' E hα' hE
    have h1 : |α' - α| < 1 := lt_of_lt_of_le hα' (min_le_right _ _)
    have h2 : |α' - α| < δu := lt_of_lt_of_le hα' (min_le_left _ _)
    have hm1 : (α', E) ∈ Set.Icc (α - 1) (α + 1) ×ˢ Set.Icc c d := by
      rw [Set.mem_prod]
      refine ⟨?_, hE⟩
      rw [Set.mem_Icc]
      have := abs_lt.mp h1
      constructor <;> linarith [this.1, this.2]
    have hm2 : (α, E) ∈ Set.Icc (α - 1) (α + 1) ×ˢ Set.Icc c d := by
      rw [Set.mem_prod]
      refine ⟨?_, hE⟩
      rw [Set.mem_Icc]
      constructor <;> linarith
    have hdist : dist (α', E) (α, E) < δu := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
        max_eq_left (abs_nonneg _)]
      exact h2
    have hres := hδu (α', E) hm1 (α, E) hm2 hdist
    rwa [Real.dist_eq] at hres
  obtain ⟨δ0, hδ0pos, hδ0⟩ := hδ0ex
  set Q0 : ℕ := max 1 (Nat.ceil (8 / κ) + 1) with hQ0def
  have hQ0one : 1 ≤ Q0 := le_max_left _ _
  have hQ0ge : 8 / κ ≤ (Q0 : ℝ) := by
    have h1 : (8 / κ : ℝ) ≤ (Nat.ceil (8 / κ) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (8 / κ) : ℝ) + 1 ≤ (Q0 : ℝ) := by
      have hh : (Nat.ceil (8 / κ) + 1 : ℕ) ≤ Q0 := le_max_right _ _
      have hcast : ((Nat.ceil (8 / κ) + 1 : ℕ) : ℝ) ≤ (Q0 : ℝ) := by exact_mod_cast hh
      push_cast at hcast
      linarith
    linarith
  have hQ0inv : 2 / (Q0 : ℝ) ≤ κ / 4 := by
    rw [div_le_iff₀ (by exact_mod_cast (show 0 < Q0 by omega) : (0 : ℝ) < (Q0 : ℝ))]
    have h2 : (κ / 4) * (8 / κ) = 2 := by field_simp; ring
    have h3 : (κ / 4) * (8 / κ) ≤ (κ / 4) * (Q0 : ℝ) :=
      mul_le_mul_of_nonneg_left hQ0ge (by linarith)
    linarith
  obtain ⟨ρ, hρpos, hρ⟩ := ratDenomLarge α hα Q0
  obtain ⟨δD, hδDpos, QD, hQD⟩ := hD h4 h7 α lam c d hα hlam hlam1 hcd hspec ε hε
  have hexp : ∃ Q1 : ℕ, ∀ q : ℕ, Q1 ≤ q →
      Real.exp (-(ε * (q : ℝ))) * lam ^ ((q : ℝ) / 2) ≤ (d - c) / 3 := by
    have h3 : 0 < (d - c) / 3 := by linarith
    have htend : Tendsto (fun q : ℕ => Real.exp (-(ε * (q : ℝ)))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun q : ℕ => ε * (q : ℝ)) atTop atTop := h1.const_mul_atTop hε
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)
    have hev : ∀ᶠ q : ℕ in atTop, Real.exp (-(ε * (q : ℝ))) < (d - c) / 3 :=
      (tendsto_order.1 htend).2 _ h3
    obtain ⟨Q1, hQ1⟩ := eventually_atTop.1 hev
    refine ⟨Q1, fun q hq => ?_⟩
    have hle1 : lam ^ ((q : ℝ) / 2) ≤ 1 := by
      simpa using Real.rpow_le_rpow (le_of_lt hlam) hlam1
        (by positivity : (0 : ℝ) ≤ (q : ℝ) / 2)
    calc Real.exp (-(ε * (q : ℝ))) * lam ^ ((q : ℝ) / 2)
        ≤ Real.exp (-(ε * (q : ℝ))) * 1 :=
          mul_le_mul_of_nonneg_left hle1 (Real.exp_pos _).le
      _ = Real.exp (-(ε * (q : ℝ))) := mul_one _
      _ ≤ (d - c) / 3 := le_of_lt (hQ1 q hq)
  obtain ⟨Q1, hQ1⟩ := hexp
  set δ : ℝ := min (min δ0 δD) ρ with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ0pos hδDpos) hρpos
  have hδle0 : δ ≤ δ0 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδleD : δ ≤ δD := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδleρ : δ ≤ ρ := min_le_right _ _
  refine ⟨δ, hδpos, max Q0 (max QD Q1), ?_⟩
  intro p q hq hpq
  have hQsplit0 : Q0 ≤ q := le_trans (le_max_left _ _) hq
  have hQDq : QD ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hQ1q : Q1 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hq0 : 0 < q := lt_of_lt_of_le (show 0 < Q0 by omega) hQsplit0
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hsmall0 : |(p : ℝ) / (q : ℝ) - α| < δ0 := by
    have h2 : δ / (q : ℝ) ≤ δ0 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ))]
      have h3 : δ0 ≤ δ0 * (q : ℝ) := by nlinarith [hδ0pos, hq1]
      linarith
    rw [abs_sub_comm]
    exact lt_of_lt_of_le hpq h2
  have hsmallD : |α - (p : ℝ) / (q : ℝ)| < δD / (q : ℝ) := by
    have h2 : δ / (q : ℝ) ≤ δD / (q : ℝ) := div_le_div_of_nonneg_right hδleD (by positivity)
    exact lt_of_lt_of_le hpq h2
  have hsmallρ : |α - (p : ℝ) / (q : ℝ)| < ρ := by
    have h2 : δ / (q : ℝ) ≤ ρ := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ))]
      have h3 : ρ ≤ ρ * (q : ℝ) := by nlinarith [hρpos, hq1]
      linarith
    exact lt_of_lt_of_le hpq h2
  have hgpos0 : 0 < Nat.gcd p.natAbs q := Nat.gcd_pos_of_pos_right _ hq0
  have hq'pos0 : 0 < q / Nat.gcd p.natAbs q :=
    Nat.div_pos (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right _ _)) hgpos0
  have hq' : Q0 ≤ q / Nat.gcd p.natAbs q := by
    by_contra hcon
    rw [not_le] at hcon
    set g : ℕ := Nat.gcd p.natAbs q with hgdef
    have hq'pos : 0 < q / g := by rw [hgdef]; exact hq'pos0
    have hρle := hρ (p / (g : ℤ)) (q / g) hq'pos hcon
    have heq : (p : ℝ) / (q : ℝ)
        = ((p / (g : ℤ) : ℤ) : ℝ) / ((q / g : ℕ) : ℝ) := by
      rw [hgdef]
      exact rat_div_gcd p hq0
    rw [← heq] at hρle
    linarith
  have hEex : ∃ E ∈ Set.Ioo c1 d1, E ∉ ratSpec p q lam := by
    by_contra hcon
    push_neg at hcon
    have hB' := hB p q lam hlam (by omega : 1 ≤ q) c1 d1 (le_of_lt hc1d1)
      (fun E hE => hcon E hE)
    have hlow : κ / 2 ≤ ids ((p : ℝ) / (q : ℝ)) lam d1 - ids ((p : ℝ) / (q : ℝ)) lam c1 := by
      have h1 := hδ0 ((p : ℝ) / (q : ℝ)) d1 hsmall0 hd1mem
      have h2 := hδ0 ((p : ℝ) / (q : ℝ)) c1 hsmall0 hc1mem
      rw [abs_lt] at h1 h2
      rw [hκdef]
      linarith [h1.1, h1.2, h2.1, h2.2]
    have hup : 2 / ((q / Nat.gcd p.natAbs q : ℕ) : ℝ) ≤ κ / 4 := by
      have h1 : ((Q0 : ℝ)) ≤ ((q / Nat.gcd p.natAbs q : ℕ) : ℝ) := by exact_mod_cast hq'
      have h2 : 2 / ((Q0 : ℝ)) ≤ κ / 4 := hQ0inv
      rw [div_le_iff₀ (by exact_mod_cast (show 0 < Q0 by omega) : (0 : ℝ) < (Q0 : ℝ))] at h2
      rw [div_le_iff₀ (by exact_mod_cast hq'pos0 : (0 : ℝ) < ((q / Nat.gcd p.natAbs q : ℕ) : ℝ))]
      have h3 : (κ / 4) * (Q0 : ℝ) ≤ (κ / 4) * ((q / Nat.gcd p.natAbs q : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      linarith
    linarith
  obtain ⟨E, hE, hEnspec⟩ := hEex
  have hcE : c ≤ E := le_of_lt (lt_trans hc1lt hE.1)
  have hEd : E ≤ d := le_of_lt (lt_trans hE.2 hd1lt)
  obtain ⟨a1, b1, ha1E, hEb1, hb1d, hfree, ha1U, hb1U⟩ :=
    ratGapEndpoints.2 p q lam c d E hEnspec hcE hEd hcd
  set u : ℝ := max a1 c with hudef
  set v : ℝ := min b1 d with hvdef
  have hcu : c ≤ u := le_max_right _ _
  have hvd : v ≤ d := min_le_right _ _
  have huE : u ≤ E := by
    rw [hudef]; exact max_le ha1E (le_of_lt (lt_trans hc1lt hE.1))
  have hEv : E ≤ v := by
    rw [hvdef]; exact le_min hEb1 (le_of_lt (lt_trans hE.2 hd1lt))
  have hfree' : ∀ y ∈ Set.Ioo u v, ∀ θ : ℝ, 2 < ‖trAq p q lam (y : ℂ) θ‖ := by
    intro y hy θ
    have hy' : y ∈ Set.Ioo a1 b1 :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
    by_contra hcon
    exact hfree y hy' ⟨θ, le_of_not_gt hcon⟩
  have huv : u < v := by
    by_contra hcon
    rw [not_lt] at hcon
    have huE' : u = E := le_antisymm huE (le_trans hEv hcon)
    have hvE : v = E := le_antisymm (le_trans hcon huE) hEv
    have hmin : min b1 d = E := by rw [← hvdef]; exact hvE
    have hb1d' : b1 ≤ d := by
      by_contra hlt
      rw [not_le] at hlt
      have : min b1 d = d := min_eq_right (le_of_lt hlt)
      rw [this] at hmin
      linarith [hd1lt, hE.2]
    have hb1E : b1 = E := by
      have : min b1 d = b1 := min_eq_left hb1d'
      rw [this] at hmin
      exact hmin
    have hb1lt : b1 < d := by rw [hb1E]; exact lt_trans hE.2 hd1lt
    have hb1mem : b1 ∈ ratSpec p q lam := hb1U hb1lt
    rw [hb1E] at hb1mem
    exact hEnspec hb1mem
  have hQ1use : Real.exp (-(ε * (q : ℝ))) * lam ^ ((q : ℝ) / 2) ≤ (d - c) / 3 := hQ1 q hQ1q
  have hAuse : ids ((p : ℝ) / (q : ℝ)) lam u = ids ((p : ℝ) / (q : ℝ)) lam v :=
    hA p q lam hlam u v huv hfree'
  by_cases huc : u = c
  · have hlen : (d - c) / 3 ≤ v - u := by
      rw [huc]
      have : c1 < v := lt_of_lt_of_le hE.1 hEv
      linarith [hc1def, this]
    exact ⟨u, v, hcu, huv, hvd, le_trans hQ1use hlen, hAuse⟩
  · by_cases hvd' : v = d
    · have hlen : (d - c) / 3 ≤ v - u := by
        rw [hvd']
        have : u < d1 := lt_of_le_of_lt huE hE.2
        linarith [hd1def, this]
      exact ⟨u, v, hcu, huv, hvd, le_trans hQ1use hlen, hAuse⟩
    · have ha1c : c ≤ a1 := by
        by_contra hlt
        rw [not_le] at hlt
        exact huc (by rw [hudef, max_eq_right (le_of_lt hlt)])
      have huU : u ∈ ratSpec p q lam := by
        have : u = a1 := by rw [hudef, max_eq_left ha1c]
        rw [this]; exact ha1U ha1c
      have hb1d'' : b1 < d := by
        by_contra hlt
        rw [not_lt] at hlt
        exact hvd' (by rw [hvdef, min_eq_right hlt])
      have hvU : v ∈ ratSpec p q lam := by
        have : v = b1 := by rw [hvdef, min_eq_left (le_of_lt hb1d'')]
        rw [this]; exact hb1U hb1d''
      have hsize := hQD p q hQDq hsmallD u v hcu huv hvd hfree' huU hvU
      exact ⟨u, v, hcu, huv, hvd, hsize, hAuse⟩

end Work.TMC14Core
