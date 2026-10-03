import Mathlib
import Submission.Work.FIArea6V.Defs
import Submission.Work.FIArea6c.S16_char_bound_twoP
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea6.DetSum_le_of_chiBound
import Submission.Work.FITop4.Areas6c
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6.S16Assembly

namespace Work.FIArea6V

/-- **The per-character bound of §16 in the clean (τ-vacuous) lane.**

This is the V-lane counterpart of `Work.FIArea6.S16_char_bound_twoP`: the pin
`Pa.τ = tauOf Pa.x Asave` is replaced by the τ-vacuity hypothesis `TauVac Pa φ`, and the axis-free
polar box is carried as a hypothesis (as in `Area5TwoV`).

At `ε = 1/(4·nuU)`, `Area5TwoV` gives constants `c` (in the exponent) and `C` (the prefactor).  The
character expansion (16.11) of `DetSum` — `DetSum_le_of_chiBound` — turns the bound on each
`S_χ^k(β)` into the bound on the `ω`-detected pair sum: for `1 ≤ d ≤ X ≤ (log N)^{nuU}` and
`|k| ≤ exp(√log N)`,

  `‖DetSum (d,k)‖ ≤ 4d·( C·[exp(-η c (4d)^{-ε}√log N) + exp(-η log N/log P)]·(4d)·N·(log N)^6 )²`.

Both constants keep their slots: `c` only in the two exponentials, `C` only as the prefactor. -/
theorem S16_char_bound_twoV (h : Work.FIArea6V.Area5TwoV) (η : ℝ) (hη0 : 0 < η) :
    ∃ c C x5 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x5 ∧
    ∀ (Pa : Work.FITop.Params), x5 ≤ (Pa.x : ℝ) → Pa.η = η →
    ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (d : ℕ) (k : ℤ) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → Work.FIArea6V.TauVac Pa φ →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
      1 ≤ d → d ≤ X → 1 ≤ X →
      (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
      |(k : ℝ)| ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
      ‖Work.FIArea6.DetSum Pa d k β‖
        ≤ 4 * (d : ℝ)
          * (C * (Real.exp (-(η * c * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
                  * Real.sqrt (Real.log Pa.N)))
                + Real.exp (-(η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
              * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) ^ (2 : ℕ) := by
  -- `nuU > 1`, hence `ε = 1/(4·nuU)` is admissible for `Area5TwoV`
  have hnuU1 : (1 : ℝ) ≤ Work.FITop4.nuU := by
    rw [Work.FITop4.nuU, Work.FITop4.sigmaChoice, Work.FITop4.Aprime, Work.FITop4.Asave]
    norm_num
  have hnuU : 0 < Work.FITop4.nuU := lt_of_lt_of_le one_pos hnuU1
  have hε0 : 0 < 1 / (4 * Work.FITop4.nuU) := by positivity
  have hε4 : 1 / (4 * Work.FITop4.nuU) ≤ 1 / 4 := by
    have h4 : (0 : ℝ) < 4 := by norm_num
    exact one_div_le_one_div_of_le h4 (by linarith)
  obtain ⟨c, C, x0, hc0, hC0, hx0, h5b⟩ := h (1 / (4 * Work.FITop4.nuU)) hε0 hε4
  refine ⟨c, C, max x0 1, hc0, hC0, lt_of_lt_of_le one_pos (le_max_right x0 1), ?_⟩
  intro Pa hx hη X φ z0 d k β hβ hTau hfar hd hdX hX1 hXlog hk
  have hx0' : x0 ≤ (Pa.x : ℝ) := le_trans (le_max_left x0 1) hx
  have hlt : Work.FITop4.nuU < 1 / (2 * (1 / (4 * Work.FITop4.nuU))) := by
    have hν : Work.FITop4.nuU ≠ 0 := by linarith
    field_simp
    linarith
  have hdle : (d : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU :=
    le_trans (by exact_mod_cast hdX) hXlog
  -- the character sums of the (16.11) expansion, bounded by the two-constant Lemma 16.2
  have hBmain : ∀ χ : AddChar (Additive (Work.FIArea7.GaussUnit (4 * d))) ℂ,
      ‖∑ z ∈ Work.FITop.boxN Pa, β z * Work.FIArea7.chiOf (4 * d) χ z * Work.FIArea6.psiK k z‖ ≤
        C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
                  * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ) := by
    intro χ
    have hh := h5b Pa hx0' φ Work.FITop4.nuU z0 d k (Work.FIArea7.chiOf (4 * d) χ)
      hTau hfar hnuU hlt hd hdle hk (Work.FIArea6.chiOf_isCharMod4d d hd χ) β hβ
    simpa only [Work.FIArea6.psiK] using hh
  have hmain := Work.FIArea6.DetSum_le_of_chiBound Pa d hd k β
    (C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-(1 / (4 * Work.FITop4.nuU)))
                  * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)) hBmain
  rw [hη] at hmain
  exact hmain

end Work.FIArea6V
