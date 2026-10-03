/-
# `Work.FIArea2.area2_6e` — the round-6 area 2 of *FI*, `Area2_6b`

`Area2_6b` (`Submission/Work/FITop4/Areas6b.lean`)

  `‖D* − D₀‖ ≤ Cb·ϑ⁻¹τ²N²(log N)^{bFun η} + C3·(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`

is *FI* (9.10) plus the §10 replacement error (7.10)/(10.4).  The proof is the triangle inequality
at the **exact** main term `D0ex` of `R6/ExactMain.lean` (the (9.11) sum with the exact (6.13)
kernel, i.e. the paper's `D₀` in (9.10)):

  `‖D* − D₀‖ ≤ ‖D* − D₀^exact‖ + ‖D₀^exact − D₀‖`,

the two summands being

* `R6/A27.area2_6e_A27` — the §9 aggregate (9.10), from the lacunarity input
  `R6/hLMine27 : LacPropK (2^26 + 200)`.  The cap (instead of `2^10`) is forced by the new
  cube-cutoff box estimate: `R6/uboxSum_le_dsum3` (Landreau at `d³ ≤ |N|`) →
  `R6/ubox_bound3` (exponent `2^26`, using `R6/WC_cube` with the lossy local-density bound
  `R6/LD_lossy` and the short-vector count `R6/WC_basic`) → `R6/hbox6_of_ubox3` (exponent
  `2^26 + 200 ≤ 2^27`) → `R6/hL_of_box` → `R6/KCap.LacPropK`.  This route avoids the per-modulus
  `WC_perMod` and its "hard region" `c > max(2r, X, Y)`, which is not provable with the tools of
  this workspace (see `R6/WC_PERMOD_LEAD.md`); the exponent budget is available because
  `bFun η ≥ 2^28` on `0 < η < 3/32` (`R6/BFun29`).
* `R6/area2_6e_B2` — the (7.10)/(10.4) replacement of the exact Fourier integral by its main
  term, whose only analytic input is *FI* Lemma 10.1 at the exponent `θ³` (`R6/WProp`, proved in
  `R6/R6WProp.lean`) together with the (7.10) estimate `FintProp` (`R6/Fint_logFac6.lean`).

The constants are added: `Cb := Cb_A + Cb_B`, `C3 := C3_B`.
-/
import Mathlib
import Submission.Work.FITop4.Areas6b
import Submission.Work.FIArea2.R6.Inputs6
import Submission.Work.FIArea2.R6.ExactMain
import Submission.Work.FIArea2.R6.Pack6
import Submission.Work.FIArea2.R6.A27
import Submission.Work.FIArea2.R6.area2_6e_B2
import Submission.Work.FIArea2.R6.hLMine27
import Submission.Work.FIArea2.R6.R6WProp
import Submission.Work.FIArea2.R6.Fint_logFac6

set_option autoImplicit false

namespace Work.FIArea2

open Work.FITop4

/-- **`Area2_6b`**: (9.10) plus the (7.10)/(10.4) replacement error, by the triangle inequality at
the exact main term `R6.D0ex`. -/
theorem area2_6e : Work.FITop4.Area2_6b := by
  have hL : Work.FIArea2.R6.LacPropK (2 ^ 26 + 200) := Work.FIArea2.R6.hLMine27
  have hW : Work.FIArea2.R6.WProp := Work.FIArea2.R6.R6WProp
  have hF : Work.FIArea2.R6.FintProp := Work.FIArea2.R6.Fint_logFac6
  intro η hη hη32
  obtain ⟨CbA, x0A, hCbA, hx0A, hA⟩ := Work.FIArea2.R6.area2_6e_A27 hL η hη hη32
  obtain ⟨CbB, C3B, x0B, hCbB, hC3B, hx0B, hB⟩ := Work.FIArea2.R6.area2_6e_B2 hW hF
  refine ⟨CbA + CbB, C3B, max x0A x0B, by positivity, hC3B, ?_⟩
  intro Pa hx hηPa f φ z0 β hmaj hβ
  have hx1 : x0A ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hx2 : x0B ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have h1 := hA Pa hx1 hηPa f hmaj φ z0 β hβ
  have h2 := hB Pa hx2 f hmaj φ z0 β hβ
  have htri : ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
        - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
      ≤ ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
            - ((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa)
                (Work.FIArea2.R6.majF Pa f hmaj) β : ℝ) : ℂ)‖
        + ‖((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa)
              (Work.FIArea2.R6.majF Pa f hmaj) β : ℝ) : ℂ)
            - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖ := by
    have hsplit : ((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
          - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β
        = (((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
              - ((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa)
                  (Work.FIArea2.R6.majF Pa f hmaj) β : ℝ) : ℂ))
          + (((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa)
                (Work.FIArea2.R6.majF Pa f hmaj) β : ℝ) : ℂ)
              - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β) := by
      ring
    rw [hsplit]
    exact norm_add_le _ _
  calc ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
        - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
      ≤ ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
            - ((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa)
                (Work.FIArea2.R6.majF Pa f hmaj) β : ℝ) : ℂ)‖
        + ‖((Work.FIArea2.R6.D0ex (Work.FITop.radN Pa)
              (Work.FIArea2.R6.majF Pa f hmaj) β : ℝ) : ℂ)
            - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖ := htri
    _ ≤ CbA * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (bFun Pa.η)
        + (CbB * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ (bFun Pa.η)
          + C3B * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
            * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) :=
        add_le_add h1 h2
    _ = (CbA + CbB) * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ (2 : ℕ)
          * (Real.log Pa.N) ^ (bFun Pa.η)
        + C3B * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2)
          * Pa.N ^ ((3 : ℝ) / 2) * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) := by ring

end Work.FIArea2
