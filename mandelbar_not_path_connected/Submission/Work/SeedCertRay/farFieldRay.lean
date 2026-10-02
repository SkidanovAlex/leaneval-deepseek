/-
# The far-field estimate along a dynamic ray

`Work.SeedCertRay.farFieldRay`: the point of the dynamical ray of angle `θ` at level `r` is
within `64 / r` of the point `r · e^{2πiθ}` of the exterior circle, uniformly for `r ≥ 64`, for
every parameter `c` of the mandelbar with `‖c‖ ≤ 2`.

The mathematical content is the tangency of the Böttcher coordinate to the identity at infinity,
in the explicit quantitative form

`‖φ z - z‖ ≤ 8 / ‖z‖`   for `‖z‖ ≥ 8`

(`farFieldRay_aux_farField`, proved here from the product formula of `Work.Bottcher` and the
explicit leading-term bound `Work.Bottcher.Contraction.bottcherSeries_sub_leading_le`), together
with the *a priori* fact that the point with Böttcher coordinate of modulus `r ≥ 64` is
automatically at distance at least `8` from the origin (`farFieldRay_aux_norm_ge_eight`): if not,
the first point of its orbit to leave the disc of radius `8` has norm at most `66 = 8² + 2`,
while its Böttcher coordinate has modulus at least `r² ≥ 4096`.
-/
import Mathlib
import Submission.Work.SeedCertRay.Basic
import Submission.Work.SeedDyn.Defs
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.NAKANE2.Deriv.deriv_varphiCrit_self_ne_zero
import Submission.Work.Bottcher.Contraction.FarSeriesSharp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open Filter
open scoped Topology ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## The far field of a Böttcher coordinate -/

/-- **The Böttcher coordinate is within `8/‖z‖` of the identity for `‖z‖ ≥ 8`.**

Every Böttcher coordinate of `T_c` at a mandelbar parameter `c` with `‖c‖ ≤ 2` agrees with the
canonical critical coordinate `Work.Bottcher.varphiCrit c` on the escaping set
(`Work.Bottcher.varphiCrit_unique`), which in turn agrees with the explicit product formula
`Work.Bottcher.bottcher c = z · exp (bottcherSeries c z)` outside the escape radius
(`Work.NAKANE2.Deriv.eq_bottcher_of_analytic_gen`).  On `‖z‖ ≥ 8 ≥ 3/2 (1 + ‖c‖)` the series
differs from its leading term `conj c / (2 z²)` by at most `2‖c‖/‖z‖⁴`, so
`‖bottcherSeries c z‖ · ‖z‖² ≤ 2`, and
`‖bottcher c z - z‖ = ‖z‖ · ‖exp S - 1‖ ≤ ‖z‖ · 2‖S‖ ≤ 8/‖z‖`. -/
theorem farFieldRay_aux_farField {c : ℂ} (hc : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2) {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) {z : ℂ} (hz : (8 : ℝ) ≤ ‖z‖) :
    ‖φ z - z‖ ≤ 8 / ‖z‖ := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith
  -- the escape radius of the family is below `8`
  have hEsc : Work.Bottcher.escapeRadius c < ‖z‖ := by
    rw [show Work.Bottcher.escapeRadius c = 2 * (1 + ‖c‖) from rfl]
    linarith
  -- outside the escape radius every point lies in the critical domain
  have hcrit : ∀ w : ℂ, Work.Bottcher.escapeRadius c < ‖w‖ → w ∈ Work.ParamRays.critDomain c := by
    intro w hw
    rw [Work.SeedDyn.critDomain_eq_escapingSet hc]
    refine Work.ParamRays.escaping_of_lt_norm c w ?_
    rw [show Work.Bottcher.escapeRadius c = 2 * (1 + ‖c‖) from rfl] at hw
    have hmax : max 2 ‖c‖ ≤ 2 * (1 + ‖c‖) := by
      rw [max_le_iff]
      exact ⟨by linarith [norm_nonneg c], by linarith [norm_nonneg c]⟩
    linarith
  have hcritz : z ∈ Work.ParamRays.critDomain c := hcrit z hEsc
  -- the given coordinate is the canonical one, and the canonical one is the product formula
  have hφeq : φ z = Work.Bottcher.varphiCrit c z :=
    (Work.Bottcher.varphiCrit_unique hφ.isCritBottcher hcritz).symm
  have hbot : Work.Bottcher.varphiCrit c z = Work.Bottcher.bottcher c z :=
    Work.NAKANE2.Deriv.eq_bottcher_of_analytic_gen c (Work.Bottcher.escapeRadius c) le_rfl
      (Work.Bottcher.varphiCrit c)
      ((Work.Bottcher.analyticOnNhd_varphiCrit c).mono (fun w hw => hcrit w hw))
      (fun w hw => Work.NAKANE2.Deriv.varphiCrit_comm_pMap (hcrit w hw))
      (fun w hw => Work.Bottcher.norm_varphiCrit (hcrit w hw))
      (Work.Bottcher.varphiCrit_div_tendsto_one c) hEsc
  -- the leading-term bound for the Böttcher series
  have hlead := Work.Bottcher.Contraction.bottcherSeries_sub_leading_le c z hc2
      (show 3 / 2 * (1 + ‖c‖) ≤ ‖z‖ by linarith)
  have hw0 : ‖(starRingEnd ℂ) c / (2 * z ^ 2)‖ = ‖c‖ / (2 * ‖z‖ ^ 2) := by
    rw [norm_div, Complex.norm_conj, norm_mul, norm_pow]
    norm_num
  have hS : ‖Work.Bottcher.bottcherSeries c z‖
      ≤ ‖c‖ / (2 * ‖z‖ ^ 2) + 2 * ‖c‖ / ‖z‖ ^ 4 := by
    calc ‖Work.Bottcher.bottcherSeries c z‖
        = ‖(Work.Bottcher.bottcherSeries c z - (starRingEnd ℂ) c / (2 * z ^ 2))
            + (starRingEnd ℂ) c / (2 * z ^ 2)‖ := by ring_nf
      _ ≤ ‖Work.Bottcher.bottcherSeries c z - (starRingEnd ℂ) c / (2 * z ^ 2)‖
            + ‖(starRingEnd ℂ) c / (2 * z ^ 2)‖ := norm_add_le _ _
      _ ≤ 2 * ‖c‖ / ‖z‖ ^ 4 + ‖c‖ / (2 * ‖z‖ ^ 2) := by rw [hw0]; linarith
      _ = ‖c‖ / (2 * ‖z‖ ^ 2) + 2 * ‖c‖ / ‖z‖ ^ 4 := by ring
  have hS2 : ‖Work.Bottcher.bottcherSeries c z‖ * ‖z‖ ^ 2 ≤ 2 := by
    have hzn : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
    have hstep : (‖c‖ / (2 * ‖z‖ ^ 2) + 2 * ‖c‖ / ‖z‖ ^ 4) * ‖z‖ ^ 2
        = ‖c‖ / 2 + 2 * ‖c‖ / ‖z‖ ^ 2 := by field_simp
    have hge : ‖Work.Bottcher.bottcherSeries c z‖ * ‖z‖ ^ 2
        ≤ (‖c‖ / (2 * ‖z‖ ^ 2) + 2 * ‖c‖ / ‖z‖ ^ 4) * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hS (le_of_lt hzn)
    rw [hstep] at hge
    have h1 : ‖c‖ / 2 ≤ 1 := by linarith
    have h2 : 2 * ‖c‖ / ‖z‖ ^ 2 ≤ 4 / 64 := by
      refine div_le_div₀ (by positivity) ?_ (by norm_num) ?_
      · linarith
      · nlinarith
    linarith
  -- assemble
  rw [hφeq, hbot,
    show Work.Bottcher.bottcher c z = z * Complex.exp (Work.Bottcher.bottcherSeries c z) from rfl]
  have hS1 : ‖Work.Bottcher.bottcherSeries c z‖ ≤ 1 := by
    nlinarith [norm_nonneg (Work.Bottcher.bottcherSeries c z), hz, sq_nonneg ‖z‖]
  have hexp : ‖Complex.exp (Work.Bottcher.bottcherSeries c z) - 1‖
      ≤ 2 * ‖Work.Bottcher.bottcherSeries c z‖ := Complex.norm_exp_sub_one_le hS1
  have hrew : z * Complex.exp (Work.Bottcher.bottcherSeries c z) - z
      = z * (Complex.exp (Work.Bottcher.bottcherSeries c z) - 1) := by ring
  rw [hrew, norm_mul]
  have hSl : ‖Work.Bottcher.bottcherSeries c z‖ * ‖z‖ ≤ 2 / ‖z‖ := by
    rw [le_div_iff₀ hzpos]
    nlinarith [hS2]
  calc ‖z‖ * ‖Complex.exp (Work.Bottcher.bottcherSeries c z) - 1‖
      ≤ ‖z‖ * (2 * ‖Work.Bottcher.bottcherSeries c z‖) :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hzpos)
    _ = 2 * (‖Work.Bottcher.bottcherSeries c z‖ * ‖z‖) := by ring
    _ ≤ 2 * (2 / ‖z‖) := by linarith
    _ = 4 / ‖z‖ := by ring
    _ ≤ 8 / ‖z‖ := by
        rw [div_le_div_iff_of_pos_right hzpos]
        norm_num

/-! ## A point of large Böttcher modulus is far from the origin -/

/-- **If the Böttcher coordinate of `z` has modulus `r ≥ 64`, then `‖z‖ ≥ 8`.**

Suppose `‖z‖ < 8`.  Since `z` escapes, its orbit leaves the disc of radius `8`; let `n ≥ 1` be the
first index with `8 < ‖T^n z‖`.  Then `‖T^n z‖ ≤ 8² + ‖c‖ ≤ 66`, while the Böttcher functional
equation gives `‖φ (T^n z)‖ = ‖φ z‖^{2^n} = r^{2^n} ≥ r² ≥ 4096`, contradicting the far-field
bound `‖φ w‖ ≤ ‖w‖ + 8/‖w‖ ≤ 67` valid at `w = T^n z`. -/
theorem farFieldRay_aux_norm_ge_eight {c : ℂ} {φ : ℂ → ℂ} {z : ℂ} {r : ℝ} (hc2 : ‖c‖ ≤ 2)
    (hfe : ∀ w : ℂ, Work.ParamRays.Escaping c w →
      φ (Tantibar c w) = conj (φ w) ^ 2)
    (hzesc : Work.ParamRays.Escaping c z) (hφz : ‖φ z‖ = r) (hr : (64 : ℝ) ≤ r)
    (hfar : ∀ w : ℂ, 8 ≤ ‖w‖ → ‖φ w - w‖ ≤ 8 / ‖w‖) :
    (8 : ℝ) ≤ ‖z‖ := by
  by_contra hcon
  rw [not_le] at hcon
  -- the modulus of `φ` along the orbit
  have hnormT : ∀ n : ℕ, ‖φ (Work.ParamRays.orbit c z n)‖ = r ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simpa using hφz
    | succ n ih =>
      rw [Work.ParamRays.orbit_succ, hfe _ (hzesc.iterate n), norm_pow, Complex.norm_conj, ih]
      rw [← pow_mul, ← pow_succ]
  -- the orbit leaves the disc of radius `8`
  have hex : ∃ n : ℕ, 8 < ‖Work.ParamRays.orbit c z n‖ := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Work.ParamRays.Escaping.eventually_gt hzesc 8)
    exact ⟨N, hN N le_rfl⟩
  set n₀ := Nat.find hex with hn₀
  have hspec : 8 < ‖Work.ParamRays.orbit c z n₀‖ := Nat.find_spec hex
  have hn₀pos : 1 ≤ n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · rw [h, Work.ParamRays.orbit_zero] at hspec
      exact absurd hspec (not_lt.mpr hcon.le)
    · exact h
  have hprev : ‖Work.ParamRays.orbit c z (n₀ - 1)‖ ≤ 8 := by
    have hlt : n₀ - 1 < n₀ := by omega
    exact not_lt.mp (Nat.find_min hex hlt)
  -- the first point outside the disc is still within `66`
  have hbnd : ‖Work.ParamRays.orbit c z n₀‖ ≤ 66 := by
    have hsucc : Work.ParamRays.orbit c z n₀
        = Tantibar c (Work.ParamRays.orbit c z (n₀ - 1)) := by
      conv_lhs => rw [show n₀ = n₀ - 1 + 1 from by omega]
      rw [Work.ParamRays.orbit_succ]
    rw [hsucc]
    have h1 : ‖Tantibar c (Work.ParamRays.orbit c z (n₀ - 1))‖
        ≤ ‖Work.ParamRays.orbit c z (n₀ - 1)‖ ^ 2 + ‖c‖ := by
      calc ‖Tantibar c (Work.ParamRays.orbit c z (n₀ - 1))‖
          = ‖conj (Work.ParamRays.orbit c z (n₀ - 1)) ^ 2 + c‖ := rfl
        _ ≤ ‖conj (Work.ParamRays.orbit c z (n₀ - 1)) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖Work.ParamRays.orbit c z (n₀ - 1)‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
    have h2 : ‖Work.ParamRays.orbit c z (n₀ - 1)‖ ^ 2 ≤ 64 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hprev 2
      norm_num at h
      linarith
    linarith
  -- whereas the Böttcher modulus there is at least `r ^ 2 ≥ 4096`
  have hge : 4096 ≤ r ^ (2 ^ n₀) := by
    have h2 : (2 : ℕ) ≤ 2 ^ n₀ := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n₀ := Nat.pow_le_pow_right (by norm_num) hn₀pos
    calc (4096 : ℝ) = 64 ^ 2 := by norm_num
      _ ≤ r ^ 2 := pow_le_pow_left₀ (by linarith) hr 2
      _ ≤ r ^ (2 ^ n₀) := pow_le_pow_right₀ (by linarith) h2
  have hle : r ^ (2 ^ n₀) ≤ 67 := by
    have hff := hfar _ hspec.le
    have htri : ‖φ (Work.ParamRays.orbit c z n₀)‖
        ≤ ‖φ (Work.ParamRays.orbit c z n₀) - Work.ParamRays.orbit c z n₀‖
          + ‖Work.ParamRays.orbit c z n₀‖ := by
      calc ‖φ (Work.ParamRays.orbit c z n₀)‖
          = ‖(φ (Work.ParamRays.orbit c z n₀) - Work.ParamRays.orbit c z n₀)
              + Work.ParamRays.orbit c z n₀‖ := by ring_nf
        _ ≤ ‖φ (Work.ParamRays.orbit c z n₀) - Work.ParamRays.orbit c z n₀‖
            + ‖Work.ParamRays.orbit c z n₀‖ := norm_add_le _ _
    have h2 : 8 / ‖Work.ParamRays.orbit c z n₀‖ ≤ 1 := by
      rw [div_le_one (by linarith [hspec])]
      linarith [hspec]
    rw [hnormT n₀] at htri
    linarith
  linarith

/-! ## The far-field estimate along a ray -/

theorem farFieldRay {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (hc2 : ‖c‖ ≤ 2) {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher c φ) (hN : Work.EL.DynB c φ) {θ r : ℝ} (hr : (64 : ℝ) ≤ r) (ht : 1 < r) : ‖Work.EL.rayPt hN θ r - (r : ℂ) * Work.Landing.rayDirection θ‖ ≤ 64 / r := by
  have hrpos : (0 : ℝ) < r := by linarith
  set z : ℂ := Work.EL.rayPt hN θ r with hzdef
  -- `z` is off the filled Julia set, with Böttcher image the point `r · e^{2πiθ}`
  have hzK : z ∉ Work.EL.K c := by rw [hzdef]; exact Work.EL.rayPt_notMem_K hN ht
  have hPhi : Work.EL.dynPhi c φ z = (r : ℂ) * Work.Landing.rayDirection θ := by
    rw [hzdef, Work.Top.NakaneData.Phi_rayPt hN ht, Work.Top.NakaneData.rayPoint,
      Work.Landing.rayDirection]
    push_cast
    ring
  have hφz : φ z = (r : ℂ) * Work.Landing.rayDirection θ := by
    rw [← Work.EL.dynPhi_of_notMem (φ := φ) hzK]
    exact hPhi
  have hdir : ‖Work.Landing.rayDirection θ‖ = 1 := by
    rw [Work.Landing.rayDirection, Complex.norm_exp]
    simp
  have hnormφ : ‖φ z‖ = r := by
    rw [hφz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, hdir, mul_one]
  have hzesc : Work.ParamRays.Escaping c z := by
    rw [← Work.SeedDyn.mem_esc, Work.SeedDyn.esc_eq_compl_filledJulia]
    exact hzK
  -- `z` is at distance at least `8` from the origin, so the far-field bound applies
  have hfar : ∀ w : ℂ, 8 ≤ ‖w‖ → ‖φ w - w‖ ≤ 8 / ‖w‖ :=
    fun w hw => farFieldRay_aux_farField hc hc2 hφ hw
  have hz8 : (8 : ℝ) ≤ ‖z‖ :=
    farFieldRay_aux_norm_ge_eight hc2 hφ.2.1 hzesc hnormφ hr hfar
  have hmain : ‖z - φ z‖ ≤ 64 / r := by
    have hff := farFieldRay_aux_farField hc hc2 hφ hz8
    have htri : ‖φ z‖ ≤ ‖z‖ + ‖φ z - z‖ := by
      calc ‖φ z‖ = ‖z + (φ z - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖φ z - z‖ := norm_add_le _ _
    have h2 : 8 / ‖z‖ ≤ 1 := by
      rw [div_le_one (by linarith [hz8])]
      linarith [hz8]
    have hzge : r / 2 ≤ ‖z‖ := by
      rw [hnormφ] at htri
      linarith
    calc ‖z - φ z‖ = ‖φ z - z‖ := norm_sub_rev _ _
      _ ≤ 8 / ‖z‖ := hff
      _ ≤ 64 / r := by
          rw [div_le_iff₀ (by linarith [norm_nonneg z, hzge, hrpos] : (0 : ℝ) < ‖z‖),
            div_mul_eq_mul_div, le_div_iff₀ hrpos]
          nlinarith [hzge, norm_nonneg z]
  calc ‖Work.EL.rayPt hN θ r - (r : ℂ) * Work.Landing.rayDirection θ‖ = ‖z - φ z‖ := by
        rw [← hzdef, ← hφz]
    _ ≤ 64 / r := hmain

end

end Work.SeedCertRay
