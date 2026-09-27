import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.FanTri.BranchCompDefs
import Submission.Work.EQ.FanTri.branchComp_lipschitz
import Submission.Work.EQ.FanTri.fan_gap_unif
import Submission.Work.EQ.germC_facts

/-!
# The quantitative big-gap limit of the stable fan

`Work.EQ.tb_fan_run_limit` (Rychlik Theorem 7(3), quantitative form): for a fixed prefix `ε₀` and a
fixed trailing characteristic value `μ` with `‖μ‖ ≤ 1`, the fan maps of `ε₀ ++ true^j ++ C`
converge to `fan ε₀ (μ ·)` geometrically in `j`, uniformly in the closed trailing word `C`, on the
disc `(eqLam a) ^ ε₀.length * ‖u‖ ≤ δ`.

This is a by-product of the proven uniform big-gap estimate `Work.EQ.FanTri.fan_gap_run`
(`‖fan (true^j ++ C) u - germC (μ u)‖ ≤ Kr * rate^j * ‖u‖^2`, uniform in `C` and `μ`) together with
the branch-composition identity `fan (ε₀ ++ δ) u = branchComp ε₀ (fan δ (λ^{|ε₀|} u))`
(`Work.EQ.FanTri.fan_append_branchComp`) and the Lipschitz property of `branchComp` near the axis
point `A₁ = (-1/2,0)` (`Work.EQ.FanTri.branchComp_lipschitz`).

It is the input needed to pass to the limit in the case-(ii) argument of Rychlik's Lemma 5.1.
-/

namespace Work.EQ

open Work.EQ Complex Filter _root_.Topology

noncomputable section

abbrev tbA1 : ℂ × ℂ := (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))

/-- **Quantitative big-gap limit (local form).**  For a fixed prefix `ε₀` and a fixed trailing
characteristic value `μ` (`‖μ‖ ≤ 1`), the fan maps of `ε₀ ++ true^j ++ C` converge to
`fan ε₀ (μ ·)` geometrically in `j`, uniformly in the closed trailing word `C`, on the disc
`(eqLam a) ^ ε₀.length * ‖u‖ ≤ δ`. -/
theorem tb_fan_run_limit {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε₀ : List Bool) (μ : ℂ) (hμ : ‖μ‖ ≤ 1) :
    ∃ δ K rate : ℝ, 0 < δ ∧ 0 < K ∧ 0 < rate ∧ rate < 1 ∧
      ∀ (C : List Bool) (j : ℕ) (u : ℂ), fan a h C 0 = tbA1 → charVal a h C = μ →
        (eqLam a) ^ ε₀.length * ‖u‖ ≤ δ →
          ‖fan a h (ε₀ ++ List.replicate j true ++ C) u - fan a h ε₀ (μ * u)‖
            ≤ K * rate ^ j * ((eqLam a) ^ ε₀.length * ‖u‖) ^ 2 := by
  obtain ⟨δr, Kr, rate, hδrpos, hKrpos, hratepos, hratelt, hrun⟩ :=
    FanTri.fan_gap_run (a := a) ha0 ha1 hh
  obtain ⟨Cd, δ1, hCdpos, hδ1pos, hdev⟩ := FanTri.fan_deviation_bound (a := a) ha0 ha1 hh
  obtain ⟨Cg, δ2, hCgpos, hδ2pos, hLdev⟩ := FanTri.germC_deviation_bound (a := a) ha0 ha1 hh
  obtain ⟨ρ, L, hρpos, hLnn, hlip⟩ := FanTri.branchComp_lipschitz (a := a) ha0 ha1 ε₀
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hA1eq : FanTri.A1 = tbA1 := by
    ext <;> simp only [FanTri.A1, tbA1] <;> norm_num
  -- the small radius
  set ρs : ℝ := ρ / (2 * (Cd + Cg + 1)) with hρsdef
  have hρspos : 0 < ρs := by rw [hρsdef]; positivity
  have hden : 0 < 2 * (Cd + Cg + 1) := by linarith
  have hCdρs : Cd * ρs ≤ ρ / 2 := by
    have h2 : Cd * ρ ≤ (Cd + Cg + 1) * ρ := by nlinarith [hρpos.le, hCdpos.le]
    calc Cd * ρs = Cd * ρ / (2 * (Cd + Cg + 1)) := by rw [hρsdef]; ring
      _ ≤ (Cd + Cg + 1) * ρ / (2 * (Cd + Cg + 1)) :=
          div_le_div_of_nonneg_right h2 (le_of_lt hden)
      _ = ρ / 2 := by field_simp
  have hCgρs : Cg * ρs ≤ ρ / 2 := by
    have h2 : Cg * ρ ≤ (Cd + Cg + 1) * ρ := by nlinarith [hρpos.le, hCgpos.le]
    calc Cg * ρs = Cg * ρ / (2 * (Cd + Cg + 1)) := by rw [hρsdef]; ring
      _ ≤ (Cd + Cg + 1) * ρ / (2 * (Cd + Cg + 1)) :=
          div_le_div_of_nonneg_right h2 (le_of_lt hden)
      _ = ρ / 2 := by field_simp
  have hKpos : 0 < (L + 1) * Kr := mul_pos (by linarith) hKrpos
  refine ⟨min δr (min (δ1 / 2) (min (δ2 / 2) ρs)), (L + 1) * Kr, rate, ?_, hKpos,
    hratepos, hratelt, ?_⟩
  · exact lt_min hδrpos (lt_min (by linarith) (lt_min (by linarith) hρspos))
  · intro C j u hC0 hCμ hu
    have hu_r : (eqLam a) ^ ε₀.length * ‖u‖ ≤ δr := le_trans hu (min_le_left _ _)
    have hu_1 : (eqLam a) ^ ε₀.length * ‖u‖ ≤ δ1 / 2 :=
      le_trans hu (le_trans (min_le_right _ _) (min_le_left _ _))
    have hu_2 : (eqLam a) ^ ε₀.length * ‖u‖ ≤ δ2 / 2 :=
      le_trans hu (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hu_s : (eqLam a) ^ ε₀.length * ‖u‖ ≤ ρs :=
      le_trans hu (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
    set v : ℂ := (eqLam a : ℂ) ^ ε₀.length * u with hvdef
    have hnorm : ‖(eqLam a : ℂ)‖ = eqLam a := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hlam0.le]
    have hvn : ‖v‖ = (eqLam a) ^ ε₀.length * ‖u‖ := by
      rw [hvdef, norm_mul, norm_pow, hnorm]
    have hvr : ‖v‖ ≤ δr := by rw [hvn]; exact hu_r
    have hv1 : ‖v‖ < δ1 := by rw [hvn]; linarith
    have hv2 : ‖v‖ < δ2 := by rw [hvn]; linarith
    have hvρ : ‖v‖ ≤ ρs := by rw [hvn]; exact hu_s
    have hC0' : fan a h C 0 = FanTri.A1 := hC0.trans hA1eq.symm
    have hctrF : fan a h (List.replicate j true ++ C) 0 = FanTri.A1 :=
      FanTri.fan_replicate_true_centre ha0 ha1 hh j (C := C) hC0'
    have h1 : fan a h (ε₀ ++ List.replicate j true ++ C) u
        = FanTri.branchComp a ε₀ (fan a h (List.replicate j true ++ C) v) := by
      rw [List.append_assoc, FanTri.fan_append_branchComp, hvdef]
    have h2 : fan a h ε₀ (μ * u) = FanTri.branchComp a ε₀ (germC a h (μ * v)) := by
      have h3 : fan a h ε₀ (μ * u) = fan a h (ε₀ ++ []) (μ * u) := by rw [List.append_nil]
      rw [h3, FanTri.fan_append_branchComp]
      congr 1
      rw [fan_nil]
      congr 1
      rw [hvdef]; ring
    rw [h1, h2]
    have hX : ‖fan a h (List.replicate j true ++ C) v - tbA1‖ ≤ ρ := by
      have h' : ‖fan a h (List.replicate j true ++ C) v - FanTri.A1‖ ≤ Cd * ‖v‖ :=
        hdev (List.replicate j true ++ C) hctrF v hv1
      rw [hA1eq] at h'
      calc ‖fan a h (List.replicate j true ++ C) v - tbA1‖ ≤ Cd * ‖v‖ := h'
        _ ≤ Cd * ρs := mul_le_mul_of_nonneg_left hvρ (le_of_lt hCdpos)
        _ ≤ ρ / 2 := hCdρs
        _ ≤ ρ := by linarith [hρpos]
    have hY : ‖germC a h (μ * v) - tbA1‖ ≤ ρ := by
      have hμv : ‖μ * v‖ < δ2 := by
        rw [norm_mul]
        calc ‖μ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg v)
          _ = ‖v‖ := one_mul _
          _ < δ2 := hv2
      have hgb : ‖germC a h (μ * v) - FanTri.A1‖ ≤ Cg * ‖μ * v‖ := hLdev (μ * v) hμv
      rw [hA1eq] at hgb
      have hle : ‖μ * v‖ ≤ ‖v‖ := by
        rw [norm_mul]
        calc ‖μ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg v)
          _ = ‖v‖ := one_mul _
      calc ‖germC a h (μ * v) - tbA1‖ ≤ Cg * ‖μ * v‖ := hgb
        _ ≤ Cg * ‖v‖ := mul_le_mul_of_nonneg_left hle (le_of_lt hCgpos)
        _ ≤ Cg * ρs := mul_le_mul_of_nonneg_left hvρ (le_of_lt hCgpos)
        _ ≤ ρ / 2 := hCgρs
        _ ≤ ρ := by linarith [hρpos]
    have hlipv := hlip (fan a h (List.replicate j true ++ C) v) (germC a h (μ * v)) hX hY
    have hrunv := hrun μ hμ C hC0' hCμ j v hvr
    calc ‖FanTri.branchComp a ε₀ (fan a h (List.replicate j true ++ C) v)
            - FanTri.branchComp a ε₀ (germC a h (μ * v))‖
        ≤ L * ‖fan a h (List.replicate j true ++ C) v - germC a h (μ * v)‖ := hlipv
      _ ≤ L * (Kr * rate ^ j * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hrunv hLnn
      _ ≤ (L + 1) * (Kr * rate ^ j * ‖v‖ ^ 2) := by
          have hpos : 0 ≤ Kr * rate ^ j * ‖v‖ ^ 2 := by positivity
          nlinarith [hLnn, hpos]
      _ = ((L + 1) * Kr) * rate ^ j * ((eqLam a) ^ ε₀.length * ‖u‖) ^ 2 := by
          rw [hvn]; ring

end

end Work.EQ
