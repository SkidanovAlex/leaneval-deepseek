import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.BoxRegAux.Defs
import Submission.Work.FTS_EllLimOK.BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials
import Submission.Work.FTS_EllLimOK.BoxDataH.contDiffOn_two_of_fderivWithin_data
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_EllLimOK.ProducerH.SecondDeriv.second_theta_deriv_le_Xn6
import Submission.Work.FTS_EllLimOK.ProducerH.ThetaZero.tendsto_of_deriv_bounded
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.hasDerivWithinAt_of_tendsto_deriv
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS_EllLimOK/ProducerH/BoxAux/BoxC2` — the closed-box `C²`-regularity of `E g`

The first clause of `RulingELF.PkgBoxH`: `ContDiffOn ℝ 2 (uncurry (E g)) (cbox a₀ b₀)`.

## Route

The function `E g` is `C^∞` on the *open* quadrant (`SmoothOpen`, a field of `EllClassOk`) and
the two boundary lines `θ = 0`, `θ = π/2` carry the prescribed values `E g z 0 = E g z (π/2) = 0`
(`IsBslSol`), which by `BoxAux.Trace` are also the one-sided limits.  The whole content of the
clause is therefore the *one-sided differentiability* of the slices at the two endpoints.

The assembly is the staircase of `BoxRegAux.hasFDerivWithinAt_of_uniform_slice_partials`, applied
with the *constant* family `H n = E g` three times (to `E g`, to `∂_z (E g)`, and to the
θ-slope), followed by `BoxDataH.contDiffOn_two_of_fderivWithin_data`.  The two slopes are
`derivWithin`-versions of the partials on the closed intervals, so that their boundary values are
the one-sided derivatives:

* `thSlope W z θ = ∂_θ^{[0,π/2]} W z ·(θ)`, `zSlope a b W z θ = ∂_z^{[a,b]} W · θ(z)`.

The one-sided derivatives at the endpoints exist because the interior derivatives have limits
there: `∂_θ (E g)` is bounded (`second_theta_deriv_DzIter_le_Xn6`, level `0`) and
`∂_θ∂_z (E g)` is bounded (level `1`), so `tendsto_of_deriv_bounded` gives their one-sided limits,
and `hasDerivWithinAt_of_tendsto_deriv` converts those into the within-derivatives.

Everything here is `sorry`-free.
-/
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The θ-slope on the closed interval `[0,π/2]`**: the within-derivative of the `θ`-slice,
whose value at the two endpoints is the corresponding one-sided derivative. -/
noncomputable def thSlope (W : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  derivWithin (fun θ' => W z θ') (Set.Icc 0 (Real.pi / 2)) θ

/-- **The `z`-slope on the closed interval `[a,b]`**. -/
noncomputable def zSlope (a b : ℝ) (W : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  derivWithin (fun z' => W z' θ) (Set.Icc a b) z

theorem thSlope_of_mem_Ioo {W : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    thSlope W z θ = deriv (fun θ' => W z θ') θ := by
  rw [thSlope]
  exact derivWithin_of_mem_nhds
    (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hθ)
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))

theorem zSlope_of_mem_Ioo {W : ℝ → ℝ → ℝ} {a b z θ : ℝ} (hz : z ∈ Set.Ioo a b) :
    zSlope a b W z θ = deriv (fun z' => W z' θ) z := by
  rw [zSlope]
  exact derivWithin_of_mem_nhds
    (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz)
      (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩))


/-! ## A uniform `θ`-modulus and the vertical lines give continuity on the box -/

/-- **Continuity on the vertical lines of the box from a uniform `θ`-modulus.** -/
theorem continuousOn_line_of_thetaModulus {F : ℝ → ℝ → ℝ} {C β : ℝ} {a₀ b₀ : ℝ}
    (hβ : 0 < β)
    (hmod : ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      ∀ θ' ∈ Set.Icc 0 (Real.pi / 2), |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β)
    (hint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousOn (fun z => F z θ) (Set.Icc a₀ b₀)) :
    ∀ θ ∈ Set.Icc 0 (Real.pi / 2), ContinuousOn (fun z => F z θ) (Set.Icc a₀ b₀) := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    by_cases hC : C ≤ 0
    · have hconst : ∀ z ∈ Set.Icc a₀ b₀, F z 0 = F z (Real.pi / 4) := by
        intro z hz
        have h1 := hmod z hz 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩ (Real.pi / 4)
          ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have h2 : C * |(0 : ℝ) - Real.pi / 4| ^ β ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
        have h3 : |F z 0 - F z (Real.pi / 4)| = 0 :=
          le_antisymm (le_trans h1 h2) (abs_nonneg _)
        exact sub_eq_zero.mp (abs_eq_zero.mp h3)
      exact (hint (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).congr
        (fun z hz => hconst z hz)
    · have hCpos : 0 < C := not_le.mp hC
      refine fun z hz => ?_
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hbase : 0 < ε / (8 * C) := by positivity
      set θ₀ : ℝ := min (Real.pi / 4) (min 1 ((ε / (8 * C)) ^ (1 / β))) with hθ₀def
      have hθ₀pos : 0 < θ₀ :=
        lt_min (by linarith [Real.pi_pos]) (lt_min one_pos (Real.rpow_pos_of_pos hbase _))
      have hθ₀lt : θ₀ < Real.pi / 2 :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos])
      have hθ₀le : θ₀ ≤ (ε / (8 * C)) ^ (1 / β) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hpoweq : ((ε / (8 * C)) ^ (1 / β)) ^ β = ε / (8 * C) := by
        rw [← Real.rpow_mul hbase.le]
        have h1 : 1 / β * β = 1 := by field_simp
        rw [h1, Real.rpow_one]
      have hpow : θ₀ ^ β ≤ ε / (8 * C) :=
        calc θ₀ ^ β ≤ ((ε / (8 * C)) ^ (1 / β)) ^ β :=
              Real.rpow_le_rpow (le_of_lt hθ₀pos) hθ₀le hβ.le
          _ = ε / (8 * C) := hpoweq
      have hsmall : C * θ₀ ^ β ≤ ε / 8 := by
        have h1 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
        have h2 : C * (ε / (8 * C)) = ε / 8 := by field_simp
        linarith [h1, h2]
      obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp
        ((hint θ₀ ⟨hθ₀pos, hθ₀lt⟩).continuousWithinAt hz) (ε / 2) (by linarith)
      refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
      have hz0 : |(0 : ℝ) - θ₀| = θ₀ := by rw [abs_sub_comm, sub_zero, abs_of_pos hθ₀pos]
      have h1 : |F z' 0 - F z' θ₀| ≤ C * θ₀ ^ β := by
        have h := hmod z' hz' 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩ θ₀
          ⟨le_of_lt hθ₀pos, le_of_lt hθ₀lt⟩
        rwa [hz0] at h
      have h2 : |F z' θ₀ - F z θ₀| < ε / 2 := by
        have h := hδ hz' hdist
        rwa [Real.dist_eq] at h
      have h3 : |F z θ₀ - F z 0| ≤ C * θ₀ ^ β := by
        have h := hmod z hz 0 ⟨le_rfl, by linarith [Real.pi_pos]⟩ θ₀
          ⟨le_of_lt hθ₀pos, le_of_lt hθ₀lt⟩
        rw [hz0, abs_sub_comm] at h
        exact h
      rw [Real.dist_eq]
      calc |F z' 0 - F z 0|
          ≤ |F z' 0 - F z' θ₀| + |F z' θ₀ - F z θ₀| + |F z θ₀ - F z 0| := by
            rw [show F z' 0 - F z 0
              = (F z' 0 - F z' θ₀) + (F z' θ₀ - F z θ₀) + (F z θ₀ - F z 0) from by ring]
            exact abs_add_three _ _ _
        _ < ε := by linarith [h1, h2, h3, hsmall]
  · rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      by_cases hC : C ≤ 0
      · have hconst : ∀ z ∈ Set.Icc a₀ b₀, F z (Real.pi / 2) = F z (Real.pi / 4) := by
          intro z hz
          have h1 := hmod z hz (Real.pi / 2)
            ⟨by linarith [Real.pi_pos], le_rfl⟩ (Real.pi / 4)
            ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
          have h2 : C * |Real.pi / 2 - Real.pi / 4| ^ β ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
          have h3 : |F z (Real.pi / 2) - F z (Real.pi / 4)| = 0 :=
            le_antisymm (le_trans h1 h2) (abs_nonneg _)
          exact sub_eq_zero.mp (abs_eq_zero.mp h3)
        exact (hint (Real.pi / 4) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).congr
          (fun z hz => hconst z hz)
      · have hCpos : 0 < C := not_le.mp hC
        refine fun z hz => ?_
        rw [Metric.continuousWithinAt_iff]
        intro ε hε
        have hbase : 0 < ε / (8 * C) := by positivity
        set δ₀ : ℝ := min (Real.pi / 4) (min 1 ((ε / (8 * C)) ^ (1 / β))) with hδ₀def
        set θ₀ : ℝ := Real.pi / 2 - δ₀ with hθ₀def
        have hδ₀pos : 0 < δ₀ :=
          lt_min (by linarith [Real.pi_pos]) (lt_min one_pos (Real.rpow_pos_of_pos hbase _))
        have hδ₀le : δ₀ ≤ (ε / (8 * C)) ^ (1 / β) :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        have hpoweq : ((ε / (8 * C)) ^ (1 / β)) ^ β = ε / (8 * C) := by
          rw [← Real.rpow_mul hbase.le]
          have h1 : 1 / β * β = 1 := by field_simp
          rw [h1, Real.rpow_one]
        have hpow : δ₀ ^ β ≤ ε / (8 * C) :=
          calc δ₀ ^ β ≤ ((ε / (8 * C)) ^ (1 / β)) ^ β :=
                Real.rpow_le_rpow (le_of_lt hδ₀pos) hδ₀le hβ.le
            _ = ε / (8 * C) := hpoweq
        have hsmall : C * δ₀ ^ β ≤ ε / 8 := by
          have h1 := mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
          have h2 : C * (ε / (8 * C)) = ε / 8 := by field_simp
          linarith [h1, h2]
        have hθ₀mem : θ₀ ∈ Set.Ioo 0 (Real.pi / 2) := by
          have h1 : δ₀ ≤ Real.pi / 4 := min_le_left _ _
          constructor <;> simp only [hθ₀def] <;> linarith [Real.pi_pos]
        obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp
          ((hint θ₀ hθ₀mem).continuousWithinAt hz) (ε / 2) (by linarith)
        refine ⟨δ, hδpos, fun z' hz' hdist => ?_⟩
        have h1 : |F z' (Real.pi / 2) - F z' θ₀| ≤ C * δ₀ ^ β := by
          have h := hmod z' hz' (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩ θ₀
            ⟨le_of_lt hθ₀mem.1, le_of_lt hθ₀mem.2⟩
          have h2 : |Real.pi / 2 - θ₀| = δ₀ := by simp only [hθ₀def]; ring_nf; rw [abs_of_pos hδ₀pos]
          rwa [h2] at h
        have h2 : |F z' θ₀ - F z θ₀| < ε / 2 := by
          have h := hδ hz' hdist
          rwa [Real.dist_eq] at h
        have h3 : |F z θ₀ - F z (Real.pi / 2)| ≤ C * δ₀ ^ β := by
          have h := hmod z hz (Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩ θ₀
            ⟨le_of_lt hθ₀mem.1, le_of_lt hθ₀mem.2⟩
          have h2 : |Real.pi / 2 - θ₀| = δ₀ := by simp only [hθ₀def]; ring_nf; rw [abs_of_pos hδ₀pos]
          rw [h2, abs_sub_comm] at h
          exact h
        rw [Real.dist_eq]
        calc |F z' (Real.pi / 2) - F z (Real.pi / 2)|
            ≤ |F z' (Real.pi / 2) - F z' θ₀| + |F z' θ₀ - F z θ₀|
              + |F z θ₀ - F z (Real.pi / 2)| := by
              rw [show F z' (Real.pi / 2) - F z (Real.pi / 2)
                = (F z' (Real.pi / 2) - F z' θ₀) + (F z' θ₀ - F z θ₀)
                  + (F z θ₀ - F z (Real.pi / 2)) from by ring]
              exact abs_add_three _ _ _
          _ < ε := by linarith [h1, h2, h3, hsmall]
    · exact hint θ ⟨h0, hp⟩

/-- **A uniform `θ`-modulus, plus continuity on the interior vertical lines, gives continuity on
the closed box.** -/
theorem continuousOn_of_thetaModulus {F : ℝ → ℝ → ℝ} {C β : ℝ} {a₀ b₀ : ℝ}
    (hβ : 0 < β)
    (hmod : ∀ z ∈ Set.Icc a₀ b₀, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
      ∀ θ' ∈ Set.Icc 0 (Real.pi / 2), |F z θ - F z θ'| ≤ C * |θ - θ'| ^ β)
    (hint : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContinuousOn (fun z => F z θ) (Set.Icc a₀ b₀)) :
    ContinuousOn (Function.uncurry F) (cbox a₀ b₀) := by
  have hline := continuousOn_line_of_thetaModulus (a₀ := a₀) (b₀ := b₀) hβ hmod hint
  intro p hp
  obtain ⟨z, θ⟩ := p
  rw [mem_cbox] at hp
  obtain ⟨hz, hθ⟩ := hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousWithinAt_iff.mp
    ((hline θ hθ).continuousWithinAt hz) (ε / 2) (by linarith)
  have hmodδ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ θ' ∈ Set.Icc 0 (Real.pi / 2),
      |θ' - θ| < δ₁ → C * |θ' - θ| ^ β < ε / 2 := by
    by_cases hC : C ≤ 0
    · refine ⟨1, one_pos, fun θ' _ _ => ?_⟩
      have : C * |θ' - θ| ^ β ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
      linarith
    · have hCpos : 0 < C := not_le.mp hC
      have hbase : 0 < ε / (4 * C) := by positivity
      refine ⟨min 1 ((ε / (4 * C)) ^ (1 / β)), lt_min one_pos (Real.rpow_pos_of_pos hbase _),
        fun θ' _ hlt => ?_⟩
      have hle : |θ' - θ| ≤ (ε / (4 * C)) ^ (1 / β) :=
        le_of_lt (lt_of_lt_of_le hlt (min_le_right _ _))
      have h1 : |θ' - θ| ^ β ≤ (ε / (4 * C)) := by
        calc |θ' - θ| ^ β ≤ ((ε / (4 * C)) ^ (1 / β)) ^ β :=
              Real.rpow_le_rpow (abs_nonneg _) hle hβ.le
          _ = ε / (4 * C) := by
              rw [← Real.rpow_mul hbase.le]
              have h2 : 1 / β * β = 1 := by field_simp
              rw [h2, Real.rpow_one]
      have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
      have h4 : C * (ε / (4 * C)) = ε / 4 := by field_simp
      linarith [h3, h4]
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hmodδ
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun q hq hdist => ?_⟩
  obtain ⟨z', θ'⟩ := q
  rw [mem_cbox] at hq
  obtain ⟨hz', hθ'⟩ := hq
  have hd : dist (z', θ') (z, θ) = max |z' - z| |θ' - θ| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have hzclose : |z' - z| < δ₂ := by
    rw [hd] at hdist
    exact lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hdist (min_le_right _ _))
  have hthclose : |θ' - θ| < δ₁ := by
    rw [hd] at hdist
    exact lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hdist (min_le_left _ _))
  have h1 : |F z' θ' - F z' θ| < ε / 2 := by
    have h := hmod z' hz' θ hθ θ' hθ'
    have h2 := hδ₁ θ' hθ' hthclose
    have habs : |θ - θ'| ^ β = |θ' - θ| ^ β := by rw [abs_sub_comm]
    rw [habs] at h
    rw [abs_sub_comm (F z' θ) (F z' θ')] at h
    exact lt_of_le_of_lt h h2
  have h2 : |F z' θ - F z θ| < ε / 2 := by
    have h := hδ₂ hz' hzclose
    rwa [Real.dist_eq] at h
  rw [Real.dist_eq, Function.uncurry_apply_pair, Function.uncurry_apply_pair]
  calc |F z' θ' - F z θ| ≤ |F z' θ' - F z' θ| + |F z' θ - F z θ| := by
        rw [show F z' θ' - F z θ = (F z' θ' - F z' θ) + (F z' θ - F z θ) from by ring]
        exact abs_add_le _ _
    _ < ε := by linarith

end Work.FTS_EllLimOK.ProducerH.BoxAux

