import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.V
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B2.chordPhase_exists
import Submission.Work.RPB.B5.chart_C12
import Submission.Work.RPB.B5.chart_rho_mono
import Submission.Work.RPB.B5.collar_exists_kappa
import Submission.Work.RPB.B5.exists_rho_per_kappa
import Submission.Work.RPB.B5.chordSurf_rhoChart_endpoint
import Submission.Work.RPB.B5.K0_chordSurf_level
import Submission.Work.RPV.chord_ends_ne
import Submission.Work.RPB.B5.lagData_per
import Submission.Work.RPB.B5.lagData_symm_v2
import Submission.Work.RPB.B5.lagData_std_v2
import Submission.Work.RPB.B5.lagData_lag_v2
import Submission.Work.RPB.B5.lagData_smooth
import Submission.Work.RPB.B5.lagData_imm
import Submission.Work.RPB.B5.lagData_inj
import Submission.Work.RPB.B5.lagData_start
import Submission.Work.RPB.B5.lagData_start_surj
import Submission.Work.RPB.B5.lagPt_noSpurious_restricted
import Submission.Work.RPB.B5.lagPt_chord
import Submission.Work.RPB.B5.collar_noSpurious_restricted

namespace Work.RPB.B5

/-!
# B5: the assembled Lagrangian family (`Work.RPB.B5.exists_lagFamily`)

The family is `ℓ τ (x,t) = lagPt D.W D.Γc D.Ac D.rho (clamp τ) x t`, where `D : LagData CI a` is
built from the sibling constructions and `clamp = Real.smoothTransition` is a smooth map into
`[0,1]` with `clamp 0 = 0`, `clamp 1 = 1`:

* `D.W` is the `ρ = r²`-chart of the chord annulus, `D.ρh` its level inverse on `(-κ,κ)`
  (`Work.RPB.B5.chart_C12` and `Work.RPB.B5.chart_rho_mono` for the monotonicity and the sign);
* `D.Γc`, `D.Ac` are the collar (`Work.RPB.B5.collar_exists_kappa`);
* `D.rho` is the monotone chord reparametrisation of the middle region
  (`Work.RPB.B5.exists_rho_per_kappa`).

The `τ`-clamp is what makes `ℓ` globally `C⁸` (`LagFamily.smooth` is a global statement) while all
the *value* conditions are only available on the isotopy slab `τ ∈ [0,1]`; note `clamp 0 = 0` and
`clamp 1 = 1`, so the `start`/`start_surj` fields and the two extra conjuncts are untouched.

Everything about `lagPt` (smoothness, periodicity, injectivity, immersion, the Lagrangian
condition, the standard zero section far away, the `τ = 0` slice, the symmetry, the two extra
conjuncts) is obtained from the sibling lemmas `lagData_*`, `lagPt_noSpurious_restricted` and
`lagPt_chord`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

/-- (Node B5 of the route, statement verbatim from the appendix of `RECTPEG_ROUTE_LEAD.md`.) -/
theorem exists_lagFamily (CI : Work.RPV.CurveIsotopy) :
    ∃ L : Work.RPV.LagFamily,
      (∀ θ : ℝ, 0 < θ → θ < Real.pi → ∀ x t x' t' (k : ℤ),
        L.ℓ 1 (x', t') = Work.RPV.Tk k (Work.RPV.tau θ (L.ℓ 1 (x, t))) →
          |x| < Real.sqrt 2 ∧ |x'| < Real.sqrt 2) ∧
      (∀ x t, |x| < Real.sqrt 2 → ∃ t₁ t₂ a : ℝ, CI.c 1 t₁ ≠ CI.c 1 t₂ ∧
        CI.c 1 t₁ - CI.c 1 t₂ = (‖CI.c 1 t₁ - CI.c 1 t₂‖ : ℂ) * Complex.exp (a * Complex.I) ∧
        L.ℓ 1 (x, t) = Work.RPV.chordPS (CI.c 1 t₁) (CI.c 1 t₂) a) := by
  classical
  -- ## the chord phase
  obtain ⟨a, ha⟩ := Work.RPB.B2.chordPhase_exists CI
  -- ## the chart and its level inverse
  obtain ⟨ρ₀, hπρ₀, W, hW12, hWper, hWchordIoo, ε, hε, hεle, ρh, hρh12, hρh0, hρhv, hρhl,
    hρhper, -⟩ := chart_C12 CI a ha
  have hρ₀ : 0 < ρ₀ := lt_trans (by positivity) hπρ₀
  -- the chord identity, closed at `r = π/2`
  have hWchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r := by
    intro τ hτ t r hr
    rcases lt_or_eq_of_le hr.2 with hlt | heq
    · exact hWchordIoo τ hτ t r ⟨hr.1, hlt⟩
    · subst heq
      exact chordSurf_rhoChart_endpoint CI a ha ρ₀ hρ₀ hπρ₀ W
        (hW12.of_le (by norm_num)) hWchordIoo τ hτ t
  -- ## monotonicity and sign of the level inverse
  obtain ⟨κ, hκ, hκle, hρhmono, hρhpos⟩ :=
    chart_rho_mono CI a ρ₀ ε W ρh hρ₀ hW12 hWchord hWper hε hεle hρh12 hρh0 hρhl
  -- ## the collar
  obtain ⟨σ₂, hσ₂, Γc, Ac, hΓsm, hAsm, hΓper, hAper, hlag, -, hemb, hfar, hτ0, hσjet⟩ :=
    collar_exists_kappa CI a ha ρ₀ hρ₀ hπρ₀ W ρh ε hε hW12 hWchord hWper hρh12 hρh0 hρhv hρhl
      hρhper
  -- ## the middle reparametrisation
  have hρh12' : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) :=
    (hρh12.of_le (by norm_num)).mono (by
      rintro ⟨τ, t, σ⟩ ⟨hτ, -, hσ⟩
      exact ⟨hτ, trivial, by
        rw [Set.mem_Ioo] at hσ ⊢
        exact ⟨by linarith [hσ.1, hκle], by linarith [hσ.2, hκle]⟩⟩)
  have hρhv' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀ := by
    intro τ hτ t σ hσ
    rw [Set.mem_Ioo] at hσ ⊢
    exact hρhv τ hτ t _ (by
      rw [Set.mem_Ioo]
      exact ⟨by linarith [hσ.1, hκle], by linarith [hσ.2, hκle]⟩)
  have hρhl' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      Work.RPV.K0 (W τ t (ρh τ t σ)) + 1 = -σ := by
    intro τ hτ t σ hσ
    rw [Set.mem_Ioo] at hσ
    exact hρhl τ hτ t σ (by
      rw [Set.mem_Ioo]
      exact ⟨by linarith [hσ.1, hκle], by linarith [hσ.2, hκle]⟩)
  obtain ⟨rho, hrhosm, hrhoper, hrhorng, hrhoval, hrhonearδ, hrhoderiv, hrho0, hrhom⟩ :=
    exists_rho_per_kappa CI a ha ρ₀ W ρh κ hρ₀ hπρ₀ hκ (hW12.of_le (by norm_num)) hWchord
      hρh12' hρh0 hρhv' hρhper hρhmono hρhpos hρhl'
  -- ## the packaged data
  let D : Work.RPB.B5.LagData CI a :=
    { W := W, Γc := Γc, Ac := Ac, rho := rho, ρh := ρh, ρ₀ := ρ₀, σ₂ := σ₂, κ := κ,
      hρ₀ := hρ₀, hσ₂ := hσ₂, hκ := hκ, hπρ₀ := hπρ₀,
      hWsm := hW12.of_le (by norm_num), hWchord := hWchord, hWper := hWper,
      hΓsm := hΓsm, hAsm := hAsm, hΓper := hΓper, hAper := hAper, hlag := hlag,
      hemb := hemb, hfar := hfar, hτ0 := hτ0,
      hρh := hρh12', hρh0 := hρh0, hρhv := hρhv', hρhl := hρhl', hρhper := hρhper,
      hρhmono := hρhmono, hρhpos := hρhpos,
      hrhosm := hrhosm, hrhoper := hrhoper, hrhorng := hrhorng, hrhoval := hrhoval,
      hrhoderiv := hrhoderiv, hrho0 := hrho0, hrhom := hrhom,
      hrhonearδ := hrhonearδ, σjet := hσjet }
  -- ## the clamp
  let st : ℝ → ℝ := Real.smoothTransition
  have hst_mem : ∀ τ : ℝ, st τ ∈ Set.Icc (0 : ℝ) 1 := fun τ =>
    ⟨Real.smoothTransition.nonneg τ, Real.smoothTransition.le_one τ⟩
  have hst0 : st 0 = 0 := Real.smoothTransition.zero_of_nonpos (le_refl 0)
  have hst1 : st 1 = 1 := Real.smoothTransition.one_of_one_le (le_refl 1)
  have hsmD := lagData_smooth CI a ha D
  -- the smoothness, transported through the clamp
  have hsm_st : ∀ τ' ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 1 (fun z : ℝ × ℝ => lagPt D.W D.Γc D.Ac D.rho τ' z.1 z.2) := by
    intro τ' hτ'
    have h := hsmD.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun z => ⟨hτ', trivial, trivial⟩)
    exact h.of_le (by norm_num)
  -- ## the two extra conjuncts
  have hK : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      -1 < Work.RPV.K0 (W τ t (rho τ x t)) := by
    intro τ hτ x hx t
    obtain ⟨hr0, hr1⟩ := hrhoval τ hτ x hx t
    set r : ℝ := Real.sqrt (rho τ x t) with hrdef
    have hr2 : r ^ 2 = rho τ x t := by rw [hrdef]; exact Real.sq_sqrt hr0.le
    have hsq : Real.sqrt (Real.pi ^ 2 / 4) = Real.pi / 2 := by
      rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hrle : r ≤ Real.pi / 2 := (Real.sqrt_le_sqrt hr1).trans_eq hsq
    have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hr0
    have hne : CI.c τ (t + r) ≠ CI.c τ (t - r) :=
      Work.RPV.chord_ends_ne CI hτ ⟨hrpos, by linarith [Real.pi_pos, hrle]⟩
    have hhalf : Work.RPB.halfChord CI.c τ t r ≠ 0 := by
      intro hzero
      apply hne
      have hv : Work.RPB.chordVec CI.c τ t r = 0 := by
        rw [Work.RPB.B5.chordVec_eq_smul_halfChord, hzero, mul_zero]
      simpa only [Work.RPB.chordVec, sub_eq_zero] using hv
    have hkey : Work.RPV.K0 (W τ t (rho τ x t)) + 1
        = r ^ 2 * ‖Work.RPB.halfChord CI.c τ t r‖ ^ 2 := by
      rw [← hr2, hWchord τ hτ t r ⟨hrpos, hrle⟩]
      exact Work.RPB.B5.K0_chordSurf_level CI.c a τ t r
    have hpos : 0 < r ^ 2 * ‖Work.RPB.halfChord CI.c τ t r‖ ^ 2 :=
      mul_pos (pow_pos hrpos 2) (pow_pos (norm_pos_iff.mpr hhalf) 2)
    linarith [hkey, hpos]
  have hnosp := collar_noSpurious_restricted Γc Ac hΓper hAper hemb
  have hnosp' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ θ : ℝ, 0 < θ → θ < Real.pi →
      ∀ x t x' t' (k : ℤ),
      lagPt W Γc Ac rho τ x' t' = Work.RPV.Tk k (Work.RPV.tau θ (lagPt W Γc Ac rho τ x t)) →
        |x| < Real.sqrt 2 ∧ |x'| < Real.sqrt 2 :=
    lagPt_noSpurious_restricted W Γc Ac rho hK hΓper hAper hemb hnosp
  -- ## the family
  refine ⟨{ ℓ := fun τ z => lagPt D.W D.Γc D.Ac D.rho (st τ) z.1 z.2,
            smooth := ?_, per := ?_, inj := ?_, imm := ?_, lag := ?_,
            X0 := Real.sqrt (2 + 2 * σ₂), std := ?_, start := ?_, start_surj := ?_,
            symm := ?_ }, ?_, ?_⟩
  · -- `smooth`
    have hφ : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ((st z.1, z.2) : ℝ × (ℝ × ℝ))) := by
      have h1 : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Real.smoothTransition z.1) := by
        fun_prop
      exact h1.prodMk contDiff_snd
    exact hsmD.comp_contDiff hφ (fun z => ⟨hst_mem z.1, trivial, trivial⟩)
  · -- `per`
    intro τ x t
    show lagPt D.W D.Γc D.Ac D.rho (st τ) x (t + 2 * Real.pi)
      = Work.RPV.Tk 1 (lagPt D.W D.Γc D.Ac D.rho (st τ) x t)
    exact lagData_per CI a ha D (st τ) x t
  · -- `inj`
    intro τ hτ x t x' t' k h
    show x' = x ∧ ∃ m : ℤ, t' = t + 2 * Real.pi * m
    exact lagData_inj CI a ha D (st τ) (hst_mem τ) x t x' t' k h
  · -- `imm`
    intro τ hτ x t u v h
    show u = 0 ∧ v = 0
    exact lagData_imm CI a ha D hsm_st (st τ) (hst_mem τ) x t u v h
  · -- `lag`
    intro τ x t
    show Work.RPV.symp
      (deriv (fun y => lagPt D.W D.Γc D.Ac D.rho (st τ) y t) x)
      (deriv (fun s => lagPt D.W D.Γc D.Ac D.rho (st τ) x s) t) = 0
    exact lagData_lag_v2 CI a ha D (st τ) (hst_mem τ) x t
  · -- `std`
    intro τ x t hx
    show lagPt D.W D.Γc D.Ac D.rho (st τ) x t = Work.RPV.stdZ x t
    exact lagData_std_v2 CI a ha D (st τ) (hst_mem τ) x t hx
  · -- `start`
    intro x t
    show lagPt D.W D.Γc D.Ac D.rho (st 0) x t ∈ Work.RPV.Zsec
    rw [hst0]
    exact lagData_start CI a ha D x t
  · -- `start_surj`
    intro z hz
    obtain ⟨x, t, hxt⟩ := lagData_start_surj CI a ha D z hz
    exact ⟨x, t, by rw [hst0]; exact hxt⟩
  · -- `symm`
    intro τ x t
    show lagPt D.W D.Γc D.Ac D.rho (st τ) (-x) (t + Real.pi)
      = Work.RPV.tau Real.pi (lagPt D.W D.Γc D.Ac D.rho (st τ) x t)
    exact lagData_symm_v2 CI a ha D (st τ) (hst_mem τ) x t
  · -- the "no spurious coincidences" conjunct, at `τ = 1`
    intro θ hθ0 hθπ x t x' t' k h
    have h' : lagPt D.W D.Γc D.Ac D.rho (st 1) x' t'
        = Work.RPV.Tk k (Work.RPV.tau θ (lagPt D.W D.Γc D.Ac D.rho (st 1) x t)) := h
    rw [hst1] at h'
    exact hnosp' 1 (by norm_num) θ hθ0 hθπ x t x' t' k h'
  · -- the chord identification, at `τ = 1`
    intro x t hx
    obtain ⟨t₁, t₂, a', hne, hphase, hpt⟩ :=
      lagPt_chord CI a ha ρ₀ W (hW12.of_le (by norm_num)) hWchord Γc Ac rho hrhoval
        1 (by norm_num) x t hx
    refine ⟨t₁, t₂, a', hne, hphase, ?_⟩
    show lagPt D.W D.Γc D.Ac D.rho (st 1) x t
      = Work.RPV.chordPS (CI.c 1 t₁) (CI.c 1 t₂) a'
    rw [hst1]
    exact hpt

end

end Work.RPB.B5
