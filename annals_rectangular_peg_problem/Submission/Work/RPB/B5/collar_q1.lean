import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff

/-!
# The collar's `q₁`-coordinate at `τ = 0`

The collar of a `LagData D` sits on the levels `σ ≥ 0`; its `K₀`-level point at `τ = 0` is
`P(σ,t) = levelPt (D.Γc 0 σ t) σ (D.Ac 0 σ t)`.

The field `D.hτ0` says that `P(σ,t)` lies in the zero section `p = 0` for `σ ≥ 0`, so its
`q₁`-coordinate has square `2 + 2σ` (the point has level `K₀ = -1 - σ`).  The *sign* is pinned by
the far field `D.hfar`: for `σ ≥ σ₂` the collar is the standard circle
`√(2+2σ)·e^{i(t-π/2)}` with phase `t`, whose `q₁`-coordinate is `-√(2+2σ) < 0`.  Since the
`q₁`-coordinate is continuous in `σ` (the `σ`-slices of `Γc` and `Ac` are smooth, `D.hΓsm`,
`D.hAsm`, once the third argument is shifted into `{t ≥ 0}` using the `2π`-quasi-periodicity)
and never vanishes, it cannot change sign: hence `q₁ = -√(2+2σ)` for every `σ ≥ 0`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- Iterating the quasi-periodicity relation `f τ σ (t + 2π) = f τ σ t + c`. -/
private lemma quasi_periodic_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E)
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c) (k : ℕ) (τ σ t : ℝ) :
    f τ σ (t + 2 * Real.pi * (k : ℝ)) = f τ σ t + (k : ℝ) • c := by
  induction k generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    rw [show t + 2 * Real.pi * ((n : ℝ) + 1)
        = (t + 2 * Real.pi * (n : ℝ)) + 2 * Real.pi by ring]
    rw [hper τ σ (t + 2 * Real.pi * (n : ℝ)), ih t]
    rw [add_smul, one_smul]
    abel

/-- If `f` is `C⁸` on the set where the third argument is `≥ 0` (and the first lies in `s`),
and quasi-periodic in the third argument with shift `c`, then every `σ`-slice (varying the
second argument) is `C⁸` on the whole line: shifting the third argument into the half line
`{t ≥ 0}` (`f τ σ (t + 2πk) = f τ σ t + k • c`) makes the slice smooth. -/
private lemma contDiffOn_slice_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ → ℝ → E) (c : E) (s : Set ℝ)
    (hsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (s ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)))
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t + c) :
    ∀ τ ∈ s, ∀ t, ContDiffOn ℝ 8 (fun σ : ℝ => f τ σ t) Set.univ := by
  intro τ hτ t
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < t + 2 * Real.pi * (k : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (-t / (2 * Real.pi))
    refine ⟨k, ?_⟩
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := mul_lt_mul_of_pos_right hk hπ
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h
    linarith
  have hshift : ContDiffOn ℝ 8 (fun σ : ℝ => f τ σ (t + 2 * Real.pi * (k : ℝ))) Set.univ := by
    have hg : ContDiff ℝ 8 (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ)))) := by fun_prop
    have hmt : Set.MapsTo (fun σ : ℝ => (τ, (σ, t + 2 * Real.pi * (k : ℝ)))) Set.univ
        (s ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) := fun σ _ => ⟨hτ, Set.mem_univ _, le_of_lt hk⟩
    have h := hsm.comp hg.contDiffOn hmt
    simpa only [Function.comp_def] using h
  have heq : (fun σ : ℝ => f τ σ t)
      = fun σ : ℝ => f τ σ (t + 2 * Real.pi * (k : ℝ)) - (k : ℝ) • c := by
    funext σ
    rw [quasi_periodic_nat f c hper k τ σ t]
    abel
  rw [heq]
  exact hshift.sub contDiffOn_const

/-- The first coordinate of the far circle point: for the far shape
`√s · e^{i(t-π/2)}` with phase `t`, the `q₁`-coordinate is `-√s`. -/
private lemma far_levelPt_fst (s σ t : ℝ) :
    (Work.RPV.levelPt (((Real.sqrt s : ℝ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I))
      σ t).1.1 = -Real.sqrt s := by
  simp only [Work.RPV.levelPt]
  set c : ℂ := ((Real.sqrt s : ℝ) : ℂ) with hc
  have harg : -(t : ℂ) * Complex.I + (t - Real.pi / 2) * Complex.I
      = -(Real.pi / 2 : ℂ) * Complex.I := by ring
  have hexp : Complex.exp (-(Real.pi / 2 : ℂ) * Complex.I) = -Complex.I := by
    rw [show -(Real.pi / 2 : ℂ) * Complex.I = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  have he : Complex.exp (-(t : ℂ) * Complex.I) * (c * Complex.exp ((t - Real.pi / 2) * Complex.I))
      = -(c * Complex.I) := by
    calc Complex.exp (-(t : ℂ) * Complex.I) * (c * Complex.exp ((t - Real.pi / 2) * Complex.I))
        = c * (Complex.exp (-(t : ℂ) * Complex.I)
            * Complex.exp ((t - Real.pi / 2) * Complex.I)) := by ring
      _ = c * Complex.exp (-(t : ℂ) * Complex.I + (t - Real.pi / 2) * Complex.I) := by
            rw [Complex.exp_add]
      _ = c * Complex.exp (-(Real.pi / 2 : ℂ) * Complex.I) := by rw [harg]
      _ = c * (-Complex.I) := by rw [hexp]
      _ = -(c * Complex.I) := by ring
  rw [he]
  simp [hc]

theorem collar_q1 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ σ : ℝ, 0 ≤ σ → ∀ t : ℝ,
      (Work.RPV.levelPt (D.Γc 0 σ t) σ (D.Ac 0 σ t)).1.1 = -Real.sqrt (2 + 2 * σ) := by
  intro σ hσ t
  set q : ℝ → ℝ := fun s => (Work.RPV.levelPt (D.Γc 0 s t) s (D.Ac 0 s t)).1.1 with hq
  change q σ = -Real.sqrt (2 + 2 * σ)
  -- (1) `q s ^ 2 = 2 + 2 s` for `s ≥ 0`
  have hqsq : ∀ s : ℝ, 0 ≤ s → (q s) ^ 2 = 2 + 2 * s := by
    intro s hs
    have hP2 : (Work.RPV.levelPt (D.Γc 0 s t) s (D.Ac 0 s t)).2 = 0 := D.hτ0 s hs t
    have hK := Work.RPV.K0_levelPt (D.Γc 0 s t) s (D.Ac 0 s t)
    have h1 : (Work.RPV.levelPt (D.Γc 0 s t) s (D.Ac 0 s t)).2.1 = 0 := by
      have := congrArg Prod.fst hP2; simpa using this
    have h2 : (Work.RPV.levelPt (D.Γc 0 s t) s (D.Ac 0 s t)).2.2 = 0 := by
      have := congrArg Prod.snd hP2; simpa using this
    rw [Work.RPV.K0, h1, h2] at hK
    simp only [hq]
    linarith
  -- (2) continuity of `q` on `[0, σ₂]`
  have hΓco : ContDiffOn ℝ 8 (fun s : ℝ => D.Γc 0 s t) Set.univ :=
    contDiffOn_slice_snd D.Γc 0 (Set.Icc (0 : ℝ) 1) D.hΓsm
      (fun τ σ t => by rw [D.hΓper τ σ t, add_zero]) 0 (by norm_num) t
  have hAco : ContDiffOn ℝ 8 (fun s : ℝ => D.Ac 0 s t) Set.univ :=
    contDiffOn_slice_snd D.Ac (2 * Real.pi) (Set.Icc (0 : ℝ) 1) D.hAsm
      (fun τ σ t => D.hAper τ σ t) 0 (by norm_num) t
  have hPt : ContDiffOn ℝ 8 (fun s : ℝ => Work.RPV.levelPt (D.Γc 0 s t) s (D.Ac 0 s t))
      Set.univ :=
    chartJets_levelPt_contDiff.contDiffOn.comp
      (hΓco.prodMk (contDiffOn_id.prodMk hAco)) (fun s _ => Set.mem_univ _)
  have hqco : ContDiffOn ℝ 8 q Set.univ := by
    have h := hPt.fst.fst
    simpa only [hq] using h
  have hqc : ContinuousOn q (Set.Icc (0 : ℝ) D.σ₂) :=
    hqco.continuousOn.mono (fun s _ => Set.mem_univ s)
  -- (3) the value at `σ₂`
  have hfar₂ : q D.σ₂ = -Real.sqrt (2 + 2 * D.σ₂) := by
    obtain ⟨hG, hA⟩ := D.hfar 0 (by norm_num) D.σ₂ le_rfl t
    simp only [hq]
    rw [hG, hA]
    exact far_levelPt_fst (2 + 2 * D.σ₂) D.σ₂ t
  -- (4) `q σ ≤ 0`
  have hqle : q σ ≤ 0 := by
    by_cases hle : σ ≤ D.σ₂
    · by_contra hcon
      rw [not_le] at hcon
      have hcont' : ContinuousOn q (Set.Icc σ D.σ₂) :=
        hqc.mono (fun x hx => ⟨le_trans hσ hx.1, hx.2⟩)
      have hmem : (0 : ℝ) ∈ Set.Icc (q D.σ₂) (q σ) := by
        refine ⟨?_, le_of_lt hcon⟩
        rw [hfar₂]
        exact neg_nonpos.mpr (Real.sqrt_nonneg _)
      obtain ⟨c, hc, hcq⟩ := intermediate_value_Icc' hle hcont' hmem
      have hsq := hqsq c (le_trans hσ hc.1)
      rw [hcq] at hsq
      have hpos : (0 : ℝ) < 2 + 2 * c := by linarith [le_trans hσ hc.1]
      linarith
    · have hlt : D.σ₂ < σ := not_le.mp hle
      have hfarσ : q σ = -Real.sqrt (2 + 2 * σ) := by
        obtain ⟨hG, hA⟩ := D.hfar 0 (by norm_num) σ (le_of_lt hlt) t
        simp only [hq]
        rw [hG, hA]
        exact far_levelPt_fst (2 + 2 * σ) σ t
      rw [hfarσ]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  -- (5) conclude from the square and the sign
  have hs : (Real.sqrt (2 + 2 * σ)) ^ 2 = 2 + 2 * σ := Real.sq_sqrt (by linarith)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show (q σ) ^ 2 = (Real.sqrt (2 + 2 * σ)) ^ 2 by
    rw [hqsq σ hσ, hs]) with h | h
  · exfalso
    have hpos : 0 < Real.sqrt (2 + 2 * σ) := Real.sqrt_pos_of_pos (by linarith)
    linarith [hqle, h]
  · exact h

end Work.RPB.B5
