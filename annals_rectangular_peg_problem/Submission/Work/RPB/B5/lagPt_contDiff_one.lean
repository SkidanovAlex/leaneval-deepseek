import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff
import Submission.Work.RPB.B5.lagData_per
import Submission.Work.RPB.B2.chordSurf_period_swap
import Submission.Work.RPB.B5.lagData_junction_negSqrt2
import Submission.Work.RPB.B5.lagData_junction_zero
import Submission.Work.RPB.B5.glueC1

/-!
# B5: `lagPt` is `C¹` in `(x,t)`

This file proves `Work.RPB.B5.lagPt_contDiff_one`, needed for the `smooth` field of the assembled
`LagFamily`.  The assembled point is

`lagPt …τ x t = if x ≤ 0 then basePt …τ x t else tau π (basePt …τ (-x) (t-π))`,
`basePt …τ x t = if x ≤ -√2 then collarPt …τ (sig x) t else W τ t (rho τ x t)`.

The proof separates the three junctions `x = -√2`, `x = 0`, `x = √2` (the last transported by
`tau π`), using `Work.RPB.B5.glueC1` at each junction and the interface lemmas
`Work.RPB.B5.lagData_junction_negSqrt2` and `Work.RPB.B5.lagData_junction_zero` for the matching
of the one-sided jets.
-/

namespace Work.RPB.B5

open scoped ContDiff Topology

open Filter

set_option autoImplicit false

noncomputable section

variable {CI : Work.RPV.CurveIsotopy} {a : ℝ → ℝ → ℝ → ℝ}

/-! ## Smoothness of the basic maps -/

/-- `Tk n` is smooth (a shear of the angle coordinate). -/
theorem contDiff_Tk (n : ℤ) : ContDiff ℝ 1 (fun x : Work.RPV.PS => Work.RPV.Tk n x) := by
  simp only [Work.RPV.Tk]
  fun_prop

/-- `tau θ` is smooth (affine in the `(q₁,p₁)`-plane, translation of `q₂`). -/
theorem contDiff_tau (θ : ℝ) : ContDiff ℝ 1 (fun x : Work.RPV.PS => Work.RPV.tau θ x) := by
  simp only [Work.RPV.tau]
  fun_prop

/-- `sig x = x²/2 - 1` is smooth. -/
theorem contDiff_sig : ContDiff ℝ 8 (fun x : ℝ => sig x) := by
  simp only [sig]
  fun_prop

/-! ## The collar branch is globally smooth -/

/-- The collar branch is smooth where `Γc`, `Ac` are, i.e. on the half-space `t ≥ 0`. -/
theorem contDiffOn_collarPt_half (D : LagData CI a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => collarPt D.Γc D.Ac τ (sig z.1) z.2)
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
  have hφ : ContDiffOn ℝ 8 (fun z : ℝ × ℝ => (τ, (sig z.1, z.2)))
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    (contDiff_const.prodMk ((contDiff_sig.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
  have hΓ : ContDiffOn ℝ 8 (fun z : ℝ × ℝ => D.Γc τ (sig z.1) z.2)
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
    have h := D.hΓsm.comp hφ (fun z hz => ⟨hτ, trivial, hz.2⟩)
    simpa only [Function.comp_def] using h
  have hA : ContDiffOn ℝ 8 (fun z : ℝ × ℝ => D.Ac τ (sig z.1) z.2)
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
    have h := D.hAsm.comp hφ (fun z hz => ⟨hτ, trivial, hz.2⟩)
    simpa only [Function.comp_def] using h
  have hsig : ContDiffOn ℝ 8 (fun z : ℝ × ℝ => sig z.1) (Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    (contDiff_sig.comp contDiff_fst).contDiffOn
  have hpair : ContDiffOn ℝ 8 (fun z : ℝ × ℝ =>
      (D.Γc τ (sig z.1) z.2, (sig z.1, D.Ac τ (sig z.1) z.2)))
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) := hΓ.prodMk (hsig.prodMk hA)
  have hmain : ContDiffOn ℝ 8 (fun z : ℝ × ℝ =>
      Work.RPV.levelPt (D.Γc τ (sig z.1) z.2) (sig z.1) (D.Ac τ (sig z.1) z.2))
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    chartJets_levelPt_contDiff.comp_contDiffOn hpair
  have h1 : ContDiffOn ℝ 1 (fun z : ℝ × ℝ =>
      Work.RPV.levelPt (D.Γc τ (sig z.1) z.2) (sig z.1) (D.Ac τ (sig z.1) z.2))
      (Set.univ ×ˢ Set.Ici (0 : ℝ)) := hmain.of_le (by norm_num)
  simpa only [collarPt] using h1

/-- The collar branch is `2π`-quasi-periodic in `t`. -/
theorem collarPt_quasi (D : LagData CI a) (τ x t : ℝ) :
    collarPt D.Γc D.Ac τ (sig x) (t + 2 * Real.pi)
      = Work.RPV.Tk 1 (collarPt D.Γc D.Ac τ (sig x) t) := by
  simp only [collarPt]
  rw [D.hΓper, D.hAper, ← levelPt_Tk]

/-- **Quasi-periodic transfer.**  A function of `(x,t)` which satisfies
`f (x, t + 2π) = Tk 1 (f (x,t))` and is `C¹` on the half-plane `t ≥ 0` is `C¹` everywhere:
shift the point up into the half-plane and undo the shift by `Tk (-k)`. -/
theorem contDiff_of_quasi_periodic_Tk (f : ℝ × ℝ → Work.RPV.PS)
    (hper : ∀ x t, f (x, t + 2 * Real.pi) = Work.RPV.Tk 1 (f (x, t)))
    (hsm : ContDiffOn ℝ 1 f (Set.univ ×ˢ Set.Ici (0 : ℝ))) :
    ContDiff ℝ 1 f := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 0 < z.2 + 2 * Real.pi * (k : ℝ) := by
    obtain ⟨k, hk⟩ := exists_nat_gt (-z.2 / (2 * Real.pi))
    refine ⟨k, ?_⟩
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have h := mul_lt_mul_of_pos_right hk hπ
    rw [div_mul_cancel₀ _ (ne_of_gt hπ)] at h
    linarith
  have hiter : ∀ (n : ℕ) (x t : ℝ),
      f (x, t + 2 * Real.pi * (n : ℝ)) = Work.RPV.Tk (n : ℤ) (f (x, t)) := by
    intro n
    induction n with
    | zero => intro x t; simp [Work.RPV.Tk]
    | succ m ih =>
      intro x t
      rw [Nat.cast_succ]
      rw [show t + 2 * Real.pi * ((m : ℝ) + 1)
            = (t + 2 * Real.pi * (m : ℝ)) + 2 * Real.pi by ring]
      rw [hper x (t + 2 * Real.pi * (m : ℝ)), ih x t]
      rw [show ((m + 1 : ℕ) : ℤ) = 1 + (m : ℤ) by push_cast; ring]
      rw [← Work.RPV.Tk_add]
  have heq : f = fun w : ℝ × ℝ =>
      Work.RPV.Tk (-(k : ℤ)) (f (w.1, w.2 + 2 * Real.pi * (k : ℝ))) := by
    funext w
    rw [hiter k w.1 w.2, Work.RPV.Tk_add, neg_add_cancel, Work.RPV.Tk_zero]
  rw [heq]
  have hfk : ContDiffAt ℝ 1 (fun w : ℝ × ℝ => f (w.1, w.2 + 2 * Real.pi * (k : ℝ))) z := by
    have hpt : (z.1, z.2 + 2 * Real.pi * (k : ℝ)) ∈ interior (Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
      rw [interior_prod_eq, interior_univ, interior_Ici]
      exact ⟨trivial, hk⟩
    have hfAt : ContDiffAt ℝ 1 f (z.1, z.2 + 2 * Real.pi * (k : ℝ)) :=
      hsm.contDiffAt (Filter.mem_of_superset (isOpen_interior.mem_nhds hpt) interior_subset)
    have hgAt : ContDiffAt ℝ 1 (fun w : ℝ × ℝ => (w.1, w.2 + 2 * Real.pi * (k : ℝ))) z := by
      fun_prop
    exact hfAt.comp z hgAt
  exact (contDiff_Tk (-(k : ℤ))).contDiffAt.comp z hfk

/-- The collar branch is globally `C¹`. -/
theorem contDiff_collarPt (D : LagData CI a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiff ℝ 1 (fun z : ℝ × ℝ => collarPt D.Γc D.Ac τ (sig z.1) z.2) :=
  contDiff_of_quasi_periodic_Tk _
    (fun x t => collarPt_quasi D τ x t) (contDiffOn_collarPt_half D hτ)

/-! ## The chart branches -/

/-- `derivWithin` over a right half-line of a differentiable function is the genuine derivative. -/
theorem derivWithin_Ici_eq_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    derivWithin f (Set.Ici x) x = deriv f x :=
  (hf.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ici x)

/-- `derivWithin` over a left half-line of a differentiable function is the genuine derivative. -/
theorem derivWithin_Iic_eq_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    derivWithin f (Set.Iic x) x = deriv f x :=
  (hf.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Iic x)

/-- The chart slice `x ↦ W τ t (rho τ x t)` is smooth at any `x₀` where `rho` takes a value
interior to the box `(-ρ₀, ρ₀)`. -/
theorem contDiffAt_chartSlice (D : LagData CI a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (t x₀ : ℝ) (hx₀ : D.rho τ x₀ t ∈ Set.Ioo (-D.ρ₀) D.ρ₀) :
    ContDiffAt ℝ 8 (fun x : ℝ => D.W τ t (D.rho τ x t)) x₀ := by
  have hρ : ContDiff ℝ 8 (fun x : ℝ => D.rho τ x t) :=
    D.hrhosm.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hΦ : ContDiffAt ℝ 8 (fun x : ℝ => ((τ, (t, D.rho τ x t)) : ℝ × (ℝ × ℝ))) x₀ :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk hρ.contDiffAt)
  have hs : (fun x : ℝ => D.rho τ x t) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀ ∈ 𝓝 x₀ :=
    hρ.continuous.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx₀)
  have hmem : ((τ, (t, D.rho τ x₀ t)) : ℝ × (ℝ × ℝ)) ∈
      Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀ :=
    ⟨hτ, trivial, hx₀⟩
  have hmap : Set.MapsTo (fun x : ℝ => ((τ, (t, D.rho τ x t)) : ℝ × (ℝ × ℝ)))
      ((fun x : ℝ => D.rho τ x t) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) :=
    fun x hx => ⟨hτ, trivial, hx⟩
  exact (ContDiffWithinAt.comp x₀ (D.hWsm.contDiffWithinAt hmem) hΦ.contDiffWithinAt
    hmap).contDiffAt hs

/-- The chart branch is `C¹` on `Icc (-√2) 0 × univ`. -/
theorem contDiffOn_chart (D : LagData CI a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ => D.W τ z.2 (D.rho τ z.1 z.2))
      (Set.Icc (-Real.sqrt 2) 0 ×ˢ Set.univ) := by
  have hrho : ContDiff ℝ 8 (fun z : ℝ × ℝ => D.rho τ z.1 z.2) :=
    D.hrhosm.comp (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd))
  have hφ : ContDiffOn ℝ 8 (fun z : ℝ × ℝ => (τ, (z.2, D.rho τ z.1 z.2)))
      (Set.Icc (-Real.sqrt 2) 0 ×ˢ Set.univ) :=
    (contDiff_const.prodMk (contDiff_snd.prodMk hrho)).contDiffOn
  have hmt : Set.MapsTo (fun z : ℝ × ℝ => (τ, (z.2, D.rho τ z.1 z.2)))
      (Set.Icc (-Real.sqrt 2) 0 ×ˢ Set.univ)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) := by
    intro z hz
    exact ⟨hτ, trivial, D.hrhorng τ hτ z.1 ⟨hz.1.1, hz.1.2⟩ z.2⟩
  have h := (D.hWsm.comp hφ hmt).of_le (m := 1) (n := 8) (by norm_num)
  simpa only [Function.comp_def] using h

/-- The reflected chart branch is `C¹` on `Icc 0 √2 × univ`. -/
theorem contDiffOn_chartRefl (D : LagData CI a) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 1 (fun z : ℝ × ℝ =>
      Work.RPV.tau Real.pi (D.W τ (z.2 - Real.pi) (D.rho τ (-z.1) (z.2 - Real.pi))))
      (Set.Icc 0 (Real.sqrt 2) ×ˢ Set.univ) := by
  have hrho : ContDiff ℝ 8 (fun z : ℝ × ℝ => D.rho τ (-z.1) (z.2 - Real.pi)) :=
    D.hrhosm.comp
      (contDiff_const.prodMk (contDiff_fst.neg.prodMk (contDiff_snd.sub contDiff_const)))
  have hφ : ContDiffOn ℝ 8
      (fun z : ℝ × ℝ => (τ, (z.2 - Real.pi, D.rho τ (-z.1) (z.2 - Real.pi))))
      (Set.Icc 0 (Real.sqrt 2) ×ˢ Set.univ) :=
    (contDiff_const.prodMk ((contDiff_snd.sub contDiff_const).prodMk hrho)).contDiffOn
  have hmt : Set.MapsTo
      (fun z : ℝ × ℝ => (τ, (z.2 - Real.pi, D.rho τ (-z.1) (z.2 - Real.pi))))
      (Set.Icc 0 (Real.sqrt 2) ×ˢ Set.univ)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) := by
    intro z hz
    exact ⟨hτ, trivial, D.hrhorng τ hτ (-z.1) ⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩
      (z.2 - Real.pi)⟩
  have hinner : ContDiffOn ℝ 1
      (fun z : ℝ × ℝ => D.W τ (z.2 - Real.pi) (D.rho τ (-z.1) (z.2 - Real.pi)))
      (Set.Icc 0 (Real.sqrt 2) ×ˢ Set.univ) := by
    have h := (D.hWsm.comp hφ hmt).of_le (m := 1) (n := 8) (by norm_num)
    simpa only [Function.comp_def] using h
  exact (contDiff_tau Real.pi).comp_contDiffOn hinner

/-! ## The pieces of `lagPt` -/

/-- The collar branch `collarPt τ (sig x) t`. -/
private def lagKb (D : LagData CI a) (τ : ℝ) (z : ℝ × ℝ) : Work.RPV.PS :=
  collarPt D.Γc D.Ac τ (sig z.1) z.2

/-- The chord-chart branch `W τ t (rho τ x t)`. -/
private def lagCb (D : LagData CI a) (τ : ℝ) (z : ℝ × ℝ) : Work.RPV.PS :=
  D.W τ z.2 (D.rho τ z.1 z.2)

/-- The reflected chord-chart branch `tau π (W τ (t-π) (rho τ (-x) (t-π)))`. -/
private def lagCbr (D : LagData CI a) (τ : ℝ) (z : ℝ × ℝ) : Work.RPV.PS :=
  Work.RPV.tau Real.pi (D.W τ (z.2 - Real.pi) (D.rho τ (-z.1) (z.2 - Real.pi)))

/-- The reflected collar branch `tau π (collarPt τ (sig (-x)) (t-π))`. -/
private def lagKbr (D : LagData CI a) (τ : ℝ) (z : ℝ × ℝ) : Work.RPV.PS :=
  Work.RPV.tau Real.pi (collarPt D.Γc D.Ac τ (sig (-z.1)) (z.2 - Real.pi))

/-- The `x ≤ 0` half of `lagPt` (`= basePt`), glued at `x = -√2`. -/
private def lagG (D : LagData CI a) (τ : ℝ) (z : ℝ × ℝ) : Work.RPV.PS :=
  if z.1 ≤ -Real.sqrt 2 then lagKb D τ z else lagCb D τ z

/-- The glued middle branch at `x = 0`. -/
private def lagH (D : LagData CI a) (τ : ℝ) (z : ℝ × ℝ) : Work.RPV.PS :=
  if z.1 ≤ 0 then lagCb D τ z else lagCbr D τ z

/-- `tau π` of the reflected `x ≤ 0` half. -/
private def lagRG (D : LagData CI a) (τ : ℝ) (z : ℝ × ℝ) : Work.RPV.PS :=
  Work.RPV.tau Real.pi (lagG D τ (-z.1, z.2 - Real.pi))

/-- The assembled family as a function of `(x,t)`. -/
private def lagPtF (D : LagData CI a) (τ : ℝ) : ℝ × ℝ → Work.RPV.PS :=
  fun z => lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2

theorem lagPt_contDiff_one (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContDiff ℝ 1 (fun z : ℝ × ℝ => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2) := by
  intro τ hτ
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hs2gt1 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hpi4 : (0 : ℝ) < Real.pi ^ 2 / 4 := by positivity
  -- ## smoothness of the four branches
  have hKsm : ContDiff ℝ 1 (lagKb D τ) := contDiff_collarPt D hτ
  have hCsm : ContDiffOn ℝ 1 (lagCb D τ) (Set.Icc (-Real.sqrt 2) 0 ×ˢ Set.univ) :=
    contDiffOn_chart D hτ
  have hCrsm : ContDiffOn ℝ 1 (lagCbr D τ) (Set.Icc 0 (Real.sqrt 2) ×ˢ Set.univ) :=
    contDiffOn_chartRefl D hτ
  have hKrsm : ContDiff ℝ 1 (lagKbr D τ) := by
    have h1 : ContDiff ℝ 1 (fun z : ℝ × ℝ => lagKb D τ (-z.1, z.2 - Real.pi)) :=
      hKsm.comp (by fun_prop)
    exact (contDiff_tau Real.pi).comp h1
  -- ## the two junctions
  have hvalA : ∀ p : ℝ, lagKb D τ (-Real.sqrt 2, p) = lagCb D τ (-Real.sqrt 2, p) :=
    fun p => (lagData_junction_negSqrt2 CI a ha D τ hτ p).1
  have hderA : ∀ p : ℝ,
      derivWithin (fun x : ℝ => lagKb D τ (x, p)) (Set.Iic (-Real.sqrt 2)) (-Real.sqrt 2)
        = derivWithin (fun x : ℝ => lagCb D τ (x, p)) (Set.Ici (-Real.sqrt 2)) (-Real.sqrt 2) := by
    intro p
    have h2 := (lagData_junction_negSqrt2 CI a ha D τ hτ p).2
    have hx0 : D.rho τ (-Real.sqrt 2) p ∈ Set.Ioo (-D.ρ₀) D.ρ₀ := by
      rw [D.hrhom τ hτ p]; exact ⟨by linarith [D.hρ₀, hpi4], D.hρ₀⟩
    have hdiff : DifferentiableAt ℝ (fun x : ℝ => lagCb D τ (x, p)) (-Real.sqrt 2) :=
      (contDiffAt_chartSlice D hτ p (-Real.sqrt 2) hx0).differentiableAt (by norm_num)
    rw [derivWithin_Ici_eq_deriv hdiff]
    exact h2
  have hvalB : ∀ p : ℝ, lagCb D τ (0, p) = lagCbr D τ (0, p) := by
    intro p
    simp only [lagCb, lagCbr, neg_zero]
    rw [D.hrho0 τ hτ p, D.hrho0 τ hτ (p - Real.pi)]
    have hr : (Real.pi / 2) ∈ Set.Ioc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], le_refl _⟩
    have hsq : (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 := by ring
    have h1 := D.hWchord τ hτ p (Real.pi / 2) hr
    have h2 := D.hWchord τ hτ (p - Real.pi) (Real.pi / 2) hr
    rw [hsq] at h1 h2
    rw [h1, h2]
    have hswap := (Work.RPB.B2.chordSurf_period_swap CI a ha).2 τ hτ (p - Real.pi) (Real.pi / 2)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [show p - Real.pi + Real.pi = p by ring,
      show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at hswap
    exact hswap
  have hderB : ∀ p : ℝ,
      derivWithin (fun x : ℝ => lagCb D τ (x, p)) (Set.Iic 0) 0
        = derivWithin (fun x : ℝ => lagCbr D τ (x, p)) (Set.Ici 0) 0 := by
    intro p
    have hde := (lagData_junction_zero CI a ha D τ hτ p).2
    rw [iteratedDeriv_one, iteratedDeriv_one] at hde
    have hx0 : D.rho τ 0 p ∈ Set.Ioo (-D.ρ₀) D.ρ₀ := by
      rw [D.hrho0 τ hτ p]; exact ⟨by linarith [D.hρ₀, hpi4], D.hπρ₀⟩
    have hx0' : D.rho τ 0 (p - Real.pi) ∈ Set.Ioo (-D.ρ₀) D.ρ₀ := by
      rw [D.hrho0 τ hτ (p - Real.pi)]; exact ⟨by linarith [D.hρ₀, hpi4], D.hπρ₀⟩
    have hF : DifferentiableAt ℝ (fun x : ℝ => lagCb D τ (x, p)) 0 :=
      (contDiffAt_chartSlice D hτ p 0 hx0).differentiableAt (by norm_num)
    have hG : DifferentiableAt ℝ (fun x : ℝ => lagCbr D τ (x, p)) 0 := by
      have h1 : ContDiffAt ℝ 8 (fun x : ℝ => D.W τ (p - Real.pi) (D.rho τ x (p - Real.pi))) 0 :=
        contDiffAt_chartSlice D hτ (p - Real.pi) 0 hx0'
      have h2 : ContDiffAt ℝ 8 (fun x : ℝ => -x) 0 := by fun_prop
      have h3 : ContDiffAt ℝ 8
          (fun x : ℝ => D.W τ (p - Real.pi) (D.rho τ (-x) (p - Real.pi))) 0 :=
        ContDiffAt.comp (f := fun x : ℝ => -x)
          (g := fun y : ℝ => D.W τ (p - Real.pi) (D.rho τ y (p - Real.pi))) 0
          (by simpa using h1) h2
      exact ((contDiff_tau Real.pi).contDiffAt.comp 0 (h3.of_le (by norm_num))).differentiableAt
        (by norm_num)
    rw [derivWithin_Iic_eq_deriv hF, derivWithin_Ici_eq_deriv hG]
    exact hde
  -- ## the glued functions
  have hGsm : ContDiffOn ℝ 1 (lagG D τ)
      (Set.Ioo (-Real.sqrt 2 - 1 / 8) (-Real.sqrt 2 + 1 / 8) ×ˢ Set.univ) := by
    have hu : ContDiffOn ℝ 1 (lagKb D τ)
        (Set.Ioc (-Real.sqrt 2 - 1 / 8) (-Real.sqrt 2) ×ˢ Set.univ) :=
      hKsm.contDiffOn.mono (fun z hz => trivial)
    have hv : ContDiffOn ℝ 1 (lagCb D τ)
        (Set.Icc (-Real.sqrt 2) (-Real.sqrt 2 + 1 / 8) ×ˢ Set.univ) :=
      hCsm.mono (fun z hz => ⟨⟨hz.1.1, by linarith [hz.1.2, hs2gt1]⟩, hz.2⟩)
    exact glueC1 (lagKb D τ) (lagCb D τ) (-Real.sqrt 2 - 1 / 8) (-Real.sqrt 2 + 1 / 8)
      (-Real.sqrt 2) (by norm_num) (by norm_num) hu hv hvalA hderA
  have hHsm : ContDiffOn ℝ 1 (lagH D τ) (Set.Ioo (-(1 : ℝ) / 8) (1 / 8) ×ˢ Set.univ) := by
    have hu : ContDiffOn ℝ 1 (lagCb D τ)
        (Set.Ioc (-(1 : ℝ) / 8) 0 ×ˢ Set.univ) :=
      hCsm.mono (fun z hz => ⟨⟨by linarith [hz.1.1, hs2gt1], hz.1.2⟩, hz.2⟩)
    have hv : ContDiffOn ℝ 1 (lagCbr D τ) (Set.Icc 0 (1 / 8) ×ˢ Set.univ) :=
      hCrsm.mono (fun z hz => ⟨⟨hz.1.1, by linarith [hz.1.2, hs2gt1]⟩, hz.2⟩)
    exact glueC1 (lagCb D τ) (lagCbr D τ) (-(1 : ℝ) / 8) (1 / 8) 0
      (by norm_num) (by norm_num) hu hv hvalB hderB
  have hRGsm : ContDiffOn ℝ 1 (lagRG D τ)
      (Set.Ioo (Real.sqrt 2 - 1 / 8) (Real.sqrt 2 + 1 / 8) ×ˢ Set.univ) := by
    have hcomp : ContDiffOn ℝ 1 (fun z : ℝ × ℝ => lagG D τ (-z.1, z.2 - Real.pi))
        (Set.Ioo (Real.sqrt 2 - 1 / 8) (Real.sqrt 2 + 1 / 8) ×ˢ Set.univ) :=
      hGsm.comp (by fun_prop)
        (fun z hz => ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, trivial⟩)
    exact (contDiff_tau Real.pi).comp_contDiffOn hcomp
  -- ## `lagPt` agrees with the pieces on the relevant regions
  have hlagKb : ∀ z : ℝ × ℝ, z.1 ≤ -Real.sqrt 2 →
      lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 = lagKb D τ z := by
    intro z hz
    simp only [lagPt, basePt, lagKb, collarPt]
    rw [if_pos hz, if_pos (le_trans hz (by linarith [hs2pos]))]
  have hlagCb : ∀ z : ℝ × ℝ, -Real.sqrt 2 < z.1 → z.1 ≤ 0 →
      lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 = lagCb D τ z := by
    intro z hz1 hz2
    simp only [lagPt, basePt, lagCb]
    rw [if_pos hz2, if_neg (not_le.mpr hz1)]
  have hlagCbr : ∀ z : ℝ × ℝ, 0 < z.1 → z.1 < Real.sqrt 2 →
      lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 = lagCbr D τ z := by
    intro z hz1 hz2
    simp only [lagPt, basePt, lagCbr]
    rw [if_neg (not_le.mpr hz1), if_neg (not_le.mpr (by linarith [hz2] : -Real.sqrt 2 < -z.1))]
  have hlagKbr : ∀ z : ℝ × ℝ, Real.sqrt 2 ≤ z.1 →
      lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 = lagKbr D τ z := by
    intro z hz
    have hz0 : ¬ (z.1 ≤ 0) := by linarith [hz, hs2pos]
    simp only [lagPt, basePt, lagKbr, lagKb, collarPt]
    rw [if_neg hz0, if_pos (by linarith [hz] : -z.1 ≤ -Real.sqrt 2)]
  have hlagG : ∀ z : ℝ × ℝ, z.1 ≤ 0 →
      lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 = lagG D τ z := by
    intro z hz
    simp only [lagPt, basePt, lagG, lagKb, lagCb, collarPt]
    rw [if_pos hz]
  have hlagH : ∀ z : ℝ × ℝ, z.1 ∈ Set.Ioo (-(1 : ℝ) / 8) (1 / 8) →
      lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 = lagH D τ z := by
    intro z hz
    by_cases h : z.1 ≤ 0
    · simp only [lagH, lagPt, basePt, lagCb]
      rw [if_pos h, if_pos h, if_neg (by linarith [hz.1, hs2gt1] : ¬ (z.1 ≤ -Real.sqrt 2))]
    · simp only [lagH, lagPt, basePt, lagCbr]
      rw [if_neg h, if_neg h,
        if_neg (by linarith [hz.2, hs2gt1] : ¬ (-z.1 ≤ -Real.sqrt 2))]
  have hlagRG : ∀ z : ℝ × ℝ, z.1 ∈ Set.Ioo (Real.sqrt 2 - 1 / 8) (Real.sqrt 2 + 1 / 8) →
      lagPt D.W D.Γc D.Ac D.rho τ z.1 z.2 = lagRG D τ z := by
    intro z hz
    have hz0 : ¬ (z.1 ≤ 0) := by linarith [hz.1, hs2gt1]
    simp only [lagRG, lagPt, basePt, lagG, lagKb, lagCb, collarPt]
    rw [if_neg hz0]
  -- ## `lagPt` is `C¹` on an open cover
  have hS1 : ContDiffOn ℝ 1 (lagPtF D τ) (Set.Iio (-Real.sqrt 2) ×ˢ Set.univ) :=
    (hKsm.contDiffOn.mono (fun z hz => trivial)).congr
      (fun z hz => by simp only [lagPtF]; exact hlagKb z (le_of_lt hz.1))
  have hS2 : ContDiffOn ℝ 1 (lagPtF D τ)
      (Set.Ioo (-Real.sqrt 2 - 1 / 8) (-Real.sqrt 2 + 1 / 8) ×ˢ Set.univ) :=
    hGsm.congr (fun z hz => by
      simp only [lagPtF]; exact hlagG z (by linarith [hz.1.2, hs2gt1]))
  have hS3 : ContDiffOn ℝ 1 (lagPtF D τ)
      (Set.Ioo (-Real.sqrt 2 + 1 / 16) 0 ×ˢ Set.univ) :=
    (hCsm.mono (fun z hz => ⟨⟨by linarith [hz.1.1], le_of_lt hz.1.2⟩, hz.2⟩)).congr
      (fun z hz => by simp only [lagPtF]; exact hlagCb z (by linarith [hz.1.1]) (le_of_lt hz.1.2))
  have hS4 : ContDiffOn ℝ 1 (lagPtF D τ) (Set.Ioo (-(1 : ℝ) / 8) (1 / 8) ×ˢ Set.univ) :=
    hHsm.congr (fun z hz => by simp only [lagPtF]; exact hlagH z hz.1)
  have hS5 : ContDiffOn ℝ 1 (lagPtF D τ)
      (Set.Ioo (1 / 16) (Real.sqrt 2 - 1 / 16) ×ˢ Set.univ) :=
    (hCrsm.mono (fun z hz => ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩)).congr
      (fun z hz => by simp only [lagPtF]; exact hlagCbr z (by linarith [hz.1.1]) (by linarith [hz.1.2]))
  have hS6 : ContDiffOn ℝ 1 (lagPtF D τ)
      (Set.Ioo (Real.sqrt 2 - 1 / 8) (Real.sqrt 2 + 1 / 8) ×ˢ Set.univ) :=
    hRGsm.congr (fun z hz => by simp only [lagPtF]; exact hlagRG z hz.1)
  have hS7 : ContDiffOn ℝ 1 (lagPtF D τ) (Set.Ioi (Real.sqrt 2) ×ˢ Set.univ) :=
    (hKrsm.contDiffOn.mono (fun z hz => trivial)).congr
      (fun z hz => by simp only [lagPtF]; exact hlagKbr z (le_of_lt hz.1))
  -- ## assembly
  have hmem_ioo : ∀ {a b : ℝ} {z : ℝ × ℝ}, z.1 ∈ Set.Ioo a b →
      (Set.Ioo a b ×ˢ Set.univ) ∈ 𝓝 z :=
    fun hz => (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hz, trivial⟩
  have hmem_iio : ∀ {a : ℝ} {z : ℝ × ℝ}, z.1 < a → (Set.Iio a ×ˢ Set.univ) ∈ 𝓝 z :=
    fun hz => (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hz, trivial⟩
  have hmem_ioi : ∀ {a : ℝ} {z : ℝ × ℝ}, a < z.1 → (Set.Ioi a ×ˢ Set.univ) ∈ 𝓝 z :=
    fun hz => (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hz, trivial⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  rcases lt_trichotomy z.1 (-Real.sqrt 2) with h | h | h
  · exact hS1.contDiffAt (hmem_iio h)
  · exact hS2.contDiffAt (hmem_ioo ⟨by rw [h]; linarith, by rw [h]; linarith⟩)
  · rcases lt_trichotomy z.1 0 with h2 | h2 | h2
    · by_cases h3 : z.1 ≤ -Real.sqrt 2 + 1 / 16
      · exact hS2.contDiffAt (hmem_ioo ⟨by linarith, by linarith⟩)
      · exact hS3.contDiffAt (hmem_ioo ⟨not_le.mp h3, h2⟩)
    · exact hS4.contDiffAt (hmem_ioo ⟨by rw [h2]; linarith, by rw [h2]; linarith⟩)
    · by_cases h3 : z.1 ≤ 1 / 16
      · exact hS4.contDiffAt (hmem_ioo ⟨by linarith, by linarith⟩)
      · by_cases h4 : z.1 < Real.sqrt 2 - 1 / 16
        · exact hS5.contDiffAt (hmem_ioo ⟨not_le.mp h3, h4⟩)
        · by_cases h5 : z.1 < Real.sqrt 2 + 1 / 8
          · exact hS6.contDiffAt (hmem_ioo ⟨by linarith [not_lt.mp h4], h5⟩)
          · exact hS7.contDiffAt (hmem_ioi (by linarith [not_lt.mp h5]))

end

end Work.RPB.B5
