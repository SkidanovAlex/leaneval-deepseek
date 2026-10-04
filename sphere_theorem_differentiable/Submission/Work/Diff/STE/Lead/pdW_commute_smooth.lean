import Mathlib
import Submission.Work.Diff.STE.Lead.Defs
import Submission.Work.Diff.STE.Lead.CompJetDefs
import Submission.Work.Diff.STE.Lead.hasFDerivAt_integral_fderiv
import Submission.Work.Diff.STE.Lead.hasDerivWithinAt_integral_Ico
import Submission.Work.Diff.STE.Lead.V_sub_eq_integral_entry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `t`-`y` commutation for the flat parabolic problem (`pdW_commute_smooth`)

With `G (t,y) = Φ (y, jetM (V t) y)`, this says that the time derivative of the word derivative
`t ↦ ∂_w (V t)_{ab}(y)` is `∂_w G_{ab}(t,y)`, one-sided on `Ico 0 τ`.

## Route

The proof uses the integral form of the equation and differentiates under the integral sign.

* `Work.Diff.STE.Lead.V_sub_eq_integral_entry` (delegated): the fundamental theorem of calculus for
  the equation, `V s y a b - V t y a b = ∫_{t}^{s} Φ (y, jetM (V σ) y) a b dσ`.
* `Work.Diff.STE.Lead.hasFDerivAt_integral_fderiv` (delegated): the Leibniz rule for the interval
  integral, `fderiv (fun y' ↦ ∫_{t}^{s} H σ y') y = ∫_{t}^{s} fderiv (H σ) y`, under the hypothesis
  that the slices `H σ` are smooth on the open set `Ω` and that their `fderiv` is jointly
  continuous.
* `Work.Diff.STE.Lead.hasDerivWithinAt_integral_Ico` (delegated): the one-sided fundamental theorem
  of calculus `HasDerivWithinAt (fun s ↦ ∫_{0}^{s} K) (K t) (Ico 0 τ) t` for `K` continuous on
  `Ico 0 τ`.

The induction on the length of the word is `key` below: for every base point `t₀ ∈ Ico 0 τ`, every
`s ∈ Ico 0 τ` and every `y ∈ Ω`,
`∂_w (V s)_{ab}(y) = ∂_w (V t₀)_{ab}(y) + ∫_{t₀}^{s} ∂_w (G σ)_{ab}(y) dσ`.
The induction step differentiates the induction hypothesis in `y` under the integral sign (the
`fderiv` of the integrand is one word derivative higher, jointly continuous by the tower hypothesis
`hG`), and the final statement follows from `key` with `t₀ = 0` and the one-sided theorem of
calculus.

The helper lemmas are prefixed `pdwc_` (and `pdwc_frameLinC` is the continuous-linear-map version of
`frameLin`) to avoid clashes with the delegated files.
-/

open scoped ContDiff BigOperators Interval Topology
open Set Filter MeasureTheory

namespace Work.Diff.STE.Lead

variable {n : ℕ}

/-- The tower index of the word `w` and the entry `(a,b)`. -/
def pdwc_idxOf (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) : Idx n j :=
  ((a, b), ⟨⟨j, Nat.lt_succ_self j⟩, w⟩)

@[simp] lemma pdwc_compTower_idxOf (u : Modl n → Mtrx n) (j : ℕ) (w : Fin j → Fin n)
    (a b : Fin n) (y : Modl n) :
    compTower u j y (pdwc_idxOf j w a b) = pdW (fun y' => u y' a b) j w y := rfl

/-- Continuity of the word derivatives of the right hand side, from the tower hypothesis `hG`. -/
theorem pdwc_continuousOn_tower {τ : ℝ} {Ω : Set (Modl n)}
    {Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n} {V : ℝ → Modl n → Mtrx n}
    (hG : ∀ m : ℕ, ContinuousOn (fun p : ℝ × Modl n =>
        compTower (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V p.1) y')) m p.2)
        (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) :
    ContinuousOn (fun p : ℝ × Modl n =>
        pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V p.1) y') a b) j w p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Ω) := by
  have h := (continuous_apply (pdwc_idxOf j w a b)).continuousOn.comp (hG j)
    (fun p _ => Set.mem_univ _)
  exact h

/-- Joint continuity of the right hand side, from the level `0` tower hypothesis. -/
theorem pdwc_continuousOn_Gslice {τ : ℝ} {Ω : Set (Modl n)}
    {Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n} {V : ℝ → Modl n → Mtrx n}
    (hG : ∀ m : ℕ, ContinuousOn (fun p : ℝ × Modl n =>
        compTower (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V p.1) y')) m p.2)
        (Set.Ico (0 : ℝ) τ ×ˢ Ω)) :
    ContinuousOn (fun p : ℝ × Modl n => Φ (p.2, Work.Diff.STE.Flat.jetM (V p.1) p.2))
      (Set.Ico (0 : ℝ) τ ×ˢ Ω) := by
  rw [continuousOn_pi]
  intro a
  rw [continuousOn_pi]
  intro b
  have h := pdwc_continuousOn_tower (n := n) (τ := τ) (Ω := Ω) hG 0 (fun _ : Fin 0 => a) a b
  convert h using 1
  · funext p
    simp [pdW_zero]

/-! ## The linear map `frameLin` is continuous in its argument -/

/-- `frameLin`, as a continuous linear map in its argument. -/
noncomputable def pdwc_frameLinC : (Fin n → ℂ) →L[ℝ] (Modl n →L[ℝ] ℂ) :=
  ∑ c : Fin n, (ContinuousLinearMap.smulRightL ℝ (Modl n) ℂ
      (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℝ) c)).comp
    (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℂ) c)

lemma pdwc_frameLinC_apply (J : Fin n → ℂ) : pdwc_frameLinC (n := n) J = frameLin J := by
  rw [frameLin]
  simp [pdwc_frameLinC, ContinuousLinearMap.smulRightL_apply_apply]

/-- Joint continuity of the derivative (in operator norm) of a word derivative of the right hand
side, from the tower hypothesis. -/
theorem pdwc_continuousOn_fderiv {τ : ℝ} {Ω : Set (Modl n)}
    {Φ : Modl n × Work.Diff.STE.Flat.Jet n → Mtrx n} {V : ℝ → Modl n → Mtrx n}
    (hG : ∀ m : ℕ, ContinuousOn (fun p : ℝ × Modl n =>
        compTower (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V p.1) y')) m p.2)
        (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) :
    ContinuousOn (fun p : ℝ × Modl n => fderiv ℝ (fun y' : Modl n =>
        pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V p.1) y'') a b) j w y') p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Ω) := by
  have htuple : ContinuousOn (fun p : ℝ × Modl n => fun c : Fin n =>
      pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V p.1) y'') a b) (j+1)
        (Fin.cons c w) p.2) (Set.Ico (0 : ℝ) τ ×ˢ Ω) := by
    rw [continuousOn_pi]
    intro c
    exact pdwc_continuousOn_tower hG (j+1) (Fin.cons c w) a b
  have hcomp := (pdwc_frameLinC (n := n)).continuous.continuousOn.comp htuple
    (fun p _ => Set.mem_univ _)
  refine hcomp.congr fun p hp => ?_
  simp only [Function.comp_apply]
  rw [pdwc_frameLinC_apply, fderiv_pdW_eq]


/-! ## Auxiliary facts -/

/-- A word derivative of the `(a,b)` entry of a smooth matrix valued function is smooth. -/
lemma pdwc_contDiffOn_entry {Ω : Set (Modl n)} (hΩ : IsOpen Ω) {u : Modl n → Mtrx n}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω) (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pdW (fun y' => u y' a b) j w) Ω :=
  contDiffOn_pdW hΩ ((contDiffOn_pi.mp ((contDiffOn_pi.mp hu) a)) b) j w

/-- The unordered interval `uIcc t₀ s` of two points of `Ico 0 τ` lies in `Ico 0 τ`. -/
lemma pdwc_uIcc_subset_Ico {a b τ : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) τ) (hb : b ∈ Set.Ico (0 : ℝ) τ) :
    Set.uIcc a b ⊆ Set.Ico (0 : ℝ) τ := by
  intro x hx
  have hx' : x ∈ Set.Icc (min a b) (max a b) := by
    simpa [Set.uIcc] using hx
  exact ⟨le_trans (le_min ha.1 hb.1) hx'.1, lt_of_le_of_lt hx'.2 (max_lt ha.2 hb.2)⟩

theorem pdW_commute_smooth {n : ℕ} {τ : ℝ} (hτ : 0 < τ) {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (V : ℝ → (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n)
    (hslice : ∀ t ∈ Set.Ico (0 : ℝ) τ, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => V t y) Ω)
    (hGs : ∀ t ∈ Set.Ico (0 : ℝ) τ,
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y => Φ (y, Work.Diff.STE.Flat.jetM (V t) y)) Ω)
    (heq : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ y ∈ Ω,
        HasDerivWithinAt (fun s : ℝ => V s y) (Φ (y, Work.Diff.STE.Flat.jetM (V t) y))
          (Set.Ico (0 : ℝ) τ) t)
    (hG : ∀ m : ℕ, ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
        Work.Diff.STE.Lead.compTower (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V p.1) y')) m p.2)
        (Set.Ico (0 : ℝ) τ ×ˢ Ω))
    (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) τ)
    (y : Fin n → ℝ) (hy : y ∈ Ω) :
    HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.Lead.pdW (fun y' => V s y' a b) j w y)
      (Work.Diff.STE.Lead.pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V t) y') a b) j w y)
      (Set.Ico (0 : ℝ) τ) t := by
  classical
  have _hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hΦ
  have key : ∀ (j : ℕ) (w : Fin j → Fin n) (a b : Fin n) (t₀ s : ℝ),
      t₀ ∈ Set.Ico (0 : ℝ) τ → s ∈ Set.Ico (0 : ℝ) τ → ∀ y ∈ Ω,
      pdW (fun y' => V s y' a b) j w y
        = pdW (fun y' => V t₀ y' a b) j w y
          + ∫ σ in t₀..s, pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V σ) y') a b) j w y := by
    intro j
    induction j with
    | zero =>
      intro w a b t₀ s ht₀ hs y hy
      have h := V_sub_eq_integral_entry Φ V heq (pdwc_continuousOn_Gslice hG) a b hs ht₀ hy
      simp only [pdW_zero]
      rw [← h]; ring
    | succ j ih =>
      intro w a b t₀ s ht₀ hs y hy
      simp only [pdW_succ]
      set Afun : Modl n → ℂ := pdW (fun y'' => V t₀ y'' a b) j (Fin.tail w) with hAfun
      set Bfun : Modl n → ℂ := fun y' => ∫ σ in t₀..s,
        pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V σ) y'') a b) j (Fin.tail w) y'
        with hBfun
      have hsm : ∀ σ ∈ Set.Ico (0 : ℝ) τ, ContDiffOn ℝ (⊤ : ℕ∞)
          (fun y' : Modl n => pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V σ) y'') a b)
            j (Fin.tail w) y') Ω :=
        fun σ hσ => pdwc_contDiffOn_entry hΩ (hGs σ hσ) j (Fin.tail w) a b
      have hc : ContinuousOn (fun p : ℝ × Modl n =>
          pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V p.1) y'') a b) j (Fin.tail w) p.2)
          (Set.Ico (0 : ℝ) τ ×ˢ Ω) :=
        pdwc_continuousOn_tower hG j (Fin.tail w) a b
      have hd : ContinuousOn (fun p : ℝ × Modl n => fderiv ℝ (fun y' : Modl n =>
          pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V p.1) y'') a b) j (Fin.tail w) y') p.2)
          (Set.Ico (0 : ℝ) τ ×ˢ Ω) :=
        pdwc_continuousOn_fderiv hG j (Fin.tail w) a b
      have hB : HasFDerivAt Bfun (∫ σ in t₀..s, fderiv ℝ (fun y' : Modl n =>
          pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V σ) y'') a b) j (Fin.tail w) y') y) y :=
        hasFDerivAt_integral_fderiv hΩ
          (fun σ (y' : Modl n) => pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V σ) y'') a b)
            j (Fin.tail w) y') hsm hc hd ht₀ hs hy
      have hdiffA : DifferentiableAt ℝ Afun y := by
        have hAA : ContDiffOn ℝ (⊤ : ℕ∞) Afun Ω :=
          pdwc_contDiffOn_entry hΩ (hslice t₀ ht₀) j (Fin.tail w) a b
        exact (hAA.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
      have hev : (pdW (fun y'' => V s y'' a b) j (Fin.tail w)) =ᶠ[𝓝 y] (Afun + Bfun) := by
        filter_upwards [hΩ.mem_nhds hy] with y' hy'
        exact ih (Fin.tail w) a b t₀ s ht₀ hs y' hy'
      rw [Filter.EventuallyEq.fderiv_eq hev]
      rw [fderiv_add hdiffA hB.differentiableAt, add_apply, hB.fderiv]
      have hInt : IntervalIntegrable (fun σ : ℝ => fderiv ℝ (fun y' : Modl n =>
          pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V σ) y'') a b) j (Fin.tail w) y') y)
          volume t₀ s := by
        have hcont : ContinuousOn (fun σ : ℝ => fderiv ℝ (fun y' : Modl n =>
            pdW (fun y'' => Φ (y'', Work.Diff.STE.Flat.jetM (V σ) y'') a b) j (Fin.tail w) y') y)
            (Set.uIcc t₀ s) :=
          hd.comp (continuousOn_id.prodMk continuousOn_const)
            (fun σ hσ => ⟨pdwc_uIcc_subset_Ico ht₀ hs hσ, hy⟩)
        exact hcont.intervalIntegrable
      rw [ContinuousLinearMap.intervalIntegral_apply hInt]
  have hK : ContinuousOn (fun σ : ℝ =>
      pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V σ) y') a b) j w y)
      (Set.Ico (0 : ℝ) τ) :=
    (pdwc_continuousOn_tower hG j w a b).comp (continuousOn_id.prodMk continuousOn_const)
      (fun p hp => ⟨hp, hy⟩)
  have hEqOn : Set.EqOn (fun s : ℝ => pdW (fun y' => V s y' a b) j w y)
      (fun s : ℝ => pdW (fun y' => V 0 y' a b) j w y
        + ∫ σ in (0 : ℝ)..s, pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V σ) y') a b) j w y)
      (Set.Ico (0 : ℝ) τ) :=
    fun s hs => key j w a b 0 s ⟨le_refl 0, hτ⟩ hs y hy
  have hder : HasDerivWithinAt (fun s : ℝ => pdW (fun y' => V 0 y' a b) j w y
      + ∫ σ in (0 : ℝ)..s, pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V σ) y') a b) j w y)
      (pdW (fun y' => Φ (y', Work.Diff.STE.Flat.jetM (V t) y') a b) j w y)
      (Set.Ico (0 : ℝ) τ) t :=
    (hasDerivWithinAt_integral_Ico hτ hK ht).const_add (pdW (fun y' => V 0 y' a b) j w y)
  exact hder.congr hEqOn (hEqOn ht)



end Work.Diff.STE.Lead
