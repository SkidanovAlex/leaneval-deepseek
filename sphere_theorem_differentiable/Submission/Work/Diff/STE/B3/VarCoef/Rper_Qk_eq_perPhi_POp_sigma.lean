import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.ChartCE
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs
import Submission.Work.Diff.STE.B3.VarCoef.Rper_Qk_eq_perPhi_POp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The periodised chart expansion of `R_l (Q_k h)`, with the cut-off `η` only `σ`-normalised

`VarCoef.Rper_Qk_eq_perPhi_POp` proves the periodised chart expansion of `R_l (Q_k h)` under the
hypothesis that the cut-off `η` equals `1` on the ball of radius `1/4`.  That ball is much larger
than the ball on which the localised weight `ψ l` is actually supported: the *only* property of
`η` used in the argument is that `η = 1` at the points where `perMat` must be replaced by the chart
matrix, and those points lie in the ball of radius `σ l` (`2 σ l ≤ 1/4`, and `ψ l` is supported in
the open `σ l`-ball).

The present file repeats the argument with the honest `σ`-ball hypothesis

  `hη1 : ∀ z, ‖z‖ ≤ D.σ l → η z = 1`

(the one that the assembly actually has: the cut-off is built to be `1` on the `σ`-ball and
supported in the open unit cube).  Two ingredients change with respect to
`Rper_Qk_eq_perPhi_POp`:

* `perMat_eq_of_mem_sigma_ball`: on the `σ l`-ball the periodisation of the cut-off chart matrix is
  the chart matrix — the cube membership needed for the lattice argument follows from
  `2 σ l ≤ 1/4`;
* `perMat_eventuallyEq_sigma`: consequently `perMat` agrees with a translate of the chart matrix
  near any point whose translate lies in the support of `ψ l`.

With these, the proof of `Rper_Qk_eq_perPhi_POp` (pointwise splitting on whether some lattice
translate of `z` lies in the support of `ψ l`) goes through verbatim; it is reproduced below as
`Rper_Qk_eq_perPhi_POp_sigma_gen` with the parameters `A, B, ci, co` kept general, and the requested
statement is the specialisation to the bundle `ce : ChartCE D k l`.
-/

noncomputable section

namespace Work.Diff.STE.B3.VarCoef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The `σ`-ball variants of the two periodisation lemmas -/

/-- On the ball `‖z‖ ≤ σ l` the periodised cut-off chart matrix is the chart matrix itself, when
`η = 1` on that ball (and `η` is supported in the open centred cube).

This is `Work.Diff.STE.B3.perMat_eq_of_mem_ball` with the `1/4`-ball replaced by the `σ l`-ball; the
cube membership used by the lattice argument follows from `2 σ l ≤ 1/4`. -/
lemma perMat_eq_of_mem_sigma_ball (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (l : ι₀)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ D.σ l) :
    Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b z
      = ((D.mat l h a b z : ℝ) : ℂ) := by
  have hquarter : ‖z‖ ≤ 1 / 4 := by
    have h2 : 2 * D.σ l ≤ 1 / 4 := D.hσ2 l
    linarith
  have hzc : ∀ j : Fin (Module.finrank ℝ E), |z j| ≤ 1 / 4 := fun j =>
    le_trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z j) hquarter
  have hcube : ∀ j, z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := fun j =>
    abs_lt.mp (lt_of_le_of_lt (hzc j) (by norm_num))
  rw [Work.Diff.STE.B3.perMat]
  rw [tsum_eq_single (0 : Fin (Module.finrank ℝ E) → ℤ)]
  · have h0 : z + Work.Diff.STE.iVec (0 : Fin (Module.finrank ℝ E) → ℤ) = z := by
      funext j
      simp [Work.Diff.STE.iVec]
    rw [h0, hη1 z hz]
    simp
  · intro m hm
    have hzero : η (z + Work.Diff.STE.iVec m) = 0 := by
      by_contra hne
      have hmem := hηt (subset_closure (Function.mem_support.mpr hne))
      rw [Set.mem_pi] at hmem
      exact hm (Work.Diff.STE.B3.lattice_add_eq_zero_of_mem_cube hcube
        (fun j => hmem j (Set.mem_univ j)))
    simp [hzero]

/-- Near a point `z` whose translate `z + m` lies in the support of `ψ l`, the periodised cut-off
chart matrix agrees with the chart matrix at the translate, assuming `η = 1` only on the `σ l`-ball.

This is `Work.Diff.STE.B3.VarCoef.perMat_eventuallyEq` with the `σ`-ball hypothesis. -/
lemma perMat_eventuallyEq_sigma (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (l : ι₀)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    {m : Fin (Module.finrank ℝ E) → ℤ} (hm : D.psi l (z + Work.Diff.STE.iVec m) ≠ 0) :
    ∀ᶠ w in nhds z, Work.Diff.STE.B3.perMat D η l h a b w
      = ((D.mat l h a b (w + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
  have hlt : ‖z + Work.Diff.STE.iVec m‖ < D.σ l :=
    Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero D hm
  have hgerm : ∀ᶠ u in nhds (z + Work.Diff.STE.iVec m),
      Work.Diff.STE.B3.perMat D η l h a b u = ((D.mat l h a b u : ℝ) : ℂ) :=
    Filter.eventually_of_mem
      ((Metric.isOpen_ball (x := (0 : Fin (Module.finrank ℝ E) → ℝ))
          (ε := D.σ l)).mem_nhds
        (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hlt))
      (fun u hu => perMat_eq_of_mem_sigma_ball D η l hη1 hηt h a b
        (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hu)))
  have hpull : ∀ᶠ w in nhds z, Work.Diff.STE.B3.perMat D η l h a b (w + Work.Diff.STE.iVec m)
      = ((D.mat l h a b (w + Work.Diff.STE.iVec m) : ℝ) : ℂ) :=
    Filter.Tendsto.eventually ((continuous_add_const (Work.Diff.STE.iVec m)).tendsto z) hgerm
  filter_upwards [hpull] with w hw
  rw [← hw]
  exact (Work.Diff.STE.B3.Periodic1_iVec (perMat_periodic D η l h a b) m w).symm

/-! ## 2. The general `σ`-ball version of the periodised chart expansion -/

/-- The general form of `VarCoef.Rper_Qk_eq_perPhi_POp` with the `σ`-ball hypothesis on `η`: for
arbitrary coefficients `A, B, ci, co` satisfying the chart expression `hCE`, the periodised
component of `Q_k h` is the periodised weight times the variable-coefficient operator applied to
the periodised chart matrix. -/
theorem Rper_Qk_eq_perPhi_POp_sigma_gen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (A : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (B : ι₀ → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (ci co : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hA : ∀ i a b, ContDiff ℝ (⊤ : ℕ∞) (A i a b))
    (hAp : ∀ i a b, Work.Diff.STE.Periodic1 (A i a b))
    (hB : ∀ i a, ContDiff ℝ (⊤ : ℕ∞) (B i a))
    (hBp : ∀ i a, Work.Diff.STE.Periodic1 (B i a))
    (hci : ∀ i c d c' d', ContDiff ℝ (⊤ : ℕ∞) (ci i c d c' d'))
    (hcip : ∀ i c d c' d', Work.Diff.STE.Periodic1 (ci i c d c' d'))
    (hco : ∀ i a b c d, ContDiff ℝ (⊤ : ℕ∞) (co i a b c d))
    (hcop : ∀ i a b c d, Work.Diff.STE.Periodic1 (co i a b c d))
    (hCE : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)),
      (∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) →
      ∀ z : Fin (Module.finrank ℝ E) → ℝ,
        ((D.R l (Work.Diff.STE.B3.Qk D k h) a b z : ℝ) : ℂ) =
          ((D.psi l z * Real.sqrt (D.dens l z) : ℝ) : ℂ) *
            (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ((co i a b c d z : ℝ) : ℂ) *
                Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
                  (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                    ((ci i c d c' d' w : ℝ) : ℂ) *
                      ((D.mat l h c' d' w : ℝ) : ℂ)) z))
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (hh : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) :
    D.Rper l (Work.Diff.STE.B3.Qk D k h) a b
      = fun z => Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z *
          (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((co i a b c d z : ℝ) : ℂ) *
              Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
                (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                  ((ci i c d c' d' w : ℝ) : ℂ) *
                    Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z) := by
  funext z
  by_cases hS : ∃ m : Fin (Module.finrank ℝ E) → ℤ,
      D.psi l (z + Work.Diff.STE.iVec m) ≠ 0
  · -- there is a unique translate `m₀` with `ψ l (z + m₀) ≠ 0`: everything is computed there
    obtain ⟨m₀, hm₀⟩ := hS
    have hL : D.Rper l (Work.Diff.STE.B3.Qk D k h) a b z
        = ((D.R l (Work.Diff.STE.B3.Qk D k h) a b
            (z + Work.Diff.STE.iVec m₀) : ℝ) : ℂ) :=
      Rper_eq_of_psi_ne D (Work.Diff.STE.B3.Qk D k h) l a b hm₀
    have hPhi : Work.Diff.STE.B3.perPhi D l z
        = ((D.psi l (z + Work.Diff.STE.iVec m₀)
            * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m₀)) : ℝ) : ℂ) :=
      perPhi_eq_of_psi_ne D l hm₀
    -- the operator applied to the periodised data at `z` is the operator applied to the chart
    -- matrix at `z + m₀`
    have hG : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ((co i a b c d z : ℝ) : ℂ) *
            Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
              (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z)
        = (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          ((co i a b c d (z + Work.Diff.STE.iVec m₀) : ℝ) : ℂ) *
            Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
              (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  ((D.mat l h c' d' w : ℝ) : ℂ))
              (z + Work.Diff.STE.iVec m₀)) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ =>
        Finset.sum_congr rfl (fun d _ => ?_)))
      have hco' : ((co i a b c d (z + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)
          = ((co i a b c d z : ℝ) : ℂ) := by
        rw [Work.Diff.STE.B3.Periodic1_iVec (hcop i a b c d) m₀ z]
      have hV : Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
            (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' w : ℝ) : ℂ) *
                Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z
          = Work.Diff.STE.B3.VarCoef.varLapPow k (A i) (B i)
            (fun w => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' w : ℝ) : ℂ) * ((D.mat l h c' d' w : ℝ) : ℂ))
            (z + Work.Diff.STE.iVec m₀) := by
        -- locality: `perMat` agrees with the translate of `mat` near `z`
        have hinner : ∀ c' d' : Fin (Module.finrank ℝ E),
            (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ((ci i c d c' d' w : ℝ) : ℂ) *
                Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w)
            =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ((ci i c d c' d' w : ℝ) : ℂ) *
                ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)) := by
          intro c' d'
          filter_upwards [perMat_eventuallyEq_sigma D η l hη1 hηt h c' d' hm₀] with w hw
          rw [hw]
        have hgerm : (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w)
            =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)) := by
          filter_upwards [Filter.eventually_all.mpr (fun c' =>
            Filter.eventually_all.mpr (fun d' => hinner c' d'))] with w hw
          refine Finset.sum_congr rfl (fun c' _ => Finset.sum_congr rfl (fun d' _ => ?_))
          exact hw c' d'
        rw [(varLapPow_eventuallyEq (A := A i) (B := B i) hgerm k).eq_of_nhds]
        -- translation: the coefficients are `1`-periodic
        have hAper : ∀ a' b' (w : Fin (Module.finrank ℝ E) → ℝ),
            A i a' b' (w + Work.Diff.STE.iVec m₀) = A i a' b' w :=
          fun a' b' w => Work.Diff.STE.B3.Periodic1_iVec (hAp i a' b') m₀ w
        have hBper : ∀ a' (w : Fin (Module.finrank ℝ E) → ℝ),
            B i a' (w + Work.Diff.STE.iVec m₀) = B i a' w :=
          fun a' w => Work.Diff.STE.B3.Periodic1_iVec (hBp i a') m₀ w
        have hshift : (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' w : ℝ) : ℂ) *
                  ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ))
            = (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
                ((ci i c d c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ) *
                  ((D.mat l h c' d' (w + Work.Diff.STE.iVec m₀) : ℝ) : ℂ)) := by
          funext w
          refine Finset.sum_congr rfl (fun c' _ => Finset.sum_congr rfl (fun d' _ => ?_))
          rw [Work.Diff.STE.B3.Periodic1_iVec (hcip i c d c' d') m₀ w]
        rw [hshift, iterate_varLap_comp_add hAper hBper k
          (fun u => ∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
              ((ci i c d c' d' u : ℝ) : ℂ) * ((D.mat l h c' d' u : ℝ) : ℂ))]
      rw [← hco', hV]
    rw [hL, hPhi, hG]
    exact hCE h a b hh (z + Work.Diff.STE.iVec m₀)
  · -- no translate of `z` lies in the support of `ψ l`: both sides vanish
    have hS' : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
        D.psi l (z + Work.Diff.STE.iVec m) = 0 := fun m => by
      by_contra hh'
      exact hS ⟨m, hh'⟩
    have hL0 : D.Rper l (Work.Diff.STE.B3.Qk D k h) a b z = 0 := by
      rw [show D.Rper l (Work.Diff.STE.B3.Qk D k h) a b z
          = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ((D.R l (Work.Diff.STE.B3.Qk D k h) a b
                (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) from rfl]
      have hz : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
          ((D.R l (Work.Diff.STE.B3.Qk D k h) a b
            (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) = 0 := fun m => by
        simp only [Work.Diff.STE.B3Data.R, hS' m, zero_mul, Complex.ofReal_zero]
      simp only [hz, tsum_zero]
    have hPhi0 : Work.Diff.STE.B3.perPhi D l z = 0 := by
      rw [show Work.Diff.STE.B3.perPhi D l z
          = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ((D.psi l (z + Work.Diff.STE.iVec m)
                * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ) from rfl]
      have hz : ∀ m : Fin (Module.finrank ℝ E) → ℤ,
          ((D.psi l (z + Work.Diff.STE.iVec m)
            * Real.sqrt (D.dens l (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ) = 0 := fun m => by
        simp only [hS' m, zero_mul, Complex.ofReal_zero]
      simp only [hz, tsum_zero]
    rw [hL0, hPhi0, zero_mul]

/-! ## 3. The requested statement -/

theorem Rper_Qk_eq_perPhi_POp_sigma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (l : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hη1 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → η z = 1)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (ce : Work.Diff.STE.B3.VarCoef.ChartCE (I := I) (M := M) D k l)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (hh : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) :
    D.Rper l (Work.Diff.STE.B3.Qk D k h) a b
      = fun z => Work.Diff.STE.B3.perPhi (I := I) (M := M) D l z *
          (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((ce.co i a b c d z : ℝ) : ℂ) *
              Work.Diff.STE.B3.VarCoef.varLapPow k (ce.A i) (ce.B i)
                (fun w => ∑ c' : Fin (Module.finrank ℝ E),
                  ∑ d' : Fin (Module.finrank ℝ E),
                  ((ce.ci i c d c' d' w : ℝ) : ℂ) *
                    Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h c' d' w) z) :=
  Rper_Qk_eq_perPhi_POp_sigma_gen D k l η hη1 hηt ce.A ce.B ce.ci ce.co
    ce.hA ce.hAp ce.hB ce.hBp ce.hci ce.hcip ce.hco ce.hcop ce.hCE h a b hh

end Work.Diff.STE.B3.VarCoef
