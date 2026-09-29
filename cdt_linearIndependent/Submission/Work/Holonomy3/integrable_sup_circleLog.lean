import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.fstats
import Submission.Work.Holonomy3.expectation_max_blocked
import Submission.Work.Holonomy3.integral_sup_bound

namespace Work.Holonomy3

open Submission.CDTPlan MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Almost-everywhere strong measurability of `t ↦ h (t c)` for `h` continuous on `[0,1]`:
the `c`-th coordinate of `torMeasure d` is `volume` restricted to `[0,1]`. -/
private lemma aemeasurable_comp_eval {d : ℕ} {h : ℝ → ℝ} (hh : ContinuousOn h (Set.Icc 0 1))
    (c : Fin d) : AEMeasurable (fun t : Fin d → ℝ => h (t c)) (torMeasure d) := by
  have hmap : Measure.map (Function.eval c) (torMeasure d)
      = (volume : Measure ℝ).restrict (Set.Icc 0 1) :=
    (MeasureTheory.measurePreserving_eval
      (fun _ : Fin d => (volume : Measure ℝ).restrict (Set.Icc 0 1)) c).map_eq
  have h1 : AEMeasurable h (Measure.map (Function.eval c) (torMeasure d)) := by
    rw [hmap]; exact hh.aemeasurable measurableSet_Icc
  exact h1.comp_aemeasurable (measurable_pi_apply c).aemeasurable

/-- Almost every point of the parameter cube `[0,1]^d` has all coordinates in `[0,1]`. -/
private lemma ae_box_mem (d : ℕ) :
    ∀ᵐ t ∂(torMeasure d), ∀ s : Fin d, t s ∈ Set.Icc (0:ℝ) 1 :=
  MeasureTheory.ae_all_iff.2 (fun s => ae_eval_mem_Icc s)

/-- **Integrability of the sup of the linear forms `Σ_s k_s · log‖φ_{κ s}‖`.**

`K` is a finite set of exponent vectors whose coordinates are bounded by `D`, `φ` is a family of maps
whose `circleLog` is continuous and bounded by `G₀` on `[0,1]`, and `κ` assigns a map to each of the
`d` variables.  Then the function

`t ↦ K.sup' hKne (fun k => ∑ s, (k s : ℝ) * circleLog (φ (κ s)) (t s))`

is integrable for the torus measure `torMeasure d` on the parameter cube `[0,1]^d`.

It is bounded by `d · D · G₀`, and it is a.e. strongly measurable because it is a finite sup of
finite sums of functions `t ↦ circleLog (φ p) (t s)` which are a.e. strongly measurable by
`MeasureTheory.measurePreserving_eval`. -/
theorem integrable_sup_circleLog {l d : ℕ} (K : Finset (Fin d →₀ ℕ)) (hKne : K.Nonempty)
    (φ : Fin (l + 1) → ℂ → ℂ) (κ : Fin d → Fin (l + 1)) (D G₀ : ℝ)
    (hcont : ∀ p, ContinuousOn (Submission.CDTPlan.circleLog (φ p)) (Set.Icc 0 1))
    (hg : ∀ p t, t ∈ Set.Icc 0 1 → |Submission.CDTPlan.circleLog (φ p) t| ≤ G₀)
    (hdeg : ∀ k ∈ K, ∀ j : Fin d, (k j : ℝ) ≤ D) (hD : 0 ≤ D) (hG₀ : 0 ≤ G₀) :
    MeasureTheory.Integrable
      (fun t : Fin d → ℝ => K.sup' hKne (fun k : Fin d →₀ ℕ =>
        ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s)))
      (Work.Holonomy3.torMeasure d) := by
  -- (1) a.e. strong measurability of each summand family indexed by `k ∈ K`
  have hfun : ∀ k ∈ K, AEStronglyMeasurable
      (fun t : Fin d → ℝ =>
        ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s))
      (torMeasure d) := by
    intro k _
    have h' := (Finset.aemeasurable_sum (Finset.univ : Finset (Fin d))
      (fun s _ =>
        (aemeasurable_comp_eval (hcont (κ s)) s).const_mul (k s : ℝ))).aestronglyMeasurable
    have h2 : (∑ i : Fin d,
          fun x : Fin d → ℝ => (k i : ℝ) * Submission.CDTPlan.circleLog (φ (κ i)) (x i))
        = fun t : Fin d → ℝ =>
            ∑ i : Fin d, (k i : ℝ) * Submission.CDTPlan.circleLog (φ (κ i)) (t i) := by
      ext t; simp
    rwa [h2] at h'
  -- (2) a.e. strong measurability of the sup
  have hmeasF : AEStronglyMeasurable
      (fun t : Fin d → ℝ => K.sup' hKne (fun k : Fin d →₀ ℕ =>
        ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s)))
      (torMeasure d) := by
    have h := Finset.sup'_induction (s := K) hKne
      (f := fun k => fun t : Fin d → ℝ =>
        ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s))
      (p := fun F => AEStronglyMeasurable F (torMeasure d))
      (fun a1 ha1 a2 ha2 => ha1.sup ha2) hfun
    have h2 : (K.sup' hKne fun k => fun t : Fin d → ℝ =>
          ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s))
        = fun t : Fin d → ℝ => K.sup' hKne fun k =>
            ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s) := by
      ext t; rw [Finset.sup'_apply]
    rwa [h2] at h
  -- (3) the a.e. bound by `d · D · G₀`
  have hboundF : ∀ᵐ t ∂(torMeasure d),
      ‖K.sup' hKne (fun k : Fin d →₀ ℕ =>
        ∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s))‖
        ≤ (d : ℝ) * (D : ℝ) * G₀ := by
    filter_upwards [ae_box_mem d] with t ht
    rw [Real.norm_eq_abs]
    have hbd : ∀ k ∈ K,
        |∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s)|
          ≤ (d : ℝ) * (D : ℝ) * G₀ := by
      intro k hk
      have h1 : |∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s)|
          ≤ ∑ s : Fin d, (k s : ℝ) * |Submission.CDTPlan.circleLog (φ (κ s)) (t s)| := by
        calc |∑ s : Fin d, (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s)|
            ≤ ∑ s : Fin d,
                |(k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ s : Fin d,
                (k s : ℝ) * |Submission.CDTPlan.circleLog (φ (κ s)) (t s)| := by
              refine Finset.sum_congr rfl (fun s _ => ?_)
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have h2 : ∑ s : Fin d,
            (k s : ℝ) * |Submission.CDTPlan.circleLog (φ (κ s)) (t s)|
          ≤ ∑ _s : Fin d, (D : ℝ) * G₀ :=
        Finset.sum_le_sum (fun s _ =>
          mul_le_mul (hdeg k hk s) (hg (κ s) (t s) (ht s)) (abs_nonneg _) hD)
      have h3 : ∑ _s : Fin d, (D : ℝ) * G₀ = (d : ℝ) * (D : ℝ) * G₀ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      linarith
    rw [abs_le]
    refine ⟨?_, Finset.sup'_le hKne (fun k => ∑ s : Fin d,
      (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s))
      (fun k hk => (abs_le.mp (hbd k hk)).2)⟩
    obtain ⟨k0, hk0⟩ := hKne
    exact le_trans (abs_le.mp (hbd k0 hk0)).1
      (Finset.le_sup' (f := fun k => ∑ s : Fin d,
        (k s : ℝ) * Submission.CDTPlan.circleLog (φ (κ s)) (t s)) hk0)
  -- (4) conclude by the a.e. bound
  exact Integrable.of_bound hmeasF ((d : ℝ) * (D : ℝ) * G₀) hboundF

end

end Work.Holonomy3
