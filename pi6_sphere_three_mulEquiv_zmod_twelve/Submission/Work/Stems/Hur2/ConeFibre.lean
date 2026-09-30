import Submission.Work.Stems.Hur2.BdInj

/-!
# The fibres of the cone map

A function `H` on `I × I` that is constant on `{1} × I` and identifies the two ends `(s,0)`, `(s,1)`
of every horizontal segment (i.e. is constant on the fibres of `bd` along each `s`) is automatically
constant on the fibres of `coneMap`.  This is the condition under which a null-homotopy of the
boundary loop descends to a filling square.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

/-- **Constancy on the fibres of `coneMap`.** -/
theorem coneMap_fibre {X : Type} (H : unitInterval → unitInterval → X)
    (hwrap : ∀ s : unitInterval, H s 0 = H s 1) (hcentre : ∀ t : unitInterval, H 1 t = H 1 0)
    {p q : IC 1 × IC 1} (h : coneMap p = coneMap q) :
    H (p.1 0) (p.2 0) = H (q.1 0) (q.2 0) := by
  have hs : (p.1 0 : ℝ) = (q.1 0 : ℝ) := by
    have h1 : rad (coneMap p) = rad (coneMap q) := by rw [h]
    rw [rad_coneMap, rad_coneMap] at h1
    linarith
  have hsf : p.1 0 = q.1 0 := Subtype.ext hs
  by_cases hs1 : (p.1 0 : unitInterval) = 1
  · have hq1 : (q.1 0 : unitInterval) = 1 := by rw [← hsf]; exact hs1
    rw [hs1, hq1, hcentre (p.2 0), hcentre (q.2 0)]
  · have hsne : (p.1 0 : ℝ) ≠ 1 := by
      intro hc
      exact hs1 (Subtype.ext hc)
    have hne : (1 : ℝ) - (p.1 0 : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne)
    have hne' : (1 : ℝ) - (q.1 0 : ℝ) ≠ 0 := by rw [← hs]; exact hne
    have hbdfun : bd (p.2 0) = bd (q.2 0) := by
      funext j
      apply Subtype.ext
      have hcoord := congrArg (fun z : IC 2 => (z j : ℝ)) h
      have e1 : ((coneMap p : IC 2) j : ℝ)
          = 1 / 2 + (1 - (p.1 0 : ℝ)) * (((bd (p.2 0) : IC 2) j : ℝ) - 1 / 2) := rfl
      have e2 : ((coneMap q : IC 2) j : ℝ)
          = 1 / 2 + (1 - (q.1 0 : ℝ)) * (((bd (q.2 0) : IC 2) j : ℝ) - 1 / 2) := rfl
      rw [e1, e2, hs] at hcoord
      have hcan : ((bd (p.2 0) : IC 2) j : ℝ) - 1 / 2
          = ((bd (q.2 0) : IC 2) j : ℝ) - 1 / 2 := by
        refine mul_left_cancel₀ hne' ?_
        linarith
      linarith
    rcases bd_inj_weak (p.2 0) (q.2 0) hbdfun with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [hsf, h3]
    · rw [h3, h4, hsf]
      exact hwrap (q.1 0)
    · rw [h3, h4, hsf]
      exact (hwrap (q.1 0)).symm

end

end Work.Stems.Hur2
