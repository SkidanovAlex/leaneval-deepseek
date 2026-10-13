import Mathlib
import Submission.Work.CoreStep.CrossDefs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open Work.WilE7.CoreStep Work.CoreStep

namespace Work.WilE7.Endgame

/-- The pair point `pairPtUp (absPtUp A) z` only depends on `z` through its `absPt`, and equals
the value of the continuous linear pairing map `pairingCLM` on the pair `(A, absPt z)`. -/
theorem pairPtUp_absPtUp_eq_pairingCLM {n m : ℕ}
    (A : Fin (n + (m + 1)) → ℝ) (z : Fin (0 + (n + (m + 1))) → ℝ) :
    Work.WilE7.CoreStep.pairPtUp (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) A) z
      = Work.CoreStep.pairingCLM n m (A, Work.WilE7.MainDesign.absPt z) := by
  rw [Work.CoreStep.pairingCLM_apply]
  congr 1

/-- The witness pair point is continuous along a converging sequence of bases (with the sheets
continuous on `C`) and a sequence of pair points converging in the `absPt` coordinates. -/
theorem witness_pairPtUp_tendsto {n m k : ℕ} {C : Set (Fin n → ℝ)}
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C) (j : Fin k)
    {x : ℕ → Fin n → ℝ} {x₀ : Fin n → ℝ} (hxC : ∀ t, x t ∈ C)
    (hxtend : Filter.Tendsto x Filter.atTop (nhds x₀)) (hx₀ : x₀ ∈ C)
    {z : ℕ → Fin (0 + (n + (m + 1))) → ℝ} {w : Fin (n + (m + 1)) → ℝ}
    (hztend : Filter.Tendsto (fun t => Work.WilE7.MainDesign.absPt (z t)) Filter.atTop (nhds w)) :
    Filter.Tendsto
      (fun t => Work.WilE7.CoreStep.pairPtUp
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append (x t) (s j (x t))))
        (z t))
      Filter.atTop
      (nhds (Work.WilE7.CoreStep.pairPtUp
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) w))) := by
  -- The sheets converge at `x₀`, using the continuity on `C`.
  have hsx : Filter.Tendsto (fun t => s j (x t)) Filter.atTop (nhds (s j x₀)) := by
    have hxw : Filter.Tendsto x Filter.atTop (nhdsWithin x₀ C) :=
      tendsto_nhdsWithin_iff.mpr ⟨hxtend, Filter.Eventually.of_forall hxC⟩
    have hct : Filter.Tendsto (s j) (nhdsWithin x₀ C) (nhds (s j x₀)) := hcont j x₀ hx₀
    exact hct.comp hxw
  -- The first blocks `Fin.append (x t) (s j (x t))` converge.
  have hA : Filter.Tendsto (fun t => Fin.append (x t) (s j (x t))) Filter.atTop
      (nhds (Fin.append x₀ (s j x₀))) := by
    have h := (Fin.continuous_append n (m + 1)).tendsto (x₀, s j x₀)
    exact h.comp (hxtend.prodMk_nhds hsx)
  -- Both blocks together converge.
  have hpair : Filter.Tendsto
      (fun t => (Fin.append (x t) (s j (x t)), Work.WilE7.MainDesign.absPt (z t)))
      Filter.atTop (nhds (Fin.append x₀ (s j x₀), w)) := hA.prodMk_nhds hztend
  -- Apply the continuous linear pairing map.
  have hmain := ((Work.CoreStep.pairingCLM n m).continuous.tendsto
      (Fin.append x₀ (s j x₀), w)).comp hpair
  -- Rewrite the two endpoints to the form produced by `pairingCLM`.
  have hfun : (fun t => Work.WilE7.CoreStep.pairPtUp
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append (x t) (s j (x t)))) (z t))
      = fun t => Work.CoreStep.pairingCLM n m
          (Fin.append (x t) (s j (x t)), Work.WilE7.MainDesign.absPt (z t)) := by
    funext t
    exact pairPtUp_absPtUp_eq_pairingCLM (Fin.append (x t) (s j (x t))) (z t)
  have hlim : Work.WilE7.CoreStep.pairPtUp
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)))
        (Work.WilE7.CoreStep.absPtUp (n := n) (m := m) w)
      = Work.CoreStep.pairingCLM n m (Fin.append x₀ (s j x₀), w) :=
    (Work.CoreStep.pairingCLM_apply n m (Fin.append x₀ (s j x₀)) w).symm
  rw [hfun, hlim]
  exact hmain

end Work.WilE7.Endgame
