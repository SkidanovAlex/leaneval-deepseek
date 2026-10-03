import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.ofParts

/-!
# `Work.Horn.hornOfParts` — `HornStatement` from the lead's pieces

Top-level assembly: given the lead's six pieces (as `HornTopoStatement`, `HornPhiStatement`,
`HornVarphiStatement`, `HornSCStatement`, and the three assembly conclusions `crit`, `cov`,
`surj_inf` in their `∀`-form), plus the two remaining inputs of the HORN area

* `hsecond` / `hgF0` — Lemma 5.4 (`g''(0) ≠ 0` and the rescaled horn map lies in `𝓕₀`),
* (`IsTInvariant d.DE`, if ever needed, is NOT a field of `ParabData` any more: it follows from
  `φ (Dφ) ⊆ D₀` via `Work.Horn.DE_T_of_phi_maps_to_D0`; see `NOTES_SESSION14.md` §11.)
* `hcl` — the lower-end sign `cl_im_pos`,

we obtain `HornStatement`.  `Work.Horn.horn` is then
`horn_of_parts HornTopo.horn_topo HornPhi.horn_phi HornVarphi.horn_varphi HornSC.horn_sc ...`.
-/

namespace Work.Horn

noncomputable section

open _root_.MandelDim Filter Topology Metric Set
open scoped Topology

/-- **`HornStatement` from the pieces.** -/
theorem horn_of_parts
    (hTopo : HornTopoStatement) (hSC : HornSCStatement)
    (hcrit : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀),
      IsF0Setup f₀ D₀ B c →
      ∀ w ∈ BuOf d B ∪ BlOf d B, deriv d.E w = 0 → ∃ k : ℤ, d.E w = d.Φ c + k)
    (hcov : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀),
      IsF0Setup f₀ D₀ B c →
      IsCoveringMapOn (fun x : BuOf d B => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
      IsCoveringMapOn (fun x : BlOf d B => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k})
    (hsurj : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀),
      IsF0Setup f₀ D₀ B c →
      (∀ y : ℂ, ∃ w ∈ BuOf d B, d.E w = y) ∧
      (∀ y : ℂ, ∃ w ∈ BlOf d B, d.E w = y))
    (hinf : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀),
      IsF0Setup f₀ D₀ B c →
      (∀ y : ℂ, (piExp '' {w : ℂ | w ∈ BuOf d B ∧ d.E w = y}).Infinite) ∧
      (∀ y : ℂ, (piExp '' {w : ℂ | w ∈ BlOf d B ∧ d.E w = y}).Infinite))
    (hsecond : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀),
      IsF0Setup f₀ D₀ B c → deriv (deriv (pushdown d.E)) 0 ≠ 0)
    (hgF0 : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀),
      IsF0Setup f₀ D₀ B c →
      InF0 (fun ζ => (deriv (deriv (pushdown d.E)) 0 / 2) *
          pushdown d.E (ζ / (deriv (deriv (pushdown d.E)) 0 / 2)))
        ((fun ζ => (deriv (deriv (pushdown d.E)) 0 / 2) * ζ) ''
          insert 0 (piExp '' (BuOf d B ∪ BlOf d B))))
    (hcl : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀),
      IsF0Setup f₀ D₀ B c →
      ∀ cl : ℂ, Tendsto (fun w => d.E w - w) lowerEnd (𝓝 cl) → 0 < cl.im) :
    HornStatement := by
  intro f₀ D₀ hF0 d
  obtain ⟨hgem, B, hB, c, ⟨hcB, hderc⟩, huniqc⟩ := hF0
  have hsetup : IsF0Setup f₀ D₀ B c :=
    ⟨hgem, hB, hcB, hderc, fun c' hc' hd => huniqc c' ⟨hc', hd⟩⟩
  exact hornData_of_parts hTopo hSC hsetup
    (hcrit f₀ D₀ B c d hsetup) (hcov f₀ D₀ B c d hsetup)
    (hsurj f₀ D₀ B c d hsetup) (hinf f₀ D₀ B c d hsetup)
    (hsecond f₀ D₀ B c d hsetup) (hgF0 f₀ D₀ B c d hsetup)
    (hcl f₀ D₀ B c d hsetup)

end

end Work.Horn
