import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.contDiffOn_kappaComp
import Submission.Work.RPB.B3.continuousOn_signedArea_levelData

/-!
# `B5`: continuity in the level parameter of the signed area of the chart level curves

`Work.RPB.B5.kappa_continuous`: for the `ρ = r²`-chart `W` of the chord annulus and its level
inverse `ρh` on the level interval `(-κ, κ)`, the signed area of the level curve

  `σ ↦ signedArea (fun t => uproj (W τ t (ρh τ t σ)))`

is continuous in the level parameter `σ` on `(-κ, κ)`, for every `τ ∈ [0,1]`.

Writing `N τ σ t = uproj (W τ t (ρh τ t σ))`, the proof has two steps.

* The uncurried chart `(τ, t, ρ) ↦ W τ t ρ` is `C⁸` on the slab `[0,1] × ℝ × (-ρ₀,ρ₀)` (`hW`) and
  `ρh` is `C⁸` on the slab `[0,1] × ℝ × (-κ,κ)` (`hρh`), while `hρhv` says exactly that the level
  inversion carries the second slab into the first.  Hence
  `z ↦ (z.1, z.2.1, ρh z.1 z.2.1 z.2.2)` is a `C⁸` map from `[0,1] × ℝ × (-κ,κ)` into the
  `W`-slab, and composing with the (globally `C^∞`) reduced coordinate `uproj` shows that `N` is
  `C⁸` on `[0,1] × ℝ × (-κ,κ)`; this is the standalone lemma
  `Work.RPB.B5.contDiffOn_kappaComp`.
* Fixing `τ ∈ [0,1]`, the map `(σ,t) ↦ N τ σ t` is the composite of `N` with the `C^∞` map
  `(σ,t) ↦ (τ, t, σ)`, hence `C³` on the open strip `(-κ,κ) ×ˢ univ`, and
  `Work.RPB.B3.continuousOn_signedArea_of_contDiffOn` (the signed area of a `C³` curve family
  depending on a parameter in an open set is continuous) gives the claim.
-/

open scoped ContDiff Topology

namespace Work.RPB.B5

theorem kappa_continuous (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (ρ₀ : ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hρh : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-κ) κ,
      ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ContinuousOn
        (fun σ => Work.RPB.signedArea (fun t => Work.RPV.uproj (W τ t (ρh τ t σ))))
        (Set.Ioo (-κ) κ) := by
  have _hκ := hκ
  -- the reduced coordinate of the chart point on the level `σ`, jointly `C⁸` in `(τ,t,σ)`
  have hbox : ContDiffOn ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPV.uproj (W z.1 z.2.1 (ρh z.1 z.2.1 z.2.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) :=
    contDiffOn_kappaComp W ρh ρ₀ κ hW hρh hρhv
  intro τ hτ
  -- fixing `τ`, the level curves `(σ,t) ↦ uproj (W τ t (ρh τ t σ))` form a `C³` family on the
  -- open strip `(-κ,κ) × univ`
  have hG : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 p.1)))
      (Set.Ioo (-κ) κ ×ˢ Set.univ) := by
    have hg : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (τ, (p.2, p.1)))
        (Set.Ioo (-κ) κ ×ˢ Set.univ) := by fun_prop
    have hmapg : Set.MapsTo (fun p : ℝ × ℝ => (τ, (p.2, p.1)))
        (Set.Ioo (-κ) κ ×ˢ Set.univ)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ) := by
      rintro ⟨σ, t⟩ ⟨hσ, -⟩
      exact ⟨hτ, Set.mem_univ _, hσ⟩
    have h := (hbox.of_le (by norm_num)).comp hg hmapg
    simpa only [Function.comp_def] using h
  -- continuity of the signed area of a `C³` family on an open parameter set
  exact Work.RPB.B3.continuousOn_signedArea_of_contDiffOn
    (X := Set.Ioo (-κ) κ)
    (G := fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 p.1))) isOpen_Ioo hG

end Work.RPB.B5