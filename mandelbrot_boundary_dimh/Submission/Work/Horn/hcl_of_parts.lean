import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.horn_cl_im_pos
import Submission.Work.Horn.section_Bl_free
import Submission.Work.Horn.section_Bu_free
import Submission.Work.Horn.bu_side_false
import Submission.Work.Horn.hornS_deriv_of_deep_section
import Submission.Work.Horn.top_section_exists

/-!
# `Work.Horn.hcl_of_parts` — the lower-end sign from the Prop.-5.3 pieces

Assembly of `HornData.cl_im_pos` (`0 < Im cl` for the lower-end limit `E w - w → cl`) from the
four Horn pieces (`HornTopoStatement`, `HornSCStatement`, the covering statement `hcov` and the
infinite-fibre statement `hinf`), using the toolbox of `Work.Horn.horn_cl_im_pos` (not its final
theorem, which is being replaced here).

The route is the one of `NOTES_HCL.md`:

* Step A (`bu_side_false`): the critical-value class `v + ℤ` (`v = d.Φ c`) cannot miss `Bu`.
  Otherwise the global inverse branch of `E` over `Bu` would descend to a self-map of the bounded
  cylinder domain `{0} ∪ π(Bu)` with `|S'(0)| = 1`, contradicting strict Schwarz—Cartan.
* Hence (`critvalue_avoid`) the class misses `Bl`, so the deep lower-end section `σ` of `E` over
  the simply connected `Bl` exists (`section_Bl_free`).
* `hornS_deriv_of_deep_section` upgrades `σ` to an analytic germ `Ŝ = hornS σ` at `0` with
  `Ŝ'(0) = π(cl)`, and `cl_im_pos_of_section` (strict Cartan at the lower end) gives `0 < cl.im`.
-/

namespace Work.Horn

open MandelDim Filter Topology Metric Set
open scoped Topology

noncomputable section

theorem hcl_of_parts (hTopo : MandelDim.HornTopoStatement) (hSC : MandelDim.HornSCStatement)
    (hcov : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      IsCoveringMapOn (fun x : MandelDim.BuOf d B => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
      IsCoveringMapOn (fun x : MandelDim.BlOf d B => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k})
    (hinf : ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      (∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = y}).Infinite) ∧
      (∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BlOf d B ∧ d.E w = y}).Infinite)) :
    ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀),
      MandelDim.IsF0Setup f₀ D₀ B c →
      ∀ cl : ℂ, Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl) → 0 < cl.im := by
  intro f₀ D₀ B c d hsetup cl hcl
  -- unpack the four pieces
  obtain ⟨hBuO, hBlO, htBu, htBl, hup₀, hlo₀, hsub⟩ := hTopo f₀ D₀ B c d hsetup
  obtain ⟨hBuS, hBlS, hdisj⟩ := hSC f₀ D₀ B c d hsetup
  obtain ⟨hcovu, hcovl⟩ := hcov f₀ D₀ B c d hsetup
  obtain ⟨hinfu, hinfl⟩ := hinf f₀ D₀ B c d hsetup
  -- a positive height `η'` at which both half-plane inclusions hold
  set η' : ℝ := max d.η₀ 1 with hη'def
  have hη'pos : 0 < η' := by
    rw [hη'def]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hη'ge : d.η₀ ≤ η' := by rw [hη'def]; exact le_max_left _ _
  have hup : {w : ℂ | η' < w.im} ⊆ MandelDim.BuOf d B :=
    fun w hw => hup₀ (lt_of_le_of_lt hη'ge hw)
  have hlo : {w : ℂ | w.im < -η'} ⊆ MandelDim.BlOf d B :=
    fun w hw => hlo₀ (lt_of_lt_of_le hw (neg_le_neg hη'ge))
  -- `Bu` stays above `-η'`: it avoids `Bl` and `{Im < -η₀} ⊆ Bl`
  have hlowBu : ∀ w ∈ MandelDim.BuOf d B, -η' ≤ w.im := by
    intro w hw
    have h1 : -d.η₀ ≤ w.im := by
      by_contra hcon
      exact Set.disjoint_left.mp hdisj hw (hlo₀ (not_le.mp hcon))
    exact le_trans (neg_le_neg hη'ge) h1
  -- `Bl` stays below `η'`: it avoids `Bu` and `{η₀ < Im} ⊆ Bu`
  have hhiBl : ∀ w ∈ MandelDim.BlOf d B, w.im ≤ η' := by
    intro w hw
    by_contra hcon
    exact Set.disjoint_left.mp hdisj (hup₀ (lt_of_le_of_lt hη'ge (not_le.mp hcon))) hw
  -- **Step A**: the critical-value class `d.Φ c + ℤ` meets `Bu`
  have hexBu : ∃ k : ℤ, d.Φ c + k ∈ MandelDim.BuOf d B := by
    by_contra hcon
    refine bu_side_false f₀ D₀ d (MandelDim.BuOf d B) η' (d.Φ c) hη'pos hBuO hBuS htBu hup
      hlowBu ?_ hcovu ?_ hinfu
    · intro w hw; exact hsub (Or.inl hw)
    · intro k hk; exact hcon ⟨k, hk⟩
  -- **Step B**: hence the class misses `Bl`, and `Bl` is free of critical values
  have havoid : ∀ k : ℤ, d.Φ c + k ∉ MandelDim.BlOf d B := by
    rcases critvalue_avoid (d.Φ c) htBu htBl hdisj with h | h
    · exact h
    · obtain ⟨k, hk⟩ := hexBu
      exact absurd hk (h k)
  have havoid' : ∀ w ∈ MandelDim.BlOf d B, ∀ k : ℤ, w ≠ d.Φ c + k := by
    intro w hw k hwk
    exact havoid k (hwk ▸ hw)
  -- the lifted horn map is holomorphic and `T`-equivariant on `Bl ⊆ DE`
  have hEhol : DifferentiableOn ℂ d.E (MandelDim.BlOf d B) :=
    d.Φ_holo.comp (d.φ_holo.mono fun w hw => (hsub (Or.inr hw)).1)
      fun w hw => (hsub (Or.inr hw)).2
  have hEeq : ∀ w ∈ MandelDim.BlOf d B, d.E (w + 1) = d.E w + 1 :=
    E_add_one_of_subset_DE d (fun w hw => hsub (Or.inr hw))
  -- the global lower-end section of `E` over the simply connected `Bl`
  obtain ⟨y₀, x₀, σ, _hy₀, _hx₀, _hEx₀, hσdiff, _hσy₀, hσsec, hσT, _hσlim⟩ :=
    section_Bl_free (E := d.E) (D := MandelDim.BlOf d B) (cl := cl) (η := η') (v := d.Φ c)
      hBlO hBlS htBl hlo hEhol hEeq hcovl havoid' hcl
  -- the lower-end asymptotics of `E` in `ε`-form
  have hasym : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, w.im < R → ‖d.E w - w - cl‖ < ε :=
    tendsto_lowerEnd_iff.mp hcl
  -- `Ŝ = hornS σ` is analytic at `0` with `Ŝ'(0) = π(cl)`
  obtain ⟨hana, _h0, hder⟩ := hornS_deriv_of_deep_section (E := d.E) (s := σ)
    (D := MandelDim.BlOf d B) (cl := cl) (η := η') hBlO htBl hσdiff hσT
    (fun w hw => (hσsec w hw).1) (fun w hw => (hσsec w hw).2) hlo hhiBl hasym
  -- strict Schwarz at the lower end
  exact cl_im_pos_of_section f₀ D₀ d (Bu := MandelDim.BuOf d B) (Bl := MandelDim.BlOf d B)
    (η := η') (cl := cl) (s := σ) hBuO htBu hup hBlO hBlS htBl hlo hdisj hsub hinfl hσdiff
    (fun y hy => (hσsec y hy).1) (fun y hy => (hσsec y hy).2) hσT hana hder

end

end Work.Horn
