import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseC3QAll.Assembly
import Submission.Work.BoseC3QAll.PH_subset_PHq_sub
import Submission.Work.BoseC3QAll.Prep
import Submission.Work.BoseC3QAll.Q3T_split
import Submission.Work.BoseC3QAll.kernel_basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7AK.Glue` — from the kernel interface to the assembly

The remaining glue between the kernel interface `Q3KernelFSAll` and the final
assembly:

* `substHyp_of_kernel` — `Q3KernelFSAll K₀ F T E` + `FSParamsView` at small `t` gives
  `SubstHypG F T E`: `hasKernel` and the parities of `χ̂`, `χ̂²` are fields of
  `Q3KernelFSAll`, `α` is even by `A_even`/`B_even`, and the denominators `1−α²` do
  not vanish on the pairs used because `kernel_basic` gives `1−α_q² ≥ 1/2` on
  `P_H^q` while `PH_subset_PHq_sub` puts both `k` and `s−k` there;
* `splitQ3A` — the preparation bundle: FS `lem:EstimatesOnQ3-js`'s split plus
  `𝓁² ≤ 1`;
* `control3QA_of_estimates_and_arithmetic` — the end-to-end assembly: the three
  `Prop`-valued estimates and the arithmetic `ErrALe`, nothing else, give
  `thm:Control3Q` with the absolute constant `1`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

universe u v

/-- From the kernel interface to the substitution hypotheses: at small `t`,
`Q3KernelFSAll K₀ F T E` implies `SubstHypG F T E`. -/
theorem substHyp_of_kernel (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode) (hv : FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Q3KernelFSAll K₀ F T E → SubstHypG F T E := by
  obtain ⟨t₁, ht₁, H₁⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, H₂⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK
  have h1 := H₁ F T E hv (le_trans hle (min_le_left _ _)) hb hK
  have h2 := H₂ F T E hv (le_trans hle (min_le_right _ _)) hb hK
  obtain ⟨hαeven, -, hhalf, -, -⟩ := h1
  obtain ⟨hPHsub, hsub, -⟩ := h2
  refine substHypG_of_kernel hK hαeven ?_
  intro s k hfL hk hW
  have hkPH : F.PH E.KH E.aScat k := by
    have h := hk
    simp only [FockData.PHset, Finset.mem_filter] at h
    exact h.2
  have hkq : F.PHq E.KH E.aScat k := hPHsub k hkPH
  have hskq : F.PHq E.KH E.aScat (s - k) := hsub s k hfL hk hW
  exact ⟨ne_of_gt (lt_of_lt_of_le (by norm_num) (hhalf k hkq)),
    ne_of_gt (lt_of_lt_of_le (by norm_num) (hhalf (s - k) hskq))⟩

/-- **The preparation bundle `SplitQ3A`**: at FS's parameters with the kernel
interface, `Q₃` splits into its four pieces, and `𝓁² ≤ 1`.  (The thresholds of
`kernel_basic` and `PH_subset_PHq_sub` are extracted with `Classical.choice`,
since they are existential statements.) -/
noncomputable def splitQ3A (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) : SplitQ3A K₀ b₀ hb₀ := by
  classical
  let t₁ : ℝ := Classical.choose (kernel_basic K₀ b₀ hb₀)
  have ht₁ := Classical.choose_spec (kernel_basic K₀ b₀ hb₀)
  let t₂ : ℝ := Classical.choose (PH_subset_PHq_sub K₀ b₀ hb₀)
  have ht₂ := Classical.choose_spec (PH_subset_PHq_sub K₀ b₀ hb₀)
  refine ⟨min t₁ t₂, lt_min ht₁.1 ht₂.1, ?_, ?_, ?_⟩
  · intro Mode _ _ _ F T E hv hle hb hK
    have hs : SubstHypG F T E := by
      have h1 := ht₁.2 F T E hv (le_trans hle (min_le_left _ _)) hb hK
      have h2 := ht₂.2 F T E hv (le_trans hle (min_le_right _ _)) hb hK
      obtain ⟨hαeven, -, hhalf, -, -⟩ := h1
      obtain ⟨hPHsub, hsub, -⟩ := h2
      refine substHypG_of_kernel hK hαeven ?_
      intro s k hfL hk hW
      have hkPH : F.PH E.KH E.aScat k := by
        have h := hk
        simp only [FockData.PHset, Finset.mem_filter] at h
        exact h.2
      have hkq : F.PHq E.KH E.aScat k := hPHsub k hkPH
      have hskq : F.PHq E.KH E.aScat (s - k) := hsub s k hfL hk hW
      exact ⟨ne_of_gt (lt_of_lt_of_le (by norm_num) (hhalf k hkq)),
        ne_of_gt (lt_of_lt_of_le (by norm_num) (hhalf (s - k) hskq))⟩
    exact Q3T_split F T E hs
  · intro Mode _ _ _ E hv _
    exact lille_sq_le_one E hv
  · intro Mode _ _ _ F T E hv hle hb hK
    exact (ht₂.2 F T E hv (le_trans hle (min_le_right _ _)) hb hK).2.2

/-- **The end-to-end assembly**: the three `Prop`-valued estimates and the
arithmetic leg give `thm:Control3Q` with absolute constants (the constant is
`1`: `controlErrA E = μ²aℓ³(μa³)^{1/2+1/323}`). -/
theorem control3QFS_of_estimates_and_arithmetic (K₀ b₀ : ℝ) (hb₀ : 0 < b₀)
    (h1 : EstQ3oneA.{u, v} K₀ b₀ hb₀) (h23 : EstQ3twoThreeA.{u, v} K₀ b₀ hb₀)
    (h4 : EstQ3fourA.{u, v} K₀ b₀ hb₀)
    (hErr : ∀ C₁ C₂₃ C₄ : ℝ, ErrALe.{u} b₀ hb₀ C₁ C₂₃ C₄) :
    Control3QFS.{u, v} K₀ b₀ hb₀ :=
  control3QFS_of_three.{u, v} K₀ b₀ hb₀ (splitQ3A.{u, v} K₀ b₀ hb₀) h1 h23 h4 hErr

end Work.BoseC3QAll
