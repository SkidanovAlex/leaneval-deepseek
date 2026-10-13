import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Filter Topology

namespace Work.FTS.PhiStar.FlatWAux.Fam2Diff

/-- The Gegenbauer family is of class `C⁸` (the order used by `QmSmooth`; the version
`contDiff_gC` in `Gegenbauer.gC_ode` gives only `C³`).  Same two-step induction as there, run at
order `8`: the recurrence expresses `gC (n+2)` by `mul`, `sub` and division by the constant
`n+2`, all of which preserve the order. -/
theorem contDiff_gC_eight : ∀ n : ℕ, ContDiff ℝ 8 (Work.FTS.PhiStar.Gegenbauer.gC n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
    exact contDiff_const
  | one =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
    rw [show Work.FTS.PhiStar.Gegenbauer.gC (n + 2) = (fun x => (2 * ((n : ℝ) + 5 / 2) * x
      * Work.FTS.PhiStar.Gegenbauer.gC (n + 1) x
      - ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x) / ((n : ℝ) + 2)) from rfl]
    exact (((contDiff_const.mul contDiff_id).mul ih2).sub (contDiff_const.mul ih1)).div_const _

/-- `eFam m = cos θ · gC (2m+1) (sin θ)` is of class `C⁸`. -/
theorem contDiff_eFam_eight (m : ℕ) :
    ContDiff ℝ 8 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  show ContDiff ℝ 8 (fun θ : ℝ => Real.cos θ
    * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.contDiff_cos.mul ((contDiff_gC_eight (2 * m + 1)).comp Real.contDiff_sin)

/-- `s2 θ = sin 2θ` is of class `C⁸`. -/
theorem contDiff_s2_eight : ContDiff ℝ 8 Work.Construction.s2 := by
  rw [show Work.Construction.s2 = fun θ : ℝ => Real.sin (2 * θ) from rfl]
  exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

/-- `sin 2θ` does not vanish on `(0, π/2)`, so the defining quotient of `Qm m` is legitimate
there. -/
theorem s2_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Construction.s2 θ ≠ 0 := by
  refine ne_of_gt ?_
  rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem QmSmooth :
    (∀ m : ℕ, ContDiffOn ℝ 8 (Work.FTS.PhiStar.FlatWAux.Qm m) (Set.Ioo 0 (Real.pi / 2))) ∧
      (∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → Work.FTS.PhiStar.FlatWAux.Qm 0 θ = 3 / 2) ∧
      (∀ (r : ℕ), 1 ≤ r → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        iteratedDeriv r (Work.FTS.PhiStar.FlatWAux.Qm 0) θ = 0) := by
  have hs2ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Work.Construction.s2 θ ≠ 0 :=
    fun θ hθ => s2_ne_zero_of_mem_Ioo hθ
  -- the `m = 0` mode is the constant `3/2` on the open interval
  have hconst : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.FTS.PhiStar.FlatWAux.Qm 0 θ = 3 / 2 := by
    intro θ hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have heFam : Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = Real.cos θ * (3 * Real.sin θ) := by
      show Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * 0 + 1) (Real.sin θ)
        = Real.cos θ * (3 * Real.sin θ)
      rw [show (2 * 0 + 1 : ℕ) = 1 from rfl,
        show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
    show Work.FTS.PhiStar.Gegenbauer.eFam 0 θ / Work.Construction.s2 θ = 3 / 2
    rw [heFam, show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl, Real.sin_two_mul]
    have hne : (2 : ℝ) * Real.sin θ * Real.cos θ ≠ 0 := by positivity
    field_simp
  refine ⟨?_, hconst, ?_⟩
  · intro m
    have hmain : ContDiffOn ℝ 8 (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
        / Work.Construction.s2 θ) (Set.Ioo 0 (Real.pi / 2)) :=
      ((contDiff_eFam_eight m).contDiffOn).div contDiff_s2_eight.contDiffOn hs2ne
    show ContDiffOn ℝ 8 (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
      / Work.Construction.s2 θ) (Set.Ioo 0 (Real.pi / 2))
    exact hmain
  · intro r hr θ hθ
    -- on the neighbourhood `(0, π/2)` of `θ`, the function `Qm 0` is the constant `3/2`
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
    have heq : Work.FTS.PhiStar.FlatWAux.Qm 0 =ᶠ[𝓝 θ] (fun _ : ℝ => (3 : ℝ) / 2) :=
      Filter.eventuallyEq_of_mem hmem (fun y hy => hconst y hy)
    have h1 : iteratedDeriv r (Work.FTS.PhiStar.FlatWAux.Qm 0) θ
        = iteratedDeriv r (fun _ : ℝ => (3 : ℝ) / 2) θ :=
      (heq.iteratedDeriv r).eq_of_nhds
    rw [h1, iteratedDeriv_const]
    simp [Nat.one_le_iff_ne_zero.mp hr]

end Work.FTS.PhiStar.FlatWAux.Fam2Diff
