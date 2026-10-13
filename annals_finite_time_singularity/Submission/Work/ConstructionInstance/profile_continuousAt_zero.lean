import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **Continuity of the profile at `θ = 0`.**  For `0 < p`, a perturbation `g` vanishing on the
angular boundaries (`VanishTheta`) and smooth near the closed quadrant (`SmoothNbhd`), the profile
`F = F_* + g` (extended oddly in `θ`) is continuous at `(z,0)` for every `z > -1`.

Both branches of the odd extension agree at `θ = 0` because `F_*(z,0) = Γ(0)·… = 0` (`p ≠ 0`) and
`g z 0 = 0`; the reflected branch `θ ↦ -(F_*(z,-θ) + g(z,-θ))` is continuous as the composition of
the (continuous) reflection `θ ↦ -θ` with the profile.  Only the *restricted* continuity of the two
branches is used, on the closed halves `{θ ≥ 0}` and `{θ ≤ 0}`, which cover the plane. -/
theorem profile_continuousAt_zero {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ → ℝ}
    (hvt : Work.Spaces.VanishTheta g) (hsmooth : Work.Spaces.SmoothNbhd g) {z : ℝ}
    (hz : -1 < z) :
    ContinuousAt (Function.uncurry (Work.ConstructionInstance.profile p g)) (z, 0) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hg0 : ∀ z' : ℝ, g z' 0 = 0 := hvt.1
  have hF0 : ∀ z' : ℝ, Work.Construction.Fstar p z' 0 = 0 :=
    fun z' => Fstar_zero_theta hp0 z'
  -- The "positive branch" `A(z,θ) = F_*(z,θ) + g(z,θ)` is continuous at `(z,0)`.
  have hGam : Continuous (fun q : ℝ × ℝ => Work.Spaces.Gam p q.2) := by
    unfold Work.Spaces.Gam
    exact (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ p / 3)).comp
      ((Real.continuous_sin.comp continuous_snd).mul
        ((Real.continuous_cos.comp continuous_snd).pow 2))
  have hFst : ContinuousAt (fun q : ℝ × ℝ => Work.FM.Fstar q.1) (z, 0) :=
    ContinuousAt.comp (x := (z, 0)) (g := Work.FM.Fstar) (f := fun q : ℝ × ℝ => q.1)
      (Work.FM.hasDerivAt_Fstar z hz).continuousAt
      (continuous_fst.continuousAt : ContinuousAt (fun q : ℝ × ℝ => q.1) (z, 0))
  have hFcont : ContinuousAt (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) (z, 0) :=
    ((continuousAt_const.mul (hGam.continuousAt.div_const (Work.Spaces.c p))).mul hFst)
  have hgcont : ContinuousAt (fun q : ℝ × ℝ => g q.1 q.2) (z, 0) :=
    hsmooth.continuousOn.continuousAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
        ⟨hz, by constructor <;> linarith [Real.pi_pos]⟩)
  have hAcont : ContinuousAt
      (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, 0) :=
    hFcont.add hgcont
  -- The reflection `q ↦ (q.1, -q.2)`.
  have hPhicont : Continuous (fun q : ℝ × ℝ => (q.1, -q.2)) := by fun_prop
  -- The reflected branch `q ↦ -(F_*(q) + g(q))` (with the sign flip) is continuous at `(z,0)`.
  have hnegcont : ContinuousAt
      (fun q : ℝ × ℝ => -(Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2))) (z, 0) := by
    have hA0 : ContinuousAt
        (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2) (z, -0) := by
      simpa using hAcont
    have hcomp := ContinuousAt.comp (x := (z, 0))
      (g := fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2)
      (f := fun q : ℝ × ℝ => (q.1, -q.2)) hA0 hPhicont.continuousAt
    have hrefl : ((fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2 + g q.1 q.2)
        ∘ (fun q : ℝ × ℝ => (q.1, -q.2)))
        = fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 (-q.2) + g q.1 (-q.2) := by
      ext q; rfl
    rw [hrefl] at hcomp
    exact hcomp.neg
  -- The profile equals `A` on the closed half `{θ ≥ 0}`.
  have hs1 : ContinuousWithinAt (Function.uncurry (profile p g))
      {q : ℝ × ℝ | 0 ≤ q.2} (z, 0) :=
    hAcont.continuousWithinAt.congr
      (fun y hy => profile_of_nonneg hy)
      (profile_of_nonneg le_rfl)
  -- The profile equals `-(A ∘ reflect)` on the closed half `{θ ≤ 0}`.
  have hs2 : ContinuousWithinAt (Function.uncurry (profile p g))
      {q : ℝ × ℝ | q.2 ≤ 0} (z, 0) := by
    refine hnegcont.continuousWithinAt.congr (fun y hy => ?_) ?_
    · obtain ⟨a, b⟩ := y
      by_cases h : 0 ≤ b
      · have hb : b = 0 := le_antisymm hy h
        subst hb
        rw [Function.uncurry_apply_pair, profile_of_nonneg (le_refl (0 : ℝ)), hF0 a, hg0 a]
        simp [hF0 a, hg0 a]
      · exact profile_of_neg h
    · rw [Function.uncurry_apply_pair, profile_of_nonneg (le_refl (0 : ℝ)), hF0 z, hg0 z]
      simp [hF0 z, hg0 z]
  have hcover : {q : ℝ × ℝ | 0 ≤ q.2} ∪ {q : ℝ × ℝ | q.2 ≤ 0} = Set.univ := by
    ext q
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact le_total 0 q.2
  have hunion : ContinuousWithinAt (Function.uncurry (profile p g))
      ({q : ℝ × ℝ | 0 ≤ q.2} ∪ {q : ℝ × ℝ | q.2 ≤ 0}) (z, 0) :=
    continuousWithinAt_union.mpr ⟨hs1, hs2⟩
  rw [hcover] at hunion
  exact (continuousWithinAt_univ _ _).1 hunion

end Work.ConstructionInstance
