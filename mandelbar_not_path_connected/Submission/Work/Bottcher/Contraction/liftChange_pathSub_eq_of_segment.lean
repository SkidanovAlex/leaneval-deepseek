import Mathlib
import Submission.Work.Bottcher.Contraction.LiftCoreDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Equal lift changes for a loop avoiding a segment

If `γ : C(I, ℂ)` is a closed path whose image is disjoint from the segment joining `p` to `q`,
then the winding numbers of `γ` around `p` and around `q` coincide.  Equivalently, the
**lift changes** (through the exponential covering `ℂ → ℂ*`) of the nowhere-zero paths
`t ↦ γ t - p` and `t ↦ γ t - q` are equal.

The proof is a homotopy-lifting argument.  The "cylinder"
`F (t, s) = γ t - ((1 - s) p + s q) : I × I → ℂ*`
is a nowhere-zero homotopy whose boundary components `{0} × I` and `{1} × I` agree, since
`γ 1 = γ 0`.  Lifting `F` through the exponential covering starting from a lift `f` of
`{0} × I` produces a continuous map `G : I × I → ℂ`.  For every `s`, both `G (1, s)` and
`G (0, s) = f s` project to the same point of `ℂ*`, so `s ↦ G (1, s) - f s` is a continuous
map into the discrete fibre of `1`: being defined on the connected interval `I`, it is constant.
This gives the desired equality.
-/

namespace Work.Bottcher.Contraction

open scoped Topology

noncomputable section

/-- The exponential map viewed as a map `ℂ → ℂ*`. -/
abbrev expCover : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨Complex.exp z, Complex.exp_ne_zero z⟩

@[simp] theorem expCover_coe (z : ℂ) :
    ((expCover z : {z : ℂ // z ≠ 0}) : ℂ) = Complex.exp z := rfl

/-- The cylinder `(t, s) ↦ γ t - ((1 - s) p + s q) : I × I → ℂ*`, defined when `γ` avoids the
segment from `p` to `q`. -/
def segmentHomotopy (γ : C(unitInterval, ℂ)) (p q : ℂ)
    (hseg : ∀ t : unitInterval, ∀ s : ℝ, s ∈ Set.Icc 0 1 → γ t ≠ (1 - s) * p + s * q) :
    C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}) where
  toFun ts := ⟨γ ts.1 - ((1 - (ts.2 : ℝ)) * p + (ts.2 : ℝ) * q),
    sub_ne_zero.mpr (hseg ts.1 (ts.2 : ℝ) ts.2.2)⟩
  continuous_toFun :=
    (by fun_prop : Continuous fun ts : unitInterval × unitInterval =>
        γ ts.1 - ((1 - (ts.2 : ℝ)) * p + (ts.2 : ℝ) * q)).subtype_mk
      (fun ts => sub_ne_zero.mpr (hseg ts.1 (ts.2 : ℝ) ts.2.2))

@[simp] theorem segmentHomotopy_apply (γ : C(unitInterval, ℂ)) (p q : ℂ)
    (hseg : ∀ t : unitInterval, ∀ s : ℝ, s ∈ Set.Icc 0 1 → γ t ≠ (1 - s) * p + s * q)
    (ts : unitInterval × unitInterval) :
    ((segmentHomotopy γ p q hseg ts : {z : ℂ // z ≠ 0}) : ℂ)
      = γ ts.1 - ((1 - (ts.2 : ℝ)) * p + (ts.2 : ℝ) * q) := rfl

/-- The boundary path `s ↦ F (0, s)` of a cylinder in `ℂ*`. -/
def basePath (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0})) :
    C(unitInterval, {z : ℂ // z ≠ 0}) :=
  F.comp (ContinuousMap.prodMk (ContinuousMap.const unitInterval 0) (ContinuousMap.id unitInterval))

theorem basePath_apply (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}))
    (s : unitInterval) : basePath F s = F (0, s) := rfl

/-- A lift of the boundary path `s ↦ F (0, s)` through the exponential covering, starting at
`Complex.log` of its initial point. -/
def baseLift (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0})) : C(unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftPath (basePath F)
    (Complex.log ((basePath F 0 : {z : ℂ // z ≠ 0}) : ℂ))
    (Subtype.ext (Complex.exp_log (basePath F 0).2).symm)

theorem baseLift_zero (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0})) :
    baseLift F 0 = Complex.log ((basePath F 0 : {z : ℂ // z ≠ 0}) : ℂ) :=
  Complex.isCoveringMap_exp.liftPath_zero (basePath F) _ _

theorem exp_baseLift (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0})) (s : unitInterval) :
    Complex.exp (baseLift F s) = ((basePath F s : {z : ℂ // z ≠ 0}) : ℂ) :=
  congrArg Subtype.val
    (congr_fun (Complex.isCoveringMap_exp.liftPath_lifts (basePath F) _ _) s)

theorem liftHomotopyBase (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}))
    (a : unitInterval) : F (0, a) = expCover (baseLift F a) := by
  refine Subtype.ext ?_
  rw [expCover_coe, ← basePath_apply, ← exp_baseLift]

/-- The homotopy lift of `F` through the exponential covering, extending `baseLift`. -/
def cylLift (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0})) :
    C(unitInterval × unitInterval, ℂ) :=
  Complex.isCoveringMap_exp.liftHomotopy F (baseLift F) (liftHomotopyBase F)

theorem exp_cylLift (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}))
    (t s : unitInterval) :
    Complex.exp (cylLift F (t, s)) = ((F (t, s) : {z : ℂ // z ≠ 0}) : ℂ) :=
  congrArg Subtype.val
    (congr_fun (Complex.isCoveringMap_exp.liftHomotopy_lifts F (baseLift F) (liftHomotopyBase F))
      (t, s))

theorem cylLift_zero (F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}))
    (s : unitInterval) : cylLift F (0, s) = baseLift F s :=
  Complex.isCoveringMap_exp.liftHomotopy_zero F (baseLift F) (liftHomotopyBase F) s

/-- **Uniqueness of the exponential lift.** A continuous `Γ` with `exp (Γ t) = δ t` and
`Γ 0 = e` agrees with `liftOf δ hδ e he`. -/
theorem liftOf_eq_of_lifts {δ : C(unitInterval, ℂ)} {hδ : ∀ t, δ t ≠ 0} {e : ℂ}
    {he : Complex.exp e = δ 0} {Γ : unitInterval → ℂ} (hcont : Continuous Γ)
    (hlift : ∀ t, Complex.exp (Γ t) = δ t) (h0 : Γ 0 = e) :
    ∀ t, liftOf δ hδ e he t = Γ t := by
  have hcomp : expCover ∘ Γ = ⇑(pathSubtype δ hδ) := funext fun t => Subtype.ext (hlift t)
  have h := (Complex.isCoveringMap_exp.eq_liftPath_iff (γ := pathSubtype δ hδ) (e := e)
    (γ_0 := Subtype.ext he.symm)).mpr ⟨hcont, hcomp, h0⟩
  intro t
  show Complex.isCoveringMap_exp.liftPath (pathSubtype δ hδ) e (Subtype.ext he.symm) t = Γ t
  exact (congr_fun h t).symm

/-- The lift change computed from any lift `Γ` of a nowhere-zero path with `exp (Γ 0) = δ 0`. -/
theorem liftChange_eq_of_lift {δ : C(unitInterval, ℂ)} (hδ : ∀ t, δ t ≠ 0) {e : ℂ}
    (he : Complex.exp e = δ 0) {Γ : unitInterval → ℂ} (hcont : Continuous Γ)
    (hlift : ∀ t, Complex.exp (Γ t) = δ t) (h0 : Γ 0 = e) :
    liftChange δ hδ = Γ 1 - e := by
  rw [liftChange_eq_liftOf δ hδ e he,
    liftOf_eq_of_lifts (δ := δ) (hδ := hδ) (e := e) (he := he) hcont hlift h0 1]

theorem liftChange_pathSub_eq_of_segment (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) {p q : ℂ}
    (hseg : ∀ t : unitInterval, ∀ s : ℝ, s ∈ Set.Icc 0 1 → γ t ≠ (1 - s) * p + s * q)
    (h₁ : ∀ t, Work.Bottcher.Contraction.pathSub γ p t ≠ 0)
    (h₂ : ∀ t, Work.Bottcher.Contraction.pathSub γ q t ≠ 0) :
    Work.Bottcher.Contraction.liftChange (Work.Bottcher.Contraction.pathSub γ p) h₁ =
      Work.Bottcher.Contraction.liftChange (Work.Bottcher.Contraction.pathSub γ q) h₂ := by
  set F : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}) :=
    segmentHomotopy γ p q hseg with hF
  have hF0val : ((F (0, 0) : {z : ℂ // z ≠ 0}) : ℂ) = pathSub γ p 0 := by
    simp only [hF, segmentHomotopy_apply]
    norm_num
  have hF1val : ((F (0, 1) : {z : ℂ // z ≠ 0}) : ℂ) = pathSub γ q 0 := by
    simp only [hF, segmentHomotopy_apply]
    norm_num
  have he₀ : Complex.exp (baseLift F 0) = pathSub γ p 0 := by
    rw [exp_baseLift, basePath_apply]; exact hF0val
  have he₁ : Complex.exp (baseLift F 1) = pathSub γ q 0 := by
    rw [exp_baseLift, basePath_apply]; exact hF1val
  have hp : liftChange (pathSub γ p) h₁ = cylLift F (1, 0) - baseLift F 0 := by
    refine liftChange_eq_of_lift (δ := pathSub γ p) h₁ he₀
      (Γ := fun t => cylLift F (t, 0)) ?_ ?_ ?_
    · exact (cylLift F).continuous.comp (Continuous.prodMk continuous_id continuous_const)
    · intro t
      rw [exp_cylLift]
      simp only [hF, segmentHomotopy_apply, pathSub_apply]
      norm_num
    · rw [cylLift_zero]
  have hq : liftChange (pathSub γ q) h₂ = cylLift F (1, 1) - baseLift F 1 := by
    refine liftChange_eq_of_lift (δ := pathSub γ q) h₂ he₁
      (Γ := fun t => cylLift F (t, 1)) ?_ ?_ ?_
    · exact (cylLift F).continuous.comp (Continuous.prodMk continuous_id continuous_const)
    · intro t
      rw [exp_cylLift]
      simp only [hF, segmentHomotopy_apply, pathSub_apply]
      norm_num
    · rw [cylLift_zero]
  have hconst : cylLift F (1, 0) - baseLift F 0 = cylLift F (1, 1) - baseLift F 1 := by
    have hdisc : DiscreteTopology (expCover ⁻¹' {⟨1, one_ne_zero⟩}) :=
      (Complex.isCoveringMap_exp ⟨1, one_ne_zero⟩).discreteTopology_fiber
    have hfib : ∀ s : unitInterval, Complex.exp (cylLift F (1, s) - baseLift F s) = 1 := by
      intro s
      rw [Complex.exp_sub, exp_cylLift, exp_baseLift, basePath_apply]
      simp only [hF, segmentHomotopy_apply]
      rw [hloop]
      exact div_self (F (0, s)).2
    let ψ : unitInterval → (expCover ⁻¹' {⟨1, one_ne_zero⟩}) := fun s =>
      ⟨cylLift F (1, s) - baseLift F s, by
        rw [Set.mem_preimage, Set.mem_singleton_iff]
        refine Subtype.ext ?_
        simpa using hfib s⟩
    have hcontψ : Continuous ψ := by
      have h1 : Continuous fun s : unitInterval => cylLift F (1, s) - baseLift F s :=
        ((cylLift F).continuous.comp (Continuous.prodMk continuous_const continuous_id)).sub
          (baseLift F).continuous
      exact h1.subtype_mk fun s => (ψ s).2
    have h01 : ψ 0 = ψ 1 := PreconnectedSpace.constant inferInstance hcontψ
    exact congrArg Subtype.val h01
  rw [hp, hq, hconst]

end

end Work.Bottcher.Contraction
