/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ThetaUnifPz.lean` — the `Pz`/`bump` legs of the uniform
# angular-flatness route

`Work.FTS.EpsEngine.ThetaUnif` is the *uniform* (`ε`-`δ`, uniformly in `z`) angular flatness of a
profile; it is the hypothesis under which the mollifier preserves the angular boundary traces
(`ThetaUnifJeps`), sums of profiles preserve them (`ThetaUnifAdd`) and fake-time integrals preserve
them (`ThetaUnifInterval`).  The missing legs of that route are the **projection** `Pz` (which
subtracts a multiple of the bump) and the **bump** itself:

* `thetaUnif_bump` — `bump` vanishes in a whole `θ`-neighbourhood of both ends of the quadrant, so
  every one of its mixed derivatives vanishes there (`StrongEps.bump_iter_eq_zero_of_not_mem`,
  proved in `StrongEps/BumpDefs.lean`), hence `ThetaUnif α k bump`;
* `thetaUnif_const_mul`, `thetaUnif_neg`, `thetaUnif_sub` — closure of `ThetaUnif` under the
  elementary algebraic operations (the `mixed`-operators are linear on the open quadrant, which is
  the only place where `ThetaUnif` is stated);
* `thetaUnif_Pz` — `ThetaUnif α k f ⟹ ThetaUnif α k (Pz f)`, from `PZeroAux.mixed_Pz`
  (`D_z^jD_θ^i (Pz f) = D_z^jD_θ^i f − c·D_z^jD_θ^i bump` on the open quadrant);
* `thetaUnif_Pz_Jeps` and **`tauTraces_Pz_Jeps_of_thetaUnif`** — the composition with the
  mollifier (`ThetaUnifJeps`), i.e. the pointwise angular half `TauTraces` of the *projected
  mollified* profile from the uniform angular flatness of the raw profile.  This is the leg that
  the class-`C` invariance of the local step needs: the pointwise `TauTraces` of a raw profile does
  *not* transfer through `J_ε` (the travelling-spike counterexample of
  `EpsEngine/NOTES_HtrUnused.md` §4 — it is the *rate*, not the limit, that is lost), so the
  uniform form is the only route.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EpsEngine.ThetaUnifInterval
import Submission.Work.FTS.EpsEngine.ThetaUnifJeps
import Submission.Work.FTS.EpsEngine.ThetaUnifAdd
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Shorthand for the open quadrant of the `(z,θ)`-plane. -/
private abbrev Qu : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-! ## `ThetaUnif` of the bump -/

/-- **The bump is uniformly flat at both angular ends.**  `bump` vanishes on the half-planes
`θ < π/4` and `3π/8 < θ`, and so do all its mixed derivatives
(`StrongEps.bump_iter_eq_zero_of_not_mem`); there the flatness expression is identically `0`. -/
theorem thetaUnif_bump {α : ℝ} {k : ℕ} :
    ThetaUnif α k (Work.FTS.StrongEps.bump) := by
  have hzero : ∀ {θ : ℝ}, (θ < Real.pi / 4 ∨ 3 * Real.pi / 8 < θ) → ∀ z : ℝ, ∀ a b : ℕ,
      Work.Spaces.mixed b a Work.FTS.StrongEps.bump z θ = 0 := by
    intro θ hθ z a b
    exact Work.FTS.StrongEps.bump_iter_eq_zero_of_not_mem (Or.inr (Or.inr hθ)) b a
  have hsq : Real.sin (2 * (0 : ℝ)) ^ (1 - Work.Spaces.gam α) * (0 : ℝ) ^ 2 = 0 := by ring
  constructor
  · intro a b hab ε' hε'
    refine ⟨Real.pi / 4, by linarith [Real.pi_pos], fun θ hθ0 hθδ z hz => ?_⟩
    rw [hzero (Or.inl hθδ) z a b]
    rw [show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (0 : ℝ) ^ 2 = 0 by ring]
    exact hε'.le
  · intro a b hab ε' hε'
    refine ⟨Real.pi / 8, by linarith [Real.pi_pos], fun θ hθ2 hθδ z hz => ?_⟩
    rw [hzero (Or.inr (by linarith : 3 * Real.pi / 8 < θ)) z a b]
    rw [show Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (0 : ℝ) ^ 2 = 0 by ring]
    exact hε'.le

/-- The smoothness data of the bump in the form used by `ThetaUnifAdd`. -/
theorem bump_contDiffOn : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.bump))
    Qu :=
  (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp Work.FTS.StrongEps.smoothOpen_bump

/-! ## Closure of `ThetaUnif` under the elementary algebraic operations -/

/-- The `θ`-only arithmetic of the scalar multiple: `c²·(ε'/(c²+1)) ≤ ε'`. -/
private theorem const_mul_tol {c ε' : ℝ} (hε' : 0 < ε') :
    c ^ 2 * (ε' / (c ^ 2 + 1)) ≤ ε' := by
  rw [mul_div_assoc']
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < c ^ 2 + 1)]
  nlinarith [sq_nonneg c, hε'.le]

/-- **`ThetaUnif` is closed under scalar multiplication** (the `mixed`-operators are homogeneous,
unconditionally: `StrongEps.mixed_const_mul`). -/
theorem thetaUnif_const_mul {α : ℝ} {k : ℕ} {f : Fn} (c : ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Qu)
    (hf : ThetaUnif α k f) :
    ThetaUnif α k (fun z θ => c * f z θ) := by
  -- the two-sided normalised form of the hypothesis
  have htwo : ∀ (a b : ℕ), a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ,
      (0 < θ ∧ θ < δ) ∨ (θ < Real.pi / 2 ∧ Real.pi / 2 - δ < θ) → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε' := by
    intro a b hab ε' hε'
    obtain ⟨δ0, hδ0, hp0⟩ := hf.t0 a b hab ε' hε'
    obtain ⟨δ1, hδ1, hp1⟩ := hf.t1 a b hab ε' hε'
    refine ⟨min (min δ0 δ1) (Real.pi / 2),
      lt_min (lt_min hδ0 hδ1) (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθ z hz
    rcases hθ with ⟨h1, h2⟩ | ⟨h2, h3⟩
    · exact hp0 θ h1 (lt_of_lt_of_le h2 (le_trans (min_le_left _ _) (min_le_left _ _))) z hz
    · refine hp1 θ h2 ?_ z hz
      have hle : min (min δ0 δ1) (Real.pi / 2) ≤ δ1 :=
        le_trans (min_le_left (min δ0 δ1) (Real.pi / 2)) (min_le_right δ0 δ1)
      linarith
  have key : ∀ (a b : ℕ), a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ,
      (0 < θ ∧ θ < δ) ∨ (θ < Real.pi / 2 ∧ Real.pi / 2 - δ < θ) → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed b a (fun z θ => c * f z θ) z θ) ^ 2 ≤ ε' := by
    intro a b hab ε' hε'
    obtain ⟨δ, hδ, hp⟩ := htwo a b hab (ε' / (c ^ 2 + 1)) (by positivity)
    refine ⟨min δ (Real.pi / 2), lt_min hδ (by linarith [Real.pi_pos]), ?_⟩
    intro θ hθ z hz
    have hθq : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      rcases hθ with ⟨h1, h2⟩ | ⟨h2, h3⟩
      · exact ⟨h1, lt_of_lt_of_le h2 (min_le_right _ _)⟩
      · exact ⟨by linarith [min_le_right δ (Real.pi / 2), Real.pi_pos], h2⟩
    have hθ' : (0 < θ ∧ θ < δ) ∨ (θ < Real.pi / 2 ∧ Real.pi / 2 - δ < θ) := by
      rcases hθ with ⟨h1, h2⟩ | ⟨h2, h3⟩
      · exact Or.inl ⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩
      · exact Or.inr ⟨h2, by
          have hle : min δ (Real.pi / 2) ≤ δ := min_le_left δ (Real.pi / 2)
          linarith⟩
    rw [Work.FTS.StrongEps.mixed_const_mul (j := b) (i := a) c hsm hz hθq]
    have hmul : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (c * Work.Spaces.mixed b a f z θ) ^ 2
        = c ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (Work.Spaces.mixed b a f z θ) ^ 2) := by ring
    rw [hmul]
    exact le_trans (mul_le_mul_of_nonneg_left (hp θ hθ' z hz) (sq_nonneg c)) (const_mul_tol hε')
  refine ⟨fun a b hab ε' hε' => ?_, fun a b hab ε' hε' => ?_⟩
  · obtain ⟨δ, hδ, hp⟩ := key a b hab ε' hε'
    exact ⟨δ, hδ, fun θ hθ0 hθδ z hz => hp θ (Or.inl ⟨hθ0, hθδ⟩) z hz⟩
  · obtain ⟨δ, hδ, hp⟩ := key a b hab ε' hε'
    exact ⟨δ, hδ, fun θ hθ2 hθδ z hz => hp θ (Or.inr ⟨hθ2, hθδ⟩) z hz⟩

/-- **`ThetaUnif` is closed under negation.** -/
theorem thetaUnif_neg {α : ℝ} {k : ℕ} {f : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Qu)
    (hf : ThetaUnif α k f) : ThetaUnif α k (fun z θ => -f z θ) := by
  have h := thetaUnif_const_mul (α := α) (k := k) (f := f) (-1) hsm hf
  have hfun : (fun z θ => (-1 : ℝ) * f z θ) = (fun z θ => -f z θ) := by
    funext z θ; ring
  rwa [hfun] at h

/-- **`ThetaUnif` is closed under subtraction** of profiles smooth on the open quadrant. -/
theorem thetaUnif_sub {α : ℝ} {k : ℕ} {f g : Fn}
    (hfsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Qu)
    (hgsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Qu)
    (hf : ThetaUnif α k f) (hg : ThetaUnif α k g) :
    ThetaUnif α k (fun z θ => f z θ - g z θ) := by
  have hneg := thetaUnif_neg (α := α) (k := k) (f := g) hgsm hg
  have hsum := ThetaUnifAdd (α := α) (k := k) (f := f) (g := fun z θ => -g z θ)
    hfsm (fun n => (hgsm n).neg) hf hneg
  have hfun : (fun z θ => f z θ + -g z θ) = (fun z θ => f z θ - g z θ) := by
    funext z θ; ring
  rwa [hfun] at hsum

/-! ## `ThetaUnif` of the projection, and of the projected mollified profile -/

/-- **`ThetaUnif` passes to the projection `Pz`.**  `Pz f = f − c • bump`; both summands are
uniformly flat (`hf`, and `thetaUnif_bump` scaled). -/
theorem thetaUnif_Pz {α : ℝ} {k : ℕ} {f : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Qu)
    (hf : ThetaUnif α k f) : ThetaUnif α k (Work.FTS.StrongEps.Pz f) := by
  have hcsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm
        * Work.FTS.StrongEps.bump z θ)) Qu :=
    fun n => contDiffOn_const.mul (bump_contDiffOn n)
  have hsub := thetaUnif_sub (α := α) (k := k) (f := f)
    (g := fun z θ => Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm
      * Work.FTS.StrongEps.bump z θ) hsm hcsm hf
    (thetaUnif_const_mul _ bump_contDiffOn thetaUnif_bump)
  have hfun : (fun z θ => f z θ - Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm
      * Work.FTS.StrongEps.bump z θ) = Work.FTS.StrongEps.Pz f := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
  rwa [hfun] at hsub

/-- **The smoothness data of the projected mollified profile.** -/
theorem contDiffOn_Pz_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {f : Fn} (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Qu) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.StrongEps.Pz
      (Work.FTS.StrongEps.Jeps ρ ε f))) Qu := by
  have hJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / Work.FTS.StrongEps.pzNorm
        * Work.FTS.StrongEps.bump z θ) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr
      (fun n => contDiffOn_const.mul (bump_contDiffOn n))
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.StrongEps.Jeps ρ ε f z θ
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / Work.FTS.StrongEps.pzNorm
          * Work.FTS.StrongEps.bump z θ) :=
    hJ.sub h1
  have hfun : (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ
      - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / Work.FTS.StrongEps.pzNorm
        * Work.FTS.StrongEps.bump z θ) = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f) := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply]
  rw [hfun] at h2
  exact (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h2

/-- **`ThetaUnif` of the projected mollified profile.**  The mollifier preserves the uniform
angular flatness (`ThetaUnifJeps`), the projection too (`thetaUnif_Pz`). -/
theorem thetaUnif_Pz_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Qu)
    (hf : ThetaUnif α k f) :
    ThetaUnif α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)) :=
  thetaUnif_Pz
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm))
    (ThetaUnifJeps hρ hα hε hsm hf)

/-- **The angular half of the boundary traces of the projected mollified profile, from the uniform
angular flatness of the raw profile.**  This is the leg consumed by the class-`C` invariance of the
local step. -/
theorem tauTraces_Pz_Jeps_of_thetaUnif {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Qu)
    (hf : ThetaUnif α k f) :
    TauTraces α k (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)) :=
  (thetaUnif_Pz_Jeps hρ hα hε hsm hf).tauTraces

end Work.FTS.EpsEngine
