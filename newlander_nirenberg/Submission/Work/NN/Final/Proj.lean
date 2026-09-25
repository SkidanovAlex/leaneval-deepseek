/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Calderón–Zygmund projection `Π₀ = 1 - T₂∂̄₀` and the derived estimates

Given `FlatTwo n α ρ` (the flat `(0,2)`-Poincaré operator on nested polydiscs), the projection

  `proj F h = h - F.T2 (∂̄₀ h)`

maps any `(0,1)`-form which is smooth on `pd n ρ 4` to a form which is `∂̄₀`-*closed* on `pd n ρ 2`;
this (`proj_closed`) is what allows `T1` to be applied to `proj F (g - L_A w)` in the fixed-point
argument.  We also record the difference estimates for `T1`/`T2` (immediate consequences of
linearity and the `k = 0` estimates of the interface), and the subtraction lemmas for the
coefficient operators `∂̄`.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.TelAux
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

open Work.CR.Flat

variable {n : ℕ}

/-! ## Subtracting the coefficient operators -/

/-- `dbarCoord` is additive in the function at differentiable points. -/
lemma dbarCoord_sub_diff {u v : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    dbarCoord j (fun y => u y - v y) z = dbarCoord j u z - dbarCoord j v z := by
  have hfd : fderiv ℝ (fun y => u y - v y) z = fderiv ℝ u z - fderiv ℝ v z :=
    fderiv_sub hu hv
  simp only [dbarCoord, hfd, sub_apply]
  ring


/-- `∂̄`-differentiation preserves `C^∞` on an open set. -/
lemma contDiffOn_dbarCoord {u : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => dbarCoord j u z) Ω := by
  have hfd : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z) Ω := hu.fderiv_of_isOpen hΩ le_rfl
  have hfun : (fun z => dbarCoord j u z)
      = fun z => (Work.CR.Flat.Polydisc.dbarCoordPhi j) (fderiv ℝ u z) := by
    funext z
    exact congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp j u) z
  rw [hfun]
  exact ((Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.contDiffOn).comp hfd
    (fun x _ => Set.mem_univ _)

/-- Pointwise form of the definition of the projection. -/
@[simp] lemma proj_apply_fun {ρ : Fin n → ℝ} {α : ℝ} (F : FlatTwo n α ρ)
    (f : Fin n → (Fin n → ℂ) → ℂ) (j : Fin n) :
    (proj F f) j = fun z => f j z
      - F.T2 (fun j l z => ddbar (Work.NN.Core.JstdCn n) f j l z) j z := rfl

/-- `Clos1` is closed under subtraction. -/
lemma Clos1_sub {ρ : Fin n → ℝ} {c : ℝ} {f g : Fin n → (Fin n → ℂ) → ℂ}
    (hf : Clos1 n ρ c f) (hg : Clos1 n ρ c g)
    (hd : ∀ m, ContDiffOn ℝ 1 (f m) (pd n ρ c))
    (hd' : ∀ m, ContDiffOn ℝ 1 (g m) (pd n ρ c)) :
    Clos1 n ρ c (fun j z => f j z - g j z) := by
  intro j l z hz
  have hmem : z ∈ pd n ρ c := hz
  have hget : ∀ (m : Fin n) (u : Fin n → (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ 1 (u m) (pd n ρ c) → DifferentiableAt ℝ (u m) z := fun m u hu =>
    ((hu.contDiffAt ((isOpen_pd ρ c).mem_nhds hmem)).differentiableAt (by simp))
  rw [dbarCoord_sub_diff (hget l f (hd l)) (hget l g (hd' l)) j,
    dbarCoord_sub_diff (hget j f (hd j)) (hget j g (hd' j)) l, hf j l z hz, hg j l z hz]

/-- `Clos1` is the vanishing of `∂̄₀` at the `(0,2)`-level. -/
lemma Clos1_iff_ddbar {ρ : Fin n → ℝ} {c : ℝ} {f : Fin n → (Fin n → ℂ) → ℂ} :
    Clos1 n ρ c f
      ↔ ∀ j l z, z ∈ pd n ρ c → ddbar (Work.NN.Core.JstdCn n) f j l z = 0 := by
  simp only [Clos1, ddbar_std, sub_eq_zero]

/-- **`∂̄₀² = 0` at the level of `(0,1)`-forms**: the `(0,2)`-form `∂̄₀h` is itself closed
(a `(0,3)`-form). -/
lemma clos2_ddbar_std {ρ : Fin n → ℝ} {c : ℝ} {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh : ∀ m, ContDiffOn ℝ 2 (h m) (pd n ρ c)) :
    Clos2 n ρ c (fun j l z => ddbar (Work.NN.Core.JstdCn n) h j l z) := by
  intro j l m z hz
  have hd : ∀ i : Fin n, ContDiffAt ℝ 2 (h i) z := fun i =>
    (hh i).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)
  -- the three terms, expanded
  have e1 : dbarCoord j (fun y => ddbar (Work.NN.Core.JstdCn n) h l m y) z
      = dbarCoord l (dbarCoord j (h m)) z - dbarCoord m (dbarCoord j (h l)) z := by
    simp only [ddbar_std]
    rw [dbarCoord_sub_diff (diffAt_dbarCoord (hd m) l) (diffAt_dbarCoord (hd l) m) j,
      Work.CR.Flat.Polydisc.dbarCoord_comm l j (h m) z (hd m),
      Work.CR.Flat.Polydisc.dbarCoord_comm m j (h l) z (hd l)]
  have e2 : dbarCoord l (fun y => ddbar (Work.NN.Core.JstdCn n) h j m y) z
      = dbarCoord l (dbarCoord j (h m)) z - dbarCoord m (dbarCoord l (h j)) z := by
    simp only [ddbar_std]
    rw [dbarCoord_sub_diff (diffAt_dbarCoord (hd m) j) (diffAt_dbarCoord (hd j) m) l,
      Work.CR.Flat.Polydisc.dbarCoord_comm m l (h j) z (hd j)]
  have e3 : dbarCoord m (fun y => ddbar (Work.NN.Core.JstdCn n) h j l y) z
      = dbarCoord m (dbarCoord j (h l)) z - dbarCoord m (dbarCoord l (h j)) z := by
    simp only [ddbar_std]
    rw [dbarCoord_sub_diff (diffAt_dbarCoord (hd l) j) (diffAt_dbarCoord (hd j) l) m]
  rw [e1, e2, e3]
  ring

/-! ## The projection `Π₀ = 1 - T₂∂̄₀` lands in the `∂̄₀`-closed forms -/

/-- **The projection `Π₀` maps smooth forms to `∂̄₀`-closed forms.**  If `h` is smooth (`C^∞`) on
`pd n ρ 4`, then `proj F h = h - T₂(∂̄₀h)` is `∂̄₀`-closed on `pd n ρ 2`: indeed
`∂̄₀ h - ∂̄₀ T₂(∂̄₀h) = ∂̄₀h - ∂̄₀h = 0` by the solving property of `T₂`. -/
theorem proj_closed {ρ : Fin n → ℝ} {α : ℝ} (F : FlatTwo n α ρ) {h : Fin n → (Fin n → ℂ) → ℂ}
    (hh : ∀ m : Fin n, ContDiffOn ℝ ∞ (h m) (pd n ρ 4)) :
    Clos1 n ρ 2 (proj F h) := by
  set η : Fin n → Fin n → (Fin n → ℂ) → ℂ :=
    fun j l z => ddbar (Work.NN.Core.JstdCn n) h j l z with hη
  have hηsm : ∀ j l, ContDiffOn ℝ ∞ (η j l) (pd n ρ 4) := by
    intro j l
    simp only [hη, ddbar_std]
    exact (contDiffOn_dbarCoord (isOpen_pd ρ 4) (hh l) j).sub
      (contDiffOn_dbarCoord (isOpen_pd ρ 4) (hh j) l)
  have hηanti : ∀ j l : Fin n, ∀ z : Fin n → ℂ, η j l z = - η l j z := by
    intro j l z
    simp only [hη, ddbar_std]
    ring
  have hηcl : Clos2 n ρ 4 η := by
    intro j l m z hz
    simp only [hη]
    exact clos2_ddbar_std (ρ := ρ) (c := 4)
      (fun i => (hh i).of_le (by simp)) j l m z hz
  have hT2 : ∀ j, ContDiffOn ℝ ∞ (F.T2 η j) (pd n ρ 2) := fun j =>
    F.T2_smooth η hηsm hηanti hηcl j
  intro j l z hz
  have hzmem : z ∈ pd n ρ 2 := hz
  -- differentiability at `z` of all four functions involved
  have hdl : DifferentiableAt ℝ (h l) z := ((hh l).contDiffAt
    ((isOpen_pd ρ 4).mem_nhds (pd_two_subset_four F.hρ hzmem))).differentiableAt (by simp)
  have hdj : DifferentiableAt ℝ (h j) z := ((hh j).contDiffAt
    ((isOpen_pd ρ 4).mem_nhds (pd_two_subset_four F.hρ hzmem))).differentiableAt (by simp)
  have htl : DifferentiableAt ℝ (F.T2 η l) z :=
    ((hT2 l).contDiffAt ((isOpen_pd ρ 2).mem_nhds hzmem)).differentiableAt (by simp)
  have htj : DifferentiableAt ℝ (F.T2 η j) z :=
    ((hT2 j).contDiffAt ((isOpen_pd ρ 2).mem_nhds hzmem)).differentiableAt (by simp)
  have hpt : ∀ m, (proj F h) m = (fun y => h m y) - F.T2 η m := by
    intro m
    rw [proj_apply_fun]
    rfl
  have e1 : dbarCoord j ((proj F h) l) z
      = dbarCoord j (h l) z - dbarCoord j (F.T2 η l) z := by
    rw [hpt l]
    exact dbarCoord_sub_diff hdl htl j
  have e2 : dbarCoord l ((proj F h) j) z
      = dbarCoord l (h j) z - dbarCoord l (F.T2 η j) z := by
    rw [hpt j]
    exact dbarCoord_sub_diff hdj htj l
  rw [e1, e2]
  have hsol := F.T2_solves η (fun j l => (hηsm j l).of_le (by simp))
    hηanti hηcl j l z hzmem
  have hηdef : η j l z = dbarCoord j (h l) z - dbarCoord l (h j) z := by
    simp only [hη, ddbar_std]
  have hAB : dbarCoord j (h l) z - dbarCoord l (h j) z
      = dbarCoord j (F.T2 η l) z - dbarCoord l (F.T2 η j) z := hηdef.symm.trans hsol.symm
  linear_combination hAB

end Work.NN.Final
