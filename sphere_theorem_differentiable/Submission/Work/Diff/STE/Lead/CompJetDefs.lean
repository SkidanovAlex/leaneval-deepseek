import Mathlib
import Submission.Work.Diff.STE.Lead.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the jet chain rule `pdW_comp_jet`

This file collects the small pieces of linear algebra and calculus on which the proof of
`Work.Diff.STE.Lead.pdW_comp_jet` rests:

* `restrIdx` — the embedding of the words of length `≤ k` into the words of length `≤ m` for
  `k ≤ m`, and its compatibility with the jet tower `compTower` (`compTower_restrIdx`);
* `frameLin` — the linear form `v ↦ ∑ c, v c • J c`, the derivative of a word derivative in the
  coordinate frame, with `fderiv_eq_frameLin` and `fderiv_pdW_eq`;
* `contDiffOn_pdW` — a word derivative of a smooth function is smooth;
* `towerScan` — the linear map `v ↦ (i ↦ ∑ c, v c • J (ishift c i))`, the derivative of the jet
  tower map, with `towerScan_apply` and `towerScan_single`.

The names here are deliberately distinct from the helpers of
`Submission/Work/Diff/STE/Lead/contDiffOn_of_solves_jet.lean` (`bLin`, `fderiv_pdW`, …), which
declares the same kind of auxiliary lemmas: that file imports this one, so the names must not
clash.
-/

open scoped ContDiff BigOperators
open Set Filter

namespace Work.Diff.STE.Lead

variable {n : ℕ}

/-! ## Restriction of words to a longer allowed length -/

/-- The words of length `≤ k` are words of length `≤ m` when `k ≤ m`. -/
def restrWds {k m : ℕ} (h : k ≤ m) (w : Wds n k) : Wds n m :=
  ⟨⟨w.1.val, Nat.lt_succ_of_le (le_trans (Nat.lt_succ_iff.mp w.1.2) h)⟩, w.2⟩

/-- The corresponding restriction of tower indices. -/
def restrIdx {k m : ℕ} (h : k ≤ m) (i : Idx n k) : Idx n m := (i.1, restrWds h i.2)

/-- The jet tower of order `m` restricts to the jet tower of order `k ≤ m`. -/
@[simp] lemma compTower_restrIdx {u : Modl n → Mtrx n} {k m : ℕ} (h : k ≤ m)
    (i : Idx n k) (y : Modl n) :
    compTower u m y (restrIdx h i) = compTower u k y i := rfl

/-! ## The derivative of a word derivative in the coordinate frame -/

/-- The linear form `v ↦ ∑ c, v c • J c` on the model space. -/
noncomputable def frameLin (J : Fin n → ℂ) : Modl n →L[ℝ] ℂ :=
  ∑ c : Fin n, (ContinuousLinearMap.proj c : Modl n →L[ℝ] ℝ).smulRight (J c)

@[simp] lemma frameLin_apply (J : Fin n → ℂ) (v : Modl n) :
    frameLin J v = ∑ c, v c • J c := by
  simp [frameLin]

/-- The expansion of a vector in the coordinate frame. -/
lemma sum_single_eq_self (v : Modl n) :
    ∑ c : Fin n, v c • (Pi.single c (1 : ℝ) : Modl n) = v := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne (Ne.symm hb)]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The derivative of a `ℂ`-valued function in terms of its values on the coordinate frame.  No
differentiability hypothesis is needed: `fderiv` is always a continuous linear map, and the
coordinate vectors form a basis. -/
lemma fderiv_eq_frameLin (g : Modl n → ℂ) (y : Modl n) :
    fderiv ℝ g y = frameLin (fun c => fderiv ℝ g y (Pi.single c 1)) := by
  ext v
  have h1 : fderiv ℝ g y v =
      fderiv ℝ g y (∑ c : Fin n, v c • (Pi.single c (1 : ℝ) : Modl n)) := by
    rw [sum_single_eq_self]
  rw [h1, map_sum, frameLin_apply]
  simp

/-- The derivative of a word derivative is the sum of the next word derivatives.  Again
unconditional: this is the *definition* of the word derivatives. -/
lemma fderiv_pdW_eq (f : Modl n → ℂ) (y : Modl n) (j : ℕ) (w : Fin j → Fin n) :
    fderiv ℝ (pdW f j w) y = frameLin (fun c => pdW f (j + 1) (Fin.cons c w) y) := by
  rw [fderiv_eq_frameLin]
  exact congrArg frameLin (funext fun c => (congrFun (pdW_succ_cons f j c w) y).symm)

/-- A word derivative of a smooth function is smooth.

Note the level `(⊤ : ℕ∞)`: the order slot of `ContDiff` is `WithTop ℕ∞`, so a *bare* `⊤` there
means `ω` (analytic), not `∞` (smooth).  All the statements in this file are at the smooth
level. -/
lemma contDiffOn_pdW {Ω : Set (Modl n)} (hΩ : IsOpen Ω) {f : Modl n → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (j : ℕ) (w : Fin j → Fin n) :
    ContDiffOn ℝ (⊤ : ℕ∞) (pdW f j w) Ω := by
  induction j with
  | zero => simpa using hf
  | succ j ih =>
    rw [pdW_succ]
    exact (ih (Fin.tail w)).fderiv_of_isOpen hΩ (by simp) |>.clm_apply contDiffOn_const

/-- **The derivative of a word derivative**: the `j`-th word derivative of a smooth function has
derivative the linear combination of its `(j+1)`-st word derivatives. -/
lemma pdW_hasFDerivAt {Ω : Set (Modl n)} (hΩ : IsOpen Ω) {f : Modl n → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) {y : Modl n} (hy : y ∈ Ω) (j : ℕ) (w : Fin j → Fin n) :
    HasFDerivAt (pdW f j w) (frameLin (fun c => pdW f (j + 1) (Fin.cons c w) y)) y := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (pdW f j w) Ω := contDiffOn_pdW hΩ hf j w
  have h2 : ContDiffAt ℝ (1 : ℕ∞) (pdW f j w) y :=
    (h1.contDiffAt (hΩ.mem_nhds hy)).of_le (by simp)
  have hd : DifferentiableAt ℝ (pdW f j w) y := h2.differentiableAt (by norm_num)
  have h3 := hd.hasFDerivAt
  rwa [fderiv_pdW_eq f y j w] at h3

/-! ## The derivative of the jet tower -/

/-- The linear map underlying the derivative of the jet tower: the `i`-th component of
`v ↦ (i ↦ ∑ c, v c • J (ishift c i))` is the `(m+1)`-component of `J` on the shifted index. -/
noncomputable def towerScan (m : ℕ) (J : Idx n (m+1) → ℂ) : Modl n →L[ℝ] (Idx n m → ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ c : Fin n,
    (ContinuousLinearMap.proj c : Modl n →L[ℝ] ℝ).smulRight (J (ishift c i))

lemma towerScan_apply (m : ℕ) (J : Idx n (m+1) → ℂ) (v : Modl n) (i : Idx n m) :
    towerScan m J v i = ∑ c, v c • J (ishift c i) := by
  rw [towerScan, ContinuousLinearMap.pi_apply]
  exact frameLin_apply _ _

/-- Evaluating the tower scan on a basis direction singles out the shifted component. -/
lemma towerScan_single (m : ℕ) (J : Idx n (m+1) → ℂ) (c : Fin n) :
    towerScan m J (Pi.single c 1) = fun i => J (ishift c i) := by
  funext i
  rw [towerScan_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The jet replacement of the induction step of `pdW_comp_jet`: the `(m+1)`-st tower is plugged
into the derivative of `Ψ` along the direction `Pi.single c 1`. -/
noncomputable def jetReplace (m : ℕ) (Ψ : Modl n × (Idx n m → ℂ) → ℂ) (c : Fin n) :
    Modl n × (Idx n (m+1) → ℂ) → ℂ :=
  fun p => fderiv ℝ Ψ (p.1, fun i => p.2 (restrIdx (Nat.le_succ m) i))
    (Pi.single c 1, fun i => p.2 (ishift c i))

/-- The value of the jet replacement on a genuine jet tower. -/
@[simp] lemma jetReplace_apply (m : ℕ) (Ψ : Modl n × (Idx n m → ℂ) → ℂ) (c : Fin n)
    (y : Modl n) (J : Idx n (m+1) → ℂ) :
    jetReplace m Ψ c (y, J) =
      fderiv ℝ Ψ (y, fun i => J (restrIdx (Nat.le_succ m) i))
        (Pi.single c 1, fun i => J (ishift c i)) := rfl

end Work.Diff.STE.Lead
