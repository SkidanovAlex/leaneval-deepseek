import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le
import Submission.Work.Diff.STE.garding_base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet vocabulary of the composition bound `gardCompBound`

The target `Work.Diff.STE.Lead.Gal.gardCompBound` bounds the iterated partial derivatives
`pdVec m β (z ↦ Φ z (u z) (∂u z))` of the composition of a smooth function `Φ` of the value and
the first jet of `u`, uniformly over all `u` whose value and first jet stay in a fixed compact
region of the domain `{det ≠ 0}` of `Φ`.

The compact region is the set `JetSet n lam KG R`: the point `z` in the closed ball of radius `R`,
the matrix `u z` positive definite with constant `lam`, and all entries of `u z` (resp. of `∂u z`)
bounded by `KG`.  This file defines it and records the two structural facts:

* `JetSet n lam KG R` is compact (closed and bounded);
* it is contained in `{det ≠ 0}` (a positive definite matrix is nonsingular), so that `Φ` is
  smooth on an open neighbourhood of it;
* the jet `(z, u z, ∂u z)` of an admissible `u` at a point `‖z‖ ≤ R` belongs to it.

The definitions live here (rather than in the target file) so that the auxilliary lemmas of the
target can be stated in this vocabulary and proved in parallel.
-/

namespace Work.Diff.STE.Lead.Gal

open scoped BigOperators

noncomputable section

/-- The jet type of the composition: point, value (matrix), first derivative (three-tensor). -/
abbrev Jet (n : ℕ) : Type :=
  (Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → Fin n → ℝ)

/-- **The compact set of admissible jet values**: the point lies in the closed ball of radius `R`,
the matrix is positive definite with constant `lam`, and all entries of the matrix and of the
three-tensor are bounded by `KG`. -/
def JetSet (n : ℕ) (lam KG R : ℝ) : Set (Jet n) :=
  {w | ‖w.1‖ ≤ R ∧
       (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j) ∧
       (∀ i j : Fin n, |w.2.1 i j| ≤ KG) ∧
       (∀ c i j : Fin n, |w.2.2 c i j| ≤ KG)}

variable {n : ℕ} {lam KG R : ℝ} {k : ℕ}

lemma continuous_fst_mat (i j : Fin n) :
    Continuous (fun w : Jet n => w.2.1 i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp (continuous_fst.comp continuous_snd))

lemma continuous_snd_ten (c i j : Fin n) :
    Continuous (fun w : Jet n => w.2.2 c i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp
    ((continuous_apply c).comp (continuous_snd.comp continuous_snd)))

/-- **The jet set is closed**: all four defining conditions are closed. -/
lemma isClosed_jetSet : IsClosed (JetSet n lam KG R) := by
  have h1 : IsClosed {w : Jet n | ‖w.1‖ ≤ R} :=
    isClosed_le (continuous_norm.comp continuous_fst) continuous_const
  have h2 : IsClosed {w : Jet n | ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j} := by
    rw [show {w : Jet n | ∀ ξ : Fin n → ℝ,
        lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j}
        = ⋂ ξ : Fin n → ℝ, {w : Jet n |
            lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, w.2.1 i j * ξ i * ξ j} from by
      ext w; simp]
    refine isClosed_iInter fun ξ => isClosed_le continuous_const ?_
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_fst_mat i j).mul continuous_const).mul continuous_const
  have h3 : IsClosed {w : Jet n | ∀ i j : Fin n, |w.2.1 i j| ≤ KG} := by
    rw [show {w : Jet n | ∀ i j : Fin n, |w.2.1 i j| ≤ KG}
        = ⋂ i : Fin n, ⋂ j : Fin n, {w : Jet n | |w.2.1 i j| ≤ KG} from by
      ext w; simp]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le ((continuous_fst_mat i j).abs) continuous_const
  have h4 : IsClosed {w : Jet n | ∀ c i j : Fin n, |w.2.2 c i j| ≤ KG} := by
    rw [show {w : Jet n | ∀ c i j : Fin n, |w.2.2 c i j| ≤ KG}
        = ⋂ c : Fin n, ⋂ i : Fin n, ⋂ j : Fin n, {w : Jet n | |w.2.2 c i j| ≤ KG} from by
      ext w; simp]
    exact isClosed_iInter fun c => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le ((continuous_snd_ten c i j).abs) continuous_const
  have h := IsClosed.inter (IsClosed.inter (IsClosed.inter h1 h2) h3) h4
  convert h using 1
  ext w
  simp only [JetSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- **The jet set is bounded** (by `max R KG`, when both are nonnegative). -/
lemma jetSet_subset_closedBall (hR : 0 ≤ R) (hKG : 0 ≤ KG) :
    JetSet n lam KG R ⊆ Metric.closedBall (0 : Jet n) (max R KG) := by
  intro w hw
  obtain ⟨h1, -, h3, h4⟩ := hw
  rw [Metric.mem_closedBall, dist_zero_right]
  have hmat : ‖w.2.1‖ ≤ KG := by
    refine pi_norm_le_iff_of_nonneg hKG |>.mpr fun i => ?_
    refine pi_norm_le_iff_of_nonneg hKG |>.mpr fun j => ?_
    simpa [Real.norm_eq_abs] using h3 i j
  have hten : ‖w.2.2‖ ≤ KG := by
    refine pi_norm_le_iff_of_nonneg hKG |>.mpr fun c => ?_
    refine pi_norm_le_iff_of_nonneg hKG |>.mpr fun i => ?_
    refine pi_norm_le_iff_of_nonneg hKG |>.mpr fun j => ?_
    simpa [Real.norm_eq_abs] using h4 c i j
  calc ‖w‖ = max ‖w.1‖ ‖(w.2.1, w.2.2)‖ := Prod.norm_mk w.1 (w.2.1, w.2.2)
    _ = max ‖w.1‖ (max ‖w.2.1‖ ‖w.2.2‖) := by rw [Prod.norm_mk]
    _ ≤ max R KG := max_le_max h1 (max_le hmat hten)

/-- **The jet set is compact.** -/
lemma isCompact_jetSet (hKG : 0 ≤ KG) : IsCompact (JetSet n lam KG R) := by
  by_cases hR : 0 ≤ R
  · exact (isCompact_closedBall (0 : Jet n) (max R KG)).of_isClosed_subset
      isClosed_jetSet (jetSet_subset_closedBall hR hKG)
  · -- the closed ball of a negative radius is empty
    have hempty : JetSet n lam KG R = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨w, hw⟩
      exact absurd (le_trans (norm_nonneg _) hw.1) hR
    rw [hempty]
    exact isCompact_empty

/-- **A positive definite matrix is nonsingular**, so the jet set lies in the domain of `Φ`. -/
lemma jetSet_subset_det (hlam : 0 < lam) :
    JetSet n lam KG R ⊆ {w : Jet n | (Matrix.of w.2.1).det ≠ 0} := by
  intro w hw
  refine Work.Diff.STE.flat.det_ne_zero_of_quadForm_le (Matrix.of w.2.1) hlam fun v => ?_
  simpa [Matrix.of_apply] using hw.2.1 v

/-- The set of admissible points is a neighbourhood of `z` when `‖z‖ ≤ R`: it is the open ball of
radius `R + 1`. -/
lemma ball_mem_nhds {z : Fin n → ℝ} (hz : ‖z‖ ≤ R) :
    {z' : Fin n → ℝ | ‖z'‖ < R + 1} ∈ nhds z := by
  refine Metric.mem_nhds_iff.mpr ⟨1, by norm_num, ?_⟩
  intro y hy
  simp only [Set.mem_setOf_eq]
  have h2 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
    simpa using norm_add_le (y - z) z
  rw [Metric.mem_ball, dist_eq_norm] at hy
  linarith

/-- `pdVec` of order one along a single direction is `pd`. -/
lemma pdVec_one_eq_pd (c : Fin n)
    (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => c) f = Work.Diff.STE.pd c f := by
  simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]

/-- `pdVec` of order zero is the function itself. -/
lemma pdVec_zero_eq (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 0 (Fin.elim0 : Fin 0 → Fin n) f = f := by
  simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]

/-- **Membership in the jet set.**  The jet `(z, u z, ∂u z)` of an admissible `u` at a point
`z` with `‖z‖ ≤ R` belongs to `JetSet n lam KG R`. -/
theorem mem_jetSet {u : (Fin n → ℝ) → (Fin n → Fin n → ℝ)}
    (hsm : ∀ i j : Fin n, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun z => u z i j)
      {z : Fin n → ℝ | ‖z‖ < R + 1})
    (hpos : ∀ (z : Fin n → ℝ), ‖z‖ ≤ R → ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, u z i j * ξ i * ξ j)
    (hjet : ∀ (m : ℕ) (hm : m ≤ k + 1) (β : Fin m → Fin n) (z : Fin n → ℝ) (i j : Fin n),
      ‖z‖ ≤ R → ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((u y i j : ℝ) : ℂ)) z‖ ≤ KG)
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ R) :
    (z, u z, fun c i j => Work.Diff.STE.pdR c (fun w : Fin n → ℝ => u w i j) z) ∈
      JetSet n lam KG R := by
  refine ⟨hz, hpos z hz, ?_, ?_⟩
  · intro i j
    have h0 := hjet 0 (Nat.zero_le _) (Fin.elim0 : Fin 0 → Fin n) z i j hz
    rw [pdVec_zero_eq] at h0
    simpa using h0
  · intro c i j
    have h1 := hjet 1 (by omega) (fun _ : Fin 1 => c) z i j hz
    rw [pdVec_one_eq_pd c] at h1
    have hd : DifferentiableAt ℝ (fun w : Fin n → ℝ => u w i j) z :=
      ((hsm i j).differentiableOn (by simp)).differentiableAt (ball_mem_nhds hz)
    rw [Work.Diff.STE.ga_pd_ofReal c (fun w : Fin n → ℝ => u w i j) z hd] at h1
    simpa using h1

/-! ## The local bridge `pdVec = iteratedFDeriv` on coordinate tuples

The library lemma `Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv` needs *global* smoothness of `f`
(and is stated for `ι → ℝ`); the functions of the composition bound are only smooth on an open
ball, so we record the version with `ContDiffOn` on an open set. -/

theorem pdVec_eq_iteratedFDeriv_on {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {f : (Fin n → ℝ) → ℂ} (hf : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) f U)
    {x : Fin n → ℝ} (hx : x ∈ U) (m : ℕ) (l : Fin m → Fin n) :
    Work.Diff.STE.pdVec m l f x =
      iteratedFDeriv ℝ m f x (fun j => Pi.single (l j) 1) := by
  have hpd : ∀ (m : ℕ) (l : Fin (m + 1) → Fin n),
      Work.Diff.STE.pdVec (m + 1) l f =
        Work.Diff.STE.pd (l 0) (Work.Diff.STE.pdVec m (Fin.tail l) f) := by
    intro m l
    have h : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
      conv_lhs => rw [← Fin.cons_self_tail l]
      rw [List.ofFn_cons]
    simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
    rw [h, List.foldr_cons]
  have hdiff : ∀ (y : Fin n → ℝ), y ∈ U → ∀ k : ℕ,
      DifferentiableAt ℝ (iteratedFDeriv ℝ k f) y := by
    intro y hy k
    exact ((hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (m := 1) (i := k)
      (by simp)).differentiableAt (by norm_num)
  have key : ∀ (m : ℕ) (x : Fin n → ℝ), x ∈ U → ∀ l : Fin m → Fin n,
      Work.Diff.STE.pdVec m l f x =
        iteratedFDeriv ℝ m f x (fun j => Pi.single (l j) 1) := by
    intro m
    induction m with
    | zero =>
      intro x hx l
      rw [show Work.Diff.STE.pdVec 0 l f = f from by
        simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]]
      exact (iteratedFDeriv_zero_apply (fun j => Pi.single (l j) 1)).symm
    | succ m ih =>
      intro x hx l
      rw [hpd m l]
      have heq : (fun y => Work.Diff.STE.pdVec m (Fin.tail l) f y)
          =ᶠ[nhds x]
            (fun y => iteratedFDeriv ℝ m f y
              (fun j => Pi.single ((Fin.tail l) j) 1)) :=
        Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy (Fin.tail l))
      simp only [Work.Diff.STE.pd]
      rw [heq.fderiv_eq]
      rw [iteratedFDeriv_succ_apply_left]
      rw [fderiv_continuousMultilinear_apply_const (c := fun y => iteratedFDeriv ℝ m f y)
        (x := x) (u := (fun j => Pi.single ((Fin.tail l) j) 1)) (hdiff x hx m)]
      rfl
  exact key m x hx l

end

end Work.Diff.STE.Lead.Gal
