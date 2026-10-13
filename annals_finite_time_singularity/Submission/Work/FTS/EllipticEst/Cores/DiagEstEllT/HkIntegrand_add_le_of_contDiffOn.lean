/-
Copyright: work module for the Elgindi finite-time singularity project.

# Subadditivity of the `ℋ^k`-integrand for data smooth to *finite* order

`Work.FTS.EllipticEst.HkIntegrand_add_le_open` proves

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`

on `Iz ×ˢ Iθ` for `f, g` of class `SmoothOpen`, i.e. `C^∞` on the open quadrant.  Its proof uses
the additivity of the iterated operators `D_z^i`, `D_z^j D_θ^i` on the open quadrant, which the
workspace API (`SmoothOpenAdd`) provides for `C^∞` data.

The *honest* (finite-smoothness) data of the trace-free classes have only finitely many orders of
smoothness: e.g. for the straightening `V = Ψ + Gsing α F · sin 2θ` of Theorem `RemovingL12`, the
two summands `Ψ` and `Gsing α F·sin 2θ` are `C^∞` and `C^{k+1}` respectively.  Only the indices
`i ≤ k` and `i + j ≤ k` occur in `HkIntegrand α k`, so the finite-order hypothesis
`ContDiffOn ℝ k (uncurry ·) Q0` on each summand suffices; this module records that form.

The finite-order regularity toolkit used is `Work.FTS.EllipticEst.RegQ.Q2`:
`contDiffOn_DzIter_fin`, `contDiffOn_DthIter_fin`, `contDiffOn_slice_z_fin`,
`contDiffOn_slice_θ_fin`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.EllipticEst.HkIntegrand_add_le_open
import Submission.Work.FTS.EllipticEst.RegQ.pthU_slot_alg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.DiagEstEllT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The algebraic core -/

private lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ## Finite-order additivity of the iterated operators on the open quadrant -/

/-- The `z`-slice of a function that is `C^m` on the open quadrant is differentiable in `z`. -/
lemma differentiableAt_zslice {G : ℝ → ℝ → ℝ} {m : ℕ}
    (hG : ContDiffOn ℝ m (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hm : 1 ≤ m)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    DifferentiableAt ℝ (fun z' => G z' θ) z := by
  have hslice : ContDiffOn ℝ m (fun z' => G z' θ) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_z_fin
      (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) hG ⟨h1, h2⟩
  have h1' : ContDiffOn ℝ 1 (fun z' => G z' θ) (Set.Ioi 0) :=
    hslice.of_le (by exact_mod_cast hm)
  exact (h1'.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by simp)

/-- The `θ`-slice of a function that is `C^m` on the open quadrant is differentiable in `θ`. -/
lemma differentiableAt_thslice {G : ℝ → ℝ → ℝ} {m : ℕ}
    (hG : ContDiffOn ℝ m (Function.uncurry G) Work.FTS.EllipticEst.Q0) (hm : 1 ≤ m)
    {z θ : ℝ} (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < π / 2) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ := by
  have hslice : ContDiffOn ℝ m (fun θ' => G z θ') (Set.Ioo 0 (π / 2)) :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_slice_θ_fin
      (s := Set.Ioi 0) (t := Set.Ioo 0 (π / 2)) hG hz
  have h1' : ContDiffOn ℝ 1 (fun θ' => G z θ') (Set.Ioo 0 (π / 2)) :=
    hslice.of_le (by exact_mod_cast hm)
  exact (h1'.contDiffAt (isOpen_Ioo.mem_nhds ⟨h1, h2⟩)).differentiableAt (by simp)

/-- **Additivity of the iterated operator `D_z^j`** for data that are `C^m` on the open
quadrant, at orders `j ≤ m`. -/
theorem DzIter_add_fin {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ j ≤ m, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  intro j
  induction j with
  | zero => intro _ z θ _ _ _; rfl
  | succ n ih =>
      intro hn z θ hz h1 h2
      have hn' : n ≤ m := by omega
      have hlt : n < m := by omega
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter n f z' θ + Work.Spaces.DzIter n g z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih hn' z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        differentiableAt_zslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hf n hn')
          (by omega) hz h1 h2
      have hd2 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n g z' θ) z :=
        differentiableAt_zslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DzIter_fin isOpen_Q0 hg n hn')
          (by omega) hz h1 h2
      have hd : deriv (fun z' => Work.Spaces.DzIter n f z' θ
            + Work.Spaces.DzIter n g z' θ) z
          = deriv (fun z' => Work.Spaces.DzIter n f z' θ) z
            + deriv (fun z' => Work.Spaces.DzIter n g z' θ) z := deriv_add hd1 hd2
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]
      ring

/-- **Additivity of the iterated operator `D_θ^i`** for data that are `C^m` on the open
quadrant, at orders `i ≤ m`. -/
theorem DthIter_add_fin {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ i ≤ m, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.DthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  intro i
  induction i with
  | zero => intro _ z θ _ _ _; rfl
  | succ n ih =>
      intro hn z θ hz h1 h2
      have hn' : n ≤ m := by omega
      have hlt : n < m := by omega
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => f z θ + g z θ) z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n f z θ' + Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)] with θ' hθ'
        exact ih hn' z θ' hz hθ'.1 hθ'.2
      have hd1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        differentiableAt_thslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hf n hn')
          (by omega) hz h1 h2
      have hd2 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n g z θ') θ :=
        differentiableAt_thslice
          (Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hg n hn')
          (by omega) hz h1 h2
      have hd : deriv (fun θ' => Work.Spaces.DthIter n f z θ'
            + Work.Spaces.DthIter n g z θ') θ
          = deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ
            + deriv (fun θ' => Work.Spaces.DthIter n g z θ') θ := deriv_add hd1 hd2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq, hd]
      ring

/-- **Additivity of the mixed operators `D_z^j D_θ^i`** for data that are `C^m` on the open
quadrant, at orders `i + j ≤ m`. -/
theorem mixed_add_fin {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ j i, i + j ≤ m → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  intro j i hij z θ hz h1 h2
  have hi : i ≤ m := by omega
  have hcongr := Work.FTS.EllipticEst.SmoothOpen.DzIter_congr (j := j)
    (F := Work.Spaces.DthIter i (fun z θ => f z θ + g z θ))
    (G := fun z θ => Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ)
    (fun z θ hz' h1' h2' => DthIter_add_fin hf hg i hi z θ hz' h1' h2') z θ hz h1 h2
  have hf' : ContDiffOn ℝ (m - i) (Function.uncurry (Work.Spaces.DthIter i f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hf i hi
  have hg' : ContDiffOn ℝ (m - i) (Function.uncurry (Work.Spaces.DthIter i g))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_DthIter_fin isOpen_Q0 hg i hi
  have hadd := DzIter_add_fin hf' hg' j (by omega) z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact hcongr.trans hadd

/-! ## The pointwise inequality -/

/-- The pointwise inequality for the integrand, given the additivity of the iterated operators
at `(z, θ)` for the indices that occur in `HkIntegrand α k`. -/
private lemma HkIntegrand_add_le_pt_fin (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i ≤ k, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ j i, i + j ≤ k → Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hij : p.1 + p.2 ≤ k := (Finset.mem_filter.mp hp).2.2
      rw [hm p.2 p.1 hij]
      ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-! ## The theorem -/

/-- **Subadditivity of the `ℋ^k`-integrand for data smooth to order `k`.**  For `f`, `g` of
class `C^k` on the open quadrant and `(z,θ)` in the open quadrant,

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`.

This is the honest (finite-smoothness) form of `HkIntegrand_add_le_open`, which is what the
straightened datum `Ψ + Gsing α F · sin 2θ` of Theorem `RemovingL12` can be fed. -/
theorem HkIntegrand_add_le_of_contDiffOn (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z θ hz h1 h2
  exact HkIntegrand_add_le_pt_fin α k f g z θ
    (fun i hi => DzIter_add_fin hf hg i hi z θ hz h1 h2)
    (fun j i hij => mixed_add_fin hf hg j i hij z θ hz h1 h2)


/-! ## Additivity of `∂_θ` and of its iterates, on the open quadrant -/

/-- **`pthIter` drops `l` orders of differentiability.** -/
theorem contDiffOn_pthIter_fin {G : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {m : ℕ}
    (h : ContDiffOn ℝ m (Function.uncurry G) U) :
    ∀ l ≤ m, ContDiffOn ℝ (m - l : ℕ) (Function.uncurry (Work.Spaces.pthIter l G)) U := by
  intro l
  induction l with
  | zero => intro _; simpa using h
  | succ l ih =>
      intro hl
      have hl' : l ≤ m := by omega
      have h1 : ContDiffOn ℝ (m - l : ℕ) (Function.uncurry (Work.Spaces.pthIter l G)) U := ih hl'
      have h2 : ContDiffOn ℝ (m - l - 1 + 1 : ℕ)
          (Function.uncurry (Work.Spaces.pthIter l G)) U := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ m - l)]; exact h1
      have h3 : ContDiffOn ℝ (m - l - 1 : ℕ)
          (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter l G))) U :=
        Work.FTS.EllipticEst.RegQ.Q2.contDiffOn_pth_fin hU h2
      have heq : m - (l + 1) = m - l - 1 := by omega
      rw [heq, Work.Spaces.pthIter_succ]
      exact h3

/-- **`pth` is additive on `Q0`** for data that are `C^1` in `θ` there (the totalised `deriv` is
additive at points where both slices are differentiable). -/
theorem pth_add_on_Q0 {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) (hm : 1 ≤ m) :
    ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hdf : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    differentiableAt_thslice hf hm hz h1 h2
  have hdg : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    differentiableAt_thslice hg hm hz h1 h2
  show deriv (fun θ' => (fun z θ => f z θ + g z θ) z θ') θ = _
  rw [show (fun θ' => (fun z θ => f z θ + g z θ) z θ') = fun θ' => f z θ' + g z θ' from rfl]
  exact deriv_add hdf hdg

/-- **`pthIter i` is additive on `Q0`** (`1 ≤ i ≤ m`) for data that are `C^m` in `θ` there. -/
theorem pthIter_add_on_Q0 {f g : ℝ → ℝ → ℝ} {m : ℕ}
    (hf : ContDiffOn ℝ m (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ m (Function.uncurry g) Work.FTS.EllipticEst.Q0) :
    ∀ i, 1 ≤ i → i ≤ m → ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pthIter i (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pthIter i f z θ + Work.Spaces.pthIter i g z θ := by
  intro i
  induction i with
  | zero => intro h1 _; exact absurd h1 (by omega)
  | succ n ih =>
      intro _ hn z θ hz h1 h2
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simpa using pth_add_on_Q0 hf hg (by omega) z θ hz h1 h2
      · have hnle : n ≤ m := by omega
        have hfn : ContDiffOn ℝ (m - n : ℕ) (Function.uncurry (Work.Spaces.pthIter n f))
            Work.FTS.EllipticEst.Q0 := contDiffOn_pthIter_fin isOpen_Q0 hf n hnle
        have hgn : ContDiffOn ℝ (m - n : ℕ) (Function.uncurry (Work.Spaces.pthIter n g))
            Work.FTS.EllipticEst.Q0 := contDiffOn_pthIter_fin isOpen_Q0 hg n hnle
        have hev : (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ')
            =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pthIter n f z θ'
              + Work.Spaces.pthIter n g z θ') := by
          filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (π / 2) from ⟨h1, h2⟩)]
            with θ' hθ'
          exact ih hnpos hnle z θ' hz hθ'.1 hθ'.2
        show deriv (fun θ' => Work.Spaces.pthIter n (fun z θ => f z θ + g z θ) z θ') θ
            = deriv (fun θ' => Work.Spaces.pthIter n f z θ') θ
              + deriv (fun θ' => Work.Spaces.pthIter n g z θ') θ
        rw [hev.deriv_eq]
        simpa only [Work.Spaces.pth] using pth_add_on_Q0 hfn hgn (by omega) z θ hz h1 h2

end Work.FTS.EllipticEst.Cores.DiagEstEllT
