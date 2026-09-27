import Mathlib
import Submission.Work.EKLComp.C8Defs

/-!
# C8/Leaf — (F4): transfer of equality of `ℝ`-valued leafwise measures along `U_01`

If two points `x, x'` of the domain `X'` have the same `ℝ`-valued leafwise measure
(`nuR (ν x) = nuR (ν x')`), then so do their translates `u s • x`, `u s • x'` by the same
element of the root group `U_01`.

The argument is EKL (3) plus normalisation:

* `IsLeafwise.equivariant` at `x` and at `x'` with `u = u s` gives constants `0 < c, c' < ∞`
  with `ν x = c • (ν (u s • x)).map (g ↦ g * u s)` and
  `ν x' = c' • (ν (u s • x')).map (g ↦ g * u s)`.
* Pushing these forward along `nuR = (·.restrict U_01).map par` (using `nuR_smul` and
  `nuR_map_mul_u`, the latter requiring `ν y` to be carried by `U_01`) turns them into
  `nuR (ν x) = c • (nuR (ν (u s • x))).map (t ↦ t + s)` and likewise for `x'`.
* Since `nuR (ν x) = nuR (ν x')`, the two scalar multiples of the shift-pushforwards coincide.
  Both `nuR (ν (u s • x))` and `nuR (ν (u s • x'))` are normalised to `1` on `[-1,1]`
  (`nuR_normalised`), which pins the scalars (`c = c'`) and lets the shift be undone.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract

noncomputable section

namespace Work.EKLCompLeaf

/-- **(F4), measure-theoretic core.**  Suppose a measure `M` on `ℝ` is simultaneously a
scalar multiple of the `s`-translate pushforward of `P` and of that of `P'`, the two scalars
being finite and nonzero, and suppose `P` and `P'` are normalised on `[-1,1]`.  Then
`P = P'`.

Indeed evaluating `M` on the interval `[-1+s, 1+s]`, whose preimage under `t ↦ t + s` is
`[-1,1]`, recovers both scalars from the same number `M [-1+s, 1+s]`, so `c = c'`; then the
affine changes of variable cancel. -/
theorem measure_eq_of_smul_map_add {M P P' : Measure ℝ} {c c' : ℝ≥0∞} {s : ℝ}
    (hc : c ≠ 0) (hcT : c ≠ ⊤) (hc' : c' ≠ 0) (hc'T : c' ≠ ⊤)
    (hP : P (Set.Icc (-1) 1) = 1) (hP' : P' (Set.Icc (-1) 1) = 1)
    (hM : M = c • P.map (fun t => t + s)) (hM' : M = c' • P'.map (fun t => t + s)) :
    P = P' := by
  have hms : Measurable (fun t : ℝ => t + s) := measurable_id.add_const s
  have hms' : Measurable (fun t : ℝ => t - s) := measurable_id.sub_const s
  have hpre : (fun t : ℝ => t + s) ⁻¹' Set.Icc (-1 + s) (1 + s) = Set.Icc (-1) 1 := by
    ext t; simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith
  have hMB : M (Set.Icc (-1 + s) (1 + s)) = c := by
    rw [hM, Measure.smul_apply, Measure.map_apply hms measurableSet_Icc, hpre, hP]
    simp
  have hMB' : M (Set.Icc (-1 + s) (1 + s)) = c' := by
    rw [hM', Measure.smul_apply, Measure.map_apply hms measurableSet_Icc, hpre, hP']
    simp
  have hcc : c = c' := by rw [← hMB, hMB']
  have hPmap : P.map (fun t => t + s) = c⁻¹ • M := by
    rw [hM, smul_smul, ENNReal.inv_mul_cancel hc hcT, one_smul]
  have hPmap' : P'.map (fun t => t + s) = c⁻¹ • M := by
    have h2 : P'.map (fun t => t + s) = c'⁻¹ • M := by
      rw [hM', smul_smul, ENNReal.inv_mul_cancel hc' hc'T, one_smul]
    rw [← hcc] at h2; exact h2
  have hleft : P = c⁻¹ • (M.map (fun t => t - s)) := by
    have h1 : P = (P.map (fun t => t + s)).map (fun t => t - s) := by
      rw [Measure.map_map hms' hms]
      rw [show (fun t : ℝ => t - s) ∘ (fun t : ℝ => t + s) = id by funext t; simp,
        Measure.map_id]
    rw [h1, hPmap, Measure.map_smul] <;> try fun_prop
  have hright : P' = c⁻¹ • (M.map (fun t => t - s)) := by
    have h1 : P' = (P'.map (fun t => t + s)).map (fun t => t - s) := by
      rw [Measure.map_map hms' hms]
      rw [show (fun t : ℝ => t - s) ∘ (fun t : ℝ => t + s) = id by funext t; simp,
        Measure.map_id]
    rw [h1, hPmap', Measure.map_smul] <;> try fun_prop
  rw [hleft, hright]

/-- **(F4).**  Leafwise measures that agree at `x` and `x'` also agree after translating both
points by the same `u(s)` (EKL (3) + normalisation + (8)). -/
theorem equiv_transfer {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij Work.EKLComp.h01) ν X')
    {x x' : Work.EKLContract.X3} (hx : x ∈ X') (hx' : x' ∈ X') (s : ℝ)
    (hux : Work.EKLComp.u s • x ∈ X') (hux' : Work.EKLComp.u s • x' ∈ X')
    (h : Work.EKLComp.nuR (ν x) = Work.EKLComp.nuR (ν x')) :
    Work.EKLComp.nuR (ν (Work.EKLComp.u s • x)) = Work.EKLComp.nuR (ν (Work.EKLComp.u s • x')) := by
  -- (3) at `x` and at `x'`, with the same `u = u s`.
  obtain ⟨c, hc0, hcT, heq⟩ :=
    hL.equivariant x hx (Work.EKLComp.u s) (Work.EKLComp.u_mem s) hux
  obtain ⟨c', hc'0, hc'T, heq'⟩ :=
    hL.equivariant x' hx' (Work.EKLComp.u s) (Work.EKLComp.u_mem s) hux'
  -- `ν` is carried by `U_01` at the translated points, and normalised there.
  have hcarx : (ν (Work.EKLComp.u s • x)) (↑(Work.EKLContract.Uij Work.EKLComp.h01))ᶜ = 0 :=
    hL.carried _ hux
  have hcarx' : (ν (Work.EKLComp.u s • x')) (↑(Work.EKLContract.Uij Work.EKLComp.h01))ᶜ = 0 :=
    hL.carried _ hux'
  have hnormx : Work.EKLComp.nuR (ν (Work.EKLComp.u s • x)) (Set.Icc (-1) 1) = 1 :=
    Work.EKLComp.nuR_normalised (hL.normalised _ hux)
  have hnormx' : Work.EKLComp.nuR (ν (Work.EKLComp.u s • x')) (Set.Icc (-1) 1) = 1 :=
    Work.EKLComp.nuR_normalised (hL.normalised _ hux')
  -- Push (3) forward along `nuR`: the parameter is shifted by `s`.
  have h1 : Work.EKLComp.nuR (ν x)
      = c • (Work.EKLComp.nuR (ν (Work.EKLComp.u s • x))).map (fun t => t + s) := by
    conv_lhs => rw [heq]
    rw [Work.EKLComp.nuR_smul, Work.EKLComp.nuR_map_mul_u hcarx s]
  have h2 : Work.EKLComp.nuR (ν x')
      = c' • (Work.EKLComp.nuR (ν (Work.EKLComp.u s • x'))).map (fun t => t + s) := by
    conv_lhs => rw [heq']
    rw [Work.EKLComp.nuR_smul, Work.EKLComp.nuR_map_mul_u hcarx' s]
  exact measure_eq_of_smul_map_add hc0 hcT hc'0 hc'T hnormx hnormx' h1 (h.trans h2)

end Work.EKLCompLeaf
