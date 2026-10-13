/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/Shadow.lean`

The combinatorial heart of the mollifier-approximation estimate `HkSq_Jeps_sub_le`: the level-`k+1`
shadow of the level-`k` slot sum of `J_ε f - f` is at most twice the level-`k+1` integrand.

Each level-`k` slot of `J_ε f - f`, differentiated once along the shift path (which produces the
two operators `D_z` and `D_θ`), yields level-`k+1` slots whose weights are exactly the weights of
`HkIntegrand α (k+1) f`.  With the `D_θ`-groups carrying the `1/4` produced by
`(a + b)² ≤ 2a² + 2b²`, each of the four groups is dominated by one of the two parts of
`HkIntegrand α (k+1) f`, giving the total factor `1 + 1/4 + 1 + 1/4 = 5/2 ≤ 2·(1 + 1)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.DiffAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A sum of squares over a sub-family of the level-`k+1` mixed slots is dominated by the whole
level-`k+1` mixed part. -/
theorem sum_image_le_HkMPartF {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ} {ι : Type*}
    (s : Finset ι) (e : ι → ℕ × ℕ)
    (he : ∀ i ∈ s, e i ∈ slots (k + 1))
    (hinj : ∀ i ∈ s, ∀ j ∈ s, e i = e j → i = j) :
    (∑ i ∈ s, (Work.Spaces.mixed (e i).2 (e i).1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ := by
  have hkey : (∑ i ∈ s, (Work.Spaces.mixed (e i).2 (e i).1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      = ∑ q ∈ s.image e,
          (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
    (Finset.sum_image (f := fun q : ℕ × ℕ =>
        (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2) (g := e) hinj).symm
  rw [hkey, HkMPartF_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => sq_nonneg _
  intro q hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  exact he i hi

/-- A sum of squares over a sub-family of the level-`k+1` pure `D_z`-slots is dominated by the
whole level-`k+1` `D_z`-part. -/
theorem sum_image_le_HkZPart {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (e : ℕ → ℕ) (he : ∀ i ∈ Finset.range (k + 1), e i ∈ Finset.range (k + 2))
    (hinj : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1), e i = e j → i = j) :
    (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (e i) f z θ * wE z θ) ^ 2)
      ≤ HkSqAux.HkZPart (k + 1) f z θ := by
  have hkey : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter (e i) f z θ * wE z θ) ^ 2)
      = ∑ m ∈ (Finset.range (k + 1)).image e,
          (Work.Spaces.DzIter m f z θ * wE z θ) ^ 2 :=
    (Finset.sum_image (f := fun m : ℕ => (Work.Spaces.DzIter m f z θ * wE z θ) ^ 2)
      (g := e) hinj).symm
  rw [hkey, HkZPart_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => sq_nonneg _
  intro m hm
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
  exact he i hi

/-- **The shadow bound.**  The level-`k+1` shadow of the level-`k` slot sum of `J_ε f - f` is at
most twice the level-`k+1` integrand. -/
theorem shadow_le (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    shadow α k f z θ ≤ 2 * Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * wE z θ) ^ 2)
      ≤ HkSqAux.HkZPart (k + 1) f z θ :=
    sum_image_le_HkZPart (k := k) (f := f) (z := z) (θ := θ) (fun i => i + 1)
      (fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega)
      (fun i _ j _ h => by omega)
  have h2 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.mixed i 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ :=
    sum_image_le_HkMPartF (k := k) (f := f) (z := z) (θ := θ) (s := Finset.range (k + 1))
      (e := fun i => (1, i)) (fun i hi => by
        rw [mem_slots]; simp only [Finset.mem_range] at hi; omega)
      (fun i _ j _ h => by simpa using congrArg Prod.snd h)
  have h3 : (∑ q ∈ slots k, (Work.Spaces.mixed (q.2 + 1) q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ :=
    sum_image_le_HkMPartF (k := k) (f := f) (z := z) (θ := θ) (s := slots k)
      (e := fun q => (q.1, q.2 + 1)) (fun q hq => by
        rw [mem_slots] at hq ⊢; omega)
      (fun i hi j hj h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (by omega))
  have h4 : (∑ q ∈ slots k, (Work.Spaces.mixed q.2 (q.1 + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ HkSqAux.HkMPartF α (k + 1) f z θ :=
    sum_image_le_HkMPartF (k := k) (f := f) (z := z) (θ := θ) (s := slots k)
      (e := fun q => (q.1 + 1, q.2)) (fun q hq => by
        rw [mem_slots] at hq ⊢; omega)
      (fun i hi j hj h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (by omega) h.2)
  have hZnn : 0 ≤ HkSqAux.HkZPart (k + 1) f z θ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMnn : 0 ≤ HkSqAux.HkMPartF α (k + 1) f z θ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hparts : Work.Spaces.HkIntegrand α (k + 1) f z θ
      = HkSqAux.HkZPart (k + 1) f z θ + HkSqAux.HkMPartF α (k + 1) f z θ := by
    rw [HkSqAux.HkIntegrand_eq_parts, HkSqAux.HkMPart_eq_HkMPartF]
  rw [hparts, shadow]
  nlinarith [h1, h2, h3, h4, hZnn, hMnn]

end Work.FTS.StrongEps.DiffAux
