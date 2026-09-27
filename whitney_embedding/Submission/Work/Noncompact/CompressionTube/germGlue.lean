import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Gluing two curve germs that agree with the same straight chart line

If two curves `A`, `B` agree near a parameter `τ`, on their respective sides, with the *same*
straight chart line `t ↦ c.symm (c p + (t - τ) • w)`, then the glued curve
`t ↦ if t ≤ τ then A t else B t` is `C^∞` (and an immersion) at `τ`.

This is the junction lemma of the line construction.  It is kept in its own small module so that
the files that only need the gluing (and not the corridor/canal machinery) do not have to import
the whole compressed-spine development.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology
open scoped Manifold ContDiff

noncomputable section

theorem contMDiffAt_glue_same_germ {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M)
    {p : M} (hp : p ∈ c.source) {w : EuclideanSpace ℝ (Fin n)}
    {A B : ℝ → M} {τ δ : ℝ} (hδ : 0 < δ)
    (hAgerm : ∀ t : ℝ, τ - δ ≤ t → t ≤ τ → A t = c.symm (c p + (t - τ) • w))
    (hBgerm : ∀ t : ℝ, τ ≤ t → t ≤ τ + δ → B t = c.symm (c p + (t - τ) • w)) :
    ContMDiffAt MCreal (MC n) smoothOrder (fun t : ℝ => if t ≤ τ then A t else B t) τ := by
  have htarget : c p ∈ c.target := c.map_source hp
  have hinner : ContMDiffAt MCreal (MC n) smoothOrder
      (fun t : ℝ => c p + (t - τ) • w) τ := by
    rw [contMDiffAt_iff_contDiffAt]
    fun_prop
  have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder (⇑c.symm) (c p) :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt (c.open_target.mem_nhds htarget)
  have hpt : c p + (τ - τ) • w = c p := by rw [sub_self, zero_smul, add_zero]
  have hsymm' : ContMDiffAt (MC n) (MC n) smoothOrder (⇑c.symm) (c p + (τ - τ) • w) := by
    rw [hpt]; exact hsymm
  have hΦ : ContMDiffAt MCreal (MC n) smoothOrder
      (fun t : ℝ => c.symm (c p + (t - τ) • w)) τ := hsymm'.comp τ hinner
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (by linarith : τ - δ < τ) (by linarith : τ < τ + δ)]
    with t ht
  by_cases h : t ≤ τ
  · rw [if_pos h]; exact hAgerm t ht.1.le h
  · rw [if_neg h]; exact hBgerm t (not_le.mp h).le ht.2.le

/-- The derivative of a translation of `ℝ` is the identity. -/
lemma mfderiv_sub_eq_id (c x : ℝ) :
    mfderiv MCreal MCreal (fun s : ℝ => s - c) x = ContinuousLinearMap.id ℝ ℝ := by
  have h : (fun s : ℝ => s - c) = (id : ℝ → ℝ) - (fun _ : ℝ => c) := rfl
  rw [h, mfderiv_sub (z := x) (f := (id : ℝ → ℝ)) (g := fun _ : ℝ => c)
    ((contMDiffAt_id (x := x) (n := ∞)).mdifferentiableAt (by simp))
    ((contMDiffAt_const (x := x) (n := ∞)).mdifferentiableAt (by simp))]
  rw [mfderiv_id, mfderiv_const]
  exact sub_zero _

/-- The derivative of the reflection `s ↦ c - s` of `ℝ` is minus the identity. -/
lemma mfderiv_const_sub_eq_negId (c x : ℝ) :
    mfderiv MCreal MCreal (fun s : ℝ => c - s) x = -(ContinuousLinearMap.id ℝ ℝ) := by
  have h : (fun s : ℝ => c - s) = -(fun s : ℝ => s - c) := by
    funext s
    rw [Pi.neg_apply, neg_sub]
  rw [h, mfderiv_neg, mfderiv_sub_eq_id]
  rfl

/-- The derivative of the translation `s ↦ s - c` is injective. -/
lemma injective_mfderiv_sub (c x : ℝ) :
    Function.Injective (mfderiv MCreal MCreal (fun s : ℝ => s - c) x) := by
  rw [mfderiv_sub_eq_id]
  exact Function.injective_id

/-- The derivative of the reflection `s ↦ c - s` is injective. -/
lemma injective_mfderiv_const_sub (c x : ℝ) :
    Function.Injective (mfderiv MCreal MCreal (fun s : ℝ => c - s) x) := by
  rw [mfderiv_const_sub_eq_negId]
  exact fun u v huv => (neg_injective (show -u = -v from huv) : u = v)

end

end Work.Noncompact.CompressionTube
