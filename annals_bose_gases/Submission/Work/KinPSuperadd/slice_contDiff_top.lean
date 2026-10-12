import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Smoothness of the block slices of a smooth `(N₁+N₂)`-particle function

The block decomposition `X (N₁+N₂) ≃ X N₁ × X N₂` via `mergeBlock N₁ N₂` (each
of the `N₁+N₂` coordinates of the merged configuration is one of the two block
coordinates) is a **linear homeomorphism**, so freezing one of the two blocks
is a smooth operation: if `Φ : X (N₁+N₂) → ℝ` is `C^∞` then so are both slices

    u ↦ Φ (mergeBlock N₁ N₂ (u, w))        (w : X N₂ fixed)
    w ↦ Φ (mergeBlock N₁ N₂ (u, w))        (u : X N₁ fixed)

This is the standing hypothesis that every slice/Fubini argument of the
small-box analysis (`SlotSplit`, the `IntegrableOn`-witness of the slice
integrands, the per-slice Rayleigh bound) needs in order to even *state* the
sliced objects: a slice of a smooth trial state is again a smooth trial state.

The mathematical content is `Coordination`: `mergeBlock` is linear plus a
constant in each variable, and the slices of a `C^∞` function along an affine
map are `C^∞`.  Both statements are proved coordinatewise through
`contDiff_pi`: a coordinate of `mergeBlock N₁ N₂ (·, w)` is either one of the
`N₁` coordinates of the variable (`contDiff_apply`) or a constant.
-/

noncomputable section

open scoped ContDiff Topology

namespace Work.KinPSuperadd

set_option autoImplicit false

/-- The first-block reassembly `u ↦ mergeBlock N₁ N₂ (u, w)`, with the second
block `w` frozen, is smooth: coordinatewise it is either a variable coordinate
or a constant. -/
lemma contDiff_mergeBlock_fst (N1 N2 : ℕ) (w : Submission.BoseGases.X N2) :
    ContDiff ℝ ⊤ (fun u : Submission.BoseGases.X N1 =>
      Submission.BoseGases.mergeBlock N1 N2 (u, w)) := by
  rw [contDiff_pi]
  intro k
  by_cases h : (k : ℕ) < N1
  · -- a coordinate of the first block: the corresponding coordinate of `u`
    let i : Fin N1 := ⟨k.val, h⟩
    have hk : k = Fin.castAdd N2 i := by ext; simp [i]
    rw [hk]
    have hfun : (fun u : Submission.BoseGases.X N1 =>
        Submission.BoseGases.mergeBlock N1 N2 (u, w) (Fin.castAdd N2 i))
        = fun u : Submission.BoseGases.X N1 => u i := by
      funext u; simp [Submission.BoseGases.mergeBlock]
    rw [hfun]
    exact contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) i
  · -- a coordinate of the second block: constant in `u`
    let j : Fin N2 := ⟨k.val - N1, by omega⟩
    have hk : k = Fin.natAdd N1 j := by ext; simp [j]; omega
    rw [hk]
    have hfun : (fun u : Submission.BoseGases.X N1 =>
        Submission.BoseGases.mergeBlock N1 N2 (u, w) (Fin.natAdd N1 j))
        = fun _ : Submission.BoseGases.X N1 => w j := by
      funext u; simp [Submission.BoseGases.mergeBlock]
    rw [hfun]
    exact contDiff_const

/-- The second-block reassembly `w ↦ mergeBlock N₁ N₂ (u, w)`, with the first
block `u` frozen, is smooth. -/
lemma contDiff_mergeBlock_snd (N1 N2 : ℕ) (u : Submission.BoseGases.X N1) :
    ContDiff ℝ ⊤ (fun w : Submission.BoseGases.X N2 =>
      Submission.BoseGases.mergeBlock N1 N2 (u, w)) := by
  rw [contDiff_pi]
  intro k
  by_cases h : (k : ℕ) < N1
  · -- a coordinate of the first block: constant in `w`
    let i : Fin N1 := ⟨k.val, h⟩
    have hk : k = Fin.castAdd N2 i := by ext; simp [i]
    rw [hk]
    have hfun : (fun w : Submission.BoseGases.X N2 =>
        Submission.BoseGases.mergeBlock N1 N2 (u, w) (Fin.castAdd N2 i))
        = fun _ : Submission.BoseGases.X N2 => u i := by
      funext w; simp [Submission.BoseGases.mergeBlock]
    rw [hfun]
    exact contDiff_const
  · -- a coordinate of the second block: the corresponding coordinate of `w`
    let j : Fin N2 := ⟨k.val - N1, by omega⟩
    have hk : k = Fin.natAdd N1 j := by ext; simp [j]; omega
    rw [hk]
    have hfun : (fun w : Submission.BoseGases.X N2 =>
        Submission.BoseGases.mergeBlock N1 N2 (u, w) (Fin.natAdd N1 j))
        = fun w : Submission.BoseGases.X N2 => w j := by
      funext w; simp [Submission.BoseGases.mergeBlock]
    rw [hfun]
    exact contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) j

/-- The first-block slice `u ↦ Φ (mergeBlock N₁ N₂ (u, w))` of a smooth
`(N₁+N₂)`-particle function is smooth. -/
lemma contDiff_slice_fst {N1 N2 : ℕ} {Φ : Submission.BoseGases.X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ⊤ Φ) (w : Submission.BoseGases.X N2) :
    ContDiff ℝ ⊤ (fun u : Submission.BoseGases.X N1 =>
      Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))) :=
  hΦ.comp (contDiff_mergeBlock_fst N1 N2 w)

/-- The second-block slice `w ↦ Φ (mergeBlock N₁ N₂ (u, w))` of a smooth
`(N₁+N₂)`-particle function is smooth. -/
lemma contDiff_slice_snd {N1 N2 : ℕ} {Φ : Submission.BoseGases.X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ⊤ Φ) (u : Submission.BoseGases.X N1) :
    ContDiff ℝ ⊤ (fun w : Submission.BoseGases.X N2 =>
      Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))) :=
  hΦ.comp (contDiff_mergeBlock_snd N1 N2 u)

theorem slice_contDiff_top {N1 N2 : ℕ} {Φ : Submission.BoseGases.X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ⊤ Φ) :
    (∀ w : Submission.BoseGases.X N2, ContDiff ℝ ⊤ (fun u : Submission.BoseGases.X N1 =>
        Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w))))
    ∧ (∀ u : Submission.BoseGases.X N1, ContDiff ℝ ⊤ (fun w : Submission.BoseGases.X N2 =>
        Φ (Submission.BoseGases.mergeBlock N1 N2 (u, w)))) :=
  ⟨fun w => contDiff_slice_fst hΦ w, fun u => contDiff_slice_snd hΦ u⟩

end Work.KinPSuperadd
