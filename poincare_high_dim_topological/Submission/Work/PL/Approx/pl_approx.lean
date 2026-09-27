import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Interp.exists_interp
import Submission.Work.PL.Approx.Near.dist_lt_of_linOn
import Submission.Work.PL.Approx.Continuous.continuousOn_g
import Submission.Work.PL.Approx.Continuous.dist_add_smul_sub_le
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_one_of_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_zero
import Submission.Work.PL.Approx.Cutoff.cubeCut_ne_zero
import Submission.Work.PL.Approx.Finite.exists_delta_of_continuousOn
import Submission.Work.PL.Approx.Finite.dist_lt_of_mesh
import Submission.Work.PL.Approx.Finite.isCompact_space_of_finite
import Submission.Work.PL.Approx.Finite.abs_apply_le_dist_zero

/-!
# PL approximation in a cube (area A5, G5): `pl_approx`

Given a continuous `f : ℝᴺ → ℝⁿ` on the underlying space of a finite simplicial complex `K`
and radii `α < β < 1`, one can approximate `f` uniformly within `ε` by a map `g` which

* is continuous on `K.space`,
* agrees with `f` outside the preimage of the cube of radius `β` (freezing), and
* is affine on every simplex of a sufficiently fine subdivision `S.iter r K` which meets the
  preimage of the cube of radius `α`.

The construction is the classical one: take the vertexwise linear interpolant `ℓ` of `f` on a
fine subdivision `K'` (so that `ℓ` is close to `f` because `f` hardly oscillates on the small
simplices), and set

  `g x = f x + cubeCut β'' β' (f x) • (ℓ x - f x)`,   `α < β'' < β' < β` `(β'' = (α+β)/2, β' = (β''+β)/2)`.

The cutoff `cubeCut β'' β'` is `1` on the cube of radius `β''` and `0` off the cube of radius `β'`,
so `g = f` where `f` is outside the cube of radius `β`, while `g` agrees with `ℓ` (hence is affine
on the simplices) wherever `g` lands in the cube of radius `α`: there `f` is within `4ε'` of the
cube of radius `α`, and on the whole surrounding simplex `f` oscillates by at most `ε'`, so `f`
lands in the cube of radius `β''` where the cutoff is `1`.
-/

namespace Work.PL.Approx

open Set Metric

lemma pl_approx {N n : ℕ} (S : Subdiv N) (K : PL.Cx N) (hK : K.faces.Finite) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧
      ∀ s ∈ (S.iter r K hK).faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y := by
  classical
  have hα0 : 0 < α := hα
  have hβ1' : β < 1 := hβ1
  -- the two intermediate cube radii
  set β'' := (α + β) / 2 with hβ''
  set β' := (β'' + β) / 2 with hβ'
  have hαβ'' : α < β'' := by rw [hβ'']; linarith
  have hβ''β' : β'' < β' := by rw [hβ', hβ'']; linarith
  have hβ'β : β' < β := by rw [hβ', hβ'']; linarith
  have hβ''pos : 0 < β'' := lt_trans hα0 hαβ''
  have hβ''β1 : β'' < 1 := lt_trans hβ''β' (lt_trans hβ'β hβ1')
  -- the accuracy demanded of the interpolant
  set ε' := min ((β'' - α) / 4) ε with hε'
  have hε'pos : 0 < ε' := by rw [hε']; exact lt_min (by linarith) hε
  have hε'le : ε' ≤ (β'' - α) / 4 := by rw [hε']; exact min_le_left _ _
  have hε'leε : ε' ≤ ε := by rw [hε']; exact min_le_right _ _
  have hαb : α + 4 * ε' ≤ β'' := by linarith
  -- uniform continuity of `f` on `K.space`
  obtain ⟨δ, hδpos, hδ⟩ := Finite.exists_delta_of_continuousOn K hK f hf (ε := ε') hε'pos
  obtain ⟨r, hr⟩ := S.mesh K hK δ hδpos
  set K' := S.iter r K hK with hK'
  have hK'fin : K'.faces.Finite := S.iter_fin r K hK
  have hK'space : K'.space = K.space := S.iter_space r K hK
  have hsub : PL.Subdivides K' K := S.iter_subdivides r K hK
  obtain ⟨ℓ, hℓcont, hℓlin, hℓvert⟩ := Interp.exists_interp K' hK'fin f
  have hℓcontK : ContinuousOn ℓ K.space := by rwa [hK'space] at hℓcont
  set g := fun x : PL.E N => f x + cubeCut β'' β' (f x) • (ℓ x - f x) with hg'
  -- `simp s ⊆ K.space` for `s` a face of `K'`
  have hface : ∀ s ∈ K'.faces, PL.simp s ⊆ K.space := by
    intro s hs z hz
    rw [← hK'space, Geometry.SimplicialComplex.space]
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hz⟩
  -- `f` has oscillation `< ε'` on each simplex of `K'`
  have hosc : ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < ε' := by
    intro s hs x hx y hy
    exact hδ x (hface s hs hx) y (hface s hs hy) (Finite.dist_lt_of_mesh K' hr hs hx hy)
  -- the interpolant is `ε'`-close to `f`
  have hnear : ∀ x ∈ K.space, dist (ℓ x) (f x) < ε' :=
    Near.dist_lt_of_linOn K K' hsub hε'pos f ℓ hℓlin hℓvert hosc
  -- ... and so is `g`
  have hgdist : ∀ x ∈ K.space, dist (g x) (f x) < ε' := by
    intro x hx
    have hmem := (Cutoff.cubeCut_mem hβ''β' (f x)).1
    have hmem2 := (Cutoff.cubeCut_mem hβ''β' (f x)).2
    have hstep : dist (f x + cubeCut β'' β' (f x) • (ℓ x - f x)) (f x) ≤ dist (ℓ x) (f x) :=
      Continuous.dist_add_smul_sub_le (f x) (ℓ x) hmem hmem2
    exact lt_of_le_of_lt hstep (hnear x hx)
  -- the cutoff vanishes where `f` is outside the cube of radius `β`
  have hcut0 : ∀ x ∈ K.space, f x ∉ PL.closedCube β → cubeCut β'' β' (f x) = 0 := by
    intro x _ hx
    obtain ⟨i, hi⟩ : ∃ i, β < |(f x) i| := by
      simpa [PL.closedCube, not_forall, not_le] using hx
    exact Cutoff.cubeCut_eq_zero hβ''β' ⟨i, le_of_lt (lt_trans hβ'β hi)⟩
  refine ⟨r, g, ?_, ?_, ?_, ?_⟩
  · exact Continuous.continuousOn_g K f ℓ β'' β' hf hℓcontK
  · intro x hx
    exact lt_of_lt_of_le (hgdist x hx) hε'leε
  · intro x hx hfx
    change f x + cubeCut β'' β' (f x) • (ℓ x - f x) = f x
    rw [hcut0 x hx hfx, zero_smul, add_zero]
  · intro s hs hx
    obtain ⟨x, hxs, hgx⟩ := hx
    have hcut1 : ∀ y ∈ PL.simp s, cubeCut β'' β' (f y) = 1 :=
      Cutoff.cubeCut_eq_one_of_mem s x f g hαb hβ''β' hε'pos hxs hgx
        (fun y hy => hgdist y (hface s hs hy))
        (fun y hy => hosc s hs y hy x hxs)
    obtain ⟨A, hA⟩ := hℓlin s hs
    refine ⟨A, ?_⟩
    intro y hy
    change f y + cubeCut β'' β' (f y) • (ℓ y - f y) = A y
    rw [hcut1 y hy, one_smul, hA hy]
    abel

end Work.PL.Approx
