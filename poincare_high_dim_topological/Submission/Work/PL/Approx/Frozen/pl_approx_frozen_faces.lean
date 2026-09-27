import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Interp.exists_interp
import Submission.Work.PL.Approx.Near.dist_lt_of_linOn
import Submission.Work.PL.Approx.Interp.eqOn_simp_of_eqOn
import Submission.Work.PL.Approx.Continuous.continuousOn_g
import Submission.Work.PL.Approx.Continuous.dist_add_smul_sub_le
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_one_of_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_zero

namespace Work.PL.Approx.Frozen

open Set Metric

lemma pl_approx_frozen_faces {N n : ℕ} (K K' : PL.Cx N) (hK' : K'.faces.Finite) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (hsub : PL.Subdivides K' K) (α β : ℝ) (hα : 0 < α)
    (hαβ : α < β) (hβ1 : β < 1) (ε : ℝ) (hε : 0 < ε) (T : Finset (Finset (PL.E N)))
    (hT : ∀ t ∈ T, t ∈ K'.faces)
    (hlinT : ∀ t ∈ T, (∃ z ∈ PL.simp t, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp t, f z = A z)
    (hosc : ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < min ε ((β - α) / 24)) :
    ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧
      (∀ t ∈ T, ∀ x ∈ PL.simp t, g x = f x) ∧
      ∀ s ∈ K'.faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y := by
  classical
  -- the two intermediate cube radii
  set β'' := (α + β) / 2 with hβ''
  set β' := (β'' + β) / 2 with hβ'
  have hαβ'' : α < β'' := by rw [hβ'']; linarith
  have hβ''β' : β'' < β' := by rw [hβ', hβ'']; linarith
  have hβ'β : β' < β := by rw [hβ', hβ'']; linarith
  -- the accuracy demanded of the interpolant
  set ε' := min ε ((β - α) / 24) with hε'
  have hε'pos : 0 < ε' := by rw [hε']; exact lt_min hε (by linarith)
  have hε'leε : ε' ≤ ε := by rw [hε']; exact min_le_left ε ((β - α) / 24)
  have hε'le24 : ε' ≤ (β - α) / 24 := by rw [hε']; exact min_le_right ε ((β - α) / 24)
  have hαb : α + 4 * ε' ≤ β'' := by rw [hβ'']; linarith
  -- the vertexwise linear interpolant of `f` on `K'`
  obtain ⟨ℓ, hℓcont, hℓlin, hℓvert⟩ := Interp.exists_interp K' hK' f
  have hsubsp : K'.space = K.space := hsub.1
  have hℓcontK : ContinuousOn ℓ K.space := by rwa [hsubsp] at hℓcont
  set g := fun x : PL.E N => f x + cubeCut β'' β' (f x) • (ℓ x - f x) with hg'
  -- `simp s ⊆ K.space` for `s` a face of `K'`
  have hface : ∀ s ∈ K'.faces, PL.simp s ⊆ K.space := by
    intro s hs z hz
    rw [← hsubsp, Geometry.SimplicialComplex.space]
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hz⟩
  -- the oscillation hypothesis is exactly the bound `ε'` we need
  have hoscε' : ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < ε' := by
    intro s hs x hx y hy
    rw [hε']
    exact hosc s hs x hx y hy
  -- the interpolant is `ε'`-close to `f`
  have hnear : ∀ x ∈ K.space, dist (ℓ x) (f x) < ε' :=
    Near.dist_lt_of_linOn K K' hsub hε'pos f ℓ hℓlin hℓvert hoscε'
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
  -- the frozen faces: `g` agrees with `f` on every simplex of `T`
  have hgfrozen : ∀ t ∈ T, ∀ x ∈ PL.simp t, g x = f x := by
    intro t htT x hx
    have ht : t ∈ K'.faces := hT t htT
    by_cases hβ : f x ∈ PL.closedCube β
    · -- `f` is affine on `simp t`, and so is the interpolant `ℓ`; they agree at the vertices
      obtain ⟨B, hB⟩ := hlinT t htT ⟨x, hx, hβ⟩
      obtain ⟨A, hA⟩ := hℓlin t ht
      have hAB : ∀ v ∈ t, A v = B v := by
        intro v hv
        rw [← hA (subset_convexHull ℝ (t : Set (PL.E N)) hv),
          hℓvert t ht v hv, hB v (subset_convexHull ℝ (t : Set (PL.E N)) hv)]
      have hℓx : ℓ x = f x := by
        rw [hA hx, Interp.eqOn_simp_of_eqOn t A B hAB x hx, hB x hx]
      change f x + cubeCut β'' β' (f x) • (ℓ x - f x) = f x
      rw [hℓx, sub_self, smul_zero, add_zero]
    · change f x + cubeCut β'' β' (f x) • (ℓ x - f x) = f x
      rw [hcut0 x (hface t ht hx) hβ, zero_smul, add_zero]
  refine ⟨g, ?_, ?_, ?_, hgfrozen, ?_⟩
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
        (fun y hy => hoscε' s hs y hy x hxs)
    obtain ⟨A, hA⟩ := hℓlin s hs
    refine ⟨A, ?_⟩
    intro y hy
    change f y + cubeCut β'' β' (f y) • (ℓ y - f y) = A y
    rw [hcut1 y hy, one_smul]
    have hℓA : ℓ y = A y := hA hy
    rw [hℓA]
    abel

end Work.PL.Approx.Frozen
