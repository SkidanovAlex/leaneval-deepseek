import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Interp.exists_interp
import Submission.Work.PL.Approx.Interp.eqOn_simp_of_eqOn
import Submission.Work.PL.Approx.Near.dist_lt_of_linOn
import Submission.Work.PL.Approx.Continuous.continuousOn_g
import Submission.Work.PL.Approx.Continuous.dist_add_smul_sub_le
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_one_of_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_zero

/-!
# PL approximation in a cube, frozen on a subcomplex of the subdivision

`Work.PL.Approx.Frozen.pl_approx_frozen_sub`: the frozen PL approximation in the form used by the
engulfing argument, where the frozen complex `L` is a subcomplex of the *given* fine complex `K'`
(rather than of `K`).

The construction is the same cutoff construction as in `Work.PL.Approx.pl_approx_of_osc`:

`g x = f x + cubeCut β'' β' (f x) • (ℓ x - f x)`, `β'' = (α+β)/2`, `β' = (β''+β)/2`,

where `ℓ` is the vertexwise linear interpolant of `f` on `K'` and `ε' = min ε ((β-α)/24)` bounds the
oscillation of `f` on the simplices of `K'`, whence `dist (ℓ x) (f x) < ε'` on `K.space`.

The new point (compared with `pl_approx_frozen_of_osc`) is that the freezing on `L.space` needs no
compatibility hypothesis of `RestrictsTo` type at all, only `L.faces ⊆ K'.faces`: given
`x ∈ L.space` with `f x ∈ closedCube β`, choose a face `ρ` of `L` with `x ∈ simp ρ`.  By `hlinL`
the map `f` agrees on `simp ρ` with an affine map `A`; the interpolant `ℓ` agrees with `f` at the
vertices of `ρ` (they are vertices of `K'`), hence with `A` on all of `simp ρ` (affine maps
agreeing on the vertices of a finite set agree on its convex hull).  So `ℓ x = f x` and the cutoff
term vanishes.  Outside `closedCube β` the cutoff itself vanishes, and on any simplex `s` of `K'`
on which `g` meets `closedCube α` the cutoff is `1` (since `α + 4 ε' ≤ β''`), so that `g = ℓ` is
affine there.
-/

namespace Work.PL.Approx.Frozen

open Set Metric

lemma pl_approx_frozen_sub {N n : ℕ} (K K' : PL.Cx N) (hK' : K'.faces.Finite) (L : PL.Cx N)
    (hLK' : PL.IsSub L K') (f : PL.E N → PL.E n) (hf : ContinuousOn f K.space)
    (hsub : PL.Subdivides K' K) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (ε : ℝ) (hε : 0 < ε)
    (hlinL : ∀ ρ ∈ L.faces, (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z)
    (hosc : ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < min ε ((β - α) / 24)) :
    ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧ (∀ x ∈ L.space, g x = f x) ∧
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
  have hβmα : 0 < β - α := by linarith
  have hε'pos : 0 < ε' := by rw [hε']; exact lt_min hε (by linarith)
  have hε'leε : ε' ≤ ε := by rw [hε']; exact min_le_left ε ((β - α) / 24)
  have hε'le24 : ε' ≤ (β - α) / 24 := by rw [hε']; exact min_le_right ε ((β - α) / 24)
  have hαb : α + 4 * ε' ≤ β'' := by rw [hβ'']; linarith
  have hsubsp : K'.space = K.space := hsub.1
  -- the vertexwise linear interpolant of `f` on `K'`
  obtain ⟨ℓ, hℓcont, hℓlin, hℓvert⟩ := Interp.exists_interp K' hK' f
  have hℓcontK : ContinuousOn ℓ K.space := by rw [← hsubsp]; exact hℓcont
  set g := fun x : PL.E N => f x + cubeCut β'' β' (f x) • (ℓ x - f x) with hg'
  -- `simp s ⊆ K.space` for `s` a face of `K'`
  have hface : ∀ s ∈ K'.faces, PL.simp s ⊆ K.space := by
    intro s hs z hz
    rw [← hsubsp, Geometry.SimplicialComplex.space]
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hz⟩
  -- the oscillation hypothesis is exactly the bound `ε'` we need
  have hoscε' : ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < ε' := by
    intro s hs x hx y hy
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
    have := hnear x hx
    exact lt_of_le_of_lt hstep this
  -- the cutoff vanishes where `f` is outside the cube of radius `β`
  have hcut0 : ∀ x ∈ K.space, f x ∉ PL.closedCube β → cubeCut β'' β' (f x) = 0 := by
    intro x _ hx
    obtain ⟨i, hi⟩ : ∃ i, β < |(f x) i| := by
      simpa [PL.closedCube, not_forall, not_le] using hx
    exact Cutoff.cubeCut_eq_zero hβ''β' ⟨i, le_of_lt (lt_trans hβ'β hi)⟩
  -- `L.space ⊆ K.space`, since the faces of `L` are faces of `K'`
  have hLKsp : L.space ⊆ K.space := by
    intro x hx
    obtain ⟨ρ, hρ, hxρ⟩ := (Geometry.SimplicialComplex.mem_space_iff (K := L)).mp hx
    rw [← hsubsp]
    exact K'.convexHull_subset_space (hLK' hρ) hxρ
  -- freezing on `L.space`: the interpolant agrees with `f` wherever `f` meets `closedCube β`
  have hfrozen : ∀ x ∈ L.space, f x ∈ PL.closedCube β → ℓ x = f x := by
    intro x hxL hβ
    obtain ⟨ρ, hρ, hxρ⟩ := (Geometry.SimplicialComplex.mem_space_iff (K := L)).mp hxL
    have hxρ' : x ∈ PL.simp ρ := by simpa [PL.simp] using hxρ
    obtain ⟨A, hA⟩ := hlinL ρ hρ ⟨x, hxρ', hβ⟩
    obtain ⟨A', hA'⟩ := hℓlin ρ (hLK' hρ)
    have haeq : ∀ v ∈ ρ, A' v = A v := by
      intro v hv
      have hvρ : v ∈ PL.simp ρ := subset_convexHull ℝ (ρ : Set (PL.E N)) hv
      rw [← hA' hvρ, hℓvert ρ (hLK' hρ) v hv, hA v hvρ]
    have hAx : A' x = A x := Interp.eqOn_simp_of_eqOn ρ A' A haeq x hxρ'
    rw [hA' hxρ', hAx, hA x hxρ']
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · exact Continuous.continuousOn_g K f ℓ β'' β' hf hℓcontK
  · intro x hx
    exact lt_of_lt_of_le (hgdist x hx) hε'leε
  · intro x hx hfx
    change f x + cubeCut β'' β' (f x) • (ℓ x - f x) = f x
    rw [hcut0 x hx hfx, zero_smul, add_zero]
  · intro x hxL
    have hxK : x ∈ K.space := hLKsp hxL
    change f x + cubeCut β'' β' (f x) • (ℓ x - f x) = f x
    by_cases hβ : f x ∈ PL.closedCube β
    · rw [hfrozen x hxL hβ, sub_self, smul_zero, add_zero]
    · rw [hcut0 x hxK hβ, zero_smul, add_zero]
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
