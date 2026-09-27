import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Interp.exists_interp
import Submission.Work.PL.Approx.Near.dist_lt_of_linOn
import Submission.Work.PL.Approx.Continuous.continuousOn_g
import Submission.Work.PL.Approx.Continuous.dist_add_smul_sub_le
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_one_of_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_mem
import Submission.Work.PL.Approx.Cutoff.cubeCut_eq_zero
import Submission.Work.PL.Approx.Finite.exists_delta_of_continuousOn
import Submission.Work.PL.Approx.Finite.dist_lt_of_mesh
import Submission.Work.PL.Approx.Frozen.eq_of_mem_frozen

/-!
# PL approximation frozen on a subcomplex, from a prescribed oscillation bound

`Work.PL.Approx.pl_approx_frozen_of_osc`: the "of oscillation" form of the frozen PL
approximation `G5`.  Instead of asking for a subdivision operator `S` and producing a
sufficiently fine iterate `K' = S.iter r K` (as `Work.PL.Approx.pl_approx_frozen` does), the
fine complex `K'` is **given**, together with

* `hsub : Subdivides K' K`,
* the compatibility of `K'` with the frozen subcomplex `L` (`hresK'`, `hfaceK'`, the two clauses
  of `Work.PL.Approx.RestrictsTo` at level `0`), and
* the oscillation bound `hosc` on every simplex of `K'`.

The construction is the same cutoff construction as in `pl_approx_frozen`:
`g x = f x + cubeCut β'' β' (f x) • (ℓ x - f x)` with `β'' = (α+β)/2`, `β' = (β''+β)/2`, where
`ℓ` is the vertexwise linear interpolant of `f` on `K'` and `ε' = min ((β-α)/24) ε`.

Since `α + 4ε' ≤ β''` (as `4 ε' ≤ (β-α)/6 ≤ (β-α)/2 = β'' - α`), the cutoff is `1` on the
`f`-image of any simplex of `K'` on which `g` meets `closedCube α`, so `g = ℓ` is affine there;
off `closedCube β` the cutoff vanishes; and on `L.space` the frozen lemma
`Work.PL.Approx.Frozen.eq_of_mem_frozen` gives `ℓ = f` wherever `f` meets `closedCube β`.
-/

namespace Work.PL.Approx

open Set Metric

lemma pl_approx_frozen_of_osc {N n : ℕ} (K K' : PL.Cx N) (hK' : K'.faces.Finite) (L : PL.Cx N)
    (hLK : PL.IsSub L K) (f : PL.E N → PL.E n) (hf : ContinuousOn f K.space) (hsub : PL.Subdivides K' K)
    (hresK' : ∀ s ∈ K'.faces, PL.simp s ∩ L.space = PL.simp (frozenPart L s))
    (hfaceK' : ∀ s ∈ K'.faces, (∃ v ∈ s, v ∈ L.space) → ∃ ρ ∈ L.faces, ∀ v ∈ s, v ∈ L.space → v ∈ PL.simp ρ)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1) (ε : ℝ) (hε : 0 < ε)
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
  set ε' := min ((β - α) / 24) ε with hε'
  have hε'pos : 0 < ε' := by rw [hε']; exact lt_min (by linarith) hε
  have hε'le24 : ε' ≤ (β - α) / 24 := by rw [hε']; exact min_le_left _ _
  have hε'leε : ε' ≤ ε := by rw [hε']; exact min_le_right _ _
  have hαb : α + 4 * ε' ≤ β'' := by rw [hβ'']; linarith
  have hK'space : K'.space = K.space := hsub.1
  -- the oscillation hypothesis is exactly the bound `ε'` we need
  have hoscε' : ∀ s ∈ K'.faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s, dist (f x) (f y) < ε' := by
    intro s hs x hx y hy
    have h1 := hosc s hs x hx y hy
    have h2 : min ε ((β - α) / 24) = ε' := by rw [hε', min_comm]
    linarith
  obtain ⟨ℓ, hℓcont, hℓlin, hℓvert⟩ := Interp.exists_interp K' hK' f
  have hℓcontK : ContinuousOn ℓ K.space := by rw [← hK'space]; exact hℓcont
  set g := fun x : PL.E N => f x + cubeCut β'' β' (f x) • (ℓ x - f x) with hg'
  -- `simp s ⊆ K.space` for `s` a face of `K'`
  have hface : ∀ s ∈ K'.faces, PL.simp s ⊆ K.space := by
    intro s hs z hz
    rw [← hK'space, Geometry.SimplicialComplex.space]
    exact Set.mem_iUnion₂.mpr ⟨s, hs, hz⟩
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
  -- `L.space ⊆ K.space`
  have hLKsp : L.space ⊆ K.space := by
    intro x hx
    rw [Geometry.SimplicialComplex.mem_space_iff] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hLK hs, hxs⟩
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
    · have hℓx : ℓ x = f x :=
        Frozen.eq_of_mem_frozen K' L hresK' hfaceK' f ℓ hℓlin hℓvert hlinL x hxL
          (by rw [hK'space]; exact hxK) hβ
      rw [hℓx, sub_self, smul_zero, add_zero]
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

end Work.PL.Approx
