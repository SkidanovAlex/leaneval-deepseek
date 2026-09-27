import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Interp.eqOn_simp_of_eqOn

namespace Work.PL.Approx.Frozen

open Set

/-- Points of `L.space ∩ K'.space` at which `f` lands in the cube `closedCube β` are fixed by any
vertex interpolant `ℓ` of `f` on `K'`.

More precisely: if `ℓ` is affine on every face of `K'` (`hlin`) and agrees with `f` at the
vertices of every face of `K'` (`hvert`), and if on the subcomplex `L` the map `f` is affine on
every face `ρ` of `L` that contains a point with `f`-image in `closedCube β` (`hlinL`), then
`ℓ` and `f` agree on the part of `L.space` lying in `K'.space` and mapping into `closedCube β`.

The proof picks a face `s` of `K'` containing `x`; the frozen vertices of `s` (those in `L.space`)
span `simp s ∩ L.space` (`hresK'`) and lie in a single face `ρ` of `L` (`hfaceK'`).  Both `ℓ` (via
its affine map on `s`) and `f` (via its affine map on `ρ`) are affine near `x`, and they agree at
the frozen vertices of `s`, hence — by convexity of the agreement set — at `x`. -/
lemma eq_of_mem_frozen {N n : ℕ} (K' : PL.Cx N) (L : PL.Cx N)
    (hresK' : ∀ s ∈ K'.faces, PL.simp s ∩ L.space = PL.simp (frozenPart L s))
    (hfaceK' : ∀ s ∈ K'.faces, (∃ v ∈ s, v ∈ L.space) → ∃ ρ ∈ L.faces, ∀ v ∈ s, v ∈ L.space → v ∈ PL.simp ρ)
    (f ℓ : PL.E N → PL.E n) (hlin : PL.LinOn K' ℓ)
    (hvert : ∀ s ∈ K'.faces, ∀ v ∈ s, ℓ v = f v) {β : ℝ}
    (hlinL : ∀ ρ ∈ L.faces, (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z)
    (x : PL.E N) (hx : x ∈ L.space) (hxK : x ∈ K'.space) (hxβ : f x ∈ PL.closedCube β) :
    ℓ x = f x := by
  classical
  -- `x` lies in some face `s` of `K'`.
  obtain ⟨s, hs, hxs⟩ := (Geometry.SimplicialComplex.mem_space_iff (K := K')).mp hxK
  have hxss : x ∈ PL.simp s := by simpa [PL.simp] using hxs
  -- `x` lies in the simplex spanned by the frozen vertices of `s`.
  have hxgen : x ∈ PL.simp (frozenPart L s) := by
    rw [← hresK' s hs]
    exact ⟨hxss, hx⟩
  -- Hence `s` has a frozen vertex.
  have hne : (frozenPart L s).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (frozenPart L s) with h | h
    · exfalso
      rw [h, PL.simp] at hxgen
      simp at hxgen
    · exact h
  obtain ⟨v, hv⟩ := hne
  have hv' : v ∈ s ∧ v ∈ L.space := by
    simpa only [frozenPart, Finset.mem_filter] using hv
  -- All frozen vertices of `s` lie in a single face `ρ` of `L`.
  obtain ⟨ρ, hρ, hρspec⟩ := hfaceK' s hs ⟨v, hv'.1, hv'.2⟩
  have hsub : ((frozenPart L s : Finset (PL.E N)) : Set (PL.E N)) ⊆ PL.simp ρ := by
    intro w hw
    rw [Finset.mem_coe] at hw
    have hw' : w ∈ s ∧ w ∈ L.space := by
      simpa only [frozenPart, Finset.mem_filter] using hw
    exact hρspec w hw'.1 hw'.2
  have hconvρ : Convex ℝ (PL.simp ρ) := convex_convexHull ℝ (ρ : Set (PL.E N))
  have hxρ : x ∈ PL.simp ρ := convexHull_min hsub hconvρ hxgen
  -- `f` is affine on `ρ` and `ℓ` is affine on `s`.
  obtain ⟨B, hB⟩ := hlinL ρ hρ ⟨x, hxρ, hxβ⟩
  obtain ⟨A, hA⟩ := hlin s hs
  -- `A` and `B` agree at the frozen vertices of `s`.
  have hAB : ∀ w ∈ frozenPart L s, A w = B w := by
    intro w hw
    have hw' : w ∈ s ∧ w ∈ L.space := by
      simpa only [frozenPart, Finset.mem_filter] using hw
    have hwρ : w ∈ PL.simp ρ := hρspec w hw'.1 hw'.2
    have h1 : ℓ w = A w := hA (subset_convexHull ℝ (s : Set (PL.E N)) hw'.1)
    have h2 : ℓ w = f w := hvert s hs w hw'.1
    have h3 : f w = B w := hB w hwρ
    rw [← h1, h2, h3]
  -- Conclude at `x`, which is a convex combination of those frozen vertices.
  have hABx : A x = B x :=
    Work.PL.Approx.Interp.eqOn_simp_of_eqOn (frozenPart L s) A B hAB x hxgen
  have h1x : ℓ x = A x := hA hxss
  have h2x : f x = B x := hB x hxρ
  exact h1x.trans (hABx.trans h2x.symm)

end Work.PL.Approx.Frozen
