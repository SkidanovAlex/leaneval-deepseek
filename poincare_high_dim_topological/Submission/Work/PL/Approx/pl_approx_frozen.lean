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
import Submission.Work.PL.Approx.Frozen.eq_of_mem_frozen

namespace Work.PL.Approx

open Set Metric

/-- The frozen step, proved here for self-containedness: if `x` lies in the frozen subcomplex `L`
and `f x` lies in the cube of radius `β`, then the vertex interpolant `ℓ` of `f` on a subdivision
`K'` of `K` that is compatible with `L` (`RestrictsTo`) agrees with `f` at `x`.

The point is that `x` lies in the simplex of the *frozen* vertices of some face `s` of `K'`; those
vertices span a face `ρ` of `L` by compatibility, and on `simp ρ ⊆ f⁻¹(closedCube β)` the map `f`
coincides with an affine map by hypothesis.  The interpolant `ℓ` agrees with that affine map on
the frozen vertices, hence on their convex hull. -/
private lemma frozen_eq_of_mem {N n : ℕ} (K' : PL.Cx N) (L : PL.Cx N)
    (hres1 : ∀ s ∈ K'.faces, PL.simp s ∩ L.space = PL.simp (frozenPart L s))
    (hres2 : ∀ s ∈ K'.faces, (∃ v ∈ s, v ∈ L.space) →
      ∃ ρ ∈ L.faces, ∀ v ∈ s, v ∈ L.space → v ∈ PL.simp ρ)
    (f ℓ : PL.E N → PL.E n) (hlin : PL.LinOn K' ℓ)
    (hvert : ∀ s ∈ K'.faces, ∀ v ∈ s, ℓ v = f v) {β : ℝ}
    (hlinL : ∀ ρ ∈ L.faces, (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z)
    {x : PL.E N} (hxL : x ∈ L.space) (hxK : x ∈ K'.space) (hxβ : f x ∈ PL.closedCube β) :
    ℓ x = f x := by
  classical
  rw [Geometry.SimplicialComplex.mem_space_iff] at hxK
  obtain ⟨s, hs, hxs⟩ := hxK
  have hxinter : x ∈ PL.simp s ∩ L.space := ⟨hxs, hxL⟩
  rw [hres1 s hs] at hxinter
  -- the frozen part of `s` is nonempty
  have hne : (frozenPart L s).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (frozenPart L s) with h | h
    · rw [h] at hxinter ⊢
      simp [PL.simp] at hxinter
    · exact h
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨hv0s, hv0L⟩ := Finset.mem_filter.mp hv0
  obtain ⟨ρ, hρ, hρspec⟩ := hres2 s hs ⟨v0, hv0s, hv0L⟩
  -- the frozen vertices lie in the face `ρ` of `L`
  have hsub : PL.simp (frozenPart L s) ⊆ PL.simp ρ := by
    show convexHull ℝ ((frozenPart L s : Finset (PL.E N)) : Set (PL.E N)) ⊆
      convexHull ℝ ((ρ : Finset (PL.E N)) : Set (PL.E N))
    refine convexHull_min ?_ (convex_convexHull ℝ (ρ : Set (PL.E N)))
    intro v hv
    exact hρspec v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  have hxρ : x ∈ PL.simp ρ := hsub hxinter
  obtain ⟨A, hA⟩ := hlinL ρ hρ ⟨x, hxρ, hxβ⟩
  obtain ⟨As, hAs⟩ := hlin s hs
  have hagree : ∀ v ∈ frozenPart L s, As v = A v := by
    intro v hv
    obtain ⟨hvs, hvL⟩ := Finset.mem_filter.mp hv
    have h1 : ℓ v = f v := hvert s hs v hvs
    have h2 : f v = A v := hA v (hsub (subset_convexHull ℝ ((frozenPart L s : Finset (PL.E N)) : Set (PL.E N)) hv))
    have h3 : ℓ v = As v := hAs (subset_convexHull ℝ ((s : Finset (PL.E N)) : Set (PL.E N)) hvs)
    rw [← h3, h1, h2]
  have hAsA : As x = A x := by
    have hcc : x ∈ convexHull ℝ ((frozenPart L s : Finset (PL.E N)) : Set (PL.E N)) := hxinter
    exact convexHull_min (fun v hv => hagree v hv) (Interp.interp_convex_eqSet As A) hcc
  exact (hAs hxs).trans (hAsA.trans (hA x hxρ).symm)

/-- **PL approximation in a cube, frozen on a subcomplex** (blueprint §2 G5, frozen variant).

Let `K` be a finite geometric simplicial complex in `ℝᴺ`, `L ⊆ K` a subcomplex, and
`f : ℝᴺ → ℝⁿ` continuous on `K.space`.  Given `0 < α < β < 1`, `ε > 0`, a subdivision operator `S`
carried as a `Subdiv`, a compatibility `hres : RestrictsTo S K hK L` of `S` with `L`, and the
hypothesis `hlinL` that `f` is already affine on every simplex `ρ` of `L` that meets
`f⁻¹(closedCube β)`, there is an approximation `g` of `f` such that

* `g` is continuous on `K.space` and `ε`-close to `f` there,
* `g = f` outside the cube of radius `β`, and `g = f` on all of `L.space` (the *frozen* part),
* after `r` further subdivisions of `K`, every simplex on which `g` meets `closedCube α` is a
  simplex on which `g` is affine.

The construction is the one of §2 G5: pick `α < β'' < β' < β` and `ε' ≤ (β'' − α)/4, ε`; choose
`r` so that `f` oscillates by less than `ε'` on every simplex of `K' := S.iter r K` (possible by
uniform continuity of `f` on the compact `K.space`); let `ℓ` be the vertexwise-linear interpolant
of `f` on `K'` and set `g x = f x + cubeCut β'' β' (f x) • (ℓ x - f x)`.  Then `g` is `ε'`-close to
`f`, the cutoff is `1` on `f(simp s)` for every simplex `s` on which `g` meets `closedCube α`
(the bound `α + 4ε' ≤ β''`), so that `g = ℓ` is affine there; off `closedCube β` the cutoff is `0`,
and on `L` the frozen lemma `frozen_eq_of_mem` gives `ℓ = f` whenever `f` meets `closedCube β`. -/
lemma pl_approx_frozen {N n : ℕ} (S : Subdiv N) (K : PL.Cx N) (hK : K.faces.Finite) (L : PL.Cx N)
    (hLK : PL.IsSub L K) (f : PL.E N → PL.E n) (hf : ContinuousOn f K.space)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1) (ε : ℝ) (hε : 0 < ε)
    (hres : RestrictsTo S K hK L)
    (hlinL : ∀ ρ ∈ L.faces, (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z) :
    ∃ r : ℕ, ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧ (∀ x ∈ L.space, g x = f x) ∧
      ∀ s ∈ (S.iter r K hK).faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y := by
  classical
  -- the two intermediate cube radii
  set β'' := (α + β) / 2 with hβ''
  set β' := (β'' + β) / 2 with hβ'
  have hαβ'' : α < β'' := by rw [hβ'']; linarith
  have hβ''β' : β'' < β' := by rw [hβ', hβ'']; linarith
  have hβ'β : β' < β := by rw [hβ', hβ'']; linarith
  -- the accuracy demanded of the interpolant
  set ε' := min ((β'' - α) / 4) ε with hε'
  have hβ''pos : 0 < β'' := lt_trans hα hαβ''
  have hβ'1 : β' < 1 := lt_trans hβ'β hβ1
  have hβ''α : 0 < β'' - α := by linarith
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
  refine ⟨r, g, ?_, ?_, ?_, ?_, ?_⟩
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
        frozen_eq_of_mem K' L (fun s hs => hres.1 r s hs) (fun s hs => hres.2 r s hs)
          f ℓ hℓlin hℓvert hlinL hxL (by rw [hK'space]; exact hxK) hβ
      rw [hℓx, sub_self, smul_zero, add_zero]
    · rw [hcut0 x hxK hβ, zero_smul, add_zero]
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
    rw [hcut1 y hy, one_smul]
    have hℓA : ℓ y = A y := hA hy
    rw [hℓA]
    abel

/-- The unfrozen form G5 (`pl_approx`) is the special case of `pl_approx_frozen` in which the
frozen subcomplex is empty: on `⊥` every hypothesis and extra conclusion is vacuous.  Recorded so
that the sibling statement `Work.PL.Approx.pl_approx` is immediate. -/
lemma pl_approx_of_frozen {N n : ℕ} (S : Subdiv N) (K : PL.Cx N) (hK : K.faces.Finite)
    (f : PL.E N → PL.E n) (hf : ContinuousOn f K.space) (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hβ1 : β < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧
      (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧
      ∀ s ∈ (S.iter r K hK).faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y := by
  have hsub : PL.IsSub (⊥ : PL.Cx N) K := fun s hs => by
    simpa [Geometry.SimplicialComplex.faces_bot] using hs
  have hres : RestrictsTo S K hK (⊥ : PL.Cx N) := by
    refine ⟨?_, ?_⟩
    · intro r s _
      simp [frozenPart, PL.simp, Geometry.SimplicialComplex.space_bot]
    · intro r s _ h
      obtain ⟨v, _, hv⟩ := h
      simp [Geometry.SimplicialComplex.space_bot] at hv
  have hlinL : ∀ ρ ∈ (⊥ : PL.Cx N).faces,
      (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z := by
    intro ρ hρ
    simp [Geometry.SimplicialComplex.faces_bot] at hρ
  obtain ⟨r, g, hcont, hdist, hout, _hfrozen, hlin⟩ :=
    pl_approx_frozen S K hK ⊥ hsub f hf α β hα hαβ hβ1 ε hε hres hlinL
  exact ⟨r, g, hcont, hdist, hout, hlin⟩

end Work.PL.Approx
