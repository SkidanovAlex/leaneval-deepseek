import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

open Work.ORVonNeumann

/-- **The `Φ`-block lemma** (B5b of `P311_DESIGN_LEAD.md`): the diagonal inclusion
`Φ_N : N(N) → N(G)` of `Rep.exists_diagHom` is block diagonal over the right `N`-cosets, so it
preserves the set of vectors of `ℓ²(G)` supported on the coset `N * y`.

Concretely, `f` orthogonal to every `δ_g` with `g ∉ N * y` (i.e. `g` not of the form `k * y`,
`k ∈ N`) satisfies the same for `Φ_N(b) f`.

The coset `{g | ∃ k ∈ N, g = k * y}` is the right coset `N * (C.qpart y)` of the chosen coset
decomposition `C = cosetDataN N`, and `Φ_N(b)` is the diagonal operator `cosetDiagOp C b`, which
acts as `b` on the copy `C.e q (ℓ²(N))` of every right coset.  The proof therefore reduces to
(a) `f` lies in the block `C.e q (ℓ²(N))` of `q = C.qpart y` (a consequence of `hf`, since the
basis vectors in that block are exactly the `δ_g`, `g ∈ N * y`), and (b) `Φ_N(b)` preserves it. -/
theorem PhiN_mapsTo {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (N : Subgroup G) (b : ↥(Work.ORVonNeumann.groupVonNeumann ↥N)) (y : G) (f : Work.ORVonNeumann.l2 G) (hf : ∀ g : G, (¬∃ k ∈ N, g = k * y) → inner ℂ f (Work.ORVonNeumann.Rep.deltaG g) = 0) : ∀ g : G, (¬∃ k ∈ N, g = k * y) → inner ℂ (((Work.ORP311.P311.PhiN N b : ↥(Work.ORVonNeumann.groupVonNeumann G)) : Work.ORVonNeumann.boundedEnd G) f) (Work.ORVonNeumann.Rep.deltaG g) = 0 := by
  classical
  intro g hg
  let C := Work.ORP311.P311.cosetDataN N
  -- The coset `N * g` differs from `N * y`, i.e. `C.qpart g ≠ C.qpart y`.
  have hqg : C.qpart g ≠ C.qpart y := by
    refine C.qpart_ne_of_not_mem g y ?_
    intro hmem
    exact hg ⟨g * y⁻¹, hmem, by group⟩
  -- No element of the block of `g` lies in `N * y`.
  have hmem_coset : ∀ h : ↥N,
      ¬ ∃ k ∈ N, ((h : G) * ((C.qpart g : C.Q) : G)) = k * y := by
    rintro h ⟨k, hk, hk'⟩
    have e1 : C.qpart ((h : G) * ((C.qpart g : C.Q) : G)) = C.qpart g :=
      C.qpart_eq_of_mul_eq _ (h := h) (q := C.qpart g) rfl
    have e2 : C.qpart ((h : G) * ((C.qpart g : C.Q) : G)) = C.qpart y := by
      rw [hk']
      refine C.qpart_eq_of_mul_eq _ (h := (⟨k, hk⟩ : ↥N) * C.hpart y) (q := C.qpart y) ?_
      rw [Subgroup.coe_mul]
      show k * ((C.hpart y : ↥N) : G) * ((C.qpart y : C.Q) : G) = k * y
      rw [mul_assoc, C.hpart_mul_qpart y]
    exact hqg (e1.symm.trans e2)
  -- `f` is orthogonal to the whole block `C.e (C.qpart g) (ℓ²(N))`, by expansion in `{δ_h}`.
  have horth : ∀ w : l2 ↥N, inner ℂ f (C.e (C.qpart g) w) = 0 := by
    intro w
    have hterm : ∀ h : ↥N,
        inner ℂ f (inner ℂ (Rep.deltaG h) w • C.e (C.qpart g) (Rep.deltaG h)) = 0 := by
      intro h
      rw [inner_smul_right, C.e_delta]
      show inner ℂ (Rep.deltaG h) w *
        inner ℂ f (Rep.deltaG ((h : G) * ((C.qpart g : C.Q) : G))) = 0
      rw [hf _ (hmem_coset h), mul_zero]
    rw [Rep.e_apply_eq_tsum C (C.qpart g) w,
      Work.ORVonNeumann.Rep.inner_tsum_right f (Rep.summable_e C (C.qpart g) w),
      tsum_congr hterm, tsum_zero]
  -- `Φ_N` is `*`-preserving, so `(Φ_N b)† = Φ_N (star b)`, which is also block diagonal.
  have hstarval : star (((Work.ORP311.P311.PhiN N b : ↥(groupVonNeumann G)) : boundedEnd G))
      = ((Work.ORP311.P311.PhiN N (star b) : ↥(groupVonNeumann G)) : boundedEnd G) := by
    have h1 : ((Work.ORP311.P311.PhiN N (star b) : ↥(groupVonNeumann G)) : boundedEnd G)
        = ((star (Work.ORP311.P311.PhiN N b) : ↥(groupVonNeumann G)) : boundedEnd G) := by
      rw [(Work.ORP311.P311.PhiN_spec N).2.1 b]
    have h2 : ((star (Work.ORP311.P311.PhiN N b) : ↥(groupVonNeumann G)) : boundedEnd G)
        = star (((Work.ORP311.P311.PhiN N b : ↥(groupVonNeumann G)) : boundedEnd G)) := rfl
    rw [h1, h2]
  have hPhi := (Work.ORP311.P311.PhiN_spec N).2.2.2 (star b) (C.qpart g)
    (Rep.deltaG (C.hpart g))
  -- `δ_g` is the basis vector of the block `C.e (C.qpart g)`, and it lies in `N * g`.
  have hdelta : C.e (C.qpart g) (Rep.deltaG (C.hpart g)) = Rep.deltaG g := by
    rw [C.e_delta, C.hpart_mul_qpart]
  rw [← hdelta]
  -- Move the adjoint to the other side of the pairing.
  rw [← ContinuousLinearMap.adjoint_inner_right
    (((Work.ORP311.P311.PhiN N b : ↥(groupVonNeumann G)) : boundedEnd G)) f
    (C.e (C.qpart g) (Rep.deltaG (C.hpart g)))]
  rw [← ContinuousLinearMap.star_eq_adjoint, hstarval, hPhi]
  exact horth _

end Work.ORP311
