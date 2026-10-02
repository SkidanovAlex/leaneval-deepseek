import Mathlib
import Submission.Work.Tubular.Gauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A continuous map of Thom spaces that is `∞` off the tube fixes `∞`

Let `E : V ↪ ℝ^{8+k}` be an embedding of a closed oriented smooth `8`-manifold, `C` a tube chart of
radius `ε` (`Work.Tubular.TubeChart`), and

`g : OnePoint (Euc (8+k)) ⟶ OnePoint (NormalTotal E)`

a continuous map of the two one-point compactifications which sends every point *outside the open
tube* `C.openTube` to the point at infinity.  Then `g` fixes `∞`:

`g ∞ = ∞`.

The point is that the complement of the tube is "unbounded": the tube is contained in the box
`|y i| < R` (`Work.Tubular.TubeChart.exists_box`), so the points `n • v` (`v` the `j₀`-th standard
basis vector of length `R+1`) stay outside the tube for all large `n`, while their norms tend to
`∞`.  Hence `∞` lies in the closure of `some '' {y | y ∉ C.openTube}`, the image of that set under
`g` is contained in `{∞}` (by hypothesis), and continuity transports the closure:

`g ∞ ∈ closure (g '' (some '' {y | y ∉ C.openTube})) ⊆ closure {∞} = {∞}`.
-/

open Set Filter Topology

namespace Work.ThomBordism

theorem tubeGen_gInfty {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty) :
    g OnePoint.infty = OnePoint.infty := by
  -- the tube sits inside a coordinate box
  obtain ⟨R, hR, hbox⟩ := C.exists_box
  obtain ⟨j₀⟩ : Nonempty (Fin (8 + k)) := ⟨⟨0, by omega⟩⟩
  set a : ℝ := R + 1 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set v : Work.Tubular.Euc (8 + k) := EuclideanSpace.single j₀ a with hv
  have hvj : v j₀ = a := by rw [hv]; simp
  have hnorm : ∀ n : ℕ, ‖(n : ℝ) • v‖ = (n : ℝ) * a := by
    intro n
    rw [hv, norm_smul, PiLp.norm_single]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha0,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  -- the multiples `n • v` are outside the open tube as soon as they are long enough
  have hSn : ∀ n : ℕ, R + 2 < (n : ℝ) * a → ((n : ℝ) • v) ∉ C.openTube := by
    intro n hn hnmem
    rcases hnmem with ⟨p, hp, hpy⟩
    have h2 : ((n : ℝ) • v) ∈ C.U := hpy ▸ C.mem_U p (le_of_lt hp)
    have h3 := hbox _ h2 j₀
    have h4 : (((n : ℝ) • v) : Work.Tubular.Euc (8 + k)) j₀ = (n : ℝ) * a := by
      rw [hv]; simp [PiLp.smul_apply, smul_eq_mul]
    rw [h4] at h3
    obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
    linarith
  -- hence `∞` is in the closure of (the image of) the complement of the tube
  have hcl : OnePoint.infty ∈ closure (OnePoint.some ''
      {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube}) := by
    rw [mem_closure_iff]
    intro t ht hxt
    have ht' : t ∈ 𝓝 (OnePoint.infty : OnePoint (Work.Tubular.Euc (8 + k))) :=
      ht.mem_nhds hxt
    obtain ⟨K, ⟨hKc, hKcomp⟩, hKsub⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp ht'
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : Work.Tubular.Euc (8 + k))).mp hKcomp.isBounded
    obtain ⟨n, hn⟩ : ∃ n : ℕ, max R' (R + 2) < (n : ℝ) * a := by
      obtain ⟨n, hn⟩ := exists_nat_gt (max R' (R + 2) / a)
      refine ⟨n + 1, ?_⟩
      have h1 : max R' (R + 2) / a < (n : ℝ) + 1 := by
        have : (n : ℝ) < (n : ℝ) + 1 := by linarith
        linarith
      have h2 : (max R' (R + 2) / a) * a = max R' (R + 2) := div_mul_cancel₀ _ (ne_of_gt ha0)
      have h3 : (max R' (R + 2) / a) * a < ((n : ℝ) + 1) * a :=
        mul_lt_mul_of_pos_right h1 ha0
      have h4 : (((n : ℝ) + 1) * a) = ((n + 1 : ℕ) : ℝ) * a := by push_cast; ring
      rw [h2] at h3
      rw [h4] at h3
      linarith
    have hKmem : ((n : ℝ) • v) ∉ K := by
      intro hmem
      have h1 : ((n : ℝ) • v) ∈ Metric.closedBall (0 : Work.Tubular.Euc (8 + k)) R' := hR' hmem
      rw [Metric.mem_closedBall, dist_zero_right, hnorm n] at h1
      linarith [le_max_left R' (R + 2)]
    exact ⟨OnePoint.some ((n : ℝ) • v), hKsub (Or.inl ⟨_, hKmem, rfl⟩),
      ⟨_, hSn n (lt_of_le_of_lt (le_max_right R' (R + 2)) hn), rfl⟩⟩
  have himg : g '' (OnePoint.some '' {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube})
      ⊆ {OnePoint.infty} := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact hg y hy
  have h1 : g OnePoint.infty ∈ closure
      (g '' (OnePoint.some '' {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube})) :=
    image_closure_subset_closure_image g.continuous ⟨OnePoint.infty, hcl, rfl⟩
  have h2 : closure (g '' (OnePoint.some '' {y : Work.Tubular.Euc (8 + k) | y ∉ C.openTube}))
      ⊆ {OnePoint.infty} := isClosed_singleton.closure_subset_iff.mpr himg
  exact h2 h1

end Work.ThomBordism
