import Mathlib
import Submission.Work.Drive.Final.tls_defs
import Submission.Work.Drive.Mono.isPreconnected_frontier_inter_hyperplane_inter_halfspace
import Submission.Work.Drive.Mono.exists_frontier_mem_inter_hyperplane_inter_halfspace

/-!
# The seam is nonempty when the wall plane cuts the box (`tls_seam_caseAlpha`)

`Work.Drive.Final.tlsSeam s c σ u h lam v ℓ` is the circle along which the box sphere
`∂PBox s c σ` meets the boundary of the chunk
(`closure (PBox s c σ) ∩ {|⟪v,·⟫ - (⟪v,c⟫+u)| ≤ h} ∩ {ℓ ≤ lam}`).

The statement proved here is the *case α* of the window dichotomy: if some point `y` of the
**open** box lies on the wall and in the tilted slab,

`y ∈ PBox s c σ`,  `ℓ y = lam`,  `|⟪v,y⟫ - (⟪v,c⟫+u)| ≤ h`,

then the seam is nonempty.

The proof is a line argument.  Since `ℓ ≠ 0` and `dim ℝ³ = 3`, the two functionals `⟪v,·⟫`
and `ℓ` have a common nonzero kernel vector `u₀`
(`exists_ne_zero_ker_pair`).  The line `y + ℝ u₀` keeps both `⟪v,·⟫` and `ℓ` constant, so the
*last* point of the line inside the box (which exists because `closure (PBox s c σ)` is
compact, and which is a point of the frontier of the box) lies on the seam: it is on the box
sphere, in the closure of the box, in the slab, on the wall `{ℓ = lam}`, and hence in
`tlsSlabBdry ∪ {ℓ = lam}`.

The compactness argument is `exists_frontier_mem_inter_two_levels`, the two-hyperplane
companion of `Work.Drive.Mono.exists_frontier_mem_inter_hyperplane_inter_halfspace`.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

noncomputable section

set_option linter.unusedVariables false

/-- **Two linear functionals on `ℝ³` have a common nonzero kernel vector.**  Otherwise the map
`y ↦ (f y, g y) : ℝ³ → ℝ²` would be injective, contradicting `finrank ℝ³ = 3 > 2`.-/
lemma exists_ne_zero_ker_pair {f g : R3 →L[ℝ] ℝ} :
    ∃ u : R3, u ≠ 0 ∧ f u = 0 ∧ g u = 0 := by
  by_contra h
  have hker : LinearMap.ker (LinearMap.prod (f : R3 →ₗ[ℝ] ℝ) (g : R3 →ₗ[ℝ] ℝ)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    by_contra hu0
    have hu' : (LinearMap.prod (f : R3 →ₗ[ℝ] ℝ) (g : R3 →ₗ[ℝ] ℝ)) u = 0 := hu
    rw [LinearMap.prod_apply] at hu'
    change (f u, g u) = (0 : ℝ × ℝ) at hu'
    rw [Prod.mk_eq_zero] at hu'
    exact h ⟨u, hu0, hu'.1, hu'.2⟩
  have hinj : Function.Injective (LinearMap.prod (f : R3 →ₗ[ℝ] ℝ) (g : R3 →ₗ[ℝ] ℝ)) :=
    LinearMap.ker_eq_bot.mp hker
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℝ (R3) = 3 := by simp
  have h3 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  omega

/-- **The two-hyperplane frontier lemma.**  If `y` lies in the compact set `K`, on the two level
sets `{f = t}` and `{g = lam}`, and `u ≠ 0` is a common direction on which both functionals
vanish, then the line `y + ℝ u` meets the frontier of `K` *(the last point of the line inside
`K`)*, and at that point both `f` and `g` still have the values they have at `y`. -/
lemma exists_frontier_mem_inter_two_levels {K : Set R3} (hKcomp : IsCompact K)
    {f g : R3 →L[ℝ] ℝ} {t lam : ℝ} {y u : R3} (hyK : y ∈ K) (hyf : f y = t)
    (hyg : g y = lam) (hu : u ≠ 0) (hfu : f u = 0) (hgu : g u = 0) :
    ∃ z ∈ frontier K, f z = t ∧ g z = lam := by
  set φ : ℝ → R3 := fun s => y + s • u with hφdef
  have hφcont : Continuous φ := by rw [hφdef]; fun_prop
  set A : Set ℝ := φ ⁻¹' K with hAdef
  have hAclosed : IsClosed A := hKcomp.isClosed.preimage hφcont
  have hAne : A.Nonempty := ⟨0, by show φ 0 ∈ K; rw [hφdef]; simpa using hyK⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hKcomp.isBounded
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  -- `A` is bounded, because `K` is
  have hbdd : BddAbove A := by
    refine ⟨max 0 ((R + ‖y‖) / ‖u‖), fun s hs => ?_⟩
    rcases le_or_gt s 0 with hs0 | hs0
    · exact le_trans hs0 (le_max_left _ _)
    · have hmem : φ s ∈ K := hs
      have hnorm : ‖φ s‖ ≤ R := hR _ hmem
      have h3 : ‖s • u‖ ≤ R + ‖y‖ := by
        calc ‖s • u‖ = ‖φ s - y‖ := by rw [hφdef]; simp
          _ ≤ ‖φ s‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ R + ‖y‖ := by linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at h3
      exact le_trans ((le_div_iff₀ hu_pos).mpr h3) (le_max_right _ _)
  have hsup_mem : sSup A ∈ A := hAclosed.csSup_mem hAne hbdd
  have hle : ∀ b ∈ A, b ≤ sSup A := fun b hb => le_csSup hbdd hb
  -- the last point of the line inside `K`
  have hzK : φ (sSup A) ∈ K := hsup_mem
  have hznotint : φ (sSup A) ∉ interior K := by
    intro hint
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_interior _ hint
    set δ : ℝ := ε / (2 * ‖u‖) with hδdef
    have hδpos : 0 < δ := div_pos hε (by linarith)
    have hmem : φ (sSup A + δ) ∈ K := by
      apply interior_subset
      apply hεsub
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : φ (sSup A + δ) - φ (sSup A) = δ • u := by
        rw [hφdef]; module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos, hδdef]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [hε, hu_pos]
    have := hle _ hmem
    linarith
  refine ⟨φ (sSup A), ?_, ?_, ?_⟩
  · rw [hKcomp.isClosed.frontier_eq]
    exact ⟨hzK, hznotint⟩
  · show f (y + sSup A • u) = t
    rw [map_add, map_smul, smul_eq_mul, hfu, mul_zero, add_zero, hyf]
  · show g (y + sSup A • u) = lam
    rw [map_add, map_smul, smul_eq_mul, hgu, mul_zero, add_zero, hyg]

/-- **Case α of the window dichotomy.**  A point of the open box which lies on the wall and in
the tilted slab produces a point of the seam. -/
theorem tls_seam_caseAlpha (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (u h lam : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (hs : 0 < s) (hℓne : ℓ ≠ 0)
    (hα : ∃ y ∈ Submission.PBox s c σ, ℓ y = lam ∧
      |inner ℝ v y - (inner ℝ v c + u)| ≤ h) :
    (Work.Drive.Final.tlsSeam s c σ u h lam v ℓ).Nonempty := by
  obtain ⟨y, hyPBox, hylam, hslab⟩ := hα
  -- a direction on which both `⟪v,·⟫` and `ℓ` vanish
  obtain ⟨u₀, hu₀ne, hvu₀, hℓu₀⟩ := exists_ne_zero_ker_pair (f := innerSL ℝ v) (g := ℓ)
  -- the compact convex body: the closed box
  have hKcomp : IsCompact (closure (Submission.PBox s c σ)) := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall c ((5 / 2) * s)) isClosed_closure ?_
    refine closure_minimal ?_ Metric.isClosed_closedBall
    exact (Submission.PBox_subset_ball s (le_of_lt hs) c σ).trans Metric.ball_subset_closedBall
  -- the farthest point of the line through `y` inside the box
  obtain ⟨z, hzfr, hzf, hzg⟩ :=
    exists_frontier_mem_inter_two_levels (K := closure (Submission.PBox s c σ))
      (hKcomp := hKcomp) (f := innerSL ℝ v) (g := ℓ) (t := inner ℝ v y) (lam := lam)
      (subset_closure hyPBox) (innerSL_apply_apply ℝ v y) hylam hu₀ne hvu₀ hℓu₀
  have hzv : inner ℝ v z = inner ℝ v y := by
    rw [← innerSL_apply_apply ℝ v z]; exact hzf
  refine ⟨z, ⟨?_, ⟨⟨?_, ?_⟩, ?_⟩⟩, Or.inr hzg⟩
  · -- `z` lies on the box sphere
    rw [← Work.JordanBrouwer3.frontier_closure_PBox hs c σ]; exact hzfr
  · -- `z` lies in the closure of the box
    have h := frontier_subset_closure hzfr
    rwa [closure_closure] at h
  · -- `z` lies in the slab
    show |inner ℝ v z - (inner ℝ v c + u)| ≤ h
    rw [hzv]; exact hslab
  · -- `z` lies below the wall, indeed on it
    show ℓ z ≤ lam
    rw [hzg]

end

end Work.Drive.Final
