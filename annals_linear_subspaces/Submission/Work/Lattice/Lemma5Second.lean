import Mathlib
import Submission.GeometryOfNumbers.WedgeBlockZero
import Submission.Work.Lattice.WedgeProjection
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_le_pow_of_dist_le_subspace

/-!
# Lemma 5 (second assertion): extending an orthonormal family with a large `π₊`-wedge

Coordinate model: `ℝᵈ = EuclideanSpace ℝ (Fin d)`, `x₀ = modelX ℓ = span {e_j | j.val < ℓ}`,
`P := modelProj ℓ` the orthogonal projection onto `x₀`, and `π₊ = ⋀^• P` the projection onto
the "all contracting" block (in the block notation of `Submission.ExteriorCoordinates`,
`π₊ = blockElem · 0`).

**Lemma 5, second assertion** (de Saxcé, §3).  Let `s < i`, let `v : Fin s → ℝᵈ` be a family
whose `π₊`-wedge is almost as large as its wedge,
`ε ‖v₁∧…∧v_s‖ ≤ ‖P v₁∧…∧P v_s‖`, and let `u : Fin i → ℝᵈ` be an orthonormal family with
`ε ≤ ‖P u₁∧…∧P u_i‖`.  Then some `k` makes `π₊` almost norm-preserving on
`v₁∧…∧v_s ∧ u_k`:
`ε γ ‖v₁∧…∧v_s ∧ u_k‖ ≤ ‖P v₁∧…∧P v_s ∧ P u_k‖`
for any `γ > 0` with `γ ≤ 1` and `2^i γ^{i-s} ≤ ε`.

Proof (as in the paper, made quantitative): put `U := span(P v₁,…,P v_s)`, of rank `≤ s < i`.
If every `P u_k` were within `γ` of `U`, then (pigeonhole sub-lemma
`norm_iMulti_le_pow_of_dist_le_subspace`) the wedge `P u₁∧…∧P u_i` would have norm
`≤ 2^i γ^{i-``rank U``} ≤ 2^i γ^{i-s} ≤ ε`, contradiction.  So some `k` has
`dist(P u_k, U) ≥ γ`; then

`‖P v₁∧…∧P v_s ∧ P u_k‖ = ‖P v₁∧…∧P v_s‖ · dist(P u_k, U) ≥ ε‖v₁∧…∧v_s‖γ`

(the exact wedge/`Fin.snoc` identity `norm_iMulti_snoc_eq_mul_dist`), while on the other side
`‖v₁∧…∧v_s ∧ u_k‖ ≤ ‖v₁∧…∧v_s‖` (Hadamard, `norm_iMulti_snoc_le_mul_norm`, using
`‖u_k‖ = 1`).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeBlocks
open Submission.WedgeBlockZero

namespace Submission.Lemma5Second

variable {d : ℕ}

/-- The projection onto `x₀` is a contraction. -/
lemma norm_modelProj_le (ℓ : ℕ) (x : RD d) : ‖modelProj ℓ x‖ ≤ ‖x‖ := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection x (modelX ℓ)
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [h]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The span of `n` vectors has dimension at most `n`. -/
lemma starProjection_orthogonal_eq_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x : E) :
    Kᗮ.starProjection x = x - K.starProjection x := by
  have h := congrArg (fun f : E →L[ℝ] E => f x)
    (Submodule.starProjection_orthogonal (𝕜 := ℝ) K)
  simpa using h.symm

lemma finrank_span_range_le {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ} (f : Fin n → E) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range f)) ≤ n := by
  haveI : Fintype (Set.range f) := (Set.finite_range f).fintype
  have h := finrank_span_le_card (R := ℝ) (Set.range f)
  rw [← Set.ncard_eq_toFinset_card'] at h
  have h2 : (Set.range f).ncard ≤ n := by
    have hle := Set.ncard_image_le (s := (Set.univ : Set (Fin n))) (f := f) Set.finite_univ
    simpa [Set.image_univ, Set.ncard_univ, Nat.card_eq_fintype_card] using hle
  exact le_trans h h2

/-- **Pigeonhole**: if `i` vectors of norm `≤ 1` have a large exterior product and
`s < i`, then one of them is at distance `≥ γ` from any subspace `U` of rank `≤ s`. -/
lemma exists_dist_ge {i s : ℕ} (hsi : s < i) (y : Fin i → RD d) (hy : ∀ k, ‖y k‖ ≤ 1)
    (U : Submodule ℝ (RD d)) (hU : Module.finrank ℝ U ≤ s)
    {ε γ : ℝ} (hε : 0 < ε) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγε : (2 : ℝ) ^ i * γ ^ (i - s) < ε)
    (hbig : ε ≤ ‖exteriorPower.ιMulti ℝ i y‖) :
    ∃ k : Fin i, γ ≤ ‖y k - U.starProjection (y k)‖ := by
  classical
  by_contra h
  push_neg at h
  have hdist : ∀ k, ∃ p ∈ U, ‖y k - p‖ ≤ γ := by
    intro k
    exact ⟨U.starProjection (y k), Submodule.starProjection_apply_mem U (y k),
      le_of_lt (h k)⟩
  have hbound := Commons.Analysis.InnerProductSpace.norm_iMulti_le_pow_of_dist_le_subspace
    (s := Module.finrank ℝ U) U rfl y hy hγ0.le hγ1 hdist
  have hexp : (i - s : ℕ) ≤ i - Module.finrank ℝ U := by omega
  have hpow : γ ^ (i - Module.finrank ℝ U) ≤ γ ^ (i - s) :=
    pow_le_pow_of_le_one hγ0.le hγ1 hexp
  have h2 : (2 : ℝ) ^ i * γ ^ (i - Module.finrank ℝ U) < ε :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow (by positivity)) hγε
  linarith

/-- **Lemma 5, second assertion** (de Saxcé, §3): an orthonormal family of the type produced by
the first assertion can be used to *extend* a family whose `π₊`-wedge is already large, keeping
the `π₊`-wedge large. -/
theorem lemma5_second_assertion {d : ℕ} (P : RD d →ₗ[ℝ] RD d) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (s i : ℕ) (hsi : s < i)
    (v : Fin s → RD d) (u : Fin i → RD d) (hu : Orthonormal ℝ u)
    {ε γ : ℝ} (hε : 0 < ε) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγε : (2 : ℝ) ^ i * γ ^ (i - s) < ε)
    (hbig : ε ≤ ‖exteriorPower.ιMulti ℝ i (fun k => P (u k))‖)
    (hπ : ε * ‖exteriorPower.ιMulti ℝ s v‖ ≤
        ‖exteriorPower.ιMulti ℝ s (fun k => P (v k))‖) :
    ∃ k : Fin i, γ ≤ ‖P (u k) -
        (Submodule.span ℝ (Set.range fun k : Fin s => P (v k))).starProjection (P (u k))‖ ∧
      ε * γ * ‖exteriorPower.ιMulti ℝ (s + 1) (Fin.snoc v (u k))‖ ≤
      ‖exteriorPower.ιMulti ℝ (s + 1)
        (Fin.snoc (fun k => P (v k)) (P (u k)))‖ := by
  classical
  have hUle : Module.finrank ℝ
      (Submodule.span ℝ (Set.range fun k : Fin s => P (v k))) ≤ s :=
    finrank_span_range_le _
  obtain ⟨k, hk⟩ := exists_dist_ge (d := d) hsi (fun k : Fin i => P (u k))
    (fun k => (hP (u k)).trans (le_of_eq (hu.norm_eq_one k)))
    (Submodule.span ℝ (Set.range fun k : Fin s => P (v k))) hUle
    hε hγ0 hγ1 hγε hbig
  refine ⟨k, hk, ?_⟩
  have hD : ‖exteriorPower.ιMulti ℝ (s + 1) (Fin.snoc v (u k))‖ ≤
      ‖exteriorPower.ιMulti ℝ s v‖ := by
    have h := Submission.WedgeProjection.norm_iMulti_snoc_le_mul_norm (d := d) v (u k)
    rwa [hu.norm_eq_one k, mul_one] at h
  have hN : ‖exteriorPower.ιMulti ℝ s (fun k : Fin s => P (v k))‖ * γ ≤
      ‖exteriorPower.ιMulti ℝ (s + 1)
        (Fin.snoc (fun k : Fin s => P (v k)) (P (u k)))‖ := by
    rw [Submission.WedgeProjection.norm_iMulti_snoc_eq_mul_dist
      (d := d) (fun k : Fin s => P (v k)) (P (u k))]
    exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)
  calc ε * γ * ‖exteriorPower.ιMulti ℝ (s + 1) (Fin.snoc v (u k))‖
      ≤ ε * γ * ‖exteriorPower.ιMulti ℝ s v‖ :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = γ * (ε * ‖exteriorPower.ιMulti ℝ s v‖) := by ring
    _ ≤ γ * ‖exteriorPower.ιMulti ℝ s (fun k : Fin s => P (v k))‖ :=
        mul_le_mul_of_nonneg_left hπ hγ0.le
    _ = ‖exteriorPower.ιMulti ℝ s (fun k : Fin s => P (v k))‖ * γ := by ring
    _ ≤ ‖exteriorPower.ιMulti ℝ (s + 1)
          (Fin.snoc (fun k : Fin s => P (v k)) (P (u k)))‖ := hN

/-- The `π₊ = ⋀^•(modelProj ℓ)` form of the second assertion. -/
theorem lemma5_second_assertion_modelProj {d : ℕ} (ℓ s i : ℕ) (hsi : s < i)
    (v : Fin s → RD d) (u : Fin i → RD d) (hu : Orthonormal ℝ u)
    {ε γ : ℝ} (hε : 0 < ε) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγε : (2 : ℝ) ^ i * γ ^ (i - s) < ε)
    (hbig : ε ≤ ‖exteriorPower.ιMulti ℝ i (fun k => modelProj ℓ (u k))‖)
    (hπ : ε * ‖exteriorPower.ιMulti ℝ s v‖ ≤
        ‖exteriorPower.ιMulti ℝ s (fun k => modelProj ℓ (v k))‖) :
    ∃ k : Fin i, ε * γ * ‖exteriorPower.ιMulti ℝ (s + 1) (Fin.snoc v (u k))‖ ≤
      ‖exteriorPower.ιMulti ℝ (s + 1)
        (Fin.snoc (fun k => modelProj ℓ (v k)) (modelProj ℓ (u k)))‖ :=
  (lemma5_second_assertion (modelProj ℓ) (fun x => norm_modelProj_le ℓ x) s i hsi v u hu
    hε hγ0 hγ1 hγε hbig hπ).imp (fun k hk => hk.2)

/-- The cone-ratio form of the second assertion (drop the pigeonhole component). -/
theorem lemma5_second_assertion' {d : ℕ} (P : RD d →ₗ[ℝ] RD d) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (s i : ℕ) (hsi : s < i)
    (v : Fin s → RD d) (u : Fin i → RD d) (hu : Orthonormal ℝ u)
    {ε γ : ℝ} (hε : 0 < ε) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγε : (2 : ℝ) ^ i * γ ^ (i - s) < ε)
    (hbig : ε ≤ ‖exteriorPower.ιMulti ℝ i (fun k => P (u k))‖)
    (hπ : ε * ‖exteriorPower.ιMulti ℝ s v‖ ≤
        ‖exteriorPower.ιMulti ℝ s (fun k => P (v k))‖) :
    ∃ k : Fin i, ε * γ * ‖exteriorPower.ιMulti ℝ (s + 1) (Fin.snoc v (u k))‖ ≤
      ‖exteriorPower.ιMulti ℝ (s + 1)
        (Fin.snoc (fun k => P (v k)) (P (u k)))‖ :=
  (lemma5_second_assertion P hP s i hsi v u hu hε hγ0 hγ1 hγε hbig hπ).imp
    (fun k hk => hk.2)

end Submission.Lemma5Second
