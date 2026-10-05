import Mathlib
import Submission.Work.RPB.B1a.Defs
import Submission.Work.RPB.Port.Drive.signed_jump_at_point
import Submission.Work.RPB.Port.Drive.CurveRatioAux
import Submission.Work.RPB1a.exists_smooth_embedding_descend

/-!
# Points of the curve on the two sides of a smooth loop lie in different components

Let `v : ℝ → ℂ` be a smooth immersed `2π`-periodic loop which is injective modulo `2π`
(`Work.RPB.B1a.IsSmoothLoop`).  At any parameter `t₀` and for all sufficiently small `ε > 0`, the two
points

`v t₀ ± ε • (I * deriv v t₀)`

of the normal line of the curve at `v t₀` lie off the curve (`∈ (Set.range v)ᶜ`) and in *different*
path components of the complement of the curve (`pathComponentIn`).

The mathematical content is classical: `v` is a Jordan curve, its complement has exactly two path
components (the two sides of the curve), and the two normal offsets fall on opposite sides.  The
route taken here is the winding-number one, which avoids proving the Jordan separation statement for
`Set.range v` directly:

* `Work.RPB1a.exists_smooth_embedding_descend` descends `v` to a smooth embedding `γ : Circle → ℝ×ℝ`
  of the circle, whose range is the image of `Set.range v` under the linear homeomorphism
  `rp = Complex.equivRealProdCLM : ℂ ≃ ℝ × ℝ`;
* `Work.RPB.Port.Drive.signed_jump_at_point` computes that the winding numbers of the two normal
  points differ by `2`, and that both points are off the curve;
* `Work.RPB.Port.Drive.windG_preconnected` says the winding number is constant on a path connected
  subset of the complement, so the two points cannot be joined inside the complement.
-/

namespace Work.RPB.B1a

open Set Metric
open scoped ContDiff

/-- The linear homeomorphism identifying `ℂ` with `ℝ × ℝ`, matching the coordinate convention
`cpx` of `Work.RPB.Port.Drive`. -/
private noncomputable abbrev rp : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM

/-- **The winding number is constant on a path-connected piece of the complement of the curve.**

If `q` and `q'` lie off the smooth closed plane curve `γ` and can be joined by a path avoiding
`γ`, then the winding number of `γ` about them is the same.  This is
`Work.RPB.Port.Drive.windG_preconnected` with the path-connectedness hypothesis resolved along a path
witnessing `JoinedIn`. -/
lemma windG_eq_of_joinedIn_compl {γ : Circle → ℝ × ℝ} (hγ : Continuous γ)
    {q q' : ℝ × ℝ} (hq : q ∉ Set.range γ) (hq' : q' ∉ Set.range γ)
    (h : JoinedIn ((Set.range γ)ᶜ) q q') :
    Work.RPB.Port.Drive.windG γ hγ hq = Work.RPB.Port.Drive.windG γ hγ hq' := by
  obtain ⟨P, hP⟩ := h
  have hP' : ∀ t : unitInterval, P t ∈ (Set.range γ)ᶜ := hP
  have hC : Set.range (P : unitInterval → ℝ × ℝ) ⊆ (Set.range γ)ᶜ :=
    Set.range_subset_iff.mpr hP'
  have hconn : IsPreconnected (Set.range (P : unitInterval → ℝ × ℝ)) :=
    isPreconnected_range P.continuous
  have hqC : q ∈ Set.range (P : unitInterval → ℝ × ℝ) := Set.mem_range.mpr ⟨0, P.source⟩
  have hq'C : q' ∈ Set.range (P : unitInterval → ℝ × ℝ) := Set.mem_range.mpr ⟨1, P.target⟩
  have hres := Work.RPB.Port.Drive.windG_preconnected
    (C := Set.range (P : unitInterval → ℝ × ℝ)) hγ hC hconn
    (q := ⟨q, hqC⟩) (q' := ⟨q', hq'C⟩)
  rw [show hC hq'C = hq' from Subsingleton.elim _ _,
    show hC hqC = hq from Subsingleton.elim _ _] at hres
  exact hres.symm

/-- Rotation of a complex number by `I` corresponds to `rot90` under `rp`. -/
private lemma rp_I_mul (w : ℂ) : rp (Complex.I * w) = Work.RPB.Port.Drive.rot90 (rp w) := by
  simp [rp, Complex.equivRealProdCLM_apply, Work.RPB.Port.Drive.rot90, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]

theorem normal_points_different_component (v : ℝ → ℂ) (hv : Work.RPB.B1a.IsSmoothLoop v) (t₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      v t₀ + (ε : ℂ) * (Complex.I * deriv v t₀) ∈ (Set.range v)ᶜ ∧
      v t₀ - (ε : ℂ) * (Complex.I * deriv v t₀) ∈ (Set.range v)ᶜ ∧
      pathComponentIn (Set.range v)ᶜ (v t₀ + (ε : ℂ) * (Complex.I * deriv v t₀)) ≠
        pathComponentIn (Set.range v)ᶜ (v t₀ - (ε : ℂ) * (Complex.I * deriv v t₀)) := by
  obtain ⟨hvd, hper, hinj, himm⟩ := hv
  -- Descend the loop to a smooth embedding of the circle.
  obtain ⟨γ, hemb, -, -, hγexp, hrange⟩ :=
    Work.RPB1a.exists_smooth_embedding_descend v ⟨hvd, hper, hinj, himm⟩
  have hcont : Continuous γ := hemb.isEmbedding.continuous
  have hcurve : Work.RPB.Port.Drive.curve γ t₀ = rp (v t₀) := hγexp t₀
  -- The derivative of the descended curve is `rp` of the derivative of `v`.
  have hderiv : deriv (Work.RPB.Port.Drive.curve γ) t₀ = rp (deriv v t₀) := by
    have hfun : Work.RPB.Port.Drive.curve γ = fun t => rp (v t) := funext hγexp
    rw [hfun]
    have hU : HasDerivAt v (deriv v t₀) t₀ :=
      ((hvd.differentiable (by simp)).differentiableAt).hasDerivAt
    have hder : HasDerivAt (fun s : ℝ => rp (v s)) (rp (deriv v t₀)) t₀ := by
      have h1 := (rp : ℂ →L[ℝ] ℝ × ℝ).hasFDerivAt.comp_hasDerivAt t₀ hU
      simpa [Function.comp_def] using h1
    exact hder.deriv
  -- The signed jump of the winding number at `t₀`.
  obtain ⟨δ, hδpos, hjump⟩ := Work.RPB.Port.Drive.signed_jump_at_point γ hemb t₀
  refine ⟨δ, hδpos, fun ε hε hεδ => ?_⟩
  obtain ⟨hne_pos, hne_neg, hwind⟩ := hjump ε hε hεδ
  -- The images under `rp` of the two normal offsets.
  have hsmul : (ε : ℂ) * (Complex.I * deriv v t₀) = ε • (Complex.I * deriv v t₀) :=
    (Complex.real_smul (x := ε) (z := Complex.I * deriv v t₀)).symm
  have he_pos : rp (v t₀ + (ε : ℂ) * (Complex.I * deriv v t₀))
      = Work.RPB.Port.Drive.curve γ t₀
        + ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀) := by
    rw [hsmul, map_add, map_smul, rp_I_mul, ← hderiv, ← hcurve]
  have he_neg : rp (v t₀ - (ε : ℂ) * (Complex.I * deriv v t₀))
      = Work.RPB.Port.Drive.curve γ t₀
        - ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀) := by
    rw [hsmul, map_sub, map_smul, rp_I_mul, ← hderiv, ← hcurve]
  -- Both points lie off the curve.
  have hp_pos : Work.RPB.Port.Drive.curve γ t₀
      + ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀)
      ∉ Set.range γ := by
    rw [← Work.RPB.Port.Drive.range_curve γ]
    rintro ⟨t, ht⟩
    exact hne_pos t ht
  have hp_neg : Work.RPB.Port.Drive.curve γ t₀
      - ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀)
      ∉ Set.range γ := by
    rw [← Work.RPB.Port.Drive.range_curve γ]
    rintro ⟨t, ht⟩
    exact hne_neg t ht
  -- Hence the offsets themselves lie off the loop.
  have hmem_pos : v t₀ + (ε : ℂ) * (Complex.I * deriv v t₀) ∉ Set.range v := by
    rintro ⟨t, ht⟩
    have h1 : Work.RPB.Port.Drive.curve γ t₀
        + ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀)
        = Work.RPB.Port.Drive.curve γ t := by
      rw [← he_pos, ← ht]
      exact (hγexp t).symm
    exact hp_pos (by rw [← Work.RPB.Port.Drive.range_curve γ]; exact ⟨t, h1.symm⟩)
  have hmem_neg : v t₀ - (ε : ℂ) * (Complex.I * deriv v t₀) ∉ Set.range v := by
    rintro ⟨t, ht⟩
    have h1 : Work.RPB.Port.Drive.curve γ t₀
        - ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀)
        = Work.RPB.Port.Drive.curve γ t := by
      rw [← he_neg, ← ht]
      exact (hγexp t).symm
    exact hp_neg (by rw [← Work.RPB.Port.Drive.range_curve γ]; exact ⟨t, h1.symm⟩)
  -- The image of the complement of the loop is the complement of the curve.
  have himage : rp '' (Set.range v)ᶜ = (Set.range γ)ᶜ := by
    rw [hrange]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
      exact hy (rp.injective hzy ▸ hz)
    · intro hx
      refine ⟨rp.symm x, ?_, rp.apply_symm_apply x⟩
      rintro ⟨z, hz⟩
      exact hx ⟨v z, ⟨z, rfl⟩, by rw [hz, rp.apply_symm_apply]⟩
  refine ⟨hmem_pos, hmem_neg, ?_⟩
  -- The two points cannot lie in the same path component: the winding numbers differ.
  intro heqcomp
  have hjoin_v : JoinedIn ((Set.range v)ᶜ)
      (v t₀ + (ε : ℂ) * (Complex.I * deriv v t₀))
      (v t₀ - (ε : ℂ) * (Complex.I * deriv v t₀)) := by
    have hm : v t₀ + (ε : ℂ) * (Complex.I * deriv v t₀)
        ∈ pathComponentIn ((Set.range v)ᶜ) (v t₀ - (ε : ℂ) * (Complex.I * deriv v t₀)) := by
      rw [← heqcomp]
      exact mem_pathComponentIn_self hmem_pos
    exact hm.symm
  have hjoin_g : JoinedIn ((Set.range γ)ᶜ)
      (Work.RPB.Port.Drive.curve γ t₀
        + ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀))
      (Work.RPB.Port.Drive.curve γ t₀
        - ε • Work.RPB.Port.Drive.rot90 (deriv (Work.RPB.Port.Drive.curve γ) t₀)) := by
    have h1 := JoinedIn.map hjoin_v rp.continuous.continuousOn
    rw [himage, he_pos, he_neg] at h1
    exact h1
  have hEq : Work.RPB.Port.Drive.windE γ hemb hp_pos
      = Work.RPB.Port.Drive.windE γ hemb hp_neg :=
    windG_eq_of_joinedIn_compl hcont hp_pos hp_neg hjoin_g
  have hJump := hwind hp_pos hp_neg
  omega

end Work.RPB.B1a
