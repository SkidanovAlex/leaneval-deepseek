import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.lensToProj_capTorus
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece

namespace Work.Drive


open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## Auxiliary computations for the cap piece of the capping space

The statement `Work.Drive.contMDiffAt_cappingSpace_capPieceClass` is proved by unwinding the
transparent smooth structure `Work.Drive.cappingCharted` of the capping space; the two elementary
computations below are the exact cap analogues of `Work.Drive.contDiffAt_ofComplex` and
`Work.Drive.contDiffAt_confProjVecOf` of `Submission/Work/Drive/contMDiffAt_cappingSpace_configPiece.lean`
(the complex-coordinate embedding `ofComplex` is shared between the two pieces). -/

/-- **Smoothness of the sphere lift `capProjVecOf (z ·) (d ·)`.**  The vector
`capProjVecOf z d = (d · z / √2, z̄ · √(1 - ‖d‖²/2))` is smooth in `(z, d)` as long as `‖d x‖ ≤ 1`,
the only point to note being that `‖d ·‖ ^ 2 = Complex.normSq (d ·)` is a *polynomial* in the real
and imaginary parts of `d` (the norm itself is not smooth at `0`). -/
lemma contDiffAt_capProjVecOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z d : E → ℂ} {x : E} {n : WithTop ℕ∞} (hz : ContDiffAt ℝ n z x) (hd : ContDiffAt ℝ n d x)
    (hd1 : ‖d x‖ ≤ 1) :
    ContDiffAt ℝ n (fun x => capProjVecOf (z x) (d x)) x := by
  have hre : ContDiffAt ℝ n (fun x => (d x).re) x :=
    (Complex.reCLM.contDiff.contDiffAt).comp x hd
  have him : ContDiffAt ℝ n (fun x => (d x).im) x :=
    (Complex.imCLM.contDiff.contDiffAt).comp x hd
  have hnorm2 : ContDiffAt ℝ n (fun x => ‖d x‖ ^ 2) x := by
    have h := (hre.mul hre).add (him.mul him)
    have hfun : (fun x => ‖d x‖ ^ 2)
        = fun x => (d x).re * (d x).re + (d x).im * (d x).im := by
      funext x
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hfun]
    exact h
  have hinner : ContDiffAt ℝ n (fun x => 1 - ‖d x‖ ^ 2 / 2) x :=
    contDiffAt_const.sub (hnorm2.div_const 2)
  have hpos : (1 - ‖d x‖ ^ 2 / 2) ≠ 0 := by
    have := norm_nonneg (d x)
    nlinarith
  have hsqrt : ContDiffAt ℝ n (fun x => Real.sqrt (1 - ‖d x‖ ^ 2 / 2)) x :=
    (Real.contDiffAt_sqrt hpos).comp x hinner
  have hstar : ContDiffAt ℝ n (fun x => star (z x)) x :=
    (Complex.conjCLE.contDiff.contDiffAt).comp x hz
  have h1 : ContDiffAt ℝ n (fun x => d x * z x / ((Real.sqrt 2 : ℝ) : ℂ)) x :=
    (hd.mul hz).div_const _
  have h2 : ContDiffAt ℝ n
      (fun x => star (z x) * ((Real.sqrt (1 - ‖d x‖ ^ 2 / 2) : ℝ) : ℂ)) x :=
    hstar.mul ((Complex.ofRealCLM.contDiff.contDiffAt).comp x hsqrt)
  have := contDiffAt_ofComplex h1 h2
  simpa only [capProjVecOf] using this

/-- **The value of `cappingSpaceHomeoProj` on a cap piece point.**  Since `Work.Drive.Φ` sends
`(r, θ, d)` to `(r, [θ, d])` (`Work.Drive.toProdCap`), the value of
`cappingSpaceHomeoProj = Φ` followed by the slice identification `LensSpace ≃ₜ ℝP³` is
`(r, lensToProj [θ, d])`. -/
lemma cappingSpaceHomeoProj_capPiece_lens (p : ℝ × UnitAddCircle × ℂ)
    (h1 : 0 < p.1) (h2 : ‖p.2.2‖ ≤ 1) :
    cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inr (⟨p, h1, h2⟩ : CapPiece) : ConfigPiece ⊕ CapPiece))
      = (⟨p.1, h1⟩,
          lensToProj (Quotient.mk'' (Sum.inl (capTorusOf (⟨p, h1, h2⟩ : CapPiece))) :
            LensSpace)) := rfl

/-- **The sphere lift of a cap torus point**: `lensToProj` of the class of
`(θ, d) ∈ S¹ × D²` with a chosen square root `w` of `circleOf θ` is the projectivisation of the
unit vector `Work.Drive.capProjVecOf w d` (the two choices of `w` differ by a sign, i.e. by the
antipodal identification of the sphere, so the projective class is well defined). -/
lemma lensToProj_capPiece (θ : UnitAddCircle) (d : Metric.closedBall (0 : ℂ) 1) {w : ℂ}
    (hw : ‖w‖ = 1) (hc : w ^ 2 = circleOf θ) :
    lensToProj (Quotient.mk'' (Sum.inl (θ, d) : CapTorus ⊕ ConfTorus) : LensSpace)
      = Projectivization.mk ℝ (capProjVecOf w (d : ℂ))
          (capProjVecOf_ne_zero hw (norm_coe_closedBall_le_one d)) :=
  (lensToProj_capTorus θ d hc).trans (projectivizationMk_congr ℝ (Eucl 3))

end

open Manifold in
open scoped Manifold ContDiff in
/-- **Smoothness of a cap-piece map into the capping space, from a smooth sphere lift.**  For a map
`w ↦ (r w, θ w, d w)` into the cap solid torus, where `r > 0`, `d` lies in the closed unit disk and
`θ = circOf (z w ^ 2)` for a smooth **non-vanishing** `z` — i.e. `z` is a smooth *halving* of the
cap's `S¹`-coordinate (`z w ^ 2 = circleOf (θ w)`) — the class in `Work.Drive.CappingSpace` is `C^∞`
at `x₀` for the transparent smooth structure `Work.Drive.cappingCharted`
(`Submission/Work/Drive/cappingCharted.lean`).  This is the cap analogue of the proved
`Work.Drive.contMDiffAt_cappingSpace_configPiece`, which should be used as the template (the two
proofs are identical with `Sum.inl`/`ConfigPiece`/`toProdConfig`/`lensToProj_confTorus` replaced by
`Sum.inr`/`CapPiece`/`toProdCap`/`lensToProj_capTorus`).

The halving has to be carried as data: the cap coordinate of `LensSpace` is `(‖z₂‖/z₂)²`, so
`lensToProj ⟦inl (θ, d)⟧ = mk ℝ (capProjVecOf z d) ⋯` for `z ^ 2 = circleOf θ`
(`Work.Drive.lensToProj_capTorus`), and no continuous choice of `z` as a function of `θ` exists.
For the cap cone `Work.Drive.capConePt r₀ ρ Ψ Θ u s t` the required halving is
`z (s,t) = w₀ * circleOf (s * (Θ t - Θ 0) / 2)` with a constant `w₀` satisfying
`w₀ ^ 2 = circleOf (Θ 0 + u)` (the identity `circOf ((w₀ * circleOf (s * δ / 2)) ^ 2) =
(Θ 0 + s * δ) + u` is the proved `Work.Drive.circOf_half_sq`), together with
`d (s,t) = s * circleOf (Ψ t)` and `r (s,t) = (1 - s) * r₀ + s * ρ t`; so this statement, with the
smooth capping data `Work.Drive.exists_smooth_cap_data`, turns the cap cone into a smooth chain.

Route: `Work.Drive.chartedStructure_contMDiffWithinAt` reduces smoothness into
`(CappingSpace, cappingCharted)` to smoothness of the composite with
`Work.Drive.cappingSpaceHomeoProj`, whose cap-piece value is `(⟨r w, ⋯⟩, lensToProj ⟦inl (θ w, d w)⟧)`
(`Work.Drive.toProdCap`); then `Work.Drive.lensToProj_capTorus` evaluates the second component as
`mk ℝ (capProjVecOf (z w) (d w)) ⋯` (using `circleOf (circOf (z w ^ 2)) = z w ^ 2`), smooth by
`Work.Drive.contMDiffAt_projMk` because `capProjVecOf (z w) (d w)` never vanishes (its second complex
coordinate is `star (z w) * √(1 - ‖d w‖²/2)` with `‖z w‖ = 1`); the first component is smooth in
`(0,∞)` because `r` is smooth and positive, and the product and the model change
(`Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel`) finish. -/
theorem contMDiffAt_cappingSpace_capPieceClass {k : ℕ}
    (r : EuclideanSpace ℝ (Fin k) → ℝ) (z : EuclideanSpace ℝ (Fin k) → ℂ)
    (d : EuclideanSpace ℝ (Fin k) → ℂ) (x₀ : EuclideanSpace ℝ (Fin k))
    (hr : ∀ w, 0 < r w) (hd : ∀ w, ‖d w‖ ≤ 1) (hz : ∀ w, ‖z w‖ = 1)
    (hrs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀)
    (hzs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) z x₀)
    (hds : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) d x₀) :
    letI := Work.Drive.cappingCharted
    ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (Quotient.mk'' (Sum.inr (⟨(r w, Work.Drive.circOf (z w ^ 2)
        (by rw [norm_pow, hz w]; norm_num), d w), hr w, hd w⟩ : Work.Drive.CapPiece) :
          Work.Drive.ConfigPiece ⊕ Work.Drive.CapPiece) : Work.Drive.CappingSpace)) x₀ := by
  -- the transparent structures entering the definition of `halfLineProjectiveCharted`
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  -- the map of the statement
  let F : EuclideanSpace ℝ (Fin k) → CappingSpace := fun w =>
    (Quotient.mk'' (Sum.inr (⟨(r w, circOf (z w ^ 2)
      (by rw [norm_pow, hz w]; norm_num), d w), hr w, hd w⟩ : CapPiece) :
        ConfigPiece ⊕ CapPiece) : CappingSpace)
  -- its composite with the homeomorphism onto `(0,∞) × ℝP³`
  let g : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  -- the explicit value of `cappingSpaceHomeoProj` on the cap piece
  have hgcap : ∀ w, cappingSpaceHomeoProj (F w) = (⟨r w, hr w⟩,
      lensToProj (Quotient.mk'' (Sum.inl
        (capTorusOf (⟨(r w, circOf (z w ^ 2) (by rw [norm_pow, hz w]; norm_num), d w),
          hr w, hd w⟩ : CapPiece)) : CapTorus ⊕ ConfTorus) : LensSpace)) := fun w =>
    cappingSpaceHomeoProj_capPiece_lens
      (r w, circOf (z w ^ 2) (by rw [norm_pow, hz w]; norm_num), d w) (hr w) (hd w)
  -- step 1: transport along `cappingSpaceHomeoProj`
  have hchart : (letI := Work.Drive.cappingCharted
        ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀) ↔
      ContMDiffAt (𝓡 k) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀ := by
    have hiff := chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k))
      (𝓡 k)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      cappingSpaceHomeoProj.symm F Set.univ x₀
    exact hiff
  -- step 2: split the two components of `(0,∞) × ℝP³`
  have hfirst : ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => expHomeo.symm (g w).1) x₀ := by
    have hg1 : ∀ w, (g w).1 = (⟨r w, hr w⟩ : Set.Ioi (0:ℝ)) := fun w =>
      congrArg Prod.fst (hgcap w)
    have hcomp : (fun w => expHomeo.symm (g w).1)
        = fun w => expHomeo.symm ⟨r w, hr w⟩ := by
      funext w
      rw [hg1 w]
    rw [hcomp]
    exact contMDiffAt_expHomeo_symm hr x₀ hrs
  have hsecond : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (g w).2) x₀ := by
    have hg2 : ∀ w, (g w).2 = Projectivization.mk ℝ (capProjVecOf (z w) (d w))
        (capProjVecOf_ne_zero (hz w) (hd w)) := fun w =>
      (congrArg Prod.snd (hgcap w)).trans
        (lensToProj_capPiece (circOf (z w ^ 2) (by rw [norm_pow, hz w]; norm_num))
          (⟨d w, mem_closedBall_of_norm_le_one (hd w)⟩ : Metric.closedBall (0:ℂ) 1)
          (hz w) (circleOf_circOf (z w ^ 2) (by rw [norm_pow, hz w]; norm_num)).symm)
    have hcomp : (fun w => (g w).2)
        = fun w => Projectivization.mk ℝ (capProjVecOf (z w) (d w))
            (capProjVecOf_ne_zero (hz w) (hd w)) := funext hg2
    rw [hcomp]
    exact contMDiffAt_projMk (fun w => capProjVecOf (z w) (d w))
      (fun w => capProjVecOf_ne_zero (hz w) (hd w)) x₀
      (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_capProjVecOf
        (E := EuclideanSpace ℝ (Fin k)) (z := z) (d := d) (x := x₀)
        hzs.contDiffAt hds.contDiffAt (hd x₀)))
  have hhl := contMDiffAt_halfLineProjective_iff g x₀
  have hgoal := hhl.mpr ⟨hfirst, hsecond⟩
  exact hchart.mpr hgoal

end Work.Drive
