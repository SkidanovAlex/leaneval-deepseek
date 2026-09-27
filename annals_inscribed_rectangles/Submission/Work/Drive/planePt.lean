import Mathlib
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece
import Submission.Work.Drive.contMDiffAt_cappingSpace_capPieceClass
import Submission.Work.Drive.cappingSpaceHomeoProj_capPiece
import Submission.Work.Drive.capLift_reflect
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.chartedStructure_contMDiffWithinAt

/-!
# The unified plane point of the capping space

A presentation of the capped plane `P = M ∪ cap` as *one* smooth map has to cross the gluing torus
(the common boundary of the configuration piece and the cap piece), i.e. it has to describe, with a
single smooth formula, a point of the configuration piece for `‖d‖ < 1` and a point of the cap piece
for `‖d‖ > 1` (`d` the disk coordinate).  Neither `Quotient.mk'' (Sum.inl ·)` nor
`Quotient.mk'' (Sum.inr ·)` alone can do that — the two sides lie in different pieces — so the plane
has to be presented through the transparent coordinates
`Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³`.

This file provides that presentation:

* `Work.Drive.planePt u r hr d hu hv` — the point of the capping space with capping radius `r` whose
  projective class is that of the configuration sphere lift `Work.Drive.confProjVecOf u d`
  (`Submission/Work/Drive/cappingProjCoords.lean`);
* `Work.Drive.planePt_eq_confPiece` — for `‖d‖ ≤ 1` it *is* the configuration point
  `(r, d, circOf (u²))`, i.e. an ordinary strip point;
* `Work.Drive.exists_capPiece_planePt` — for `1 ≤ ‖d‖ ≤ √2` it *is* a cap point: the class has
  crossed the Clifford torus.  This is the algebraic content of `Work.Drive.capLift_reflect`, and it
  is the reason the capped plane is homologically essential (a disk filling `∂M` inside the
  configuration piece would be null-homologous in `Y ≅ ℝ × ℝP³`);
* `Work.Drive.contMDiffAt_planePt` — smoothness of `w ↦ planePt (u w) (r w) · (d w) ·` from
  smoothness of `r`, `u`, `d`, together with `1 - ‖d x₀‖²/2 ≠ 0` at the base point.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- The sphere lift `confProjVecOf u d` of a configuration point does not vanish as soon as
`‖u‖ = 1` and `‖d‖ ≤ √2`: for `‖d‖ ≤ 1` this is `Work.Drive.confProjVecOf_ne_zero`, and for
`1 < ‖d‖ ≤ √2` it is the cap form `capProjVecOf w d_cap` of the same class
(`Work.Drive.capLift_reflect`). -/
lemma confProjVecOf_ne_zero_of_le_sqrt2 {u : ℂ} (hu : ‖u‖ = 1) {d : ℂ}
    (hd : ‖d‖ ≤ Real.sqrt 2) : confProjVecOf u d ≠ 0 := by
  by_cases h : ‖d‖ ≤ 1
  · exact confProjVecOf_ne_zero hu h
  · have hlt : 1 < ‖d‖ := not_le.mp h
    have hd0 : d ≠ 0 := fun hz => by rw [hz, norm_zero] at hlt; norm_num at hlt
    rw [← capLift_reflect hu hd0 hd]
    refine capProjVecOf_ne_zero (norm_reflectW hu hd0) ?_
    rw [norm_capReflectVec hd0 hd, Real.sqrt_le_one]
    nlinarith [hlt, norm_nonneg d]

/-- For a **unit** complex halving `u` the sphere lift `confProjVecOf u d` never vanishes, for any
`d` whatsoever: a vanishing needs `√(1 - ‖d‖²/2) = 0` (first coordinate) and `d = 0` (second
coordinate), which are incompatible.  This removes all side conditions from the plane point. -/
lemma confProjVecOf_ne_zero_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (d : ℂ) :
    confProjVecOf u d ≠ 0 := by
  intro h
  have h1 : c₁ (confProjVecOf u d) = 0 := by rw [h]; simp [c₁]
  have h2 : c₂ (confProjVecOf u d) = 0 := by rw [h]; simp [c₂]
  rw [c₁_confProjVecOf] at h1
  rw [c₂_confProjVecOf] at h2
  have hu0 : u ≠ 0 := fun hz => by rw [hz, norm_zero] at hu; norm_num at hu
  have hs : ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact absurd h' hu0
    · exact h'
  have hs' : Real.sqrt (1 - ‖d‖ ^ 2 / 2) = 0 := Complex.ofReal_eq_zero.mp hs
  have hlow : 1 - ‖d‖ ^ 2 / 2 ≤ 0 := Real.sqrt_eq_zero'.mp hs'
  have hd0 : d = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd (star_eq_zero.mp h'') hu0
      · exact h''
    · exact absurd h' (by norm_num)
  rw [hd0, norm_zero] at hlow
  norm_num at hlow

/-- **The plane point.**  The point of the capping space with capping radius `r` whose projective
class is that of the configuration sphere lift `confProjVecOf u d`.  It is defined through the
transparent coordinates `cappingSpaceHomeoProj`, so that it can describe the configuration piece and
the cap piece with one formula. -/
def planePt (u : ℂ) (r : ℝ) (hr : 0 < r) (d : ℂ) (hu : ‖u‖ = 1)
    (hv : confProjVecOf u d ≠ 0) : CappingSpace :=
  cappingSpaceHomeoProj.symm (⟨r, hr⟩, Projectivization.mk ℝ (confProjVecOf u d) hv)

/-- The defining property of `planePt` in the transparent coordinates. -/
lemma cappingSpaceHomeoProj_planePt (u : ℂ) (r : ℝ) (hr : 0 < r) (d : ℂ) (hu : ‖u‖ = 1)
    (hv : confProjVecOf u d ≠ 0) :
    cappingSpaceHomeoProj (planePt u r hr d hu hv)
      = (⟨r, hr⟩, Projectivization.mk ℝ (confProjVecOf u d) hv) :=
  cappingSpaceHomeoProj.apply_symm_apply _

/-- **The configuration side of the plane point.**  For `‖d‖ ≤ 1` the plane point is the ordinary
configuration point `(r, d, circOf (u²))` of the configuration piece. -/
theorem planePt_eq_confPiece {u : ℂ} {r : ℝ} (hr : 0 < r) {d : ℂ} (hd : ‖d‖ ≤ 1)
    (hu : ‖u‖ = 1) :
    planePt u r hr d hu (confProjVecOf_ne_zero hu hd)
      = Quotient.mk'' (Sum.inl (⟨(r, d, circOf (u ^ 2) (by rw [norm_pow, hu]; norm_num)),
          hr, hd⟩ : ConfigPiece) : ConfigPiece ⊕ CapPiece) := by
  apply cappingSpaceHomeoProj.injective
  rw [cappingSpaceHomeoProj_planePt,
    cappingSpaceHomeoProj_confPiece r d (circOf (u ^ 2) (by rw [norm_pow, hu]; norm_num)) hr hd,
    lensToProj_confPiece d hd u hu]

/-- **The cap side of the plane point.**  For `1 ≤ ‖d‖ ≤ √2` the plane point is a point of the *cap*
piece: the projective class of the configuration lift has crossed the Clifford torus
`{|c₁| = |c₂|} ⊂ ℝP³`.  Explicitly, with `w = u · d̄/‖d‖` and `d_cap = √2·(d/‖d‖)·√(1-‖d‖²/2)`
(so that `‖d_cap‖² = 2 - ‖d‖² ≤ 1`), the point is `(r, circOf (w²), d_cap)`. -/
theorem exists_capPiece_planePt {u : ℂ} {r : ℝ} (hr : 0 < r) {d : ℂ} (hu : ‖u‖ = 1)
    (hd1 : 1 ≤ ‖d‖) (hd2 : ‖d‖ ≤ Real.sqrt 2) :
    ∃ c : CapPiece,
      planePt u r hr d hu (confProjVecOf_ne_zero_of_le_sqrt2 hu hd2) = Quotient.mk'' (Sum.inr c) := by
  have hd0 : d ≠ 0 := fun hz => by rw [hz, norm_zero] at hd1; norm_num at hd1
  have hw1 : ‖u * star d / (‖d‖ : ℂ)‖ = 1 := norm_reflectW hu hd0
  have hdcn : ‖((Real.sqrt 2 : ℝ) : ℂ) * (d / (‖d‖ : ℂ))
      * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)‖ = Real.sqrt (2 - ‖d‖ ^ 2) :=
    norm_capReflectVec hd0 hd2
  have hdc1 : ‖((Real.sqrt 2 : ℝ) : ℂ) * (d / (‖d‖ : ℂ))
      * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [hdcn, Real.sqrt_le_one]
    nlinarith [hd1, norm_nonneg d]
  set w : ℂ := u * star d / (‖d‖ : ℂ) with hwdef
  set dc : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) * (d / (‖d‖ : ℂ))
    * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) with hdcdef
  have hw1' : ‖w‖ = 1 := hw1
  have hdc1' : ‖dc‖ ≤ 1 := hdc1
  have hz : ‖w ^ 2‖ = 1 := by rw [norm_pow, hw1']; norm_num
  let θ : UnitAddCircle := circOf (w ^ 2) hz
  let p : ℝ × UnitAddCircle × ℂ := (r, θ, dc)
  have hp1 : 0 < p.1 := hr
  have hp2 : ‖p.2.2‖ ≤ 1 := hdc1'
  refine ⟨⟨p, hp1, hp2⟩, ?_⟩
  have htw : w ^ 2 = circleOf p.2.1 := (circleOf_circOf (w ^ 2) hz).symm
  apply cappingSpaceHomeoProj.injective
  rw [cappingSpaceHomeoProj_planePt,
    cappingSpaceHomeoProj_capPiece p hp1 hp2 htw]
  have hkey : capProjVecOf w p.2.2 = confProjVecOf u d := by
    show capProjVecOf w dc = confProjVecOf u d
    rw [hdcdef, hwdef]
    exact capLift_reflect hu hd0 hd2
  refine Prod.ext rfl ((Projectivization.mk_eq_mk_iff ℝ (confProjVecOf u d)
    (capProjVecOf w p.2.2) _ _).mpr ⟨1, ?_⟩)
  rw [one_smul]
  exact hkey

/-- Negation of a vector of `ℂ² ≅ ℝ⁴` negates both complex coordinates. -/
lemma ofComplex_neg (a b : ℂ) : ofComplex (-a) (-b) = -ofComplex a b := by
  apply WithLp.ofLp_injective
  ext i
  fin_cases i <;> simp [ofComplex]

/-- The projective class of the vector `-v` is that of `v`. -/
lemma projectivizationMk_eq_of_eq_neg {v v' : Eucl 3} (h : v' = -v) (hv : v ≠ 0)
    (hv' : v' ≠ 0) :
    Projectivization.mk ℝ v' hv' = Projectivization.mk ℝ v hv := by
  subst h
  exact (Projectivization.mk_eq_mk_iff ℝ (-v) v hv' hv).mpr ⟨-1, by simp⟩

/-- **The plane point depends on the halving only through its square.**  Two unit complex numbers
with the same square differ by a sign, and the sign change negates the sphere lift, hence does not
change the projective class. -/
theorem planePt_eq_of_sq_eq {u u' : ℂ} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) (h : u ^ 2 = u' ^ 2)
    (r : ℝ) (hr : 0 < r) (d : ℂ) (hv : confProjVecOf u d ≠ 0)
    (hv' : confProjVecOf u' d ≠ 0) :
    planePt u r hr d hu hv = planePt u' r hr d hu' hv' := by
  have hfac : (u - u') * (u + u') = 0 := by
    have hh : u ^ 2 - u' ^ 2 = (u - u') * (u + u') := by ring
    rw [h, sub_self] at hh
    exact hh.symm
  have hcases : u = u' ∨ u = -u' := by
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (eq_neg_of_add_eq_zero_left h')
  apply cappingSpaceHomeoProj.injective
  rw [cappingSpaceHomeoProj_planePt, cappingSpaceHomeoProj_planePt]
  rcases hcases with h' | h'
  · subst h'
    exact Prod.ext rfl (projectivizationMk_congr ℝ (Eucl 3))
  · have hneg : confProjVecOf u d = -confProjVecOf u' d := by
      rw [h']
      show confProjVecOf (-u') d = -confProjVecOf u' d
      simp only [confProjVecOf]
      rw [show (-u') * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)
            = -(u' * ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ)) by ring,
          show star (-u') * d / ((Real.sqrt 2 : ℝ) : ℂ)
            = -(star u' * d / ((Real.sqrt 2 : ℝ) : ℂ)) by rw [star_neg]; ring,
          ofComplex_neg]
    exact Prod.ext rfl (projectivizationMk_eq_of_eq_neg hneg hv' hv)

/-- **Smoothness of the sphere lift** `w ↦ confProjVecOf (u w) (d w)`, with the weaker hypothesis
`1 - ‖d x₀‖²/2 ≠ 0` at the base point (the form needed on the cap side, where `‖d‖ > 1`).  It is
`Work.Drive.contDiffAt_confProjVecOf` with `‖d x₀‖ ≤ 1` weakened to the actual side condition of the
square root. -/
lemma contDiffAt_confProjVecOf' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u d : E → ℂ} {x : E} {n : WithTop ℕ∞} (hu : ContDiffAt ℝ n u x) (hd : ContDiffAt ℝ n d x)
    (hne : 1 - ‖d x‖ ^ 2 / 2 ≠ 0) :
    ContDiffAt ℝ n (fun w => confProjVecOf (u w) (d w)) x := by
  have hre : ContDiffAt ℝ n (fun w => (d w).re) x :=
    (Complex.reCLM.contDiff.contDiffAt).comp x hd
  have him : ContDiffAt ℝ n (fun w => (d w).im) x :=
    (Complex.imCLM.contDiff.contDiffAt).comp x hd
  have hnorm2 : ContDiffAt ℝ n (fun w => ‖d w‖ ^ 2) x := by
    have h := (hre.mul hre).add (him.mul him)
    have hfun : (fun w => ‖d w‖ ^ 2)
        = fun w => (d w).re * (d w).re + (d w).im * (d w).im := by
      funext w
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hfun]
    exact h
  have hinner : ContDiffAt ℝ n (fun w => 1 - ‖d w‖ ^ 2 / 2) x :=
    contDiffAt_const.sub (hnorm2.div_const 2)
  have hsqrt : ContDiffAt ℝ n (fun w => Real.sqrt (1 - ‖d w‖ ^ 2 / 2)) x :=
    (Real.contDiffAt_sqrt hne).comp x hinner
  have h1 : ContDiffAt ℝ n
      (fun w => u w * ((Real.sqrt (1 - ‖d w‖ ^ 2 / 2) : ℝ) : ℂ)) x :=
    hu.mul ((Complex.ofRealCLM.contDiff.contDiffAt).comp x hsqrt)
  have hstar : ContDiffAt ℝ n (fun w => star (u w)) x :=
    (Complex.conjCLE.contDiff.contDiffAt).comp x hu
  have h2 : ContDiffAt ℝ n
      (fun w => star (u w) * d w / ((Real.sqrt 2 : ℝ) : ℂ)) x :=
    (hstar.mul hd).div_const _
  have := contDiffAt_ofComplex h1 h2
  simpa only [confProjVecOf] using this

/-- **Smoothness of the plane point**, from smoothness of `r`, `u`, `d` and the non-vanishing of
`1 - ‖d x₀‖²/2` at the base point.  This is the tool that lets a plane chart be written through the
transparent coordinates `cappingSpaceHomeoProj` — i.e. lets one formula cover the configuration
piece and the cap piece — while keeping the smoothness proof entirely explicit. -/
theorem contMDiffAt_planePt {k : ℕ} (r : EuclideanSpace ℝ (Fin k) → ℝ)
    (u d : EuclideanSpace ℝ (Fin k) → ℂ) (x₀ : EuclideanSpace ℝ (Fin k))
    (hr : ∀ w, 0 < r w) (hu : ∀ w, ‖u w‖ = 1)
    (hne : 1 - ‖d x₀‖ ^ 2 / 2 ≠ 0)
    (hv : ∀ w, confProjVecOf (u w) (d w) ≠ 0)
    (hrs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀)
    (hus : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) u x₀)
    (hds : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) d x₀) :
    letI := cappingCharted
    ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => planePt (u w) (r w) (hr w) (d w) (hu w) (hv w)) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  let F : EuclideanSpace ℝ (Fin k) → CappingSpace :=
    fun w => planePt (u w) (r w) (hr w) (d w) (hu w) (hv w)
  let g : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  have hg : ∀ w, g w = (⟨r w, hr w⟩,
      Projectivization.mk ℝ (confProjVecOf (u w) (d w)) (hv w)) := fun w =>
    cappingSpaceHomeoProj_planePt (u w) (r w) (hr w) (d w) (hu w) (hv w)
  have hchart : (letI := cappingCharted
        ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀) ↔
      ContMDiffAt (𝓡 k) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀ :=
    chartedStructure_contMDiffWithinAt (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4))
      (H := EuclideanSpace ℝ (Fin 4)) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k)) (𝓡 k)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      cappingSpaceHomeoProj.symm F Set.univ x₀
  have hfirst : ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => expHomeo.symm (g w).1) x₀ := by
    have hcomp : (fun w => expHomeo.symm (g w).1)
        = fun w => expHomeo.symm ⟨r w, hr w⟩ := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_expHomeo_symm hr x₀ hrs
  have hsecond : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (g w).2) x₀ := by
    have hcomp : (fun w => (g w).2)
        = fun w => Projectivization.mk ℝ (confProjVecOf (u w) (d w)) (hv w) := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_projMk (fun w => confProjVecOf (u w) (d w)) hv x₀
      (contMDiffAt_iff_contDiffAt.mpr
        (contDiffAt_confProjVecOf' hus.contDiffAt hds.contDiffAt hne))
  exact hchart.mpr ((contMDiffAt_halfLineProjective_iff g x₀).mpr ⟨hfirst, hsecond⟩)

end

end Work.Drive
