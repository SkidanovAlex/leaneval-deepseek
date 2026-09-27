import Mathlib
import Submission.Work.Drive.sweepPertSurjDef

/-!
# The `ChartPert` instance produces the `hsurj` brick for clamped sweeps

`Work.Drive.SweepPertSurj Q m Ξ` (`Submission/Work/Drive/sweepPertSurjDef.lean`) says: for every level
`c > 0`, every sweep parameter `y ∈ unitBox 2` with `y 2 ∈ (0,1)` and every parameter `t`, the
parameter-derivative of `t' ↦ clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (diskPlane Q z)) y` at
`t` is surjective.  This file proves it from `Work.Drive.ChartPert Q m Ξ`.

## The mechanism

`clampedSweep c ψ P y` only reads `P` at `mk2 (y 0) (y 1)`:

> `clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (diskPlane Q z)) y`
>   `= scaleCapping (pos (exp ((1 - y 2) * (log c - log (levelOf q)))) _) q`,
>   `q = Ξ t' (diskPlane Q (mk2 (y 0) (y 1)))`,

so the family is the composite of the parameter curve `u t' = Ξ t' (diskPlane Q (mk2 (y 0) (y 1)))`
— whose derivative is onto at *every* parameter and every point, by the third clause of
`Work.Drive.ChartPert` — with the **fixed** map

> `dil c a q = scaleCapping (pos (exp (a * (log c - log (levelOf q)))) _) q`,   `a = 1 - y 2`,

whose derivative is *onto* because the map is a diffeomorphism: with `b = -a / (1 - a)` (so that
`a + b - a * b = 0`, i.e. `a * (1 - b) + b = 0` and `(1 - a) * (1 - b) = 1`) one has
`dil c b (dil c a q) = q` and `dil c a (dil c b q) = q` — the level of `dil c a q` is
`c ^ a * (levelOf q) ^ (1 - a)` and the two exponents cancel; the class is untouched.  Differentiating
`(dil c b) ∘ (dil c a) = id` at `q` with the chain rule exhibits `mfderiv (dil c a) q` as injective,
and an injective endomorphism of the finite dimensional `ℝ⁴` is surjective.  Composing the onto
derivative of `u` with the onto derivative of `dil c a` finishes.

The *interiority* hypothesis `y 2 ∈ (0,1)` enters exactly through `1 - a = y 2 ≠ 0` (the inverse
exponent `b` must make sense); at `y 2 = 1` the map `dil c a` is the identity and the conclusion holds
directly.

## The smoothness of `dil`

`dil c a` is `C^∞` on the capping space: transporting along `cappingSpaceHomeoProj`
(`Work.Drive.chartedStructure_contMDiffWithinAt`) and splitting into the two coordinates of the model
`(0,∞) × ℝP³` (`Work.Drive.contMDiffAt_halfLineProjective_iff_general`), the level coordinate becomes
`a * (log c - log (levelOf ·)) + log (levelOf ·)` (smooth, using that `log ∘ levelOf` is smooth,
`Work.Drive.contMDiffAt_logLevelOf`) and the class coordinate is simply the class of the point
(`Work.Drive.cls_scaleCapping`).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The level power dilation -/

/-- **The level power dilation.**  `dil c a q` is the point with the same projective class as `q` and
with level `exp (a * (log c - log (levelOf q))) * levelOf q = c ^ a * (levelOf q) ^ (1 - a)`.  With
`a = 1 - y 2` this is exactly the fixed map `q ↦ clampedSweep c (fun s => 1 - s) (fun _ => q) y`. -/
def dil (c a : ℝ) (q : CappingSpace) : CappingSpace :=
  scaleCapping (pos (Real.exp (a * (Real.log c - Real.log (levelOf q)))) (Real.exp_pos _)) q

/-- The level of the power dilation. -/
lemma dil_level (c a : ℝ) (q : CappingSpace) :
    levelOf (dil c a q)
      = Real.exp (a * (Real.log c - Real.log (levelOf q))) * levelOf q := by
  rw [dil, levelOf_scaleCapping, pos_val]

/-! ## Smoothness of `dil` -/

/-- The class coordinate of `cappingSpaceHomeoProj` is `C^∞` on the capping space. -/
theorem contMDiffAt_classProj (q₀ : CappingSpace) :
    ContMDiffAt (𝓡 4) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : CappingSpace => (cappingSpaceHomeoProj q).2) q₀ :=
  ((contMDiffAt_halfLineProjective_iff_general (𝓡 4)
    (fun q : CappingSpace => cappingSpaceHomeoProj q) q₀).mp
    (contMDiffAt_cappingSpaceHomeoProj q₀)).2

/-- **`log` of the level is `C^∞` on the capping space.**  `Real.log (levelOf q)` is
`euclLog (expHomeo.symm ((cappingSpaceHomeoProj q).1))`, which is smooth because the first coordinate
of `cappingSpaceHomeoProj` is. -/
theorem contMDiffAt_logLevelOf (q₀ : CappingSpace) :
    ContMDiffAt (𝓡 4) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => Real.log (levelOf q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : CappingSpace => expHomeo.symm ((cappingSpaceHomeoProj q).1)) q₀ :=
    ((contMDiffAt_halfLineProjective_iff_general (𝓡 4)
      (fun q : CappingSpace => cappingSpaceHomeoProj q) q₀).mp
      (contMDiffAt_cappingSpaceHomeoProj q₀)).1
  rw [show (fun q : CappingSpace => Real.log (levelOf q))
      = fun q => CapSmooth.euclLog (expHomeo.symm ((cappingSpaceHomeoProj q).1)) from
    funext (fun q => by rw [levelOf, expHomeo_symm_apply, CapSmooth.euclLog_logEucl])]
  exact (CapSmooth.euclLog.contMDiff.contMDiffAt (x := expHomeo.symm
    ((cappingSpaceHomeoProj q₀).1))).comp q₀ h1

/-- **The level power dilation is `C^∞`.** -/
theorem contMDiffAt_dil (c a : ℝ) (q₀ : CappingSpace) :
    ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (dil c a) q₀ := by
  rw [← contMDiffWithinAt_univ]
  refine (chartedStructure_contMDiffWithinAt (I := 𝓡 4) (I' := 𝓡 4)
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (e := cappingSpaceHomeoProj.symm) (Z := CappingSpace)
    (f := dil c a) Set.univ q₀).mpr ?_
  rw [contMDiffWithinAt_univ]
  refine (contMDiffAt_halfLineProjective_iff_general (𝓡 4)
    (fun y : CappingSpace => cappingSpaceHomeoProj (dil c a y)) q₀).mpr ⟨?_, ?_⟩
  · -- the level coordinate, in the exponential chart, is `a (log c - log l) + log l`
    have hfun : (fun w : CappingSpace => expHomeo.symm ((cappingSpaceHomeoProj (dil c a w)).1))
        = fun w : CappingSpace =>
            logEucl (a * (Real.log c - Real.log (levelOf w)) + Real.log (levelOf w)) := by
      funext w
      rw [expHomeo_symm_apply]
      show logEucl (Real.log (levelOf (dil c a w))) = _
      rw [dil_level, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (levelOf_pos w)),
        Real.log_exp]
    rw [hfun]
    have hg : ContMDiffAt (𝓡 4) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : CappingSpace =>
          a * (Real.log c - Real.log (levelOf w)) + Real.log (levelOf w)) q₀ :=
      ((contMDiffAt_const.mul (contMDiffAt_const.sub (contMDiffAt_logLevelOf q₀))).add
        (contMDiffAt_logLevelOf q₀))
    exact (logEucl.contMDiff.contMDiffAt (x := a * (Real.log c - Real.log (levelOf q₀))
      + Real.log (levelOf q₀))).comp q₀ hg
  · -- the class coordinate is unchanged
    have hfun : (fun w : CappingSpace => (cappingSpaceHomeoProj (dil c a w)).2)
        = fun w : CappingSpace => (cappingSpaceHomeoProj w).2 := by
      funext w; rw [dil, cls_scaleCapping]
    rw [hfun]
    exact contMDiffAt_classProj q₀

/-! ## The reciprocal dilation -/

/-- **The reciprocal dilation.**  If `a + b - a * b = 0` (equivalently `a * (1 - b) + b = 0`, which
is the same as `(1 - a) * (1 - b) = 1`), then `dil c b` inverts `dil c a`: the levels `l ↦ c^a l^(1-a)`
and `l ↦ c^b l^(1-b)` compose to the identity. -/
lemma dil_dil (c : ℝ) (hc : 0 < c) {a b : ℝ} (hab : a + b - a * b = 0) (q : CappingSpace) :
    dil c a (dil c b q) = q := by
  have hl : 0 < levelOf q := levelOf_pos q
  have hlog : Real.log (levelOf (dil c b q))
      = b * (Real.log c - Real.log (levelOf q)) + Real.log (levelOf q) := by
    rw [dil_level, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hl), Real.log_exp]
  have hlevel : levelOf (dil c a (dil c b q)) = levelOf q := by
    rw [dil_level, hlog, dil_level, ← mul_assoc, ← Real.exp_add]
    have hXY : a * (Real.log c - (b * (Real.log c - Real.log (levelOf q))
          + Real.log (levelOf q))) + b * (Real.log c - Real.log (levelOf q)) = 0 := by
      have h1 : a * (Real.log c - (b * (Real.log c - Real.log (levelOf q))
            + Real.log (levelOf q))) + b * (Real.log c - Real.log (levelOf q))
          = (a + b - a * b) * (Real.log c - Real.log (levelOf q)) := by ring
      rw [h1, hab, zero_mul]
    rw [hXY, Real.exp_zero, one_mul]
  refine cappingSpaceHomeoProj.injective ?_
  refine Prod.ext (Subtype.ext hlevel) ?_
  show (cappingSpaceHomeoProj (dil c a (dil c b q))).2 = (cappingSpaceHomeoProj q).2
  rw [dil, cls_scaleCapping, dil, cls_scaleCapping]

/-- **The derivative of the power dilation is onto.**  Since `dil c b` inverts `dil c a` and both are
smooth, the chain rule exhibits `mfderiv (dil c a) q` as injective; an injective endomorphism of `ℝ⁴`
is surjective. -/
theorem surjective_mfderiv_dil (c : ℝ) (hc : 0 < c) {a b : ℝ} (hab : a + b - a * b = 0)
    (q : CappingSpace) : Function.Surjective (mfderiv (𝓡 4) (𝓡 4) (dil c a) q) := by
  have hab' : b + a - b * a = 0 := by
    rw [mul_comm b a]; linarith [hab]
  have hcomp : (dil c b) ∘ (dil c a) = id := funext fun r => dil_dil c hc hab' r
  have hmd₁ : MDifferentiableAt (𝓡 4) (𝓡 4) (dil c a) q :=
    (contMDiffAt_dil c a q).mdifferentiableAt (by simp)
  have hmd₂ : MDifferentiableAt (𝓡 4) (𝓡 4) (dil c b) (dil c a q) :=
    (contMDiffAt_dil c b (dil c a q)).mdifferentiableAt (by simp)
  have hcomp' : ContinuousLinearMap.id ℝ _
      = (mfderiv (𝓡 4) (𝓡 4) (dil c b) (dil c a q)).comp
        (mfderiv (𝓡 4) (𝓡 4) (dil c a) q) := by
    rw [← mfderiv_comp (I := 𝓡 4) (I' := 𝓡 4) (I'' := 𝓡 4)
      (f := dil c a) (g := dil c b) (x := q) hmd₂ hmd₁, hcomp, mfderiv_id]
  have hinj : Function.Injective (mfderiv (𝓡 4) (𝓡 4) (dil c a) q) := by
    intro u v huv
    have key : ∀ w : TangentSpace (𝓡 4) q,
        (mfderiv (𝓡 4) (𝓡 4) (dil c b) (dil c a q))
          ((mfderiv (𝓡 4) (𝓡 4) (dil c a) q) w) = w :=
      fun w => (congrArg (fun L => L w) hcomp').symm
    exact (key u).symm.trans (by rw [huv]; exact key v)
  haveI : FiniteDimensional ℝ (TangentSpace (𝓡 4) q) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 4)))
  haveI : FiniteDimensional ℝ (TangentSpace (𝓡 4) (dil c a q)) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 4)))
  have hfd : Module.finrank ℝ (TangentSpace (𝓡 4) q)
      = Module.finrank ℝ (TangentSpace (𝓡 4) (dil c a q)) := by
    simp only [TangentSpace]
    rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfd).mp hinj

/-! ## The brick -/

/-- **The `ChartPert` instance produces the `hsurj` brick for clamped sweeps.**

`Work.Drive.SweepPertSurj Q m Ξ` (defined in `Submission/Work/Drive/sweepPertSurjDef.lean`) says: for
every level `c > 0`, every sweep parameter `y ∈ unitBox 2` with `y 2 ∈ (0,1)` and every parameter `t`,
the parameter-derivative of `t' ↦ clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (diskPlane Q z)) y`
at `t` is surjective.

This is exactly the `hsurj` input of the parametric-Sard engines (`exists_meet3Hyp_of_good_family`,
`exists_forall_good_face_and_notMem_family`) for the germ design of the lead's 14:15 message, where the
*plane presentations* are perturbed (`Q ↦ Ξ t ∘ Q`) and the chains stay clamped sweeps, so that the
transport of `Submission/Work/Drive/transportChartAdapter.lean` applies to the perturbed triple as well.

Proof plan (verified on paper, and by the two reviewers): `clampedSweep c ψ P y` only reads `P` at
`mk2 (y 0) (y 1)`, so the family is the composite of `u t' = Ξ t' (diskPlane Q (mk2 (y 0) (y 1)))` —
whose derivative is onto at *every* parameter and every point, by `Work.Drive.ChartPert`'s third clause —
with the *fixed* map `G q = scaleCapping (exp ((1 - y 2) * (log c - log (levelOf q)))) q`, whose
differential in the `(level, class)` coordinates of the capping space is diagonal with entries
`(c / l) ^ (1 - y 2) * y 2 ≠ 0` (level) and `id` (class): an isomorphism for `y 2 ∈ (0,1)`.  Composing
the onto derivative with an isomorphism keeps it onto.

Note (from the reviews): the genuinely relevant hypothesis is `y 2 ≠ 0`; at `y 2 = 1` the map `G` is the
identity and the conclusion holds directly, and `(0,1)` is the *interiority* condition the counting
engines consume. -/
theorem sweepPertSurj_of_chartPert {Q : ℂ → CappingSpace} {m : ℕ}
    {Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace} (hΞ : ChartPert Q m Ξ) :
    SweepPertSurj Q m Ξ := by
  intro c hc y _hy hy2 t
  -- the exponent condition of the reciprocal dilation
  have hy2ne : y 2 ≠ 0 := ne_of_gt hy2.1
  have hab : (1 - y 2) + (-(1 - y 2) / (y 2)) - (1 - y 2) * (-(1 - y 2) / (y 2)) = 0 := by
    field_simp
    ring
  -- the parameter curve: the perturbation family evaluated at the point the sweep reads
  set u : EuclideanSpace ℝ (Fin m) → CappingSpace :=
    fun t' => Ξ t' (diskPlane Q (mk2 (y 0) (y 1)))
  have hmd_u : MDifferentiableAt (𝓡 m) (𝓡 4) u t := by
    have hpair : ContMDiffAt (𝓡 m) ((𝓡 m).prod (𝓡 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t' : EuclideanSpace ℝ (Fin m) =>
          (t', diskPlane Q (mk2 (y 0) (y 1)))) t :=
      ContMDiffAt.prodMk contMDiffAt_id contMDiffAt_const
    exact ((hΞ.2.1.contMDiffAt (x := (t, diskPlane Q (mk2 (y 0) (y 1))))).comp t hpair).mdifferentiableAt
      (by simp)
  have hsurj_u : Function.Surjective (mfderiv (𝓡 m) (𝓡 4) u t) := hΞ.2.2 t _
  -- the fixed dilation
  have hmd_G : MDifferentiableAt (𝓡 4) (𝓡 4) (dil c (1 - y 2)) (u t) :=
    (contMDiffAt_dil c (1 - y 2) (u t)).mdifferentiableAt (by simp)
  have hsurj_G : Function.Surjective (mfderiv (𝓡 4) (𝓡 4) (dil c (1 - y 2)) (u t)) :=
    surjective_mfderiv_dil c hc hab (u t)
  -- the family is the composite
  have hfun : (fun t' => clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (diskPlane Q z)) y)
      = (dil c (1 - y 2)) ∘ u := by
    funext t'
    rfl
  rw [hfun]
  -- the chain rule, and the composite of two onto derivatives
  have hchain := mfderiv_comp (I := 𝓡 m) (I' := 𝓡 4) (I'' := 𝓡 4)
    (f := u) (g := dil c (1 - y 2)) t hmd_G hmd_u
  rw [hchain]
  exact hsurj_G.comp hsurj_u

end

end Work.Drive
