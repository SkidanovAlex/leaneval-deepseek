import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Mono.gammaArcs_exist
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace

/-!
# `JunctionGenC` from a finite family of height-parametrised trace arcs

`Work.Drive.Mono.gammaArcs_exist` produces, at a regular cutting level, a finite family
`γ : Fin N → ℝ → R3` of arcs which cover the box trace inside a band of the cutting plane; each arc
is parametrised by the `σ 2`-height and lies on one signed face of the box.  This module turns such
a family, together with the *arc* genericity hypotheses

* `harcℓ` (the level function `ℓ` is regular along the arcs) and
* `harcv` (the slab coordinate grows at speed `≥ 1/2` along the arcs),

into the junction bundle `Work.Drive.Mono.JunctionGenC`: the exceptional set `exc` is enlarged by
the finitely many `ℓ`-values of the points of the trace lying on the **boundary of the slab**
(these are finitely many because `harcv` makes the slab coordinate strictly increasing along each
arc, so each arc meets a level of it at most twice).

The two nontrivial outputs are:

* the finite enlargement (`finite_slabBoundary_aux`, clause (d) of the bundle);
* the regularity of the height function and of the box norm at the arc points: `harcℓ` gives the
  first, the general position of the box faces at the level `s` (the `BoxGen` hypothesis) gives the
  second, and `harcv` gives the regularity of the slab coordinate.

The `σ 2`-height identity `hγh` is not used here; it is part of the interface of the arcs producer.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-! ## Analytic plumbing -/

/-- The chain rule for `r ↦ G (β r)` at a point where `G` has an explicit derivative. -/
private theorem deriv_comp_of_hasFDerivAt {G : ℝ × ℝ → ℝ} {β : ℝ → ℝ × ℝ} {t : ℝ}
    (hG : HasFDerivAt G (fderiv ℝ G (β t)) (β t)) (hβ : DifferentiableAt ℝ β t) :
    deriv (fun r => G (β r)) t = fderiv ℝ G (β t) (deriv β t) :=
  (hG.comp_hasDerivAt t hβ.hasDerivAt).deriv

/-- The derivative of `r ↦ ⟪v, K r⟫` at `t`. -/
private theorem deriv_inner_comp {v : R3} {K : ℝ → R3} {t : ℝ}
    (hK : HasDerivAt K (deriv K t) t) :
    deriv (fun r => inner ℝ v (K r)) t = inner ℝ v (deriv K t) := by
  have h := (ContinuousLinearMap.hasFDerivAt (innerSL ℝ v : R3 →L[ℝ] ℝ)).comp_hasDerivAt t hK
  have h' : deriv (fun r => inner ℝ v (K r)) t = (innerSL ℝ v : R3 →L[ℝ] ℝ) (deriv K t) := by
    simpa only [Function.comp_def, innerSL_apply_apply] using h.deriv
  simpa only [innerSL_apply_apply] using h'

/-- If `A w ≠ 0` and `B w = 0` then `A` is not a multiple of `B`. -/
private theorem ne_smul_of_apply_eq_zero {A B : (ℝ × ℝ) →L[ℝ] ℝ} {w : ℝ × ℝ}
    (hA : A w ≠ 0) (hB : B w = 0) : ∀ c : ℝ, A ≠ c • B := by
  intro c hc
  refine hA ?_
  rw [hc, ContinuousLinearMap.smul_apply, hB, smul_eq_mul, mul_zero]

/-- A function with positive derivative on an interval takes each value at most once there. -/
private theorem preimage_subsingleton_of_deriv_pos {f : ℝ → ℝ} {a b y : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, 0 < deriv f x) :
    (f ⁻¹' {y} ∩ Set.Icc a b).Subsingleton := by
  have hmono : StrictMonoOn f (Set.Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) hcont ?_
    rwa [interior_Icc]
  intro t₁ ht₁ t₂ ht₂
  exact hmono.injOn ht₁.2 ht₂.2 (by rw [ht₁.1, ht₂.1])

/-! ## The faces of the box at a point of the trace -/

/-- **A point on a face of the box has that signed face active.** -/
private theorem isActiveSignedFace_of_face_eq {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ}
    {i : Fin 3} {ε : ℝ} {z : R3} (hε : ε = 1 ∨ ε = -1)
    (hbox : Submission.boxNorm c σ z = s)
    (hface : z (σ i) = c (σ i) + ε * Submission.boxSide i * s) :
    Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z := by
  have hbi : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  constructor
  · rw [Work.Smooth.BoxGeneric.faceLin_apply, Work.Smooth.BoxGeneric.signedFace_apply, hface]
    rcases hε with hh | hh <;> rw [hh] <;> field_simp <;> ring
  · intro j
    rw [← hbox]
    exact Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j z

/-- **A point on a face of the box has that coordinate extremal.** -/
private theorem abs_coord_eq_of_face_eq {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ}
    {i : Fin 3} {ε : ℝ} {z : R3} (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hface : z (σ i) = c (σ i) + ε * Submission.boxSide i * s) :
    |z (σ i) - c (σ i)| = Submission.boxSide i * s := by
  rw [hface,
    show c (σ i) + ε * Submission.boxSide i * s - c (σ i)
      = ε * (Submission.boxSide i * s) by ring,
    abs_mul, abs_of_pos (mul_pos (Submission.boxSide_pos i) hs)]
  rcases hε with hh | hh <;> rw [hh] <;> simp

/-- **Only the face of the box which the point sits on is active**, unless the point is a corner
point of the box sphere. -/
private theorem faceNorm_lt_of_not_corner {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3}
    {i : Fin 3} (hbox : Submission.boxNorm c σ z = s)
    (haceq : |z (σ i) - c (σ i)| = Submission.boxSide i * s)
    (hnotcorner : ¬ ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
      |z (σ j) - c (σ j)| = Submission.boxSide j * s) :
    ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s := by
  intro j hji
  rcases lt_or_eq_of_le (show Work.Smooth.BoxGeneric.faceNorm c σ j z ≤ s from by
    rw [← hbox]
    exact Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j z) with hlt | heq
  · exact hlt
  · exact absurd ⟨i, j, hji.symm, haceq, by
      have h2 := heq
      rw [Work.Smooth.BoxGeneric.faceNorm_apply] at h2
      rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos j))] at h2
      linarith [h2]⟩ hnotcorner

/-- **A point on a face of the box is not inside the box.** -/
private theorem le_boxNorm_of_face_eq {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {i : Fin 3}
    {ε : ℝ} {z : R3} (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hface : z (σ i) = c (σ i) + ε * Submission.boxSide i * s) :
    s ≤ Submission.boxNorm c σ z := by
  have hbi : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  have h3 : |z (σ i) - c (σ i)| = Submission.boxSide i * s :=
    abs_coord_eq_of_face_eq hs hε hface
  have h4 : Work.Smooth.BoxGeneric.faceNorm c σ i z = s := by
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, h3, mul_div_cancel_left₀ s hbi]
  rw [← h4]
  exact Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i z

/-! ## The box norm as a smooth function of the parameters -/

/-- **Near a point with a unique active face the box norm agrees with that face**, so `boxNorm ∘ par`
is differentiable there; if moreover the active face is regular at the level of `z`, the derivative
of `boxNorm ∘ par` does not vanish at any parameter over `z`. -/
private theorem boxNorm_par_fderiv_ne_zero {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {i : Fin 3} {ε : ℝ} {z : R3} {p : ℝ × ℝ}
    (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z)
    (huniq : ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s)
    (hreg : fderiv ℝ (Work.Smooth.Morse.pullback ψ
      (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0) :
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
  have hcont : Filter.Tendsto (Work.BoxShrink.Pinch.par ψ) (𝓝 p) (𝓝 z) := by
    rw [← hp]
    exact (Work.BoxShrink.Pinch.par_continuous ψ).continuousAt
  have hev : (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.BoxShrink.Pinch.par ψ q)) := by
    filter_upwards [hcont.eventually
      (Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin hs hε hact huniq)]
      with q hq
    exact hq
  rw [hev.fderiv_eq]
  exact hreg

/-- **The box norm is constant to first order along a trace arc.**  If `r ↦ γ r` lies on the box
sphere of level `s` and `par ψ (β r) = γ r` for `r` near `t`, then the derivative of `boxNorm ∘ par`
at `β t` in the direction of the arc vanishes. -/
private theorem boxNorm_par_deriv_apply_eq_zero {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {i : Fin 3} {ε : ℝ} {z : R3} {β : ℝ → ℝ × ℝ} {γ : ℝ → R3}
    {t η : ℝ} (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z)
    (huniq : ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s)
    (hβcd : ContDiffOn ℝ 3 β (Set.Icc (-η) η)) (ht : t ∈ Set.Ioo (-η) η)
    (hβspec : ∀ r ∈ Set.Icc (-η) η, Work.BoxShrink.Pinch.par ψ (β r) = γ r)
    (hzpar : Work.BoxShrink.Pinch.par ψ (β t) = z) (hboxz : Submission.boxNorm c σ z = s)
    (hmin : ∀ r ∈ Set.Icc (-η) η, s ≤ Submission.boxNorm c σ (γ r)) :
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q))
      (β t) (deriv β t) = 0 := by
  have hlocmin : IsLocalMin (fun r : ℝ => Submission.boxNorm c σ (γ r)) t := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    have hzt : Submission.boxNorm c σ (γ t) = s := by
      rw [← hβspec t (Set.Ioo_subset_Icc_self ht), hzpar]
      exact hboxz
    rw [hzt]
    exact hmin r hr
  have hzeroderiv : deriv (fun r : ℝ => Submission.boxNorm c σ (γ r)) t = 0 :=
    hlocmin.deriv_eq_zero
  have hcont : Filter.Tendsto (Work.BoxShrink.Pinch.par ψ) (𝓝 (β t)) (𝓝 z) := by
    rw [← hzpar]
    exact (Work.BoxShrink.Pinch.par_continuous ψ).continuousAt
  have hev : (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) =ᶠ[𝓝 (β t)]
      (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.BoxShrink.Pinch.par ψ q)) := by
    filter_upwards [hcont.eventually
      (Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin hs hε hact huniq)]
      with q hq
    exact hq
  have hsmooth : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.BoxShrink.Pinch.par ψ q))
      (β t) :=
    (((Work.Smooth.BoxGeneric.contDiff_faceLin c σ i ε).comp
      (Work.BoxShrink.Pinch.par_contDiff ψ)).differentiable (by simp)).differentiableAt
  have hdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) (β t) :=
    hev.differentiableAt_iff.mpr hsmooth
  have hβdiff : DifferentiableAt ℝ β t :=
    (hβcd.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt (by norm_num)
  have hchain : deriv (fun r : ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ (β r))) t =
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q))
        (β t) (deriv β t) :=
    deriv_comp_of_hasFDerivAt hdiff.hasFDerivAt hβdiff
  have hev2 : (fun r : ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ (β r))) =ᶠ[𝓝 t]
      (fun r : ℝ => Submission.boxNorm c σ (γ r)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    rw [hβspec r hr]
  rw [← hchain, hev2.deriv_eq, hzeroderiv]

/-- **The regularity of the active face at the level gives the regularity of `boxNorm ∘ par`.**
(`BoxGen` at the level `s`.) -/
private theorem fderiv_pullback_faceLin_ne_zero_of_boxGen {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {i : Fin 3} {ε : ℝ} {z : R3} {p : ℝ × ℝ}
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s) (hε : ε = 1 ∨ ε = -1)
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0 := by
  intro hzero
  rw [Work.Smooth.BoxGeneric.fderiv_pullback_faceLin] at hzero
  have hval : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i) p = ε * s := by
    have h2 : Work.Smooth.BoxGeneric.signedFace c σ i z = ε * s :=
      Work.Smooth.BoxGeneric.signedFace_eq_of_faceLin_eq hε hact.1
    show Work.Smooth.BoxGeneric.signedFace c σ i (Work.BoxShrink.Pinch.par ψ p) = ε * s
    rw [hp]
    exact h2
  have hzero' : fderiv ℝ (Work.Smooth.Morse.pullback ψ
      (Work.Smooth.BoxGeneric.signedFace c σ i)) p = 0 := by
    rcases hε with h1 | h1
    · rw [h1, one_smul] at hzero
      exact hzero
    · rw [h1] at hzero
      simpa using hzero
  exact ((Work.Smooth.Morse.isRegularValue_iff ψ _ _).mp (hBG.1 i ε hε)) p hval hzero'

/-! ## The slab boundary of the trace is finite -/

/-- **The points of the trace on the boundary of the slab are finite.**  Each such point lies on one
of the arcs (`hcover`), and each arc meets the boundary of the slab at most twice: the slab
coordinate `r ↦ ⟪v, γ k r⟫` has derivative `≥ 1/2` on the arc (`harcv`), so it is strictly
increasing there. -/
private theorem finite_slabBoundary_aux {ψ : Submission.Diffeo} {s u h : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {N : ℕ} {γ : Fin N → ℝ → R3} {η : ℝ} (hη : 0 < η)
    (hγ : ∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η))
    (harcv : ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      (1 / 2 : ℝ) ≤ inner ℝ v (deriv (γ k) t))
    (hnoCorner : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| = h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → False)
    (hcover : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
        ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
           |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
      ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h) :
    {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
      Submission.boxNorm c σ z = s ∧ |inner ℝ v z - (inner ℝ v c + u)| = h}.Finite := by
  classical
  set M : ℝ := min η (2 * h) with hM
  set S : Fin N → Set ℝ := fun k => {t : ℝ | t ∈ Set.Ioo (-η) η ∧ |t| ≤ 2 * h ∧
      |inner ℝ v (γ k t) - (inner ℝ v c + u)| = h} with hS
  have hSfin : ∀ k, (S k).Finite := by
    intro k
    rw [hS]
    have hmono : StrictMonoOn (fun t : ℝ => inner ℝ v (γ k t) - (inner ℝ v c + u))
        (Set.Icc (-M) M) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
      · refine ContinuousOn.sub ?_ continuousOn_const
        refine Continuous.comp_continuousOn
          (ContinuousLinearMap.continuous (innerSL ℝ v : R3 →L[ℝ] ℝ)) ?_
        exact (hγ k).continuousOn.mono fun r hr =>
          ⟨by linarith [hr.1, min_le_left η (2 * h)], by linarith [hr.2, min_le_left η (2 * h)]⟩
      · rw [interior_Icc]
        intro x hx
        have hxη : x ∈ Set.Ioo (-η) η :=
          ⟨by linarith [hx.1, min_le_left η (2 * h)], by linarith [hx.2, min_le_left η (2 * h)]⟩
        have hx2h : |x| ≤ 2 * h := by
          rw [abs_le]
          exact ⟨by linarith [hx.1, min_le_right η (2 * h)],
            by linarith [hx.2, min_le_right η (2 * h)]⟩
        have hd : deriv (fun t : ℝ => inner ℝ v (γ k t) - (inner ℝ v c + u)) x =
            inner ℝ v (deriv (γ k) x) := by
          rw [deriv_sub_const]
          exact deriv_inner_comp (((hγ k).contDiffAt (Icc_mem_nhds hxη.1 hxη.2)).differentiableAt
            (by norm_num)).hasDerivAt
        rw [hd]
        linarith [harcv k x hxη hx2h]
    have hsub : ∀ y : ℝ, ((fun t : ℝ => inner ℝ v (γ k t) - (inner ℝ v c + u)) ⁻¹' {y} ∩
        Set.Icc (-M) M).Subsingleton := fun y t₁ ht₁ t₂ ht₂ =>
      hmono.injOn ht₁.2 ht₂.2 (by
        have h1 : inner ℝ v (γ k t₁) - (inner ℝ v c + u) = y := ht₁.1
        have h2 : inner ℝ v (γ k t₂) - (inner ℝ v c + u) = y := ht₂.1
        rw [h1, h2])
    refine ((hsub h).finite.union (hsub (-h)).finite).subset ?_
    rintro t ⟨htIoo, htabs, htval⟩
    have htM : |t| ≤ M :=
      le_min (le_of_lt (abs_lt.mpr ⟨htIoo.1, htIoo.2⟩)) htabs
    have htIcc : t ∈ Set.Icc (-M) M := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le t, htM], by linarith [le_abs_self t, htM]⟩
    rcases lt_trichotomy (inner ℝ v (γ k t) - (inner ℝ v c + u)) 0 with hlt | heq | hgt
    · refine Or.inr ⟨?_, htIcc⟩
      rw [abs_of_neg hlt] at htval
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      linarith
    · refine Or.inr ⟨?_, htIcc⟩
      rw [heq, abs_zero] at htval
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      linarith
    · refine Or.inl ⟨?_, htIcc⟩
      rw [abs_of_nonneg (le_of_lt hgt)] at htval
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using htval
  have hunion : (⋃ k : Fin N, γ k '' S k).Finite := by
    refine Set.Finite.iUnion (Set.finite_univ) ?_ ?_
    · intro k _
      exact (hSfin k).image (γ k)
    · intro k hk
      exact absurd (Set.mem_univ k) hk
  refine hunion.subset ?_
  rintro z ⟨hzcar, hzbox, hzslab⟩
  have hnc : ¬ ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
      |z (σ j) - c (σ j)| = Submission.boxSide j * s := by
    rintro ⟨i, j, hij, hi, hj⟩
    exact hnoCorner z hzcar hzbox hzslab ⟨i, j, hij, hi, hj⟩
  have hcpre : ∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
      ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
         |z (σ j') - c (σ j')| = Submission.boxSide j' * s) :=
    fun j _ j' _ hjj' hcon => hnc ⟨j, j', hjj', hcon.1, hcon.2⟩
  obtain ⟨k, t, htIoo, hzt, htle⟩ := hcover z hzcar hzbox (le_of_eq hzslab) hcpre
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  rw [hzt]
  exact ⟨t, by rw [hS]; exact ⟨htIoo, htle, by rw [← hzt]; exact hzslab⟩, rfl⟩

/-! ## The main theorem -/

theorem junctionGenC_of_arcs
    (ψ : Submission.Diffeo) {s u : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (v : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s)
    (hcornerC : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → ℓ z ∈ (exc : Set ℝ))
    (hnoCornerFace : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → False)
    {N : ℕ} {γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {η : ℝ} (hη : 0 < η)
    (hγ : ∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η))
    (hγh : ∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t)
    (hγβ : ∀ k, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ β : ℝ → ℝ × ℝ,
      ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
        Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
        (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s)
    (hcover : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
        ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
           |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
      ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h)
    (harcℓ : ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      deriv (fun r : ℝ => ℓ (γ k r)) t ≠ 0)
    (harcv : ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      (1 / 2 : ℝ) ≤ inner ℝ v (deriv (γ k) t))
    (hwin : ∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1)
    (hexcWin : ∀ t ∈ exc, lam0 < t ∧ t < lam1) :
    ∃ exc' : Finset ℝ, (∀ t ∈ exc, t ∈ exc') ∧ (∀ t ∈ exc', lam0 < t ∧ t < lam1) ∧
      Work.Drive.Mono.JunctionGenC ψ s c σ u v h ℓ exc' lam0 lam1 := by
  classical
  have hBfin : {z : LeanEval.KnotTheory.PardonDistortion.R3 |
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
      Submission.boxNorm c σ z = s ∧ |inner ℝ v z - (inner ℝ v c + u)| = h}.Finite :=
    finite_slabBoundary_aux (ψ := ψ) hη hγ harcv hnoCornerFace hcover
  set B : Finset ℝ := hBfin.toFinset.image ℓ with hB
  refine ⟨exc ∪ B, ?_, ?_, ?_⟩
  · intro t ht
    exact Finset.mem_union_left B ht
  · intro t ht
    rw [Finset.mem_union] at ht
    rcases ht with h1 | h2
    · exact hexcWin t h1
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h2
      obtain ⟨hzcar, hzbox, -⟩ := (Set.Finite.mem_toFinset hBfin).mp hz
      have hfr : z ∈ frontier (Submission.PBox s c σ) := by
        rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ]
        exact hzbox
      exact hwin z (frontier_subset_closure hfr)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · -- clause (a): the levels of the trace inside the closed slab
      intro lam hlam hne z hz hbox hslab hzlam
      have hnotcorner : ¬ ∃ i j : Fin 3, i ≠ j ∧
          |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s := by
        rintro ⟨i, j, hij, hi, hj⟩
        refine hne (coe_subset_union exc B ?_)
        rw [← hzlam]
        exact hcornerC z hz hbox hslab ⟨i, j, hij, hi, hj⟩
      have hcpre : ∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
          ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
             |z (σ j') - c (σ j')| = Submission.boxSide j' * s) :=
        fun j _ j' _ hjj' hcon => hnotcorner ⟨j, j', hjj', hcon.1, hcon.2⟩
      obtain ⟨k, t, htIoo, hzt, htle⟩ := hcover z hz hbox hslab hcpre
      obtain ⟨i, hi, ε, hε, β, hβcd, hβspec⟩ := hγβ k
      have htIcc : t ∈ Set.Icc (-η) η := Set.Ioo_subset_Icc_self htIoo
      have hnhds : Set.Icc (-η) η ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
      have hparβ : Work.BoxShrink.Pinch.par ψ (β t) = z := by
        rw [hzt]
        exact (hβspec t htIcc).1
      have hface : z (σ i) = c (σ i) + ε * Submission.boxSide i * s := by
        rw [hzt]
        exact (hβspec t htIcc).2
      have hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z :=
        isActiveSignedFace_of_face_eq hε hbox hface
      have haceqi : |z (σ i) - c (σ i)| = Submission.boxSide i * s :=
        abs_coord_eq_of_face_eq hs hε hface
      have huniq := faceNorm_lt_of_not_corner (s := s) (z := z) (i := i) hbox haceqi hnotcorner
      have hmin : ∀ r ∈ Set.Icc (-η) η, s ≤ Submission.boxNorm c σ (γ k r) :=
        fun r hr => le_boxNorm_of_face_eq hs hε ((hβspec r hr).2)
      have hboxzero : fderiv ℝ (fun q : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) (β t) (deriv β t) = 0 :=
        boxNorm_par_deriv_apply_eq_zero (ψ := ψ) hs hε hact huniq hβcd htIoo
          (fun r hr => (hβspec r hr).1) hparβ hbox hmin
      have hboxne : fderiv ℝ (fun q : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) (β t) ≠ 0 :=
        boxNorm_par_fderiv_ne_zero (ψ := ψ) hs hε hparβ hact huniq
          (fderiv_pullback_faceLin_ne_zero_of_boxGen hBG hε hparβ hact)
      have hsmooth : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
          (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t)) (β t) := by
        have hcd : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.EpsForm.sweepHeight ψ ℓ) := by
          rw [Work.Drive.EpsForm.sweepHeight]
          exact Work.Smooth.Morse.pullback_contDiff ψ (ContinuousLinearMap.contDiff ℓ)
        exact ((hcd.differentiable (by simp)).differentiableAt).hasFDerivAt
      have hβdiff : DifferentiableAt ℝ β t :=
        (hβcd.contDiffAt hnhds).differentiableAt (by norm_num)
      have hchain := deriv_comp_of_hasFDerivAt hsmooth hβdiff
      have hderivpos : deriv (fun r : ℝ => Work.Drive.EpsForm.sweepHeight ψ ℓ (β r)) t ≠ 0 := by
        have hev : (fun r : ℝ => Work.Drive.EpsForm.sweepHeight ψ ℓ (β r)) =ᶠ[𝓝 t]
            (fun r : ℝ => ℓ (γ k r)) := by
          filter_upwards [hnhds] with r hr
          show ℓ (Work.BoxShrink.Pinch.par ψ (β r)) = ℓ (γ k r)
          rw [(hβspec r hr).1]
        rw [hev.deriv_eq]
        exact harcℓ k t htIoo htle
      have hAw : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t) (deriv β t) ≠ 0 := by
        rw [← hchain]
        exact hderivpos
      refine ⟨β t, hparβ, ?_, hboxne, ?_⟩
      · intro h0
        exact hAw (by rw [h0]; simp)
      · exact ne_smul_of_apply_eq_zero hAw hboxzero
    · -- clause (b): the levels of the trace on the boundary of the slab
      intro lam hlam hne z hz hbox hslab hzlt
      have hnotcorner : ¬ ∃ i j : Fin 3, i ≠ j ∧
          |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
          |z (σ j) - c (σ j)| = Submission.boxSide j * s :=
        fun hcon => hnoCornerFace z hz hbox hslab hcon
      have hcpre : ∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
          ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
             |z (σ j') - c (σ j')| = Submission.boxSide j' * s) :=
        fun j _ j' _ hjj' hcon => hnotcorner ⟨j, j', hjj', hcon.1, hcon.2⟩
      obtain ⟨k, t, htIoo, hzt, htle⟩ := hcover z hz hbox (le_of_eq hslab) hcpre
      obtain ⟨i, hi, ε, hε, β, hβcd, hβspec⟩ := hγβ k
      have htIcc : t ∈ Set.Icc (-η) η := Set.Ioo_subset_Icc_self htIoo
      have hnhds : Set.Icc (-η) η ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
      have hparβ : Work.BoxShrink.Pinch.par ψ (β t) = z := by
        rw [hzt]
        exact (hβspec t htIcc).1
      have hface : z (σ i) = c (σ i) + ε * Submission.boxSide i * s := by
        rw [hzt]
        exact (hβspec t htIcc).2
      have hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z :=
        isActiveSignedFace_of_face_eq hε hbox hface
      have haceqi : |z (σ i) - c (σ i)| = Submission.boxSide i * s :=
        abs_coord_eq_of_face_eq hs hε hface
      have huniq := faceNorm_lt_of_not_corner (s := s) (z := z) (i := i) hbox haceqi hnotcorner
      have hmin : ∀ r ∈ Set.Icc (-η) η, s ≤ Submission.boxNorm c σ (γ k r) :=
        fun r hr => le_boxNorm_of_face_eq hs hε ((hβspec r hr).2)
      have hboxzero : fderiv ℝ (fun q : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) (β t) (deriv β t) = 0 :=
        boxNorm_par_deriv_apply_eq_zero (ψ := ψ) hs hε hact huniq hβcd htIoo
          (fun r hr => (hβspec r hr).1) hparβ hbox hmin
      have hboxne : fderiv ℝ (fun q : ℝ × ℝ =>
          Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) (β t) ≠ 0 :=
        boxNorm_par_fderiv_ne_zero (ψ := ψ) hs hε hparβ hact huniq
          (fderiv_pullback_faceLin_ne_zero_of_boxGen hBG hε hparβ hact)
      have hVdiff : HasFDerivAt (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q))
          (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) (β t))
          (β t) := by
        have hcd : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) :=
          (ContinuousLinearMap.contDiff (innerSL ℝ v : R3 →L[ℝ] ℝ)).comp
            (Work.BoxShrink.Pinch.par_contDiff ψ)
        exact ((hcd.differentiable (by simp)).differentiableAt).hasFDerivAt
      have hβdiff : DifferentiableAt ℝ β t :=
        (hβcd.contDiffAt hnhds).differentiableAt (by norm_num)
      have hchainV := deriv_comp_of_hasFDerivAt hVdiff hβdiff
      have hVpos : deriv (fun r : ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ (β r))) t ≠ 0 := by
        have hev : (fun r : ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ (β r))) =ᶠ[𝓝 t]
            (fun r : ℝ => inner ℝ v (γ k r)) := by
          filter_upwards [hnhds] with r hr
          rw [(hβspec r hr).1]
        rw [hev.deriv_eq, deriv_inner_comp (((hγ k).contDiffAt hnhds).differentiableAt
          (by norm_num)).hasDerivAt]
        linarith [harcv k t htIoo htle]
      have hAw : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q))
          (β t) (deriv β t) ≠ 0 := by
        rw [← hchainV]
        exact hVpos
      refine ⟨β t, hparβ, ?_, hboxne, ?_⟩
      · intro h0
        exact hAw (by rw [h0]; simp)
      · exact ne_smul_of_apply_eq_zero hAw hboxzero
    · -- clause (c): the corner locus of the closed slab
      intro z hz hbox hslab hext
      exact coe_subset_union exc B (hcornerC z hz hbox hslab hext)
    · -- clause (d): the boundary of the slab
      intro z hz hbox hface
      refine Finset.mem_coe.mpr (Finset.mem_union_right exc ?_)
      refine Finset.mem_image.mpr ⟨z, ?_, rfl⟩
      exact (Set.Finite.mem_toFinset hBfin).mpr ⟨hz, hbox, hface⟩

end

end Work.Drive.Mono
