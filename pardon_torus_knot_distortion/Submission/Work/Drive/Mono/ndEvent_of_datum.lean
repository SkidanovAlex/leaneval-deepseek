import Mathlib
import Submission.Work.Drive.Mono.OneEventNDDefs
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.trace_locallyEuclidean_at_of_noEventAt

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set Filter
open scoped RealInnerProductSpace

noncomputable section

/-! ## Elementary helpers -/

/-- A datum whose slab cuts its box has a box of positive size: the box being non-empty forces
`boxSide 0 * s = s` to be positive. -/
private theorem pos_of_slabCutsBox {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {a h : ℝ} {v : R3}
    (hc : SlabCutsBox s c σ a h v) : 0 < s := by
  obtain ⟨⟨y, hy, _⟩, _⟩ := hc
  rw [Submission.mem_PBox] at hy
  have h1 : |y (σ 0) - c (σ 0)| < Submission.boxSide 0 * s := hy 0
  rw [Submission.boxSide_zero, one_mul] at h1
  exact lt_of_le_of_lt (abs_nonneg _) h1

/-- **Uniqueness of the multiplier of a nonzero functional**: a functional `D ≠ 0` is a multiple of
itself through one scalar only. -/
private theorem smul_eq_of_ne_zero {D : (ℝ × ℝ) →L[ℝ] ℝ} (hD : D ≠ 0) {t t' : ℝ}
    (h : t • D = t' • D) : t = t' := by
  obtain ⟨w, hw⟩ : ∃ w : ℝ × ℝ, D w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hD (ContinuousLinearMap.ext fun w => by simpa using hcon w)
  have hw' := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) h
  simp only [smul_apply, smul_eq_mul] at hw'
  exact mul_right_cancel₀ hw hw'

/-- **A multiple carries the same tangency relation**: if `Y = d • G` and `H` is never a multiple
of `G`, then `H` is never a multiple of `Y` either (the multiplier `t` is rescaled to `t * d`). -/
private theorem ne_smul_of_eq_smul {H Y G : (ℝ × ℝ) →L[ℝ] ℝ} {d : ℝ}
    (hY : Y = d • G) (h : ∀ t : ℝ, H ≠ t • G) : ∀ t : ℝ, H ≠ t • Y := by
  intro t ht
  exact h (t * d) (ht.trans (by rw [hY, smul_smul]))

/-- **The pulled-back box norm near a point with a single active face.**  At a parameter point `p`
over a point of the box sphere of level `s > 0` at which the single signed face `(i, ε)`
(`ε = ±1`) is tight and the other face norms are strictly below `s`, the box norm agrees with the
face function `faceLin c σ i ε` on a neighbourhood of `par ψ p`, so the derivative of the pulled-back
coordinate `q ↦ (par ψ q) (σ i)` is the nonzero multiple `(ε * (boxSide i)⁻¹)⁻¹` of the derivative
of the pulled-back box norm. -/
private theorem fderiv_coord_eq_smul_fderiv_boxNorm {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {i : Fin 3} {ε : ℝ} {p : ℝ × ℝ}
    (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε (Work.BoxShrink.Pinch.par ψ p))
    (huniq : ∀ j : Fin 3, j ≠ i →
      Work.Smooth.BoxGeneric.faceNorm c σ j (Work.BoxShrink.Pinch.par ψ p) < s) :
    fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p
      = (ε * (Submission.boxSide i)⁻¹)⁻¹ •
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p := by
  -- the box norm agrees with the tight face near `par ψ p`
  have htend : Filter.Tendsto (Work.BoxShrink.Pinch.par ψ) (nhds p)
      (nhds (Work.BoxShrink.Pinch.par ψ p)) :=
    (Work.BoxShrink.Pinch.par_continuous ψ).continuousAt
  have hev : (Work.Smooth.Morse.pullback ψ (Submission.boxNorm c σ)) =ᶠ[nhds p]
      (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) :=
    htend.eventually
      (Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin hs hε hact huniq)
  -- the chain rule, in the pull-back vocabulary of `Work.Smooth.BoxGeneric`
  have hkey : fderiv ℝ (Work.Smooth.Morse.pullback ψ (Submission.boxNorm c σ)) p
      = (ε * (Submission.boxSide i)⁻¹) •
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i))) p := by
    rw [Filter.EventuallyEq.fderiv_eq hev]
    rw [Work.Smooth.BoxGeneric.fderiv_pullback_faceLin]
    rw [show fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)) p
        = (Submission.boxSide i)⁻¹ •
          fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i))) p from by
      have hfun : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)
          = fun q : ℝ × ℝ => (Submission.boxSide i)⁻¹ *
              (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) := by
        funext q
        rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, div_eq_mul_inv, mul_comm]
      rw [hfun]
      have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ =>
          Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) p :=
        (((Work.Smooth.Morse.pullback_contDiff ψ (g := fun y : R3 => y (σ i))
            (by fun_prop)).differentiable (by simp)).sub_const (c (σ i))).differentiableAt
      rw [fderiv_const_mul hdiff (Submission.boxSide i)⁻¹, fderiv_sub_const]]
    rw [smul_smul]
  -- convert the pull-back forms to the parametrisation `par ψ`
  have hgoal : fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i))) p
      = (ε * (Submission.boxSide i)⁻¹)⁻¹ •
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (Submission.boxNorm c σ)) p := by
    have hεne : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
    rw [hkey, smul_smul, inv_mul_cancel₀ (mul_ne_zero hεne
      (inv_ne_zero (ne_of_gt (Submission.boxSide_pos i)))), one_smul]
  exact hgoal

/-! ## The main lemma -/

/-- **Every event of a good datum is non-degenerate.**  At a datum satisfying
`Work.Drive.Mono.GoodDataPackage3` (which carries `Work.Drive.Mono.DataPackage` — with the tilt
genericity `Work.Drive.Mono.TiltData`, hence `Work.Drive.Final.TiltedGenericity` — and
`Work.Drive.Final.GoodSweepData3` — with `EdgeFree`, `SlabInBelt`, the universal
`SlabBoxCrossReg`, `GammaTransverse`, `FaceRegClosed` and the event clauses of
`Work.Drive.Final.GoodSweepData2`), every event (`Work.Drive.Final.IsAnyEvent`) is non-degenerate
(`Work.Drive.Mono.NDEvent`).

The three clauses of `NDEvent` are exactly what the bundle already records:

* for `IsEvent`: `|slabFn| < h` is the "no `IsEvent` on a slab face" clause of `GoodSweepData2` and
  the injective Hessian is clause (iii) of `TiltedGenericity`;
* for `IsFaceEvent`: `fderiv slabFnPar ≠ 0` is `FaceRegClosed`, the constrained second derivative is
  the `IsFaceEvent` non-degeneracy clause of `GoodSweepData2`, and `fderiv sweepHeight ≠ 0` at a face
  event follows from the same clause (otherwise the point would also be an `IsEvent` on a slab face,
  which `GoodSweepData2` forbids);
* for `IsCornerEvent`: the single active face and the strict inequalities for the other coordinates
  come from `SlabInBelt` and `EdgeFree` (a point with two active coordinates would be on a box edge,
  hence off the closed slab), the invertible derivative from the universal `SlabBoxCrossReg`, and the
  non-tangency of the level to the face from the second conjunct of `GammaTransverse`. -/
theorem ndEvent_of_datum {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot}
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pt : ℝ × ℝ} (hp : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pt) :
    Work.Drive.Mono.NDEvent ψ s c σ u v h ℓ pt := by
  obtain ⟨hDPkg, hGSD3, _⟩ := hDP
  obtain ⟨hGSD2, hEF, hbelt, hcross, hΓ, hfaceReg, _, _, _, _⟩ := hGSD3
  obtain ⟨_, _, _, hnoEventFace, hfaceND, _⟩ := hGSD2
  obtain ⟨hgen, _⟩ := hDPkg.tilt
  obtain ⟨_, _, hgen3, _⟩ := hgen
  have hs : 0 < s := pos_of_slabCutsBox hDPkg.slabCuts
  rcases hp with hEv | hface_ev | hcor_ev
  · -- ### `IsEvent`: strictly inside the slab, with an injective Hessian
    exact Or.inl ⟨hEv, hnoEventFace pt hEv, (hgen3 pt hEv.1 hEv.2.1 hEv.2.2).1⟩
  · -- ### `IsFaceEvent`: submersions and the constrained second derivative
    have hPBox : Work.BoxShrink.Pinch.par ψ pt ∈ Submission.PBox s c σ := hface_ev.1
    have hslab_face : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ pt)| = h :=
      hface_ev.2.1
    have hDslab : fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) pt ≠ 0 :=
      hfaceReg pt (subset_closure hPBox) hslab_face
    have hsweep : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) pt ≠ 0 := by
      intro h0
      have hIsEv : Work.Drive.Final.IsEvent ψ s c σ u v h ℓ pt := by
        refine ⟨hPBox, ?_, h0⟩
        have h1 : |inner ℝ v (Work.BoxShrink.Pinch.par ψ pt) - (inner ℝ v c + u)| = h := by
          simpa using hslab_face
        exact le_of_eq h1
      exact (not_lt.mpr (le_of_eq hslab_face.symm)) (hnoEventFace pt hIsEv)
    obtain ⟨t₀, ht₀, hnd₀⟩ := hfaceND pt hface_ev
    refine Or.inr (Or.inl ⟨hface_ev, hsweep, hDslab, ?_⟩)
    intro t ht w hw hDw
    have ht_eq : t = t₀ := smul_eq_of_ne_zero hDslab (ht.symm.trans ht₀)
    rw [ht_eq]
    exact hnd₀ w hw hDw
  · -- ### `IsCornerEvent`: a unique active vertical face, transversality and non-tangency
    have hcl : Work.BoxShrink.Pinch.par ψ pt ∈ closure (Submission.PBox s c σ) := hcor_ev.1
    have hbn : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ pt) = s := hcor_ev.2.1
    have hslab_cor : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ pt)| = h :=
      hcor_ev.2.2
    have hz : Work.BoxShrink.Pinch.par ψ pt ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
      Work.BoxShrink.Pinch.par_mem_carrier ψ pt
    have hslab_le : |inner ℝ v (Work.BoxShrink.Pinch.par ψ pt) - (inner ℝ v c + u)| ≤ h := by
      have h1 : |inner ℝ v (Work.BoxShrink.Pinch.par ψ pt) - (inner ℝ v c + u)| = h := by
        simpa using hslab_cor
      exact le_of_eq h1
    obtain ⟨i, ε, hε, hact, huniq⟩ :=
      Work.Drive.Mono.unique_activeFace_of_edgeFree hEF hz hbn hslab_le
    have hfaceNorm : Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ pt) = s := by
      rw [Work.Smooth.BoxGeneric.faceNorm_eq_abs_signedFace,
        Work.Smooth.BoxGeneric.signedFace_eq_of_faceLin_eq hε hact.1]
      rcases hε with h1 | h1
      · rw [h1, one_mul, abs_of_pos hs]
      · rw [h1, neg_one_mul, abs_neg, abs_of_pos hs]
    have hi2 : i ≠ 2 := by
      intro hi
      have hb := hbelt _ hz hcl hslab_le
      rw [hi, Work.Smooth.BoxGeneric.faceNorm_apply,
        div_eq_iff (ne_of_gt (Submission.boxSide_pos 2))] at hfaceNorm
      have hb' : |Work.BoxShrink.Pinch.par ψ pt (σ 2) - c (σ 2)| < s * Submission.boxSide 2 := by
        rw [mul_comm]; exact hb
      linarith
    refine Or.inr (Or.inr ⟨hcor_ev, i, hi2, ?_, ?_, ?_⟩)
    · -- the other vertical coordinates are strictly inside the box
      intro j hj
      have h1 := huniq j hj
      rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_lt_iff₀ (Submission.boxSide_pos j)] at h1
      simpa [mul_comm] using h1
    · -- the pair of face functionals has invertible derivative (`SlabBoxCrossReg`)
      have hface_i : (Work.BoxShrink.Pinch.par ψ pt) (σ i)
          = c (σ i) + ε * Submission.boxSide i * s := by
        have hsf := Work.Smooth.BoxGeneric.signedFace_eq_of_faceLin_eq hε hact.1
        rw [Work.Smooth.BoxGeneric.signedFace_apply,
          div_eq_iff (ne_of_gt (Submission.boxSide_pos i))] at hsf
        have h2 : ε * s * Submission.boxSide i = ε * Submission.boxSide i * s := by ring
        linarith [hsf, h2]
      obtain ⟨η, hη, hslab_i⟩ : ∃ η : ℝ, (η = 1 ∨ η = -1) ∧
          inner ℝ v (Work.BoxShrink.Pinch.par ψ pt) = (inner ℝ v c + u) + η * h := by
        have h0 : 0 ≤ h := le_trans (abs_nonneg _) hslab_le
        have habs : |inner ℝ v (Work.BoxShrink.Pinch.par ψ pt) - (inner ℝ v c + u)| = h := by
          simpa using hslab_cor
        rcases (abs_eq h0).mp habs with h' | h'
        · exact ⟨1, Or.inl rfl, by linarith [h']⟩
        · exact ⟨-1, Or.inr rfl, by linarith [h']⟩
      exact hcross i hi2 ε hε η hη pt hface_i hslab_i
    · -- the level is not tangent to the active face (`GammaTransverse` + the local model)
      have hY := fderiv_coord_eq_smul_fderiv_boxNorm hs hε hact huniq
      exact ne_smul_of_eq_smul hY (hΓ pt hbn (le_of_eq hslab_cor)).2

end

end Work.Drive.Mono
