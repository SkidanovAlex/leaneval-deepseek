import Mathlib
import Submission.Work.Drive.Prelude
import Submission.Work.Drive.tangencyBadSet
import Submission.Work.Drive.exists_close_transverse_noInflection
import Submission.Work.Drive.rankZeroSetTool
import Submission.Work.Drive.fiveCollinearDefs
import Submission.Work.Drive.rank_fivePsi_slice
import Submission.Work.Drive.tangentChord_jet_surjective
import Submission.Work.Drive.trigBasisDD
import Submission.Work.Drive.rank_patchA

/-!
# The two remaining bad sets of the generic reduction

This module defines, in the coefficient space of the bounded degree trigonometric perturbation
family `Work.Drive.pertV` of a smooth knot `r`:

* `tcBad r ρ k` — the coefficients in the ball `Kv ρ` at which some pair of parameters `(a, b)`
  separated by `1/(k+1)` on the parameter circle is a *degenerate tangent chord*: the chord
  `r b - r a` is parallel to the velocity at `a` and the second order functional
  `⟪v a × a a, v b⟫` vanishes;
* `bad5C r ρ k` — the coefficients at which five parameters in `[0, 2π]`, pairwise separated by
  `1/(k+1)`, give five collinear points of the perturbed curve.

Both are closed (they are projections along a compact parameter space of the zero set of a
continuous map) and have empty interior (the coefficient derivative of the associated map has
rank larger than the dimension of the parameter space, so the projection of its zero set has
empty interior by `Work.Drive.interior_zeroSet_projection_empty_of_rank`).

The perturbation family is written in the explicit affine form `tcPos`, `tcVel`, `tcAcc` (equal to
`pertV`, `pertVelV` and the derivative of the latter), in which the dependence on the coefficient
vector is through the linear maps `linSum`; this keeps the Fréchet derivative computations small.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The parameter pair of the tangent–chord condition -/

/-- The space of parameter pairs `(a, b)` of the tangent–chord condition. -/
abbrev TCP := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate of a tangent–chord parameter pair, as a continuous linear map. -/
def tcPaLin : TCP →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 2)).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toContinuousLinearMap)

/-- The second coordinate of a tangent–chord parameter pair, as a continuous linear map. -/
def tcPbLin : TCP →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (1 : Fin 2)).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toContinuousLinearMap)

/-- The first parameter. -/
def tcPa (w : TCP) : ℝ := w.ofLp 0

/-- The second parameter. -/
def tcPb (w : TCP) : ℝ := w.ofLp 1

lemma tcPa_eq : tcPa = ⇑tcPaLin := by funext w; rfl

lemma tcPb_eq : tcPb = ⇑tcPbLin := by funext w; rfl

theorem contDiff_tcPa : ContDiff ℝ ⊤ tcPa := tcPa_eq ▸ tcPaLin.contDiff

theorem contDiff_tcPb : ContDiff ℝ ⊤ tcPb := tcPb_eq ▸ tcPbLin.contDiff

/-- The parameter pair with coordinates `(a, b)`. -/
def tcPar (a b : ℝ) : TCP := WithLp.toLp 2 ![a, b]

@[simp] lemma tcPa_tcPar (a b : ℝ) : tcPa (tcPar a b) = a := by simp [tcPa, tcPar]

@[simp] lemma tcPb_tcPar (a b : ℝ) : tcPb (tcPar a b) = b := by simp [tcPb, tcPar]

/-- The homeomorphism of the parameter pair space with `ℝ²`. -/
def tcHomeo : TCP ≃ₜ (Fin 2 → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toHomeomorph

lemma tcHomeo_apply (w : TCP) : tcHomeo w = w.ofLp := rfl

/-- The compact box of separated parameter pairs in `[0, 2π]²`. -/
def tcBase (k : ℕ) : Set (Fin 2 → ℝ) :=
  {v | v 0 ∈ Set.Icc 0 (2 * Real.pi) ∧ v 1 ∈ Set.Icc 0 (2 * Real.pi) ∧
    (1:ℝ)/(k+1) ≤ csep (v 0) (v 1)}

theorem isCompact_tcBase (k : ℕ) : IsCompact (tcBase k) := by
  have hpi : IsCompact (Set.univ.pi (fun _ : Fin 2 => Set.Icc (0:ℝ) (2 * Real.pi))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcl : IsClosed {v : Fin 2 → ℝ | (1:ℝ)/(k+1) ≤ csep (v 0) (v 1)} := by
    have hcont : Continuous (fun v : Fin 2 → ℝ => csep (v 0) (v 1)) := by
      unfold csep
      exact (((continuous_apply 0).sub (continuous_apply 1)).abs).min
        (continuous_const.sub (((continuous_apply 0).sub (continuous_apply 1)).abs))
    exact isClosed_Ici.preimage hcont
  have heq : tcBase k = Set.univ.pi (fun _ : Fin 2 => Set.Icc (0:ℝ) (2 * Real.pi)) ∩
      {v : Fin 2 → ℝ | (1:ℝ)/(k+1) ≤ csep (v 0) (v 1)} := by
    ext v
    simp only [tcBase, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun i => by fin_cases i <;> assumption, h3⟩
    · rintro ⟨h, h3⟩
      exact ⟨h 0, h 1, h3⟩
  rw [heq]
  exact hpi.inter_right hcl

/-- The compact family of separated parameter pairs, as a subset of `TCP`. -/
def tcKset (k : ℕ) : Set TCP := tcHomeo ⁻¹' tcBase k

lemma mem_tcKset {k : ℕ} {w : TCP} : w ∈ tcKset k ↔ tcBase k (tcHomeo w) := Iff.rfl

theorem isCompact_tcKset (k : ℕ) : IsCompact (tcKset k) := by
  have himg : tcHomeo.symm '' tcBase k = tcKset k := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [tcKset, tcHomeo.symm_apply_apply] using hv
    · intro hw
      exact ⟨tcHomeo w, hw, tcHomeo.symm_apply_apply w⟩
  rw [← himg]
  exact (isCompact_tcBase k).image tcHomeo.symm.continuous

lemma tcKset_spec {k : ℕ} {w : TCP} (hw : w ∈ tcKset k) :
    tcPa w ∈ Set.Icc 0 (2 * Real.pi) ∧ tcPb w ∈ Set.Icc 0 (2 * Real.pi) ∧
      (1:ℝ)/(k+1) ≤ csep (tcPa w) (tcPb w) := by
  have h : tcBase k (tcHomeo w) := hw
  rw [tcHomeo_apply] at h
  exact h

/-! ## The perturbation family in explicit linear form

The perturbed curve, its velocity and its acceleration are *affine* functions of the coefficient
vector; we record them in the explicit form in which the linearity is transparent. -/

/-- The perturbed curve. -/
def tcPos (r : ℝ → Space) (c : Coeff) (t : ℝ) : Space :=
  r t + linSum (fun j => trigBasis j t) c

/-- The velocity of the perturbed curve. -/
def tcVel (r : ℝ → Space) (c : Coeff) (t : ℝ) : Space :=
  velocity r t + linSum (fun j => trigBasisD j t) c

/-- The acceleration of the perturbed curve. -/
def tcAcc (r : ℝ → Space) (c : Coeff) (t : ℝ) : Space :=
  deriv (deriv r) t + linSum (fun j => trigBasisDD j t) c

lemma tcPos_apply (r : ℝ → Space) (c : Coeff) (t : ℝ) :
    tcPos r c t = r t + ∑ j : Fin 9, (trigBasis j t) • coeffProj j c := by
  rw [tcPos, linSum_apply]

lemma tcVel_apply (r : ℝ → Space) (c : Coeff) (t : ℝ) :
    tcVel r c t = velocity r t + ∑ j : Fin 9, (trigBasisD j t) • coeffProj j c := by
  rw [tcVel, linSum_apply]

lemma tcAcc_apply (r : ℝ → Space) (c : Coeff) (t : ℝ) :
    tcAcc r c t = deriv (deriv r) t + ∑ j : Fin 9, (trigBasisDD j t) • coeffProj j c := by
  rw [tcAcc, linSum_apply]

lemma tcPos_eq_pertV (r : ℝ → Space) (c : Coeff) (t : ℝ) : tcPos r c t = pertV r c t := by
  simp [tcPos, pertV, perturb, perturbCorr, linSum_apply, coeffProj_apply]

lemma tcVel_eq_pertVelV (r : ℝ → Space) (c : Coeff) (t : ℝ) : tcVel r c t = pertVelV r c t := by
  simp [tcVel, pertVelV, perturbVel, perturbVelCorr, linSum_apply, coeffProj_apply]

lemma tcAcc_eq_deriv (r : ℝ → Space) (hr : ContDiff ℝ ⊤ r) (c : Coeff) (t : ℝ) :
    tcAcc r c t = deriv (pertVelV r c) t := by
  simp [tcAcc, deriv_pertVelV r hr c, perturbAccCorr, linSum_apply, coeffProj_apply]

lemma tcPos_add_smul (r : ℝ → Space) (c d : Coeff) (t : ℝ) (s : ℝ) :
    tcPos r (c + s • d) t = tcPos r c t + s • ((linSum (fun j => trigBasis j t)) d) := by
  simp only [tcPos, map_add, map_smul]
  abel

lemma tcVel_add_smul (r : ℝ → Space) (c d : Coeff) (t : ℝ) (s : ℝ) :
    tcVel r (c + s • d) t = tcVel r c t + s • ((linSum (fun j => trigBasisD j t)) d) := by
  simp only [tcVel, map_add, map_smul]
  abel

lemma tcAcc_add_smul (r : ℝ → Space) (c d : Coeff) (t : ℝ) (s : ℝ) :
    tcAcc r (c + s • d) t = tcAcc r c t + s • ((linSum (fun j => trigBasisDD j t)) d) := by
  simp only [tcAcc, map_add, map_smul]
  abel

/-! ## The tangent–chord bad map -/

/-- The chord direction of the perturbed curve at the parameter pair. -/
def tcTheta (w : TCP) (δ : Coeff) : Space :=
  (linSum (fun j => trigBasis j (tcPb w)) - linSum (fun j => trigBasis j (tcPa w))) δ

/-- The velocity variation at the first parameter. -/
def tcWv (w : TCP) (δ : Coeff) : Space := (linSum (fun j => trigBasisD j (tcPa w))) δ

/-- The acceleration variation at the first parameter. -/
def tcZv (w : TCP) (δ : Coeff) : Space := (linSum (fun j => trigBasisDD j (tcPa w))) δ

/-- The velocity variation at the second parameter. -/
def tcVv (w : TCP) (δ : Coeff) : Space := (linSum (fun j => trigBasisD j (tcPb w))) δ

/-- The first slot of the tangent–chord map: `(r_c b - r_c a) × v_c a`. -/
def tcE1 (r : ℝ → Space) (z : Coeff × TCP) : Space :=
  cross3 (tcPos r z.1 (tcPb z.2) - tcPos r z.1 (tcPa z.2)) (tcVel r z.1 (tcPa z.2))

/-- The second slot of the tangent–chord map: `⟪v_c a × a_c a, v_c b⟫`. -/
def tcE3 (r : ℝ → Space) (z : Coeff × TCP) : ℝ :=
  inner ℝ (cross3 (tcVel r z.1 (tcPa z.2)) (tcAcc r z.1 (tcPa z.2)))
    (tcVel r z.1 (tcPb z.2))

/-- The tangent–chord bad map of the perturbation family. -/
def tcPsi (r : ℝ → Space) : Coeff × TCP → Space × ℝ := fun z => (tcE1 r z, tcE3 r z)

/-- The tangent–chord bad set at separation scale `k`. -/
def tcBad (r : ℝ → Space) (ρ : ℝ) (k : ℕ) : Set Coeff :=
  {c : Coeff | c ∈ Kv ρ ∧ ∃ w ∈ tcKset k, tcPsi r (c, w) = 0}

/-! ## Joint smoothness -/

lemma contDiff_tcE1 {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ 1 (fun z : Coeff × TCP => tcE1 r z) := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have hPa : ContDiff ℝ 1 (fun z : Coeff × TCP => tcPa z.2) :=
    (contDiff_tcPa.comp contDiff_snd).of_le le_top
  have hPb : ContDiff ℝ 1 (fun z : Coeff × TCP => tcPb z.2) :=
    (contDiff_tcPb.comp contDiff_snd).of_le le_top
  have hsum : ∀ (D : Fin 9 → ℝ → ℝ), (∀ j, ContDiff ℝ ⊤ (D j)) → ∀ (X : Coeff × TCP → ℝ),
      ContDiff ℝ 1 X →
      ContDiff ℝ 1 (fun z : Coeff × TCP => ∑ j : Fin 9, (D j (X z)) • coeffProj j z.1) := by
    intro D hD X hX
    refine ContDiff.sum fun j _ => ?_
    exact ContDiff.smul (((hD j).of_le le_top).comp hX)
      (((coeffProj j).contDiff).comp contDiff_fst)
  have hPosA : ContDiff ℝ 1 (fun z : Coeff × TCP => tcPos r z.1 (tcPa z.2)) := by
    have hfun : (fun z : Coeff × TCP => tcPos r z.1 (tcPa z.2))
        = (fun z : Coeff × TCP =>
            r (tcPa z.2) + ∑ j : Fin 9, (trigBasis j (tcPa z.2)) • coeffProj j z.1) := by
      funext z; rw [tcPos_apply]
    rw [hfun]
    exact ContDiff.add ((hr.smooth.of_le le_top).comp hPa)
      (hsum trigBasis contDiff_trigBasis _ hPa)
  have hPosB : ContDiff ℝ 1 (fun z : Coeff × TCP => tcPos r z.1 (tcPb z.2)) := by
    have hfun : (fun z : Coeff × TCP => tcPos r z.1 (tcPb z.2))
        = (fun z : Coeff × TCP =>
            r (tcPb z.2) + ∑ j : Fin 9, (trigBasis j (tcPb z.2)) • coeffProj j z.1) := by
      funext z; rw [tcPos_apply]
    rw [hfun]
    exact ContDiff.add ((hr.smooth.of_le le_top).comp hPb)
      (hsum trigBasis contDiff_trigBasis _ hPb)
  have hVelA : ContDiff ℝ 1 (fun z : Coeff × TCP => tcVel r z.1 (tcPa z.2)) := by
    have hfun : (fun z : Coeff × TCP => tcVel r z.1 (tcPa z.2))
        = (fun z : Coeff × TCP =>
            velocity r (tcPa z.2) + ∑ j : Fin 9, (trigBasisD j (tcPa z.2)) • coeffProj j z.1) := by
      funext z; rw [tcVel_apply]
    rw [hfun]
    have hv : ContDiff ℝ 1 (fun z : Coeff × TCP => velocity r (tcPa z.2)) :=
      ((hr.smooth.deriv' (n := ⊤)).of_le le_top).comp hPa
    exact ContDiff.add hv (hsum trigBasisD contDiff_trigBasisD _ hPa)
  exact hcross.comp ((hPosB.sub hPosA).prodMk hVelA)

lemma contDiff_tcE3 {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ 1 (fun z : Coeff × TCP => tcE3 r z) := by
  have hcross : ContDiff ℝ 1 (fun p : Space × Space => cross3 p.1 p.2) := by
    simpa [cross3] using (Commons.Analysis.CrossProduct.cross3_contDiff).of_le le_top
  have hPa : ContDiff ℝ 1 (fun z : Coeff × TCP => tcPa z.2) :=
    (contDiff_tcPa.comp contDiff_snd).of_le le_top
  have hPb : ContDiff ℝ 1 (fun z : Coeff × TCP => tcPb z.2) :=
    (contDiff_tcPb.comp contDiff_snd).of_le le_top
  have hsum : ∀ (D : Fin 9 → ℝ → ℝ), (∀ j, ContDiff ℝ ⊤ (D j)) → ∀ (X : Coeff × TCP → ℝ),
      ContDiff ℝ 1 X →
      ContDiff ℝ 1 (fun z : Coeff × TCP => ∑ j : Fin 9, (D j (X z)) • coeffProj j z.1) := by
    intro D hD X hX
    refine ContDiff.sum fun j _ => ?_
    exact ContDiff.smul (((hD j).of_le le_top).comp hX)
      (((coeffProj j).contDiff).comp contDiff_fst)
  have hVelA : ContDiff ℝ 1 (fun z : Coeff × TCP => tcVel r z.1 (tcPa z.2)) := by
    have hfun : (fun z : Coeff × TCP => tcVel r z.1 (tcPa z.2))
        = (fun z : Coeff × TCP =>
            velocity r (tcPa z.2) + ∑ j : Fin 9, (trigBasisD j (tcPa z.2)) • coeffProj j z.1) := by
      funext z; rw [tcVel_apply]
    rw [hfun]
    have hv : ContDiff ℝ 1 (fun z : Coeff × TCP => velocity r (tcPa z.2)) :=
      ((hr.smooth.deriv' (n := ⊤)).of_le le_top).comp hPa
    exact ContDiff.add hv (hsum trigBasisD contDiff_trigBasisD _ hPa)
  have hVelB : ContDiff ℝ 1 (fun z : Coeff × TCP => tcVel r z.1 (tcPb z.2)) := by
    have hfun : (fun z : Coeff × TCP => tcVel r z.1 (tcPb z.2))
        = (fun z : Coeff × TCP =>
            velocity r (tcPb z.2) + ∑ j : Fin 9, (trigBasisD j (tcPb z.2)) • coeffProj j z.1) := by
      funext z; rw [tcVel_apply]
    rw [hfun]
    have hv : ContDiff ℝ 1 (fun z : Coeff × TCP => velocity r (tcPb z.2)) :=
      ((hr.smooth.deriv' (n := ⊤)).of_le le_top).comp hPb
    exact ContDiff.add hv (hsum trigBasisD contDiff_trigBasisD _ hPb)
  have hAccA : ContDiff ℝ 1 (fun z : Coeff × TCP => tcAcc r z.1 (tcPa z.2)) := by
    have hfun : (fun z : Coeff × TCP => tcAcc r z.1 (tcPa z.2))
        = (fun z : Coeff × TCP => deriv (deriv r) (tcPa z.2)
            + ∑ j : Fin 9, (trigBasisDD j (tcPa z.2)) • coeffProj j z.1) := by
      funext z; rw [tcAcc_apply]
    rw [hfun]
    have hv : ContDiff ℝ 1 (fun z : Coeff × TCP => deriv (deriv r) (tcPa z.2)) :=
      (((hr.smooth.deriv' (n := ⊤)).deriv' (n := ⊤)).of_le le_top).comp hPa
    exact ContDiff.add hv (hsum trigBasisDD contDiff_trigBasisDD _ hPa)
  have hh : ContDiff ℝ 1 (fun z : Coeff × TCP =>
      (cross3 (tcVel r z.1 (tcPa z.2)) (tcAcc r z.1 (tcPa z.2)), tcVel r z.1 (tcPb z.2))) :=
    (hcross.comp (hVelA.prodMk hAccA)).prodMk hVelB
  simpa only [tcE3, Function.comp_def] using
    ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := Space)).contDiff.of_le le_top).comp hh

theorem contDiff_tcPsi {r : ℝ → Space} (hr : IsSmoothKnot r) : ContDiff ℝ 1 (tcPsi r) :=
  (contDiff_tcE1 hr).prodMk (contDiff_tcE3 hr)

/-! ## The derivative along a coefficient line -/

lemma hasDerivAt_tcPos (r : ℝ → Space) (t : ℝ) (c₀ δ : Coeff) :
    HasDerivAt (fun s : ℝ => tcPos r (c₀ + s • δ) t) ((linSum (fun j => trigBasis j t)) δ) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => s • ((linSum (fun j => trigBasis j t)) δ))
      ((linSum (fun j => trigBasis j t)) δ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const ((linSum (fun j => trigBasis j t)) δ)
  refine (hbase.const_add (tcPos r c₀ t)).congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [tcPos_add_smul]

lemma hasDerivAt_tcVel (r : ℝ → Space) (t : ℝ) (c₀ δ : Coeff) :
    HasDerivAt (fun s : ℝ => tcVel r (c₀ + s • δ) t) ((linSum (fun j => trigBasisD j t)) δ) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => s • ((linSum (fun j => trigBasisD j t)) δ))
      ((linSum (fun j => trigBasisD j t)) δ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const ((linSum (fun j => trigBasisD j t)) δ)
  refine (hbase.const_add (tcVel r c₀ t)).congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [tcVel_add_smul]

lemma hasDerivAt_tcAcc (r : ℝ → Space) (t : ℝ) (c₀ δ : Coeff) :
    HasDerivAt (fun s : ℝ => tcAcc r (c₀ + s • δ) t) ((linSum (fun j => trigBasisDD j t)) δ) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => s • ((linSum (fun j => trigBasisDD j t)) δ))
      ((linSum (fun j => trigBasisDD j t)) δ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const ((linSum (fun j => trigBasisDD j t)) δ)
  refine (hbase.const_add (tcAcc r c₀ t)).congr_of_eventuallyEq ?_
  filter_upwards with s
  rw [tcAcc_add_smul]

/-- **The coefficient derivative of the first slot of the tangent–chord map.** -/
lemma tcE1_fderiv_apply {r : ℝ → Space} (hr : IsSmoothKnot r) (w : TCP) (c₀ δ : Coeff) :
    (fderiv ℝ (fun c : Coeff => tcE1 r (c, w)) c₀) δ =
      cross3 (tcTheta w δ) (tcVel r c₀ (tcPa w))
        + cross3 (tcPos r c₀ (tcPb w) - tcPos r c₀ (tcPa w)) (tcWv w δ) := by
  have h1 : ContDiff ℝ 1 (fun c : Coeff => tcE1 r (c, w)) :=
    (contDiff_tcE1 hr).comp ((contDiff_id (𝕜 := ℝ)).prodMk contDiff_const)
  have hdiff : DifferentiableAt ℝ (fun c : Coeff => tcE1 r (c, w)) c₀ :=
    (h1.differentiable (by norm_num)).differentiableAt
  refine (Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun c : Coeff => tcE1 r (c, w)) (p := c₀) (e := δ) hdiff).unique ?_
  have hB := hasDerivAt_tcPos r (tcPb w) c₀ δ
  have hA := hasDerivAt_tcPos r (tcPa w) c₀ δ
  have hVA := hasDerivAt_tcVel r (tcPa w) c₀ δ
  have hchord : HasDerivAt (fun s : ℝ =>
      tcPos r (c₀ + s • δ) (tcPb w) - tcPos r (c₀ + s • δ) (tcPa w)) (tcTheta w δ) 0 :=
    hB.sub hA
  have he1 := hasDerivAt_cross3_curves
    (fun s : ℝ => tcPos r (c₀ + s • δ) (tcPb w) - tcPos r (c₀ + s • δ) (tcPa w))
    (fun s : ℝ => tcVel r (c₀ + s • δ) (tcPa w)) hchord hVA
  have he1' : HasDerivAt (fun s : ℝ => cross3
      (tcPos r (c₀ + s • δ) (tcPb w) - tcPos r (c₀ + s • δ) (tcPa w))
      (tcVel r (c₀ + s • δ) (tcPa w)))
      (cross3 (tcTheta w δ) (tcVel r c₀ (tcPa w))
        + cross3 (tcPos r c₀ (tcPb w) - tcPos r c₀ (tcPa w)) (tcWv w δ)) 0 := by
    simpa [tcWv] using he1
  refine he1'.congr_of_eventuallyEq ?_
  filter_upwards with s
  simp only [tcE1]

/-- **The coefficient derivative of the second slot of the tangent–chord map.** -/
lemma tcE3_fderiv_apply {r : ℝ → Space} (hr : IsSmoothKnot r) (w : TCP) (c₀ δ : Coeff) :
    (fderiv ℝ (fun c : Coeff => tcE3 r (c, w)) c₀) δ =
      inner ℝ (cross3 (tcWv w δ) (tcAcc r c₀ (tcPa w))
            + cross3 (tcVel r c₀ (tcPa w)) (tcZv w δ)) (tcVel r c₀ (tcPb w))
        + inner ℝ (cross3 (tcVel r c₀ (tcPa w)) (tcAcc r c₀ (tcPa w))) (tcVv w δ) := by
  have h1 : ContDiff ℝ 1 (fun c : Coeff => tcE3 r (c, w)) :=
    (contDiff_tcE3 hr).comp ((contDiff_id (𝕜 := ℝ)).prodMk contDiff_const)
  have hdiff : DifferentiableAt ℝ (fun c : Coeff => tcE3 r (c, w)) c₀ :=
    (h1.differentiable (by norm_num)).differentiableAt
  refine (Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun c : Coeff => tcE3 r (c, w)) (p := c₀) (e := δ) hdiff).unique ?_
  have hVA := hasDerivAt_tcVel r (tcPa w) c₀ δ
  have hVB := hasDerivAt_tcVel r (tcPb w) c₀ δ
  have hAA := hasDerivAt_tcAcc r (tcPa w) c₀ δ
  have hcross' := hasDerivAt_cross3_curves
    (fun s : ℝ => tcVel r (c₀ + s • δ) (tcPa w))
    (fun s : ℝ => tcAcc r (c₀ + s • δ) (tcPa w)) hVA hAA
  have he3 := HasDerivAt.inner ℝ hcross' hVB
  have he3' : HasDerivAt (fun s : ℝ => inner ℝ
      (cross3 (tcVel r (c₀ + s • δ) (tcPa w)) (tcAcc r (c₀ + s • δ) (tcPa w)))
      (tcVel r (c₀ + s • δ) (tcPb w)))
      (inner ℝ (cross3 (tcWv w δ) (tcAcc r c₀ (tcPa w))
            + cross3 (tcVel r c₀ (tcPa w)) (tcZv w δ)) (tcVel r c₀ (tcPb w))
        + inner ℝ (cross3 (tcVel r c₀ (tcPa w)) (tcAcc r c₀ (tcPa w))) (tcVv w δ)) 0 := by
    simpa [tcWv, tcZv, tcVv, add_comm, add_left_comm, add_assoc] using he3
  refine he3'.congr_of_eventuallyEq ?_
  filter_upwards with s
  simp only [tcE3]

/-- **The coefficient derivative of the tangent–chord map, as a pair.** -/
lemma tc_fderiv_slice_eq {r : ℝ → Space} (hr : IsSmoothKnot r) (w : TCP) (c₀ : Coeff) :
    fderiv ℝ (fun c : Coeff => tcPsi r (c, w)) c₀
      = (fderiv ℝ (fun c : Coeff => tcE1 r (c, w)) c₀).prod
          (fderiv ℝ (fun c : Coeff => tcE3 r (c, w)) c₀) := by
  have h1 : ContDiff ℝ 1 (fun c : Coeff => tcE1 r (c, w)) :=
    (contDiff_tcE1 hr).comp ((contDiff_id (𝕜 := ℝ)).prodMk contDiff_const)
  have h2 : ContDiff ℝ 1 (fun c : Coeff => tcE3 r (c, w)) :=
    (contDiff_tcE3 hr).comp ((contDiff_id (𝕜 := ℝ)).prodMk contDiff_const)
  have hd1 : DifferentiableAt ℝ (fun c : Coeff => tcE1 r (c, w)) c₀ :=
    (h1.differentiable (by norm_num)).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun c : Coeff => tcE3 r (c, w)) c₀ :=
    (h2.differentiable (by norm_num)).differentiableAt
  have hp := hd1.hasFDerivAt.prodMk hd2.hasFDerivAt
  rw [show (fun c : Coeff => tcPsi r (c, w))
      = (fun c : Coeff => (tcE1 r (c, w), tcE3 r (c, w))) from rfl]
  exact hp.fderiv

/-! ## The coefficient directions realizing prescribed data -/

lemma linSum_sub_symm (a b : ℝ) (c' : Fin 9 → Space) :
    ((linSum (fun j => trigBasis j b) - linSum (fun j => trigBasis j a)) (eCoeff.symm c'))
      = ∑ j, (trigBasis j b - trigBasis j a) • c' j := by
  rw [ContinuousLinearMap.sub_apply, linSum_eCoeff_symm, linSum_eCoeff_symm,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => (sub_smul _ _ _).symm

/-- **The data of a coefficient direction.**  The four quantities below are the linear part of
the tangent–chord data map at the parameter pair `w`. -/
theorem tc_jet_surjective {w : TCP} (h : Real.cos (tcPb w - tcPa w) ≠ 1) (θ ζ ξ η : Space) :
    ∃ δ : Coeff, tcTheta w δ = θ ∧ tcWv w δ = ξ ∧ tcVv w δ = η ∧ tcZv w δ = ζ := by
  obtain ⟨c', h1, h2, h3, h4⟩ :=
    tangentChord_jet_surjective (a := tcPa w) (b := tcPb w) h θ ξ η ζ
  refine ⟨eCoeff.symm c', ?_, ?_, ?_, ?_⟩
  · rw [tcTheta, linSum_sub_symm, h1]
  · rw [tcWv, linSum_eCoeff_symm, h2]
  · rw [tcVv, linSum_eCoeff_symm, h3]
  · rw [tcZv, linSum_eCoeff_symm, h4]

/-! ## The rank bound -/

/-- **A cross-product knob and a scalar knob contribute additively to the rank.** -/
lemma cross_scalar_knob_rank {E : Type*} [AddCommGroup E] [Module ℝ E]
    {D : E →ₗ[ℝ] Space × ℝ} {f : Space →ₗ[ℝ] Space} (dir : Space → E) (δs : E) {s : ℝ}
    (h₁ : ∀ u : Space, D (dir u) = (f u, 0)) (h₂ : D δs = (0, s)) (hs : s ≠ 0) :
    Module.finrank ℝ (LinearMap.range f) + 1 ≤ Module.finrank ℝ (LinearMap.range D) := by
  let Ψ : ((LinearMap.range f) × ℝ) →ₗ[ℝ] (LinearMap.range D) :=
    { toFun := fun p =>
        ⟨(p.1.1, p.2), by
          obtain ⟨u, hu⟩ := p.1.2
          refine ⟨dir u + p.2 • (s⁻¹ • δs), ?_⟩
          rw [map_add, map_smul, map_smul, h₁ u, h₂, hu]
          simp only [Prod.smul_mk, smul_eq_mul, smul_zero, Prod.mk_add_mk, add_zero]
          congr 1
          rw [inv_mul_cancel₀ hs, mul_one, zero_add]⟩
      map_add' := fun p q => by apply Subtype.ext; simp
      map_smul' := fun c p => by apply Subtype.ext; simp }
  have hΨ : Function.Injective Ψ := by
    intro p q hpq
    have h1 : (p.1.1, p.2) = (q.1.1, q.2) := by
      have := congrArg Subtype.val hpq
      simpa [Ψ] using this
    have h2 : p.1.1 = q.1.1 := congrArg (fun z : Space × ℝ => z.1) h1
    have h3 : p.2 = q.2 := congrArg (fun z : Space × ℝ => z.2) h1
    exact Prod.ext (Subtype.ext h2) h3
  have hle := LinearMap.finrank_le_finrank_of_injective (f := Ψ) hΨ
  rw [Module.finrank_prod, Module.finrank_self] at hle
  linarith

/-- **The coefficient derivative of the tangent–chord map has rank at least three.** -/
theorem rank_tcPsi_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (w : TCP) (c₀ : Coeff)
    (hcos : Real.cos (tcPb w - tcPa w) ≠ 1)
    (hvel : tcVel r c₀ (tcPa w) ≠ 0)
    (hcurv : cross3 (tcVel r c₀ (tcPa w)) (tcAcc r c₀ (tcPa w)) ≠ 0) :
    3 ≤ Module.finrank ℝ
      (LinearMap.range ((fderiv ℝ (fun c : Coeff => tcPsi r (c, w)) c₀).toLinearMap)) := by
  set V : Space := tcVel r c₀ (tcPa w) with hV
  set A : Space := tcAcc r c₀ (tcPa w) with hA
  set f : Space →ₗ[ℝ] Space := rpa_crossLin V with hf
  have hfr : Module.finrank ℝ (LinearMap.range f) = 2 := by
    rw [hf]; exact rpa_finrank_range_crossLin hvel
  set D : Coeff →ₗ[ℝ] Space × ℝ :=
    (fderiv ℝ (fun c : Coeff => tcPsi r (c, w)) c₀).toLinearMap with hD
  have hpair : ∀ δ : Coeff, D δ =
      ((fderiv ℝ (fun c : Coeff => tcE1 r (c, w)) c₀) δ,
        (fderiv ℝ (fun c : Coeff => tcE3 r (c, w)) c₀) δ) := by
    intro δ
    rw [hD]
    show (fderiv ℝ (fun c : Coeff => tcPsi r (c, w)) c₀) δ = _
    rw [tc_fderiv_slice_eq hr w c₀]
    rfl
  have hdir : ∀ u : Space, ∃ δ : Coeff, D δ = (f u, 0) := by
    intro u
    obtain ⟨δ, hδ1, hδ2, hδ3, hδ4⟩ := tc_jet_surjective hcos u 0 0 0
    refine ⟨δ, ?_⟩
    rw [hpair δ, tcE1_fderiv_apply hr w c₀ δ, tcE3_fderiv_apply hr w c₀ δ,
      hδ1, hδ2, hδ3, hδ4]
    simp only [cross3_zero_right, cross3_zero_left, zero_add, add_zero, inner_zero_left,
      inner_zero_right, hV, hA]
    rw [hf, rpa_crossLin_apply]
  have hscal : ∃ δ : Coeff, D δ = (0, inner ℝ (cross3 V A) (cross3 V A)) := by
    obtain ⟨δ, hδ1, hδ2, hδ3, hδ4⟩ := tc_jet_surjective hcos 0 0 0 (cross3 V A)
    refine ⟨δ, ?_⟩
    rw [hpair δ, tcE1_fderiv_apply hr w c₀ δ, tcE3_fderiv_apply hr w c₀ δ,
      hδ1, hδ2, hδ3, hδ4]
    simp only [cross3_zero_right, cross3_zero_left, zero_add, add_zero, inner_zero_left,
      inner_zero_right, hV, hA]
  obtain ⟨δs, hδs⟩ := hscal
  have hs : inner ℝ (cross3 V A) (cross3 V A) ≠ 0 := by
    rw [inner_self_ne_zero]
    exact hcurv
  have hrank := cross_scalar_knob_rank (D := D) (f := f)
    (fun u => Classical.choose (hdir u)) δs (fun u => Classical.choose_spec (hdir u)) hδs hs
  rw [hfr] at hrank
  rw [hD] at hrank
  exact hrank

/-! ## The bad set has empty interior -/

theorem tcBad_interior_empty {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ c ∈ Kv ρ, IsSmoothKnot (pertV r c))
    (hcurv : ∀ c ∈ Kv ρ, ∀ t : ℝ, cross3 (tcVel r c t) (tcAcc r c t) ≠ 0)
    (k : ℕ) : interior (tcBad r ρ k) = ∅ := by
  refine interior_zeroSet_projection_empty_of_rank (hΨ := contDiff_tcPsi hr)
    (hKv := isCompact_Kv ρ) (hK := isCompact_tcKset k) ?_
  intro p hp hp0
  have hspec := tcKset_spec hp.2
  obtain ⟨hpc, hpa, hpb, hsep⟩ := hp.1, hspec.1, hspec.2.1, hspec.2.2
  have hcos : Real.cos (tcPb p.2 - tcPa p.2) ≠ 1 := by
    have h := cos_ne_one_of_csep_pos hpa hpb (lt_of_lt_of_le (by positivity) hsep)
    rw [show tcPb p.2 - tcPa p.2 = -(tcPa p.2 - tcPb p.2) by ring, Real.cos_neg]
    intro hc
    exact h (by linarith)
  have hvel : tcVel r p.1 (tcPa p.2) ≠ 0 := by
    rw [tcVel_eq_pertVelV]
    have h := (hS p.1 hpc).regular (tcPa p.2)
    rwa [velocity_pertV hr.smooth p.1 (tcPa p.2)] at h
  have hcv := hcurv p.1 hpc (tcPa p.2)
  have hrank := rank_tcPsi_slice hr p.2 p.1 hcos hvel hcv
  have hle := range_fderiv_slice_le (contDiff_tcPsi hr) p
  have hmono := Submodule.finrank_mono hle
  have hfin : Module.finrank ℝ TCP = 2 := finrank_euclideanSpace_fin
  omega

theorem tcBad_isClosed {r : ℝ → Space} (hr : IsSmoothKnot r) (ρ : ℝ) (k : ℕ) :
    IsClosed (tcBad r ρ k) :=
  isClosed_badSet (K := tcKset k) (isCompact_tcKset k) (contDiff_tcPsi hr).continuous ρ

/-! ## The five-collinear bad set -/

/-- The five-collinear bad set at separation scale `k`: the coefficients in the ball `Kv ρ` for
which five pairwise `1/(k+1)`-separated parameters of `[0, 2π]` give five collinear points of the
perturbed curve. -/
def bad5C (r : ℝ → Space) (ρ : ℝ) (k : ℕ) : Set Coeff :=
  {c : Coeff | c ∈ Kv ρ ∧ ∃ w ∈ K5 k, fivePsi r (c, w) = 0}

theorem bad5C_interior_empty {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ c ∈ Kv ρ, IsSmoothKnot (pertV r c)) (k : ℕ) : interior (bad5C r ρ k) = ∅ := by
  refine interior_zeroSet_projection_empty_of_rank (hΨ := contDiff_fivePsi hr)
    (hKv := isCompact_Kv ρ) (hK := isCompact_K5 k) ?_
  intro p hp hp0
  obtain ⟨hpc, hpw⟩ := hp
  obtain ⟨hIcc, hsep⟩ := mem_K5.mp hpw
  have hJ : Function.Surjective (valLin p.2) := valLin_surjective_of_mem_K5 hpw
  have hne := pertV_ne_of_csep_pos hr (hS p.1 hpc) (hIcc 1) (hIcc 0)
    (lt_of_lt_of_le (by positivity) (hsep 1 0 (by decide)))
  have hd : pertV r p.1 (p.2 1) - pertV r p.1 (p.2 0) ≠ 0 := sub_ne_zero.mpr hne
  have hrk := rank_fivePsi_slice hr p.2 p.1 hJ hd
  have hle := range_fderiv_slice_le (contDiff_fivePsi hr) p
  have hmono := Submodule.finrank_mono hle
  have hfin : Module.finrank ℝ Param5 = 5 := by simp
  omega

theorem bad5C_isClosed {r : ℝ → Space} (hr : IsSmoothKnot r) (ρ : ℝ) (k : ℕ) :
    IsClosed (bad5C r ρ k) :=
  isClosed_badSet (K := K5 k) (isCompact_K5 k) (contDiff_fivePsi hr).continuous ρ

end

end Work.Drive
