import Mathlib
import Submission.Work.Drive.N2C.mfrFootPlumbing
import Submission.Work.Drive.N2Lead.mobiusUpperFootKit
import Submission.Work.Drive.N2Lead.mobius_bridgeStar
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.mobiusUpperFarRate
import Submission.Work.Drive.N2Lead.mobius_lowerProfile
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The park (bridge) piece of the twisted Möbius upper picture

At the level `f p + 3η/2`, a point `y` outside the model (saddle) region whose foot lands on the
*marked* component `S.L.γ S.i t₀` of the anchor level has its twisted picture equal to the pushed,
twisted polar *bridge* picture `parkPicture S ε εp Dp (S.Θ t₀)` of the polar angle `Θ t₀`.

The three rows of the park piece are proved here:

* the picture is non-zero on the bridge zone `∃ k, |Θ t₀ - kπ| ≤ φE`, and `(proj2 …).im = 0` forces
  `Θ t₀ ∈ πℤ` (the one-dimensional push profile is strictly increasing with the unique zero `0`, so
  the vanishing of the imaginary part of the picture is equivalent to
  `r (Θ t₀) sin (Θ t₀) cos (π τ ((r (Θ t₀) cos (Θ t₀) + ε)/2ε)) = 0`; the `cos` factor vanishes only
  for `r (Θ t₀) cos (Θ t₀) = 0` because `τ` is injective on `[0,1]`, and the bridge zone excludes
  `cos (Θ t₀) = 0` since `φE < π/2`);
* a positive real value forces `Θ t₀ ∈ 2πℤ` (the real part of the picture is `r (Θ t₀) cos (Θ t₀)`);
* the tangent line of the picture misses the origin (`mobiusTwisted_eventually_foot` + the chain rule
  along the level curve of the foot + the non-radiality hypothesis `hcurve`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

section ParkKit

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- **The pushed, twisted polar bridge picture** of the marked component at the polar angle `φ`:
the planar projection of `pushY Dp εp 1 (twistX ε (-1) (cE3 (r φ · e^{iφ})))`. -/
noncomputable def parkPicture {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : Work.Drive.N2Lead.MobiusPacket D η) (ε εp Dp : ℝ) : ℝ → ℂ :=
  fun φ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
    (Work.Drive.N2.cE3 (S.r φ * Complex.exp (((φ : ℝ) : ℂ) * Complex.I)))))

lemma park_polar_re (r φ : ℝ) :
    (r * Complex.exp (((φ:ℝ):ℂ) * Complex.I)).re = r * Real.cos φ := by
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma park_polar_im (r φ : ℝ) :
    (r * Complex.exp (((φ:ℝ):ℂ) * Complex.I)).im = r * Real.sin φ := by
  rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The `y`-coordinate of the vertical slab twist of a planar point. -/
lemma park_twistX_cE3_one (ε : ℝ) (z : ℂ) :
    (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3 z)) 1
      = z.im * Real.cos (Real.pi * Real.smoothTransition ((z.re + ε)/(2*ε))) := by
  rw [Work.Drive.N2Lead.twistX_eq]
  simp only [neg_one_mul, Work.Drive.N2Lead.twistAngleX, Work.Drive.N2.cE3_apply_zero]
  simp [Work.Drive.N2Lead.rot12, Real.cos_neg, sub_zero]

lemma park_pushProf_one_zero {D ε : ℝ} (hε : 0 < ε) :
    Work.Drive.N2Lead.pushProf D ε 1 0 = 0 := by
  rw [Work.Drive.N2Lead.pushProf, Real.smoothTransition.one_of_one_le le_rfl, one_mul]
  have h : (0 + ε) / (2 * ε) = 1 / 2 := by field_simp; ring
  rw [h, Work.Drive.N2Lead.smoothTransition_one_half]
  ring

/-- The one-dimensional push profile is strictly increasing with the unique zero `0`. -/
lemma park_pushProf_one_eq_zero_iff {D ε : ℝ} (hε : 0 < ε) (hD : 0 ≤ D) {y : ℝ} :
    Work.Drive.N2Lead.pushProf D ε 1 y = 0 ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, park_pushProf_one_zero hε]⟩
  have hmono := Work.Drive.N2Lead.strictMono_pushProf D ε 1 hε hD
  exact hmono.injective (by rw [h, park_pushProf_one_zero hε])

lemma park_expNegInvGlue_pos_eq (x : ℝ) (hx : 0 < x) :
    expNegInvGlue x = Real.exp (-x⁻¹) := by
  rw [expNegInvGlue, if_neg (not_le.mpr hx)]

/-- The smooth transition is injective on `[0,1]`: `τ u = 1/2` forces `u = 1/2`. -/
lemma park_smoothTransition_eq_half {u : ℝ} (h : Real.smoothTransition u = 1 / 2) :
    u = 1 / 2 := by
  have hu1 : u < 1 := by
    by_contra hle
    rw [Real.smoothTransition.one_of_one_le (le_of_not_gt hle)] at h
    norm_num at h
  have hu0 : 0 < u := by
    by_contra hle
    rw [Real.smoothTransition.zero_of_nonpos (le_of_not_gt hle)] at h
    norm_num at h
  have hgu := park_expNegInvGlue_pos_eq u hu0
  have hgv := park_expNegInvGlue_pos_eq (1 - u) (by linarith)
  rw [Real.smoothTransition, hgu, hgv] at h
  have hd : Real.exp (-u⁻¹) + Real.exp (-(1 - u)⁻¹) ≠ 0 := by positivity
  rw [div_eq_iff hd] at h
  have h1 : Real.exp (-(1 - u)⁻¹) = Real.exp (-u⁻¹) := by linarith
  have h2 : -(1 - u)⁻¹ = -u⁻¹ := Real.exp_injective h1
  have h3 : (1 - u)⁻¹ = u⁻¹ := by linarith
  have h4 : 1 - u = u := inv_injective h3
  linarith

/-- `cos (π τ u) = 0` forces `u = 1/2` (`τ u` lies in `[0,1]`, and `π τ u ∈ [0,π]` meets the zero
set of the cosine only at `π/2`). -/
lemma park_eq_half_of_cos_pi_smoothTransition {u : ℝ}
    (hx : Real.cos (Real.pi * Real.smoothTransition u) = 0) : u = 1 / 2 := by
  set a : ℝ := Real.pi * Real.smoothTransition u with ha
  have hα0 : 0 ≤ a := mul_nonneg Real.pi_pos.le (Real.smoothTransition.nonneg u)
  have hαπ : a ≤ Real.pi := by
    have := Real.smoothTransition.le_one u
    simp only [ha]
    nlinarith [Real.pi_pos]
  have hc : Real.cos a = Real.cos (Real.pi / 2) := by rw [ha, hx, Real.cos_pi_div_two]
  have ha2 : a = Real.pi / 2 := Real.strictAntiOn_cos.injOn ⟨hα0, hαπ⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hc
  have hτ : Real.smoothTransition u = 1 / 2 := by
    have h := congrArg (fun t : ℝ => t / Real.pi) ha2
    rw [ha] at h
    field_simp at h
    linarith
  exact park_smoothTransition_eq_half hτ

/-- The rescaling used by the vertical slab twist: `cos (π τ ((x+ε)/2ε)) = 0` forces `x = 0`. -/
lemma park_eq_zero_of_cos_pi_smoothTransition_div {x ε : ℝ} (hε : 0 < ε)
    (h : Real.cos (Real.pi * Real.smoothTransition ((x + ε)/(2*ε))) = 0) : x = 0 := by
  have h2 : (x + ε) / (2 * ε) = 1 / 2 := park_eq_half_of_cos_pi_smoothTransition h
  field_simp at h2
  linarith

lemma park_picture_re {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : Work.Drive.N2Lead.MobiusPacket D η) (ε εp Dp : ℝ) (φ : ℝ) :
    (parkPicture S ε εp Dp φ).re = S.r φ * Real.cos φ := by
  simp only [parkPicture, Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.pushY_eq_prof,
    Work.Drive.N2Lead.pushY_apply_zero, Work.Drive.N2Lead.twistX_first,
    Work.Drive.N2.cE3_apply_zero]
  exact park_polar_re (S.r φ) φ

lemma park_picture_im {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : Work.Drive.N2Lead.MobiusPacket D η) (ε εp Dp : ℝ) (φ : ℝ) :
    (parkPicture S ε εp Dp φ).im = Work.Drive.N2Lead.pushProf Dp εp 1
      (S.r φ * Real.sin φ * Real.cos (Real.pi * Real.smoothTransition
        ((S.r φ * Real.cos φ + ε)/(2*ε)))) := by
  simp only [parkPicture, Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.pushY_eq_prof]
  rw [park_twistX_cE3_one, park_polar_im (S.r φ) φ, park_polar_re (S.r φ) φ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **The vanishing of the imaginary part of the bridge picture**.  Either the polar point is on the
real axis (`sin (Θ t₀) = 0`), or on the imaginary axis (`cos (Θ t₀) = 0`, which the bridge zone
excludes). -/
lemma park_picture_im_eq_zero {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : Work.Drive.N2Lead.MobiusPacket D η) {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp)
    (hDp : 0 ≤ Dp) {θ : ℝ} (him : (parkPicture S ε εp Dp θ).im = 0) :
    S.r θ * Real.sin θ = 0 ∨ S.r θ * Real.cos θ = 0 := by
  have h := him
  rw [park_picture_im] at h
  rw [park_pushProf_one_eq_zero_iff hεp hDp] at h
  rcases mul_eq_zero.mp h with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (park_eq_zero_of_cos_pi_smoothTransition_div hε h2)

lemma park_contDiff_picture {f : M → ℝ} {p : M} {D : Work.Drive.N2.WindowDatum f p} {η : ℝ}
    (S : Work.Drive.N2Lead.MobiusPacket D η) (ε εp Dp : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (parkPicture S ε εp Dp) := by
  have hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun φ : ℝ => ((S.r φ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp S.hr
  have hexp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun φ : ℝ => Complex.exp (((φ : ℝ) : ℂ) * Complex.I)) := by
    apply Complex.contDiff_exp.comp
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp contDiff_id
    · exact contDiff_const
  have hpolar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun φ : ℝ => ((S.r φ : ℝ) : ℂ) * Complex.exp (((φ : ℝ) : ℂ) * Complex.I)) :=
    hr.mul hexp
  have htw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.Drive.N2Lead.E3 => Work.Drive.N2Lead.twistX ε (-1) z) :=
    Work.Drive.N2Lead.contDiff_twistX_fixed ε (-1)
  have hpush : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.Drive.N2Lead.E3 => Work.Drive.N2Lead.pushY Dp εp 1 z) :=
    (Work.Drive.N2Lead.contDiff_pushY Dp εp).comp (contDiff_const.prodMk contDiff_id)
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun φ : ℝ =>
      Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (((S.r φ : ℝ) : ℂ) * Complex.exp (((φ : ℝ) : ℂ) * Complex.I))))) :=
    hpush.comp (htw.comp (Work.Drive.N2.cE3.contDiff.comp hpolar))
  have h2 := Work.Drive.N2Lead.proj2CLM.contDiff.comp h1
  convert h2 using 1
  ext φ
  simp only [Function.comp_apply, Work.Drive.N2Lead.proj2CLM_apply, parkPicture]

end ParkKit

theorem mfrParkPiece {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) {η : ℝ}
    (hη : 0 < η) (hsmall : Work.Drive.N2.packetEtaB D η < 1 / 200)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (S : Work.Drive.N2Lead.MobiusPacket D η) (hshape : Work.Drive.N2C.MobiusShape D η S)
    {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    {y : M} {t₀ : ℝ} (hy : f y = f p + 3 * η / 2)
    (hyD : y ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
      S.Z (39 / 20))
    (hfoot : Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) y = S.L.γ S.i t₀)
    (hzone : ∃ k : ℤ, |S.Θ t₀ - (k : ℝ) * Real.pi|
      ≤ Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50))
    (hcurve : ∀ φ : ℝ, (∃ k : ℤ, |φ - (k : ℝ) * Real.pi|
        ≤ Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50)) →
      Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
          (Work.Drive.N2.cE3 (S.r φ * Complex.exp ((φ : ℂ) * Complex.I))))) ≠ 0 ∧
      (star (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
          (Work.Drive.N2.cE3 (S.r φ * Complex.exp ((φ : ℂ) * Complex.I))))))
        * deriv (fun ψ : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
            (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3
              (S.r ψ * Complex.exp ((ψ : ℂ) * Complex.I)))))) φ).im ≠ 0) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) ≠ 0 ∧
      (∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) y,
        mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) f y v = 0 →
        v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ)
            (fun z : M => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
          = t • Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y))) ∧
      ((Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)).im = 0 →
        ∃ k : ℤ, S.Θ t₀ = (k : ℝ) * Real.pi) ∧
      ((∃ s : ℝ, 0 < s ∧ Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y) = ((s : ℝ) : ℂ)) →
        ∃ k : ℤ, S.Θ t₀ = (k : ℝ) * (2 * Real.pi)) := by
  have hηs : 0 < Work.Drive.N2.packetEta D η := Work.Drive.N2.packetEta_pos D hη
  obtain ⟨-, hφEpos, hφElt⟩ :=
    Work.Drive.N2Lead.leadProfile_phiE (η := Work.Drive.N2.packetEta D η) (m := 99 / 50) hηs
      (by norm_num)
  have hval : Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)
      = parkPicture S ε εp Dp (S.Θ t₀) := by
    rw [Work.Drive.N2Lead.mobiusTwisted_foot hyD, hfoot, S.hC₀val t₀]
    rfl
  have hfun : (fun ψ : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1
        (Work.Drive.N2Lead.twistX ε (-1) (Work.Drive.N2.cE3
          (S.r ψ * Complex.exp (((ψ : ℝ) : ℂ) * Complex.I)))))) = parkPicture S ε εp Dp := rfl
  have hcurveθ : parkPicture S ε εp Dp (S.Θ t₀) ≠ 0 ∧
      (star (parkPicture S ε εp Dp (S.Θ t₀))
        * deriv (parkPicture S ε εp Dp) (S.Θ t₀)).im ≠ 0 := by
    have h := hcurve (S.Θ t₀) hzone
    rw [hfun] at h
    exact h
  have hcosne : Real.cos (S.Θ t₀) ≠ 0 := by
    intro hc0
    obtain ⟨k, hk⟩ := hzone
    obtain ⟨k2, hk2⟩ := Real.cos_eq_zero_iff.mp hc0
    have h2 : S.Θ t₀ = (2 * (k2 : ℝ) + 1) * Real.pi / 2 := hk2
    have h3 : S.Θ t₀ - (k : ℝ) * Real.pi
        = (2 * ((k2 : ℝ) - (k : ℝ)) + 1) * (Real.pi / 2) := by
      rw [h2]; ring
    have h5 : (1 : ℝ) ≤ |(2 * ((k2 : ℝ) - (k : ℝ)) + 1)| := by
      have hcast : ((2 * (k2 - k) + 1 : ℤ) : ℝ) = 2 * ((k2 : ℝ) - (k : ℝ)) + 1 := by
        push_cast; ring
      rw [← hcast]
      exact_mod_cast Int.one_le_abs (by omega : (2 * (k2 - k) + 1 : ℤ) ≠ 0)
    have hk1 : |S.Θ t₀ - (k : ℝ) * Real.pi|
        ≤ Work.Drive.N2Lead.mobiusPhiE (Work.Drive.N2.packetEta D η) (99 / 50) := hk
    rw [h3, abs_mul, abs_of_pos (by positivity : (0:ℝ) < Real.pi / 2)] at hk1
    nlinarith [Real.pi_pos, hφElt, h5, hk1]
  have hnr : ¬ ∃ t : ℝ, deriv (parkPicture S ε εp Dp) (S.Θ t₀)
      = t • parkPicture S ε εp Dp (S.Θ t₀) := by
    rintro ⟨t, ht⟩
    refine hcurveθ.2 ?_
    rw [ht, Complex.real_smul]
    simp only [Complex.star_def, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him0 : (parkPicture S ε εp Dp (S.Θ t₀)).im = 0
      → ∃ k : ℤ, S.Θ t₀ = (k : ℝ) * Real.pi := by
    intro him
    rcases park_picture_im_eq_zero S hε hεp hDp him with h | h
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (ne_of_gt (S.hrpos _))
      · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h1
        exact ⟨n, hn.symm⟩
    · rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 (ne_of_gt (S.hrpos _))
      · exact absurd h1 hcosne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hval]; exact hcurveθ.1
  · -- ## the tangent line of the picture misses the origin
    intro v hv hvne'
    obtain ⟨hfootsm, -, hfootimm⟩ :=
      Work.Drive.N2.footMap_rows_noLaw (f := f) (Φ := D.Φ) (hf := hf) (hΦsm := D.hΦsm)
        (hΦ0 := D.hΦ0) (hΦcomp := D.hΦcomp) (a := f p - 3 * η / 2)
    set foot : M → M := Work.Drive.N2.footMap D.Φ f (f p - 3 * η / 2) with hfootdef
    set Wp : M → Work.Drive.N2Lead.E3 := fun z : M => Work.Drive.N2Lead.pushY Dp εp 1
      (Work.Drive.N2Lead.twistX ε (-1) (S.C₀ z)) with hWpdef
    have hWpsm : ∀ z : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) Wp z := fun z =>
      Work.Drive.N2Lead.mfr_contMDiffAt_pushed (D := D) (η := η) (S := S) (ε := ε) (εp := εp)
        (Dp := Dp) z
    -- the twisted picture is `proj2 ∘ Wp ∘ foot` near `y`
    have hmw : (fun z : M => Work.Drive.N2Lead.proj2
          (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z))
        =ᶠ[𝓝 y] (fun z : M => Work.Drive.N2Lead.proj2 (Wp (foot z))) := by
      filter_upwards [Work.Drive.N2C.mobiusTwisted_eventually_foot (D := D) (η := η) (S := S)
        (ε := ε) (εp := εp) (Dp := Dp) hη hsmall hf (y := y) hy hyD] with z hz
      simp only [hz, hfootdef, hWpdef]
    have hmf1 : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
        = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp (foot z))) y v :=
      DFunLike.congr_fun hmw.mfderiv_eq_v433 v
    have hchain : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2 (Wp (foot z))) y v
        = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (foot y)
            (mfderiv (𝓡 2) (𝓡 2) foot y v) :=
      Work.Drive.N2Lead.mfr_mfderiv_proj2_comp_foot (A := Wp) hfootsm.contMDiffAt hWpsm v
    have hyband : f y ∈ Set.Ioo (f p - 2 * η) (f p + 2 * η) := by
      refine ⟨?_, ?_⟩ <;> rw [hy] <;> linarith
    set region : Set M :=
      Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) S.Z (39 / 20)
      with hregiondef
    have hregionopen : IsOpen region :=
      Work.Drive.N2.isOpen_saddleRegion
        (Work.Drive.N2Lead.isOpen_modelBall_mobius (D.φ D.j) (D.ρ D.j)) S.hZsm
    have hycl_or_fr : y ∈ frontier region ∨ y ∉ closure region := by
      by_cases hfr : y ∈ frontier region
      · exact Or.inl hfr
      · refine Or.inr fun hcl => hfr ?_
        rw [frontier_eq_closure_inter_closure]
        refine ⟨hcl, ?_⟩
        rw [IsClosed.closure_eq (isClosed_compl_iff.mpr hregionopen)]
        exact hyD
    -- the landing row: `f (foot ·)` is constantly the anchor level near `y`
    have hevland : (fun z : M => f (foot z)) =ᶠ[𝓝 y] (fun _ : M => f p - 3 * η / 2) := by
      rcases hycl_or_fr with hfr | hcl
      · exact S.hlandFr y hfr hyband
      · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl,
          hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hyband)] with z hzcl hzf
        have hzD : z ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j))
            S.Z (39 / 20) := fun hzD => hzcl (subset_closure hzD)
        exact S.hfootval z hzD hzf
    have hkerfoot : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot y) (mfderiv (𝓡 2) (𝓡 2) foot y v) = 0 := by
      have h0 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (foot z)) y v = 0 := by
        rw [hevland.mfderiv_eq_v433, mfderiv_const]
        rfl
      rw [Work.Drive.N2Lead.mfr_mfderiv_f_comp_foot hfootsm.contMDiffAt (hf.contMDiffAt) v] at h0
      exact h0
    obtain ⟨s₀, hs₀⟩ :=
      S.L.ker S.i t₀ (mfderiv (𝓡 2) (𝓡 2) foot y v) (by rw [← hfoot]; exact hkerfoot)
    have hs₀ne : s₀ ≠ 0 := by
      intro h0
      refine hvne' (hfootimm y v hv ?_)
      exact hs₀.symm.trans ((congrArg (fun c : ℝ =>
        mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀ c) h0).trans
          (map_zero (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀)))
    have hlevel : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (S.L.γ S.i t₀)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀ s₀)
        = deriv (fun u : ℝ => Work.Drive.N2Lead.proj2 (Wp (S.L.γ S.i u))) t₀ * (s₀ : ℂ) :=
      Work.Drive.N2Lead.mfr_mfderiv_levelCurve_eq_deriv (L := S.L) (W := Wp)
        (fun z _ => hWpsm z) S.i t₀ s₀
    have hcurve_eq : (fun u : ℝ => Work.Drive.N2Lead.proj2 (Wp (S.L.γ S.i u)))
        = fun u : ℝ => parkPicture S ε εp Dp (S.Θ u) := by
      funext u
      simp only [hWpdef]
      rw [S.hC₀val u]
      rfl
    have hderivcomp : deriv (fun u : ℝ => parkPicture S ε εp Dp (S.Θ u)) t₀
        = deriv (parkPicture S ε εp Dp) (S.Θ t₀) * deriv S.Θ t₀ := by
      have h2 : DifferentiableAt ℝ (parkPicture S ε εp Dp) (S.Θ t₀) :=
        ((park_contDiff_picture S ε εp Dp).differentiable (by simp)).differentiableAt
      have h1 : DifferentiableAt ℝ S.Θ t₀ := (S.hΘ.differentiable (by simp)).differentiableAt
      have hcomp : fderiv ℝ (fun u : ℝ => parkPicture S ε εp Dp (S.Θ u)) t₀
          = (fderiv ℝ (parkPicture S ε εp Dp) (S.Θ t₀)).comp (fderiv ℝ S.Θ t₀) := by
        simpa only [Function.comp_def] using fderiv_comp (x := t₀) h2 h1
      calc deriv (fun u : ℝ => parkPicture S ε εp Dp (S.Θ u)) t₀
          = (fderiv ℝ (fun u : ℝ => parkPicture S ε εp Dp (S.Θ u)) t₀) 1 :=
            fderiv_apply_one_eq_deriv.symm
        _ = ((fderiv ℝ (parkPicture S ε εp Dp) (S.Θ t₀)).comp (fderiv ℝ S.Θ t₀)) 1 := by
            rw [hcomp]
        _ = (fderiv ℝ (parkPicture S ε εp Dp) (S.Θ t₀)) ((fderiv ℝ S.Θ t₀) 1) := rfl
        _ = (fderiv ℝ (parkPicture S ε εp Dp) (S.Θ t₀)) (deriv S.Θ t₀) := by
            rw [fderiv_apply_one_eq_deriv]
        _ = (fderiv ℝ (parkPicture S ε εp Dp) (S.Θ t₀)) ((deriv S.Θ t₀) • (1 : ℝ)) := by
            rw [smul_eq_mul, mul_one]
        _ = (deriv S.Θ t₀) • ((fderiv ℝ (parkPicture S ε εp Dp) (S.Θ t₀)) 1) := by
            rw [map_smul]
        _ = (deriv S.Θ t₀) • deriv (parkPicture S ε εp Dp) (S.Θ t₀) := by
            rw [fderiv_apply_one_eq_deriv]
        _ = deriv (parkPicture S ε εp Dp) (S.Θ t₀) * deriv S.Θ t₀ := by
            rw [Complex.real_smul]; ring
    have hGder : mfderiv (𝓡 2) 𝓘(ℝ, ℂ)
          (fun z : M => Work.Drive.N2Lead.proj2
            (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp z)) y v
        = deriv (parkPicture S ε εp Dp) (S.Θ t₀) * (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ) := by
      rw [hmf1, hchain]
      have hfoot' : foot y = S.L.γ S.i t₀ := hfoot
      have hA : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z)) (foot y)
            (mfderiv (𝓡 2) (𝓡 2) foot y v)
          = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
            (S.L.γ S.i t₀) (mfderiv (𝓡 2) (𝓡 2) foot y v) := by rw [hfoot']
      have hB : mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
            (S.L.γ S.i t₀) (mfderiv (𝓡 2) (𝓡 2) foot y v)
          = mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
            (S.L.γ S.i t₀) (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (S.L.γ S.i) t₀ s₀) :=
        congrArg (fun w => mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (fun z : M => Work.Drive.N2Lead.proj2 (Wp z))
          (S.L.γ S.i t₀) w) hs₀.symm
      rw [hA, hB, hlevel, hcurve_eq, hderivcomp]
      rw [Complex.ofReal_mul, mul_assoc]
    rintro ⟨t, ht⟩
    have hcne : deriv S.Θ t₀ * s₀ ≠ 0 := mul_ne_zero (S.hΘderiv t₀) hs₀ne
    rw [hGder, hval, Complex.real_smul] at ht
    have hd : deriv (parkPicture S ε εp Dp) (S.Θ t₀)
        = (t / (deriv S.Θ t₀ * s₀)) • parkPicture S ε εp Dp (S.Θ t₀) := by
      have hc' : (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hcne
      have h1 : deriv (parkPicture S ε εp Dp) (S.Θ t₀)
          = (((t : ℂ) * parkPicture S ε εp Dp (S.Θ t₀))
              / (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ)) := by
        rw [eq_div_iff hc']
        exact ht
      rw [h1, Complex.real_smul]
      have h2 : (((t : ℂ) * parkPicture S ε εp Dp (S.Θ t₀))
            / (((deriv S.Θ t₀ * s₀ : ℝ)) : ℂ))
          = ((t / (deriv S.Θ t₀ * s₀) : ℝ) : ℂ) * parkPicture S ε εp Dp (S.Θ t₀) := by
        rw [Complex.ofReal_div]
        field_simp
      rw [h2]
    exact hnr ⟨t / (deriv S.Θ t₀ * s₀), hd⟩
  · -- ## the imaginary part vanishes only on the real axis
    intro him
    exact him0 (by rw [← hval]; exact him)
  · -- ## a positive real value is on the positive real axis
    rintro ⟨s, hs, hsv⟩
    have him : (parkPicture S ε εp Dp (S.Θ t₀)).im = 0 := by
      rw [← hval, hsv]
      simp
    obtain ⟨k, hk⟩ := him0 him
    have hsin : Real.sin (S.Θ t₀) = 0 := by rw [hk]; simp [Real.sin_int_mul_pi]
    have hre : S.r (S.Θ t₀) * Real.cos (S.Θ t₀) = s := by
      have h1 : (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.mobiusTwisted D η S ε εp Dp y)).re
          = S.r (S.Θ t₀) * Real.cos (S.Θ t₀) := by
        rw [hval, park_picture_re]
      rw [← h1, hsv]
      simp
    have hcospos : 0 < Real.cos (S.Θ t₀) := by
      have hc : Real.cos (S.Θ t₀) = s / S.r (S.Θ t₀) := by
        have hrne : S.r (S.Θ t₀) ≠ 0 := ne_of_gt (S.hrpos _)
        rw [← hre]
        exact (mul_div_cancel_left₀ (Real.cos (S.Θ t₀)) hrne).symm
      rw [hc]
      exact div_pos hs (S.hrpos _)
    have hcos1 : Real.cos (S.Θ t₀) = 1 := by
      have h1 : Real.cos (S.Θ t₀) ^ 2 = 1 := by
        have := Real.cos_sq_add_sin_sq (S.Θ t₀)
        rw [hsin] at this
        nlinarith
      have h2 : (Real.cos (S.Θ t₀) - 1) * (Real.cos (S.Θ t₀) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h2 with h | h
      · linarith
      · linarith
    obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp hcos1
    exact ⟨m, hm.symm⟩


end Work.Drive.N2C
