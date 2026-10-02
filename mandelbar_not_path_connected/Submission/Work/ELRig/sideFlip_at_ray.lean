import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.exists_local_angle_at_lift
import Submission.Work.Top.extAngle_close_of_Phi_close
import Submission.Work.ELTop.pairSides_decomposition

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
variable {L : Work.ELRig.RayCylLift d fl}

/-! ## Elementary facts about the exponential `exp (2πi x)` -/

/-- The imaginary part of `exp (2πi x)`. -/
theorem im_exp_two_pi (x : ℝ) :
    (Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)).im = Real.sin (2 * Real.pi * x) := by
  have hexp : (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hexp, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  rw [Real.exp_zero, one_mul]

/-- The imaginary part of `a * exp (2πi x)` for real `a`. -/
theorem mul_im_exp_two_pi (a x : ℝ) :
    ((a : ℂ) * Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)).im
      = a * Real.sin (2 * Real.pi * x) := by
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, im_exp_two_pi]

/-- For `|x| < 1/2`, the imaginary part of `exp (2πi x)` is positive exactly when `x` is. -/
theorem im_exp_two_pi_pos (x : ℝ) (hx : |x| < 1 / 2) :
    (0 < (Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)).im ↔ 0 < x) := by
  obtain ⟨hxlo, hxhi⟩ := abs_lt.mp hx
  rw [im_exp_two_pi]
  constructor
  · intro h
    by_contra hx0
    push_neg at hx0
    rcases lt_or_eq_of_le hx0 with hxlt | hxeq
    · have hneg : Real.sin (2 * Real.pi * x) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
      linarith
    · rw [hxeq] at h; simp at h
  · intro hxpos
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])

/-- For `|x| < 1/2`, the imaginary part of `exp (2πi x)` is negative exactly when `x` is. -/
theorem im_exp_two_pi_neg (x : ℝ) (hx : |x| < 1 / 2) :
    ((Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)).im < 0 ↔ x < 0) := by
  obtain ⟨hxlo, hxhi⟩ := abs_lt.mp hx
  rw [im_exp_two_pi]
  constructor
  · intro h
    by_contra hx0
    rw [not_lt] at hx0
    rcases lt_or_eq_of_le hx0 with hxpos | hxeq
    · have hpos : 0 < Real.sin (2 * Real.pi * x) :=
        Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
      linarith
    · rw [← hxeq] at h; simp at h
  · intro hxneg
    exact Real.sin_neg_of_neg_of_neg_pi_lt (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos])

/-- Sin form of `im_exp_two_pi_pos`. -/
theorem sin_two_pi_pos (x : ℝ) (hx : |x| < 1 / 2) :
    (0 < Real.sin (2 * Real.pi * x) ↔ 0 < x) := by
  rw [← im_exp_two_pi]; exact im_exp_two_pi_pos x hx

/-- Sin form of `im_exp_two_pi_neg`. -/
theorem sin_two_pi_neg (x : ℝ) (hx : |x| < 1 / 2) :
    (Real.sin (2 * Real.pi * x) < 0 ↔ x < 0) := by
  rw [← im_exp_two_pi]; exact im_exp_two_pi_neg x hx

/-- Multiplying by a positive real preserves the sign. -/
private theorem mul_neg_iff_of_pos_left' {a b : ℝ} (ha : 0 < a) : (a * b < 0 ↔ b < 0) := by
  have h : a * b < 0 ↔ 0 < a * (-b) := by rw [mul_neg, neg_pos]
  rwa [mul_pos_iff_of_pos_left ha, neg_pos] at h

/-! ## The straightening chart as the exponential of the external angle -/

/-- **The straightening chart in polar form.**  Off the filled Julia set, the Böttcher value of
`Ψ w` is `‖·‖ exp (2πi θ)` with `θ` the external angle, and the normalising ray point is
`η exp (2πi α₁)`; hence the chart is `(‖·‖/η) exp (2πi (θ - α₁))`. -/
theorem sideFlipChart_eq_exp (s₀ : ℝ) (w : ℂ) (hwK : fl.Ψ w ∉ Work.EL.K c) :
    sideFlipChart c d fl L s₀ w =
      ((‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖ / L.τ s₀ : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) *
          ((Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) - Work.EL.alpha1 : ℝ) : ℂ) *
          Complex.I) := by
  rw [sideFlipChart_apply]
  have hne : Work.EL.dynPhi c d.φ (fl.Ψ w) ≠ 0 := d.hN.Phi_ne_zero hwK
  have hdyn := Work.Top.Phi_eq_norm_mul_exp_extAngle d.hN hne
  have hrp : Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) =
      ((L.τ s₀ : ℝ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * ((Work.EL.alpha1 : ℝ) : ℂ) * Complex.I) := rfl
  conv_lhs => rw [hdyn, hrp]
  have hsplit : Complex.exp (2 * (Real.pi : ℂ) *
        (((Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) - Work.EL.alpha1 : ℝ)) : ℂ) *
        Complex.I) =
      Complex.exp (2 * (Real.pi : ℂ) *
          ((Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) : ℝ) : ℂ) * Complex.I) /
        Complex.exp (2 * (Real.pi : ℂ) * ((Work.EL.alpha1 : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sub]
    congr 1
    push_cast; ring
  rw [hsplit, Complex.ofReal_div, div_mul_div_comm]

/-! ## The main statement -/

/-- **The side flip along the horizontal line is read off from the straightening chart.**  For
`p = L.γ₁ s₀` in the far-left half plane, the condition that `Ψ` sends `p + t` and `p - t` to
strictly opposite sides of the `α`-pair `P` is equivalent to the imaginary part of the chart
`sideFlipChart c d fl L s₀` at `p + t` and at `p - t` having opposite signs.  (The chart sends the
ray `R(α₁)` to the real axis and `p` to `1`; for `w` near `p` and off both lifts, the sign of the
imaginary part of the chart is the side of `P` containing `Ψ w`.) -/
theorem sideFlip_at_ray {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (P : Work.EL.CoPair d.hN)
    (hPa : P.a = Work.EL.alpha1) (hPb : P.b = Work.EL.alpha2) (hPy : P.y = d.z₁)
    (hside : Work.EL.PairSides d.hN P)
    {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R)
    (hsimple : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₁ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      (fl.Ψ (L.γ₁ s₀ + t) ∈ Work.EL.pairSide P ↔
        ¬ (fl.Ψ (L.γ₁ s₀ - t) ∈ Work.EL.pairSide P))) ↔
    (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      ((0 < (sideFlipChart c d fl L s₀ (L.γ₁ s₀ + t)).im ∧
          (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im < 0) ∨
        ((sideFlipChart c d fl L s₀ (L.γ₁ s₀ + t)).im < 0 ∧
          0 < (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im))) := by
  classical
  -- ### the local angle/side data around `p = L.γ₁ s₀`
  obtain ⟨D, hDopen, hpD, hDsub, hDK, hDγ, hDfar, hDnear⟩ :=
    exists_local_angle_at_lift d fl L P hPa hPb hPy hside hre
  -- ### numerical facts about the root angles
  have hα1pos : 0 < Work.EL.alpha1 := by rw [Work.EL.alpha1]; norm_num
  have hα1lt1 : Work.EL.alpha1 < 1 := by rw [Work.EL.alpha1]; norm_num
  have hα2pos : 0 < Work.EL.alpha2 := by rw [Work.EL.alpha2]; norm_num
  have hα2lt1 : Work.EL.alpha2 < 1 := by rw [Work.EL.alpha2]; norm_num
  have hab : Work.EL.alpha1 < Work.EL.alpha2 := by rw [Work.EL.alpha1, Work.EL.alpha2]; norm_num
  have hd2 : (1 : ℝ) / 100 < Work.EL.alpha2 - Work.EL.alpha1 := by
    rw [Work.EL.alpha1, Work.EL.alpha2]; norm_num
  have hd3 : Work.EL.alpha2 - Work.EL.alpha1 < 1 - 1 / 100 := by
    rw [Work.EL.alpha1, Work.EL.alpha2]; norm_num
  have harcLen : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 = Work.EL.alpha2 - Work.EL.alpha1 := by
    rw [Work.EL.arcLen]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  -- ### the level `η = L.τ s₀`
  have hη1 : 1 < L.τ s₀ := L.hτ1 s₀
  have hηpos : 0 < L.τ s₀ := lt_trans zero_lt_one hη1
  -- ### a radius on which the external angle is close to `α₁`
  obtain ⟨δcl, hδclpos, hδcl⟩ :=
    Work.Top.extAngle_close_of_Phi_close (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c d.φ) d.hN
      hα1pos hα1lt1 hη1 (η := (1 : ℝ) / 100) (by norm_num)
  -- ### a radius contained in `D`
  obtain ⟨rD, hrDpos, hrD⟩ := Metric.isOpen_iff.mp hDopen (L.γ₁ s₀) hpD
  -- ### a radius on which the chart is close to `1`
  obtain ⟨rc, hrcpos, hrc⟩ := Metric.continuousAt_iff.mp
    (sideFlipChart_continuousAt (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀))
    (δcl / L.τ s₀) (by positivity)
  obtain ⟨δs, hδspos, hδs⟩ := hsimple
  -- ### the pointwise equivalence in a neighbourhood of `p`
  have pointwise : ∀ w : ℂ, w ∈ D → dist w (L.γ₁ s₀) < rc →
      w ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((fl.Ψ w ∈ Work.EL.pairSide P ↔ 0 < (sideFlipChart c d fl L s₀ w).im) ∧
       (sideFlipChart c d fl L s₀ w).im ≠ 0) := by
    intro w hwD hwrc hwoff
    have hwR : w.re < -L.R := hDsub hwD
    have hwK : fl.Ψ w ∉ Work.EL.K c := hDK w hwD
    have hcurve : fl.Ψ w ∉ Work.EL.pairCurve P := by
      intro hmem
      exact hwoff ((L.preimage_pairCurve P hPa hPb hPy w hwR).mp hmem)
    let θ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)
    -- the chart is close to `1`
    have hchart_lt : ‖sideFlipChart c d fl L s₀ w - 1‖ < δcl / L.τ s₀ := by
      have h := hrc hwrc
      rw [sideFlipChart_at_p] at h
      rwa [dist_eq_norm] at h
    have hmul : Work.EL.dynPhi c d.φ (fl.Ψ w)
          - Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)
        = Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)
          * (sideFlipChart c d fl L s₀ w - 1) := by
      rw [sideFlipChart_apply, mul_sub, mul_one]
      rw [mul_div_cancel₀ _ (rayPoint_alpha1_ne_zero (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀))]
    have hnorm_eq : ‖Work.EL.dynPhi c d.φ (fl.Ψ w)
          - Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)‖
        = L.τ s₀ * ‖sideFlipChart c d fl L s₀ w - 1‖ := by
      rw [hmul, norm_mul, Work.Top.NakaneData.norm_rayPoint, abs_of_pos hηpos]
    have hdist_cl : ‖Work.EL.dynPhi c d.φ (fl.Ψ w)
          - Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)‖ < δcl := by
      rw [hnorm_eq]
      calc L.τ s₀ * ‖sideFlipChart c d fl L s₀ w - 1‖ < L.τ s₀ * (δcl / L.τ s₀) :=
            mul_lt_mul_of_pos_left hchart_lt hηpos
        _ = δcl := by field_simp
    have hθclose : |θ - Work.EL.alpha1| < 1 / 100 := hδcl (fl.Ψ w) hwK hdist_cl
    have hθlt : θ < 1 := (Work.Top.NakaneData.extAngle_mem_Ico _ _).2
    have hθge : 0 ≤ θ := (Work.Top.NakaneData.extAngle_mem_Ico _ _).1
    -- `θ` is congruent to neither `P.a` nor `P.b` modulo `ℤ`
    have h1 : ∀ k : ℤ, θ ≠ P.a + (k : ℝ) := by
      intro k hk
      rcases eq_or_ne k 0 with hk0 | hkne
      · subst hk0
        have hθa : θ = Work.EL.alpha1 := by rw [hPa] at hk; simpa using hk
        exact hwoff (Or.inl ((hDγ w hwD).mp hθa))
      · have hk1 : (1 : ℤ) ≤ k ∨ k ≤ -1 := by omega
        rw [hPa] at hk
        rcases hk1 with hk1 | hk1
        · have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
          have : (1 : ℝ) < Work.EL.alpha1 + (k : ℝ) := by linarith
          linarith [hk, hθlt]
        · have hk1r : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
          have : Work.EL.alpha1 + (k : ℝ) < 0 := by linarith
          linarith [hk, hθge]
    have h2 : ∀ k : ℤ, θ ≠ P.b + (k : ℝ) := by
      intro k hk
      rcases eq_or_ne k 0 with hk0 | hkne
      · subst hk0
        have hθa : θ = Work.EL.alpha2 := by rw [hPb] at hk; simpa using hk
        have hmem0 : fl.Ψ w ∈ Work.EL.paramRay d.hN Work.EL.alpha2 := by
          rw [← hθa]
          exact Work.Top.mem_paramRay_extAngle (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c d.φ) d.hN hwK
        exact hwoff (Or.inr (L.tailId₂ w hwR hmem0))
      · have hk1 : (1 : ℤ) ≤ k ∨ k ≤ -1 := by omega
        rw [hPb] at hk
        rcases hk1 with hk1 | hk1
        · have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
          have : (1 : ℝ) < Work.EL.alpha2 + (k : ℝ) := by linarith
          linarith [hk, hθlt]
        · have hk1r : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
          have : Work.EL.alpha2 + (k : ℝ) < 0 := by linarith
          linarith [hk, hθge]
    -- the side is decided by the external angle
    have hab' : P.a < P.b := by rw [hPa, hPb]; exact hab
    have hb1' : P.b < P.a + 1 := by rw [hPa, hPb, Work.EL.alpha1, Work.EL.alpha2]; norm_num
    have hfar_iff : fl.Ψ w ∈ Work.EL.pairSide P ↔ Work.EL.InArc θ P.a P.b := by
      constructor
      · intro hf
        rcases Work.ELTop.InArc_or_InArc_near hab' hb1' h1 h2 with harc | harc
        · exact harc
        · exfalso
          have hnear := hDnear w hwD harc
          have hmem : fl.Ψ w ∈ Work.EL.pairSide P ∩ Work.EL.pairSideNear P := ⟨hf, hnear⟩
          rw [Set.disjoint_iff_inter_eq_empty.mp hside.disjoint] at hmem
          exact hmem
      · intro harc; exact hDfar w hwD harc
    -- the far arc near `α₁` is `(α₁, α₂)`
    have harc_iff : Work.EL.InArc θ P.a P.b ↔ Work.EL.alpha1 < θ := by
      rw [hPa, hPb]
      constructor
      · rintro ⟨hpos, hlt⟩
        rw [harcLen] at hlt
        by_contra hle
        rw [not_lt] at hle
        rcases lt_or_eq_of_le hle with hlt' | heq
        · have hxlo := (abs_lt.mp hθclose).1
          have hxmem : Int.fract (θ - Work.EL.alpha1) = (θ - Work.EL.alpha1) + 1 := by
            conv_lhs => rw [show θ - Work.EL.alpha1 = ((θ - Work.EL.alpha1) + 1) + ((-1 : ℤ) : ℝ) from by
              push_cast; ring]
            rw [Int.fract_add_intCast]
            exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
          rw [hxmem] at hlt
          linarith [hlt, hxlo, hd3]
        · rw [← heq] at hpos; simp at hpos
      · intro hgt
        have hpos' : 0 < θ - Work.EL.alpha1 := sub_pos.mpr hgt
        have hfrac : Int.fract (θ - Work.EL.alpha1) = θ - Work.EL.alpha1 :=
          Int.fract_eq_self.mpr ⟨le_of_lt hpos', by linarith [hθclose]⟩
        show 0 < Int.fract (θ - Work.EL.alpha1) ∧
          Int.fract (θ - Work.EL.alpha1) < Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2
        rw [hfrac, harcLen]
        exact ⟨hpos', by linarith [(abs_lt.mp hθclose).2, hd2]⟩
    have hxhalf : |θ - Work.EL.alpha1| < 1 / 2 := by linarith [hθclose]
    have hrpos : 0 < ‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖ / L.τ s₀ := by
      refine div_pos ?_ hηpos
      exact norm_pos_iff.mpr (d.hN.Phi_ne_zero hwK)
    -- the sign of the chart's imaginary part
    have hsign : 0 < (sideFlipChart c d fl L s₀ w).im ↔ Work.EL.alpha1 < θ := by
      rw [sideFlipChart_eq_exp s₀ w hwK, mul_im_exp_two_pi]
      rw [mul_pos_iff_of_pos_left hrpos, sin_two_pi_pos _ hxhalf]
      constructor <;> intro h <;> linarith
    have hsignneg : (sideFlipChart c d fl L s₀ w).im < 0 ↔ θ < Work.EL.alpha1 := by
      rw [sideFlipChart_eq_exp s₀ w hwK, mul_im_exp_two_pi]
      rw [mul_neg_iff_of_pos_left' hrpos, sin_two_pi_neg _ hxhalf]
      constructor <;> intro h <;> linarith
    have hθne : θ ≠ Work.EL.alpha1 := by
      intro h
      exact hwoff (Or.inl ((hDγ w hwD).mp h))
    refine ⟨hfar_iff.trans (harc_iff.trans hsign.symm), ?_⟩
    intro him0
    rw [him0] at hsign hsignneg
    have h1' : ¬ (Work.EL.alpha1 < θ) := fun h => (lt_irrefl (0 : ℝ)) (hsign.mpr h)
    have h2' : ¬ (θ < Work.EL.alpha1) := fun h => (lt_irrefl (0 : ℝ)) (hsignneg.mpr h)
    exact hθne (le_antisymm (not_lt.mp h2') (not_lt.mp h1')).symm
  -- ### assemble
  let R0 : ℝ := min (min rD rc) δs
  have hR0pos : 0 < R0 := lt_min (lt_min hrDpos hrcpos) hδspos
  have hR0_le_rD : R0 ≤ rD := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR0_le_rc : R0 ≤ rc := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR0_le_ds : R0 ≤ δs := min_le_right _ _
  -- the argument at `p ± t`
  have hstep : ∀ t : ℝ, 0 < t → t < R0 →
      ((fl.Ψ (L.γ₁ s₀ + t) ∈ Work.EL.pairSide P ↔
          0 < (sideFlipChart c d fl L s₀ (L.γ₁ s₀ + t)).im) ∧
        (sideFlipChart c d fl L s₀ (L.γ₁ s₀ + t)).im ≠ 0) ∧
      ((fl.Ψ (L.γ₁ s₀ - t) ∈ Work.EL.pairSide P ↔
          0 < (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im) ∧
        (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im ≠ 0) := by
    intro t ht hRt
    have ht_rD : t < rD := lt_of_lt_of_le hRt hR0_le_rD
    have ht_rc : t < rc := lt_of_lt_of_le hRt hR0_le_rc
    have ht_ds : t < δs := lt_of_lt_of_le hRt hR0_le_ds
    obtain ⟨hoffp, hoffm⟩ := hδs t ⟨ht, ht_ds⟩
    have hdp : dist (L.γ₁ s₀ + t) (L.γ₁ s₀) = t := by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hdm : dist (L.γ₁ s₀ - t) (L.γ₁ s₀) = t := by
      rw [dist_eq_norm, show (L.γ₁ s₀ - (t : ℂ)) - L.γ₁ s₀ = -(t : ℂ) by ring,
        norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact ⟨pointwise (L.γ₁ s₀ + t) (hrD (Metric.mem_ball.mpr (by rw [hdp]; exact ht_rD)))
        (by rw [hdp]; exact ht_rc) hoffp,
      pointwise (L.γ₁ s₀ - t) (hrD (Metric.mem_ball.mpr (by rw [hdm]; exact ht_rD)))
        (by rw [hdm]; exact ht_rc) hoffm⟩
  constructor
  · rintro ⟨δ, hδpos, hδ⟩
    refine ⟨min R0 δ, lt_min hR0pos hδpos, fun t ht => ?_⟩
    have hRt : t < R0 := lt_of_lt_of_le ht.2 (min_le_left _ _)
    have htδ : t < δ := lt_of_lt_of_le ht.2 (min_le_right _ _)
    obtain ⟨⟨hAp, hneAp⟩, ⟨hAm, hneAm⟩⟩ := hstep t ht.1 hRt
    have h := hδ t ⟨ht.1, htδ⟩
    rw [hAp, hAm] at h
    rcases lt_or_gt_of_ne hneAp with hu | hu
    · have hv : 0 < (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im := by
        by_contra hv0
        exact absurd (h.mpr hv0) (not_lt.mpr (le_of_lt hu))
      exact Or.inr ⟨hu, hv⟩
    · have hv : (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im < 0 := by
        rcases lt_trichotomy (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im 0 with hv | hv | hv
        · exact hv
        · exact absurd hv hneAm
        · exact absurd hv (h.mp hu)
      exact Or.inl ⟨hu, hv⟩
  · rintro ⟨δ, hδpos, hδ⟩
    refine ⟨min R0 δ, lt_min hR0pos hδpos, fun t ht => ?_⟩
    have hRt : t < R0 := lt_of_lt_of_le ht.2 (min_le_left _ _)
    have htδ : t < δ := lt_of_lt_of_le ht.2 (min_le_right _ _)
    obtain ⟨⟨hAp, hneAp⟩, ⟨hAm, hneAm⟩⟩ := hstep t ht.1 hRt
    have h := hδ t ⟨ht.1, htδ⟩
    rw [hAp, hAm]
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨fun _ => not_lt.mpr (le_of_lt hv), fun _ => hu⟩
    · exact ⟨fun hu' => absurd hu' (not_lt.mpr (le_of_lt hu)), fun hv' => absurd hv hv'⟩

end Work.ELRig
