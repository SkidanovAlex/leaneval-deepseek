import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.extremumCollapse
import Submission.Work.Drive.N2.exists_extremumProfile
import Submission.Work.Drive.N2.goodDrawingOn_of_pieces
import Submission.Work.Drive.N2.pictureOfConfig
import Submission.Work.Drive.N2.footMapDefs
import Submission.Work.Drive.N2.extremumJourney_avoids
import Submission.Work.Drive.N2.norm_le_of_mem_closure_modelBall
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The certified extremum window: wiring

The extremum window block of `Work.Drive.N2.criticalWindowDrawing` (reproved, with the transport rows
required only on the band, in `Submission/Work/Drive/N2/extremumWindowBlock.lean`) produces *some*
good drawing of a value window around an extremum.  The certified form
(`Work.N2C.exists_certifiedWindow_extremum`) needs the drawing to be an explicit hybrid

    `W x = if x ∈ Dm then Work.Drive.N2.extremumCollapse φ μ x else A₀ (Work.Drive.N2.footMap Φ f a x)`

with the picture `A₀` *chosen by the caller* (it is the picture of a round configuration at the
anchor level, which is what makes the certificates at the two levels read off a round configuration).

This file is the assembly: given the datum, the width `ηw` of the window, and a picture `A₀` with the
picture rows at the anchor level `f p + s ηw` (smooth, injective and immersive on the anchor level,
with a positive third coordinate), it produces the profile `μ`, the model radius `b` and the proof
that the hybrid is a good drawing of `(f p - ηw, f p + ηw)`.

The two geometric inputs are produced here as well:

* `anchorAttained`: the anchor level is attained (via the Morse chart);
* `landingRow`: the transport row `f (foot x) = a` for every band point outside the model ball
  (via `Work.Drive.N2.extremumJourney_avoids`).
-/

namespace Work.N2C

open scoped Manifold ContDiff Topology
open Set Filter

namespace Ext

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- `ℝ³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The third coordinate of `ℝ³`, as a continuous linear functional. -/
noncomputable def psi3 : E3 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2

/-- The first two coordinates of `ℝ³`, read as a complex number. -/
noncomputable def toC3 : E3 →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0)) +
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1)).smulRight Complex.I)

lemma psi3_apply (v : E3) : psi3 v = v.ofLp 2 := rfl

lemma toC3_re (v : E3) : (toC3 v).re = v.ofLp 0 := by simp [toC3]

lemma toC3_im (v : E3) : (toC3 v).im = v.ofLp 1 := by simp [toC3]

lemma psi3_roundPic (t : ℝ) : psi3 (Work.Drive.N2.roundPic t) = 0 := by
  rw [psi3_apply]
  simp [Work.Drive.N2.roundPic]

lemma toC3_roundPic (t : ℝ) :
    toC3 (Work.Drive.N2.roundPic t) = Complex.exp ((t : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · rw [toC3_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp [Work.Drive.N2.roundPic]
  · rw [toC3_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp [Work.Drive.N2.roundPic]

lemma toC3_eq_zero_iff (v : E3) : toC3 v = 0 ↔ v.ofLp 0 = 0 ∧ v.ofLp 1 = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := congrArg Complex.re h
      simpa [toC3_re] using h1
    · have h1 := congrArg Complex.im h
      simpa [toC3_im] using h1
  · rintro ⟨h1, h2⟩
    apply Complex.ext <;> simp [toC3_re, toC3_im, h1, h2]

/-- A vector of `ℝ³` with vanishing third coordinate and complex first two coordinates
`r • exp (i φ)` is the round picture point `r • Work.Drive.N2.roundPic φ`. -/
lemma eq_smul_roundPic_of_toC3 {v : E3} {r φ : ℝ} (h2 : psi3 v = 0)
    (h : toC3 v = r • Complex.exp ((φ : ℂ) * Complex.I)) :
    v = r • Work.Drive.N2.roundPic φ := by
  have hre : v.ofLp 0 = r * Real.cos φ := by
    have h1 := congrArg Complex.re h
    rw [toC3_re, Complex.exp_ofReal_mul_I, Complex.smul_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h1
    simpa using h1
  have him : v.ofLp 1 = r * Real.sin φ := by
    have h1 := congrArg Complex.im h
    rw [toC3_im, Complex.exp_ofReal_mul_I, Complex.smul_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at h1
    simpa using h1
  have h3 : v.ofLp 2 = 0 := by rw [← psi3_apply v]; exact h2
  refine PiLp.ext fun j => ?_
  fin_cases j
  · simpa [Work.Drive.N2.roundPic, WithLp.ofLp_smul, PiLp.smul_apply] using hre
  · simpa [Work.Drive.N2.roundPic, WithLp.ofLp_smul, PiLp.smul_apply] using him
  · simpa [Work.Drive.N2.roundPic, WithLp.ofLp_smul, PiLp.smul_apply] using h3

lemma normSq_exp_ofReal_mul_I (t : ℝ) :
    Complex.normSq (Complex.exp ((t : ℂ) * Complex.I)) = 1 := by
  have h1 : ((t : ℂ) * Complex.I).re = 0 := by simp
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, h1, Real.exp_zero, one_pow]

/-- The round picture point `z` of height `h`. -/
noncomputable def mk3 (x y z : ℝ) : E3 := WithLp.toLp 2 ![x, y, z]

@[simp] lemma mk3_zero (x y z : ℝ) : mk3 x y z 0 = x := rfl
@[simp] lemma mk3_one (x y z : ℝ) : mk3 x y z 1 = y := rfl
@[simp] lemma mk3_two (x y z : ℝ) : mk3 x y z 2 = z := rfl

lemma psi3_mk3 (x y z : ℝ) : psi3 (mk3 x y z) = z := by
  rw [psi3_apply]; rfl

/-- **A canonical disjoint round configuration**: unit circles of increasing height. -/
noncomputable def stackConfig (m : ℕ) : Work.Drive.N2.RoundConfig m where
  pos := fun i => mk3 0 0 (10 * ((i : ℕ) : ℝ) + 10)
  rad := fun _ => 1
  hrad := fun _ => one_pos
  phase := fun _ => 0

lemma circle_stackConfig (m : ℕ) (i : Fin m) (t : ℝ) :
    (stackConfig m).circle i t = mk3 (Real.cos (2 * Real.pi * t)) (Real.sin (2 * Real.pi * t))
      (10 * ((i : ℕ) : ℝ) + 10) := by
  ext j <;> fin_cases j <;>
    simp [Work.Drive.N2.RoundConfig.circle, stackConfig, Work.Drive.N2.roundPic, mk3]

lemma psi3_circle_stackConfig (m : ℕ) (i : Fin m) (t : ℝ) :
    psi3 ((stackConfig m).circle i t) = 10 * ((i : ℕ) : ℝ) + 10 := by
  rw [circle_stackConfig, psi3_mk3]

lemma stackConfig_disjoint (m : ℕ) : (stackConfig m).Disjoint := by
  intro i j hij s t h
  have h' : psi3 ((stackConfig m).circle i s) = psi3 ((stackConfig m).circle j t) := by rw [h]
  rw [psi3_circle_stackConfig, psi3_circle_stackConfig] at h'
  have : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by linarith
  exact hij (Fin.ext (Nat.cast_injective this))

open Classical in
/-- **The hybrid drawing of the extremum window**: the radial collapse of the chart on the model ball
and the transported picture outside it. -/
noncomputable def hybridW (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (μ : ℝ → ℝ)
    (b : ℝ) (A₀ : M → E3) (foot : M → M) : M → E3 :=
  fun y => if y ∈ Work.Drive.N2.modelBall φ b then Work.Drive.N2.extremumCollapse φ μ y
    else A₀ (foot y)

/-- **The model ball intersected with a level is compact, hence closed.**  On the source of the
chart `f` is `c + s ‖φ·‖²`, so the level-`u` part of the model ball `{‖φ·‖ < b}` is the preimage of
the sphere of radius `√(s(u-c))` (below `b`), which is compact. -/
theorem isClosed_modelBall_inter_level {f : M → ℝ}
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))}
    {c s b u : ℝ} (hs : s = 1 ∨ s = -1) (hb : 0 < b)
    (hmodel : ∀ y ∈ φ.source, f y = c + s * ((φ y 0) ^ 2 + (φ y 1) ^ 2))
    (hfsm : ∀ x : M, ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f x)
    {C : Set M} (hCcl : IsClosed C) (hCsrc : C ⊆ φ.source)
    (hsub : Work.Drive.N2.modelBall φ b ⊆ C)
    (hbu : |u - c| < b ^ 2) :
    IsClosed (Work.Drive.N2.modelBall φ b ∩ {x : M | f x = u}) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  have hcl : closure (Work.Drive.N2.modelBall φ b ∩ {x : M | f x = u}) ⊆ C :=
    (hCcl.closure_subset_iff).mpr (fun y hy => hsub hy.1)
  have hxsrc : x ∈ φ.source := hCsrc (hcl hx)
  have hfx : f x = u := by
    have hfcont : Continuous f :=
      continuous_iff_continuousAt.mpr fun y => (hfsm y).continuousAt
    have h1 : closure (Work.Drive.N2.modelBall φ b ∩ {x : M | f x = u}) ⊆ {x : M | f x = u} :=
      closure_minimal (fun y hy => hy.2) (isClosed_eq hfcont continuous_const)
    exact h1 hx
  have hnorm2 : ‖φ x‖ ^ 2 = s * (u - c) := by
    have h1 : f x = c + s * ((φ x) 0 ^ 2 + (φ x) 1 ^ 2) := hmodel x hxsrc
    have h2 := Work.Drive.N2.coord_sq_eq_norm_sq (φ x)
    rw [h2] at h1
    rw [hfx] at h1
    have h3 : s * ‖φ x‖ ^ 2 = u - c := by linarith
    rcases hs with h | h <;> rw [h] at h3 ⊢ <;> nlinarith
  have hnorm : ‖φ x‖ < b := by
    have h1 : ‖φ x‖ ^ 2 < b ^ 2 := by
      rw [hnorm2]
      rcases hs with h | h
      · rw [h, one_mul]; linarith [(abs_lt.mp hbu).2]
      · rw [h]
        linarith [(abs_lt.mp hbu).1]
    nlinarith [norm_nonneg (φ x), sq_nonneg (‖φ x‖), sq_nonneg b]
  exact ⟨⟨hxsrc, hnorm⟩, hfx⟩

/-- The model ball of a chart is open. -/
lemma isOpen_modelBall' (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    IsOpen (Work.Drive.N2.modelBall φ r) := by
  have h1 : Work.Drive.N2.modelBall φ r = φ.source ∩ φ ⁻¹' Metric.ball 0 r := by
    ext y
    simp [Work.Drive.N2.modelBall, Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [h1]
  exact φ.isOpen_inter_preimage Metric.isOpen_ball

/-! ## Polar coordinates in the chart plane, and the clopen level argument -/

/-- The two coordinates of `ℝ²`, read as a complex number. -/
noncomputable def toC2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0)) +
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1)).smulRight Complex.I)

lemma toC2_re (v : EuclideanSpace ℝ (Fin 2)) : (toC2 v).re = v.ofLp 0 := by simp [toC2]
lemma toC2_im (v : EuclideanSpace ℝ (Fin 2)) : (toC2 v).im = v.ofLp 1 := by simp [toC2]

lemma normSq_toC2 (v : EuclideanSpace ℝ (Fin 2)) : Complex.normSq (toC2 v) = ‖v‖ ^ 2 := by
  rw [Complex.normSq_apply, toC2_re, toC2_im, EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_two, sq]

lemma norm_toC2 (v : EuclideanSpace ℝ (Fin 2)) : ‖toC2 v‖ = ‖v‖ := by
  have h : ‖toC2 v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_toC2]
  nlinarith [norm_nonneg (toC2 v), norm_nonneg v]

lemma incl23_apply_zero (u : EuclideanSpace ℝ (Fin 2)) : (Work.Drive.N2.incl23 u) 0 = u 0 := by
  simp [Work.Drive.N2.incl23, WithLp.linearEquiv, ContinuousLinearMap.pi_apply]

lemma incl23_apply_one (u : EuclideanSpace ℝ (Fin 2)) : (Work.Drive.N2.incl23 u) 1 = u 1 := by
  simp [Work.Drive.N2.incl23, WithLp.linearEquiv, ContinuousLinearMap.pi_apply]

lemma incl23_apply_two (u : EuclideanSpace ℝ (Fin 2)) : (Work.Drive.N2.incl23 u) 2 = 0 := by
  simp [Work.Drive.N2.incl23, WithLp.linearEquiv, ContinuousLinearMap.pi_apply]

/-- **Polar coordinates in the chart plane**: a point of the plane is its norm times a round
picture vector. -/
lemma exists_roundPic_of_incl23 (v : EuclideanSpace ℝ (Fin 2)) :
    ∃ t : ℝ, Work.Drive.N2.incl23 v = ‖v‖ • Work.Drive.N2.roundPic t := by
  classical
  refine ⟨Complex.arg (toC2 v), ?_⟩
  have hcos : v.ofLp 0 = ‖v‖ * Real.cos (Complex.arg (toC2 v)) := by
    have h := Complex.norm_mul_cos_arg (toC2 v)
    rw [toC2_re, norm_toC2] at h
    exact h.symm
  have hsin : v.ofLp 1 = ‖v‖ * Real.sin (Complex.arg (toC2 v)) := by
    have h := Complex.norm_mul_sin_arg (toC2 v)
    rw [toC2_im, norm_toC2] at h
    exact h.symm
  ext i
  fin_cases i <;>
    simp [Work.Drive.N2.incl23, WithLp.linearEquiv, Work.Drive.N2.roundPic, hcos, hsin,
      WithLp.ofLp_smul, PiLp.smul_apply]

/-- **The clopen argument on a level set.**  A set `S` of points of the level `f = u` which is both
open and closed *in the level* and which meets the image of a continuous level curve contains that
whole image: the image is preconnected, and a preconnected set meeting one member of a separation
lies inside it. -/
theorem mem_of_mem_of_level_clopen {f : M → ℝ} {u : ℝ} {S : Set M}
    (hopen : IsOpen (Subtype.val ⁻¹' S : Set {x : M // f x = u}))
    (hclosed : IsClosed (Subtype.val ⁻¹' S : Set {x : M // f x = u}))
    {γ : ℝ → M} (hγval : ∀ x, f (γ x) = u) (hγcont : Continuous γ) (h0 : γ 0 ∈ S) :
    ∀ x, γ x ∈ S := by
  classical
  set γ' : ℝ → {x : M // f x = u} := fun x => ⟨γ x, hγval x⟩ with hγ'def
  have hcont' : Continuous γ' := Continuous.subtype_mk hγcont (fun x => hγval x)
  have hpre : IsPreconnected (Set.range γ') := by
    simpa using (isPreconnected_univ (α := ℝ)).image γ' hcont'.continuousOn
  set S' : Set {x : M // f x = u} := Subtype.val ⁻¹' S with hS'def
  have hne : (Set.range γ' ∩ S').Nonempty := ⟨γ' 0, ⟨0, rfl⟩, h0⟩
  have hcov : Set.range γ' ⊆ S' ∪ S'ᶜ := by
    intro z _
    by_cases h : z ∈ S' <;> simp [h]
  have hsub : IsPreconnected (Set.range γ') → Set.range γ' ⊆ S' :=
    IsPreconnected.subset_left_of_subset_union hopen hclosed.isOpen_compl disjoint_compl_right
      hcov hne
  intro x
  exact hsub hpre ⟨x, rfl⟩

/-! ## The exposed extremum window with a chosen picture -/

open Classical in
/-- **The exposed extremum window with a chosen picture.**

This is `Work.Drive.N2.extremumWindowExposed` with the transport picture `A₀` (which that theorem
produces existentially from `levelSetEmbedding`) taken as a *hypothesis*: the caller wants a specific
picture (one whose level-`a` image is a disjoint round configuration), so that the window's value
pictures at the two certificate levels read off round configurations.

The rows requested of `A₀` are exactly the rows `extremumWindowExposed` produces. -/
theorem extremumWindowExposed_picture {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hext : D.s₁ D.j = D.s₂ D.j)
    {η : ℝ} (hη : 0 < η) (hηd : η ≤ D.ηd) (hρη : 4 * η ≤ (D.ρ D.j) ^ 2)
    {A₀ : M → EuclideanSpace ℝ (Fin 3)}
    (hA₀sm : ∀ y : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A₀ y)
    (hA₀inj : ∀ x y : M, f x = f p + D.s₁ D.j * η → f y = f p + D.s₁ D.j * η →
      A₀ x = A₀ y → x = y)
    (hA₀imm : ∀ x : M, f x = f p + D.s₁ D.j * η → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) A₀ x v = 0 → v = 0)
    (hA₀third : ∀ y : M, 0 < (A₀ y) 2)
    (hland : ∀ x : M, x ∉ Work.Drive.N2.modelBall (D.φ D.j) (max (D.ρ D.j / 8) (2 * Real.sqrt η)) →
      f x ∈ Set.Ioo (f p - η) (f p + η) →
      f (Work.Drive.N2.footMap D.Φ f (f p + D.s₁ D.j * η) x) = f p + D.s₁ D.j * η) :
    ∃ (b : ℝ) (μ : ℝ → ℝ),
      b = max (D.ρ D.j / 8) (2 * Real.sqrt η) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ ∧ (∀ t : ℝ, 0 < μ t) ∧
      (∀ t : ℝ, t ≤ η → μ t = 1) ∧
      (∀ t : ℝ, b ^ 2 ≤ t → μ t = 1 / Real.sqrt t) ∧
      Work.Drive.N2.GoodDrawingOn f (Set.Ioo (f p - η) (f p + η))
        (fun x : M => if x ∈ Work.Drive.N2.modelBall (D.φ D.j) b then Work.Drive.N2.extremumCollapse (D.φ D.j) μ x
          else A₀ (Work.Drive.N2.footMap D.Φ f (f p + D.s₁ D.j * η) x)) := by
  classical
  have hincl : ∀ u : EuclideanSpace ℝ (Fin 2), (Work.Drive.N2.incl23 u) 2 = 0 := by
    intro u
    simp [Work.Drive.N2.incl23, WithLp.linearEquiv, ContinuousLinearMap.pi_apply]
  set s : ℝ := D.s₁ D.j with hsdef
  have hs : s = 1 ∨ s = -1 := (D.hsgn D.j).1
  have hs₂ : D.s₂ D.j = s := hext.symm
  set c : ℝ := f p with hcdef
  have hfc : f (D.x D.j) = c := by rw [D.hxj, hcdef]
  set b : ℝ := max (D.ρ D.j / 8) (2 * Real.sqrt η) with hbdef
  have hρpos : 0 < D.ρ D.j := D.hρ D.j
  have hηsqrt : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hb_ge : Real.sqrt η < b := by
    rw [hbdef]
    have : Real.sqrt η < 2 * Real.sqrt η := by linarith
    exact lt_of_lt_of_le this (le_max_right _ _)
  have hb2 : η < b ^ 2 := by
    have h2 : 2 * Real.sqrt η ≤ b := by rw [hbdef]; exact le_max_right _ _
    have h3 : 0 ≤ 2 * Real.sqrt η := by linarith
    have h4 : (2 * Real.sqrt η) ^ 2 = 4 * η := by rw [mul_pow, Real.sq_sqrt hη.le]; ring
    nlinarith
  have hb_ge_ρ : D.ρ D.j / 8 ≤ b := by rw [hbdef]; exact le_max_left _ _
  have hb_le_ρ : b ≤ D.ρ D.j := by
    rw [hbdef]
    refine max_le (by linarith) ?_
    have h5 : η ≤ (D.ρ D.j / 2) ^ 2 := by nlinarith
    have h6 : Real.sqrt η ≤ D.ρ D.j / 2 := (Real.sqrt_le_iff).mpr ⟨by linarith, h5⟩
    linarith
  have hmodel : ∀ y ∈ (D.φ D.j).source,
      f y = c + s * ((D.φ D.j y 0) ^ 2 + (D.φ D.j y 1) ^ 2) := by
    intro y hy
    have h := D.hval D.j y hy
    rw [Work.Drive.N2.chartQ] at h
    rw [h, hfc, hext, hs₂]
    ring
  set Dm : Set M := Work.Drive.N2.modelBall (D.φ D.j) b with hDmdef
  have hDm_open : IsOpen Dm := isOpen_modelBall' _ _
  have hDm_sub : Dm ⊆ (D.φ D.j).source := fun y hy => hy.1
  have hDm_sub_C : Dm ⊆ D.C D.j := by
    intro y hy
    exact D.hCop D.j ⟨hy.1, lt_of_lt_of_le hy.2 hb_le_ρ⟩
  have hchart_win : ∀ y ∈ (D.φ D.j).source, f y ∈ Set.Ioo (c - η) (c + η) → y ∈ Dm := by
    intro y hy hb
    have h1 : |f y - c| < η := abs_lt.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
    have h2 : f y - c = s * ((D.φ D.j y 0) ^ 2 + (D.φ D.j y 1) ^ 2) := by
      rw [hmodel y hy]; ring
    have h3 : (D.φ D.j y 0) ^ 2 + (D.φ D.j y 1) ^ 2 < η := by
      have h1' : |s * ((D.φ D.j y 0) ^ 2 + (D.φ D.j y 1) ^ 2)| < η := by
        rw [← h2]; exact h1
      rcases hs with h | h
      · rw [h, one_mul] at h1'
        exact (abs_lt.mp h1').2
      · rw [h] at h1'
        simp only [neg_one_mul, abs_neg] at h1'
        exact (abs_lt.mp h1').2
    have h4 : ‖D.φ D.j y‖ ^ 2 < η := by
      rw [← Work.Drive.N2.coord_sq_eq_norm_sq]; exact h3
    refine ⟨hy, ?_⟩
    have h5 : ‖D.φ D.j y‖ < Real.sqrt η := (Real.lt_sqrt (norm_nonneg _)).mpr h4
    linarith [h5, hb_ge]
  have hfr_no : ∀ x : M, x ∉ Dm → f x ∈ Set.Ioo (c - η) (c + η) → x ∉ closure Dm := by
    intro x hxD hxb hxcl
    have hxsrc : x ∈ (D.φ D.j).source :=
      (D.hCcl D.j).2 (closure_mono hDm_sub_C hxcl)
    exact hxD (hchart_win x hxsrc hxb)
  obtain ⟨μ, hμsm, hμpos, hμone', hμinv⟩ := Work.Drive.N2.exists_extremumProfile hηsqrt hb_ge
  obtain ⟨hmrow1, hmrow2, hmrow3, -, -⟩ :=
    Work.Drive.N2.extremumCollapseBlock f (D.φ D.j) c s hs Dm hDm_open hDm_sub (D.hφ D.j) (D.hφ' D.j)
      hmodel μ hμsm hμpos hηsqrt (le_of_lt hb_ge) hμone' hμinv
  set a : ℝ := c + s * η with hadef
  set foot : M → M := Work.Drive.N2.footMap D.Φ f a with hfootdef
  obtain ⟨hfoot_sm, hfoot_inj, hfoot_imm⟩ :=
    Work.Drive.N2.footMap_rows_noLaw (M := M) (f := f) hf (D.hΦsm) (D.hΦ0) (D.hΦcomp) a
  set gb : M → EuclideanSpace ℝ (Fin 3) := fun x => A₀ (foot x) with hgbdef
  have hbsm : ∀ x : M, x ∉ Dm → f x ∈ Set.Ioo (c - η) (c + η) →
      ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) gb x := fun x _ _ =>
    (hA₀sm (foot x)).comp x (hfoot_sm.contMDiffAt)
  have hgerm : ∀ x : M, x ∉ Dm → f x ∈ Set.Ioo (c - η) (c + η) →
      (f ∘ foot) =ᶠ[𝓝 x] fun _ => a := by
    intro x hxD hxb
    have hxcl : x ∉ closure Dm := hfr_no x hxD hxb
    have hopen : ((closure Dm)ᶜ : Set M) ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hxcl
    have hfc' : Continuous f := hf.continuous
    have hband : Set.Ioo (c - η) (c + η) ∈ 𝓝 (f x) := isOpen_Ioo.mem_nhds hxb
    filter_upwards [hopen, hfc'.continuousAt hband] with y hy hyb
    have hyD : y ∉ Dm := fun h => hy (subset_closure h)
    exact hland y hyD hyb
  have hbinj : ∀ x : M, x ∉ Dm → ∀ y : M, y ∉ Dm →
      f x ∈ Set.Ioo (c - η) (c + η) → f y ∈ Set.Ioo (c - η) (c + η) →
      f x = f y → gb x = gb y → x = y := by
    intro x hxD y hyD hxb hyb hfxy hg
    have hlx : f (foot x) = a := hland x hxD hxb
    have hly : f (foot y) = a := hland y hyD hyb
    exact hfoot_inj x y hfxy (hA₀inj (foot x) (foot y) (by rw [hadef]; exact hlx)
      (by rw [hadef]; exact hly) hg)
  have hbimm : ∀ x : M, x ∉ Dm → f x ∈ Set.Ioo (c - η) (c + η) → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 3) gb x v = 0 → v = 0 := by
    intro x hxD hxb v hv hv'
    have hfootdiff : MDifferentiableAt (𝓡 2) (𝓡 2) foot x := hfoot_sm.mdifferentiableAt (by simp)
    have hAdiff : MDifferentiableAt (𝓡 2) (𝓡 3) A₀ (foot x) :=
      (hA₀sm (foot x)).mdifferentiableAt (by simp)
    have hfdiff : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (foot x) := hf.mdifferentiableAt (by simp)
    have hcompA := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
      (f := foot) (g := A₀) (x := x) hAdiff hfootdiff v
    have hcompF := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
      (f := foot) (g := f) (x := x) hfdiff hfootdiff v
    have hconst : (f ∘ foot) =ᶠ[𝓝 x] fun _ => a := hgerm x hxD hxb
    have hzero0 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (f ∘ foot) x = 0 := by
      rw [hconst.mfderiv_eq_v433]; exact mfderiv_const
    have hzero : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot x) (mfderiv (𝓡 2) (𝓡 2) foot x v) = 0 := by
      rw [← hcompF, hzero0]; exact ContinuousLinearMap.zero_apply v
    have hAzero : mfderiv (𝓡 2) (𝓡 3) A₀ (foot x) (mfderiv (𝓡 2) (𝓡 2) foot x v) = 0 := by
      rw [← hcompA]; exact hv'
    exact hfoot_imm x v hv (hA₀imm (foot x) (by rw [hadef]; exact hland x hxD hxb)
      (mfderiv (𝓡 2) (𝓡 2) foot x v) hzero hAzero)
  have hcross : ∀ x : M, x ∈ Dm → ∀ y : M, y ∉ Dm →
      f x ∈ Set.Ioo (c - η) (c + η) → f y ∈ Set.Ioo (c - η) (c + η) →
      f x = f y → Work.Drive.N2.extremumCollapse (D.φ D.j) μ x ≠ gb y := by
    intro x _ y _ _ _ _ hxy
    have h1 : (Work.Drive.N2.extremumCollapse (D.φ D.j) μ x) 2 = 0 := by
      rw [Work.Drive.N2.extremumCollapse]; exact hincl _
    have h2 : 0 < (gb y) 2 := hA₀third (foot y)
    rw [hxy] at h1
    linarith
  refine ⟨b, μ, hbdef, hμsm, hμpos, ?_, hμinv, ?_⟩
  · intro t ht
    exact hμone' t (by rw [Real.sq_sqrt hη.le]; exact ht)
  · have hmain : Work.Drive.N2.GoodDrawingOn f (Set.Ioo (c - η) (c + η))
        (fun x : M => if x ∈ Dm then Work.Drive.N2.extremumCollapse (D.φ D.j) μ x else gb x) :=
      Work.Drive.N2.goodDrawingOn_of_pieces f (Set.Ioo (c - η) (c + η)) Dm hDm_open
        (Work.Drive.N2.extremumCollapse (D.φ D.j) μ) gb
        (fun x hx _ => hmrow1 x hx) hbsm
        (fun x hxfr hxb => by
          have hxD : x ∉ Dm := fun hxin => hxfr.2 (by rw [hDm_open.interior_eq]; exact hxin)
          exact absurd hxfr.1 (hfr_no x hxD hxb))
        (fun x hx _ => hmrow3 x hx) hbimm
        (fun x hx y hy _ _ hfxy hg => hmrow2 x hx y hy hfxy hg) hbinj hcross
    simpa only [hDmdef, hgbdef, hcdef, hadef, hfootdef] using hmain

end Ext

end Work.N2C
