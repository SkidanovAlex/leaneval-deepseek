import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.levelCurves_ofComponentCurves
import Submission.Work.Drive.N2C.exists_reparam_unitCircle
import Submission.Work.Drive.N2.roundConfigDefs
import Submission.Work.Drive.N2.roundConfigPath
import Submission.Work.Drive.N2.roundConfigPicture
import Submission.Work.Drive.N2.orientationFlipDefs

/-!
# `N2C` D2e: `isCertifiedAt_of_roundImage`

If a level isotopy `e` of the regular level `f = u` reads its time-`1` picture as `n` disjoint
round circles (through a parametrisation `L` of the level), then the level picture `g = e 0` is
*certified*: there is a parametrisation `L'` of the level and a round configuration `D` such that
`e 1` reads `D` through `L'`.

The proof reparametrises `L` by the angle of the round circle: for each component curve the curve
`x ↦ e 1 (L.γ i x) - c i` is `r i` times the round picture of a smooth angle, and the angle is a
`C^∞` strictly monotone function with period shift `±2π`; its inverse is smooth by the inverse
function theorem.  The analytic input is isolated in `exists_reparam_unitCircle_aux`.
-/

namespace Work.N2C

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- `ℝ³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## The two coordinate projections of `ℝ³` -/

/-- The last coordinate of `ℝ³`. -/
def psi3 : E3 →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2

/-- The first two coordinates of `ℝ³`, read as a complex number. -/
def toC3 : E3 →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0)) +
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1)).smulRight Complex.I)

theorem psi3_apply (v : E3) : psi3 v = v.ofLp 2 := rfl

theorem toC3_re (v : E3) : (toC3 v).re = v.ofLp 0 := by simp [toC3]

theorem toC3_im (v : E3) : (toC3 v).im = v.ofLp 1 := by simp [toC3]

theorem psi3_roundPic (t : ℝ) : psi3 (Work.Drive.N2.roundPic t) = 0 := by
  rw [psi3_apply]
  simp [Work.Drive.N2.roundPic]

theorem toC3_roundPic (t : ℝ) :
    toC3 (Work.Drive.N2.roundPic t) = Complex.exp ((t : ℂ) * Complex.I) := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · rw [toC3_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp [Work.Drive.N2.roundPic]
  · rw [toC3_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp [Work.Drive.N2.roundPic]

theorem toC3_eq_zero_iff (v : E3) : toC3 v = 0 ↔ v.ofLp 0 = 0 ∧ v.ofLp 1 = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := congrArg Complex.re h
      simpa [toC3_re] using h1
    · have h1 := congrArg Complex.im h
      simpa [toC3_im] using h1
  · rintro ⟨h1, h2⟩
    apply Complex.ext <;> simp [toC3_re, toC3_im, h1, h2]

theorem eq_zero_of_toC3_eq_zero_of_psi3_eq_zero {v : E3} (h1 : toC3 v = 0)
    (h2 : psi3 v = 0) : v = 0 := by
  obtain ⟨ha, hb⟩ := (toC3_eq_zero_iff v).mp h1
  refine PiLp.ext fun i => ?_
  fin_cases i
  · simpa using ha
  · simpa using hb
  · simpa [psi3_apply v] using h2

theorem eq_of_toC3_eq_of_psi3_eq {v w : E3} (h1 : toC3 v = toC3 w) (h2 : psi3 v = psi3 w) :
    v = w := by
  have h0 : v.ofLp 0 = w.ofLp 0 := by
    have := congrArg Complex.re h1
    simpa [toC3_re] using this
  have h1' : v.ofLp 1 = w.ofLp 1 := by
    have := congrArg Complex.im h1
    simpa [toC3_im] using this
  have h2' : v.ofLp 2 = w.ofLp 2 := by
    rw [← psi3_apply v, ← psi3_apply w, h2]
  refine PiLp.ext fun i => ?_
  fin_cases i
  · simpa using h0
  · simpa using h1'
  · simpa using h2'

/-- A vector of `ℝ³` whose first two coordinates vanish in `ℂ`, whose third coordinate vanishes,
and whose complex coordinate is a real multiple of `exp (i φ)`, is that round-picture point. -/
theorem eq_smul_roundPic_of_toC3 {v : E3} {r φ : ℝ} (h2 : psi3 v = 0)
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

/-! ## Two arithmetic lemmas about an integer displacement -/

/-- Two points of `[0,1)` differing by an integer coincide. -/
theorem eq_of_sub_intCast_of_mem_Ico {x y : ℝ} (hx : x ∈ Set.Ico 0 1) (hy : y ∈ Set.Ico 0 1)
    {k : ℤ} (hk : x - y = (k : ℝ)) : x = y := by
  have hlt : |(k : ℝ)| < 1 := by
    have h1 : 0 ≤ x := hx.1
    have h2 : x < 1 := hx.2
    have h3 : 0 ≤ y := hy.1
    have h4 : y < 1 := hy.2
    rw [abs_lt]
    constructor <;> linarith
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
  rw [hk0] at hk
  push_cast at hk
  linarith

/-- Periodicity of a real function with period shift `1` upgrades to integer shifts. -/
theorem shift_int_of_shift_one {τ : ℝ → ℝ} {ε : ℤ} (hshift : ∀ x, τ (x + 1) = τ x + (ε : ℝ))
    (m : ℤ) (x : ℝ) : τ (x + (m : ℝ)) = τ x + ((ε * m : ℤ) : ℝ) := by
  have hper : ∀ z : ℝ, (fun w : ℝ => τ w - (ε : ℝ) * w) (z + 1) =
      (fun w : ℝ => τ w - (ε : ℝ) * w) z := by
    intro z
    change τ (z + 1) - (ε : ℝ) * (z + 1) = τ z - (ε : ℝ) * z
    rw [hshift z]
    ring
  have h := Work.Drive.N2C.eq_of_add_intCast_of_periodic
    (γ := fun w : ℝ => τ w - (ε : ℝ) * w) hper x m
  have hthis : τ (x + (m : ℝ)) - (ε : ℝ) * (x + (m : ℝ)) = τ x - (ε : ℝ) * x := h
  have h' : τ (x + (m : ℝ)) = τ x + (ε : ℝ) * (m : ℝ) := by linarith [hthis]
  rw [h']
  push_cast
  ring

/-- A shift by `ε * n` with `ε = ±1` undoes an integer displacement of `τ`. -/
theorem tau_inj_mod {τ : ℝ → ℝ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hshift : ∀ x, τ (x + 1) = τ x + (ε : ℝ)) (hinj : Function.Injective τ)
    {x y : ℝ} (h : ∃ k : ℤ, τ x - τ y = (k : ℝ)) : ∃ k : ℤ, x - y = (k : ℝ) := by
  obtain ⟨n, hn⟩ := h
  have hstep := shift_int_of_shift_one hshift (ε * n) y
  have hεε : ε * (ε * n) = n := by
    rcases hε with h | h <;> subst h <;> ring
  rw [hεε] at hstep
  have heq : y + ((ε * n : ℤ) : ℝ) = x := by
    apply hinj
    rw [hstep]
    linarith
  exact ⟨ε * n, by linarith⟩

/-! ## Smoothness of the level curve -/

theorem contMDiffAt_eval_level {f : M → ℝ} {u : ℝ} {e : ℝ → M → E3}
    (he : Work.Drive.N2C.IsLevelIsotopy f u e) {n : ℕ} (L : Work.Drive.N2C.LevelCurves f u n)
    (i : Fin n) (x : ℝ) :
    ContMDiffAt 𝓘(ℝ,ℝ) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => e 1 (L.γ i x)) x :=
  (he.1 1 (L.γ i x) (L.val i x)).comp₂ contMDiffAt_const ((L.sm i).contMDiffAt)

theorem contDiff_eval_level {f : M → ℝ} {u : ℝ} {e : ℝ → M → E3}
    (he : Work.Drive.N2C.IsLevelIsotopy f u e) {n : ℕ} (L : Work.Drive.N2C.LevelCurves f u n)
    (i : Fin n) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => e 1 (L.γ i x)) :=
  contMDiff_iff_contDiff.mp (fun x => contMDiffAt_eval_level he L i x)

/-! ## The immersion of the level curve -/

theorem deriv_eval_level_ne_zero {f : M → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {u : ℝ}
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {e : ℝ → M → E3} (he : Work.Drive.N2C.IsLevelIsotopy f u e) {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f u n) (i : Fin n) (x : ℝ) :
    deriv (fun y : ℝ => e 1 (L.γ i y)) x ≠ 0 := by
  intro h0
  have hmde : MDifferentiableAt (𝓡 2) (𝓡 3) (fun y : M => e 1 y) (L.γ i x) := by
    have hjointe : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × M => e p.1 p.2) (1, L.γ i x) := he.1 1 (L.γ i x) (L.val i x)
    exact (hjointe.comp₂ contMDiffAt_const contMDiffAt_id).mdifferentiableAt (by simp)
  have hmdγ : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x :=
    (L.sm i).contMDiffAt.mdifferentiableAt (by simp)
  -- the chain rule, for every parameter
  have hcomp_u : ∀ u : TangentSpace 𝓘(ℝ,ℝ) x,
      mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun y : ℝ => e 1 (L.γ i y)) x u
        = mfderiv (𝓡 2) (𝓡 3) (fun y : M => e 1 y) (L.γ i x)
            (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) x u) := by
    intro u
    have hc := mfderiv_comp (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓡 3)
      (f := L.γ i) (g := fun y : M => e 1 y) x hmde hmdγ
    have h2 := congrArg (fun (A : _ →L[ℝ] _) => A u) hc
    rw [ContinuousLinearMap.comp_apply] at h2
    rw [show ((fun y : M => e 1 y) ∘ (L.γ i)) = (fun y : ℝ => e 1 (L.γ i y)) from rfl] at h2
    exact h2
  have h1zero : mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun y : ℝ => e 1 (L.γ i y)) x 1 = 0 := by
    rw [mfderiv_eq_fderiv]
    exact h0
  have hlin : ∀ s : ℝ, mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun y : ℝ => e 1 (L.γ i y)) x s
      = s • mfderiv 𝓘(ℝ,ℝ) (𝓡 3) (fun y : ℝ => e 1 (L.γ i y)) x 1 := by
    intro s
    have hs1 : s • (1 : TangentSpace 𝓘(ℝ,ℝ) x) = s := by
      show s * 1 = s
      ring
    conv_lhs => rw [← hs1, ContinuousLinearMap.map_smul]
  obtain ⟨v, hvne, hfv⟩ :=
    Work.Drive.N2.exists_ne_zero_ker (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ i x))
  obtain ⟨s, hs⟩ := L.ker i x v hfv
  have hv : mfderiv (𝓡 2) (𝓡 3) (fun y : M => e 1 y) (L.γ i x) v ≠ 0 :=
    fun hz => hvne (he.2.2 1 (L.γ i x) (L.val i x) v hfv hz)
  exact hv (by rw [← hs, ← hcomp_u s, hlin s, h1zero, smul_zero])

/-! ## Two one-dimensional chain rules for `deriv` -/

theorem deriv_clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (g : ℝ → F) (x : ℝ) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => L (g y)) x = L (deriv g x) := by
  have h : HasDerivAt (fun y => L (g y)) (L (deriv g x)) x :=
    (ContinuousLinearMap.hasFDerivAt L).comp_hasDerivAt x hg.hasDerivAt
  exact h.deriv

theorem deriv_const_smul {g : ℝ → ℂ} (c : ℝ) (x : ℝ) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => c • g y) x = c • deriv g x := by
  simpa using (hg.hasDerivAt.const_smul c).deriv

theorem normSq_exp_ofReal_mul_I (t : ℝ) :
    Complex.normSq (Complex.exp ((t : ℂ) * Complex.I)) = 1 := by
  have h1 : ((t : ℂ) * Complex.I).re = 0 := by simp
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, h1, Real.exp_zero, one_pow]

theorem exists_reparam_level {f : M → ℝ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {u : ℝ}
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {e : ℝ → M → E3} (he : Work.Drive.N2C.IsLevelIsotopy f u e) {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f u n) (c : Fin n → E3) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i)
    (hround : ∀ (i : Fin n) (x : ℝ), ∃ t : ℝ,
      e 1 (L.γ i x) = c i + r i • Work.Drive.N2.roundPic t)
    (i : Fin n) :
    ∃ (τ : ℝ → ℝ) (φ : ℝ) (ε : ℤ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ x, τ (x + 1) = τ x + (ε : ℝ)) ∧ Function.Surjective τ ∧
      (StrictMono τ ∨ StrictAnti τ) ∧ (∀ x, deriv τ x ≠ 0) ∧
      (∀ x, e 1 (L.γ i (τ x)) = c i + r i • Work.Drive.N2.roundPic (φ + 2 * Real.pi * x)) := by
  have hraw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => e 1 (L.γ i y)) :=
    contDiff_eval_level he L i
  set G : ℝ → E3 := fun y => e 1 (L.γ i y) - c i with hGdef
  have hGcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    rw [hGdef]
    exact hraw.sub contDiff_const
  set z : ℝ → ℂ := fun y => (r i)⁻¹ • toC3 (G y) with hzdef
  have hzcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z := by
    rw [hzdef]
    exact (toC3.contDiff.comp hGcd).const_smul ((r i)⁻¹)
  have hroundG : ∀ y, ∃ t : ℝ, G y = r i • Work.Drive.N2.roundPic t := by
    intro y
    obtain ⟨t, ht⟩ := hround i y
    exact ⟨t, by rw [hGdef]; simp only; rw [ht, add_sub_cancel_left]⟩
  have hG3 : ∀ y, psi3 (G y) = 0 := by
    intro y
    obtain ⟨t, ht⟩ := hroundG y
    rw [ht, map_smul, psi3_roundPic, smul_zero]
  have hunit : ∀ y, Complex.normSq (z y) = 1 := by
    intro y
    obtain ⟨t, ht⟩ := hroundG y
    have hz : z y = Complex.exp ((t : ℂ) * Complex.I) := by
      rw [hzdef]
      rw [show (fun y => (r i)⁻¹ • toC3 (G y)) y = (r i)⁻¹ • toC3 (G y) from rfl]
      rw [ht, map_smul, toC3_roundPic, smul_smul, inv_mul_cancel₀ (ne_of_gt (hr i)), one_smul]
    rw [hz]
    exact normSq_exp_ofReal_mul_I t
  have hzper : ∀ y, z (y + 1) = z y := by
    intro y
    rw [hzdef]
    simp only
    rw [show G (y + 1) = G y from by rw [hGdef]; simp only; rw [L.per i y]]
  have hzinj : Set.InjOn z (Set.Ico 0 1) := by
    intro x hx y hy hxy
    have htoC : toC3 (G x) = toC3 (G y) := by
      have h := hxy
      rw [hzdef] at h
      have h' : (r i)⁻¹ • toC3 (G x) = (r i)⁻¹ • toC3 (G y) := h
      exact (smul_right_inj (inv_ne_zero (ne_of_gt (hr i)))).mp h'
    have hGxy : G x = G y := eq_of_toC3_eq_of_psi3_eq htoC (by rw [hG3 x, hG3 y])
    have heq : e 1 (L.γ i x) = e 1 (L.γ i y) := by
      have h := hGxy
      rw [hGdef] at h
      simp only at h
      have h2 := congrArg (fun w : E3 => w + c i) h
      simpa using h2
    have hxy' : L.γ i x = L.γ i y :=
      he.2.1 1 (L.γ i x) (L.γ i y) (L.val i x) (L.val i y) heq
    obtain ⟨k, hk⟩ := L.modOne i x y hxy'
    exact eq_of_sub_intCast_of_mem_Ico hx hy (by linarith)
  have hzder : ∀ y, deriv z y ≠ 0 := by
    intro y hzero
    have hGder : deriv G y ≠ 0 := by
      rw [hGdef, deriv_sub_const]
      exact deriv_eval_level_ne_zero hf hreg he L i y
    have hGdiff : DifferentiableAt ℝ G y := (hGcd.contDiffAt (x := y)).differentiableAt (by simp)
    have htoCdiff : DifferentiableAt ℝ (fun y => toC3 (G y)) y :=
      ((toC3.contDiff.comp hGcd).contDiffAt (x := y)).differentiableAt (by simp)
    have hdz : deriv z y = (r i)⁻¹ • toC3 (deriv G y) := by
      rw [hzdef]
      rw [deriv_const_smul (r i)⁻¹ y htoCdiff, deriv_clm_comp toC3 G y hGdiff]
    have htoC : toC3 (deriv G y) = 0 := by
      rw [hdz] at hzero
      rcases smul_eq_zero.mp hzero with h | h
      · exact absurd h (inv_ne_zero (ne_of_gt (hr i)))
      · exact h
    have hpsi : psi3 (deriv G y) = 0 := by
      have hconst : (psi3 ∘ G) = fun _ : ℝ => (0 : ℝ) := funext hG3
      have hd : deriv (psi3 ∘ G) y = 0 := by rw [hconst]; simp
      have hcm : deriv (psi3 ∘ G) y = psi3 (deriv G y) := by
        rw [show (psi3 ∘ G) = fun y => psi3 (G y) from rfl]
        exact deriv_clm_comp psi3 G y hGdiff
      rw [← hcm]
      exact hd
    exact hGder (eq_zero_of_toC3_eq_zero_of_psi3_eq_zero htoC hpsi)
  obtain ⟨τ, φ, ε, hτ, hε, hsh, hsurj, hmono, hderτ, hz⟩ :=
    Work.Drive.N2C.exists_reparam_unitCircle z hzcd hunit hzper hzinj hzder
  refine ⟨τ, φ, ε, hτ, hε, hsh, hsurj, hmono, hderτ, ?_⟩
  intro x
  have h1 : toC3 (G (τ x)) = r i • Complex.exp (((φ + 2 * Real.pi * x) : ℂ) * Complex.I) := by
    have h := hz x
    rw [hzdef] at h
    have h' : (r i)⁻¹ • toC3 (G (τ x)) =
        Complex.exp (((φ + 2 * Real.pi * x) : ℂ) * Complex.I) := h
    have h2 := congrArg (fun w : ℂ => (r i) • w) h'
    have hW : (r i) • ((r i)⁻¹ • toC3 (G (τ x))) = toC3 (G (τ x)) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hr i)), one_smul]
    rw [hW] at h2
    exact h2
  have hGv : G (τ x) = r i • Work.Drive.N2.roundPic (φ + 2 * Real.pi * x) := by
    refine eq_smul_roundPic_of_toC3 (v := G (τ x)) (r := r i)
      (φ := φ + 2 * Real.pi * x) (hG3 (τ x)) ?_
    convert h1 using 2
    push_cast
    ring
  have h2 : e 1 (L.γ i (τ x)) = c i + r i • Work.Drive.N2.roundPic (φ + 2 * Real.pi * x) := by
    have h := hGv
    rw [hGdef] at h
    have h' : e 1 (L.γ i (τ x)) - c i = r i • Work.Drive.N2.roundPic (φ + 2 * Real.pi * x) := h
    have h3 := congrArg (fun w : E3 => w + c i) h'
    simpa [add_comm] using h3
  exact h2

/-! ## The target -/

theorem isCertifiedAt_of_roundImage {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {u : ℝ}
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {g : M → EuclideanSpace ℝ (Fin 3)} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : Work.Drive.N2C.IsLevelIsotopy f u e) (h0 : ∀ y : M, f y = u → e 0 y = g y)
    {n : ℕ} (L : Work.Drive.N2C.LevelCurves f u n)
    (c : Fin n → EuclideanSpace ℝ (Fin 3)) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hround : ∀ (i : Fin n) (x : ℝ), ∃ t : ℝ,
      e 1 (L.γ i x) = c i + r i • Work.Drive.N2.roundPic t)
    (hsep : ∀ i j, i ≠ j → ∀ t t' : ℝ,
      c i + r i • Work.Drive.N2.roundPic t ≠ c j + r j • Work.Drive.N2.roundPic t') :
    Work.Drive.N2C.IsCertifiedAt f u g := by
  classical
  have key : ∀ i : Fin n, ∃ (τ : ℝ → ℝ) (φ : ℝ) (ε : ℤ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ x, τ (x + 1) = τ x + (ε : ℝ)) ∧ Function.Surjective τ ∧
      (StrictMono τ ∨ StrictAnti τ) ∧ (∀ x, deriv τ x ≠ 0) ∧
      (∀ x, e 1 (L.γ i (τ x)) = c i + r i • Work.Drive.N2.roundPic (φ + 2 * Real.pi * x)) :=
    fun i => exists_reparam_level hf hreg he L c r hr hround i
  choose τ φ ε hP using key
  have hτ : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (τ i) := fun i => (hP i).1
  have hε : ∀ i, (ε i = 1 ∨ ε i = -1) := fun i => (hP i).2.1
  have hsh : ∀ i x, τ i (x + 1) = τ i x + ((ε i : ℤ) : ℝ) := fun i => (hP i).2.2.1
  have hsurj : ∀ i, Function.Surjective (τ i) := fun i => (hP i).2.2.2.1
  have hmono : ∀ i, StrictMono (τ i) ∨ StrictAnti (τ i) := fun i => (hP i).2.2.2.2.1
  have hderτ : ∀ i x, deriv (τ i) x ≠ 0 := fun i => (hP i).2.2.2.2.2.1
  have hround' : ∀ i x, e 1 (L.γ i (τ i x))
      = c i + r i • Work.Drive.N2.roundPic (φ i + 2 * Real.pi * x) :=
    fun i => (hP i).2.2.2.2.2.2
  have hτinj : ∀ i, Function.Injective (τ i) :=
    fun i => (hmono i).elim (fun h => h.injective) (fun h => h.injective)
  refine ⟨n, ?_, ?_, e, ?_, he, h0, ?_⟩
  · refine ⟨fun i x => L.γ i (τ i x), ?_, fun i x => L.val i (τ i x), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (L.sm i).comp (contMDiff_iff_contDiff.mpr (hτ i))
    · intro i x
      rw [hsh i x]
      exact Work.Drive.N2C.eq_of_add_intCast_of_periodic (L.per i) (τ i x) (ε i)
    · intro i x hx y hy hxy
      obtain ⟨k, hk⟩ := L.modOne i (τ i x) (τ i y) hxy
      have hkey : ∃ k : ℤ, τ i x - τ i y = (k : ℝ) := ⟨k, by linarith [hk]⟩
      obtain ⟨m, hm⟩ := tau_inj_mod (hε i) (hsh i) (hτinj i) hkey
      exact eq_of_sub_intCast_of_mem_Ico hx hy hm
    · intro i x y hxy
      obtain ⟨k, hk⟩ := L.modOne i (τ i x) (τ i y) hxy
      have hkey : ∃ k : ℤ, τ i x - τ i y = (k : ℝ) := ⟨k, by linarith [hk]⟩
      obtain ⟨m, hm⟩ := tau_inj_mod (hε i) (hsh i) (hτinj i) hkey
      exact ⟨m, by linarith [hm]⟩
    · intro y hy
      obtain ⟨i, t, ht⟩ := L.cover y hy
      obtain ⟨s, hs⟩ := hsurj i t
      exact ⟨i, s, by rw [hs]; exact ht⟩
    · intro i j hij
      refine (L.disj i j hij).mono ?_ ?_
      · rintro _ ⟨x, rfl⟩
        exact Set.mem_range_self (τ i x)
      · rintro _ ⟨x, rfl⟩
        exact Set.mem_range_self (τ j x)
    · intro i x v hv
      obtain ⟨s, hs⟩ := L.ker i (τ i x) v hv
      have hmdγ : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) (τ i x) :=
        (L.sm i).contMDiffAt.mdifferentiableAt (by simp)
      have hmdτ : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (τ i) x :=
        ((contMDiff_iff_contDiff.mpr (hτ i)).contMDiffAt).mdifferentiableAt (by simp)
      have hτmf : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (τ i) x (s / deriv (τ i) x) = s := by
        have hs1 : (s / deriv (τ i) x) • (1 : TangentSpace 𝓘(ℝ,ℝ) x) = s / deriv (τ i) x := by
          show (s / deriv (τ i) x) * 1 = s / deriv (τ i) x
          ring
        have hval : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (τ i) x 1 = deriv (τ i) x := by
          rw [mfderiv_eq_fderiv]
          rfl
        conv_lhs => rw [← hs1, ContinuousLinearMap.map_smul]
        rw [hval]
        show (s / deriv (τ i) x) * deriv (τ i) x = s
        rw [div_mul_cancel₀ _ (hderτ i x)]
      have h2 : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun y : ℝ => L.γ i (τ i y)) x (s / deriv (τ i) x)
          = mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) (τ i x)
              (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (τ i) x (s / deriv (τ i) x)) := by
        have h := mfderiv_comp_apply x hmdγ hmdτ (s / deriv (τ i) x)
        rw [show ((L.γ i) ∘ (τ i)) = (fun y : ℝ => L.γ i (τ i y)) from rfl] at h
        exact h
      refine ⟨s / deriv (τ i) x, ?_⟩
      rw [h2, hτmf]
      exact hs
  · exact ⟨c, r, hr, φ⟩
  · intro i j hij s t
    exact hsep i j hij (φ i + 2 * Real.pi * s) (φ j + 2 * Real.pi * t)
  · intro i x
    show e 1 (L.γ i (τ i x)) = c i + r i • Work.Drive.N2.roundPic (φ i + 2 * Real.pi * x)
    exact hround' i x

end

end Work.N2C
