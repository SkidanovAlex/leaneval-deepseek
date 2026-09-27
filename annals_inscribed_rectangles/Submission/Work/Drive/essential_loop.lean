import Mathlib
import Submission.Work.Configuration
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.DirCTools
import Submission.Work.Drive.muOrd_injective_unordered
import Submission.Work.Drive.exists_embedded_configuration_strip
import Submission.Work.Drive.core_loop

/-!
# The essential loop of the configuration Möbius strip, parametrised once

The capped plane `P_u = u·M ∪ cap_u` of the chain route is a copy of `ℝP²`
(`Submission/Work/Drive/cappedPlaneFamily.lean`), and Hugelmeyer's order `≺` is defined by evaluating
the dual class `ω` of another plane on **an essential loop** of `P_u`, i.e. a curve whose class
generates `H₁(P_u; ℤ/2) = ℤ/2` (equivalently, a curve with `⟨γ, γ⟩ = 1` in the mod-2 intersection form
of `ℝP²`).  In the Möbius band `M` that generator is the **core** of the band.

## Why the "diameters" must be parametrised by the square-root lift

The chords of `μ` that degenerate onto the core are the *diameters*
`{γ x, γ (-x)} = {γ x, γ (x * w)}` with `w = -1`.  The map

> `x ↦ muOrd γ (x, x * (-1))`

used by `Work.Drive.core_loop` (and by `Work.Drive.chord_loop_winding`, whose monodromy `±2` is the
degree of the **doubled** direction, hence `±2` and not `±1`) is, however, **two-to-one** onto the
core: it does not parametrise the core once.  Since the core generates `H₁(M; ℤ) = ℤ` and the boundary
of the band is twice the core (`[∂M] = 2[C]`, which is the `2 = deg(doubled direction on ∂M)` of the
Umlauf), a loop traversing the core twice represents `2[C] = 0` in `H₁(M; ℤ/2)` — so it is *not*
essential, and using it as `γ_P` would make every count `⟨ω, [γ_P]⟩` vanish.

The core of `M` as a set is the image of the diameters, and the set of diameters is parametrised once
by the circle of *directions*: the map

> `Work.Drive.coreLoopPt γ θ = muOrd γ (Circle.exp (π θ), - Circle.exp (π θ))`

has period `1` in `θ` (`θ ↦ θ + 1` negates `Circle.exp (π θ)`, giving the same unordered pair) and is
injective modulo that period.  This is the essential loop of the capped plane: `θ ↦` the diameter at
direction `π θ`; its doubled direction has degree `±1`, half the `±2` of the twice-traversed
diametral loop.  Substituting `x = Circle.exp (π θ)` shows that `coreLoopPt` is
`Work.Drive.core_loop`'s loop with the base point running over the circle *twice* as `θ` runs over
`[0,2)` — exactly the two-to-one-ness above.
-/

namespace Work.Drive

noncomputable section

/-! ## Elementary facts about `Circle.exp` -/

/-- `Circle.exp π = -1`: the point of the circle at angle `π`. -/
lemma circle_exp_pi : Circle.exp Real.pi = -1 := by
  apply Subtype.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

/-- **The exponential kernel.**  `Circle.exp a = Circle.exp b` iff `a - b` is an integral multiple of
`2π`. -/
lemma circle_exp_eq_iff_exists_int {a b : ℝ} :
    Circle.exp a = Circle.exp b ↔ ∃ n : ℤ, a - b = 2 * Real.pi * n := by
  constructor
  · intro h
    have h' : Complex.exp (↑a * Complex.I) = Complex.exp (↑b * Complex.I) := by
      simpa [Circle.coe_exp] using congrArg (fun z : Circle => (z : ℂ)) h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h'
    refine ⟨n, ?_⟩
    have h1 : (↑a : ℂ) * Complex.I - ↑b * Complex.I = ↑n * (2 * ↑Real.pi * Complex.I) := by
      rw [hn]; ring
    have h2 : ((a - b : ℝ) : ℂ) * Complex.I = ((2 * Real.pi * n : ℝ) : ℂ) * Complex.I := by
      push_cast
      linear_combination (norm := ring_nf) h1
    have h3 := mul_right_cancel₀ Complex.I_ne_zero h2
    exact_mod_cast h3
  · rintro ⟨n, hn⟩
    have h2 : Circle.exp (2 * Real.pi * (n : ℝ)) = 1 := by
      rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring, Circle.exp_intCast_mul]
      have h3 : Circle.exp (2 * Real.pi) = 1 := by
        apply Subtype.ext
        simp
      rw [h3]
      simp
    have : a = b + 2 * Real.pi * (n : ℝ) := by linarith
    rw [this, add_comm, Circle.exp_add, h2, one_mul]

/-- The point of the circle at half the angle `2πθ`: a continuous choice of the square root of
`Circle.exp (2 * π * θ)`. -/
def corePt (θ : ℝ) : Circle := Circle.exp (Real.pi * θ)

lemma corePt_add_one (θ : ℝ) : corePt (θ + 1) = -corePt θ := by
  rw [corePt, show Real.pi * (θ + 1) = Real.pi * θ + Real.pi by ring, Circle.exp_add, corePt,
    circle_exp_pi, mul_neg, mul_one]

/-- `corePt θ` is never the antipode of itself: the circle has no element of order `2` equal to it. -/
lemma corePt_ne_neg (θ : ℝ) : corePt θ ≠ -corePt θ := by
  intro h
  have h' : (corePt θ : ℂ) = -(corePt θ : ℂ) := by
    simpa using congrArg (fun z : Circle => (z : ℂ)) h
  have h2 : (2 : ℂ) * (corePt θ : ℂ) = 0 := by linear_combination h'
  have h3 : (corePt θ : ℂ) = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · norm_num at h4
    · exact h4
  exact (corePt θ).coe_ne_zero h3

/-- **`corePt` is injective modulo the period `2`.** -/
lemma corePt_eq_iff {θ θ' : ℝ} : corePt θ = corePt θ' ↔ ∃ n : ℤ, θ = θ' + 2 * n := by
  rw [corePt, corePt, circle_exp_eq_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have : Real.pi * θ = Real.pi * θ' + 2 * Real.pi * (n : ℝ) := by linarith [hn]
    have h2 : Real.pi * (θ - θ' - 2 * (n : ℝ)) = 0 := by ring_nf; linarith [this]
    have h3 : θ - θ' - 2 * (n : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hπ
      · exact h
    linarith [h3]
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

/-! ## The essential loop -/

/-- **The essential loop of the configuration Möbius strip**: the core of the band, parametrised once
by the circle of directions.  `θ` is the direction of the diameter joining `γ z` to `γ (-z)`, where
`z = Circle.exp (π θ)`; the parametrisation has period `1`. -/
def coreLoopPt (γ : Circle → ℝ × ℝ) (θ : ℝ) : (ℝ × ℝ) × UnitAddCircle × ℝ :=
  Submission.Configuration.muOrd γ (corePt θ, -corePt θ)

/-- **The configuration map is symmetric**: the unordered pair `{x, y}` gives the same configuration
as `{y, x}` (a gap in the workspace: `Work.Drive.muOrd_swap` is quoted by earlier notes but was never
declared). -/
lemma muOrd_comm (γ : Circle → ℝ × ℝ) (x y : Circle) :
    Submission.Configuration.muOrd γ (y, x) = Submission.Configuration.muOrd γ (x, y) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Submission.Configuration.muOrd]
    rw [add_comm]
  · simp only [Submission.Configuration.muOrd]
    rw [show γ y - γ x = -(γ x - γ y) by abel, Work.Drive.dirC_neg]
  · simp only [Submission.Configuration.muOrd]
    rw [show γ y - γ x = -(γ x - γ y) by abel, Work.Drive.eucNorm_neg_ext]

/-- The essential loop is `1`-periodic: it descends to the circle `ℝ/ℤ` of directions. -/
lemma coreLoopPt_periodic (γ : Circle → ℝ × ℝ) (θ : ℝ) :
    coreLoopPt γ (θ + 1) = coreLoopPt γ θ := by
  simp only [coreLoopPt, corePt_add_one, neg_neg]
  exact muOrd_comm γ _ _

/-- **The essential loop is injective**: distinct directions in `[0, 1)` give distinct configurations
(the two parametrisations of a diameter differ by `θ = θ' + 1`). -/
lemma coreLoopPt_injective {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {θ θ' : ℝ} (h1 : θ ∈ Set.Ico (0 : ℝ) 1) (h2 : θ' ∈ Set.Ico (0 : ℝ) 1)
    (h : coreLoopPt γ θ = coreLoopPt γ θ') : θ = θ' := by
  have hmem : (0 : ℝ) ≤ θ := h1.1
  have hmem2 : (0 : ℝ) ≤ θ' := h2.1
  have hlt : θ < 1 := h1.2
  have hlt2 : θ' < 1 := h2.2
  rcases Work.Drive.muOrd_injective_unordered hγ h with ⟨hA, _⟩ | ⟨hA, _⟩
  · rw [corePt_eq_iff] at hA
    obtain ⟨n, hn⟩ := hA
    have hb : |(n : ℝ)| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hn1 : n < 1 := by exact_mod_cast (abs_lt.mp hb).2
    have hn2 : -1 < n := by exact_mod_cast (abs_lt.mp hb).1
    have : n = 0 := by omega
    rw [this] at hn
    norm_num at hn
    exact hn
  · exfalso
    have hexp : Circle.exp (Real.pi * θ) = Circle.exp (Real.pi * θ' + Real.pi) := by
      rw [Circle.exp_add, circle_exp_pi, mul_neg, mul_one]
      simpa only [corePt] using hA
    obtain ⟨n, hn⟩ := circle_exp_eq_iff_exists_int.mp hexp
    have hn' : Real.pi * θ = Real.pi * θ' + Real.pi + 2 * Real.pi * (n : ℝ) := by linarith [hn]
    have hkey : Real.pi * (θ - θ' - 1) = Real.pi * (2 * (n : ℝ)) := by
      ring_nf
      linarith [hn']
    have h3 : θ - θ' - 1 = 2 * (n : ℝ) := mul_left_cancel₀ Real.pi_ne_zero hkey
    have hb : (-2 : ℝ) < 2 * (n : ℝ) ∧ 2 * (n : ℝ) < 0 := by
      constructor <;> linarith
    have hn1 : 2 * n < 0 := by exact_mod_cast hb.2
    have hn2 : -2 < 2 * n := by exact_mod_cast hb.1
    omega

/-- `corePt` is surjective: it is `Circle.exp` along the reparametrisation `t ↦ t / π`. -/
lemma corePt_surjective : Function.Surjective corePt := by
  intro z
  obtain ⟨t, ht⟩ := Circle.exp_surjective z
  exact ⟨t / Real.pi, by rw [corePt, show Real.pi * (t / Real.pi) = t by field_simp, ht]⟩

/-- **`coreLoopPt` and the diametral loop of `core_loop` have the same image** (`coreLoopPt` is the
diametral loop, which is two-to-one onto the core, with the base point run over the circle twice):
the difference is the parametrisation, hence the class — `2[C]` for the diametral loop, `[C]` for
`coreLoopPt`, and `[C]` is the generator of `H₁(P_u; ℤ/2)`. -/
lemma range_coreLoopPt (γ : Circle → ℝ × ℝ) :
    Set.range (coreLoopPt γ) =
      Set.range (fun x : Circle => Submission.Configuration.muOrd γ (x, -x)) := by
  ext q
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨corePt θ, rfl⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨θ, rfl⟩ := corePt_surjective x
    exact ⟨θ, rfl⟩

/-- **The essential loop lies in the interior of the strip**: the diameter is a genuine chord, so its
length coordinate is non-zero (this is what makes it a loop of the capped plane rather than of its
boundary). -/
lemma coreLoopPt_length_ne_zero {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (θ : ℝ) :
    (coreLoopPt γ θ).2.2 ≠ 0 := by
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  have hne : γ (corePt θ) - γ (-corePt θ) ≠ 0 := by
    intro h0
    exact corePt_ne_neg θ (hinj (sub_eq_zero.mp h0))
  have hpos := Submission.Geometry.eucNorm_pos hne
  simpa [coreLoopPt, Submission.Configuration.muOrd] using ne_of_gt hpos

end

end Work.Drive
