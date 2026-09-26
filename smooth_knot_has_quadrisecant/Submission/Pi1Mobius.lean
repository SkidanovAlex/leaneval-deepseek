import ChallengeDeps
import Submission.Helpers
import Submission.KnotMap
import Submission.ChordMap
import Submission.SecantSpace

open LeanEval.KnotTheory.Quadrisecant

/-!
# Layer C — the fundamental group of the open Möbius band

**Target theorem of this layer** (the engine of Kuperberg's winding-counting
argument): for the open Möbius band `M := OpenMobius` (secants of the knot
with distinct endpoints, `Submission/SecantSpace.lean`),

    π₁(M) ≅ ℤ   (as groups),

together with the geometric consequences used in Layer C: an embedded circle
in `M` that meets every non-separating proper arc is essential, and essential
embedded circles wind either *once* (orientation reversing — the core circle)
or *twice* (orientation preserving); a once-winding circle does not separate
its complement, a twice-winding circle separates off an annulus.  Following
the middle point of the trisecants along such a circle yields the two
contradictions of Kuperberg's proof (a jump discontinuity, or every point of
the knot lying between two others).

**Route (decomposition).**  Mathlib currently provides the fundamental group
(`AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`),
`SimplyConnectedSpace`, homotopy equivalences and homotopy groups (`π_ 1`),
but *not* `π₁(S¹) = ℤ` and not the covering↔π₁ bridge.  The layer therefore
splits as:

  1. **The core circle of `M`** (this file, started): the antipodal pairs
     `{x, x + h}` (`h := period/2`) form the core circle of the open Möbius
     band: `core : AddCircle period → OpenMobius`, continuous, invariant
     under `x ↦ x + h` (so it factors through a genuine circle), and
     injective up to that involution.  Proved here: the half-period facts
     (`halfPeriod_pos`, `add_halfPeriod_ne_self` — the pairs are genuinely
     of *distinct* parameters), `corePair` (continuous, swaps under the
     half-turn), and `core` (continuous, half-period invariant).
  2. **Deformation retraction of `M` onto the core** (target formulated
     below as `OpenMobiusCoreRetract`): construct
     `ρ : OpenMobius × I → OpenMobius` with `ρ (m, 0) = m`,
     `ρ (m, 1) ∈ range coreFactor` and `ρ (coreFactor x, t) = coreFactor x`;
     this yields a homotopy equivalence `M ≃ₕ (range coreFactor)`.
     Decomposition: (2a) an explicit retraction-normalisation on the real
     lifts of pairs (slide the second lift toward `first + halfPeriod`,
     equivariant under the swap), (2b) its well-definedness on `OpenMobius`
     and continuity via the quotient (reusing the `OpenMobius` topology
     machinery), (2c) the homotopy-extension to all `t` fixing the core, (2d)
     the homotopy-equivalence certificate.
  3. **The core is a circle**: DONE — `coreFactor_homeo : (range coreFactor)
     ≃ₜ AddCircle halfPeriod`, and `range coreFactor = range core`.
  4. **π₁(S¹) = ℤ** (the main Mathlib gap): prove via the covering
     `ℝ → S¹` (`IsCoveringMap` is available for the exponential), the
     simple-connectivity of `ℝ`, path-lifting in `Topology/Covering`, and a
     winding-degree/decoupling argument — this is a sub-project of its own
     and must be built (or published to Mathlib) before `π₁(M) = ℤ` can be
     assembled.
  5. **Assembly**: homotopy equivalence preserves the fundamental group on
     path-connected spaces, giving `π₁(M) ≅ π₁(S¹) ≅ ℤ`; then the
     embedded-circle classification and the winding-counting argument of
     Layer C.

All code in this file is verified (no axioms, no `sorry`); unproved target
statements are described in doc comments only.
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The half period `h = π`. -/
def halfPeriod : ℝ := period / 2

lemma halfPeriod_pos : 0 < halfPeriod := by
  unfold halfPeriod
  exact div_pos period_pos (by norm_num)

/-- The half period is not a period: `(h : AddCircle period) ≠ 0`. -/
lemma halfPeriod_ne_zero_circle : ((halfPeriod : ℝ) : AddCircle period) ≠ 0 := by
  intro hz
  have hn : ∃ n : ℤ, n • period = halfPeriod := by
    have hn' := (AddCircle.coe_eq_zero_iff (p := period)).mp hz
    simpa [halfPeriod] using hn'
  rcases hn with ⟨n, hn⟩
  have hnq : (n : ℝ) = 1 / 2 := by
    have hn'' : (n : ℝ) * period = period / 2 := by
      simpa [halfPeriod] using hn
    have hp : period ≠ 0 := period_ne_zero
    field_simp [hp] at hn'' ⊢
    linarith
  have hc : (2 : ℝ) * (n : ℝ) = 1 := by
    rw [hnq]
    norm_num
  have hz2 : (2 * n : ℤ) = 1 := by
    exact_mod_cast hc
  omega

/-- Adding the half period never fixes a point of the parameter circle (there
is no 2-torsion from the half turn). -/
lemma add_halfPeriod_ne_self (x : AddCircle period) : x ≠ x + halfPeriod := by
  intro h
  have h0 : ((halfPeriod : ℝ) : AddCircle period) = 0 := by
    have := congrArg (fun y : AddCircle period => y - x) h
    simpa using this.symm
  exact halfPeriod_ne_zero_circle h0

/-- Twice the half period is a full period. -/
lemma two_mul_halfPeriod : 2 * halfPeriod = period := by
  unfold halfPeriod
  ring

/-- The ordered pair of a parameter and its antipode (half a period away). -/
noncomputable def corePair (x : AddCircle period) : OrderedPairs :=
  ⟨(x, x + halfPeriod), add_halfPeriod_ne_self x⟩

/-- `corePair` is continuous. -/
lemma continuous_corePair : Continuous corePair := by
  -- underlying map x ↦ (x, x + halfPeriod) is continuous and lands off-diagonal
  have hunder : Continuous (fun x : AddCircle period => (x, x + halfPeriod)) :=
    continuous_id.prodMk (continuous_id.add continuous_const)
  exact Continuous.subtype_mk (f := fun x : AddCircle period => (x, x + halfPeriod))
    (p := fun q : AddCircle period × AddCircle period => q.1 ≠ q.2) hunder
    (fun x => add_halfPeriod_ne_self x)

/-- Shifting by the half period swaps the two parameters of `corePair`. -/
lemma corePair_halfPeriod (x : AddCircle period) :
    corePair (x + halfPeriod) = swapOrdered (corePair x) := by
  apply Subtype.ext
  -- values: (x + h, x + 2h) = (x + h, x) = swapOrdered (x, x + h)
  change ((x + halfPeriod), (x + halfPeriod) + halfPeriod) =
    (x + halfPeriod, x)
  have hx2 : (x + halfPeriod) + halfPeriod = x := by
    -- (x + h) + h = x + (h + h) = x + period = x
    rw [add_assoc]
    have hh : (halfPeriod : AddCircle period) + halfPeriod = (period : AddCircle period) := by
      have hs : (halfPeriod + halfPeriod : ℝ) = period := by
        unfold halfPeriod
        ring
      rw [← hs]
      simp
    rw [hh]
    have hp0 : (period : AddCircle period) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨1, by simp⟩
    rw [hp0]
    simp
  simp [hx2]

/-- The core circle of the open Möbius band: the class of the antipodal pair
`{x, x + h}`.  It is continuous and invariant under `x ↦ x + h`, so it
factors through the circle of half-periods. -/
noncomputable def core (x : AddCircle period) : OpenMobius :=
  mobiusCover (corePair x)

/-- The two parameters of `corePair x` are swapped when `x` is shifted by the
half period, so the corresponding unordered pair — the core point — is
unchanged. -/
lemma core_halfPeriod (x : AddCircle period) : core (x + halfPeriod) = core x := by
  unfold core
  rw [corePair_halfPeriod]
  -- mobiusCover is invariant under swapping the ordered representatives
  exact mobiusCover_swap (corePair x)

/-- The core circle is a continuous family of secants. -/
lemma continuous_core : Continuous core := by
  unfold core
  exact continuous_mobiusCover.comp continuous_corePair

/-- The core is *the* circle of antipodal pairs: two core points coincide
iff their parameters differ by the half period (i.e. they represent the same
antipodal pair).  So `core` factors through the half-period circle
`AddCircle halfPeriod` and is injective there. -/
lemma core_eq_iff (x y : AddCircle period) :
    core x = core y ↔ y = x ∨ y = x + halfPeriod := by
  unfold core
  have h1 : mobiusCover (corePair x) = mobiusCover (corePair y) ↔
      corePair x = corePair y ∨ swapOrdered (corePair x) = corePair y := by
    rw [show mobiusCover (corePair x) = mobiusCover (corePair y) ↔
        unordOfOrdered (corePair x) = unordOfOrdered (corePair y) by
          constructor
          · intro h
            exact congrArg Subtype.val h
          · intro h
            apply Subtype.ext
            exact h]
    exact unordOfOrdered_eq_iff (corePair x) (corePair y)
  rw [h1]
  constructor
  · intro h
    rcases h with h | h
    · left
      have hv := congrArg (fun p : OrderedPairs =>
        (p : AddCircle period × AddCircle period)) h
      have hy : x = y := by simpa [corePair] using congrArg Prod.fst hv
      exact hy.symm
    · right
      have hv := congrArg (fun p : OrderedPairs =>
        (p : AddCircle period × AddCircle period)) h
      have hy : x + halfPeriod = y := by
        simpa [corePair, swapOrdered] using congrArg Prod.fst hv
      exact hy.symm
  · intro h
    rcases h with h | h
    · rw [h]
      exact Or.inl rfl
    · rw [h]
      right
      exact (corePair_halfPeriod x).symm


/-- The integer-two multiple of the half period is the full period. -/
lemma two_zsmul_halfPeriod : (2 : ℤ) • halfPeriod = period := by
  rw [zsmul_eq_mul]
  unfold halfPeriod
  ring

/-- The full period vanishes in the period circle. -/
lemma period_zero_circle : (period : AddCircle period) = 0 := by
  exact (AddCircle.coe_eq_zero_iff (p := period)).mpr ⟨1, by simp⟩

/-- Full-period multiples lie inside half-period multiples
(`period = 2 • halfPeriod`). -/
lemma zmultiples_period_le_half :
    (AddSubgroup.zmultiples period : AddSubgroup ℝ) ≤ AddSubgroup.zmultiples halfPeriod := by
  intro x hx
  rw [AddSubgroup.mem_zmultiples_iff] at hx ⊢
  rcases hx with ⟨k, hk⟩
  refine ⟨2 * k, ?_⟩
  calc (2 * k : ℤ) • halfPeriod = (k * 2 : ℤ) • halfPeriod := by ring
    _ = k • ((2 : ℤ) • halfPeriod) := by
      exact (smul_smul k 2 halfPeriod).symm
    _ = k • period := by rw [two_zsmul_halfPeriod]
    _ = x := hk

/-- Twice the half-period element vanishes in the period circle. -/
lemma two_zsmul_half_circle : (2 : ℤ) • (halfPeriod : AddCircle period) = 0 := by
  have hsum : (halfPeriod : AddCircle period) + (halfPeriod : AddCircle period) =
      ((halfPeriod + halfPeriod : ℝ) : AddCircle period) := rfl
  rw [two_zsmul, hsum]
  have hs : halfPeriod + halfPeriod = period := by unfold halfPeriod; ring
  rw [hs]
  exact period_zero_circle

/-- Any multiple of the half-period element in the period circle is either
zero or the half period itself (the half period has order two). -/
lemma zsmul_half_circle_eq (k : ℤ) :
    k • (halfPeriod : AddCircle period) = (0 : AddCircle period) ∨
      k • (halfPeriod : AddCircle period) = (halfPeriod : AddCircle period) := by
  rcases Int.even_or_odd k with h | h
  · left
    rcases h with ⟨m, hm⟩
    have hm2 : k = 2 * m := by omega
    rw [hm2]
    calc (2 * m : ℤ) • (halfPeriod : AddCircle period)
        = m • ((2 : ℤ) • (halfPeriod : AddCircle period)) := by
          rw [mul_comm]
          exact (smul_smul m 2 (halfPeriod : AddCircle period)).symm
      _ = m • (0 : AddCircle period) := by rw [two_zsmul_half_circle]
      _ = 0 := by simp
  · right
    rcases h with ⟨m, hm⟩
    rw [hm]
    calc (2 * m + 1 : ℤ) • (halfPeriod : AddCircle period)
        = (2 * m : ℤ) • (halfPeriod : AddCircle period)
            + (1 : ℤ) • (halfPeriod : AddCircle period) := by rw [add_smul]
      _ = (halfPeriod : AddCircle period) := by
          rw [one_zsmul]
          have hzm : (2 * m : ℤ) • (halfPeriod : AddCircle period) = 0 := by
            calc (2 * m : ℤ) • (halfPeriod : AddCircle period)
                = m • ((2 : ℤ) • (halfPeriod : AddCircle period)) := by
                  rw [mul_comm]
                  exact (smul_smul m 2 (halfPeriod : AddCircle period)).symm
              _ = m • (0 : AddCircle period) := by rw [two_zsmul_half_circle]
              _ = 0 := by simp
          simp [hzm]

/-- The core is well defined on the half-period circle: parameters that agree
modulo the half period give the same core point. -/
lemma core_wd_half {a b : ℝ} (hab : (a : AddCircle halfPeriod) = (b : AddCircle halfPeriod)) :
    core (a : AddCircle period) = core (b : AddCircle period) := by
  have hm : ∃ k : ℤ, k • halfPeriod = b - a := by
    have hmem : -a + b ∈ AddSubgroup.zmultiples halfPeriod :=
      (QuotientAddGroup.eq (s := (AddSubgroup.zmultiples halfPeriod : AddSubgroup ℝ))
        (a := a) (b := b)).mp hab
    rw [AddSubgroup.mem_zmultiples_iff] at hmem
    rcases hmem with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc k • halfPeriod = -a + b := hk
      _ = b - a := by ring
  rcases hm with ⟨k, hk⟩
  have hb : (b : AddCircle period) = (a : AddCircle period) +
      k • (halfPeriod : AddCircle period) := by
    have hb' : a + k • halfPeriod = b := by
      rw [hk]
      ring
    rw [← hb']
    rfl
  rcases zsmul_half_circle_eq k with hk0 | hk1
  · apply (core_eq_iff (x := (a : AddCircle period)) (y := (b : AddCircle period))).mpr
    left
    simp [hb, hk0]
  · apply (core_eq_iff (x := (a : AddCircle period)) (y := (b : AddCircle period))).mpr
    right
    simp [hb, hk1]

/-- The quotient map from the full period circle to the half-period circle
(`x` ↦ `x mod halfPeriod`): every parameter is remembered modulo half a
period. -/
noncomputable def periodToHalfPeriod : AddCircle period → AddCircle halfPeriod :=
  Quotient.lift (fun t : ℝ => (t : AddCircle halfPeriod)) (by
    intro a b hab
    have hmem : -a + b ∈ AddSubgroup.zmultiples period := by
      -- the quotient relation of `ℝ ⧸ zmultiples period` is leftRel
      exact (QuotientAddGroup.leftRel_apply (s := (AddSubgroup.zmultiples period : AddSubgroup ℝ))
        (x := a) (y := b)).mp hab
    rw [QuotientAddGroup.eq]
    exact zmultiples_period_le_half hmem)

/-- `periodToHalfPeriod` maps a lifted real to its half-period class. -/
lemma periodToHalfPeriod_coe (t : ℝ) :
    periodToHalfPeriod (t : AddCircle period) = (t : AddCircle halfPeriod) := by
  rfl

/-- The core, viewed on the half-period circle: the factorisation of `core`
through `periodToHalfPeriod`. -/
noncomputable def coreFactor : AddCircle halfPeriod → OpenMobius :=
  Quotient.lift (fun t : ℝ => core (t : AddCircle period)) (by
    intro a b hab
    exact core_wd_half (Quotient.sound hab))

lemma core_factorizes : core = coreFactor ∘ periodToHalfPeriod := by
  ext u
  refine Quotient.inductionOn u ?_
  intro t
  -- both sides compute to core (t : AddCircle period)
  simp [coreFactor, periodToHalfPeriod]


/-- `periodToHalfPeriod` is surjective (every half-period class contains a
full-period representative). -/
lemma periodToHalfPeriod_surjective : Function.Surjective periodToHalfPeriod := by
  intro w
  refine Quotient.inductionOn w ?_
  intro t
  exact ⟨(t : AddCircle period), by simp [periodToHalfPeriod]⟩

/-- `halfPeriod` is positive, as a typeclass fact. -/
instance halfPeriod_pos_fact : Fact (0 < halfPeriod) :=
  ⟨halfPeriod_pos⟩

/-- Shifting a full-period parameter by the half period does not change its
half-period class (the half period vanishes in the half-period circle). -/
lemma periodToHalfPeriod_add_half (a : AddCircle period) :
    periodToHalfPeriod (a + halfPeriod) = periodToHalfPeriod a := by
  refine Quotient.inductionOn a ?_
  intro t
  change ((t + halfPeriod : ℝ) : AddCircle halfPeriod) = (t : AddCircle halfPeriod)
  rw [AddCircle.coe_add halfPeriod t halfPeriod]
  have hh : (halfPeriod : AddCircle halfPeriod) = 0 := by
    exact (AddCircle.coe_eq_zero_iff (p := halfPeriod)).mpr ⟨1, by simp⟩
  rw [hh]
  simp

/-- **`coreFactor` is injective**: the core circle of antipodal pairs, viewed
on the half-period circle, parametrizes each core point exactly once. -/
lemma coreFactor_injective : Function.Injective coreFactor := by
  intro u v huv
  rcases periodToHalfPeriod_surjective u with ⟨a, rfl⟩
  rcases periodToHalfPeriod_surjective v with ⟨b, rfl⟩
  -- coreFactor (ρ a) = core a (factorisation), so the hypothesis reads core a = core b
  have hc : core a = core b := by
    have h1 := congrFun core_factorizes a
    have h2 := congrFun core_factorizes b
    -- h1 : core a = coreFactor (ρ a); h2 : core b = coreFactor (ρ b)
    rw [h1, h2]
    exact huv
  rcases (core_eq_iff a b).mp hc with h | h
  · rw [← h]
  · rw [h]
    exact (periodToHalfPeriod_add_half a).symm


/-- **`coreFactor` is continuous**: it is the lift of the continuous map
`core` along the quotient `periodToHalfPeriod`. -/
lemma continuous_coreFactor : Continuous coreFactor := by
  have hf : Continuous (fun t : ℝ => core (t : AddCircle period)) := by
    exact continuous_core.comp (AddCircle.continuous_mk' (p := period))
  have hcont : Continuous (Quotient.lift (fun t : ℝ => core (t : AddCircle period))
      (by intro a b hab; exact core_wd_half (Quotient.sound hab))) := by
    exact Continuous.quotient_lift hf (by intro a b hab; exact core_wd_half (Quotient.sound hab))
  simpa [coreFactor] using hcont

/-- The image of `coreFactor` is exactly the image of `core` (the factor
covers the same core circle, since `periodToHalfPeriod` is surjective). -/
lemma coreFactor_range_eq_core_range :
    Set.range coreFactor = Set.range core := by
  -- core = coreFactor ∘ periodToHalfPeriod with periodToHalfPeriod surjective
  have hsurj : Function.Surjective periodToHalfPeriod := periodToHalfPeriod_surjective
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    rcases hsurj w with ⟨x, rfl⟩
    -- y = coreFactor (ρ x) = core x
    refine ⟨x, ?_⟩
    exact congrFun core_factorizes x
  · rintro ⟨x, rfl⟩
    -- y = core x = coreFactor (ρ x)
    refine ⟨periodToHalfPeriod x, ?_⟩
    exact (congrFun core_factorizes x).symm

/-- The core circle of antipodal pairs is homeomorphic to the half-period
circle: `coreFactor` is a continuous bijection onto its image with compact
domain and Hausdorff codomain. -/
noncomputable def coreFactor_homeo : AddCircle halfPeriod ≃ₜ Set.range coreFactor := by
  refine Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective coreFactor coreFactor_injective) ?_
  change Continuous (fun x : AddCircle halfPeriod =>
    (⟨coreFactor x, ⟨x, rfl⟩⟩ : Set.range coreFactor))
  exact Continuous.subtype_mk continuous_coreFactor _


/-- **Step (b) target — deformation retraction of the open Möbius band onto
its core circle.**  `ρ` slides every secant continuously onto an antipodal
pair (a point of the core `Set.range coreFactor`), fixing the core pointwise.
(`I := Set.Icc 0 1`; the statement is deliberately self-contained.) -/
def OpenMobiusCoreRetract : Prop :=
  ∃ ρ : OpenMobius × Set.Icc (0 : ℝ) 1 → OpenMobius,
    Continuous ρ ∧
    (∀ c : OpenMobius, ρ (c, ⟨(0 : ℝ), by norm_num⟩) = c) ∧
    (∀ c : OpenMobius, ρ (c, ⟨(1 : ℝ), by norm_num⟩) ∈ Set.range coreFactor) ∧
    (∀ (x : AddCircle halfPeriod) (t : Set.Icc (0 : ℝ) 1),
      ρ (coreFactor x, t) = coreFactor x)


/-- `halfPeriod` is nonzero (a half turn is not a period). -/
lemma halfPeriod_ne_zero : halfPeriod ≠ 0 := ne_of_gt halfPeriod_pos

/-! ### (2a) — the trigonometric circle models

The parameter circle of a knot is, through the complex exponential, the unit
circle `Circle = {z : ℂ | ‖z‖ = 1}`; Mathlib's
`AddCircle.homeomorphCircle` is the homeomorphism `AddCircle T ≃ₜ Circle`
sending `mk t ↦ exp(2πi·t/T)`.  We record the two instances of this needed
by the chord geometry: the *parameter* circle and the *core* circle
(`AddCircle halfPeriod` ≃ `Circle`, since a half-period direction is a
diameter direction = an unoriented line through the origin = a point of
`Circle` under `z ↦ z²`), and the resulting plane models of the core
embedded in the open Möbius band.  With these, the chord-slide deformation
retraction of (2a) becomes a statement about actual lines and angles in the
plane: a chord is `{z : ℂ | z · n = d}` for a unit normal `n` and
`d ∈ (−1,1)`, its chord-line data `(n, d)` up to `(n,d) ~ (−n,−d)`, and the
retraction `(n,d) ↦ (n, 0)` slides it onto the parallel diameter. -/

/-- The parameter circle of the knot is the unit circle. -/
noncomputable def paramCircleHomeo : AddCircle period ≃ₜ Circle :=
  AddCircle.homeomorphCircle (T := period) period_ne_zero

/-- The core circle of the open Möbius band is the unit circle: a half-period
class is a diameter direction. -/
noncomputable def coreCircleHomeo : AddCircle halfPeriod ≃ₜ Circle :=
  AddCircle.homeomorphCircle (T := halfPeriod) halfPeriod_ne_zero

/-- The core of the open Möbius band, embedded in `OpenMobius`, is the unit
circle (plane model of the core circle). -/
noncomputable def coreRangeCircle : Set.range coreFactor ≃ₜ Circle :=
  coreFactor_homeo.symm.trans coreCircleHomeo

/-- The image of the core parametrization `core` is the unit circle as well
(`range core = range coreFactor`). -/
noncomputable def coreRangeCircle' : Set.range core ≃ₜ Circle := by
  rw [← coreFactor_range_eq_core_range]
  exact coreRangeCircle


/-! ## S263 — π₁(S¹) ≅ ℤ for the parameter circle (VERIFIED, sorry-free) —
the winding route's first layer (Pi1Mobius route step 4, DONE)

The Pi1Mobius layer plan requires `π₁(M) ≅ ℤ` for the open Möbius band M of
secants; its missing engine was `π₁(S¹) = ℤ`.  Since the plan was written,
Mathlib gained the quotient-covering machinery of Junyan Xu
(`Topology/Covering/Quotient.lean`, `Topology/Covering/AddCircle.lean`,
`Topology/Homotopy/Lifting.lean`): for a quotient covering
`p : E → X` by a discrete group `G` with `E` simply connected,
`IsQuotientCoveringMap.fundamentalGroupEquiv` identifies
`π₁(X) ≃* G` (the monodromy/degree iso).  This section instantiates it for
the circle `AddCircle p = ℝ ⧸ zmultiples p` (`E = ℝ`, the deck group
`zmultiples p ≅ ℤ`):

* **`zmultiplesHom`** — the deck group as a hom `ℤ →+ zmultiples p`,
  `n ↦ ⟨n • p, ⋯⟩`;
* **`zmultiplesHom_injective` / `zmultiplesHom_surjective` /
  `zmultiplesEquivInt`** — for `p ≠ 0` the map `n ↦ n • p` is a bijection
  (`mul_right_cancel₀` for injectivity on ℝ), so the deck group is the
  infinite cyclic group: `zmultiples p ≃+ ℤ`;
* **`mulOppositeIntEquiv`** — the opposite of the (commutative)
  multiplicative ℤ is itself;
* **`fundamentalGroupAddCircle_isoZ`** — **`π₁(AddCircle p) ≃* ℤ`**: for
  `p ≠ 0`, `FundamentalGroup (AddCircle p) (0 : AddCircle p) ≃*
  Multiplicative ℤ`, assembled as
  `(AddCircle.isAddQuotientCoveringMap_coe p).fundamentalGroupEquiv
  ⟨0, rfl⟩` (`π₁ ≃* (Multiplicative (zmultiples p))ᵐᵒᵖ`, injective by
  `SimplyConnectedSpace ℝ` — lift uniqueness, surjective by
  `PathConnectedSpace ℝ` — the standard loops) followed by the deck-group
  identification through `AddEquiv.toMultiplicative` and
  `MulEquiv.op`/`mulOppositeIntEquiv`.

NOTES on the three ingredient lemmas of the winding route (provided by the
Mathlib machinery invoked here, to be made explicit in the next step):
degree of a loop = the endpoint difference of its lift to ℝ (the monodromy
integer — `Γ 1 − Γ 0 ∈ p·ℤ`, identified with ℤ by `zmultiplesEquivInt`);
homotopy-invariance = `IsCoveringMap.monodromy` is well-defined on
`Path.Homotopic.Quotient` (`liftPath_apply_one_eq_of_homotopicRel`);
surjectivity by standard loops = `fundamentalGroupToMulOpposite_surjective`
(`PathConnectedSpace ℝ`); injectivity by lift uniqueness =
`fundamentalGroupToMulOpposite_injective` (`SimplyConnectedSpace ℝ`).
STATUS: the `π₁(S¹) = ℤ` engine of the winding route is DONE for the
parameter circle `AddCircle p`; the next steps of the route are the
explicit winding-number API on loops (degree of a loop as an integer,
standard loops of every degree, the generator), the deformation
retraction of the Möbius band onto its core (`OpenMobiusCoreRetract`,
route step 2), and the assembly `π₁(M) ≅ ℤ` (route step 5).  Tree green;
TWO documented sorries; no children pending.
-/

open AddSubgroup
open scoped Real Topology unitInterval

/-- **The deck group of `ℝ → AddCircle p` as a hom from ℤ (VERIFIED)**:
`n ↦ ⟨n • p, ⋯⟩` sends an integer to the corresponding translation of the
real line in the subgroup `zmultiples p` (an additive homomorphism). -/
def zmultiplesHom (p : ℝ) : ℤ →+ zmultiples p where
  toFun := fun n => ⟨n • p, by
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨n, rfl⟩⟩
  map_zero' := by ext; simp
  map_add' := by
    intro a b
    ext
    simp [zsmul_eq_mul]
    ring

/-- **`zmultiplesHom` is injective for `p ≠ 0` (VERIFIED)**: in ℝ the map
`n ↦ n • p` has trivial kernel when the period is nonzero
(`mul_right_cancel₀` after `zsmul_eq_mul`, then the integer casts). -/
lemma zmultiplesHom_injective (p : ℝ) (hp : p ≠ 0) : Function.Injective (zmultiplesHom p) := by
  intro a b h
  have hval : a • p = b • p := by
    exact congrArg Subtype.val h
  have hval' : (a : ℝ) * p = (b : ℝ) * p := by
    simpa [zsmul_eq_mul] using hval
  have hc : (a : ℝ) = (b : ℝ) := mul_right_cancel₀ hp hval'
  exact_mod_cast hc

/-- **`zmultiplesHom` is surjective (VERIFIED)**: every element of
`zmultiples p` is `n • p` for the witness `n` of its membership. -/
lemma zmultiplesHom_surjective (p : ℝ) : Function.Surjective (zmultiplesHom p) := by
  intro x
  rcases (AddSubgroup.mem_zmultiples_iff.mp x.2) with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  exact hn

/-- **The deck group of the circle is the infinite cyclic group (VERIFIED)**:
for `p ≠ 0`, `zmultiples p ≃+ ℤ` — the translations of the real line by
integer multiples of the period. -/
noncomputable def zmultiplesEquivInt (p : ℝ) (hp : p ≠ 0) : zmultiples p ≃+ ℤ := by
  refine (AddEquiv.ofBijective (zmultiplesHom p) ?_).symm
  exact ⟨zmultiplesHom_injective p hp, zmultiplesHom_surjective p⟩

/-- **The opposite of the multiplicative integers is itself (VERIFIED)**:
ℤ is commutative, so `x ↦ xᵒᵖ` (equivalently unop) is a group
isomorphism `(Multiplicative ℤ)ᵐᵒᵖ ≃* Multiplicative ℤ`. -/
def mulOppositeIntEquiv : (Multiplicative ℤ)ᵐᵒᵖ ≃* Multiplicative ℤ where
  toFun := MulOpposite.unop
  invFun := MulOpposite.op
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_mul' := by
    intro a b
    -- unop (a * b) = unop a * unop b in the commutative Multiplicative ℤ
    rw [MulOpposite.unop_mul]
    exact mul_comm (MulOpposite.unop b) (MulOpposite.unop a)

/-- **π₁ of the parameter circle is the infinite cyclic group (VERIFIED)**:
for `p ≠ 0`, `FundamentalGroup (AddCircle p) (0 : AddCircle p) ≃*
Multiplicative ℤ`.  Proof: `ℝ → AddCircle p` is an additive quotient
covering by the deck group `zmultiples p`
(`AddCircle.isAddQuotientCoveringMap_coe`); `ℝ` is simply connected, so
Mathlib's `IsAddQuotientCoveringMap.fundamentalGroupEquiv` gives
`π₁(AddCircle p) ≃* (Multiplicative (zmultiples p))ᵐᵒᵖ` (injectivity —
lift uniqueness over the simply-connected total space; surjectivity — the
standard loops, path-connected total space); the deck group is ℤ
(`zmultiplesEquivInt`), transported through `AddEquiv.toMultiplicative`,
`MulEquiv.op` and `mulOppositeIntEquiv`.  This is the `π₁(S¹) = ℤ` engine
of the winding route (Pi1Mobius route step 4, DONE). -/
noncomputable def fundamentalGroupAddCircle_isoZ (p : ℝ) (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p) (0 : AddCircle p) ≃* Multiplicative ℤ := by
  let cov : ℝ → AddCircle p := QuotientAddGroup.mk
  let e : cov ⁻¹' {(0 : AddCircle p)} := ⟨0, by simp [cov]⟩
  have hcov : IsAddQuotientCoveringMap cov (zmultiples p) := by
    simpa [cov] using (AddCircle.isAddQuotientCoveringMap_coe p)
  have h1 : FundamentalGroup (AddCircle p) (0 : AddCircle p) ≃*
      (Multiplicative (zmultiples p))ᵐᵒᵖ :=
    hcov.fundamentalGroupEquiv e
  have h2 : (Multiplicative (zmultiples p))ᵐᵒᵖ ≃* (Multiplicative ℤ)ᵐᵒᵖ :=
    MulEquiv.op (AddEquiv.toMultiplicative (zmultiplesEquivInt p hp))
  have h3 : (Multiplicative ℤ)ᵐᵒᵖ ≃* Multiplicative ℤ := mulOppositeIntEquiv
  exact h1.trans (h2.trans h3)


/-! ## S264 — the degree of a loop: lift endpoint difference over ℝ
(VERIFIED, sorry-free) — the winding route's first ingredient lemma

The integer in `π₁(AddCircle p) ≅ ℤ` (S263) is given its geometric meaning
here: for a loop `γ` in `AddCircle p`, lift it to a real path `Γ` (the
covering `ℝ → AddCircle p`); since `γ` is a loop the lifted endpoint
differs from the lifted start by an integer multiple of the period, and
that integer is the DEGREE of the loop:

* **`coeffOfZmultiples`** (+ `coeffOfZmultiples_spec`) — the coefficient
  API on the period lattice: every element `x` of `zmultiples p` is
  `(coeff x : ℝ) * p` for the integer `coeff x` (the membership witness of
  `mem_zmultiples_iff`, read off by `Classical.choose`; uniqueness needs
  `p ≠ 0` and is a later lemma);
* **`lift_endpoint_diff_mem_zmultiples`** — a real lift `Γ` of a loop has
  `Γ 1 − Γ 0 ∈ zmultiples p`: at the circle level `(Γ 1 : AddCircle p) =
  γ 1 = x = γ 0 = (Γ 0 : AddCircle p)` (`AddCircle.coe_sub`,
  `Path.source`/`Path.target`), and `AddCircle.coe_eq_zero_iff` lands in
  the period lattice;
* **`loopDegree`** (+ `loopDegree_spec`) — **the degree as the lift
  endpoint difference**: for a loop `γ : Path x x` with a real lift `Γ`,
  `loopDegree hp Γ hΓlifts : ℤ` is the integer with
  `Γ 1 − Γ 0 = (loopDegree hp Γ hΓlifts : ℝ) * period` (p generic);
* **`exists_lift_of_loop`** — every loop lifts over ℝ from any real
  representative of its base point (the covering path-lift
  `IsCoveringMap.exists_path_lifts` of `AddCircle.isCoveringMap_coe`).

STATUS after S264: the degree-as-endpoint-difference spine of the winding
route is verified.  Next ingredient lemmas (S265+): homotopy-invariance of
`loopDegree` (`IsCoveringMap.monodromy` well-defined on
`Path.Homotopic.Quotient` — `liftPath_apply_one_eq_of_homotopicRel`; the
lift-endpoint difference is the same for homotopic loops), well-definedness
of the induced group hom `π₁(AddCircle p) → ℤ` agreeing with the S263 iso
(so the iso's explicit content is the degree), the standard loops of every
degree (surjectivity), and the winding API on the Möbius band.  Tree
green; TWO documented sorries; no children pending.
-/

set_option linter.unusedVariables false

/-- **The integer coefficient of a period-lattice element (VERIFIED)**:
an element `x` of `zmultiples p` is an integer multiple of the period; this
is the integer (the membership witness of `mem_zmultiples_iff`, chosen
canonically).  (Uniqueness of the coefficient requires `p ≠ 0` — a later
lemma; existence is unconditional.) -/
noncomputable def coeffOfZmultiples (p : ℝ) (hp : p ≠ 0) (x : zmultiples p) : ℤ :=
  Classical.choose (AddSubgroup.mem_zmultiples_iff.mp x.2)

/-- **The coefficient reads off the element (VERIFIED)**: for
`x ∈ zmultiples p`, `x.1 = (coeffOfZmultiples p hp x : ℝ) * p`. -/
lemma coeffOfZmultiples_spec (p : ℝ) (hp : p ≠ 0) (x : zmultiples p) :
    x.1 = (coeffOfZmultiples p hp x : ℝ) * p := by
  have h := Classical.choose_spec (AddSubgroup.mem_zmultiples_iff.mp x.2)
  -- h : (coeffOfZmultiples p hp x) • p = x.1
  rw [zsmul_eq_mul] at h
  exact h.symm

/-- **The lifted endpoint difference of a loop lies in the period lattice
(VERIFIED)**: if `Γ : C(I, ℝ)` is a real lift of a loop `γ : Path x x` in
`AddCircle p` (`(Γ t : AddCircle p) = γ t`), then `Γ 1 − Γ 0 ∈ zmultiples
p` — at the circle level `(Γ 1 : AddCircle p) = γ 1 = x = γ 0 =
(Γ 0 : AddCircle p)` (`AddCircle.coe_sub`, `Path.source`, `Path.target`),
and `AddCircle.coe_eq_zero_iff` lands in the period lattice. -/
lemma lift_endpoint_diff_mem_zmultiples {p : ℝ} {x : AddCircle p} {γ : Path x x}
    (Γ : C(I, ℝ)) (hΓlifts : ∀ t : I, (Γ t : AddCircle p) = γ t) :
    Γ 1 - Γ 0 ∈ zmultiples p := by
  rw [AddSubgroup.mem_zmultiples_iff]
  rw [← AddCircle.coe_eq_zero_iff (p := p)]
  rw [AddCircle.coe_sub]
  rw [sub_eq_zero]
  calc
    (Γ 1 : AddCircle p) = γ 1 := hΓlifts 1
    _ = γ 0 := γ.target.trans γ.source.symm
    _ = (Γ 0 : AddCircle p) := (hΓlifts 0).symm

/-- **The degree of a loop as the lift endpoint difference (VERIFIED)**:
for a loop `γ : Path x x` in `AddCircle p` and a real lift `Γ` of it, the
integer `loopDegree hp Γ hΓlifts` is the degree/winding of the loop: the
coefficient of the period lattice element `Γ 1 − Γ 0`
(`lift_endpoint_diff_mem_zmultiples`). -/
noncomputable def loopDegree {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} {γ : Path x x}
    (Γ : C(I, ℝ)) (hΓlifts : ∀ t : I, (Γ t : AddCircle p) = γ t) : ℤ :=
  coeffOfZmultiples p hp ⟨Γ 1 - Γ 0, lift_endpoint_diff_mem_zmultiples Γ hΓlifts⟩

/-- **The degree reads off the lifted endpoint difference (VERIFIED)**: for
a loop `γ` with real lift `Γ`,
`Γ 1 − Γ 0 = (loopDegree hp Γ hΓlifts : ℝ) * p`.  This is the geometric
meaning of the integer in `π₁(AddCircle p) ≅ ℤ` (S263): going once around
the circle advances the real lift by one period. -/
theorem loopDegree_spec {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} {γ : Path x x}
    (Γ : C(I, ℝ)) (hΓlifts : ∀ t : I, (Γ t : AddCircle p) = γ t) :
    Γ 1 - Γ 0 = (loopDegree hp Γ hΓlifts : ℝ) * p := by
  have hspec := coeffOfZmultiples_spec p hp ⟨Γ 1 - Γ 0, lift_endpoint_diff_mem_zmultiples Γ hΓlifts⟩
  simpa [loopDegree] using hspec

/-- **Every loop of the circle lifts over ℝ (VERIFIED)**: for a loop
`γ : Path x x` in `AddCircle p` there is a continuous real lift `Γ` of `γ`
(from any real representative of the base point — the covering path-lift
`IsCoveringMap.exists_path_lifts` of `AddCircle.isCoveringMap_coe`), so
`loopDegree` is defined on every loop. -/
theorem exists_lift_of_loop {p : ℝ} {x : AddCircle p} (γ : Path x x) :
    ∃ Γ : C(I, ℝ), (∀ t : I, (Γ t : AddCircle p) = γ t) ∧
      (∃ e : ℝ, (e : AddCircle p) = x ∧ Γ 0 = e) := by
  let cov : IsCoveringMap (fun y : ℝ => (y : AddCircle p)) := by
    simpa using (AddCircle.isCoveringMap_coe (𝕜 := ℝ) p)
  let γC : C(I, AddCircle p) := ⟨fun t => γ t, γ.continuous⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, (e : AddCircle p) = x := by
    simpa using (QuotientAddGroup.mk_surjective (s := zmultiples p) (x))
  have hγ₀ : γC 0 = (fun y : ℝ => (y : AddCircle p)) e := by
    dsimp [γC]
    rw [he]
    exact γ.source
  rcases cov.exists_path_lifts γC e hγ₀ with ⟨Γ, hΓl, hΓ₀⟩
  refine ⟨Γ, ?_, ⟨e, he, hΓ₀⟩⟩
  intro t
  exact congrFun hΓl t


/-! ## S265 — homotopy invariance of the degree (VERIFIED, sorry-free) —
the winding route's hinge

`loopDegree` (S264) is invariant under homotopy of loops rel endpoints —
the hinge that turns the S263 isomorphism into a *computable* one: the
degree of a loop depends only on its homotopy class, so it descends to a
well-defined map `π₁(AddCircle p) → ℤ` (agreeing with the S263 iso), and
the standard loops of every degree become the surjectivity certificate.

* **`lift_endpoint_diff_independent`** — the endpoint difference of a real
  lift of a loop is independent of the lift: two lifts Γ, Δ of the same
  loop differ by a continuous map into the discrete group `zmultiples p`
  (at every t the circle classes coincide, `AddCircle.coe_sub` +
  `coe_eq_zero_iff`), which is constant on the connected interval I
  (`PreconnectedSpace.constant`, `PreconnectedSpace I`), so
  `Γ 1 − Γ 0 = Δ 1 − Δ 0`;
* **`loopDegree_eq_of_homotopic`** — the main theorem: if two loops
  `γ γ' : Path x x` are homotopic rel endpoints (`Path.Homotopic γ γ'`),
  then for any real lifts Γ of γ and Γ' of γ',
  `loopDegree hp Γ hΓ = loopDegree hp Γ' hΓ'`.  Proof: fix a real
  representative `e` of the base point; lift both loops canonically from
  `e` (covering `cov.liftPath`); Mathlib's
  `liftPath_apply_one_eq_of_homotopicRel` gives equality of the two
  canonical lifted endpoints; `lift_endpoint_diff_independent` relates the
  arbitrary lifts Γ, Γ' to the canonical ones (which start at `e`); the
  endpoint differences agree, hence by `loopDegree_spec` and
  `mul_right_cancel₀` the integer degrees agree.

STATUS after S265: homotopy invariance of `loopDegree` is verified.  Next
ingredient lemmas (S266+): the induced group hom `π₁(AddCircle p) → ℤ`
well-defined on `Path.Homotopic.Quotient`/`FundamentalGroup` agreeing with
the S263 iso; the standard loops of every degree (surjectivity); the
winding API on the Möbius band (once/twice classification).  Tree green;
TWO documented sorries; no children pending.
-/

/-- **The lifted endpoint difference is independent of the lift
(VERIFIED)**: two continuous real lifts Γ, Δ of the same loop γ in
`AddCircle p` satisfy `Γ 1 − Γ 0 = Δ 1 − Δ 0`.  Proof: at every t the two
lifts have the same circle class (`(Γ t : AddCircle p) = γ t = (Δ t :
AddCircle p)`), so `t ↦ Γ t − Δ t` is a continuous map into the discrete
additive group `zmultiples p` (`AddCircle.coe_sub` + `coe_eq_zero_iff`),
constant on the connected interval I (`PreconnectedSpace.constant`,
`PreconnectedSpace I`); comparing t = 1 and t = 0 gives the claim. -/
theorem lift_endpoint_diff_independent {p : ℝ} {x : AddCircle p} {γ : Path x x}
    {Γ Δ : C(I, ℝ)} (hΓ : ∀ t : I, (Γ t : AddCircle p) = γ t)
    (hΔ : ∀ t : I, (Δ t : AddCircle p) = γ t) :
    Γ 1 - Γ 0 = Δ 1 - Δ 0 := by
  -- φ(t) = Γ t − Δ t is continuous with values in the discrete group zmultiples p,
  -- hence constant on the connected interval I
  let φ : I → zmultiples p := fun t => ⟨Γ t - Δ t, by
    rw [AddSubgroup.mem_zmultiples_iff]
    rw [← AddCircle.coe_eq_zero_iff (p := p)]
    rw [AddCircle.coe_sub]
    rw [sub_eq_zero]
    calc
      (Γ t : AddCircle p) = γ t := hΓ t
      _ = (Δ t : AddCircle p) := (hΔ t).symm⟩
  have hφcont : Continuous (fun t : I => Γ t - Δ t) := Γ.continuous.sub Δ.continuous
  have hφ : Continuous φ := Continuous.subtype_mk (f := fun t : I => Γ t - Δ t)
    (by exact hφcont) (fun t => (φ t).2)
  have hφc : φ 1 = φ 0 :=
    PreconnectedSpace.constant (α := I) (Y := zmultiples p)
      (inferInstance : PreconnectedSpace I) hφ
  have hvals : Γ 1 - Δ 1 = Γ 0 - Δ 0 := congrArg Subtype.val hφc
  linarith

/-- **Homotopy invariance of the degree (VERIFIED)**: if two loops
`γ γ' : Path x x` in `AddCircle p` are homotopic rel endpoints
(`Path.Homotopic γ γ'`), then their degrees coincide: for any real lifts
Γ of γ and Γ' of γ', `loopDegree hp Γ hΓ = loopDegree hp Γ' hΓ'`.  Proof:
fix a real representative `e` of the base point `x` and lift both loops
canonically from `e` (`cov.liftPath` of the covering
`ℝ → AddCircle p`); Mathlib's `liftPath_apply_one_eq_of_homotopicRel`
gives equality of the canonical lifted endpoints; the auxiliary
`lift_endpoint_diff_independent` relates the arbitrary lifts Γ, Γ' to the
canonical ones (both canonical lifts start at `e`); the endpoint
differences agree, so by `loopDegree_spec` and `mul_right_cancel₀` the
integer degrees agree.  This is the hinge that makes the S263
isomorphism computable: the degree descends to the homotopy class of the
loop. -/
theorem loopDegree_eq_of_homotopic {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    {γ γ' : Path x x} (h : Path.Homotopic γ γ') :
    ∀ {Γ : C(I, ℝ)} (hΓ : ∀ t : I, (Γ t : AddCircle p) = γ t)
      {Γ' : C(I, ℝ)} (hΓ' : ∀ t : I, (Γ' t : AddCircle p) = γ' t),
      loopDegree hp Γ hΓ = loopDegree hp Γ' hΓ' := by
  intro Γ hΓ Γ' hΓ'
  let cov : IsCoveringMap (fun y : ℝ => (y : AddCircle p)) := by
    simpa using (AddCircle.isCoveringMap_coe (𝕜 := ℝ) p)
  obtain ⟨e, he⟩ : ∃ e : ℝ, (e : AddCircle p) = x := by
    simpa using (QuotientAddGroup.mk_surjective (s := zmultiples p) (x))
  let γC : C(I, AddCircle p) := γ.toContinuousMap
  let γC' : C(I, AddCircle p) := γ'.toContinuousMap
  have h₀ : γC 0 = (fun y : ℝ => (y : AddCircle p)) e := by
    change γ 0 = (e : AddCircle p)
    rw [he]
    exact γ.source
  have h₀' : γC' 0 = (fun y : ℝ => (y : AddCircle p)) e := by
    change γ' 0 = (e : AddCircle p)
    rw [he]
    exact γ'.source
  -- canonical lifts from e
  let Γc : C(I, ℝ) := cov.liftPath γC e h₀
  let Γc' : C(I, ℝ) := cov.liftPath γC' e h₀'
  have hΓc : ∀ t : I, (Γc t : AddCircle p) = γC t := by
    intro t
    have hl := congrFun (cov.liftPath_lifts γC e h₀) t
    simpa [Γc] using hl
  have hΓc' : ∀ t : I, (Γc' t : AddCircle p) = γC' t := by
    intro t
    have hl := congrFun (cov.liftPath_lifts γC' e h₀') t
    simpa [Γc'] using hl
  -- homotopy-invariance of the canonical lift endpoint (Mathlib)
  have H := h.some
  -- H : γ.Homotopy γ' = HomotopyRel γ.toContinuousMap γ'.toContinuousMap {0,1}
  have hh : ContinuousMap.HomotopicRel γC γC' ({0, 1} : Set I) := ⟨H⟩
  have hend : Γc 1 = Γc' 1 := by
    dsimp [Γc, Γc']
    exact cov.liftPath_apply_one_eq_of_homotopicRel hh e h₀ h₀'
  -- endpoint differences of arbitrary lifts equal those of the canonical ones
  have hdiff : Γ 1 - Γ 0 = Γc 1 - Γc 0 := by
    apply lift_endpoint_diff_independent (p := p) (γ := γ) (Γ := Γ) (Δ := Γc) hΓ
    intro t
    simpa [γC] using (hΓc t)
  have hdiff' : Γ' 1 - Γ' 0 = Γc' 1 - Γc' 0 := by
    apply lift_endpoint_diff_independent (p := p) (γ := γ') (Γ := Γ') (Δ := Γc') hΓ'
    intro t
    simpa [γC'] using (hΓc' t)
  -- canonical lifts start at e
  have hΓc0 : Γc 0 = e := cov.liftPath_zero γC e h₀
  have hΓc'0 : Γc' 0 = e := cov.liftPath_zero γC' e h₀'
  -- degrees equal since endpoint differences equal
  have hdeg : (loopDegree hp Γ hΓ : ℝ) * p = (loopDegree hp Γ' hΓ' : ℝ) * p := by
    rw [← loopDegree_spec hp Γ hΓ, ← loopDegree_spec hp Γ' hΓ']
    calc
      Γ 1 - Γ 0 = Γc 1 - Γc 0 := hdiff
      _ = Γc' 1 - Γc' 0 := by rw [hΓc0, hΓc'0]; exact congrArg (fun z => z - e) hend
      _ = Γ' 1 - Γ' 0 := hdiff'.symm
  have hc : (loopDegree hp Γ hΓ : ℝ) = (loopDegree hp Γ' hΓ' : ℝ) := mul_right_cancel₀ hp hdeg
  exact_mod_cast hc


/-! ## S266 — the degree as a map on homotopy classes of loops (VERIFIED,
sorry-free) — the quotient of `loopDegree` over `Path.Homotopic.Quotient`

With homotopy invariance (S265), `loopDegree` descends to the quotient of
loops by homotopy rel endpoints (`Path.Homotopic.Quotient x x` — the
fundamental-group carrier): the degree becomes a well-defined function on
homotopy classes.

* **`liftOfLoop`** (+ `liftOfLoop_lifts`) — a canonical real lift of a
  loop (the choice from `exists_lift_of_loop`, S264), so the degree is a
  plain function of the loop;
* **`loopDegreePath`** — the degree of a loop as a function on paths,
  computed with the canonical lift;
* **`loopDegreePath_eq_of_homotopic`** — homotopic loops have equal
  `loopDegreePath` (S265 instanced at the canonical lifts);
* **`loopDegreeQuotient`** (+ `loopDegreeQuotient_mk`) — **the degree as a
  map `Path.Homotopic.Quotient x x → ℤ`**, defined by
  `Quotient.lift` on `loopDegreePath` with the S265 well-definedness
  proof, and reading back through `Quotient.mk` as `loopDegreePath`.

STATUS after S266: the degree is a well-defined map on homotopy classes of
loops.  Next (S267+): the group-homomorphism structure — `loopDegreeQuotient`
respects loop concatenation (`IsCoveringMap.liftPath_trans`: the lifted
endpoint of a concatenation is the sum of the lifted endpoints, so
`deg (γ.trans δ) = deg γ + deg δ`), identifying
`loopDegreeQuotient` with the S263 isomorphism `π₁(AddCircle p) ≃* ℤ` (it
suffices to check agreement on the generator loop — the standard loop of
degree 1); the standard loops of every degree (surjectivity) via the
explicit loops `t ↦ (n · t · p : AddCircle p)`.  Tree green; TWO
documented sorries; no children pending.
-/

/-- **A canonical real lift of a loop (VERIFIED)**: the lift chosen from
`exists_lift_of_loop` (S264) — makes the degree a plain function of the
loop, with no choice of lift left downstream. -/
noncomputable def liftOfLoop {p : ℝ} {x : AddCircle p} (γ : Path x x) : C(I, ℝ) :=
  Classical.choose (exists_lift_of_loop (p := p) (x := x) γ)

/-- **The canonical lift covers the loop (VERIFIED)**: for every `t`,
`(liftOfLoop γ t : AddCircle p) = γ t`. -/
lemma liftOfLoop_lifts {p : ℝ} {x : AddCircle p} (γ : Path x x) :
    ∀ t : I, (liftOfLoop γ t : AddCircle p) = γ t := by
  exact (Classical.choose_spec (exists_lift_of_loop (p := p) (x := x) γ)).1

/-- **The degree of a loop as a function on paths (VERIFIED)**: the degree
of a loop computed with its canonical real lift (`liftOfLoop`) — a plain
`Path x x → ℤ` function (no lift choice downstream). -/
noncomputable def loopDegreePath {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} (γ : Path x x) : ℤ :=
  loopDegree hp (liftOfLoop γ) (liftOfLoop_lifts γ)

/-- **Homotopic loops have equal path-degree (VERIFIED)**: S265 instanced
at the canonical lifts — `loopDegreePath` is constant on homotopy classes
of loops rel endpoints. -/
theorem loopDegreePath_eq_of_homotopic {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    {γ γ' : Path x x} (h : Path.Homotopic γ γ') :
    loopDegreePath hp γ = loopDegreePath hp γ' := by
  unfold loopDegreePath
  exact loopDegree_eq_of_homotopic hp h (liftOfLoop_lifts γ) (liftOfLoop_lifts γ')

/-- **The degree as a map on homotopy classes of loops (VERIFIED)**: the
well-defined function `Path.Homotopic.Quotient x x → ℤ` induced by
`loopDegreePath` on the quotient of loops by homotopy rel endpoints
(`Quotient.lift` with the S265 well-definedness proof) — the degree now
lives on the fundamental-group carrier. -/
noncomputable def loopDegreeQuotient {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} :
    Path.Homotopic.Quotient x x → ℤ :=
  Quotient.lift (loopDegreePath (p := p) (x := x) hp) (by
    intro γ γ' h
    exact loopDegreePath_eq_of_homotopic hp h)

/-- **The quotient degree reads the path degree (VERIFIED)**: through the
canonical `Quotient.mk` of a loop, `loopDegreeQuotient` is
`loopDegreePath` (rfl — the lift construction). -/
lemma loopDegreeQuotient_mk {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} (γ : Path x x) :
    loopDegreeQuotient hp (Path.Homotopic.Quotient.mk γ) = loopDegreePath hp γ := by
  rfl


/-! ## S267 — the degree respects concatenation: `loopDegreeQuotient` is a
group homomorphism (VERIFIED, sorry-free)

The degree of a concatenation of loops is the sum of the degrees — the
group-homomorphism content that, together with the degree-1 generator,
identifies `loopDegreeQuotient` with the S263 isomorphism
`π₁(AddCircle p) ≃* ℤ`:

* **`loopDegree_eq_of_lifts`** — the degree is independent of the chosen
  lift of the loop (endpoint differences equal by
  `lift_endpoint_diff_independent`, then `loopDegree_spec` +
  `mul_right_cancel₀`);
* **`coeffOfZmultiples_unique`** — the lattice coefficient is unique
  (`p ≠ 0`): if `x = (n : ℝ) * p` then `coeffOfZmultiples p hp x = n`;
* **`coeffOfZmultiples_add`** — the coefficient is additive on the period
  lattice (`coeff (x + y) = coeff x + coeff y`, from the two specs + the
  uniqueness);
* **`loopDegreePath_trans`** — **the path-level additivity**: for loops
  `γ δ : Path x x`, `loopDegreePath hp (γ.trans δ) = loopDegreePath hp γ +
  loopDegreePath hp δ`.  Proof: fix a real representative `e` of the base
  point; canonical lifts `A := cov.liftPath γ e`, `B := cov.liftPath δ
  (A 1)` (the second starting at the first's endpoint); the real
  concatenation `P := A.trans B` lifts `γ.trans δ` from `e` (pointwise
  via `Path.trans_apply`, split at `1/2`), so the degree of `γ.trans δ`
  is the coefficient of `P 1 − P 0 = B 1 − e = (A 1 − e) + (B 1 − A 1)`;
  the three endpoint differences are the period-lattice elements for the
  degrees of `γ`, `δ`, `γ.trans δ`, and `coeffOfZmultiples_add` sums
  them;
* **`loopDegreeQuotient_trans`** — the quotient-level concatenation law:
  `loopDegreeQuotient (mk (γ.trans δ)) = loopDegreeQuotient (mk γ) +
  loopDegreeQuotient (mk δ)` (the path-level additivity through
  `loopDegreeQuotient_mk`).

STATUS after S267: `loopDegreeQuotient` is additive over concatenation —
the group-homomorphism content of the degree.  Next (S268+): the degree-1
generator loop (the standard loop `t ↦ (t · period : AddCircle period)`),
agreement of `loopDegreeQuotient` with the S263 iso on the generator
(hence as group homs), and the standard loops of every degree
(surjectivity).  Tree green; TWO documented sorries; no children pending.
-/

/-- **The degree is independent of the chosen lift (VERIFIED)**: two real
lifts Γ, Δ of the same loop γ give the same `loopDegree` — the endpoint
differences agree (`lift_endpoint_diff_independent`) and the coefficient
of an endpoint difference is a function of it (`loopDegree_spec` +
`mul_right_cancel₀`). -/
theorem loopDegree_eq_of_lifts {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} {γ : Path x x}
    {Γ Δ : C(I, ℝ)} (hΓ : ∀ t : I, (Γ t : AddCircle p) = γ t)
    (hΔ : ∀ t : I, (Δ t : AddCircle p) = γ t) :
    loopDegree hp Γ hΓ = loopDegree hp Δ hΔ := by
  have hdiff := lift_endpoint_diff_independent (p := p) (γ := γ) hΓ hΔ
  have h1 := loopDegree_spec hp Γ hΓ
  have h2 := loopDegree_spec hp Δ hΔ
  have hdeg : (loopDegree hp Γ hΓ : ℝ) * p = (loopDegree hp Δ hΔ : ℝ) * p := by
    rw [← h1, ← h2]
    exact hdiff
  have hc : (loopDegree hp Γ hΓ : ℝ) = (loopDegree hp Δ hΔ : ℝ) := mul_right_cancel₀ hp hdeg
  exact_mod_cast hc

/-- **The period-lattice coefficient is unique (VERIFIED)**: for `p ≠ 0`,
if `x.1 = (n : ℝ) * p` then `coeffOfZmultiples p hp x = n` (the
coefficient is the unique integer multiple of the period equal to the
element). -/
lemma coeffOfZmultiples_unique (p : ℝ) (hp : p ≠ 0) {x : zmultiples p} {n : ℤ}
    (h : x.1 = (n : ℝ) * p) : coeffOfZmultiples p hp x = n := by
  have hc := coeffOfZmultiples_spec p hp x
  have h' : (coeffOfZmultiples p hp x : ℝ) * p = (n : ℝ) * p := by
    rw [← hc]
    exact h
  have hc' : (coeffOfZmultiples p hp x : ℝ) = (n : ℝ) := mul_right_cancel₀ hp h'
  exact_mod_cast hc'

/-- **The coefficient is additive on the period lattice (VERIFIED)**:
`coeffOfZmultiples p hp (x + y) = coeffOfZmultiples p hp x +
coeffOfZmultiples p hp y` — the sum of two lattice elements has the sum of
their coefficients (from the two specs and the uniqueness). -/
lemma coeffOfZmultiples_add (p : ℝ) (hp : p ≠ 0) (x y : zmultiples p) :
    coeffOfZmultiples p hp (x + y) = coeffOfZmultiples p hp x + coeffOfZmultiples p hp y := by
  have hx := coeffOfZmultiples_spec p hp x
  have hy := coeffOfZmultiples_spec p hp y
  apply coeffOfZmultiples_unique p hp (x := x + y) (n := coeffOfZmultiples p hp x + coeffOfZmultiples p hp y)
  calc
    (x + y : zmultiples p).1 = x.1 + y.1 := rfl
    _ = (coeffOfZmultiples p hp x : ℝ) * p + (coeffOfZmultiples p hp y : ℝ) * p := by rw [hx, hy]
    _ = ((coeffOfZmultiples p hp x + coeffOfZmultiples p hp y : ℤ) : ℝ) * p := by
      rw [Int.cast_add]
      ring

/-- **The degree of a concatenation is the sum of the degrees
(VERIFIED)**: for loops `γ δ : Path x x` in `AddCircle p`,
`loopDegreePath hp (γ.trans δ) = loopDegreePath hp γ + loopDegreePath hp
δ`.  Proof: fix a real representative `e` of the base point; canonical
lifts `A := cov.liftPath γ e` and `B := cov.liftPath δ (A 1)` (the second
starting at the first's endpoint — the concatenation structure); the real
path `P := A.trans B` lifts `γ.trans δ` from `e` (pointwise via
`Path.trans_apply`, split at `1/2`), so the degree of `γ.trans δ` is the
coefficient of `P 1 − P 0 = B 1 − e = (A 1 − e) + (B 1 − A 1)`; those
three endpoint differences are exactly the period-lattice elements
carrying the degrees of `γ`, `δ`, `γ.trans δ` (the individual degrees
relate to the canonical lifts by `loopDegree_eq_of_lifts`), and
`coeffOfZmultiples_add` sums the coefficients. -/
theorem loopDegreePath_trans {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} (γ δ : Path x x) :
    loopDegreePath hp (γ.trans δ) = loopDegreePath hp γ + loopDegreePath hp δ := by
  let cov : IsCoveringMap (fun y : ℝ => (y : AddCircle p)) := by
    simpa using (AddCircle.isCoveringMap_coe (𝕜 := ℝ) p)
  obtain ⟨e, he⟩ : ∃ e : ℝ, (e : AddCircle p) = x := by
    simpa using (QuotientAddGroup.mk_surjective (s := zmultiples p) (x))
  let hpe : x = (fun y : ℝ => (y : AddCircle p)) e := he.symm
  let A : C(I, ℝ) := cov.liftPath γ e (γ.source.trans hpe)
  have hA : ∀ t : I, (A t : AddCircle p) = γ t := by
    intro t
    have hl := congrFun (cov.liftPath_lifts γ e (γ.source.trans hpe)) t
    simpa [A] using hl
  have hA0 : A 0 = e := by simpa [A] using (cov.liftPath_zero γ e (γ.source.trans hpe))
  have hpeA : (A 1 : AddCircle p) = x := (hA 1).trans γ.target
  let B : C(I, ℝ) := cov.liftPath δ (A 1) (δ.source.trans hpeA.symm)
  have hB : ∀ t : I, (B t : AddCircle p) = δ t := by
    intro t
    have hl := congrFun (cov.liftPath_lifts δ (A 1) (δ.source.trans hpeA.symm)) t
    simpa [B] using hl
  have hB0 : B 0 = A 1 := by simpa [B] using (cov.liftPath_zero δ (A 1) (δ.source.trans hpeA.symm))
  let P1 : Path e (A 1) := Path.mk A hA0 rfl
  let P2 : Path (A 1) (B 1) := Path.mk B hB0 rfl
  let P : Path e (B 1) := P1.trans P2
  have hPlift : ∀ t : I, (P t : AddCircle p) = (γ.trans δ) t := by
    intro t
    dsimp [P, P1, P2]
    rw [Path.trans_apply, Path.trans_apply]
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · have ht2 : (t : ℝ) ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using ht
      simp [ht2]
      apply hA
    · have hnt : ¬(t : ℝ) ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using ht
      simp [hnt]
      apply hB
  have hP0 : P 0 = e := P.source
  have hP1 : P 1 = B 1 := P.target
  have memA : A 1 - e ∈ zmultiples p := by
    simpa [hA0] using (lift_endpoint_diff_mem_zmultiples (p := p) A hA)
  have memB : B 1 - A 1 ∈ zmultiples p := by
    simpa [hB0] using (lift_endpoint_diff_mem_zmultiples (p := p) B hB)
  have memP : P 1 - P 0 ∈ zmultiples p := by
    exact lift_endpoint_diff_mem_zmultiples (p := p) (γ := γ.trans δ)
      ⟨fun t => P t, P.continuous⟩ (by intro t; simpa using hPlift t)
  let u : zmultiples p := ⟨A 1 - e, memA⟩
  let v : zmultiples p := ⟨B 1 - A 1, memB⟩
  have hsum : (⟨P 1 - P 0, memP⟩ : zmultiples p) = u + v := by
    apply Subtype.ext
    dsimp [u, v]
    rw [hP1, hP0]
    ring
  have hcoeffP : coeffOfZmultiples p hp ⟨P 1 - P 0, memP⟩ =
      coeffOfZmultiples p hp u + coeffOfZmultiples p hp v := by
    rw [hsum]
    exact coeffOfZmultiples_add p hp u v
  have hdγ : loopDegreePath hp γ = coeffOfZmultiples p hp u := by
    unfold loopDegreePath
    rw [loopDegree_eq_of_lifts hp (liftOfLoop_lifts γ) hA]
    unfold loopDegree
    congr 1
    apply Subtype.ext
    dsimp [u]
    rw [hA0]
  have hdδ : loopDegreePath hp δ = coeffOfZmultiples p hp v := by
    unfold loopDegreePath
    rw [loopDegree_eq_of_lifts hp (liftOfLoop_lifts δ) hB]
    unfold loopDegree
    congr 1
    apply Subtype.ext
    dsimp [v]
    rw [hB0]
  have hP_lift : ∀ t : I, ((⟨fun t => P t, by fun_prop⟩ : C(I, ℝ)) t : AddCircle p) =
      (γ.trans δ) t := by
    intro t
    exact hPlift t
  have hdγδ : loopDegreePath hp (γ.trans δ) = coeffOfZmultiples p hp ⟨P 1 - P 0, memP⟩ := by
    unfold loopDegreePath
    rw [loopDegree_eq_of_lifts hp (liftOfLoop_lifts (γ.trans δ)) hP_lift]
    unfold loopDegree
    congr 1
  calc
    loopDegreePath hp (γ.trans δ) = coeffOfZmultiples p hp ⟨P 1 - P 0, memP⟩ := hdγδ
    _ = coeffOfZmultiples p hp u + coeffOfZmultiples p hp v := hcoeffP
    _ = loopDegreePath hp γ + loopDegreePath hp δ := by rw [hdγ, hdδ]

/-- **The quotient degree respects concatenation (VERIFIED)**: at the
level of homotopy classes,
`loopDegreeQuotient (mk (γ.trans δ)) = loopDegreeQuotient (mk γ) +
loopDegreeQuotient (mk δ)` — the additive group-homomorphism content of
the degree on `Path.Homotopic.Quotient x x` (the fundamental-group
carrier). -/
theorem loopDegreeQuotient_trans {p : ℝ} (hp : p ≠ 0) {x : AddCircle p} (γ δ : Path x x) :
    loopDegreeQuotient hp (Path.Homotopic.Quotient.mk (γ.trans δ)) =
      loopDegreeQuotient hp (Path.Homotopic.Quotient.mk γ) +
      loopDegreeQuotient hp (Path.Homotopic.Quotient.mk δ) := by
  rw [loopDegreeQuotient_mk, loopDegreeQuotient_mk, loopDegreeQuotient_mk]
  exact loopDegreePath_trans hp γ δ


/-! ## S268 — the degree-1 generator loop of `AddCircle p` (VERIFIED,
sorry-free)

The standard loop `t ↦ (t · p : AddCircle p)` (one full circuit of the
circle, winding the real line from `0` to `p`) has degree exactly `1` — the
generator of the S263 isomorphism `π₁(AddCircle p) ≃* ℤ`:

* **`standardLoop`** — the standard loop `γ : Path 0 0` of `AddCircle p`,
  `γ t = ((t : ℝ) * p : AddCircle p)` (a genuine loop: at `t = 1` the
  value is `(p : AddCircle p) = 0` by `AddCircle.coe_period`);
* **`standardLift`** (+ `standardLift_lifts`) — its real lift
  `t ↦ (t : ℝ) * p` (covers the loop by rfl);
* **`standardLoop_degree`** — the generator has degree `1`: the lift
  endpoint difference is `p − 0 = p = (1 : ℝ) * p`, so the coefficient is
  `1` (`loopDegree_spec` + `mul_right_cancel₀`);
* **`standardLoop_degreePath`** / **`standardLoop_degreeQuotient`** — the
  path-level and quotient-level statements
  (`loopDegreePath hp (standardLoop p) = 1`,
  `loopDegreeQuotient hp (mk (standardLoop p)) = 1`), via the lift
  independence (`loopDegree_eq_of_lifts`, S267) and
  `loopDegreeQuotient_mk` (S266).

STATUS after S268: the degree-1 generator is verified (generic `p ≠ 0`;
instantiate `p = period` for the knot parameter circle).  Next (S269+):
agreement of `loopDegreeQuotient` with the S263 iso
`π₁(AddCircle p) ≃* ℤ` (both are group homs — S267 additivity, S268 value
on the generator — hence equal), and the standard loops of every degree
(`t ↦ (n · t · p : AddCircle p)`, degree `n`) giving surjectivity.  Tree
green; TWO documented sorries; no children pending.
-/

/-- **The standard loop of `AddCircle p` (VERIFIED)**: one full circuit of
the circle, `γ t = ((t : ℝ) * p : AddCircle p)` for `t : I` — a genuine
loop based at `0` (at `t = 1` the value is `(p : AddCircle p) = 0` by
`AddCircle.coe_period`). -/
def standardLoop (p : ℝ) : Path (0 : AddCircle p) (0 : AddCircle p) := by
  refine Path.mk ⟨fun t : I => ((t : ℝ) * p : AddCircle p), ?_⟩ ?_ ?_
  · have hpar : Continuous (fun t : I => (t : ℝ) * p) :=
      (continuous_subtype_val : Continuous (fun t : I => (t : ℝ))).mul continuous_const
    exact (AddCircle.continuous_mk' p).comp hpar
  · simp
  · simp [AddCircle.coe_period]

/-- **The real lift of the standard loop (VERIFIED)**: `t ↦ (t : ℝ) * p`,
a continuous real path lifting the standard loop (the covering
`ℝ → AddCircle p`). -/
def standardLift (p : ℝ) : C(I, ℝ) :=
  ⟨fun t : I => (t : ℝ) * p, by
    exact (continuous_subtype_val : Continuous (fun t : I => (t : ℝ))).mul continuous_const⟩

/-- **The standard lift covers the standard loop (VERIFIED)**: for every
`t`, `(standardLift p t : AddCircle p) = standardLoop p t` (rfl — the loop
is defined as the coefficient of its lift). -/
lemma standardLift_lifts (p : ℝ) :
    ∀ t : I, (standardLift p t : AddCircle p) = standardLoop p t := by
  intro t
  rfl

/-- **The generator loop has degree 1 (VERIFIED)**: the lift endpoint
difference of the standard loop is `p − 0 = p = (1 : ℝ) * p`, so its
coefficient (`loopDegree`, via `loopDegree_spec` and `mul_right_cancel₀`,
`p ≠ 0`) is the integer `1`. -/
theorem standardLoop_degree (p : ℝ) (hp : p ≠ 0) :
    loopDegree hp (standardLift p) (standardLift_lifts p) = 1 := by
  have hspec := loopDegree_spec hp (standardLift p) (standardLift_lifts p)
  have hlhs : standardLift p 1 - standardLift p 0 = p := by
    dsimp [standardLift]
    norm_num
  have hdeg : (loopDegree hp (standardLift p) (standardLift_lifts p) : ℝ) * p = (1 : ℝ) * p := by
    rw [← hspec, hlhs]
    ring
  have hc : (loopDegree hp (standardLift p) (standardLift_lifts p) : ℝ) = (1 : ℝ) :=
    mul_right_cancel₀ hp hdeg
  norm_num at hc ⊢
  exact_mod_cast hc

/-- **The generator loop has path-degree 1 (VERIFIED)**: `loopDegreePath hp
(standardLoop p) = 1` — the canonical-lift degree of the standard loop
(its real lift `standardLift` and the canonical `liftOfLoop` agree by the
lift independence `loopDegree_eq_of_lifts`, S267). -/
theorem standardLoop_degreePath (p : ℝ) (hp : p ≠ 0) :
    loopDegreePath hp (standardLoop p) = 1 := by
  unfold loopDegreePath
  rw [loopDegree_eq_of_lifts hp (liftOfLoop_lifts (standardLoop p)) (standardLift_lifts p)]
  exact standardLoop_degree p hp

/-- **The generator loop has quotient-degree 1 (VERIFIED)**: on the
homotopy-class level, `loopDegreeQuotient hp (mk (standardLoop p)) = 1`
(through `loopDegreeQuotient_mk`, S266). -/
theorem standardLoop_degreeQuotient (p : ℝ) (hp : p ≠ 0) :
    loopDegreeQuotient hp (Path.Homotopic.Quotient.mk (standardLoop p)) = 1 := by
  rw [loopDegreeQuotient_mk]
  exact standardLoop_degreePath p hp


/-! ## S269 — the monodromy of the generator loop is the translation by p
(VERIFIED, sorry-free) — item (i) of the S263-iso agreement chain

The agreement between `loopDegreeQuotient` and the S263 isomorphism
`π₁(AddCircle p) ≃* ℤ` (target statement recorded in ROADMAP S269 STATUS)
is reduced to checking the generator under the monodromy-based iso.  This
section proves item (i) of that chain — the monodromy of the standard loop
at the basepoint fibre element is the translation by the period:

* **`coeC`** — the covering map `ℝ → AddCircle p` as a bundled continuous
  map;
* **`realPath`** — the standard loop as a real path `0 → p` (its toFun is
  the real lift `standardLift p`);
* **`realPath_map_eq_standard`** (lemma, in the proof) — the map of the
  real path to the circle is the standard loop up to the endpoint cast
  (`Path.ext`: both have toFun `t ↦ (t · p : AddCircle p)`,
  `standardLift_lifts`);
* **`monodromy_standardLoop`** — **the crux**: the monodromy of the
  standard-loop class at the fibre element `⟨0, ·⟩` is the fibre element
  `⟨p, AddCircle.coe_period⟩` (the translation by one period):
  `IsCoveringMap.monodromy (mk (standardLoop p)) ⟨0, ·⟩ = ⟨p, coe_period⟩`.
  Proof: `IsCoveringMap.monodromy_eq_of_map_eq` with the lifted real path
  `Γ := mk (realPath p)` (class of `0 → p`): the side condition is
  `Γ.map coeC = (mk (standardLoop p)).cast ex.2 ey.2`, assembled from
  `Path.Homotopic.Quotient.mk_map` (map commutes with `mk`),
  `Path.Homotopic.Quotient.mk_cast` (cast commutes with `mk`) and the path
  equality `realPath.map coeC = (standardLoop p).cast ex.2 ey.2`
  (`Path.ext` on the shared toFun).

STATUS after S269 (part 1): item (i) — monodromy of the generator — is
VERIFIED.  Remaining in the S269 chain (ROADMAP): (ii) the deck
identification `zmultiplesEquivInt ⟨p, ·⟩ = 1` (via
`zmultiplesHom 1 = ⟨p, ·⟩` + `Equiv.symm_apply_apply`); (iii) the S263-iso
value on the generator `α (mk (standardLoop p)) = ofAdd 1`, using the
additive `IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff`
with the monodromy of (i); (iv) the zpow-degree lemma
(`loopDegreeQuotient` of an integer power is the power of the degree,
from S267 additivity); (v) the agreement theorem
`loopDegreeQuotient hp q = Multiplicative.toAdd (α q)` by the free-cyclic
argument.  Tree green; TWO documented sorries; no children pending.
-/

/-- **The covering map `ℝ → AddCircle p`, bundled (VERIFIED)**: the
continuous map sending a real to its class in the circle. -/
def coeC (p : ℝ) : C(ℝ, AddCircle p) :=
  ⟨fun y : ℝ => (y : AddCircle p), by simpa using (AddCircle.continuous_mk' p)⟩

/-- **The standard loop as a real path from `0` to `p` (VERIFIED)**: the
real path whose toFun is the real lift `standardLift p` — it maps to the
standard loop of `AddCircle p` under the covering map. -/
def realPath (p : ℝ) : Path (0 : ℝ) p :=
  Path.mk (standardLift p) (by dsimp [standardLift]; norm_num) (by dsimp [standardLift]; norm_num)

/-- **The monodromy of the generator loop is the translation by `p`
(VERIFIED)** — item (i) of the S263-iso agreement chain: the monodromy of
the standard-loop class at the fibre element `⟨0, ·⟩` over the basepoint
is the fibre element `⟨p, AddCircle.coe_period⟩` — one circuit of the
circle translates the real lift by exactly one period.  Proof:
`IsCoveringMap.monodromy_eq_of_map_eq` with the lifted real path
`Γ := mk (realPath p)` (the class of the real path `0 → p`); the side
condition `Γ.map coeC = (mk (standardLoop p)).cast ex.2 ey.2` is assembled
from `Path.Homotopic.Quotient.mk_map`, `Path.Homotopic.Quotient.mk_cast`
and the path equality `realPath.map coeC = (standardLoop p).cast ex.2
ey.2` (both have toFun `t ↦ (t · p : AddCircle p)`,
`standardLift_lifts`, by `Path.ext`). -/
lemma monodromy_standardLoop (p : ℝ) :
    (AddCircle.isCoveringMap_coe (𝕜 := ℝ) p).monodromy
      (Path.Homotopic.Quotient.mk (standardLoop p))
      (⟨0, by simp⟩ : (fun y : ℝ => (y : AddCircle p)) ⁻¹' {(0 : AddCircle p)}) =
      (⟨p, by simp [AddCircle.coe_period]⟩ : (fun y : ℝ => (y : AddCircle p)) ⁻¹' {(0 : AddCircle p)}) := by
  let cov : IsCoveringMap (fun y : ℝ => (y : AddCircle p)) := by
    simpa using (AddCircle.isCoveringMap_coe (𝕜 := ℝ) p)
  let ex : (fun y : ℝ => (y : AddCircle p)) ⁻¹' {(0 : AddCircle p)} := ⟨0, by simp⟩
  let ey : (fun y : ℝ => (y : AddCircle p)) ⁻¹' {(0 : AddCircle p)} := ⟨p, by simp [AddCircle.coe_period]⟩
  have hpath : (realPath p).map (coeC p).continuous = (standardLoop p).cast ex.2 ey.2 := by
    apply Path.ext
    funext t
    rw [Path.map_coe]
    change ((realPath p) t : AddCircle p) = (standardLoop p) t
    simp [realPath]
    exact standardLift_lifts p t
  have heq1 : Path.Homotopic.Quotient.mk ((realPath p).map (coeC p).continuous) =
      Path.Homotopic.Quotient.mk ((standardLoop p).cast ex.2 ey.2) :=
    congrArg Path.Homotopic.Quotient.mk hpath
  have heq2 : Path.Homotopic.Quotient.mk ((standardLoop p).cast ex.2 ey.2) =
      (Path.Homotopic.Quotient.mk (standardLoop p)).cast ex.2 ey.2 :=
    Path.Homotopic.Quotient.mk_cast (standardLoop p) ex.2 ey.2
  have heq : (Path.Homotopic.Quotient.mk (realPath p)).map (coeC p) =
      (Path.Homotopic.Quotient.mk (standardLoop p)).cast ex.2 ey.2 := by
    rw [← Path.Homotopic.Quotient.mk_map]
    exact heq1.trans heq2
  let Γ : Path.Homotopic.Quotient (ex : ℝ) (ey : ℝ) := Path.Homotopic.Quotient.mk (realPath p)
  have hm := cov.monodromy_eq_of_map_eq (γ := Path.Homotopic.Quotient.mk (standardLoop p))
    (ex := ex) (ey := ey) Γ heq
  simpa [cov, ex, ey, Γ] using hm


/-! ## S270 — the S263 iso sends the generator loop to the generator of ℤ
(VERIFIED, sorry-free) — items (ii)+(iii) of the agreement chain

Continuing the S269 chain (items (ii) and (iii) of the ROADMAP S269
STATUS): the deck identification and the generator value under the S263
isomorphism.

* **`deckP`** — the period element `⟨p, ·⟩` of the deck group
  `zmultiples p` (the translation by one period);
* **`deck_smul_zero`** — its action on the basepoint lift is the
  translation: `(ofAdd (deckP p)) • (0 : ℝ) = p`;
* **`zmultiplesHom_one`** — `zmultiplesHom p 1 = deckP p` (the hom `ℤ →+
  zmultiples p`, `n ↦ n • p`, sends `1` to `p` by `one_zsmul`);
* **`zmultiplesEquivInt_p`** — **item (ii), the deck identification**:
  `zmultiplesEquivInt p hp (deckP p) = 1` (the deck-group iso to ℤ sends
  the translation by one period to the integer `1`, by
  `(AddEquiv.ofBijective (zmultiplesHom p) ·).symm_apply_apply 1`);
* **`fgToMulOpposite_gen`** — the additive
  `fundamentalGroupToMulOpposite` of the generator loop is
  `op (ofAdd (deckP p))`: the iff
  `IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff`
  reduces it to `(ofAdd (deckP p)) • 0 = monodromy (mk (standardLoop p))
  ⟨0, ·⟩`, closed by `deck_smul_zero` + `monodromy_standardLoop` (S269);
* **`isoZ_eq_comp`** — the S263 iso decomposes as
  `α = h1.trans (h2.trans h3)` with the fundamentalGroupEquiv,
  `MulEquiv.op (AddEquiv.toMultiplicative (zmultiplesEquivInt p hp))` and
  `mulOppositeIntEquiv` (unfold + `MulEquiv.trans_apply`/
  `MulEquiv.op_apply_apply`);
* **`isoZ_gen`** — **item (iii), the generator value**: the S263 iso sends
  the standard-loop class to the generator of the multiplicative ℤ:
  `fundamentalGroupAddCircle_isoZ p hp (mk (standardLoop p)) =
  Multiplicative.ofAdd (1 : ℤ)` — assemble `isoZ_eq_comp`, `fgToMulOpposite_gen`,
  `zmultiplesEquivInt_p` (through `AddEquiv.toMultiplicative`) and the
  unop of `mulOppositeIntEquiv`.

STATUS after S270: items (i) monodromy of the generator (S269), (ii) the
deck identification, and (iii) the S263-iso value on the generator are
VERIFIED.  Remaining in the agreement chain (ROADMAP): (iv) the
zpow-degree lemma (`loopDegreeQuotient` of an integer power of the
generator is the power of the degree, from the S267 additivity), and (v)
the agreement theorem `loopDegreeQuotient hp q = Multiplicative.toAdd (α
q)` by the free-cyclic argument (for `q`, `m := toAdd (α q)`,
`q = gen^m`, and the two group homs agree on the generator).  Tree green;
TWO documented sorries; no children pending.
-/

/-- **The period element of the deck group (VERIFIED)**: `deckP p` is the
translation of `zmultiples p` by one period — `⟨p, ·⟩` (the membership
witness is `1 • p = p`). -/
def deckP (p : ℝ) : zmultiples p := ⟨p, by
  rw [AddSubgroup.mem_zmultiples_iff]
  exact ⟨1, by simp⟩⟩

/-- **The period translation acts on the basepoint lift by addition
(VERIFIED)**: `(ofAdd (deckP p)) • (0 : ℝ) = p`. -/
lemma deck_smul_zero (p : ℝ) : (Multiplicative.ofAdd (deckP p)) • (0 : ℝ) = p := by
  simp [deckP]

/-- **`zmultiplesHom` sends `1` to the period element (VERIFIED)**: the
deck-group hom `ℤ →+ zmultiples p`, `n ↦ n • p`, evaluates at `1` to
`⟨p, ·⟩` (`one_zsmul`). -/
lemma zmultiplesHom_one (p : ℝ) :
    zmultiplesHom p 1 = ⟨p, by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨1, by simp⟩⟩ := by
  apply Subtype.ext
  simp [zmultiplesHom]

/-- **The deck identification sends the period element to `1` (VERIFIED)** —
item (ii) of the S263-iso agreement chain: under the deck-group
isomorphism `zmultiples p ≃+ ℤ` (S263, `zmultiplesEquivInt`), the
translation by one period corresponds to the integer `1` (the inverse
`(ofBijective (zmultiplesHom p))⁻¹` applied to `zmultiplesHom p 1` is `1`
by `Equiv.symm_apply_apply`, and `zmultiplesHom p 1 = deckP p`). -/
lemma zmultiplesEquivInt_p (p : ℝ) (hp : p ≠ 0) :
    zmultiplesEquivInt p hp ⟨p, by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨1, by simp⟩⟩ = 1 := by
  unfold zmultiplesEquivInt
  rw [← zmultiplesHom_one p]
  exact (AddEquiv.ofBijective (zmultiplesHom p) (⟨zmultiplesHom_injective p hp, zmultiplesHom_surjective p⟩)).symm_apply_apply 1

/-- **The monodromy hom of the generator is the period translation
(VERIFIED)**: the additive `fundamentalGroupToMulOpposite` of the
standard-loop class is `op (ofAdd (deckP p))` — the iff
`IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff`
reduces it to `(ofAdd (deckP p)) • 0 = monodromy (mk (standardLoop p))
⟨0, ·⟩`, closed by `deck_smul_zero` and the S269 monodromy. -/
lemma fgToMulOpposite_gen (p : ℝ) :
    (AddCircle.isAddQuotientCoveringMap_coe (𝕜 := ℝ) p).fundamentalGroupToMulOpposite
      (⟨0, by simp⟩ : (fun y : ℝ => (y : AddCircle p)) ⁻¹' {(0 : AddCircle p)})
      (Path.Homotopic.Quotient.mk (standardLoop p)) =
      MulOpposite.op (Multiplicative.ofAdd (deckP p)) := by
  rw [IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
  simp [deck_smul_zero p]
  rw [monodromy_standardLoop p]

/-- **The S263 iso decomposes into its three steps (VERIFIED)**: for every
`q`, `fundamentalGroupAddCircle_isoZ p hp q` equals the composition of the
additive fundamentalGroupEquiv (`π₁ → (Multiplicative (zmultiples p))ᵐᵒᵖ`),
`MulEquiv.op (AddEquiv.toMultiplicative (zmultiplesEquivInt p hp))` and
`mulOppositeIntEquiv` (unfold the S263 def + `MulEquiv.trans_apply` /
`MulEquiv.op_apply_apply`). -/
lemma isoZ_eq_comp (p : ℝ) (hp : p ≠ 0) (q : FundamentalGroup (AddCircle p) (0 : AddCircle p)) :
    fundamentalGroupAddCircle_isoZ p hp q =
      mulOppositeIntEquiv
        (MulEquiv.op (AddEquiv.toMultiplicative (zmultiplesEquivInt p hp))
          ((AddCircle.isAddQuotientCoveringMap_coe (𝕜 := ℝ) p).fundamentalGroupEquiv
            (⟨0, by simp⟩ : (fun y : ℝ => (y : AddCircle p)) ⁻¹' {(0 : AddCircle p)}) q)) := by
  unfold fundamentalGroupAddCircle_isoZ
  simp [MulEquiv.trans_apply, MulEquiv.op_apply_apply]

/-- **The S263 iso sends the generator loop to the generator of ℤ
(VERIFIED)** — item (iii) of the agreement chain: for `p ≠ 0`,
`fundamentalGroupAddCircle_isoZ p hp (mk (standardLoop p)) =
Multiplicative.ofAdd (1 : ℤ)` — the standard loop (one circuit, degree 1)
is mapped to the generator `ofAdd 1` of the multiplicative ℤ.  Proof:
decompose the iso (`isoZ_eq_comp`); the fundamentalGroupEquiv step sends
the generator to `op (ofAdd (deckP p))` (`fgToMulOpposite_gen`); the deck
identification (`zmultiplesEquivInt_p`) transports `ofAdd (deckP p)` to
`ofAdd 1` through `AddEquiv.toMultiplicative`; and `mulOppositeIntEquiv`
(unop) closes. -/
theorem isoZ_gen {p : ℝ} (hp : p ≠ 0) :
    fundamentalGroupAddCircle_isoZ p hp (Path.Homotopic.Quotient.mk (standardLoop p)) =
      Multiplicative.ofAdd (1 : ℤ) := by
  rw [isoZ_eq_comp p hp]
  have h1g : (AddCircle.isAddQuotientCoveringMap_coe (𝕜 := ℝ) p).fundamentalGroupEquiv
      (⟨0, by simp⟩ : (fun y : ℝ => (y : AddCircle p)) ⁻¹' {(0 : AddCircle p)})
      (Path.Homotopic.Quotient.mk (standardLoop p)) = MulOpposite.op (Multiplicative.ofAdd (deckP p)) := by
    exact fgToMulOpposite_gen p
  have hm : (AddEquiv.toMultiplicative (zmultiplesEquivInt p hp)) (Multiplicative.ofAdd (deckP p)) =
      Multiplicative.ofAdd (1 : ℤ) := by
    unfold AddEquiv.toMultiplicative
    simp [deckP, zmultiplesEquivInt_p p hp]
    exact congrArg Multiplicative.ofAdd (zmultiplesEquivInt_p p hp)
  simp [h1g, hm, MulEquiv.op_apply_apply, mulOppositeIntEquiv]
  rfl


/-! ## S271 — item (iv): the zpow-degree lemma (VERIFIED, sorry-free)

Extending the S267 additivity along the group multiplication gives the
bridge needed for the free-cyclic agreement argument: the degree of an
integer power is the power of the degree.

* **`genElem`** — the generator class `mk (standardLoop p)` as a
  `FundamentalGroup` element;
* **`loopDegreeQuotient_mul`** — the degree is additive over the GROUP
  multiplication: `deg (a * b) = deg a + deg b` (the FundamentalGroup
  product is the reversed trans, `mul_def`; quotient induction on `a`, `b`
  (`Path.Homotopic.Quotient.ind`) reduces to `mk (δ.trans γ)`, then
  `mk_trans` + the S267 `loopDegreePath_trans`; ℤ is commutative so the
  reversed order is immaterial);
* **`loopDegreeQuotient_one`** — the degree of the identity is `0` (from
  additivity: `deg 1 = deg (1 * 1) = deg 1 + deg 1`);
* **`degreeHom`** — the degree as a GROUP HOMOMORPHISM
  `FundamentalGroup (AddCircle p) 0 →* Multiplicative ℤ`,
  `q ↦ ofAdd (deg q)` (`map_one'` from `loopDegreeQuotient_one`,
  `map_mul'` from `loopDegreeQuotient_mul`);
* **`loopDegreeQuotient_zpow`** — the general zpow-degree lemma:
  `deg (q ^ n) = n • deg q` for every `n : ℤ` (`MonoidHom.map_zpow` for
  `degreeHom`, `congrArg Multiplicative.toAdd`, `toAdd_zpow` on ℤ);
* **`loopDegreeQuotient_gen_zpow`** — **item (iv)**: the degree of an
  integer power of the generator is the power:
  `loopDegreeQuotient hp (genElem p ^ n) = n` (the zpow lemma + S268
  `deg (genElem p) = 1`).

STATUS after S271: item (iv) is VERIFIED — the degree is compatible with
integer powers.  The agreement chain is complete except the final
assembly (v): `loopDegreeQuotient hp q = Multiplicative.toAdd (α q)` for
every `q`, by the free-cyclic argument: with `m := toAdd (α q)`,
`q = α⁻¹ (ofAdd m) = genElem^m` (α an iso with `α genElem = ofAdd 1`,
S270), and `deg (genElem^m) = m` (item (iv), S271).  Tree green; TWO
documented sorries; no children pending.
-/

/-- **The generator class as a `FundamentalGroup` element (VERIFIED)**:
the homotopy class of the standard loop of `AddCircle p`. -/
def genElem (p : ℝ) : FundamentalGroup (AddCircle p) (0 : AddCircle p) :=
  Path.Homotopic.Quotient.mk (standardLoop p)

/-- **The degree is additive over the group multiplication (VERIFIED)**:
for the fundamental group of `AddCircle p` (`mul` = reversed `trans`,
`FundamentalGroup.mul_def`), `deg (a * b) = deg a + deg b`.  Proof:
quotient induction on `a`, `b` (`Path.Homotopic.Quotient.ind`); the
product of `mk γ`, `mk δ` is `mk (δ.trans γ)` (`mul_def` + `mk_trans`);
`loopDegreeQuotient_mk` and the S267 `loopDegreePath_trans` give
`deg δ + deg γ`; ℤ is commutative. -/
lemma loopDegreeQuotient_mul {p : ℝ} (hp : p ≠ 0)
    (a b : FundamentalGroup (AddCircle p) (0 : AddCircle p)) :
    loopDegreeQuotient hp (a * b) = loopDegreeQuotient hp a + loopDegreeQuotient hp b := by
  rw [FundamentalGroup.mul_def]
  induction a using Path.Homotopic.Quotient.ind with
  | mk γ =>
      induction b using Path.Homotopic.Quotient.ind with
      | mk δ =>
          rw [← Path.Homotopic.Quotient.mk_trans]
          rw [loopDegreeQuotient_mk]
          rw [loopDegreePath_trans hp δ γ]
          rw [← loopDegreeQuotient_mk hp δ, ← loopDegreeQuotient_mk hp γ]
          exact add_comm _ _

/-- **The degree of the identity is `0` (VERIFIED)**: from the additivity
`deg 1 = deg (1 * 1) = deg 1 + deg 1` (ℤ is torsion-free). -/
lemma loopDegreeQuotient_one {p : ℝ} (hp : p ≠ 0) :
    loopDegreeQuotient hp (1 : FundamentalGroup (AddCircle p) (0 : AddCircle p)) = 0 := by
  have h := loopDegreeQuotient_mul hp (1 : FundamentalGroup (AddCircle p) (0 : AddCircle p))
    (1 : FundamentalGroup (AddCircle p) (0 : AddCircle p))
  rw [one_mul] at h
  omega

/-- **The degree as a group homomorphism (VERIFIED)**: `q ↦ ofAdd (deg q)`
is a `MonoidHom` from the fundamental group of `AddCircle p` to the
multiplicative integers (where multiplication is integer addition) —
`map_one'` from `loopDegreeQuotient_one`, `map_mul'` from
`loopDegreeQuotient_mul`. -/
noncomputable def degreeHom {p : ℝ} (hp : p ≠ 0) :
    FundamentalGroup (AddCircle p) (0 : AddCircle p) →* Multiplicative ℤ where
  toFun := fun q => Multiplicative.ofAdd (loopDegreeQuotient hp q)
  map_one' := by
    change Multiplicative.ofAdd (loopDegreeQuotient hp
      (1 : FundamentalGroup (AddCircle p) (0 : AddCircle p))) = 1
    rw [loopDegreeQuotient_one hp]
    simp
  map_mul' := by
    intro a b
    rw [loopDegreeQuotient_mul hp a b]
    rfl

/-- **The zpow-degree lemma (VERIFIED)**: for every `n : ℤ`,
`loopDegreeQuotient hp (q ^ n) = n • loopDegreeQuotient hp q` — the degree
is compatible with integer powers (`MonoidHom.map_zpow` for `degreeHom`,
then `congrArg Multiplicative.toAdd` and `toAdd_zpow` on ℤ). -/
lemma loopDegreeQuotient_zpow {p : ℝ} (hp : p ≠ 0)
    (q : FundamentalGroup (AddCircle p) (0 : AddCircle p)) (n : ℤ) :
    loopDegreeQuotient hp (q ^ n) = n • loopDegreeQuotient hp q := by
  have hz := MonoidHom.map_zpow (degreeHom hp) q n
  have hq := congrArg (fun z : Multiplicative ℤ => Multiplicative.toAdd z) hz
  rw [toAdd_zpow] at hq
  simpa [degreeHom, zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hq

/-- **Item (iv): the degree of an integer power of the generator is the
power (VERIFIED)**: `loopDegreeQuotient hp (genElem p ^ n) = n` for every
`n : ℤ` (the zpow-degree lemma + S268 `deg (genElem p) = 1`). -/
theorem loopDegreeQuotient_gen_zpow {p : ℝ} (hp : p ≠ 0) (n : ℤ) :
    loopDegreeQuotient hp (genElem p ^ n) = n := by
  rw [loopDegreeQuotient_zpow hp (genElem p) n]
  have hg : loopDegreeQuotient hp (genElem p) = 1 := by
    dsimp [genElem]
    rw [loopDegreeQuotient_mk]
    exact standardLoop_degreePath p hp
  rw [hg]
  simp


/-! ## S272 — the agreement theorem: `loopDegreeQuotient` IS the S263 iso
(VERIFIED, sorry-free) — item (v), the final assembly of the quadrant

With items (i)–(iv) verified — the monodromy of the generator (S269), the
deck identification (S270), the S263-iso value on the generator
`α (genElem p) = ofAdd 1` (S270), the degree of the generator
`deg (genElem p) = 1` (S268), and the zpow-degree lemma
`deg (q ^ n) = n • deg q` (S271) — the analytic degree invariant and the
topological fundamental-group isomorphism agree:

* **`loopDegreeQuotient_eq_isoZ`** — for every element `q` of
  `π₁(AddCircle p)`,
  `loopDegreeQuotient hp q = Multiplicative.toAdd (α q)` where
  `α := fundamentalGroupAddCircle_isoZ p hp` is the S263 iso.  Proof (the
  free-cyclic argument): let `m := toAdd (α q)`; then `ofAdd m = α q`, so
  `q = α.symm (α q) = α.symm (ofAdd m)`; since `α` is an isomorphism and
  `ofAdd m = (ofAdd 1) ^ m` (`ofAdd_zsmul`), the hom `α.symm` gives
  `q = (α.symm (ofAdd 1)) ^ m`; `α.symm (ofAdd 1) = genElem p` (S270:
  `α (genElem p) = ofAdd 1`); hence `q = (genElem p) ^ m`, and the
  zpow-degree lemma (S271) gives
  `deg q = deg (genElem p ^ m) = m = toAdd (α q)`.

STATUS after S272: the S269–S272 chain is COMPLETE — `loopDegreeQuotient`
(the concrete winding/degree invariant) is exactly the S263 isomorphism
`π₁(AddCircle p) ≃* ℤ` transported through `Multiplicative.toAdd`.  The
winding route's circle quadrant is closed: the fundamental group of the
parameter circle is the integers, computably realized by the loop degree.
Next route steps (ROADMAP): the winding API on the Möbius band
(`OpenMobiusCoreRetract`, `π₁(M) ≅ ℤ`, the embedded-circle classification
once/twice).  Tree green; TWO documented sorries; no children pending.
-/

/-- **The agreement theorem (VERIFIED)**: the concrete loop degree
(`loopDegreeQuotient`) equals the S263 isomorphism transported through
`Multiplicative.toAdd` — for every `q` in `π₁(AddCircle p)`,
`loopDegreeQuotient hp q = Multiplicative.toAdd
(fundamentalGroupAddCircle_isoZ p hp q)`.  Proof (the free-cyclic
argument): with `m := toAdd (α q)` (`α := fundamentalGroupAddCircle_isoZ
p hp`), `ofAdd m = α q`, so `q = α.symm (α q) = α.symm (ofAdd m)`; `α` is
an isomorphism and `ofAdd m = (ofAdd 1) ^ m` (`ofAdd_zsmul`), so the hom
`α.symm` (via `MulEquiv.toMonoidHom`) gives
`q = (α.symm (ofAdd 1)) ^ m`; `α.symm (ofAdd 1) = genElem p` (S270:
`α (genElem p) = ofAdd 1`); hence `q = (genElem p) ^ m`, and the
zpow-degree lemma (S271) gives `deg q = m`. -/
theorem loopDegreeQuotient_eq_isoZ {p : ℝ} (hp : p ≠ 0)
    (q : FundamentalGroup (AddCircle p) (0 : AddCircle p)) :
    loopDegreeQuotient hp q = Multiplicative.toAdd (fundamentalGroupAddCircle_isoZ p hp q) := by
  let α : FundamentalGroup (AddCircle p) (0 : AddCircle p) ≃* Multiplicative ℤ :=
    fundamentalGroupAddCircle_isoZ p hp
  let m : ℤ := Multiplicative.toAdd (α q)
  have hm : Multiplicative.ofAdd m = α q := by
    dsimp [m]
  have hgen : α.symm (Multiplicative.ofAdd (1 : ℤ)) = genElem p := by
    calc
      α.symm (Multiplicative.ofAdd (1 : ℤ)) = α.symm (α (genElem p)) :=
        congrArg α.symm (isoZ_gen (p := p) (hp := hp)).symm
      _ = genElem p := MulEquiv.symm_apply_apply α (genElem p)
  have hq : q = genElem p ^ m := by
    calc
      q = α.symm (α q) := by rw [MulEquiv.symm_apply_apply]
      _ = α.symm (Multiplicative.ofAdd m) := by rw [hm]
      _ = genElem p ^ m := by
        calc
          α.symm (Multiplicative.ofAdd m) =
              α.symm ((Multiplicative.ofAdd (1 : ℤ)) ^ m) := by
            congr 1
            simpa using (ofAdd_zsmul m (1 : ℤ))
          _ = (α.symm (Multiplicative.ofAdd (1 : ℤ))) ^ m := by
            exact (α.symm.toMonoidHom).map_zpow (Multiplicative.ofAdd (1 : ℤ)) m
          _ = genElem p ^ m := by rw [hgen]
  have hdeg : loopDegreeQuotient hp q = m := by
    rw [hq]
    rw [loopDegreeQuotient_gen_zpow hp m]
  rw [hdeg]


/-! ## S273 — the core-retraction transport along a homeomorphism
(VERIFIED, sorry-free) — the mechanical bridge for `OpenMobiusCoreRetract`

The target statement `OpenMobiusCoreRetract` (route step 2, declared above)
and the plane-chord model retraction `MobiusModel.mobius_core_retract`
(`MobiusCoreRetract`, verified in Submission/MobiusModel.lean) are the two
ends of the deformation-retraction story: the abstract Möbius band of
secants `OpenMobius` is homeomorphic to the plane chord model
(`OpenMobius ≃ₜ MobiusModel` — the composition of `CirclePairs`'s
`openMobiusCircleEquiv : OpenMobius ≃ₜ CircleOpenPairs` with the
two-point→chord-line homeo to the flip quotient, the missing plane-model
link).  This section supplies the generic transport that carries any core
deformation retraction across a homeomorphism:

* **`coreRetract_transport`** — if `ρY` is a continuous deformation
  retraction of `Y` onto `Set.range coreY` (`ρY (y,0) = y`,
  `ρY (y,1) ∈ range coreY`, fixing `coreY` pointwise), then for any
  homeomorphism `φ : X ≃ₜ Y` the conjugate
  `ρ (x, t) = φ.symm (ρY (φ x, t))` is a continuous deformation retraction
  of `X` onto `Set.range (fun a => φ.symm (coreY a))` (the transported
  core), fixing the transported core pointwise.  Proof: continuity by
  composition (`φ.symm.continuous.comp ((φ.continuous.comp continuous_fst)
  .prodMk continuous_snd).comp`-shaped), and the three pointwise
  properties by the homomorphism laws (`φ.symm_apply_apply`,
  `φ.apply_symm_apply`).

STATUS after S273: the retraction-transport bridge is verified; applying it
to `MobiusModel.mobius_core_retract` through the (to-be-built) homeo
`OpenMobius ≃ₜ MobiusModel` will deliver `OpenMobiusCoreRetract` with core
`range coreFactor`.  Next: the plane-model link (the homeo between the
pair-quotient model and `MobiusModel`/`ChordData`-flip quotient — the
two-point→chord map `{a,b} ↦ (n, d)` with `n` the chord normal and
`d ∈ (−1,1)`, a geometric chapter in its own right).  Tree green; TWO
documented sorries; no children pending.
-/

/-- **The core-retraction transport along a homeomorphism (VERIFIED)**: if
`ρY` is a continuous deformation retraction of `Y` onto
`Set.range coreY` (`ρY (y, 0) = y`, `ρY (y, 1) ∈ range coreY`, fixing
`coreY a` pointwise), then for any homeomorphism `φ : X ≃ₜ Y` the
conjugate `ρ (x, t) := φ.symm (ρY (φ x, t))` is a continuous deformation
retraction of `X` onto the transported core `Set.range (fun a => φ.symm
(coreY a))`, fixing the transported core pointwise.  This is the
mechanical bridge that carries the model retraction
(`MobiusModel.mobius_core_retract`) to the abstract band
(`OpenMobiusCoreRetract`) once the homeomorphism `OpenMobius ≃ₜ
MobiusModel` is established. -/
theorem coreRetract_transport {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) {A : Type*} {coreY : A → Y}
    {ρY : Y × Set.Icc (0 : ℝ) 1 → Y}
    (hρc : Continuous ρY)
    (hρ0 : ∀ y : Y, ρY (y, ⟨(0 : ℝ), by norm_num⟩) = y)
    (hρ1 : ∀ y : Y, ρY (y, ⟨(1 : ℝ), by norm_num⟩) ∈ Set.range coreY)
    (hfix : ∀ (a : A) (t : Set.Icc (0 : ℝ) 1), ρY (coreY a, t) = coreY a) :
    ∃ ρ : X × Set.Icc (0 : ℝ) 1 → X,
      Continuous ρ ∧
      (∀ x : X, ρ (x, ⟨(0 : ℝ), by norm_num⟩) = x) ∧
      (∀ x : X, ρ (x, ⟨(1 : ℝ), by norm_num⟩) ∈ Set.range (fun a : A => φ.symm (coreY a))) ∧
      (∀ (a : A) (t : Set.Icc (0 : ℝ) 1), ρ (φ.symm (coreY a), t) = φ.symm (coreY a)) := by
  let ρ : X × Set.Icc (0 : ℝ) 1 → X := fun z => φ.symm (ρY (φ z.1, z.2))
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · -- continuity: φ.symm ∘ ρY ∘ (φ × id)
    exact (φ.symm.continuous.comp (hρc.comp ((φ.continuous.comp continuous_fst).prodMk continuous_snd)))
  · intro x
    change φ.symm (ρY (φ x, (⟨(0 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1))) = x
    rw [hρ0 (φ x)]
    exact φ.symm_apply_apply x
  · intro x
    change φ.symm (ρY (φ x, (⟨(1 : ℝ), by norm_num⟩ : Set.Icc (0 : ℝ) 1))) ∈
      Set.range (fun a : A => φ.symm (coreY a))
    rcases hρ1 (φ x) with ⟨a, ha⟩
    rw [ha.symm]
    exact ⟨a, rfl⟩
  · intro a t
    change φ.symm (ρY (φ (φ.symm (coreY a)), t)) = φ.symm (coreY a)
    rw [φ.apply_symm_apply (coreY a)]
    rw [hfix a t]

end LeanEval.KnotTheory.Quadrisecant
