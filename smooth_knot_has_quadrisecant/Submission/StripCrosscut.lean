import Mathlib
import ChallengeDeps
import Submission.BandArcCover
import Submission.TrisecantLocus

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-!
# Brick (d) — the strip crosscut interface (VERIFIED, sorry-free)
(Submission/StripCrosscut.lean)

**What this module does.**  Brick (d) (`NonSeparatingArcAvoidingO r`,
`Submission/BandArcCover.lean`) is the last purely *two-dimensional* step of
the contrapositive argument: a quadrisecant-free knot in general position
carries a non-separating band arc avoiding the trisecant set `O`.  Kuperberg's
§3 reduces it to "`O` obstructs some non-separating arc ⟹ a circular
component of `O` winds", which the winding measurement (S279/S280) refutes.

This module fixes the **exact interface** between the trisecant geometry and
the two-dimensional separation statement, so that the latter can be proved in
the commons, on the universal cover of the band, with no reference to knots:

* `stripSecantClass r p` — the secant class attached to a point
  `p = (x, y)` of the strip `ℝ × (0, period)`, namely the class of the unordered
  pair of knot points `{K x, K (x + y)}` (the chord of *parameter length*
  `y` starting at `x`).  The strip is the universal cover of the Möbius band
  of secants `M = OpenMobius` in the coordinates `(x, y) ↦ {K x, K (x+y)}`:
  the two edges `{y = 0}` and `{y = period}` both project to the diagonal
  `∂M`, and a *non-separating* band arc is exactly a path from the bottom edge
  to the top edge.
* `liftedTrisecant r ⊆ ℝ × ℝ` — the preimage of Kuperberg's `O` under that
  covering: the set of strip points whose secant class is a trisecant.
* **`bandArcData_of_stripCrosscut`** — THE REDUCTION: a continuous path
  `γ : I → ℝ × ℝ` from the bottom edge to the top edge (`(γ 0).2 = 0`,
  `(γ 1).2 = period`), whose interior stays in the open strip and avoids
  `liftedTrisecant r`, *is* a non-separating band arc avoiding `O` — i.e. it
  produces a `BandArcData` with `BandArcNonSeparating` and the
  `trisecantSet`-avoidance property.  The two branches are
  `a s = (γ s).1` and `b s = (γ s).1 + (γ s).2`, collapsed at the two ends
  because the parameter length is `0` resp. `period` there; the real lifts
  `ta s = (γ s).1`, `tb s = (γ s).1 + (γ s).2` exhibit the non-separating
  winding `tb 1 = ta 1 + period` verbatim.
* `StripCrosscutAvoidingO r` (a `def Prop`, no `sorry`) — the residual
  two-dimensional statement, and
  **`nonSeparatingArcAvoidingO_of_stripCrosscut`**: it implies
  `NonSeparatingArcAvoidingO r`.

The companion commons lemma (delegated) is
`Commons.Topology.Strip.strip_crosscut_of_bounded_components`: for a closed
(locally closed) `F ⊆ ℝ × (0, period)` whose connected components are bounded
in the `x`-direction and which meets each vertical line finitely, a crosscut
from the bottom edge to the top edge avoiding `F` exists.  Applied to
`F = liftedTrisecant r` it closes brick (d).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-! ## 1. Strip coordinates on the band of secants -/

/-- **Distinctness of the two endpoints of a strip chord (VERIFIED)**: if the
parameter length `y` lies strictly between `0` and the period `period`, then
the two parameter classes `x` and `x + y` differ. -/
lemma coe_ne_coe_of_lt {x y : ℝ} (hy0 : 0 < y) (hy1 : y < period) :
    ((x : AddCircle period)) ≠ (((x + y : ℝ)) : AddCircle period) := by
  intro h
  have hmem : (x + y) - x ∈ AddSubgroup.zmultiples period :=
    (QuotientAddGroup.eq_iff_sub_mem).mp h.symm
  have hsub : (x + y) - x = y := by ring
  rw [hsub] at hmem
  rcases (AddSubgroup.mem_zmultiples_iff.mp hmem) with ⟨n, hn⟩
  rw [zsmul_eq_mul] at hn
  have hp0 : (0 : ℝ) < (n : ℝ) * period := by rw [hn]; exact hy0
  have hp1 : (n : ℝ) * period < period := by rw [hn]; exact hy1
  have h0 : (0 : ℝ) < (n : ℝ) := by nlinarith [period_pos, hp0]
  have h1 : (n : ℝ) < 1 := by nlinarith [period_pos, hp1]
  have hz : (0 : ℤ) < n := by exact_mod_cast h0
  have ho : n < 1 := by exact_mod_cast h1
  omega

/-- **The secant class of a strip point (VERIFIED def)**: for a point
`(x, y)` of the strip with `0 < y < period`, the unordered pair of knot
parameters `{x, x + y}` — a point of the open Möbius band of secants.  This is
the covering map `ℝ × (0, period) → OpenMobius` of the universal cover of the
band, in the coordinates in which the two boundary edges are `y = 0` and
`y = period`. -/
def stripSecantClass (p : ℝ × ℝ) (h0 : 0 < p.2)
    (h1 : p.2 < period) : OpenMobius :=
  mobiusCover ⟨((p.1 : AddCircle period),
    (((p.1 + p.2 : ℝ)) : AddCircle period)), coe_ne_coe_of_lt h0 h1⟩

/-- **The lifted trisecant locus (VERIFIED def)**: the preimage in the strip of
Kuperberg's `O = trisecantSet r` under the covering `stripSecantClass`. -/
def liftedTrisecant (r : ℝ → Space) : Set (ℝ × ℝ) :=
  {p | ∃ h0 : 0 < p.2, ∃ h1 : p.2 < period,
    stripSecantClass p h0 h1 ∈ trisecantSet r}

/-- **The deck generator of the strip cover (VERIFIED def)**: in the strip
coordinates `(x, y) ↦ {K x, K (x+y)}` the two points `(x, y)` and
`(x + y, period − y)` describe the *same* unordered pair of parameters, hence
the same secant class; `stripFlip` is the generator `σ` of the deck group
`ℤ = π₁(M)` of the universal cover `ℝ × (0, period) → OpenMobius` (its square
is the translation `(x, y) ↦ (x + period, y)`). -/
def stripFlip (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + p.2, period - p.2)

lemma stripFlip_fst (p : ℝ × ℝ) : (stripFlip p).1 = p.1 + p.2 := rfl
lemma stripFlip_snd (p : ℝ × ℝ) : (stripFlip p).2 = period - p.2 := rfl

/-- `stripFlip` squared is the translation by one period in the `x` coordinate
(the fundamental deck transformation of the double cover of the band). -/
lemma stripFlip_stripFlip (p : ℝ × ℝ) :
    stripFlip (stripFlip p) = (p.1 + period, p.2) := by
  simp only [stripFlip, Prod.mk.injEq]
  constructor <;> ring

/-- **The ordered pair of strip parameters (VERIFIED def)**: the element of the
double cover `OrderedPairs` underlying `stripSecantClass p`. -/
def stripPair (p : ℝ × ℝ) (h0 : 0 < p.2) (h1 : p.2 < period) : OrderedPairs :=
  ⟨((p.1 : AddCircle period), (((p.1 + p.2 : ℝ)) : AddCircle period)),
    coe_ne_coe_of_lt h0 h1⟩

lemma stripSecantClass_eq_mobiusCover (p : ℝ × ℝ) (h0 : 0 < p.2) (h1 : p.2 < period) :
    stripSecantClass p h0 h1 = mobiusCover (stripPair p h0 h1) := rfl

/-- `mobiusCover` is invariant under swapping the two endpoints. -/
lemma mobiusCover_swapOrdered (p : OrderedPairs) :
    mobiusCover (swapOrdered p) = mobiusCover p := by
  apply Subtype.ext
  change unordOfOrdered (swapOrdered p) = unordOfOrdered p
  rw [unordOfOrdered_eq_iff]
  exact Or.inr (swapOrdered_involutive p)

/-- **The ordered pair of a strip point and of its deck image are swapped
(VERIFIED)**: `stripPair (stripFlip p)` is the endpoint-swap of `stripPair p`
— both describe the same unordered pair `{x, x + y}` of parameters. -/
lemma stripPair_stripFlip {p : ℝ × ℝ} (h0 : 0 < p.2) (h1 : p.2 < period)
    (k0 : 0 < (stripFlip p).2) (k1 : (stripFlip p).2 < period) :
    stripPair (stripFlip p) k0 k1 = swapOrdered (stripPair p h0 h1) := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · rfl
  · show ((((stripFlip p).1 + (stripFlip p).2 : ℝ)) : AddCircle period)
      = ((p.1 : ℝ) : AddCircle period)
    rw [stripFlip_fst, stripFlip_snd,
      show p.1 + p.2 + (period - p.2) = p.1 + period from by ring,
      AddCircle.coe_add, AddCircle.coe_period, add_zero]

/-- **The secant class is invariant under the deck generator (VERIFIED)**: the
strip points `(x, y)` and `(x + y, period − y)` carry the same secant class
`{x, x + y}` of the band. -/
lemma stripSecantClass_stripFlip {p : ℝ × ℝ} (h0 : 0 < p.2) (h1 : p.2 < period)
    (k0 : 0 < (stripFlip p).2) (k1 : (stripFlip p).2 < period) :
    stripSecantClass (stripFlip p) k0 k1 = stripSecantClass p h0 h1 := by
  rw [stripSecantClass_eq_mobiusCover (stripFlip p) k0 k1,
    stripSecantClass_eq_mobiusCover p h0 h1,
    stripPair_stripFlip h0 h1 k0 k1, mobiusCover_swapOrdered]

/-- **`liftedTrisecant` is invariant under the deck generator (VERIFIED)**: a
strip point carries a trisecant secant class iff its `stripFlip` image does —
the lift of `O` to the universal cover of the band is invariant under the deck
group `ℤ = π₁(M)`. -/
lemma stripFlip_mem_liftedTrisecant {r : ℝ → Space} {p : ℝ × ℝ} :
    stripFlip p ∈ liftedTrisecant r ↔ p ∈ liftedTrisecant r := by
  constructor
  · rintro ⟨h0, h1, hmem⟩
    have k0 : 0 < p.2 := by
      rw [stripFlip_snd] at h1
      linarith
    have k1 : p.2 < period := by
      rw [stripFlip_snd] at h0
      linarith
    exact ⟨k0, k1, by rwa [stripSecantClass_stripFlip k0 k1 h0 h1] at hmem⟩
  · rintro ⟨k0, k1, hmem⟩
    have h0 : 0 < (stripFlip p).2 := by
      rw [stripFlip_snd]; linarith
    have h1 : (stripFlip p).2 < period := by
      rw [stripFlip_snd]; linarith
    exact ⟨h0, h1, by rw [stripSecantClass_stripFlip k0 k1 h0 h1]; exact hmem⟩

lemma mem_liftedTrisecant_iff {r : ℝ → Space} {p : ℝ × ℝ} :
    p ∈ liftedTrisecant r ↔ ∃ h0 : 0 < p.2, ∃ h1 : p.2 < period,
      stripSecantClass p h0 h1 ∈ trisecantSet r := Iff.rfl

/-- Membership of `liftedTrisecant` does not depend on the distinctness
witnesses. -/
lemma stripSecantClass_congr {p : ℝ × ℝ} (h0 h0' : 0 < p.2)
    (h1 h1' : p.2 < period) :
    stripSecantClass p h0 h1 = stripSecantClass p h0' h1' := by
  unfold stripSecantClass
  exact congrArg mobiusCover (Subtype.ext rfl)

/-! ## 1b. Continuity and the closedness transport -/

/-- **The strip covering map is continuous (VERIFIED)**: the secant class of a
strip point depends continuously on the point, on the strip type
`{q : ℝ × ℝ // 0 < q.2 ∧ q.2 < period}`. -/
lemma continuous_stripSecantClass :
    Continuous fun p : {q : ℝ × ℝ // 0 < q.2 ∧ q.2 < period} =>
      stripSecantClass p.1 p.2.1 p.2.2 := by
  unfold stripSecantClass
  refine continuous_mobiusCover.comp (Continuous.subtype_mk ?_ _)
  refine ((AddCircle.continuous_mk' period).comp
    (continuous_fst.comp continuous_subtype_val)).prodMk ?_
  exact (AddCircle.continuous_mk' period).comp
    ((continuous_fst.comp continuous_subtype_val).add
      (continuous_snd.comp continuous_subtype_val))

/-- **Closedness transport (VERIFIED)**: if Kuperberg's trisecant set `O` is
closed in the band, then its lift to the universal cover is closed *in the
strip* (equivalently: it is a closed subset of the strip type; it need not be
closed in `ℝ²`, since `O` may accumulate at the diagonal, cf. ROADMAP S283c).
This is the `(hF)` half of the crosscut hypotheses. -/
lemma isClosed_liftedTrisecant_of_isClosed {r : ℝ → Space}
    (h : IsClosed (trisecantSet r)) :
    IsClosed {p : {q : ℝ × ℝ // 0 < q.2 ∧ q.2 < period} | p.1 ∈ liftedTrisecant r} := by
  have hpre : {p : {q : ℝ × ℝ // 0 < q.2 ∧ q.2 < period} | p.1 ∈ liftedTrisecant r}
      = (fun p : {q : ℝ × ℝ // 0 < q.2 ∧ q.2 < period} =>
          stripSecantClass p.1 p.2.1 p.2.2) ⁻¹' trisecantSet r := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [mem_liftedTrisecant_iff]
    constructor
    · rintro ⟨h0, h1, hm⟩
      rwa [stripSecantClass_congr h0 p.2.1 h1 p.2.2] at hm
    · intro hm
      exact ⟨p.2.1, p.2.2, hm⟩
  rw [hpre]
  exact h.preimage continuous_stripSecantClass

/-! ## 2. The reduction: a strip crosscut is a non-separating avoiding arc -/

/-- **Brick (d) reduced to the strip (THE REDUCTION, VERIFIED)**: a continuous
path in the closed strip from the bottom edge (`y = 0`) to the top edge
(`y = period`) whose interior stays in the open strip and avoids the lifted
trisecant locus is a non-separating band arc avoiding `O`.

The two branches of the arc are `a s = (γ s).1` (the starting parameter) and
`b s = (γ s).1 + (γ s).2` (the chord's other endpoint); at `s = 0` resp.
`s = 1` the parameter length is `0` resp. `period`, so the two branches
collapse there, and the real lifts `ta s = (γ s).1`,
`tb s = (γ s).1 + (γ s).2` exhibit `ta 0 = tb 0` and
`tb 1 = ta 1 + period` — the arc is *non-separating*. -/
theorem bandArcData_of_stripCrosscut {r : ℝ → Space}
    (γ : C(I, ℝ × ℝ)) (hbot : (γ 0).2 = 0) (htop : (γ 1).2 = period)
    (hint : ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).2 ∧ (γ t).2 < period)
    (havoid : ∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∉ liftedTrisecant r) :
    ∃ d : BandArcData, BandArcNonSeparating d ∧
      ∀ s : I, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
        mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉ trisecantSet r := by
  classical
  -- the two branches, as classes of parameters
  set a : I → AddCircle period := fun s => ((γ s).1 : AddCircle period) with ha
  set b : I → AddCircle period :=
    fun s => (((γ s).1 + (γ s).2 : ℝ) : AddCircle period) with hb
  have hcont_a : Continuous a :=
    (AddCircle.continuous_mk' period).comp (continuous_fst.comp γ.continuous)
  have hcont_b : Continuous b :=
    (AddCircle.continuous_mk' period).comp
      ((continuous_fst.comp γ.continuous).add (continuous_snd.comp γ.continuous))
  have hleft : a 0 = b 0 := by
    show ((γ 0).1 : AddCircle period) = (((γ 0).1 + (γ 0).2 : ℝ) : AddCircle period)
    rw [hbot]
    simp
  have hright : a 1 = b 1 := by
    show ((γ 1).1 : AddCircle period) = (((γ 1).1 + (γ 1).2 : ℝ) : AddCircle period)
    rw [htop, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hoff : ∀ s : I, (s : ℝ) ≠ 0 → (s : ℝ) ≠ 1 → a s ≠ b s := by
    intro s hs0 hs1
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
    have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
    have hh := hint s hpos hlt
    show ((γ s).1 : AddCircle period) ≠ (((γ s).1 + (γ s).2 : ℝ) : AddCircle period)
    exact coe_ne_coe_of_lt hh.1 hh.2
  let d : BandArcData :=
    { a := a, b := b, cont_a := hcont_a, cont_b := hcont_b,
      collapse_left := hleft, collapse_right := hright, offdiag := hoff }
  have hns : BandArcNonSeparating d := by
    refine ⟨fun s => (γ s).1, fun s => (γ s).1 + (γ s).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact continuous_fst.comp γ.continuous
    · exact (continuous_fst.comp γ.continuous).add (continuous_snd.comp γ.continuous)
    · intro s; rfl
    · intro s; rfl
    · show (γ 0).1 = (γ 0).1 + (γ 0).2
      rw [hbot]; ring
    · show (γ 1).1 + (γ 1).2 = (γ 1).1 + period
      rw [htop]
  refine ⟨d, hns, ?_⟩
  intro s hs0 hs1
  have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs0)
  have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 hs1
  have hh := hint s hpos hlt
  have hmem : ∀ (k0 : 0 < (γ s).2) (k1 : (γ s).2 < period),
      stripSecantClass (γ s) k0 k1 ∉ trisecantSet r :=
    fun k0 k1 hcon => havoid s hpos hlt ⟨k0, k1, hcon⟩
  -- identify the two secant classes
  have heq : mobiusCover ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩
      = stripSecantClass (γ s) hh.1 hh.2 := by
    unfold stripSecantClass
    exact congrArg mobiusCover (Subtype.ext rfl)
  rw [heq]
  exact hmem hh.1 hh.2

/-- **The residual two-dimensional statement of brick (d) (PIN, `def Prop`,
no `sorry`).**  A crosscut of the closed strip from the bottom edge `y = 0` to
the top edge `y = period` whose interior avoids the lifted trisecant locus
exists.  Equivalently (Kuperberg §3, given the winding measurement): a
non-separating band arc avoiding `O`. -/
def StripCrosscutAvoidingO (r : ℝ → Space) : Prop :=
  ∃ γ : C(I, ℝ × ℝ), (γ 0).2 = 0 ∧ (γ 1).2 = period ∧
    (∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).2 ∧ (γ t).2 < period) ∧
    (∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∉ liftedTrisecant r)

/-- **Brick (d) from the strip crosscut (VERIFIED)**: the residual strip
statement `StripCrosscutAvoidingO r` implies `NonSeparatingArcAvoidingO r`
(that is, it yields a `BandArcData` which is non-separating and avoids the
trisecant set at every interior parameter). -/
theorem nonSeparatingArcAvoidingO_of_stripCrosscut {r : ℝ → Space}
    (h : StripCrosscutAvoidingO r) : NonSeparatingArcAvoidingO r := by
  rcases h with ⟨γ, hbot, htop, hint, havoid⟩
  exact bandArcData_of_stripCrosscut γ hbot htop hint havoid

end LeanEval.KnotTheory.Quadrisecant
