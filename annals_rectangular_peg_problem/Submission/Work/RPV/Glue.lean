import Submission.Work.RPV.V
import Submission.Work.RPV.rect_of_tau_chord

/-!
# Rectangular peg: glue (`Work.RPV`)

This file contains the "G" block of the route design (`RECTPEG_ROUTE_LEAD.md` §4.2):
the node hypotheses of the design as `Prop`-valued definitions, the reduction
`main_rect_of_nodes` of the main rectangle-existence theorem to those nodes, and the final wiring
of the challenge `theorem_1` from the nodes.

The four node hypotheses are the statements of the route document's nodes:

* `CoreNode`          -- CORE: `Z ∩ τ_θ(Z)` meets any compactly supported Hamiltonian image;
* `CurveIsotopyNode`  -- B1: every smooth Jordan curve is an affine image of the end of a
  normalised curve isotopy from the unit circle;
* `LagFamilyNode`     -- B5: the Lagrangian family with its no-spurious-coincidence property;
* `LagIsotopyNode`    -- A3: a compactly supported Hamiltonian flow taking `Z` onto the end
  of a `LagFamily`;

and `Theorem1OfMainNode` is the G1/G2 reduction, proved in
`Submission.Work.RPV.theorem_1_of_main` (a colleague's module).

Each node is expected to be proved in its own module later (see the route document §4.4–4.6);
`main_rect_of_nodes` and `theorem_1_of_nodes` then assemble the challenge statement.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPV

/-! ## The node hypotheses of the route -/

/-- CORE (route §3.5): a compactly supported (mod `2π`) Hamiltonian diffeomorphism `Φ` moves the
zero section onto a set meeting `τ_θ Φ(Z)` for every `θ ∈ (0,π)`. -/
def CoreNode : Prop :=
  ∀ (Hh : CptPerHam) (Φ : ℝ → PS → PS), IsFlow Hh.H Φ →
    ∀ θ : ℝ, 0 < θ → θ < π → ∃ x ∈ Zsec, ∃ y ∈ Zsec, tau θ (Φ 1 x) = Φ 1 y

/-- B1 (route §4.5): every smooth Jordan curve is, up to a homothety and a translation, the end
of a normalised curve isotopy from the unit circle. -/
def CurveIsotopyNode : Prop :=
  ∀ (γ : Circle → ℂ), IsSmoothJordan γ → ∃ CI : CurveIsotopy, ∃ (lam : ℝ) (b : ℂ), 0 < lam ∧
    ∀ t, CI.c 1 t ∈ (fun z => (lam : ℂ) * z + b) '' Set.range γ

/-- B5 (route §4.5): from a normalised curve isotopy build the `τ_π`-symmetric Lagrangian family
`L̂`, with no spurious `τ_θ`-coincidences at `τ = 1` and with the `|x| < √2` part made of chords
of the end curve. -/
def LagFamilyNode : Prop :=
  ∀ CI : CurveIsotopy, ∃ L : LagFamily,
      (∀ θ : ℝ, 0 < θ → θ < π → ∀ x t x' t' (k : ℤ),
        L.ℓ 1 (x', t') = Tk k (tau θ (L.ℓ 1 (x, t))) → |x| < Real.sqrt 2 ∧ |x'| < Real.sqrt 2) ∧
      (∀ x t, |x| < Real.sqrt 2 → ∃ t₁ t₂ a : ℝ, CI.c 1 t₁ ≠ CI.c 1 t₂ ∧
        CI.c 1 t₁ - CI.c 1 t₂ = (‖CI.c 1 t₁ - CI.c 1 t₂‖ : ℂ) * Complex.exp (a * I) ∧
        L.ℓ 1 (x, t) = chordPS (CI.c 1 t₁) (CI.c 1 t₂) a)

/-- A3 (route §4.4): a `LagFamily` is induced by a compactly supported Hamiltonian flow, and at
`τ = 1` the zero section is carried onto the image of `ℓ 1`. -/
def LagIsotopyNode : Prop :=
  ∀ L : LagFamily, ∃ Hh : CptPerHam, ∃ Φ : ℝ → PS → PS, IsFlow Hh.H Φ ∧
      ∀ z ∈ Zsec, ∃ x t, Φ 1 z = L.ℓ 1 (x, t)

/-- G2/G1 as a hypothesis: the normalised `φ`-rectangle existence for `0 < φ < π`, i.e. the
statement of `Work.RPV.theorem_1_of_main` (`Submission.Work.RPV.theorem_1_of_main`). -/
def Theorem1OfMainNode : Prop :=
  ∀ (γ : Circle → ℂ), IsSmoothJordan γ →
    ∀ φ : ℝ, 0 < φ → φ < π → HasThetaRect (Set.range γ) φ

/-! ## G2: the main rectangle-existence theorem from the four geometric nodes -/

/-- **G2** (route §4.2).  The four geometric nodes imply that every smooth Jordan curve inscribes
a rectangle of every aspect ratio: for every `φ ∈ (0,π)` there are four points of `γ` spanning a
rectangle whose `φ`-diagonals satisfy the `HasThetaRect` normal form. -/
theorem main_rect_of_nodes (hC : CoreNode) (hB1 : CurveIsotopyNode) (hB5 : LagFamilyNode)
    (hA3 : LagIsotopyNode) (γ : Circle → ℂ) (hγ : IsSmoothJordan γ) (φ : ℝ) (h0 : 0 < φ)
    (h1 : φ < π) : HasThetaRect (Set.range γ) φ := by
  obtain ⟨CI, lam, b, hlam, hCI⟩ := hB1 γ hγ
  obtain ⟨L, hnsp, hchord⟩ := hB5 CI
  obtain ⟨Hh, Φ, hΦ, hΦL⟩ := hA3 L
  obtain ⟨x, hx, y, hy, hxy⟩ := hC Hh Φ hΦ φ h0 h1
  obtain ⟨x₁, t₁, hx₁⟩ := hΦL x hx
  obtain ⟨y₁, s₁, hy₁⟩ := hΦL y hy
  have hrel : L.ℓ 1 (y₁, s₁) = Tk 0 (tau φ (L.ℓ 1 (x₁, t₁))) := by
    rw [← hx₁, ← hy₁, ← hxy]; simp [Tk]
  obtain ⟨hxs, hys⟩ := hnsp φ h0 h1 x₁ t₁ y₁ s₁ 0 hrel
  obtain ⟨a₁, a₂, a, hne, ha, hcx⟩ := hchord x₁ t₁ hxs
  obtain ⟨b₁, b₂, b, hne', hb, hcy⟩ := hchord y₁ s₁ hys
  have hrel' : tau φ (chordPS (CI.c 1 a₁) (CI.c 1 a₂) a) =
      Tk 0 (chordPS (CI.c 1 b₁) (CI.c 1 b₂) b) := by
    rw [← hcx, ← hcy, hrel]; simp [Tk]
  obtain ⟨hsum, hdiff⟩ := rect_of_tau_chord hne hne' ha hb 0 hrel'
  obtain ⟨g₁, ⟨p₁, rfl⟩, hg₁⟩ := hCI a₁
  obtain ⟨g₂, ⟨p₂, rfl⟩, hg₂⟩ := hCI a₂
  obtain ⟨g₃, ⟨p₃, rfl⟩, hg₃⟩ := hCI b₁
  obtain ⟨g₄, ⟨p₄, rfl⟩, hg₄⟩ := hCI b₂
  simp only at hg₁ hg₂ hg₃ hg₄
  have hlam0 : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  refine ⟨γ p₁, ⟨p₁, rfl⟩, γ p₂, ⟨p₂, rfl⟩, γ p₃, ⟨p₃, rfl⟩, γ p₄, ⟨p₄, rfl⟩, ?_, ?_, ?_⟩
  · intro h; apply hne; rw [← hg₁, ← hg₂, h]
  · rw [← hg₁, ← hg₂, ← hg₃, ← hg₄] at hsum
    have : (lam : ℂ) * (γ p₁ + γ p₂) = (lam : ℂ) * (γ p₃ + γ p₄) := by linear_combination hsum
    exact mul_left_cancel₀ hlam0 this
  · rw [← hg₁, ← hg₂, ← hg₃, ← hg₄] at hdiff
    have : (lam : ℂ) * (γ p₃ - γ p₄) = (lam : ℂ) * (Complex.exp (φ * I) * (γ p₁ - γ p₂)) := by
      linear_combination hdiff
    exact mul_left_cancel₀ hlam0 this

/-! ## G1: the challenge from the nodes -/

/-- **Final wiring.**  The challenge statement (`theorem_1` of `Challenge.lean`) follows from the
four geometric nodes together with the G1 reduction `Theorem1OfMainNode`.  The four nodes are
`CoreNode`, `CurveIsotopyNode`, `LagFamilyNode`, `LagIsotopyNode` (each expected to be proved in
its own module later), and the G1 reduction is supplied by `Work.RPV.theorem_1_of_main`, whose
type is exactly the `hG1` argument below.  Hence, once all node theorems are available,

`Work.RPV.theorem_1_of_nodes hC hB1 hB5 hA3 Work.RPV.theorem_1_of_main γ z w θ hγ`

is (definitionally) the challenge statement. -/
theorem theorem_1_of_nodes
    (hG1 : Theorem1OfMainNode →
      ∀ (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle), IsSmoothJordan γ →
        ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ),
          Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') ∧
          ∀ i : Fin 4, RectangularPegProblem.R z' w' θ' i ∈ Set.range γ)
    (hC : CoreNode) (hB1 : CurveIsotopyNode) (hB5 : LagFamilyNode) (hA3 : LagIsotopyNode) :
    ∀ (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle), IsSmoothJordan γ →
      ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ),
        Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') ∧
        ∀ i : Fin 4, RectangularPegProblem.R z' w' θ' i ∈ Set.range γ :=
  hG1 (main_rect_of_nodes hC hB1 hB5 hA3)

/-- Check that the wiring above produces the challenge's **conclusion with the challenge's own
hypothesis** `IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ`: `IsSmoothJordan` is definitionally that
hypothesis, so a proof of the challenge is literally
`theorem_1_of_nodes Work.RPV.theorem_1_of_main hC hB1 hB5 hA3 γ z w θ hγ`. -/
example (hG1 : Theorem1OfMainNode →
        ∀ (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle), IsSmoothJordan γ →
          ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ),
            Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') ∧
            ∀ i : Fin 4, RectangularPegProblem.R z' w' θ' i ∈ Set.range γ)
    (hC : CoreNode) (hB1 : CurveIsotopyNode) (hB5 : LagFamilyNode) (hA3 : LagIsotopyNode)
    (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ) :
    ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ),
      Similar (RectangularPegProblem.R z w θ) (RectangularPegProblem.R z' w' θ') ∧
      ∀ i : Fin 4, RectangularPegProblem.R z' w' θ' i ∈ Set.range γ :=
  theorem_1_of_nodes hG1 hC hB1 hB5 hA3 γ z w θ hγ

end Work.RPV
