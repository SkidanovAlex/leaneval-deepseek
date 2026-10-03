import Submission.Work.Interfaces.Parabolic

/-!
# HORN decomposition (lead, 2026-09-28): Shishikura Prop 5.3 in pieces

Design: NOTES_LEAD_horn.md (workspace root).  Setup: `f₀ ∈ 𝓕₀` with its immediate basin `B` and
unique critical point `c ∈ B`, and §4.1 data `d`.  `Bt = φ⁻¹(B)` (inside `Dφ`), `Bu`/`Bl` its
components through `±i(η₀+1)`.  Pieces (each an independent area; the HORN owner assembles
`HornData` from them):
* `HornTopoStatement`   – `Bu, Bl` open, `T`-invariant, contain the half planes, `⊆ DE`;
* `HornPhiStatement`    – Claim A: `Φ : B → ℂ` is onto and has holomorphic local sections through
  every point over every disc avoiding `Φ c - ℕ` (so it is a covering there);
* `HornVarphiStatement` – Claim B: `φ : Bu ∪ Bl → B` has holomorphic local sections through every
  point over small discs around points of `B` off the forward critical orbit;
* `BasinSCStatement`, `PlanarInterSCStatement`, `HornSCStatement` – simple connectivity of `B`
  (Lemma 5.2), of components of intersections of simply connected plane domains, and of `Bu, Bl`
  (+ disjointness).
-/

namespace MandelDim

open Complex Set Metric Filter Topology

noncomputable section

/-- `f₀ ∈ 𝓕₀` with a chosen immediate basin `B` and its unique critical point `c`. -/
def IsF0Setup (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) : Prop :=
  IsParabolicGerm f₀ D₀ ∧ IsImmediateBasin f₀ D₀ B ∧ c ∈ B ∧ deriv f₀ c = 0 ∧
    ∀ c' ∈ B, deriv f₀ c' = 0 → c' = c

/-- `φ⁻¹(B)` inside the maximal domain. -/
def Btil {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (B : Set ℂ) : Set ℂ :=
  {w | w ∈ d.Dφ ∧ d.φ w ∈ B}

/-- The upper component `B̃ᵘ`. -/
def BuOf {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (B : Set ℂ) : Set ℂ :=
  connectedComponentIn (Btil d B) (I * (d.η₀ + 1))

/-- The lower component `B̃ˡ`. -/
def BlOf {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) (B : Set ℂ) : Set ℂ :=
  connectedComponentIn (Btil d B) (-(I * (d.η₀ + 1)))

/-- The forward critical orbit `{f^k c | k ≥ 1}` (the postcritical set in `B`). -/
def critOrbit (f₀ : ℂ → ℂ) (c : ℂ) : Set ℂ := {z | ∃ k : ℕ, 1 ≤ k ∧ z = f₀^[k] c}

def HornTopoStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀), IsF0Setup f₀ D₀ B c →
    IsOpen (BuOf d B) ∧ IsOpen (BlOf d B) ∧ IsTInvariant (BuOf d B) ∧ IsTInvariant (BlOf d B) ∧
    {w : ℂ | d.η₀ < w.im} ⊆ BuOf d B ∧ {w : ℂ | w.im < -d.η₀} ⊆ BlOf d B ∧
    BuOf d B ∪ BlOf d B ⊆ d.DE

/-- Claim A (Φ is a covering of `ℂ ∖ (Φ c - ℕ)`, onto `ℂ`). -/
def HornPhiStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀), IsF0Setup f₀ D₀ B c →
    (∀ y : ℂ, ∃ z ∈ B, d.Φ z = y) ∧
    ∀ y : ℂ, (∀ k : ℕ, y ≠ d.Φ c - k) → ∃ r > 0, ∀ z ∈ B, d.Φ z ∈ ball y r →
      ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (ball y r) ∧ MapsTo σ (ball y r) B ∧
        (∀ u ∈ ball y r, d.Φ (σ u) = u) ∧ σ (d.Φ z) = z

/-- Claim B (φ is a covering over `B ∖ critOrbit`, on `Bu ∪ Bl`). -/
def HornVarphiStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀), IsF0Setup f₀ D₀ B c →
    ∀ y ∈ B, y ∉ critOrbit f₀ c → ∃ r > 0, ball y r ⊆ B ∧
      ∀ w ∈ BuOf d B ∪ BlOf d B, d.φ w ∈ ball y r →
        ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (ball y r) ∧ MapsTo σ (ball y r) (BuOf d B ∪ BlOf d B) ∧
          (∀ u ∈ ball y r, d.φ (σ u) = u) ∧ σ (d.φ w) = w

/-- Lemma 5.2 (one critical point ⇒ the immediate basin is simply connected). -/
def BasinSCStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (_d : ParabData f₀ D₀), IsF0Setup f₀ D₀ B c →
    SimplyConnectedSpace B

/-- Planar topology: components of the intersection of two simply connected open plane sets are
simply connected. -/
def PlanarInterSCStatement : Prop :=
  ∀ (U V : Set ℂ), IsOpen U → IsOpen V → SimplyConnectedSpace U → SimplyConnectedSpace V →
    ∀ x ∈ U ∩ V, SimplyConnectedSpace (connectedComponentIn (U ∩ V) x)

/-- `Bu`, `Bl` simply connected and disjoint (Prop 5.3, last part). -/
def HornSCStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : ParabData f₀ D₀), IsF0Setup f₀ D₀ B c →
    SimplyConnectedSpace (BuOf d B) ∧ SimplyConnectedSpace (BlOf d B) ∧
    Disjoint (BuOf d B) (BlOf d B)

/-- SPREAD-CHAIN (area, lead-approved 09-29): Shishikura's Lemma 5.4 chain for the pushed-down horn
map.  The spreads of the `q` Leau-Fatou petals of `g = pushdown d.E` on
`D_g = insert 0 (piExp '' (Bu ∪ Bl))` are pairwise disjoint immediate parabolic basins of `g` on
`D_g`, simply connected, `g` is not injective on them, and each contains its petal.

This is the single remaining input of `Work.Horn.horn_germ_F0`.  Five independent review verdicts
(`Submission/Work/Horn/NOTES_GERM_F0.md` §§36, 39, 40, 45, 48) established that it is **not**
derivable from the covering rung plus growth at infinity, so it enters here as an interface object
(in the same style as `HornTopoStatement`), rather than as a consequence of `hcov`.  Once it is
available, `Work.Horn.horn_germ_F0` closes through `Work.Horn.horn_germ_F0_of_basinClause` with
`hsecond` from `Work.Horn.eq_one_of_spreads` and `hbasin` from
`Work.Horn.unique_critPoint_of_single_critVal`. -/
def SpreadChainStatement : Prop :=
  ∀ (f₀ : ℂ → ℂ) (D₀ : Set ℂ), InF0 f₀ D₀ → ∀ (d : ParabData f₀ D₀) (B : Set ℂ),
    IsImmediateBasin f₀ D₀ B → B.Nonempty → ∀ (η : ℝ) (Bu Bl : Set ℂ) (c : ℂ),
    Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)) →
    Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))) →
    Bu ∪ Bl ⊆ d.DE → {w : ℂ | η < w.im} ⊆ Bu → {w : ℂ | w.im < -η} ⊆ Bl →
    IsF0Setup f₀ D₀ B c →
    (IsCoveringMapOn (fun x : ↥(BuOf d B) => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k} ∧
      IsCoveringMapOn (fun x : ↥(BlOf d B) => d.E x) {y : ℂ | ∀ k : ℤ, y ≠ d.Φ c + k}) →
    ∀ (q : ℕ) (a : ℂ), 1 ≤ q → a ≠ 0 →
    Filter.Tendsto (fun ζ : ℂ => (pushdown d.E ζ - ζ - a * ζ ^ (q + 1)) / ζ ^ (q + 1))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) →
    ∀ V : Fin q → Set ℂ,
    (∀ i, IsOpen (V i)) → (∀ i, IsConnected (V i)) →
    (∀ i, V i ⊆ insert 0 (piExp '' (Bu ∪ Bl))) →
    (∀ i, ∀ z ∈ V i, pushdown d.E z ∈ V i ∪ {0}) →
    (∀ i, (0 : ℂ) ∉ V i) →
    (∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j)) →
    (∀ i, (0 : ℂ) ∈ closure (V i)) →
    (∀ i, Set.InjOn (pushdown d.E) (V i)) →
    (∀ z ∈ ParabolicBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl))),
      ∃ n : ℕ, (pushdown d.E)^[n] z ∈ ⋃ i, V i) →
    (∀ z ∈ insert 0 (piExp '' (Bu ∪ Bl)),
      (∃ n : ℕ, (∀ k < n, (pushdown d.E)^[k] z ∈ insert 0 (piExp '' (Bu ∪ Bl))) ∧
        (pushdown d.E)^[n] z ∈ ⋃ i, V i) →
      z ∈ ParabolicBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl)))) →
    (∀ z ∈ ParabolicBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl))),
      ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, (pushdown d.E)^[n] z ∈ V i) ↔
        (∃ n : ℕ, (pushdown d.E)^[n] w ∈ V i))) →
    (0 : ℂ) ∉ ParabolicBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl))) →
    ∃ B' : Fin q → Set ℂ,
      (∀ i, IsImmediateBasin (pushdown d.E) (insert 0 (piExp '' (Bu ∪ Bl))) (B' i)) ∧
      (∀ i, SimplyConnectedSpace (B' i)) ∧
      (∀ i, ¬ Set.InjOn (pushdown d.E) (B' i)) ∧
      (∀ i, V i ⊆ B' i) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (B' i) (B' j))

end

end MandelDim
