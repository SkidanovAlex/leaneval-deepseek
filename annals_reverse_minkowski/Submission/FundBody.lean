import Mathlib
import Submission.Transport
import Submission.CellTransport
import Submission.VoronoiMeasure
import Submission.GaussianMeasure
import Submission.Commons.Analysis.InnerProductSpace.orthogonalSplit_measurePreserving

open Module Real MeasureTheory
open scoped Real InnerProductSpace RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Fundamental bodies: intrinsic cells of a lattice in its own span ([C]-final foundation)

The boundary case of `gamma_stable_of_two_le` must relate, for a sublattice `ℒ` of the
ambient `E = EuclideanSpace ℝ (Fin m)`, three incarnations of its Voronoi cell:

* the AMBIENT cell `Voronoi.voronoi ℒ ⊆ E` (a cylinder over the in-span cell, by
  `CellTransport.voronoi_cylinder`);
* the IN-SPAN cell `Voronoi.voronoi (latticeInSpan ℒ)` inside the real span
  `W ℒ := realSpan ℒ` (the lattice viewed in its own span — the cell is full-dimensional
  there);
* the TRANSPORTED cell `Voronoi.voronoi (transLattice ℒ)` in the standard space
  `EuclideanSpace ℝ (Fin (finrank ℤ ℒ))`, the image of the in-span cell under the
  isometry `realSpanIso ℒ` (`CellTransport.voronoi_map`).

This module records the dictionary between these incarnations:

* `latticeInSpan ℒ` — the image of `ℒ` under the `ℤ`-linear embedding `inSpanMap ℒ`
  into its real span;
* `transLattice_eq_latticeMap` — `transLattice ℒ = latticeMap (realSpanIso ℒ) (latticeInSpan ℒ)`;
* `mem_voronoi_inSpan_iff` — the in-span cell is the ambient cell restricted to the span;
* **`voronoi_transport_image`** — the transported cell is the `realSpanIso`-image of the
  ambient cell restricted to the span (the dictionary lemma).

These identities let every intrinsic statement about a rank-`d` sublattice (Voronoi-cell
geometry, determinants, stability, Gaussian masses) be moved freely between the sublattice's
own span and the standard `d`-dimensional space where the induction hypothesis lives.
-/

namespace Submission.FundBody

noncomputable section

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "W" => Submission.QuotientLattice.realSpan

/-- The `ℤ`-linear embedding of a lattice into its real span. -/
def inSpanMap (ℒ : Submodule ℤ E) : ℒ →ₗ[ℤ] W ℒ where
  toFun := fun y => ⟨(y : E), Submission.QuotientLattice.mem_realSpan (ℒ := ℒ) (x := ((y : ℒ) : E)) y.2⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- The lattice viewed as a sublattice of its own real span. -/
def latticeInSpan (ℒ : Submodule ℤ E) : Submodule ℤ (W ℒ) :=
  Submodule.map (inSpanMap ℒ) ⊤

/-- Membership in the in-span lattice: elements are the images of lattice points. -/
lemma mem_latticeInSpan_iff (ℒ : Submodule ℤ E) (x : W ℒ) :
    x ∈ latticeInSpan ℒ ↔ ∃ y : ℒ, inSpanMap ℒ y = x := by
  dsimp [latticeInSpan]
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hx⟩
    exact ⟨y, hx⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, trivial, hy⟩

/-- The basis values equal the in-span images of the basis elements. -/
lemma basisValuesW_eq_inSpanMap (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (i : Fin (Module.finrank ℤ ℒ)) :
    Submission.Transport.basisValuesW ℒ i = inSpanMap ℒ (Module.finBasis ℤ ℒ i) := by
  apply Subtype.ext
  rfl

/-- The in-span basis values span the in-span lattice. -/
lemma latticeInSpan_eq_span (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    latticeInSpan ℒ = Submodule.span ℤ (Set.range (Submission.Transport.basisValuesW ℒ)) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ (↥ℒ) := Module.finBasis ℤ ℒ
  have hset : Set.range (Submission.Transport.basisValuesW ℒ) = (inSpanMap ℒ) '' Set.range b := by
    ext x
    constructor
    · rintro ⟨i, hx⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      calc
        inSpanMap ℒ (b i) = Submission.Transport.basisValuesW ℒ i := by
            simpa [b] using (basisValuesW_eq_inSpanMap ℒ i).symm
        _ = x := hx
    · rintro ⟨y, ⟨i, rfl⟩, hx⟩
      refine ⟨i, ?_⟩
      calc
        Submission.Transport.basisValuesW ℒ i = inSpanMap ℒ (b i) := by
            simpa [b] using basisValuesW_eq_inSpanMap ℒ i
        _ = x := hx
  calc
    latticeInSpan ℒ = Submodule.map (inSpanMap ℒ) ⊤ := rfl
    _ = Submodule.map (inSpanMap ℒ) (Submodule.span ℤ (Set.range b)) := by
        congr 1
        exact (b.span_eq).symm
    _ = Submodule.span ℤ ((inSpanMap ℒ) '' Set.range b) := by rw [Submodule.map_span]
    _ = Submodule.span ℤ (Set.range (Submission.Transport.basisValuesW ℒ)) := by
        rw [hset]

/-- The transported lattice is the isometry-image of the in-span lattice. -/
lemma transLattice_eq_latticeMap (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    Submission.Transport.transLattice ℒ =
      Submission.CellTransport.latticeMap (Submission.Transport.realSpanIso ℒ) (latticeInSpan ℒ) := by
  classical
  calc
    Submission.Transport.transLattice ℒ
        = Submodule.span ℤ (Set.range (Submission.Transport.transValues ℒ)) := rfl
    _ = Submodule.span ℤ ((Submission.Transport.realSpanIso ℒ).toLinearEquiv.toLinearMap.restrictScalars ℤ
          '' Set.range (Submission.Transport.basisValuesW ℒ)) := by
        congr 1
        ext x
        simp [Submission.Transport.transValues]
    _ = Submodule.map ((Submission.Transport.realSpanIso ℒ).toLinearEquiv.toLinearMap.restrictScalars ℤ)
          (Submodule.span ℤ (Set.range (Submission.Transport.basisValuesW ℒ))) := by
        rw [← Submodule.map_span]
    _ = Submodule.map ((Submission.Transport.realSpanIso ℒ).toLinearEquiv.toLinearMap.restrictScalars ℤ)
          (latticeInSpan ℒ) := by
        rw [latticeInSpan_eq_span ℒ]
    _ = Submission.CellTransport.latticeMap (Submission.Transport.realSpanIso ℒ) (latticeInSpan ℒ) := rfl

/-- The in-span Voronoi cell equals the ambient cell restricted to the span. -/
lemma mem_voronoi_inSpan_iff (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] (x : W ℒ) :
    x ∈ Submission.Voronoi.voronoi (latticeInSpan ℒ) ↔ (x : E) ∈ Submission.Voronoi.voronoi ℒ := by
  rw [Submission.Voronoi.mem_voronoi, Submission.Voronoi.mem_voronoi]
  constructor
  · intro hx y
    have hzmem : inSpanMap ℒ y ∈ latticeInSpan ℒ := by
      exact (mem_latticeInSpan_iff ℒ (inSpanMap ℒ y)).2 ⟨y, rfl⟩
    have h := hx ⟨inSpanMap ℒ y, hzmem⟩
    simpa [inSpanMap] using h
  · intro hx z
    change ⟪x, (z : W ℒ)⟫_ℝ ≤ ‖(z : W ℒ)‖ ^ 2 / 2
    have hzcar : (z : W ℒ) ∈ latticeInSpan ℒ := z.2
    rcases (mem_latticeInSpan_iff ℒ (z : W ℒ)).1 hzcar with ⟨y, hy⟩
    have h := hx y
    rw [← hy]
    simpa [inSpanMap] using h

/-- **Dictionary lemma**: the transported Voronoi cell equals the image of the ambient cell
restricted to the real span. -/
theorem voronoi_transport_image (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    (Submission.Transport.realSpanIso ℒ) ''
        {x : W ℒ | (x : E) ∈ Submission.Voronoi.voronoi ℒ} =
      Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ) := by
  calc
    (Submission.Transport.realSpanIso ℒ) ''
        {x : W ℒ | (x : E) ∈ Submission.Voronoi.voronoi ℒ}
        = (Submission.Transport.realSpanIso ℒ) '' (Submission.Voronoi.voronoi (latticeInSpan ℒ)) := by
          congr 1
          ext x
          exact (mem_voronoi_inSpan_iff ℒ x).symm
    _ = Submission.Voronoi.voronoi
          (Submission.CellTransport.latticeMap (Submission.Transport.realSpanIso ℒ) (latticeInSpan ℒ)) := by
          exact (Submission.CellTransport.voronoi_map (Submission.Transport.realSpanIso ℒ) (latticeInSpan ℒ)).symm
    _ = Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ) := by
          rw [transLattice_eq_latticeMap ℒ]

/-- The ambient Voronoi cell of an orthogonal sum of lattices is the intersection of the
cells of the summands (no complementarity/full-rank hypotheses needed: membership in the
cell of the sum only constrains against the two summands separately, and the converse uses
orthogonality of the summands for the norm identity). -/
lemma voronoi_sup_inter (ℒ₁ ℒ₂ : Submodule ℤ E)
    (hop : Submission.QuotientLattice.OrthogonalPair ℒ₁ ℒ₂) :
    Submission.Voronoi.voronoi (ℒ₁ ⊔ ℒ₂) =
      Submission.Voronoi.voronoi ℒ₁ ∩ Submission.Voronoi.voronoi ℒ₂ := by
  ext x
  rw [Set.mem_inter_iff]
  rw [Submission.Voronoi.mem_voronoi, Submission.Voronoi.mem_voronoi, Submission.Voronoi.mem_voronoi]
  constructor
  · intro hx
    constructor
    · intro y₁
      have hz : (y₁ : E) ∈ (ℒ₁ ⊔ ℒ₂ : Submodule ℤ E) := by
        exact Submodule.mem_sup.mpr ⟨(y₁ : E), y₁.2, 0, Submodule.zero_mem ℒ₂, by simp⟩
      have h := hx ⟨(y₁ : E), hz⟩
      simpa using h
    · intro y₂
      have hz : (y₂ : E) ∈ (ℒ₁ ⊔ ℒ₂ : Submodule ℤ E) := by
        exact Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem ℒ₁, (y₂ : E), y₂.2, by simp⟩
      have h := hx ⟨(y₂ : E), hz⟩
      simpa using h
  · intro hx y
    have hx1 : ∀ w : ℒ₁, ⟪x, (w : E)⟫_ℝ ≤ ‖(w : E)‖ ^ 2 / 2 := hx.1
    have hx2 : ∀ w : ℒ₂, ⟪x, (w : E)⟫_ℝ ≤ ‖(w : E)‖ ^ 2 / 2 := hx.2
    rcases (Submodule.mem_sup.mp y.2) with ⟨a, ha, b, hb, hab⟩
    have h1 : ⟪x, a⟫_ℝ ≤ ‖a‖ ^ 2 / 2 := hx1 ⟨a, ha⟩
    have h2 : ⟪x, b⟫_ℝ ≤ ‖b‖ ^ 2 / 2 := hx2 ⟨b, hb⟩
    have horth : ⟪a, b⟫_ℝ = 0 := hop a ha b hb
    calc
      ⟪x, (y : E)⟫_ℝ = ⟪x, a + b⟫_ℝ := by rw [hab]
      _ = ⟪x, a⟫_ℝ + ⟪x, b⟫_ℝ := by rw [inner_add_right]
      _ ≤ ‖a‖ ^ 2 / 2 + ‖b‖ ^ 2 / 2 := by exact add_le_add h1 h2
      _ = ‖a + b‖ ^ 2 / 2 := by
          have hsq : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
            rw [norm_add_sq_real]
            rw [horth]
            ring
          rw [hsq]
          ring
      _ = ‖(y : E)‖ ^ 2 / 2 := by rw [hab]


/-- orthogonal carrier product vanishes: `a ∈ Sᗮ`, `b ∈ S` ⇒ `⟪a,b⟫ = 0`. -/
lemma ortho_carrier (S : Submodule ℝ E) {a b : E} (ha : a ∈ Sᗮ) (hb : b ∈ S) :
    ⟪a, b⟫_ℝ = 0 := by
  have h := (Submodule.mem_orthogonal S a).1 ha b hb
  rw [real_inner_comm] at h
  exact h

/-- every ambient point splits as `u ∈ S`, `v ∈ Sᗮ` (orthogonal projection). -/
lemma split_orthogonal (S : Submodule ℝ E) (x : E) :
    ∃ u : ↥S, ∃ v : ↥(Sᗮ), (u : E) + (v : E) = x := by
  rcases (inferInstance : S.HasOrthogonalProjection).exists_orthogonal x with ⟨w, hw, hwu⟩
  refine ⟨⟨w, hw⟩, ⟨x - w, hwu⟩, ?_⟩
  change w + (x - w) = x
  abel

/-- The Voronoi cell of an orthogonal complementary sum is the sum of the in-span bases:
`V(ℒ₁ ⊔ ℒ₂) = C₁ + C₂` with `C₁ := {u ∈ realSpan ℒ₁ | u ∈ V(ℒ₁)}` and
`C₂ := {v ∈ (realSpan ℒ₁)ᗮ | v ∈ V(ℒ₂)}` (uses `hop` for the norm-splitting of ℒ₁/ℒ₂
vectors and `hR : realSpan ℒ₂ = (realSpan ℒ₁)ᗮ` so ℒ₂-vectors lie in the complement). -/
lemma voronoi_sup_eq_cell_sum (ℒ₁ ℒ₂ : Submodule ℤ E)
    (hop : Submission.QuotientLattice.OrthogonalPair ℒ₁ ℒ₂)
    (hR : W ℒ₂ = (W ℒ₁)ᗮ) :
    Submission.Voronoi.voronoi (ℒ₁ ⊔ ℒ₂) =
      {x : E | ∃ u ∈ {u : ↥(W ℒ₁) | (u : E) ∈ Submission.Voronoi.voronoi ℒ₁},
        ∃ v ∈ {v : ↥((W ℒ₁)ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂},
          (u : E) + (v : E) = x} := by
  ext x
  constructor
  · intro hx
    rw [Submission.FundBody.voronoi_sup_inter ℒ₁ ℒ₂ hop] at hx
    have hx1 : x ∈ Submission.Voronoi.voronoi ℒ₁ := hx.1
    have hx2 : x ∈ Submission.Voronoi.voronoi ℒ₂ := hx.2
    rcases split_orthogonal (W ℒ₁) x with ⟨u, v, hxuv⟩
    refine ⟨u, ?_, v, ?_, hxuv⟩
    · change (u : E) ∈ Submission.Voronoi.voronoi ℒ₁
      rw [Submission.Voronoi.mem_voronoi]
      intro y
      have hv0 : ⟪(v : E), (y : E)⟫_ℝ = 0 := by
        have hb : (y : E) ∈ (W ℒ₁ : Set E) :=
          Submission.QuotientLattice.mem_realSpan (ℒ := ℒ₁) (x := (((y : ℒ₁) : E))) y.2
        exact ortho_carrier (W ℒ₁) v.2 hb
      have hu_eq : ⟪(u : E), (y : E)⟫_ℝ = ⟪x, (y : E)⟫_ℝ := by
        calc
          ⟪(u : E), (y : E)⟫_ℝ = ⟪x - (v : E), (y : E)⟫_ℝ := by
              congr 1
              rw [← hxuv]
              abel
          _ = ⟪x, (y : E)⟫_ℝ - ⟪(v : E), (y : E)⟫_ℝ := by rw [inner_sub_left]
          _ = ⟪x, (y : E)⟫_ℝ := by rw [hv0]; ring
      rw [hu_eq]
      rw [Submission.Voronoi.mem_voronoi] at hx1
      exact hx1 y
    · change (v : E) ∈ Submission.Voronoi.voronoi ℒ₂
      rw [Submission.Voronoi.mem_voronoi]
      intro y
      have hy2 : (y : E) ∈ ((W ℒ₁)ᗮ : Set E) := by
        rw [← hR]
        exact Submission.QuotientLattice.mem_realSpan (ℒ := ℒ₂) (x := (((y : ℒ₂) : E))) y.2
      have hu0 : ⟪(u : E), (y : E)⟫_ℝ = 0 := by
        have h0 := ortho_carrier (W ℒ₁) hy2 u.2
        rwa [real_inner_comm]
      have hv_eq : ⟪(v : E), (y : E)⟫_ℝ = ⟪x, (y : E)⟫_ℝ := by
        calc
          ⟪(v : E), (y : E)⟫_ℝ = ⟪x - (u : E), (y : E)⟫_ℝ := by
              congr 1
              rw [← hxuv]
              abel
          _ = ⟪x, (y : E)⟫_ℝ - ⟪(u : E), (y : E)⟫_ℝ := by rw [inner_sub_left]
          _ = ⟪x, (y : E)⟫_ℝ := by rw [hu0]; ring
      rw [hv_eq]
      rw [Submission.Voronoi.mem_voronoi] at hx2
      exact hx2 y
  · rintro ⟨u, hu, v, hv, hxuv⟩
    have hx1 : x ∈ Submission.Voronoi.voronoi ℒ₁ := by
      rw [Submission.Voronoi.mem_voronoi]
      intro y
      calc
        ⟪x, (y : E)⟫_ℝ = ⟪(u : E) + (v : E), (y : E)⟫_ℝ := by rw [← hxuv]
        _ = ⟪(u : E), (y : E)⟫_ℝ + ⟪(v : E), (y : E)⟫_ℝ := by rw [inner_add_left]
        _ = ⟪(u : E), (y : E)⟫_ℝ := by
            have hv0 : ⟪(v : E), (y : E)⟫_ℝ = 0 := by
              have hb : (y : E) ∈ (W ℒ₁ : Set E) :=
                Submission.QuotientLattice.mem_realSpan (ℒ := ℒ₁) (x := (((y : ℒ₁) : E))) y.2
              exact ortho_carrier (W ℒ₁) v.2 hb
            rw [hv0]
            ring
        _ ≤ ‖(y : E)‖ ^ 2 / 2 := by
            change (u : E) ∈ Submission.Voronoi.voronoi ℒ₁ at hu
            rw [Submission.Voronoi.mem_voronoi] at hu
            exact hu y
    have hx2 : x ∈ Submission.Voronoi.voronoi ℒ₂ := by
      rw [Submission.Voronoi.mem_voronoi]
      intro y
      calc
        ⟪x, (y : E)⟫_ℝ = ⟪(u : E) + (v : E), (y : E)⟫_ℝ := by rw [← hxuv]
        _ = ⟪(u : E), (y : E)⟫_ℝ + ⟪(v : E), (y : E)⟫_ℝ := by rw [inner_add_left]
        _ = ⟪(v : E), (y : E)⟫_ℝ := by
            have hu0 : ⟪(u : E), (y : E)⟫_ℝ = 0 := by
              have hy2 : (y : E) ∈ ((W ℒ₁)ᗮ : Set E) := by
                rw [← hR]
                exact Submission.QuotientLattice.mem_realSpan (ℒ := ℒ₂) (x := (((y : ℒ₂) : E))) y.2
              have h0 := ortho_carrier (W ℒ₁) hy2 u.2
              rwa [real_inner_comm]
            rw [hu0]
            ring
        _ ≤ ‖(y : E)‖ ^ 2 / 2 := by
            change (v : E) ∈ Submission.Voronoi.voronoi ℒ₂ at hv
            rw [Submission.Voronoi.mem_voronoi] at hv
            exact hv y
    rw [Submission.FundBody.voronoi_sup_inter ℒ₁ ℒ₂ hop]
    exact ⟨hx1, hx2⟩

end

/-! ## The γ-split (orthogonal product of Gaussian masses)

The orthogonal-split bijection `phiOf W : ↥W × ↥(Wᗮ) → X`, `(u,v) ↦ (u:X)+(v:X)`, is
measure-preserving from the product of the subspace volumes to the ambient volume
(`Commons.Analysis.InnerProductSpace.orthogonalSplit_measurePreserving`, proved by the
fleet); it is a measurable embedding and injective (`W.orthogonalDecomposition`-based).
This makes the Gaussian mass of the orthogonal SUM of two measurable sets factor into the
product of their own Gaussian masses (`gammaMassGen_split`) — the [C]-final-B identity that
turns `γ_s(V(ℒ' ⊔ Q))` into `γ_s(V(transQ))·γ_s(V(transℒ'))`. -/

section Generic

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]

noncomputable def phiOf (W : Submodule ℝ X) : ↥W × ↥(Wᗮ) → X :=
  fun p => (p.1 : X) + (p.2 : X)


lemma phiOf_eq_orthogonalDecomposition (W : Submodule ℝ X) :
    phiOf W = fun p => (W.orthogonalDecomposition.symm) (WithLp.toLp 2 p) := by
  funext p
  dsimp [phiOf]
  calc
    W.orthogonalDecomposition.symm (WithLp.toLp 2 p)
        = (W.orthogonalDecomposition.symm.toLinearEquiv) (WithLp.toLp 2 p) := rfl
    _ = (W.prodEquivOfIsCompl Wᗮ W.isCompl_orthogonal) p := by
        rw [Submodule.toLinearEquiv_orthogonalDecomposition_symm]
        simp
    _ = (p.1 : X) + (p.2 : X) := by
        exact Submodule.coe_prodEquivOfIsCompl' W Wᗮ W.isCompl_orthogonal p

lemma phiOf_measurableEmbedding (W : Submodule ℝ X) : MeasurableEmbedding (phiOf W) := by
  rw [phiOf_eq_orthogonalDecomposition]
  refine MeasurableEmbedding.comp ?_ ?_
  · exact (W.orthogonalDecomposition.symm).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  · exact (MeasurableEquiv.toLp 2 (↥W × ↥(Wᗮ))).measurableEmbedding

lemma phiOf_measurePreserving (W : Submodule ℝ X) :
    MeasurePreserving (phiOf W) (volume : Measure (↥W × ↥(Wᗮ))) (volume : Measure X) :=
  Commons.Analysis.InnerProductSpace.orthogonalSplit_measurePreserving W

lemma orthogonal_sum_zero (W : Submodule ℝ X) (a : ↥W) (b : ↥(Wᗮ))
    (h : (a : X) + (b : X) = 0) : a = 0 ∧ b = 0 := by
  have horth : ⟪(a : X), (b : X)⟫_ℝ = 0 := by
    exact (Submodule.mem_orthogonal (W : Submodule ℝ X) (b : X)).1 b.2 (a : X) a.2
  have haX : (a : X) = -(b : X) := by
    have : (a : X) = ((a : X) + (b : X)) - (b : X) := by abel
    rw [h] at this
    simpa using this
  have hsq : ‖(a : X)‖ ^ 2 = 0 := by
    calc
      ‖(a : X)‖ ^ 2 = ⟪(a : X), (a : X)⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
      _ = ⟪(a : X), -((b : X))⟫_ℝ := by rw [haX]
      _ = -⟪(a : X), (b : X)⟫_ℝ := by simp
      _ = 0 := by rw [horth]; ring
  have ha0 : (a : X) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hb0 : (b : X) = 0 := by
    have : (b : X) = -((a : X)) := by
      have : (b : X) = ((a : X) + (b : X)) - (a : X) := by abel
      rw [h] at this
      simpa using this
    rw [ha0] at this
    simpa using this
  exact ⟨Subtype.ext ha0, Subtype.ext hb0⟩

lemma phiOf_injective (W : Submodule ℝ X) : Function.Injective (phiOf W) := by
  intro p q hpq
  let a : ↥W := p.1 - q.1
  let b : ↥(Wᗮ) := p.2 - q.2
  have haX : (a : X) = (p.1 : X) - (q.1 : X) := by simp [a]
  have hbX : (b : X) = (p.2 : X) - (q.2 : X) := by simp [b]
  have hsum : (a : X) + (b : X) = 0 := by
    rw [haX, hbX]
    have hpqX : (p.1 : X) + (p.2 : X) = (q.1 : X) + (q.2 : X) := hpq
    calc
      ((p.1 : X) - (q.1 : X)) + ((p.2 : X) - (q.2 : X))
          = ((p.1 : X) + (p.2 : X)) - ((q.1 : X) + (q.2 : X)) := by abel
      _ = 0 := by rw [hpqX]; abel
  rcases (orthogonal_sum_zero W a b hsum) with ⟨ha, hb⟩
  have hp1 : p.1 = q.1 := sub_eq_zero.mp (by simpa [a] using ha)
  have hp2 : p.2 = q.2 := sub_eq_zero.mp (by simpa [b] using hb)
  exact Prod.ext hp1 hp2

lemma phiOf_smul (W : Submodule ℝ X) (s : ℝ) (p : ↥W × ↥(Wᗮ)) :
    phiOf W (s • p) = s • phiOf W p := by
  dsimp [phiOf]
  -- s • p = (s • p.1, s • p.2)
  rcases p with ⟨u, v⟩
  dsimp [phiOf]
  rw [smul_add]

/-- membership in the scaled image splits -/
lemma mem_scaled_image_iff (W : Submodule ℝ X) (s : ℝ) (A : Set (↥W)) (B : Set (↥(Wᗮ)))
    (p : ↥W × ↥(Wᗮ)) :
    s • phiOf W p ∈ phiOf W '' (Set.prod A B) ↔ s • p.1 ∈ A ∧ s • p.2 ∈ B := by
  constructor
  · intro h
    rcases h with ⟨q, hq, hφ⟩
    have hqA : q.1 ∈ A := (Set.mem_prod.mp hq).1
    have hqB : q.2 ∈ B := (Set.mem_prod.mp hq).2
    have hφ' : phiOf W q = phiOf W (s • p) := by
      rw [phiOf_smul]
      exact hφ
    have hqsp : q = s • p := phiOf_injective W hφ'
    have hq1 : q.1 = s • p.1 := by simpa using (congrArg Prod.fst hqsp)
    have hq2 : q.2 = s • p.2 := by simpa using (congrArg Prod.snd hqsp)
    exact ⟨by rwa [← hq1], by rwa [← hq2]⟩
  · intro h
    let q : ↥W × ↥(Wᗮ) := (s • p.1, s • p.2)
    refine ⟨q, ?_, ?_⟩
    · exact Set.mem_prod.mpr ⟨h.1, h.2⟩
    · have hq : q = s • p := by
        apply Prod.ext <;> rfl
      rw [hq, phiOf_smul]

/-- set form: the split sum-set equals the image of the product -/
lemma sumSet_eq_image (W : Submodule ℝ X) (A : Set (↥W)) (B : Set (↥(Wᗮ))) :
    {x : X | ∃ u ∈ A, ∃ v ∈ B, (u : X) + (v : X) = x} = phiOf W '' (Set.prod A B) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, hx⟩
    refine ⟨(u, v), ?_, ?_⟩
    · exact Set.mem_prod.mpr ⟨hu, hv⟩
    · dsimp [phiOf]
      exact hx
  · rintro ⟨p, hp, hx⟩
    refine ⟨p.1, (Set.mem_prod.mp hp).1, p.2, (Set.mem_prod.mp hp).2, ?_⟩
    dsimp [phiOf] at hx
    exact hx

lemma norm_sq_add_orthogonal (W : Submodule ℝ X) (u : ↥W) (v : ↥(Wᗮ)) :
    ‖(u : X) + (v : X)‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  have horth : ⟪(u : X), (v : X)⟫_ℝ = 0 := by
    exact (Submodule.mem_orthogonal (W : Submodule ℝ X) (v : X)).1 v.2 (u : X) u.2
  calc
    ‖(u : X) + (v : X)‖ ^ 2 = ‖(u : X)‖ ^ 2 + ‖(v : X)‖ ^ 2 := by
        rw [norm_add_sq_real]
        rw [horth]
        ring
    _ = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by rfl

-- pointwise Gaussian splitting over the split map
lemma gaussian_exp_split (W : Submodule ℝ X) (p : ↥W × ↥(Wᗮ)) :
    Real.exp (-Real.pi * ‖(phiOf W p : X)‖ ^ 2) =
      (Real.exp (-Real.pi * ‖(p.1 : ↥W)‖ ^ 2)) *
        (Real.exp (-Real.pi * ‖(p.2 : ↥(Wᗮ))‖ ^ 2)) := by
  have hns := norm_sq_add_orthogonal W p.1 p.2
  have hsplit : -Real.pi * ‖((p.1 : X) + (p.2 : X))‖ ^ 2 =
      -Real.pi * ‖(p.1 : ↥W)‖ ^ 2 + -Real.pi * ‖(p.2 : ↥(Wᗮ))‖ ^ 2 := by
    rw [hns]
    ring
  calc
    Real.exp (-Real.pi * ‖(phiOf W p : X)‖ ^ 2)
        = Real.exp (-Real.pi * ‖((p.1 : X) + (p.2 : X))‖ ^ 2) := by rfl
    _ = Real.exp (-Real.pi * ‖(p.1 : ↥W)‖ ^ 2 + -Real.pi * ‖(p.2 : ↥(Wᗮ))‖ ^ 2) := by rw [hsplit]
    _ = Real.exp (-Real.pi * ‖(p.1 : ↥W)‖ ^ 2) * Real.exp (-Real.pi * ‖(p.2 : ↥(Wᗮ))‖ ^ 2) := by
        rw [Real.exp_add]
    _ = (Real.exp (-Real.pi * ‖(p.1 : ↥W)‖ ^ 2)) *
          (Real.exp (-Real.pi * ‖(p.2 : ↥(Wᗮ))‖ ^ 2)) := rfl

-- scaled set is measurable
lemma scaled_measurable (S : Submodule ℝ X) (s : ℝ) (A : Set (↥S)) (hA : MeasurableSet A) :
    MeasurableSet {u : ↥S | s • u ∈ A} := by
  exact hA.preimage (Continuous.measurable (continuous_id.const_smul s))

/-- The γ-split lemma: the Gaussian mass of the orthogonal sum of two measurable sets
factors into the product of their own Gaussian masses. -/
lemma gammaMassGen_split (W : Submodule ℝ X) (s : ℝ) (A : Set (↥W)) (B : Set (↥(Wᗮ)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    gammaMassGen (X := X) s {x : X | ∃ u ∈ A, ∃ v ∈ B, (u : X) + (v : X) = x} =
      gammaMassGen (X := ↥W) s A * gammaMassGen (X := ↥(Wᗮ)) s B := by
  let S : Set X := {x : X | ∃ u ∈ A, ∃ v ∈ B, (u : X) + (v : X) = x}
  let A' : Set (↥W) := {u : ↥W | s • u ∈ A}
  let B' : Set (↥(Wᗮ)) := {v : ↥(Wᗮ) | s • v ∈ B}
  let f : ↥W → ℝ := fun u => Real.exp (-Real.pi * ‖u‖ ^ 2)
  let hh : ↥(Wᗮ) → ℝ := fun v => Real.exp (-Real.pi * ‖v‖ ^ 2)
  let gg : X → ℝ := fun x => Real.exp (-Real.pi * ‖x‖ ^ 2)
  have hS : S = phiOf W '' (Set.prod A B) := by
    dsimp [S]
    exact sumSet_eq_image W A B
  have hT : (phiOf W) ⁻¹' {x : X | s • x ∈ S} = Set.prod A' B' := by
    ext p
    simp only [Set.mem_preimage, hS, A', B']
    exact mem_scaled_image_iff W s A B p
  have hptw : ∀ p : ↥W × ↥(Wᗮ), gg (phiOf W p) = f p.1 * hh p.2 := by
    intro p
    dsimp [gg, f, hh]
    exact gaussian_exp_split W p
  have hA' : MeasurableSet A' := by
    dsimp [A']
    exact scaled_measurable W s A hA
  have hB' : MeasurableSet B' := by
    dsimp [B']
    exact scaled_measurable (Wᗮ) s B hB
  calc
    gammaMassGen (X := X) s S = ∫ x in {x : X | s • x ∈ S}, gg x := rfl
    _ = ∫ p in (phiOf W) ⁻¹' {x : X | s • x ∈ S}, gg (phiOf W p) := by
        exact ((phiOf_measurePreserving W).setIntegral_preimage_emb (phiOf_measurableEmbedding W) gg
          {x : X | s • x ∈ S}).symm
    _ = ∫ p in Set.prod A' B', gg (phiOf W p) := by rw [hT]
    _ = ∫ p in Set.prod A' B', f p.1 * hh p.2 := by
        exact MeasureTheory.setIntegral_congr_fun (MeasurableSet.prod hA' hB') (by
          intro p hp
          exact hptw p)
    _ = (∫ u in A', f u) * (∫ v in B', hh v) := by
        exact MeasureTheory.setIntegral_prod_mul f hh A' B'
    _ = gammaMassGen (X := ↥W) s A * gammaMassGen (X := ↥(Wᗮ)) s B := by
        have h1 : gammaMassGen (X := ↥W) s A = ∫ u in A', f u := by
          change (∫ x in {y : ↥W | s • y ∈ A}, Real.exp (-Real.pi * ‖x‖ ^ 2)) = (∫ u in A', f u)
          dsimp [A', f]
        have h2 : gammaMassGen (X := ↥(Wᗮ)) s B = ∫ v in B', hh v := by
          change (∫ x in {y : ↥(Wᗮ) | s • y ∈ B}, Real.exp (-Real.pi * ‖x‖ ^ 2)) = (∫ v in B', hh v)
          dsimp [B', hh]
        rw [h1, h2]

end Generic

section AmbientSum

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "W" => Submission.QuotientLattice.realSpan

/-- measurable cell base: `{u : ↥S | (u : E) ∈ voronoi ℒ}` (the coercion is continuous). -/
lemma cell_base_measurable (ℒ : Submodule ℤ E) (S : Submodule ℝ E) :
    MeasurableSet {u : ↥S | (u : E) ∈ Submission.Voronoi.voronoi ℒ} := by
  exact (Submission.Voronoi.voronoi_isClosed ℒ).measurableSet.preimage
    (continuous_subtype_val.measurable)

/-- The Gaussian mass of the Voronoi cell of the orthogonal complementary sum is the
product of the masses of the two in-span bases (the `gammaMassGen_split` instance over
`W := realSpan ℒ₁`, fed by `voronoi_sup_eq_cell_sum`). -/
lemma gamma_sup_cell_split (ℒ₁ ℒ₂ : Submodule ℤ E)
    (hop : Submission.QuotientLattice.OrthogonalPair ℒ₁ ℒ₂)
    (hR : W ℒ₂ = (W ℒ₁)ᗮ) (s : ℝ) :
    Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi (ℒ₁ ⊔ ℒ₂)) =
      gammaMassGen (X := ↥(W ℒ₁)) s {u : ↥(W ℒ₁) | (u : E) ∈ Submission.Voronoi.voronoi ℒ₁} *
      gammaMassGen (X := ↥((W ℒ₁)ᗮ)) s {v : ↥((W ℒ₁)ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂} := by
  let C₁ : Set (↥(W ℒ₁)) := {u : ↥(W ℒ₁) | (u : E) ∈ Submission.Voronoi.voronoi ℒ₁}
  let C₂ : Set (↥((W ℒ₁)ᗮ)) := {v : ↥((W ℒ₁)ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂}
  have hC₁ : MeasurableSet C₁ := by
    dsimp [C₁]
    exact cell_base_measurable ℒ₁ (W ℒ₁)
  have hC₂ : MeasurableSet C₂ := by
    dsimp [C₂]
    exact cell_base_measurable ℒ₂ ((W ℒ₁)ᗮ)
  have hsplit := gammaMassGen_split (X := E) (W ℒ₁) s C₁ C₂ hC₁ hC₂
  rw [voronoi_sup_eq_cell_sum ℒ₁ ℒ₂ hop hR]
  dsimp [C₁, C₂] at hsplit ⊢
  exact hsplit


/-- `W₁`-factor transport: the in-span-base mass of `ℒ₁` equals the mass of the
transported Voronoi cell in its standard space. -/
lemma gammaMassGen_cell_base_transport (ℒ₁ : Submodule ℤ E) [DiscreteTopology ℒ₁]
    (s : ℝ) :
    gammaMassGen (X := ↥(W ℒ₁)) s {u : ↥(W ℒ₁) | (u : E) ∈ Submission.Voronoi.voronoi ℒ₁} =
      Submission.GaussianMeasure.gammaMass s
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₁)) := by
  let e : ↥(W ℒ₁) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ₁)) :=
    Submission.Transport.realSpanIso ℒ₁
  have hpre : e ⁻¹' (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₁)) =
      {u : ↥(W ℒ₁) | (u : E) ∈ Submission.Voronoi.voronoi ℒ₁} := by
    have htrans := Submission.FundBody.voronoi_transport_image (ℒ := ℒ₁)
    -- htrans : e '' {u | (u:E) ∈ voronoi ℒ₁} = voronoi (transLattice ℒ₁)
    rw [← htrans]
    exact Set.preimage_image_eq {u : ↥(W ℒ₁) | (u : E) ∈ Submission.Voronoi.voronoi ℒ₁} (e.injective)
  calc
    gammaMassGen (X := ↥(W ℒ₁)) s {u : ↥(W ℒ₁) | (u : E) ∈ Submission.Voronoi.voronoi ℒ₁}
        = gammaMassGen (X := ↥(W ℒ₁)) s
            (e ⁻¹' (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₁))) := by
          rw [hpre]
    _ = gammaMassGen (X := EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ₁))) s
            (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₁)) := by
          exact (gammaMassGen_transport e s
            (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₁))).symm
    _ = Submission.GaussianMeasure.gammaMass s
            (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₁)) := by rfl

/-- carrier-cast isometry between equal real submodules of the ambient `E`. -/
def subCast (S₁ S₂ : Submodule ℝ E) (h : S₁ = S₂) : ↥S₁ ≃ₗᵢ[ℝ] ↥S₂ where
  toLinearEquiv := LinearEquiv.ofEq S₁ S₂ h
  norm_map' := by
    intro x
    rfl

/-- subCast preserves carriers. -/
lemma subCast_apply (S₁ S₂ : Submodule ℝ E) (h : S₁ = S₂) (x : ↥S₁) :
    ((subCast S₁ S₂ h x : ↥S₂) : E) = (x : E) := by
  rfl

-- e2: the complement factor isometry ↥(W₁ᗮ) → E_{finrank ℒ₂}
noncomputable def e2Of (ℒ₂ : Submodule ℤ E) [DiscreteTopology ℒ₂] {W₁ : Submodule ℝ E}
    (hR : W ℒ₂ = W₁ᗮ) : ↥(W₁ᗮ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ₂)) :=
  (subCast (W₁ᗮ) (W ℒ₂) hR.symm).trans (Submission.Transport.realSpanIso ℒ₂)

/-- `e2`-analog of the dictionary: the transported cell equals the image of the
complement-base under `e2Of`. -/
lemma voronoi_e2_image (ℒ₂ : Submodule ℤ E) [DiscreteTopology ℒ₂] {W₁ : Submodule ℝ E}
    (hR : W ℒ₂ = W₁ᗮ) :
    e2Of ℒ₂ (W₁ := W₁) hR '' {v : ↥(W₁ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂} =
      Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂) := by
  let S : Set (↥(W₁ᗮ)) := {v : ↥(W₁ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂}
  let T : Set (↥(W ℒ₂)) := {z : ↥(W ℒ₂) | (z : E) ∈ Submission.Voronoi.voronoi ℒ₂}
  have hcast : (subCast (W₁ᗮ) (W ℒ₂) hR.symm) '' S = T := by
    dsimp [S, T]
    ext z
    constructor
    · rintro ⟨v, hv, hz⟩
      have hzE : (z : E) = (v : E) := by
        rw [← hz]
        exact subCast_apply (W₁ᗮ) (W ℒ₂) hR.symm v
      change (z : E) ∈ Submission.Voronoi.voronoi ℒ₂
      rw [hzE]
      exact hv
    · intro hz
      let v : ↥(W₁ᗮ) := (subCast (W₁ᗮ) (W ℒ₂) hR.symm).symm z
      refine ⟨v, ?_, ?_⟩
      · have hc : ((subCast (W₁ᗮ) (W ℒ₂) hR.symm) v : E) = (z : E) := by
          exact congrArg (fun w : ↥(W ℒ₂) => (w : E))
            ((subCast (W₁ᗮ) (W ℒ₂) hR.symm).apply_symm_apply z)
        have hvE : (v : E) = (z : E) := by
          dsimp [v]
          exact (subCast_apply (W₁ᗮ) (W ℒ₂) hR.symm
            ((subCast (W₁ᗮ) (W ℒ₂) hR.symm).symm z)).symm.trans hc
        change (v : E) ∈ Submission.Voronoi.voronoi ℒ₂
        rw [hvE]
        exact hz
      · rfl
  calc
    e2Of ℒ₂ (W₁ := W₁) hR '' S
        = (Submission.Transport.realSpanIso ℒ₂) '' ((subCast (W₁ᗮ) (W ℒ₂) hR.symm) '' S) := by
          change (((Submission.Transport.realSpanIso ℒ₂) ∘ (subCast (W₁ᗮ) (W ℒ₂) hR.symm)) '' S) =
            (Submission.Transport.realSpanIso ℒ₂) '' ((subCast (W₁ᗮ) (W ℒ₂) hR.symm) '' S)
          rw [Set.image_comp]
    _ = (Submission.Transport.realSpanIso ℒ₂) '' T := by rw [hcast]
    _ = Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂) := by
          rw [← Submission.FundBody.voronoi_transport_image (ℒ := ℒ₂)]

/-- `W₁ᗮ`-factor transport: the complement-base mass of `ℒ₂` equals the mass of the
transported Voronoi cell. -/
lemma gammaMassGen_compl_base_transport (ℒ₂ : Submodule ℤ E) [DiscreteTopology ℒ₂]
    {W₁ : Submodule ℝ E} (hR : W ℒ₂ = W₁ᗮ) (s : ℝ) :
    gammaMassGen (X := ↥(W₁ᗮ)) s {v : ↥(W₁ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂} =
      Submission.GaussianMeasure.gammaMass s
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂)) := by
  let e : ↥(W₁ᗮ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ₂)) := e2Of ℒ₂ (W₁ := W₁) hR
  have hpre : e ⁻¹' (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂)) =
      {v : ↥(W₁ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂} := by
    have htrans := voronoi_e2_image ℒ₂ (W₁ := W₁) hR
    rw [← htrans]
    exact Set.preimage_image_eq {v : ↥(W₁ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂} (e.injective)
  calc
    gammaMassGen (X := ↥(W₁ᗮ)) s {v : ↥(W₁ᗮ) | (v : E) ∈ Submission.Voronoi.voronoi ℒ₂}
        = gammaMassGen (X := EuclideanSpace ℝ (Fin (Module.finrank ℤ ℒ₂))) s
            (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂)) := by
          rw [← hpre]
          exact (gammaMassGen_transport e s
            (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂))).symm
    _ = Submission.GaussianMeasure.gammaMass s
            (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂)) := by rfl

/-- ambient product identity: the γ-mass of the orthogonal-sum cell factorizes into the
transported cell masses. -/
lemma ambient_sup_cell_product (ℒ₁ ℒ₂ : Submodule ℤ E)
    [DiscreteTopology ℒ₁] [DiscreteTopology ℒ₂]
    (hop : Submission.QuotientLattice.OrthogonalPair ℒ₁ ℒ₂)
    (hR : W ℒ₂ = (W ℒ₁)ᗮ) (s : ℝ) :
    Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi (ℒ₁ ⊔ ℒ₂)) =
      Submission.GaussianMeasure.gammaMass s
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₁)) *
      Submission.GaussianMeasure.gammaMass s
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ₂)) := by
  rw [gamma_sup_cell_split ℒ₁ ℒ₂ hop hR s]
  rw [← gammaMassGen_cell_base_transport ℒ₁ s]
  rw [← gammaMassGen_compl_base_transport ℒ₂ (W₁ := W ℒ₁) hR s]

/-- Uniqueness of the `S ⊕ Sᗮ` decomposition: two decompositions of the same vector agree
in both components. -/
lemma split_orthogonal_unique (S : Submodule ℝ E) (u₁ u₂ : ↥S) (v₁ v₂ : ↥(Sᗮ))
    (h : (u₁ : E) + (v₁ : E) = (u₂ : E) + (v₂ : E)) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  let a : ↥S := u₁ - u₂
  let b : ↥(Sᗮ) := v₁ - v₂
  have haX : (a : E) = (u₁ : E) - (u₂ : E) := by simp [a]
  have hbX : (b : E) = (v₁ : E) - (v₂ : E) := by simp [b]
  have hsum : (a : E) + (b : E) = 0 := by
    rw [haX, hbX]
    calc
      ((u₁ : E) - (u₂ : E)) + ((v₁ : E) - (v₂ : E))
          = ((u₁ : E) + (v₁ : E)) - ((u₂ : E) + (v₂ : E)) := by abel
      _ = 0 := by rw [h]; abel
  rcases (orthogonal_sum_zero S a b hsum) with ⟨ha, hb⟩
  exact ⟨sub_eq_zero.mp (by simpa [a] using ha), sub_eq_zero.mp (by simpa [b] using hb)⟩

/-- the orthogonal-decomposition witness: the `S`-component of `x`. -/
noncomputable def phiOf_symm_w (S : Submodule ℝ E) (x : E) : E :=
  Classical.choose ((inferInstance : S.HasOrthogonalProjection).exists_orthogonal x)

lemma phiOf_symm_w_mem (S : Submodule ℝ E) (x : E) : phiOf_symm_w S x ∈ S :=
  (Classical.choose_spec ((inferInstance : S.HasOrthogonalProjection).exists_orthogonal x)).1

lemma phiOf_symm_xsub_mem (S : Submodule ℝ E) (x : E) :
    x - phiOf_symm_w S x ∈ Sᗮ :=
  (Classical.choose_spec ((inferInstance : S.HasOrthogonalProjection).exists_orthogonal x)).2

/-- the explicit (continuous) inverse of `phiOf S`: `x ↦ (its S-part, its Sᗮ-part)`. -/
noncomputable def phiOf_symm (S : Submodule ℝ E) (x : E) : ↥S × ↥(Sᗮ) :=
  (⟨phiOf_symm_w S x, phiOf_symm_w_mem S x⟩, ⟨x - phiOf_symm_w S x, phiOf_symm_xsub_mem S x⟩)

lemma phiOf_apply_symm (S : Submodule ℝ E) (x : E) :
    (phiOf S (phiOf_symm S x) : E) = x := by
  dsimp [phiOf_symm, phiOf_symm_w, phiOf]
  change (phiOf_symm_w S x) + (x - phiOf_symm_w S x) = x
  abel

lemma phiOf_symm_apply_w (S : Submodule ℝ E) (p : ↥S × ↥(Sᗮ)) :
    (phiOf_symm S ((phiOf S p : E))).1 = p.1 := by
  have hw : phiOf_symm_w S ((phiOf S p : E)) = (p.1 : E) := by
    have hw_mem : phiOf_symm_w S ((phiOf S p : E)) ∈ S := phiOf_symm_w_mem S ((phiOf S p : E))
    have hxu_mem : (phiOf S p : E) - phiOf_symm_w S ((phiOf S p : E)) ∈ Sᗮ :=
      phiOf_symm_xsub_mem S ((phiOf S p : E))
    have huniq := split_orthogonal_unique S
      (⟨phiOf_symm_w S ((phiOf S p : E)), hw_mem⟩ : ↥S) p.1
      (⟨(phiOf S p : E) - phiOf_symm_w S ((phiOf S p : E)), hxu_mem⟩ : ↥(Sᗮ)) p.2
      (by
        dsimp [phiOf]
        change phiOf_symm_w S ((p.1 : E) + (p.2 : E)) +
            ((p.1 : E) + (p.2 : E) - phiOf_symm_w S ((p.1 : E) + (p.2 : E))) =
          (p.1 : E) + (p.2 : E)
        abel)
    simpa using (congrArg (fun z : ↥S => (z : E)) huniq.1)
  dsimp [phiOf_symm]
  apply Subtype.ext
  exact hw

lemma phiOf_symm_apply_v (S : Submodule ℝ E) (p : ↥S × ↥(Sᗮ)) :
    (phiOf_symm S ((phiOf S p : E))).2 = p.2 := by
  have hw_mem : phiOf_symm_w S ((phiOf S p : E)) ∈ S := phiOf_symm_w_mem S ((phiOf S p : E))
  have hxu_mem : (phiOf S p : E) - phiOf_symm_w S ((phiOf S p : E)) ∈ Sᗮ :=
    phiOf_symm_xsub_mem S ((phiOf S p : E))
  have huniq := split_orthogonal_unique S
    (⟨phiOf_symm_w S ((phiOf S p : E)), hw_mem⟩ : ↥S) p.1
    (⟨(phiOf S p : E) - phiOf_symm_w S ((phiOf S p : E)), hxu_mem⟩ : ↥(Sᗮ)) p.2
    (by
      dsimp [phiOf]
      change phiOf_symm_w S ((p.1 : E) + (p.2 : E)) +
          ((p.1 : E) + (p.2 : E) - phiOf_symm_w S ((p.1 : E) + (p.2 : E))) =
        (p.1 : E) + (p.2 : E)
      abel)
  have hv : (phiOf S p : E) - phiOf_symm_w S ((phiOf S p : E)) = (p.2 : E) := by
    exact congrArg (fun z : ↥(Sᗮ) => (z : E)) huniq.2
  dsimp [phiOf_symm]
  apply Subtype.ext
  dsimp [phiOf] at hv
  change (phiOf S p : E) - phiOf_symm_w S ((phiOf S p : E)) = (p.2 : E) at hv
  simpa [phiOf] using hv

lemma phiOf_symm_apply (S : Submodule ℝ E) (p : ↥S × ↥(Sᗮ)) :
    phiOf_symm S ((phiOf S p : E)) = p := by
  apply Prod.ext
  · exact phiOf_symm_apply_w S p
  · exact phiOf_symm_apply_v S p

/-- the `S`-component of `x` via the orthogonal projection (continuous). -/
noncomputable def phiOf_symmP_w (S : Submodule ℝ E) (x : E) : E :=
  (S.orthogonalProjectionOnto x : E)

lemma phiOf_symmP_w_mem (S : Submodule ℝ E) (x : E) : phiOf_symmP_w S x ∈ S :=
  (S.orthogonalProjectionOnto x).2

lemma phiOf_symmP_xsub_mem (S : Submodule ℝ E) (x : E) :
    x - phiOf_symmP_w S x ∈ Sᗮ := by
  have h1 := Submodule.sub_starProjection_mem_orthogonal (K := S) (v := x)
  simpa [phiOf_symmP_w, Submodule.coe_orthogonalProjectionOnto_apply] using h1

/-- the explicit inverse of `phiOf S` via the orthogonal projection. -/
noncomputable def phiOf_symmP (S : Submodule ℝ E) (x : E) : ↥S × ↥(Sᗮ) :=
  (⟨phiOf_symmP_w S x, phiOf_symmP_w_mem S x⟩, ⟨x - phiOf_symmP_w S x, phiOf_symmP_xsub_mem S x⟩)

lemma phiOf_symmP_eq_phiOf_symm (S : Submodule ℝ E) (x : E) :
    phiOf_symmP S x = phiOf_symm S x := by
  apply Prod.ext
  · apply Subtype.ext
    dsimp [phiOf_symmP, phiOf_symm, phiOf_symmP_w, phiOf_symm_w]
    -- carrier equality: P x = w (both the unique S-component of x)
    have hPmem : (phiOf_symmP_w S x) ∈ S := phiOf_symmP_w_mem S x
    have hwmem : phiOf_symm_w S x ∈ S := phiOf_symm_w_mem S x
    have hPxsub : x - phiOf_symmP_w S x ∈ Sᗮ := phiOf_symmP_xsub_mem S x
    have hwxsub : x - phiOf_symm_w S x ∈ Sᗮ := phiOf_symm_xsub_mem S x
    have huniq := split_orthogonal_unique S
      (⟨phiOf_symmP_w S x, hPmem⟩ : ↥S) (⟨phiOf_symm_w S x, hwmem⟩ : ↥S)
      (⟨x - phiOf_symmP_w S x, hPxsub⟩ : ↥(Sᗮ)) (⟨x - phiOf_symm_w S x, hwxsub⟩ : ↥(Sᗮ))
      (by simp)
    exact congrArg (fun z : ↥S => (z : E)) huniq.1
  · apply Subtype.ext
    dsimp [phiOf_symmP, phiOf_symm, phiOf_symmP_w, phiOf_symm_w]
    have hPmem : (phiOf_symmP_w S x) ∈ S := phiOf_symmP_w_mem S x
    have hwmem : phiOf_symm_w S x ∈ S := phiOf_symm_w_mem S x
    have hPxsub : x - phiOf_symmP_w S x ∈ Sᗮ := phiOf_symmP_xsub_mem S x
    have hwxsub : x - phiOf_symm_w S x ∈ Sᗮ := phiOf_symm_xsub_mem S x
    have huniq := split_orthogonal_unique S
      (⟨phiOf_symmP_w S x, hPmem⟩ : ↥S) (⟨phiOf_symm_w S x, hwmem⟩ : ↥S)
      (⟨x - phiOf_symmP_w S x, hPxsub⟩ : ↥(Sᗮ)) (⟨x - phiOf_symm_w S x, hwxsub⟩ : ↥(Sᗮ))
      (by simp)
    exact congrArg (fun z : ↥(Sᗮ) => (z : E)) huniq.2

lemma phiOf_symmP_apply_symm (S : Submodule ℝ E) (x : E) :
    (phiOf S (phiOf_symmP S x) : E) = x := by
  rw [phiOf_symmP_eq_phiOf_symm S x]
  exact phiOf_apply_symm S x

lemma phiOf_symmP_symm_apply (S : Submodule ℝ E) (p : ↥S × ↥(Sᗮ)) :
    phiOf_symmP S ((phiOf S p : E)) = p := by
  rw [phiOf_symmP_eq_phiOf_symm S ((phiOf S p : E))]
  exact phiOf_symm_apply S p

lemma continuous_phiOf (S : Submodule ℝ E) : Continuous (phiOf S) := by
  have h1 : Continuous (fun p : ↥S × ↥(Sᗮ) => (p.1 : E)) := continuous_subtype_val.comp continuous_fst
  have h2 : Continuous (fun p : ↥S × ↥(Sᗮ) => (p.2 : E)) := continuous_subtype_val.comp continuous_snd
  change Continuous (fun p : ↥S × ↥(Sᗮ) => (p.1 : E) + (p.2 : E))
  exact h1.add h2

lemma continuous_phiOf_symmP (S : Submodule ℝ E) : Continuous (phiOf_symmP S) := by
  unfold phiOf_symmP
  refine Continuous.prodMk ?_ ?_
  · change Continuous (⇑S.orthogonalProjectionOnto)
    exact S.orthogonalProjectionOnto.continuous
  · exact Continuous.subtype_mk
      (continuous_id.sub (continuous_subtype_val.comp S.orthogonalProjectionOnto.continuous))
      (fun x => phiOf_symmP_xsub_mem S x)

noncomputable def phiOfHomeo (S : Submodule ℝ E) : ↥S × ↥(Sᗮ) ≃ₜ E where
  toEquiv := {
    toFun := phiOf S
    invFun := phiOf_symmP S
    left_inv := phiOf_symmP_symm_apply S
    right_inv := phiOf_symmP_apply_symm S }
  continuous_toFun := continuous_phiOf S
  continuous_invFun := continuous_phiOf_symmP S

/-- 1b: the ambient interior of the orthogonal sum of two sets is the sum of the subspace
interiors (via the split homeomorphism). -/
lemma interior_sum_eq (S : Submodule ℝ E) (C₁ : Set (↥S)) (C₂ : Set (↥(Sᗮ))) :
    interior {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x} =
      {x : E | ∃ u ∈ interior C₁, ∃ v ∈ interior C₂, (u : E) + (v : E) = x} := by
  have hsum (A : Set (↥S)) (B : Set (↥(Sᗮ))) :
      {x : E | ∃ u ∈ A, ∃ v ∈ B, (u : E) + (v : E) = x} = (phiOf S) '' (A ×ˢ B) := by
    exact sumSet_eq_image S A B
  calc
    interior {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x}
        = interior ((phiOf S) '' (C₁ ×ˢ C₂)) := by rw [hsum C₁ C₂]
    _ = (phiOf S) '' (interior (C₁ ×ˢ C₂)) := by
        exact (Homeomorph.image_interior (phiOfHomeo S) (C₁ ×ˢ C₂)).symm
    _ = (phiOf S) '' (interior C₁ ×ˢ interior C₂) := by
        rw [interior_prod_eq]
    _ = {x : E | ∃ u ∈ interior C₁, ∃ v ∈ interior C₂, (u : E) + (v : E) = x} := by
        rw [hsum (interior C₁) (interior C₂)]

/-- 1c: the Sᗮ-component of a point of the interior of the orthogonal sum lies in the
interior of the second summand. -/
lemma interior_sum_component (S : Submodule ℝ E) (C₁ : Set (↥S)) (C₂ : Set (↥(Sᗮ)))
    {x : E} (hx : x ∈ interior {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x}) :
    (phiOf_symmP S x).2 ∈ interior C₂ := by
  rw [interior_sum_eq S C₁ C₂] at hx
  rcases hx with ⟨u, hu, v, hv, hxuv⟩
  have hφ : phiOf S (u, v) = x := by
    dsimp [phiOf]
    exact hxuv
  have hx2 : (phiOf_symmP S x).2 = v := by
    calc
      (phiOf_symmP S x).2 = (phiOf_symmP S (phiOf S (u, v))).2 := by rw [hφ]
      _ = ((u, v) : ↥S × ↥(Sᗮ)).2 := by rw [phiOf_symmP_symm_apply S (u, v)]
      _ = v := rfl
  rw [hx2]
  exact hv

/-- 1c (dual): the S-component lies in the interior of the first summand. -/
lemma interior_sum_component₁ (S : Submodule ℝ E) (C₁ : Set (↥S)) (C₂ : Set (↥(Sᗮ)))
    {x : E} (hx : x ∈ interior {x : E | ∃ u ∈ C₁, ∃ v ∈ C₂, (u : E) + (v : E) = x}) :
    (phiOf_symmP S x).1 ∈ interior C₁ := by
  rw [interior_sum_eq S C₁ C₂] at hx
  rcases hx with ⟨u, hu, v, hv, hxuv⟩
  have hφ : phiOf S (u, v) = x := by
    dsimp [phiOf]
    exact hxuv
  have hx1 : (phiOf_symmP S x).1 = u := by
    calc
      (phiOf_symmP S x).1 = (phiOf_symmP S (phiOf S (u, v))).1 := by rw [hφ]
      _ = ((u, v) : ↥S × ↥(Sᗮ)).1 := by rw [phiOf_symmP_symm_apply S (u, v)]
      _ = u := rfl
  rw [hx1]
  exact hu

/-- The quotient-landing helper: for `y : ℒ`, the W₁ᗮ-component of `y` (via the orthogonal
split of `realSpan ℒ₁`) lies in `quotLattice ℒ (realSpan ℒ₁)`. -/
lemma phiOf_symmP_component_mem_quotLattice (ℒ₁ ℒ : Submodule ℤ E) (y : ℒ) :
    (((phiOf_symmP (W ℒ₁) (y : E)).2 : ↥((W ℒ₁)ᗮ)) : E) ∈
      Submission.QuotientLattice.quotLattice ℒ (W ℒ₁) := by
  let S : Submodule ℝ E := W ℒ₁
  have h1 : (((phiOf_symmP S (y : E)).2 : ↥(Sᗮ)) : E) =
      (y : E) - S.starProjection (y : E) := by
    dsimp [phiOf_symmP]
    simpa [phiOf_symmP_w, Submodule.coe_orthogonalProjectionOnto_apply]
  have h2 : (y : E) - S.starProjection (y : E) = Sᗮ.starProjection (y : E) := by
    exact (Submodule.starProjection_orthogonal_val (K := S) (u := (y : E))).symm
  have hcar : (((phiOf_symmP S (y : E)).2 : ↥(Sᗮ)) : E) = Sᗮ.starProjection (y : E) := h1.trans h2
  rw [Submission.QuotientLattice.quotLattice]
  rw [Submodule.mem_map]
  refine ⟨(y : E), y.2, ?_⟩
  change Sᗮ.starProjection (y : E) = (((phiOf_symmP S (y : E)).2 : ↥(Sᗮ)) : E)
  exact hcar.symm

end AmbientSum

end Submission.FundBody
