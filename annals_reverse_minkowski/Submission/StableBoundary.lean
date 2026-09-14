import Mathlib
import Submission.Boundary
import Submission.Transport
import Submission.SubLattice
import Submission.MainStable

open Module Real
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-!
# [B-ii] structure-package interface: from a stable boundary pair to the γ-bound

The `gamma_stable_of_two_le` boundary case (paper Prop. 7.2) will be fed, by the boundary-
structure theorem of the stable-lattice geometry (Mahler compactness + the boundary
characterization), a primitive stable sublattice `ℒ' ≤ ℒ` of rank `d ∈ (0, m)` whose
quotient `Q := quotLattice ℒ (realSpan ℒ')` (rank `m − d`) is also stable, together with
discreteness of `Q` and of `ℒ' ⊔ Q`.

This module proves the closing interface lemma `boundary_gamma_of_stable_pair`: from those
outputs and the strong per-rank induction hypothesis `ih`, the full γ-lower-bound
`2/3 ≤ γ_{1/t m}(V(ℒ))` follows.  The internally-derived structural facts (which the
boundary-structure theorem does NOT need to hand us) are:

* `hop : OrthogonalPair ℒ' Q`  — `ℒ' ⊆ realSpan ℒ'`, `Q ⊆ (realSpan ℒ')ᗮ`;
* `hR : realSpan Q = (realSpan ℒ')ᗮ` — the quotient is full-rank in the complement
  (`finrank` counting: `finrank ℝ (realSpan Q) = finrank ℤ Q = m − finrank ℤ ℒ'`
  equals `finrank ℝ ((realSpan ℒ')ᗮ)` by `Submodule.finrank_add_finrank_orthogonal`);
* `hΛz : IsZLattice ℝ (ℒ' ⊔ Q)` — every ambient point is the sum of a `realSpan ℒ'`-part
  and a `realSpan Q`-part (orthogonal decomposition), both lying in `span ℝ (ℒ' ⊔ Q)`.

With these, `Boundary.boundary_gamma_bound` (already proven) yields the conclusion.  The
still-open [B-ii] pieces (future sessions): (i) the topology/compactness of the family of
stable lattices and continuity of `ℒ ↦ γ_{1/t}(V(ℒ))`, giving the existence of a global
minimizer of the γ-value among stable lattices; (ii) the boundary-structure theorem: a
global minimizer that is not an interior point of the determinant-one manifold has a
primitive stable `ℒ'` with stable quotient (supplying the hypotheses of
`boundary_gamma_of_stable_pair`); (iii) the interior branch = isotropic Gaussian position
(`minima_have_mass`); then `gamma_stable_of_two_le` assembles as: interior ⇒
`isotropic_mass ≥ 2/3`; boundary ⇒ `boundary_gamma_of_stable_pair`; `boundary_gamma_bound`
in turn is fed by `ambient_wins` (both PROVEN in `Submission/Boundary.lean`).
-/

noncomputable section
namespace Submission.StableBoundary

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- `ℒ'` is orthogonal to its quotient: `ℒ' ⊆ realSpan ℒ'` and
`quotLattice ℒ (realSpan ℒ') ⊆ (realSpan ℒ')ᗮ`. -/
lemma orthogonalPair_quotLattice (ℒ ℒ' : Submodule ℤ E) :
    Submission.QuotientLattice.OrthogonalPair ℒ'
      (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ')) := by
  intro x hx y hy
  have hxS : x ∈ (Submission.QuotientLattice.realSpan ℒ' : Submodule ℝ E) := by
    exact Submodule.subset_span hx
  have hyperp : y ∈ ((Submission.QuotientLattice.realSpan ℒ')ᗮ : Submodule ℝ E) := by
    have hle := Submission.QuotientLattice.quotLattice_le_orthogonal ℒ
      (Submission.QuotientLattice.realSpan ℒ')
    -- hle : quotLattice ℒ (realSpan ℒ') ≤ (realSpan ℒ')ᗮ.restrictScalars ℤ
    exact hle hy
  exact (Submodule.mem_orthogonal (Submission.QuotientLattice.realSpan ℒ') y).mp hyperp x hxS

/-- The real span of the quotient is the whole orthogonal complement (the quotient is
full-rank there): containment `⊆` from `quotLattice_le_orthogonal`, equality of dimensions
from the rank hypothesis `hfinQ`. -/
lemma realSpan_quotLattice_eq_orthogonal (ℒ ℒ' : Submodule ℤ E)
    [DiscreteTopology ℒ'] [DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))]
    (hfinQ : Module.finrank ℤ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) = m - Module.finrank ℤ ℒ') :
    Submission.QuotientLattice.realSpan (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ')) = (Submission.QuotientLattice.realSpan ℒ')ᗮ := by
  classical
  let Q : Submodule ℤ E := Submission.QuotientLattice.quotLattice ℒ
    (Submission.QuotientLattice.realSpan ℒ')
  let S : Submodule ℝ E := Submission.QuotientLattice.realSpan ℒ'
  have hRQ_le : Submission.QuotientLattice.realSpan Q ≤ Sᗮ := by
    dsimp [S]
    apply Submodule.span_le.mpr
    intro x hx
    have hle := Submission.QuotientLattice.quotLattice_le_orthogonal ℒ
      (Submission.QuotientLattice.realSpan ℒ')
    simpa [Q] using hle hx
  have hdimU : Module.finrank ℝ (Submission.QuotientLattice.realSpan Q) = Module.finrank ℤ Q := by
    exact Submission.Transport.realSpan_finrank Q
  have hdimV : Module.finrank ℝ (Sᗮ) = m - Module.finrank ℤ ℒ' := by
    have hadd := S.finrank_add_finrank_orthogonal
    have hE : Module.finrank ℝ E = m := by simp
    have hdimS : Module.finrank ℝ S = Module.finrank ℤ ℒ' := by
      dsimp [S]
      exact Submission.Transport.realSpan_finrank ℒ'
    rw [hE, hdimS] at hadd
    omega
  have hfinQ' : Module.finrank ℤ Q = m - Module.finrank ℤ ℒ' := by
    dsimp [Q]
    exact hfinQ
  have hdims : Module.finrank ℝ (Submission.QuotientLattice.realSpan Q) =
      Module.finrank ℝ (Sᗮ) := by
    rw [hdimU, hdimV, hfinQ']
  have hR : Submission.QuotientLattice.realSpan Q = Sᗮ := by
    exact Submodule.eq_of_le_of_finrank_eq hRQ_le hdims
  simpa [Q, S, Submission.QuotientLattice.realSpan] using hR



/-- The ambient is spanned by the real spans of the two orthogonal factors: for every
point `x`, its orthogonal decomposition `w + (x−w)` has both parts in
`span ℝ (ℒ' ⊔ Q)` (from `hR`, the complement part is in `realSpan Q`). -/
lemma isZLattice_sup_quotLattice (ℒ ℒ' : Submodule ℤ E)
    (hΛd : DiscreteTopology ((ℒ' ⊔ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))) : Submodule ℤ E))
    (hR : Submission.QuotientLattice.realSpan (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ')) = (Submission.QuotientLattice.realSpan ℒ')ᗮ) :
    IsZLattice ℝ (ℒ' ⊔ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))) := by
  classical
  haveI : DiscreteTopology ((ℒ' ⊔ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))) : Submodule ℤ E) := hΛd
  constructor
  let Q : Submodule ℤ E := Submission.QuotientLattice.quotLattice ℒ
    (Submission.QuotientLattice.realSpan ℒ')
  let S : Submodule ℝ E := Submission.QuotientLattice.realSpan ℒ'
  let Λ : Submodule ℤ E := ℒ' ⊔ Q
  -- span ℝ ((ℒ' ⊔ Q) : Set E) = ⊤: every point is the sum of an S-part and an
  -- (Sᗮ = realSpan Q)-part, both inside the span of the sup.
  apply le_antisymm
  · exact le_top
  · intro x hx
    rcases (inferInstance : S.HasOrthogonalProjection).exists_orthogonal x with ⟨w, hwS, hwper⟩
    have hspan1 : (w : E) ∈ Submodule.span ℝ ((Λ : Submodule ℤ E) : Set E) := by
      have hle1 : S ≤ Submodule.span ℝ ((Λ : Submodule ℤ E) : Set E) := by
        dsimp [S]
        exact Submodule.span_mono (SetLike.coe_subset_coe.mpr (le_sup_left : ℒ' ≤ ℒ' ⊔ Q))
      exact hle1 hwS
    have hspan2 : (x - w) ∈ Submodule.span ℝ ((Λ : Submodule ℤ E) : Set E) := by
      have hv : x - w ∈ Sᗮ := hwper
      have hvQ : x - w ∈ Submission.QuotientLattice.realSpan Q := by
        dsimp [Q, S] at hv ⊢
        rw [hR]
        exact hv
      have hle2 : Submission.QuotientLattice.realSpan Q ≤
          Submodule.span ℝ ((Λ : Submodule ℤ E) : Set E) := by
        dsimp [S, Q, Λ]
        exact Submodule.span_mono (SetLike.coe_subset_coe.mpr (le_sup_right : Q ≤ ℒ' ⊔ Q))
      exact hle2 hvQ
    have hxmem : x ∈ Submodule.span ℝ ((Λ : Submodule ℤ E) : Set E) := by
      have h : w + (x - w) = x := by abel
      rw [← h]
      exact Submodule.add_mem _ hspan1 hspan2
    simpa [Λ, Q, Submission.QuotientLattice.realSpan] using hxmem

/-- **Closing interface of the boundary case.**  Given the full-rank host `ℒ`, a primitive
stable sublattice `ℒ'` with stable quotient `Q := quotLattice ℒ (realSpan ℒ')` (rank
`m − finrank ℤ ℒ'`), discreteness of `Q` and `ℒ' ⊔ Q`, and the strong induction hypothesis
`ih` over all ranks `< m` (transported cells), the Voronoi cell of `ℒ` has Gaussian mass
`≥ 2/3` at `1/t m`. -/
theorem boundary_gamma_of_stable_pair (m : ℕ) (hm : 2 ≤ m)
    (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ]
    (hfinL : Module.finrank ℤ ℒ = m)
    (ℒ' : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ']
    (hr1L' : 1 ≤ Module.finrank ℤ ℒ') (hrmL' : Module.finrank ℤ ℒ' < m)
    (hStL' : Submission.StableLattices.Stable ℒ')
    (hQd : DiscreteTopology ((Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) : Submodule ℤ (EuclideanSpace ℝ (Fin m))))
    (hfinQ : Module.finrank ℤ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) = m - Module.finrank ℤ ℒ')
    (hStQ : Submission.StableLattices.Stable (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')))
    (hp : Submission.QuotientLattice.Primitive ℒ' ℒ)
    (hΛd : DiscreteTopology ((ℒ' ⊔ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))) : Submodule ℤ (EuclideanSpace ℝ (Fin m))))
    (ih : ∀ (r : ℕ), r < m → ∀ (ℒd : Submodule ℤ (EuclideanSpace ℝ (Fin r)))
      [DiscreteTopology ℒd], Submission.StableLattices.Stable ℒd →
      Module.finrank ℤ ℒd = r →
      (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t r)
        (Submission.Voronoi.voronoi ℒd)) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
      (Submission.Voronoi.voronoi ℒ) := by
  classical
  have hℒ : IsZLattice ℝ ℒ := Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfinL
  haveI : DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) := hQd
  haveI : DiscreteTopology (Submission.Transport.transLattice ℒ') :=
    Submission.Transport.transLattice_discrete ℒ'
  haveI : DiscreteTopology (Submission.Transport.transLattice
      (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ'))) :=
    Submission.Transport.transLattice_discrete (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))
  have hop : Submission.QuotientLattice.OrthogonalPair ℒ' (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) :=
    orthogonalPair_quotLattice (m := m) ℒ ℒ'
  have hR : Submission.QuotientLattice.realSpan (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ')) = (Submission.QuotientLattice.realSpan ℒ')ᗮ :=
    realSpan_quotLattice_eq_orthogonal (m := m) ℒ ℒ' hfinQ
  have hΛz : IsZLattice ℝ (ℒ' ⊔ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))) :=
    isZLattice_sup_quotLattice (m := m) ℒ ℒ' hΛd hR
  have hrmQ : Module.finrank ℤ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) < m := by
    rw [hfinQ]
    omega
  have ihL' : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass
      (1 / Submission.MainStable.t (Module.finrank ℤ ℒ'))
      (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ')) := by
    exact ih (Module.finrank ℤ ℒ') hrmL' (Submission.Transport.transLattice ℒ')
      (Submission.Transport.stable_of_stable_transported ℒ' hStL')
      (Submission.Transport.finrank_transLattice ℒ')
  have ihQ : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass
      (1 / Submission.MainStable.t (Module.finrank ℤ
        (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ'))))
      (Submission.Voronoi.voronoi (Submission.Transport.transLattice
        (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ')))) := by
    exact ih (Module.finrank ℤ (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ'))) hrmQ
      (Submission.Transport.transLattice (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ')))
      (Submission.Transport.stable_of_stable_transported
        (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ'))
        hStQ)
      (Submission.Transport.finrank_transLattice (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ')))
  exact Submission.Boundary.boundary_gamma_bound (m := m) (hm := hm) (ℒ := ℒ)
    (hfinL := hfinL) (ℒ' := ℒ') (hr1L' := hr1L') (hrmL' := hrmL') (hStL' := hStL')
    (hQd := hQd) (hfinQ := hfinQ) (hStQ := hStQ) (hp := hp) (hΛd := hΛd)
    (hΛz := hΛz) (hop := hop) (hR := hR) (ihL' := ihL') (ihQ := ihQ)


/-! ## Boundary-branch interface: a strict primitive det-one sublattice

Paper Prop. 4.1 (vi): a stable lattice is on the *boundary* of the stable set exactly
when it has a strict primitive sublattice of determinant one; such a sublattice and its
quotient are then automatically stable.  The three lemmas below extract the
`boundary_gamma_of_stable_pair` interface from a primitive det-one sublattice of a stable
full-rank host. -/

/-- det-one quotient from det-one primitive sublattice of a stable host. -/
lemma det_quotLattice_of_det_one (ℒ' ℒ : Submodule ℤ E) [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hSt : Submission.StableLattices.Stable ℒ) (hle : ℒ' ≤ ℒ)
    (hp : Submission.QuotientLattice.Primitive ℒ' ℒ)
    (hdetL' : ReverseMinkowski.determinant ℒ' = 1)
    [DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))] :
    ReverseMinkowski.determinant (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) = 1 := by
  classical
  rw [Submission.SubLattice.determinant_quot_generic (nA := m) (ℒ' := ℒ') (ℒ := ℒ)
    (Submission.QuotientLattice.realSpan ℒ') rfl hp]
  rw [Submission.StableLattices.det_eq_one_of_stable hSt, hdetL']
  norm_num

/-- The quotient of a stable host by a det-one primitive sublattice is stable. -/
lemma stable_quotLattice_of_det_one (ℒ' ℒ : Submodule ℤ E) [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hSt : Submission.StableLattices.Stable ℒ) (hle : ℒ' ≤ ℒ)
    (hp : Submission.QuotientLattice.Primitive ℒ' ℒ)
    (hdetL' : ReverseMinkowski.determinant ℒ' = 1)
    [DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))] :
    Submission.StableLattices.Stable (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) := by
  classical
  constructor
  · exact det_quotLattice_of_det_one ℒ' ℒ hSt hle hp hdetL'
  · intro N₀ hN₀le hdTN₀
    haveI : DiscreteTopology N₀ := hdTN₀
    let M : Submodule ℤ E := Submission.Filtration.interLattice ℒ (Submission.QuotientLattice.realSpan ℒ') N₀
    have hMle : M ≤ ℒ := by
      dsimp [M]
      exact Submission.Filtration.interLattice_le ℒ (Submission.QuotientLattice.realSpan ℒ') N₀
    haveI : DiscreteTopology M := by
      dsimp [M]
      exact Submission.LatticeBasics.discreteTopology_of_le (ℒ := ℒ)
        (ℒ' := Submission.Filtration.interLattice ℒ (Submission.QuotientLattice.realSpan ℒ') N₀)
        (Submission.Filtration.interLattice_le ℒ (Submission.QuotientLattice.realSpan ℒ') N₀)
    have hdetMge : 1 ≤ ReverseMinkowski.determinant M := by
      exact (Submission.StableLattices.all_subdet_ge_one_of_stable hSt) M hMle
    have hdetM : ReverseMinkowski.determinant M =
        ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant N₀ := by
      dsimp [M]
      exact Submission.Filtration.det_intermediate_mul (ℒ' := ℒ') (ℒ := ℒ)
        (Submission.QuotientLattice.realSpan ℒ') rfl hp (M' := N₀) hN₀le
    have hN₀eq : ReverseMinkowski.determinant N₀ = ReverseMinkowski.determinant M := by
      rw [hdetM, hdetL']
      ring
    rw [hN₀eq]
    exact hdetMge

/-- **Boundary-branch interface.**  A strict primitive det-one sublattice of a stable
full-rank host supplies every hypothesis of `boundary_gamma_of_stable_pair`, hence the
per-rank induction hypothesis gives `2/3 ≤ γ_{1/t m}(V(ℒ))`. -/
theorem boundary_gamma_of_primitive_det_one (hm : 2 ≤ m)
    (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (hStL : Submission.StableLattices.Stable ℒ) (hfinL : Module.finrank ℤ ℒ = m)
    (ℒ' : Submodule ℤ E) [DiscreteTopology ℒ']
    (hle : ℒ' ≤ ℒ) (hp : Submission.QuotientLattice.Primitive ℒ' ℒ)
    (hdetL' : ReverseMinkowski.determinant ℒ' = 1)
    (hr1L' : 1 ≤ Module.finrank ℤ ℒ') (hrmL' : Module.finrank ℤ ℒ' < m)
    (ih : ∀ (r : ℕ), r < m → ∀ (ℒd : Submodule ℤ (EuclideanSpace ℝ (Fin r)))
      [DiscreteTopology ℒd], Submission.StableLattices.Stable ℒd →
      Module.finrank ℤ ℒd = r →
      (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t r)
        (Submission.Voronoi.voronoi ℒd)) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
      (Submission.Voronoi.voronoi ℒ) := by
  classical
  have hQd : DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) :=
    Submission.QuotientLattice.discrete_quotLattice (ℒ' := ℒ') (ℒ := ℒ)
      (Submission.QuotientLattice.realSpan ℒ') rfl hp
  haveI : DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) := hQd
  have hStL' : Submission.StableLattices.Stable ℒ' :=
    Submission.StableLattices.stable_of_det_one_le hStL hle hdetL'
  have hdetQ : ReverseMinkowski.determinant (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) = 1 :=
    det_quotLattice_of_det_one ℒ' ℒ hStL hle hp hdetL'
  have hStQ : Submission.StableLattices.Stable (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) :=
    stable_quotLattice_of_det_one ℒ' ℒ hStL hle hp hdetL'
  have hfinQ : Module.finrank ℤ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) = m - Module.finrank ℤ ℒ' := by
    have hf : Module.finrank ℤ (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ')) =
        Module.finrank ℤ ℒ - Module.finrank ℤ ℒ' :=
      Submission.Filtration.finrank_quotLattice (ℒ' := ℒ') (ℒ := ℒ)
        (Submission.QuotientLattice.realSpan ℒ') rfl hp
    rwa [hfinL] at hf
  have hop : Submission.QuotientLattice.OrthogonalPair ℒ'
      (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ')) :=
    orthogonalPair_quotLattice ℒ ℒ'
  have hΛd : DiscreteTopology ((ℒ' ⊔ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))) : Submodule ℤ E) := by
    change DiscreteTopology (Submission.QuotientLattice.supMod ℒ'
      (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ')))
    exact Submission.QuotientLattice.discrete_supMod hop
  exact boundary_gamma_of_stable_pair (m := m) (hm := hm) (ℒ := ℒ)
    (hfinL := hfinL) (ℒ' := ℒ') (hr1L' := hr1L') (hrmL' := hrmL') (hStL' := hStL')
    (hQd := hQd) (hfinQ := hfinQ) (hStQ := hStQ) (hp := hp) (hΛd := hΛd) (ih := ih)

end Submission.StableBoundary
