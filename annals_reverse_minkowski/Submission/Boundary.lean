import Mathlib
import Submission.MainStable
import Submission.Transport
import Submission.QuotientLattice
import Submission.Poisson
import Submission.Disjointness
import Submission.MonoWinsVol
import Submission.FundBody
import Submission.SubLattice
import Submission.Filtration
import Submission.Concentration

open Module Real MeasureTheory
open scoped Real BigOperators Pointwise ENNReal NNReal InnerProductSpace RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-!
# [C]-final: the ambient fundamental-product comparison (`Boundary.ambient_wins`)

For the boundary branch of the rank-`m ≥ 2` induction step of `gamma_stable`
(paper Prop. 7.2 / §5), let `ℒ` be the full-rank host lattice, `ℒ₁ ≤ ℒ` a primitive
sublattice with quotient `Q := quotLattice ℒ (realSpan ℒ₁)` (realized inside the
orthogonal complement of `realSpan ℒ₁`).  The comparison engine

    γ_s(V(ℒ))  ≥  γ_s(V(transLattice Q)) · γ_s(V(transLattice ℒ₁))      (`ambient_wins`)

holds for any common parameter `s > 0`, under the structural hypotheses
`hp : Primitive ℒ₁ ℒ`, `hop : OrthogonalPair ℒ₁ Q`, `hR : realSpan Q = (realSpan ℒ₁)ᗮ`,
full-rankness of `ℒ` and `ℒ₁ ⊔ Q` (`hℒ`, `hΛz`), and discreteness of the composite
objects (`hΛd`, `hQd`).

Proof chain (see the Blueprint's [C] plan):
  (1) `K := V(ℒ₁ ⊔ Q)` is a fundamental body of the host lattice `ℒ`:
      translate-disjointness `hKdisj := Disjointness.voronoi_interior_disjoint` and volume
      `volume K = volume (VC ℒ)` (from `det(ℒ₁ ⊔ Q) = det ℒ₁ · det Q = det ℒ` via
      `Filtration.det_sup_orthogonal` + `SubLattice.determinant_quot_generic`, lifted to
      ENNReal volumes through the Poisson `voronoi_volume_eq_det` identity);
  (2) `Cvp.monotone_voronoi_wins_of_vol` with `F := Cvp.gaussianF u` (`u := 1/s`) gives
      `γ_s(K) ≤ γ_s(V(ℒ))` (identity `γ_s = ∫ gaussianF (1/s)`, proved below);
  (3) `FundBody.ambient_sup_cell_product` factorizes `γ_s(K)` into the two transported
      cell masses.

All discreteness/full-rank facts on composite submodule terms are EXPLICIT hypotheses
(typeclass binders on such terms fail to elaborate); `Countable` of `ℒ` and `ℒ₁ ⊔ Q`
follow from full-rankness via `instCountable_of_discrete_submodule`.
-/

noncomputable section
namespace Submission.Boundary

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "W" => Submission.QuotientLattice.realSpan
local notation "VC" => Submission.Voronoi.voronoi
local notation "γ" => Submission.GaussianMeasure.gammaMass

/-! ## Volume plumbing helpers -/

/-- The Voronoi cell of a full-rank (IsZLattice) lattice has finite volume: it is a
fundamental domain, and any fundamental domain of a full-rank lattice has the volume of a
bounded fundamental parallelepiped. -/
lemma voronoi_volume_lt_top {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) : volume (VC ℒ : Set E) < ⊤ := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Countable ℒ := instCountable_of_discrete_submodule ℒ
  haveI : MeasurableConstVAdd ℒ E := ⟨fun g => by
    change Measurable (fun x : E => (g : E) + x)
    exact (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure ℒ E volume := ⟨fun g s hs => by
    simpa using (measurePreserving_add_left (μ := (volume : Measure E)) (g : E) s hs)⟩
  let b₀ : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ ℒ := Module.finBasis ℤ ℒ
  let β : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℝ E := b₀.ofZLatticeBasis ℝ ℒ
  have hV : IsAddFundamentalDomain ℒ (VC ℒ : Set E) :=
    Submission.VoronoiMeasure.isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ
  have hP : IsAddFundamentalDomain ℒ (ZSpan.fundamentalDomain β : Set E) :=
    ZLattice.isAddFundamentalDomain b₀ volume
  have hvol : volume (VC ℒ : Set E) = volume (ZSpan.fundamentalDomain β) :=
    IsAddFundamentalDomain.measure_eq hV hP
  have hfin : volume (ZSpan.fundamentalDomain β) < ⊤ :=
    Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded β)
  exact hvol ▸ hfin

/-- Two sets of equal real volume and finite measure have equal measure. -/
lemma measure_eq_of_measureReal_eq {A B : Set E}
    (h : MeasureTheory.volume.real A = MeasureTheory.volume.real B)
    (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) : volume A = volume B := by
  have htoA : (volume A).toReal = (volume B).toReal := by
    simpa [MeasureTheory.measureReal_def] using h
  calc
    volume A = ENNReal.ofReal (volume A).toReal := (ENNReal.ofReal_toReal hA).symm
    _ = ENNReal.ofReal (volume B).toReal := by rw [htoA]
    _ = volume B := ENNReal.ofReal_toReal hB

/-! ## Gaussian scale identities -/

/-- `γ_{1/t}(K) = ∫_K gaussianF t` where `gaussianF t x = t^m · exp(−π (t‖x‖)²)` and
`m` is the ambient dimension. -/
lemma gammaMass_inv_eq_gaussianF_integral (t : ℝ) (ht : 0 < t) (K : Set E) :
    γ (1 / t) K = ∫ x in K, Submission.Cvp.gaussianF t x := by
  classical
  have htn : t ≠ 0 := ne_of_gt ht
  have hm : Module.finrank ℝ E = m := by simp
  let f : E → ℝ := fun x => rexp (-Real.pi * ‖x‖ ^ 2)
  have hγ : γ (1 / t) K = ∫ x in (t • K), f x := by
    simpa [f] using (Submission.GaussianMeasure.gammaMass_inv_smul_set (n := m) t htn K)
  have hcomp := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure E))
    (f := f) (R := t) (s := K) ht
  have hJ : ∫ x in (t • K), f x = (t : ℝ) ^ m * ∫ x in K, f (t • x) := by
    have hI : (∫ x in K, f (t • x)) = (t ^ Module.finrank ℝ E)⁻¹ * ∫ x in (t • K), f x := by
      simpa [smul_eq_mul] using hcomp
    rw [hm] at hI
    calc
      ∫ x in (t • K), f x = (t : ℝ) ^ m * (((t : ℝ) ^ m)⁻¹ * ∫ x in (t • K), f x) := by
        field_simp [pow_ne_zero m htn]
      _ = (t : ℝ) ^ m * ∫ x in K, f (t • x) := by rw [← hI]
  have hfun : (fun x : E => (t : ℝ) ^ m * f (t • x)) = fun x : E => Submission.Cvp.gaussianF t x := by
    funext x
    dsimp [f, Submission.Cvp.gaussianF]
    congr 1
    congr 1
    have hnorm : ‖t • x‖ = t * ‖x‖ := by
      rw [norm_smul]
      congr 1
      exact abs_of_nonneg ht.le
    rw [hnorm]
  calc
    γ (1 / t) K = ∫ x in (t • K), f x := hγ
    _ = (t : ℝ) ^ m * ∫ x in K, f (t • x) := hJ
    _ = ∫ x in K, (t : ℝ) ^ m * f (t • x) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ∫ x in K, Submission.Cvp.gaussianF t x := by rw [hfun]

/-- `γ_s(K) = ∫_K gaussianF (1/s)` for `s > 0`. -/
lemma gammaMass_eq_gaussianF_integral (s : ℝ) (hs : 0 < s) (K : Set E) :
    γ s K = ∫ x in K, Submission.Cvp.gaussianF (1 / s) x := by
  have hu : 0 < 1 / s := one_div_pos.mpr hs
  have hs_eq : s = 1 / (1 / s) := by field_simp [ne_of_gt hs]
  calc
    γ s K = γ (1 / (1 / s)) K := congrArg (fun z : ℝ => γ z K) hs_eq
    _ = ∫ x in K, Submission.Cvp.gaussianF (1 / s) x :=
      gammaMass_inv_eq_gaussianF_integral (1 / s) hu K

/-! ## Measurability / integrability of the Gaussian along `psiCan` -/

/-- The canonical closest-vector map `psiCan hℒ` is measurable: on each (open) cell it is a
translation, and outside the union of the cells it is the identity. -/
lemma psiCan_measurable {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [Countable ℒ]
    (hℒ : IsZLattice ℝ ℒ) : Measurable (Submission.Cvp.psiCan hℒ) := by
  classical
  change ∀ ⦃s : Set E⦄, MeasurableSet s → MeasurableSet ((Submission.Cvp.psiCan hℒ) ⁻¹' s)
  intro B hB
  let U : Set E := Set.iUnion (fun y : ℒ => Submission.Cvp.openCell y)
  have hUmeas : MeasurableSet U := by
    dsimp [U]
    exact MeasurableSet.iUnion (fun y : ℒ => (Submission.Cvp.openCell_isOpen y).measurableSet)
  have hOnC : ∀ x : E, x ∈ Uᶜ → Submission.Cvp.psiCan hℒ x = x := by
    intro x hxC
    apply Submission.Cvp.psiCan_eq_self
    intro hxU
    exact hxC (Set.mem_iUnion.mpr (Set.mem_iUnion.mp hxU))
  have hOnCell (y : ℒ) (x : E) (hx : x ∈ Submission.Cvp.openCell y) :
      Submission.Cvp.psiCan hℒ x = x - (y : E) :=
    Submission.Cvp.psiCan_eq_translate_of_mem_openCell hℒ hx
  have hpreCell (y : ℒ) : (Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ Submission.Cvp.openCell y =
      ((fun x : E => x - (y : E)) ⁻¹' B) ∩ Submission.Cvp.openCell y := by
    ext x
    constructor <;> rintro ⟨h1, h2⟩
    · exact ⟨by simpa [hOnCell y x h2] using h1, h2⟩
    · exact ⟨by simpa [hOnCell y x h2] using h1, h2⟩
  have hdist : (Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ U =
      ⋃ y : ℒ, ((Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ Submission.Cvp.openCell y) := by
    calc
      (Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ U
          = (Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ (⋃ y : ℒ, Submission.Cvp.openCell y) := by simp [U]
      _ = ⋃ y : ℒ, ((Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ Submission.Cvp.openCell y) := by
          rw [Set.inter_iUnion]
  have hpreU : (Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ U =
      Set.iUnion (fun y : ℒ => ((fun x : E => x - (y : E)) ⁻¹' B) ∩ Submission.Cvp.openCell y) := by
    rw [hdist]
    congr 1
    funext y
    exact hpreCell y
  have hpreC : (Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ Uᶜ = B ∩ Uᶜ := by
    ext x
    constructor <;> rintro ⟨h1, h2⟩
    · exact ⟨by simpa [hOnC x h2] using h1, h2⟩
    · exact ⟨by simpa [hOnC x h2] using h1, h2⟩
  have hmeasU : MeasurableSet ((Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ U) := by
    rw [hpreU]
    apply MeasurableSet.iUnion
    intro y
    have ht : Measurable (fun x : E => x - (y : E)) :=
      (continuous_id.sub continuous_const).measurable
    exact (ht hB).inter ((Submission.Cvp.openCell_isOpen y).measurableSet)
  have hmeasC : MeasurableSet ((Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ Uᶜ) := by
    rw [hpreC]
    exact hB.inter hUmeas.compl
  have hdecomp : (Submission.Cvp.psiCan hℒ ⁻¹' B) =
      ((Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ U) ∪ ((Submission.Cvp.psiCan hℒ ⁻¹' B) ∩ Uᶜ) := by
    ext x
    by_cases hxU : x ∈ U <;> simp [hxU]
  rw [hdecomp]
  exact hmeasU.union hmeasC

/-- `gaussianF t ∘ psiCan hℒ` is integrable on any set of finite volume: it is measurable
and pointwise bounded by the constant `t^m`. -/
lemma gaussianF_comp_psiCan_integrableOn {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (t : ℝ) (ht : 0 < t) {K : Set E}
    (hKvol : volume K < ⊤) :
    MeasureTheory.IntegrableOn (fun x : E => Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x)) K := by
  classical
  have hpsi : Measurable (Submission.Cvp.psiCan hℒ) := psiCan_measurable hℒ
  have hgauss : Continuous (fun x : E => Submission.Cvp.gaussianF t x) := by
    dsimp [Submission.Cvp.gaussianF]
    fun_prop
  have hmeas : Measurable (fun x : E => Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x)) := by
    simpa [Function.comp_def] using hgauss.measurable.comp hpsi
  have hc : ∀ x : E, ‖Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x)‖ ≤
      ‖(fun _ : E => (t : ℝ) ^ m) x‖ := by
    intro x
    have hnonneg : 0 ≤ Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x) :=
      Submission.Cvp.gaussianF_nonneg (n := m) t ht.le (Submission.Cvp.psiCan hℒ x)
    have hle0 : Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x) ≤
        Submission.Cvp.gaussianF t (0 : E) := by
      have hmono : ∀ {a b : E}, ‖a‖ ≤ ‖b‖ →
          Submission.Cvp.gaussianF t b ≤ Submission.Cvp.gaussianF t a := by
        intro a b hab
        exact Submission.Cvp.gaussianF_mono (n := m) t ht.le hab
      exact hmono (by simp)
    have hF0 : Submission.Cvp.gaussianF t (0 : E) = (t : ℝ) ^ m := by
      dsimp [Submission.Cvp.gaussianF]
      simp
    have htm : 0 ≤ (t : ℝ) ^ m := pow_nonneg ht.le m
    calc
      ‖Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x)‖
          = Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x) := abs_of_nonneg hnonneg
      _ ≤ Submission.Cvp.gaussianF t (0 : E) := hle0
      _ = (t : ℝ) ^ m := hF0
      _ = ‖(fun _ : E => (t : ℝ) ^ m) x‖ := by
          rw [Real.norm_eq_abs]
          exact (abs_of_nonneg htm).symm
  have hg : MeasureTheory.IntegrableOn (fun _ : E => (t : ℝ) ^ m) K := by
    exact MeasureTheory.integrableOn_const (C := (t : ℝ) ^ m) hKvol.ne
  have hb : ∀ᵐ x ∂(volume.restrict K), ‖Submission.Cvp.gaussianF t (Submission.Cvp.psiCan hℒ x)‖ ≤
      ‖(fun _ : E => (t : ℝ) ^ m) x‖ := ae_of_all _ hc
  exact MeasureTheory.Integrable.mono hg hmeas.aestronglyMeasurable hb

/-- `gaussianF t` itself is integrable on any set (it is integrable on the whole space). -/
lemma gaussianF_integrableOn (t : ℝ) (ht : 0 < t) (K : Set E) :
    MeasureTheory.IntegrableOn (fun x : E => Submission.Cvp.gaussianF t x) K :=
  (Submission.Cvp.gaussianF_integrable t ht).integrableOn

/-! ## The [C] comparison: `ambient_wins` -/

/-- **Ambient-wins (monotone_Voronoi_wins + fundamental_product), ambient form.**

For the host full-rank lattice `ℒ`, a primitive sublattice `ℒ₁` with quotient
`Q := quotLattice ℒ (realSpan ℒ₁)` realized in the orthogonal complement of `realSpan ℒ₁`
(`hop`, `hR`), and a common parameter `s > 0`:

    γ_s(V(ℒ))  ≥  γ_s(V(transLattice Q)) · γ_s(V(transLattice ℒ₁)).

`ℒ₁ ⊔ Q` is assumed full-rank in `E` (`hΛz`) and discrete (`hΛd`), as is `Q` (`hQd`).
-/
theorem ambient_wins (s : ℝ) (hs : 0 < s)
    (ℒ ℒ₁ : Submodule ℤ E)
    [DiscreteTopology ℒ] [DiscreteTopology ℒ₁]
    (hℒ : IsZLattice ℝ ℒ)
    (hΛd : DiscreteTopology ((ℒ₁ ⊔ (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁))) : Submodule ℤ E))
    (hΛz : IsZLattice ℝ (ℒ₁ ⊔ (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁))))
    (hQd : DiscreteTopology ((Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)) : Submodule ℤ E))
    (hp : ∀ x : E, x ∈ ℒ₁ ↔ x ∈ ℒ ∧ x ∈ W ℒ₁)
    (hop : Submission.QuotientLattice.OrthogonalPair ℒ₁
      (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)))
    (hR : W (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)) = (W ℒ₁)ᗮ) :
    γ s (VC ℒ) ≥
      γ s (VC (Submission.Transport.transLattice (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)))) *
      γ s (VC (Submission.Transport.transLattice ℒ₁)) := by
  classical
  let Q : Submodule ℤ E := Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)
  let Λ : Submodule ℤ E := ℒ₁ ⊔ Q
  let K : Set E := VC Λ
  let u : ℝ := 1 / s
  have hu : 0 < u := one_div_pos.mpr hs
  haveI : DiscreteTopology ((Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)) : Submodule ℤ E) := hQd
  haveI : DiscreteTopology ((ℒ₁ ⊔ (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁))) : Submodule ℤ E) := hΛd
  haveI : DiscreteTopology Q := hQd
  haveI : DiscreteTopology Λ := hΛd
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Countable ℒ := instCountable_of_discrete_submodule ℒ
  have hΛz' : IsZLattice ℝ Λ := by dsimp [Λ, Q]; exact hΛz
  haveI : IsZLattice ℝ Λ := hΛz'
  haveI : Countable Λ := instCountable_of_discrete_submodule Λ
  -- (a) volume K = volume (VC ℒ)
  have hdetΛ : ReverseMinkowski.determinant Λ = ReverseMinkowski.determinant ℒ := by
    have hsup : ReverseMinkowski.determinant Λ =
        ReverseMinkowski.determinant ℒ₁ * ReverseMinkowski.determinant Q := by
      dsimp [Λ, Q]
      exact Submission.Filtration.det_sup_orthogonal (n := m) (W₁ := ℒ₁)
        (W₂ := Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)) hop
    have hquot : ReverseMinkowski.determinant Q =
        ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ₁ := by
      dsimp [Q]
      exact Submission.SubLattice.determinant_quot_generic (nA := m) (ℒ' := ℒ₁) (ℒ := ℒ)
        (W ℒ₁) rfl hp
    have hdet1 : ReverseMinkowski.determinant ℒ₁ ≠ 0 :=
      ne_of_gt (Submission.Uncrossing.det_pos (L := ℒ₁))
    calc
      ReverseMinkowski.determinant Λ = ReverseMinkowski.determinant ℒ₁ *
          ReverseMinkowski.determinant Q := hsup
      _ = ReverseMinkowski.determinant ℒ₁ *
          (ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ₁) := by rw [hquot]
      _ = ReverseMinkowski.determinant ℒ := by field_simp [hdet1]
  have hKvolReal : MeasureTheory.volume.real K = MeasureTheory.volume.real (VC ℒ : Set E) := by
    dsimp [K]
    calc
      MeasureTheory.volume.real (VC Λ) = ReverseMinkowski.determinant Λ :=
        Submission.Poisson.voronoi_volume_eq_det (n := m) (ℒ := Λ) hΛz'
      _ = ReverseMinkowski.determinant ℒ := hdetΛ
      _ = MeasureTheory.volume.real (VC ℒ : Set E) :=
        (Submission.Poisson.voronoi_volume_eq_det (n := m) (ℒ := ℒ) hℒ).symm
  have hKvol_lt : volume K < ⊤ := by
    dsimp [K]
    exact voronoi_volume_lt_top (ℒ := Λ) hΛz'
  have hVvol_lt : volume (VC ℒ : Set E) < ⊤ := voronoi_volume_lt_top (ℒ := ℒ) hℒ
  have hvolK : volume K = volume (VC ℒ : Set E) :=
    measure_eq_of_measureReal_eq hKvolReal hKvol_lt.ne hVvol_lt.ne
  -- (b) K measurable, boundary null, translate-disjoint over ℒ
  have hKmeas : MeasurableSet K := by
    dsimp [K]
    exact (Submission.Voronoi.voronoi_measurable (ℒ := Λ))
  have hKboundary : volume (K \ interior K) = 0 := by
    dsimp [K]
    exact Submission.Cvp.volume_voronoi_boundary_zero (n := m) (ℒ := Λ)
  have hKdisj : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)) := by
    intro y hy0
    dsimp [K, Λ, Q]
    exact Submission.Disjointness.voronoi_interior_disjoint (m := m) (ℒ₁ := ℒ₁) (ℒ := ℒ)
      hΛd hQd (Submission.QuotientLattice.Primitive.le hp) hp hop hR y hy0
  -- (c) comparison of Gaussian integrals (F := gaussianF u, u := 1/s)
  let F : E → ℝ := fun x => Submission.Cvp.gaussianF u x
  have hFmono : ∀ a b : E, ‖a‖ ≤ ‖b‖ → F b ≤ F a := by
    intro a b hab
    dsimp [F]
    exact Submission.Cvp.gaussianF_mono (n := m) u hu.le hab
  have hFintInt : MeasureTheory.IntegrableOn F (interior K) := by
    dsimp [F]
    exact gaussianF_integrableOn u hu (interior K)
  have hKintvol : volume (interior K) < ⊤ := lt_of_le_of_lt (measure_mono interior_subset) hKvol_lt
  have hFψint : MeasureTheory.IntegrableOn (fun x : E => F (Submission.Cvp.psiCan hℒ x))
      (interior K) := by
    dsimp [F]
    exact gaussianF_comp_psiCan_integrableOn (ℒ := ℒ) hℒ u hu hKintvol
  have hFV : MeasureTheory.IntegrableOn F (VC ℒ : Set E) := by
    dsimp [F]
    exact (Submission.Cvp.gaussianF_integrable (n := m) u hu).integrableOn
  have hmw : (∫ x in K, F x) ≤ ∫ x in (VC ℒ : Set E), F x := by
    exact Submission.Cvp.monotone_voronoi_wins_of_vol (n := m) (ℒ := ℒ) hℒ K hKmeas hvolK
      hKdisj hKboundary F hFmono hFintInt hFψint hFV hVvol_lt.ne
  have hKγ : γ s K = ∫ x in K, F x := by
    dsimp [F, u]
    exact gammaMass_eq_gaussianF_integral s hs K
  have hVγ : γ s (VC ℒ : Set E) = ∫ x in (VC ℒ : Set E), F x := by
    dsimp [F, u]
    exact gammaMass_eq_gaussianF_integral s hs (VC ℒ : Set E)
  have hmwγ : γ s K ≤ γ s (VC ℒ : Set E) := by
    rw [hKγ, hVγ]
    exact hmw
  -- (d) factorize γ_s(K)
  have hsplit : γ s K = γ s (VC (Submission.Transport.transLattice ℒ₁)) *
      γ s (VC (Submission.Transport.transLattice (Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)))) := by
    dsimp [K]
    exact Submission.FundBody.ambient_sup_cell_product (ℒ₁ := ℒ₁)
      (ℒ₂ := Submission.QuotientLattice.quotLattice ℒ (W ℒ₁)) hop hR s
  have hprod : γ s (VC (Submission.Transport.transLattice Q)) *
        γ s (VC (Submission.Transport.transLattice ℒ₁)) ≤ γ s (VC ℒ : Set E) := by
    calc
      γ s (VC (Submission.Transport.transLattice Q)) *
            γ s (VC (Submission.Transport.transLattice ℒ₁))
          = γ s (VC (Submission.Transport.transLattice ℒ₁)) *
            γ s (VC (Submission.Transport.transLattice Q)) := by rw [mul_comm]
      _ = γ s K := hsplit.symm
      _ ≤ γ s (VC ℒ : Set E) := hmwγ
  simpa [Q] using hprod

/-! ## Boundary-case assembly (`boundary_gamma_bound`) -/

/-- Nonnegativity of the Gaussian mass of a measurable set. -/
lemma gammaMass_nonneg (s : ℝ) {K : Set E} (hK : MeasurableSet K) :
    0 ≤ Submission.GaussianMeasure.gammaMass (n := m) s K := by
  have hempty : Submission.GaussianMeasure.gammaMass (n := m) s ({x : E | False} : Set E) = 0 := by
    simp [Submission.GaussianMeasure.gammaMass]
  have h := Submission.GaussianMeasure.gammaMass_mono_set (n := m) s
    (show ({x : E | False} : Set E) ⊆ K by intro x hx; exact hx.elim)
    (by simpa using (isOpen_empty : IsOpen ({x : E | False} : Set E)).measurableSet) hK
  rw [hempty] at h
  exact h

/-- **Factor boost**: a stable full-rank rank-`r` lattice `M` (in its own standard space)
whose transported Voronoi cell has Gaussian mass `≥ 2/3` at parameter `1/t r` has mass at
the common parameter `1/t m` at least `1 − e^{−2log²(m/r)}/3`.

(Concentration from inradius `≥ 1/2` + the loose constant `π·25` vs `2` in the exponent.)
-/
lemma boost_stable_factor {m r : ℕ} (hr1 : 1 ≤ r) (hrm : r < m)
    (M : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology M]
    (hStM : Submission.StableLattices.Stable M)
    (hγM : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass
      (1 / Submission.MainStable.t r) (Submission.Voronoi.voronoi M)) :
    1 - Real.exp (-2 * (Real.log ((m : ℝ) / (r : ℝ))) ^ 2) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi M) := by
  classical
  have hτ : 0 ≤ Submission.MainStable.t m - Submission.MainStable.t r := by
    have hsub := Submission.MainStable.t_sub_t m r hr1 (le_of_lt hrm)
    have hlg : 0 ≤ Real.log ((m : ℝ) / (r : ℝ)) := by
      apply Real.log_nonneg
      have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr1)
      rw [one_le_div hrr]
      exact_mod_cast (le_of_lt hrm)
    nlinarith
  have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 / 2) ⊆
      Submission.Voronoi.voronoi M := by
    exact Submission.StableLattices.half_ball_subset_voronoi_of_stable (n := r) (ℒ := M) hStM
  have hconc := Submission.Concentration.gamma_concentration (n := r)
    (K := Submission.Voronoi.voronoi M)
    (hKcvx := Submission.Voronoi.voronoi_convex M)
    (hKcl := Submission.Voronoi.voronoi_isClosed M)
    (t := Submission.MainStable.t r)
    (τ := Submission.MainStable.t m - Submission.MainStable.t r)
    (r := (1 / 2 : ℝ))
    (ht := Submission.MainStable.t_pos r) (hτ := hτ) (hr := by norm_num)
    (hball := hball) (hγ := hγM)
  have harg : 1 / (Submission.MainStable.t r + (Submission.MainStable.t m -
      Submission.MainStable.t r)) = 1 / Submission.MainStable.t m := by
    congr 1
    ring
  have hC : 1 - Real.exp (-Real.pi * (((1 : ℝ) / 2) * (Submission.MainStable.t m -
      Submission.MainStable.t r)) ^ 2) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi M) := by
    rwa [harg] at hconc
  exact le_trans (Submission.MainStable.concentration_boost_bound m r hr1 hrm) hC

/-- **Boundary-case assembly of the rank-`m` induction step.**  Host `ℒ` (full rank `m`)
with a primitive stable sublattice `ℒ'` whose quotient `Q := quotLattice ℒ (realSpan ℒ')`
(rank `m − finrank ℤ ℒ'`) is stable; `ℒ' ⊔ Q` is full-rank in the ambient (`hΛz`).  The
induction hypotheses `ihL'`, `ihQ` bound the (transported) Voronoi masses at the per-rank
parameters; `boost_stable_factor` raises them to `1/t m`, and `ambient_wins` +
`boundary_factors_ge_two_thirds` close the chain at `≥ 2/3`. -/
theorem boundary_gamma_bound (m : ℕ) (hm : 2 ≤ m)
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
    (hΛz : IsZLattice ℝ (ℒ' ⊔ (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))))
    (hop : Submission.QuotientLattice.OrthogonalPair ℒ' (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')))
    (hR : Submission.QuotientLattice.realSpan (Submission.QuotientLattice.quotLattice ℒ
        (Submission.QuotientLattice.realSpan ℒ')) = (Submission.QuotientLattice.realSpan ℒ')ᗮ)
    (ihL' : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass
        (1 / Submission.MainStable.t (Module.finrank ℤ ℒ'))
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ')))
    (ihQ : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass
        (1 / Submission.MainStable.t (Module.finrank ℤ
          (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ'))))
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice
          (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ'))))) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
      (Submission.Voronoi.voronoi ℒ) := by
  classical
  let Q : Submodule ℤ (EuclideanSpace ℝ (Fin m)) :=
    Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ')
  have hℒ : IsZLattice ℝ ℒ := Submission.MainStable.isZLattice_of_finrank (n := m) ℒ hfinL
  haveI : DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ')) := hQd
  haveI : DiscreteTopology (Submission.Transport.transLattice ℒ') :=
    Submission.Transport.transLattice_discrete ℒ'
  haveI : DiscreteTopology (Submission.Transport.transLattice
      (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ'))) :=
    Submission.Transport.transLattice_discrete (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan ℒ'))
  have hA : Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi ℒ) ≥
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice
          (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ')))) *
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ')) := by
    exact ambient_wins (s := 1 / Submission.MainStable.t m)
      (hs := one_div_pos.mpr (Submission.MainStable.t_pos m))
      (ℒ := ℒ) (ℒ₁ := ℒ') hℒ hΛd hΛz hQd hp hop hR
  -- boost of the ℒ' factor
  have hb1 : 1 - Real.exp (-2 * (Real.log ((m : ℝ) / (Module.finrank ℤ ℒ' : ℝ))) ^ 2) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ')) := by
    exact boost_stable_factor (m := m) (r := Module.finrank ℤ ℒ')
      (hr1 := hr1L') (hrm := hrmL')
      (M := Submission.Transport.transLattice ℒ')
      (hStM := Submission.Transport.stable_of_stable_transported ℒ' hStL')
      (hγM := ihL')
  -- boost of the quotient factor
  have hb2 : 1 - Real.exp (-2 * (Real.log ((m : ℝ) / (Module.finrank ℤ Q : ℝ))) ^ 2) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice Q)) := by
    have hr1Q : 1 ≤ Module.finrank ℤ Q := by
      dsimp [Q]
      rw [hfinQ]
      omega
    have hrmQ : Module.finrank ℤ Q < m := by
      dsimp [Q]
      rw [hfinQ]
      omega
    exact boost_stable_factor (m := m) (r := Module.finrank ℤ Q)
      (hr1 := hr1Q) (hrm := hrmQ)
      (M := Submission.Transport.transLattice Q)
      (hStM := by
        dsimp [Q]
        exact Submission.Transport.stable_of_stable_transported
          (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ'))
          hStQ)
      (hγM := by dsimp [Q]; exact ihQ)
  -- product of the boosted bounds is ≥ 2/3 (log-claim arithmetic)
  let a : ℝ := Real.exp (-2 * (Real.log ((m : ℝ) / (Module.finrank ℤ ℒ' : ℝ))) ^ 2)
  let b : ℝ := Real.exp (-2 * (Real.log ((m : ℝ) / (Module.finrank ℤ Q : ℝ))) ^ 2)
  have ha_le : a ≤ 1 := by
    dsimp [a]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Real.log ((m : ℝ) / (Module.finrank ℤ ℒ' : ℝ)))])
  have hb_le : b ≤ 1 := by
    dsimp [b]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (Real.log ((m : ℝ) / (Module.finrank ℤ Q : ℝ)))])
  have ha_nonneg : 0 ≤ 1 - a / 3 := by nlinarith [ha_le]
  have hb_nonneg : 0 ≤ 1 - b / 3 := by nlinarith [hb_le]
  have hγQnonneg : 0 ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
      (Submission.Voronoi.voronoi (Submission.Transport.transLattice Q)) := by
    exact gammaMass_nonneg (m := Module.finrank ℤ Q) (1 / Submission.MainStable.t m)
      (Submission.Voronoi.voronoi_measurable (Submission.Transport.transLattice Q))
  have hγLnonneg : 0 ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
      (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ')) := by
    exact gammaMass_nonneg (m := Module.finrank ℤ ℒ') (1 / Submission.MainStable.t m)
      (Submission.Voronoi.voronoi_measurable (Submission.Transport.transLattice ℒ'))
  have hbaseQ := Submission.MainStable.boundary_factors_ge_two_thirds m (Module.finrank ℤ ℒ')
    hm hr1L' hrmL'
  have hden : (m : ℝ) - (Module.finrank ℤ ℒ' : ℝ) = (Module.finrank ℤ Q : ℝ) := by
    dsimp [Q]
    rw [hfinQ]
    exact (Nat.cast_sub (le_of_lt hrmL')).symm
  have hprod23 : (2 : ℝ) / 3 ≤ (1 - b / 3) * (1 - a / 3) := by
    rw [hden] at hbaseQ
    dsimp [a, b]
    rw [mul_comm] at hbaseQ
    exact hbaseQ
  have hmul : (1 - b / 3) * (1 - a / 3) ≤
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice Q)) *
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ')) := by
    exact mul_le_mul (by simpa [b] using hb2) (by simpa [a] using hb1) ha_nonneg hγQnonneg
  calc
    (2 : ℝ) / 3 ≤ (1 - b / 3) * (1 - a / 3) := hprod23
    _ ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice Q)) *
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi (Submission.Transport.transLattice ℒ')) := hmul
    _ ≤ Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.Voronoi.voronoi ℒ) := by simpa [Q] using hA

