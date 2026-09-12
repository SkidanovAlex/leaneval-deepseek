import Mathlib
import Submission.Work.Polygon.GraysonData
import Submission.Commons.Lattice.Minkowski.covolume_zeroDim_trivial
import Submission.GeometryOfNumbers.FlowLattice
import Submission.GeometryOfNumbers.FlowLatticeCovolume

/-!
# Grayson-polygon endpoints: the trivial-subgroup endpoint `c_t(0) = 0`

The Grayson data of a lattice `Λ ≤ ℝᵈ` (`φ(W) = log covol(W)`, `covol` intrinsic in the
real span) has its rank-`0` endpoint forced by the trivial subgroup `{0} ≤ Λ`: its real
span is the zero subspace of `ℝᵈ`, whose total canonical volume is `1`, and the whole
space is a fundamental domain of the trivial group.  Hence `covol({0}) = 1` and
`φ({0}) = log 1 = 0`.  The polygon `c_t = largestConvexMinorant d (g_t ·)` then vanishes
at `0` (`DiscreteConvex.largestConvexMinorant_zero_left`), as the §3 flow layer requires.
(For the flow lattice `Λ_t ≤ ℝᵈ` this is the trivial subgroup `⊥ ≤ Λ_t` of the ambient
space — the statement is flow-independent.)

This module proves, over `E = EuclideanSpace ℝ (Fin d)`:

* `latticeCovol_bot`: the trivial subgroup has intrinsic covolume `1`
  (`latticeCovol (⊥ : Submodule ℤ (E d)) = 1`): the real span `V` of `⊥` is the zero
  subspace — a subsingleton whose canonical volume is `1`, obtained through the
  orthonormal-basis representation `V ≃ₗᵢ EuclideanSpace ℝ (Fin 0)`, where the volume is
  the Dirac measure (`volume_euclideanSpace_eq_dirac`); the trivial group has the whole
  space as fundamental domain (`IsAddFundamentalDomain.covolume_eq_volume`, pattern of the
  Commons lemma `covolume_zeroDim_trivial`);
* `log_latticeCovol_bot`: `log (latticeCovol ⊥) = 0` — the rank-`0` endpoint of the
  Grayson data.

The full-rank endpoint `c_t(d) = 0` (covol of the unimodular flow lattice `= 1`, via
`covol_flowLattice_exp` and the top-subspace transport) is a follow-up module.
-/

noncomputable section

open Set Filter Metric MeasureTheory Module Real BigOperators
open scoped ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.GraysonEndpoints

open Submission.GraysonData

variable {d : ℕ}

/-- The real span of the trivial `ℤ`-submodule of `E` sits inside the zero `ℝ`-subspace:
every element of it is `0`. -/
lemma bot_real_span_le_bot (d : ℕ) :
    Submodule.span ℝ (↑(⊥ : Submodule ℤ (E d)) : Set (E d)) ≤ (⊥ : Submodule ℝ (E d)) := by
  apply Submodule.span_le.mpr
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  rw [hx0]
  simp

/-- The real span of the trivial `ℤ`-submodule of `E` is the zero subspace, whose
(0-dimensional) type is a subsingleton. -/
lemma bot_real_span_subsingleton (d : ℕ) :
    Subsingleton (Submodule.span ℝ (↑(⊥ : Submodule ℤ (E d)) : Set (E d))) := by
  classical
  let V : Submodule ℝ (E d) := Submodule.span ℝ (↑(⊥ : Submodule ℤ (E d)) : Set (E d))
  refine ⟨by
    intro a b
    apply Subtype.ext
    have ha : (a : E d) = 0 := by
      have : (a : E d) ∈ (⊥ : Submodule ℝ (E d)) := bot_real_span_le_bot d a.2
      simpa using this
    have hb : (b : E d) = 0 := by
      have : (b : E d) ∈ (⊥ : Submodule ℝ (E d)) := bot_real_span_le_bot d b.2
      simpa using this
    simp [ha, hb]⟩

/-- The intrinsic covolume of the trivial subgroup of `ℝᵈ` is `1` (the rank-`0` endpoint
of the Grayson data): the trivial group's real span is the zero subspace, whose total
volume is `1`, and the whole space is its fundamental domain. -/
theorem latticeCovol_bot (d : ℕ) :
    latticeCovol (⊥ : Submodule ℤ (E d)) = 1 := by
  classical
  let W : Submodule ℤ (E d) := ⊥
  let V : Submodule ℝ (E d) := Submodule.span ℝ (W : Set (E d))
  have hW : W = (⊥ : Submodule ℤ (E d)) := rfl
  have hsubV : Subsingleton V := by
    dsimp [V, W]
    exact bot_real_span_subsingleton d
  change ZLattice.covolume (E := V) (Submodule.comap (V.subtype.restrictScalars ℤ) W) = 1
  -- (i) the comap of the trivial subgroup is the trivial subgroup of V
  have hL : Submodule.comap (V.subtype.restrictScalars ℤ) W = (⊥ : Submodule ℤ V) := by
    ext x
    constructor
    · intro hx
      have hx' : (V.subtype.restrictScalars ℤ) x ∈ (⊥ : Submodule ℤ (E d)) := by
        rw [hW] at hx
        rw [Submodule.mem_comap] at hx
        exact hx
      rw [Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      apply Subtype.ext
      exact hx'
    · intro hx
      rw [Submodule.mem_bot] at hx
      rw [Submodule.mem_comap]
      rw [Submodule.mem_bot]
      rw [hx]
      rfl
  rw [hL]
  -- (ii) covolume of the trivial subgroup of the zero-dimensional space V is 1
  let L0 : Submodule ℤ V := ⊥
  change ZLattice.covolume (E := V) L0 = 1
  have hfd : IsAddFundamentalDomain L0 Set.univ (volume : Measure V) := by
    refine IsAddFundamentalDomain.mk' ?_ ?_
    · refine ⟨Set.univ, MeasurableSet.univ, ?_⟩
      exact ae_of_all _ (by intro x; simp)
    · intro x
      refine ⟨0, by simp, ?_⟩
      intro y hy
      exact Subsingleton.elim y 0
  have hfinv : VAddInvariantMeasure L0 V (volume : Measure V) := by
    constructor
    intro c s hs
    have hc0 : (c : V) = 0 := (Submodule.mem_bot (R := ℤ) (M := V)).mp c.2
    have hf : (fun x : V => c +ᵥ x) = id := by
      funext x
      change (c : V) + x = x
      rw [hc0]
      simp
    rw [hf]
    simp
  haveI : VAddInvariantMeasure L0 V (volume : Measure V) := hfinv
  have hvol := IsAddFundamentalDomain.covolume_eq_volume (ν := volume) hfd
  -- the total volume of the zero-dimensional subspace V is 1
  have hVuniv : (volume : Measure V) (Set.univ : Set V) = 1 := by
    have hfin : Module.finrank ℝ V = 0 := by
      have hle : V ≤ (⊥ : Submodule ℝ (E d)) := by
        dsimp [V]
        exact bot_real_span_le_bot d
      have hmono : Module.finrank ℝ V ≤ Module.finrank ℝ (⊥ : Submodule ℝ (E d)) :=
        Submodule.finrank_mono hle
      have hbot : Module.finrank ℝ (⊥ : Submodule ℝ (E d)) = 0 := finrank_bot ℝ (E d)
      omega
    let b0 : OrthonormalBasis (Fin 0) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hfin)
    have hmp : MeasurePreserving (⇑b0.repr) (volume : Measure V)
        (volume : Measure (EuclideanSpace ℝ (Fin 0))) := b0.measurePreserving_repr
    have hd : (volume : Measure (EuclideanSpace ℝ (Fin 0))) = Measure.dirac 0 :=
      volume_euclideanSpace_eq_dirac (Fin 0)
    calc
      (volume : Measure V) (Set.univ : Set V)
          = (volume : Measure (EuclideanSpace ℝ (Fin 0))) (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by
            rw [← hmp.map_eq]
            rw [Measure.map_apply (b0.repr.continuous.measurable) MeasurableSet.univ]
            simp
      _ = 1 := by
            rw [hd]
            simp
  rw [ZLattice.covolume]
  rw [hvol, hVuniv]
  simp

/-- The rank-`0` endpoint of the Grayson data: `φ({0}) = log covol({0}) = log 1 = 0`. -/
theorem log_latticeCovol_bot (d : ℕ) :
    Real.log (latticeCovol (⊥ : Submodule ℤ (E d))) = 0 := by
  rw [latticeCovol_bot d]
  simp


/-- **Full-rank bridge**: for a `ℤ`-submodule of `ℝᵈ` whose real span is the whole space,
the intrinsic covolume equals the ambient covolume (both measure the lattice in the same
`d`-dimensional Euclidean space, identified through the canonical top-subspace isometry
`LinearIsometryEquiv.ofTop` and `ZLattice.covolume_comap`). -/
theorem latticeCovol_eq_covolume_of_span_top (W : Submodule ℤ (E d))
    [DiscreteTopology W] [IsZLattice ℝ W]
    (hspan : Submodule.span ℝ (W : Set (E d)) = ⊤) :
    latticeCovol W = ZLattice.covolume W := by
  classical
  let V : Submodule ℝ (E d) := Submodule.span ℝ (W : Set (E d))
  have hV : V = ⊤ := hspan
  let e : V ≃ₗᵢ[ℝ] E d := LinearIsometryEquiv.ofTop (E d) V hV
  let eL : V ≃L[ℝ] E d := e.toContinuousLinearEquiv
  have he : MeasurePreserving (⇑eL) (volume : Measure V) (volume : Measure (E d)) := by
    simpa [eL] using (e.measurePreserving : MeasurePreserving (⇑e) volume volume)
  change ZLattice.covolume (E := V) (Submodule.comap (V.subtype.restrictScalars ℤ) W) =
    ZLattice.covolume W
  have hc' : Submodule.comap (V.subtype.restrictScalars ℤ) W = ZLattice.comap ℝ W (↑↑eL) := by
    unfold ZLattice.comap
    congr 1
  have hc := ZLattice.covolume_comap (L := W) (μ := (volume : Measure (E d)))
    (F := V) (ν := (volume : Measure V)) (e := eL) (he := he)
  exact hc

/-- The full-rank endpoint of the Grayson data for the (two-scale) flow lattice:
`covol(flowLattice a b ℓ) = |a^ℓ·b^(d−ℓ)|`, intrinsically (real span = `ℝᵈ`). -/
lemma latticeCovol_flowLattice (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hℓd : ℓ ≤ d) :
    latticeCovol (Submission.FlowLattice.flowLattice (d := d) a b ℓ) = |a ^ ℓ * b ^ (d - ℓ)| := by
  classical
  haveI : Fact (a ≠ 0) := ⟨ha⟩
  haveI : Fact (b ≠ 0) := ⟨hb⟩
  have hspan : Submodule.span ℝ (Submission.FlowLattice.flowLattice (d := d) a b ℓ : Set (E d)) = ⊤ :=
    IsZLattice.span_top (K := ℝ) (L := Submission.FlowLattice.flowLattice (d := d) a b ℓ)
  rw [latticeCovol_eq_covolume_of_span_top (Submission.FlowLattice.flowLattice (d := d) a b ℓ) hspan]
  exact Submission.FlowLattice.covol_flowLattice a b ℓ ha hb hℓd

/-- The full-rank endpoint of the Grayson data for the **unimodular exponential flow
lattice**: `covol(a_t ℤᵈ) = 1`, intrinsically (real span = `ℝᵈ`), hence
`φ(Λ_t) = log 1 = 0` (`c_t(d) = 0`). -/
lemma latticeCovol_flowLattice_exp {d ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) :
    latticeCovol (Submission.FlowLattice.flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) = 1 := by
  classical
  have ha0 : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hb0 : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
  haveI : Fact (Real.exp (-t / (ℓ : ℝ)) ≠ 0) := ⟨ha0⟩
  haveI : Fact (Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0) := ⟨hb0⟩
  have hspan : Submodule.span ℝ (Submission.FlowLattice.flowLattice (d := d)
      (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ : Set (E d)) = ⊤ :=
    IsZLattice.span_top (K := ℝ) (L := Submission.FlowLattice.flowLattice (d := d)
      (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
  rw [latticeCovol_eq_covolume_of_span_top
    (Submission.FlowLattice.flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) hspan]
  exact Submission.FlowLattice.covol_flowLattice_exp hℓ0 hℓd t

/-- The full-rank endpoint in log form: `φ(Λ_t) = log covol(Λ_t) = 0` for the unimodular
exponential flow lattice. -/
lemma log_latticeCovol_flowLattice_exp {d ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (t : ℝ) :
    Real.log (latticeCovol (Submission.FlowLattice.flowLattice (d := d)
      (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) = 0 := by
  rw [latticeCovol_flowLattice_exp hℓ0 hℓd t]
  simp

end Submission.GraysonEndpoints
