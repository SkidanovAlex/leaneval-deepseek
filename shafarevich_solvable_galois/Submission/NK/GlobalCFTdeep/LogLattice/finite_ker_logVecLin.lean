import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.LogLattice

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

/-- At a finite place inside `T`, a `T`-unit whose log vector vanishes is a local unit there. -/
theorem expUnit_eq_zero_of_logVec_eq_zero {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (NK.GlobalCFT.Place L)) (a : Lˣ)
    (q : HeightOneSpectrum (𝓞 L)) (hq : NK.GlobalCFT.Place.ofFinite q ∈ T)
    (h : NK.GlobalCFTdeep.logVec (L := L) T a ⟨NK.GlobalCFT.Place.ofFinite q, hq⟩ = 0) :
    NK.GlobalCFTdeep.expUnit q a = 0 := by
  have h' : Real.log ((NK.GlobalCFT.Idele.localAbs L (NK.GlobalCFT.Place.ofFinite q)
      (NK.GlobalCFT.Idele.principalIdele L a (NK.GlobalCFT.Place.ofFinite q)) : ℝˣ) : ℝ) = 0 := h
  clear h
  rw [NK.GlobalCFTdeep.expUnit_eq_zero_iff_mem_localUnits,
    NK.GlobalCFT.Place.mem_localUnits_ofFinite]
  rw [NK.GlobalCFT.Idele.principalIdele_apply, NK.GlobalCFT.Idele.localAbs_ofFinite,
      Units.val_mk0, Units.coe_map] at h'
  change Real.log ‖(algebraMap L (q.adicCompletion L) (a : L))‖ = 0 at h'
  have hne : (algebraMap L (q.adicCompletion L) (a : L)) ≠ 0 := by
    simp [Units.ne_zero a]
  have hnorm : ‖(algebraMap L (q.adicCompletion L) (a : L))‖ = 1 := by
    rw [← Real.exp_log (norm_pos_iff.mpr hne), h', Real.exp_zero]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
    change ‖(algebraMap L (q.adicCompletion L) (a : L))‖ ≤ 1
    rw [hnorm]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
    rw [Units.val_inv_eq_inv_val, Units.coe_map]
    change ‖(algebraMap L (q.adicCompletion L) (a : L))⁻¹‖ ≤ 1
    rw [norm_inv, hnorm, inv_one]

/-- At an infinite place, a `T`-unit with vanishing log vector has local absolute value `1`. -/
theorem infinitePlace_eq_one_of_logVec_eq_zero {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (T : Set (NK.GlobalCFT.Place L)) (a : Lˣ)
    (w : InfinitePlace L) (hw : NK.GlobalCFT.Place.ofInfinite w ∈ T)
    (h : NK.GlobalCFTdeep.logVec (L := L) T a ⟨NK.GlobalCFT.Place.ofInfinite w, hw⟩ = 0) :
    w (a : L) = 1 := by
  have h' : Real.log ((NK.GlobalCFT.Idele.localAbs L (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Idele.principalIdele L a (NK.GlobalCFT.Place.ofInfinite w)) : ℝˣ) : ℝ) = 0 := h
  clear h
  have hval : ((NK.GlobalCFT.Idele.localAbs L (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Idele.principalIdele L a (NK.GlobalCFT.Place.ofInfinite w)) : ℝˣ) : ℝ)
      = w (a : L) ^ w.mult := by
    rw [NK.GlobalCFT.Idele.principalIdele_apply, NK.GlobalCFT.Idele.localAbs_ofInfinite,
      Units.val_pow_eq_pow_val, Units.val_mk0]
    congr 1
    simpa [NumberField.InfinitePlace.Completion.algebraMap_apply] using
      (NumberField.InfinitePlace.Completion.norm_coe (v := w) (WithAbs.toAbs w.1 (a : L)))
  rw [hval, Real.log_pow] at h'
  have hlog : Real.log (w (a : L)) = 0 := by
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' InfinitePlace.mult_coe_ne_zero
    · exact h''
  rw [← Real.exp_log (InfinitePlace.pos_iff.mpr (Units.ne_zero a)), hlog, Real.exp_zero]

/-- **The kernel of the log map on the `T`-units is finite**: it consists of the roots of unity
(Kronecker's theorem).  This is the finite module `μ` of the exact sequence
`0 → μ → U(T) → M' → 0` in Milne's proof of Proposition 3.1.

## Proof sketch

For `a ∈ U(T)` with `logVecLin T a = 0` one has `|a|_w = 1` for every `w ∈ T`; for `w ∉ T` this
holds by `T`-unithood (the `TUnits` condition), so `|a|_w = 1` at *every* place of `L`.  In
particular:

* at every finite place `q`, `|a|_q = 1` gives `expUnit q a = 0`
  (`NK.GlobalCFTdeep.expUnit_eq_zero_iff`, `NK.GlobalCFTdeep.mem_TUnits_iff_expUnit`), so `a`
  lies in the kernel of `NK.GlobalCFTdeep.tUnitsVal T`, which is the image of the global units
  `NK.GlobalCFTdeep.unitsToTUnits`
  (`NK.GlobalCFTdeep.Herbrand.ker_tUnitsVal`); in particular `a ∈ (𝓞 L)ˣ`;
* at every infinite place `w`, `logVecLin T a` has component `w.mult * Real.log (w a)`, hence
  `Real.log (w a) = 0` for all `w`, i.e. `NumberField.Units.logEmbedding L (Additive.ofMul a) = 0`,
  so `a` is a root of unity by `NumberField.Units.logEmbedding_eq_zero_iff`.

The set of roots of unity of `L` is finite (it is the torsion subgroup `NumberField.Units.torsion L`
of `(𝓞 L)ˣ`, of order bounded by `2 * finrank ℚ L`), which gives `Finite ↥(ker …)`. -/
theorem finite_ker_logVecLin {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    (T : Set (NK.GlobalCFT.Place L)) [Finite T]
    (hTinf : ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T) :
    Finite ↥(LinearMap.ker (NK.GlobalCFTdeep.logVecLin (L := L) T)) := by
  classical
  have key : ∀ x : ↥(LinearMap.ker (NK.GlobalCFTdeep.logVecLin (L := L) T)),
      ∃ y : Additive ((𝓞 L)ˣ), Additive.toMul y ∈ NumberField.Units.torsion L ∧
        (NK.GlobalCFTdeep.unitsToTUnits (L := L) T) y
          = (x : Additive (NK.GlobalCFTdeep.TUnits (L := L) T)) := by
    intro x
    set a : Lˣ := (((Additive.toMul (x : Additive (NK.GlobalCFTdeep.TUnits (L := L) T))
      : NK.GlobalCFTdeep.TUnits (L := L) T)) : Lˣ) with ha
    have hlog : NK.GlobalCFTdeep.logVec (L := L) T a = 0 := by
      rw [ha]
      simpa only [NK.GlobalCFTdeep.logVecLin_apply] using (LinearMap.mem_ker.mp x.2)
    have hval : NK.GlobalCFTdeep.tUnitsVal (L := L) T
        (x : Additive (NK.GlobalCFTdeep.TUnits (L := L) T)) = 0 := by
      funext q
      rw [NK.GlobalCFTdeep.tUnitsVal_apply]
      rw [← ha]
      exact expUnit_eq_zero_of_logVec_eq_zero (K := K) T a q.1 q.2
        (congrFun hlog ⟨NK.GlobalCFT.Place.ofFinite q.1, q.2⟩)
    have hmem : (x : Additive (NK.GlobalCFTdeep.TUnits (L := L) T)) ∈
        LinearMap.range (NK.GlobalCFTdeep.unitsToTUnits (L := L) T) := by
      rw [← NK.GlobalCFTdeep.Herbrand.ker_tUnitsVal (L := L) T]
      exact LinearMap.mem_ker.mpr hval
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_, hu⟩
    refine (NumberField.Units.mem_torsion L).mpr (fun w => ?_)
    have hcoeeq : (algebraMap (𝓞 L) L ((Additive.toMul u : (𝓞 L)ˣ) : 𝓞 L) : L) = (a : L) := by
      have hu1 : Additive.toMul (x : Additive (NK.GlobalCFTdeep.TUnits (L := L) T))
          = NK.GlobalCFTdeep.unitsToTUnitsHom (L := L) T (Additive.toMul u) := by
        exact (hu.symm).trans (NK.GlobalCFTdeep.unitsToTUnits_apply (L := L) T u).symm
      have h4 := congrArg (fun y : NK.GlobalCFTdeep.TUnits (L := L) T => ((y : Lˣ) : L)) hu1
      rw [NK.GlobalCFTdeep.unitsToTUnitsHom_apply] at h4
      rw [ha]
      simpa using h4.symm
    rw [hcoeeq]
    exact infinitePlace_eq_one_of_logVec_eq_zero (K := K) T a w (hTinf _ trivial)
      (congrFun hlog ⟨NK.GlobalCFT.Place.ofInfinite w, hTinf _ trivial⟩)
  let f : ↥(LinearMap.ker (NK.GlobalCFTdeep.logVecLin (L := L) T)) →
      NumberField.Units.torsion L := fun x => ⟨Additive.toMul (key x).choose, (key x).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (key x).choose = (key y).choose := Subtype.ext_iff.mp hxy
    have hx := (key x).choose_spec.2
    have hy := (key y).choose_spec.2
    apply Subtype.ext
    rw [← hx, ← hy, h1]
  exact Finite.of_injective f hf

end NK.GlobalCFTdeep.LogLattice
