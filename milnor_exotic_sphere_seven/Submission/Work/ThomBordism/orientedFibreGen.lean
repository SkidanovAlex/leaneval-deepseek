import Mathlib
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.thomClass_trivial_point
import Submission.Work.Tubular.Collapse
import Submission.Work.Tubular.OnePointCompl
import Submission.Work.ThomBordism.onePointExtensionTaut
import Submission.Work.ThomBordism.gaussDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the standard Thom generator of `(ℝ^k, ℝ^k∖0)`, and the coordinate reading of a frame

This file supplies the two τ-free ingredients that the *sharp* fibre comparison of the last mile of
`Work.ThomBordism.thomRational` needs (see `NOTE_SESSION39.md` and the project lead's round-39
message): the **standard generator** of the Thom pair of `ℝ^k` — the reference against which the
fibre restrictions of the relevant Thom classes are compared, independently of the opaque
`Classical.choice` that defines `Work.ThomBordism.Grassmann.tautologicalThomClass` — and the
**coordinate reading** of an ambient vector in a frame, which is what turns an *oriented frame* of a
normal space (the `σ`-corrected frame `Work.ThomBordism.Gauss.gframe`, whose orientation is the
canonical coorientation by `Work.ThomBordism.sigmaTelescope_gauss`) into a linear identification with
`ℝ^k`, hence into a class of the fibre pair.

Concretely:

* `Work.ThomBordism.readFrame f : ℝ^N →L[ℝ] ℝ^k` is the map `x ↦ (⟨f j, x⟩)_j`.  On
  `span (range f)` with `f` orthonormal it is an isometry onto `ℝ^k` (`readFrame_apply`,
  `readFrame_eq_zero_iff`).
* `Work.ThomBordism.stdThomGen k : H^k(ℝ^k, ℝ^k∖0;ℤ)` is the transport, along
  `Work.Thom.trivProductHomeo`, of the Thom class of the trivial rank-`k` bundle over a point
  (`Work.Thom.thomClass_trivial_point`).  **Warning**: like every Thom class of this tree it is
  defined by `Classical.choice`; what matters for the last mile is only that it is a *fixed* class,
  independent of the data (the uniform sign `s_k` of the lead's round-39 message is the comparison of
  `tautologicalThomClass` with *this* class), so no property of it is needed beyond `span = ⊤`
  (a delegation) and its naturality under the reading map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

/-- **The coordinate reading of an ambient vector in a frame**: `x ↦ (⟨f j, x⟩)_j`, as a continuous
linear map into `ℝ^k`. -/
noncomputable def readFrame {N k : ℕ} (f : Fin k → EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  ContinuousLinearMap.comp (Work.Tubular.funToEuc k).toContinuousLinearMap
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (f j)))

theorem readFrame_apply {N k : ℕ} (f : Fin k → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    readFrame f x = Work.Tubular.funToEuc k (fun j => inner ℝ (f j) x) := rfl

theorem readFrame_eq_zero_iff {N k : ℕ} (f : Fin k → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) : readFrame f x = 0 ↔ ∀ j, inner ℝ (f j) x = 0 := by
  rw [readFrame_apply, (Work.Tubular.funToEuc k).map_eq_zero_iff]
  exact funext_iff

/-- **The standard generator of the Thom pair `(ℝ^k, ℝ^k∖0)`.** -/
noncomputable def stdThomGen (k : ℕ) (hk : 1 ≤ k) :
    Work.Thom.RelCoh ℤ k (EuclideanSpace ℝ (Fin k))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin k))) :=
  (Work.Thom.relCohMap
    ((↑(Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm :
        C(PUnit × EuclideanSpace ℝ (Fin k),
          (Work.TangentClasses.RealBundle.trivial PUnit (EuclideanSpace ℝ (Fin k))
            PUnit).TotalSpace)).comp
      ⟨fun v : EuclideanSpace ℝ (Fin k) => (PUnit.unit, v),
        continuous_const.prodMk continuous_id⟩)
    ({0}ᶜ)
    (Work.Thom.zeroComplement (Work.TangentClasses.RealBundle.trivial PUnit
      (EuclideanSpace ℝ (Fin k)) PUnit))
    (fun v hv => by
      change (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
        (PUnit.unit, v) ∈ Work.Thom.zeroComplement
          (Work.TangentClasses.RealBundle.trivial PUnit (EuclideanSpace ℝ (Fin k)) PUnit)
      rw [Work.Thom.mem_zeroComplement]
      intro h0
      have h1 : (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit
          ((Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
            (PUnit.unit, v))).2 = v :=
        congrArg Prod.snd (Homeomorph.apply_symm_apply _ _)
      have h2 : (show EuclideanSpace ℝ (Fin k) from
          ((Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
            (PUnit.unit, v)).2)
          = (Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit
              ((Work.Thom.trivProductHomeo PUnit (EuclideanSpace ℝ (Fin k)) PUnit).symm
                (PUnit.unit, v))).2 := by
        rw [Work.Thom.trivProductHomeo_apply]
      rw [h2, h1] at h0
      exact hv h0) ℤ k).hom
    (Classical.choice (Work.Thom.thomClass_trivial_point k hk PUnit)).τ

/-! ## The fibre of the Thom pair of the normal bundle, and its oriented generator -/

section Fibre

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The fibre of the total space of the normal bundle of an embedding over `x`.** -/
def nfSet (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Set (Work.Tubular.NormalTotal E) := {p | Work.Tubular.NormalTotal.proj p = x}

/-- The **punctured** part of that fibre. -/
def nfPunct (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Set ↥(nfSet E x) := {p | Work.Tubular.NormalTotal.vec p.1 ≠ 0}

/-- The inclusion of the fibre pair of the normal bundle into the Thom pair. -/
def nfIncl (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    C(↥(nfSet E x), TopCat.of (Work.Tubular.NormalTotal E)) :=
  Work.Thom.subtypeMap (nfSet E x)

theorem nfIncl_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    ∀ p ∈ nfPunct E x, nfIncl E x p ∈ Work.Tubular.normalNonzero E := by
  intro p hp
  rw [Work.Tubular.mem_normalNonzero, Work.ThomBordism.normalNorm_eq_norm_vec]
  rw [show nfIncl E x p = p.1 from rfl]
  exact norm_ne_zero_iff.mpr hp

/-- **The restriction of a class of the Thom pair of the normal bundle to the fibre pair over
`x`.** -/
noncomputable def nfRes (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (n : ℕ) : Work.Thom.RelCoh ℤ n (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) →ₗ[ℤ]
      Work.Thom.RelCoh ℤ n ↥(nfSet E x) (nfPunct E x) :=
  (Work.Thom.relCohMap (nfIncl E x) (nfPunct E x) (Work.Tubular.normalNonzero E)
    (nfIncl_mem E x) ℤ n).hom

/-- **The coordinate reading of a point of the normal fibre in the canonical frame `gframe`.** -/
noncomputable def nfRead (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    C(↥(nfSet E x), EuclideanSpace ℝ (Fin k)) :=
  ⟨fun p : ↥(nfSet E x) => readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)
      (Work.Tubular.NormalTotal.vec p.1),
    (readFrame (Gauss.gframe E ND (ND.D.indexAt x) x)).continuous.comp
      ((Work.Tubular.NormalTotal.continuous_vec E).comp continuous_subtype_val)⟩

/-- **The oriented fibre generator of the normal bundle at `x`**: the pullback of the standard
generator `Work.ThomBordism.stdThomGen` along the coordinate reading `Work.ThomBordism.nfRead` in the
canonical (`σ`-corrected, `Work.ThomBordism.sigmaTelescope_gauss`) frame `Work.ThomBordism.Gauss.gframe`.

The definition is *conditional* on the membership obligation `nfRead ≠ 0` on the punctured fibre
(`Work.ThomBordism.nfRead_ne_zero`, the small geometric delegation); while that is unproved the
`else` branch is dead.  The class does *not* depend on the normal data `ND`: two frames of the same
normal space differ by an element of `SO(k)`, and the pullback of `stdThomGen` along an
orientation-preserving isometry is `stdThomGen`. -/
noncomputable def nfGen {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt) :
    Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x) := by
  classical
  exact if h : ∀ p ∈ nfPunct E x, nfRead E ND x p ≠ 0 then
    (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x) ({0}ᶜ) h ℤ k).hom (stdThomGen k hk)
  else 0

end Fibre

end Work.ThomBordism
