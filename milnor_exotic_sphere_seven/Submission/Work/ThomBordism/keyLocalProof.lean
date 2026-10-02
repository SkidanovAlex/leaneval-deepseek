import Mathlib
import Submission.Work.ThomBordism.keyLocalDef
import Submission.Work.ThomBordism.ambientFibreComparison
import Submission.Work.ThomBordism.normalTotal_relKronH_kernel_bot
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.ThomBordism.value_eq_chartModelClass
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.tubeChart_collapseToOnePoint_data
import Submission.Work.ThomBordism.fibreReading_collapseClass
import Submission.Work.ThomBordism.canonicalGauss_assembly
import Submission.Work.ThomBordism.frameEval_realThomClassOf
import Submission.Work.ThomBordism.localDegree_localisation
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.tautologicalBundleHoriO
import Submission.Work.ThomBordism.coorFibre_fibreGeneratorAux
import Submission.Work.ThomBordism.KeyLocal.tubePairingConvert
import Submission.Work.ThomBordism.KeyLocal.tubeCompare

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false


/-!
# The key local statement: the pairing toolkit

The relative Kronecker pairing `Work.Tubular.relKronH` of the Thom pair of the normal bundle against
the collapse class `Work.Tubular.collapseRelK8` is *injective* (`collapseRelK8_pairing_injective`
below): the collapse class generates the relative homology in degree `k + 8`
(`Work.Tubular.collapseRelK8_span_top`), and the relative Kronecker pairing of the pair is
non-degenerate (`Work.ThomBordism.normalTotal_relKronH_kernel_bot`).

Consequences recorded here:

* equal pairings against the collapse class force equality of the classes
  (`eq_of_collapseRelK8_pairing_eq`);
* hence a degree-`8 + k` class `B` of the Thom pair is a *determined* multiple of the ambient chart
  model class `ambientValueClass E C x`: the multiplier is `⟨B, c⟩ / κ` with `κ = ±1` the (uniform)
  ambient local degree of the collapse.

## Status of the target

`Work.ThomBordism.KeyLocal` is *equivalent* to the fleet's coorientation sign statement
`Work.ThomBordism.PieceP2` (`Submission/Work/ThomBordism/coorFibre_fibreGenerator.lean`):

* `PieceP2 k hk → KeyLocal k hk` — the direction recorded here, using the injectivity above;
* `KeyLocal k hk → PieceP2 k hk` — `Work.ThomBordism.coorFibre_fibreGenerator_of_keyLocal`
  (PROVED in the tree).

So the remaining obligation of both is the *uniformity* of the local-degree sign (the geometric
input of `Work.ThomBordism.branchSign_uniform_gauss`), which is what the module docstring of
`Submission/Work/ThomBordism/keyLocal.lean` describes.
-/

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

section PairingToolkit

attribute [local instance 100] ZSMul.toSMul

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The pairing of a degree-`8 + k` relative class of the Thom pair against the collapse class, as a
`ℤ`-linear functional.  The degree of the collapse class is `k + 8`, so the transport
`chainsHomologyCast` is inserted once and for all. -/
noncomputable def collapsePairingMap [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) :
    Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) →ₗ[ℤ] ℤ where
  toFun b := Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
    (Work.Tubular.normalNonzero E) (8 + k) b
    (Work.ThomBordism.chainsHomologyCast (K := Work.Cohomology.relChains
        (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))
      (Nat.add_comm 8 k).symm (Work.Tubular.collapseRelK8 C g hg hR hbox))
  map_add' a b := by
    rw [map_add, LinearMap.add_apply]
  map_smul' n a := by
    rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem collapsePairingMap_apply [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (b : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)) :
    collapsePairingMap E C g hg hR hbox b
      = Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (8 + k) b
        (Work.ThomBordism.chainsHomologyCast (K := Work.Cohomology.relChains
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))
          (Nat.add_comm 8 k).symm (Work.Tubular.collapseRelK8 C g hg hR hbox)) := rfl

/-- **The pairing against the collapse class is injective.** -/
theorem collapseRelK8_pairing_injective [ConnectedSpace V.pt] (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))) :
    Function.Injective (collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j)) := by
  have hcspan : Submodule.span ℤ
      ({(Work.ThomBordism.chainsHomologyCast (K := Work.Cohomology.relChains
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))
        (Nat.add_comm 8 k).symm (Work.Tubular.collapseRelK8 C g hg hR hbox))} : Set
          ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E)).homology (8 + k))) = ⊤ :=
    Work.Tubular.span_cast_singleton_eq_top (M := fun n => (Work.Cohomology.relChains
        (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)).homology n) (Nat.add_comm 8 k).symm
      (Work.Tubular.collapseRelK8_span_top C q hU hR hbox g hg hg2)
  intro a b hab
  have hd : collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hfun : (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) (8 + k) (a - b)) = 0 := by
    apply LinearMap.ext
    intro z
    have hz : z ∈ Submodule.span ℤ
        ({(Work.ThomBordism.chainsHomologyCast (K := Work.Cohomology.relChains
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))
          (Nat.add_comm 8 k).symm (Work.Tubular.collapseRelK8 C g hg hR hbox))} : Set
            ((Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E)).homology (8 + k))) := by
      rw [hcspan]; exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun z _ => (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (8 + k) (a - b)) z = 0) ?_ ?_ ?_ ?_ hz
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hd
    · exact map_zero _
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro n x _ hx
      rw [map_smul, hx, smul_zero]
  have hzero : ∀ z, Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) (8 + k) (a - b) z = 0 := by
    intro z
    rw [show (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (8 + k) (a - b)) z
        = ((0 : (Work.Cohomology.relChains (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E)).homology (8 + k) →ₗ[ℤ] ℤ)) z from by rw [hfun]]
    exact LinearMap.zero_apply z
  exact sub_eq_zero.mp (Work.ThomBordism.normalTotal_relKronH_kernel_bot (V := V) hk E
    (a - b) hzero)

/-- **Equality of relative classes from equality of their pairings with the collapse class.** -/
theorem eq_of_collapseRelK8_pairing_eq [ConnectedSpace V.pt] (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {a b : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)}
    (h : collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j) a
      = collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j) b) : a = b :=
  collapseRelK8_pairing_injective hk E C q hU hR hbox g hg hg2 h

end PairingToolkit

/-- **`PieceP2` implies `KeyLocal`.**

The missing direction of the equivalence `KeyLocal ⟺ PieceP2` (the converse is
`Work.ThomBordism.coorFibre_fibreGenerator_of_keyLocal`).  For a datum of `KeyLocal`:

* produce the collapse data of the tube chart (`tubeChart_collapseToOnePoint_data`) and the fibre
  generator `z` pinned by `PieceP1` (`fibreReading_collapseClass`);
* `PieceP2` gives `⟨coorFibre, z⟩ = t` with a single `t = ±1` over all data, and the frame half
  `nfRes_gtdUWith_realThomClassOf_eq_coorFibre` identifies the fibre reading of the canonical class
  `Ucan` with `coorFibre`, so `⟨w ⌣ Ucan, c⟩ = t`;
* the ambient chart model class pairs to the uniform `κ = ±1` of `AmbientUniform`, so
  `w ⌣ Ucan` and `(t * κ) • ambientValueClass E C x` have equal pairings with the collapse class,
  and `collapseRelK8_pairing_injective` upgrades this to the class equality. -/
theorem keyLocal_of_pieceP2 (k : ℕ) (hk : 1 ≤ k) (hP2 : Work.ThomBordism.PieceP2 k hk) :
    Work.ThomBordism.KeyLocal k hk := by
  classical
  obtain ⟨t, ht, hP2'⟩ := hP2
  obtain ⟨κ, hκ, hAmb⟩ := Work.ThomBordism.ambientUniform_of_claAmbient' k hk
    (Work.ThomBordism.collapseLocalisation_ambientV2 k hk)
  refine ⟨t * κ, ?_, ?_⟩
  · rcases ht with h | h <;> rcases hκ with h' | h' <;> rw [h, h'] <;> norm_num
  · intro V _inst E ND G hgm hbp hvec ε C x w hw
    haveI : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
      Work.Tubular.compactSpace_normalDiscSub E ε
    obtain ⟨q, R, hR, hbox, g, hg2, hg⟩ :=
      Work.ThomBordism.tubeChart_collapseToOnePoint_data (V := V) hk E C
    have hU : IsCompact C.U := C.isCompact_U
    obtain ⟨z, hzspan, hzrel⟩ :=
      Work.ThomBordism.fibreReading_collapseClass (V := V) hk E C q hU hR hbox g hg hg2 x w hw
    have htz := hP2' (V := V) E ND C q hU hR hbox g hg hg2 x w z hw hzspan hzrel
    set Ucan := Work.ThomBordism.gtdUWith E ND G hgm
      (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.tautologicalBundle_horiO k)) with hUcandef
    have hcoor : Work.ThomBordism.nfRes E x k Ucan = Work.ThomBordism.coorFibre hk E ND x :=
      Work.ThomBordism.nfRes_gtdUWith_realThomClassOf_eq_coorFibre hk
        (Work.ThomBordism.tautologicalBundle_horiO k)
        (Work.ThomBordism.frameEval_realThomClassOf k hk
          (Work.ThomBordism.tautologicalBundle_horiO k)) E ND G hgm hbp hvec x
    have hB : collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j)
        (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) 8 k w Ucan) = t := by
      rw [collapsePairingMap_apply,
        ← Work.ThomBordism.relKronH_cast_snd (Nat.add_comm 8 k)
          (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) 8 k w Ucan)
          (Work.Tubular.collapseRelK8 C g hg hR hbox)]
      rw [← hzrel Ucan, hcoor]
      exact htz
    have hA : collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j)
        (Work.ThomBordism.ambientValueClass E C x) = κ := by
      rw [collapsePairingMap_apply,
        ← Work.ThomBordism.relKronH_cast_snd (Nat.add_comm 8 k)
          (Work.ThomBordism.ambientValueClass E C x)
          (Work.Tubular.collapseRelK8 C g hg hR hbox)]
      exact hAmb E C q hU hR hbox g hg hg2 x
    refine collapseRelK8_pairing_injective hk E C q hU hR hbox g hg hg2 ?_
    rw [map_zsmul, hB, hA]
    rcases hκ with h | h
    · rw [h, zsmul_eq_mul]
      first | simp | norm_num | ring
    · rw [h, zsmul_eq_mul]
      first | simp | norm_num | ring

/-- **The target from the witness form of (KL)** (`Work.ThomBordism.KeyLocalWitness`).

`Work.ThomBordism.coorFibre_fibreGenerator.lean` proves `KeyLocalWitness → KeyLocalData`
(`keyLocalData_of_witness'`, using the PROVED uniqueness `admissibleUnique` of the admissible
degree-`8` class), and `KeyLocalData` is `KeyLocal` with `ambientValueClass` unfolded.  The witness
form is the version in which the local comparison may be *computed* for one explicitly constructed
class per datum (the "bump" class), the sign thereby being *determined* rather than asserted to be
uniform - the natural form of the geometric argument (i)-(v). -/
theorem keyLocalProof_of_witness (k : ℕ) (hk : 1 ≤ k)
    (hwit : Work.ThomBordism.KeyLocalWitness k hk) : Work.ThomBordism.KeyLocal k hk := by
  simpa only [Work.ThomBordism.KeyLocal, Work.ThomBordism.KeyLocalData,
    Work.ThomBordism.ambientValueClass]
    using Work.ThomBordism.keyLocalData_of_witness' k hk hwit


/-! ## The reduction of the target to the single local-degree statement about `Ucan`

`Work.ThomBordism.PieceP2` is the only unproved node of the local-degree chapter (see
`Submission/Work/ThomBordism/localDegree_localisation.lean` and
`NOTE_SESSION8_STATE.md`), and `keyLocal_of_pieceP2` above derives the target from it.  The lemma
below records the *shortest* remaining route to `PieceP2`:

**it suffices that the canonical class `Ucan = gtdUWith E ND G hgm (realThomClassOf …)` is a
local-degree class of the tube, for every datum.**

Indeed, for a datum with admissible `w` and fibre generator `z` satisfying the localisation identity
of `PieceP1` (`fibreReading_collapseClass`),

  `⟨coorFibre, z⟩ = ⟨nfRes Ucan, z⟩ = ⟨w ⌣ Ucan, c⟩`,

the first equality by the PROVED frame half `nfRes_gtdUWith_realThomClassOf_eq_coorFibre`, the
second by `hzrel` at `U = Ucan`; if `Ucan` is a local-degree class then the last term is
`⟨(zeroSection)^* w, V.c⟩ = 1` by the admissibility of `w`, so `t = 1` for every datum — i.e. the
uniformity of `PieceP2` is automatic, and no datum-dependent sign survives.

Thus `KeyLocal` follows from `∀ datum, IsLocalDegreeClass C g hg hR hbox Ucan`. -/
theorem pieceP2_of_isLocalDegreeClass (k : ℕ) (hk : 1 ≤ k)
    (hild : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (Work.ThomBordism.gtdUWith E ND G hgm
          (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.tautologicalBundle_horiO k)))) :
    Work.ThomBordism.PieceP2 k hk := by
  classical
  refine ⟨1, Or.inl rfl, ?_⟩
  intro V _inst E ND ε C q hU R hR hbox g hg hg2 x w z hw hzspan hzrel
  obtain ⟨G, hbp, hvec, hgm, -⟩ :=
    Work.ThomBordism.gtdGaussCandidate (V := V) (k := k) E ND C.eps_pos C q hU hR hbox g hg hg2
  set Ucan := Work.ThomBordism.gtdUWith E ND G hgm
      (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.tautologicalBundle_horiO k)) with hUcandef
  have hcoor : Work.ThomBordism.nfRes E x k Ucan = Work.ThomBordism.coorFibre hk E ND x :=
    Work.ThomBordism.nfRes_gtdUWith_realThomClassOf_eq_coorFibre hk
      (Work.ThomBordism.tautologicalBundle_horiO k)
      (Work.ThomBordism.frameEval_realThomClassOf k hk
        (Work.ThomBordism.tautologicalBundle_horiO k))
      E ND G hgm hbp hvec x
  have hld := hild E ND G hgm hbp hvec C q hU hR hbox g hg hg2
  rw [← hcoor, hzrel Ucan, hld w, hw]

/-- **The target from the single local-degree statement about `Ucan`.** -/
theorem keyLocal_of_isLocalDegreeClass (k : ℕ) (hk : 1 ≤ k)
    (hild : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (Work.ThomBordism.gtdUWith E ND G hgm
          (Work.Thom.realThomClassOf hk (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.tautologicalBundle_horiO k)))) :
    Work.ThomBordism.KeyLocal k hk :=
  keyLocal_of_pieceP2 k hk (pieceP2_of_isLocalDegreeClass k hk hild)




/-- **The target from the tube-level comparison of `w ⌣ Ucan` with the ambient class.**

The hypothesis `H` is the single remaining geometric statement: for every datum and every admissible
`w`, the pullback of `mixedCup w Ucan` along the tube inverse equals a *single* sign `s` times the
ambient standard class of the tube (`(y ↦ y - E.e x)^*(stdModelGen (8 + k))`).  Its content is exactly
pieces (T1) + (T2) + the model product formula + the germ comparison (GM) of the last-mile plan.

The reduction to it uses only PROVED material: `tubePairingConvert` (the naturality of the relative
Kronecker pairing along the tube inverse, in the general form), the proved
`ambientStandardClass_eq_chartModelClass`, and the injectivity `collapseRelK8_pairing_injective`. -/
theorem keyLocal_of_tubeComparison (k : ℕ) (hk : 1 ≤ k)
    (H : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
        (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
        (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)))
        (hw : Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1),
        ∃ (q : Work.Tubular.NormalSphSub E ε) (hU : IsCompact C.U) (R : ℝ) (hR : 0 ≤ R)
          (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
          (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
          (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
          (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y)
            = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
          (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
              (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
              (fun y hy => hy) ℤ (8 + k)).hom
            (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E) 8 k w
              (Work.ThomBordism.gtdUWith E ND G hgm
                (Work.Thom.realThomClassOf hk
                  (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                  (Work.ThomBordism.tautologicalBundle_horiO k))))
            = s • Work.ThomBordism.ambientStandardClass E C x) :
    Work.ThomBordism.KeyLocal k hk := by
  classical
  obtain ⟨s, hs, H'⟩ := H
  refine ⟨s, hs, ?_⟩
  intro V _inst E ND G hgm hbp hvec ε C x w hw
  obtain ⟨q, hU, R, hR, hbox, g, hg, hg2, hcmp⟩ := H' E ND G hgm hbp hvec C x w hw
  obtain ⟨δ, hδ⟩ := Work.ThomBordism.tubeInvHomologyCollapse (V := V) (k := k) E C g hg hg2
    hR hbox
  set Ucan := Work.ThomBordism.gtdUWith E ND G hgm
      (Work.Thom.realThomClassOf hk
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.tautologicalBundle_horiO k)) with hUcan
  set cK := Work.Tubular.collapseRelK8 C g hg hR hbox with hcK
  -- the pairing conversion along the tube inverse, for any class `X`
  have keypair : ∀ X : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E),
      collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j) X
        = Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
            (k + 8)
            (Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
              (Nat.add_comm 8 k) ((Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
              (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
              (fun y hy => hy) ℤ (8 + k)).hom X)) δ := by
    intro X
    rw [collapsePairingMap_apply,
      ← Work.ThomBordism.relKronH_cast_snd (Nat.add_comm 8 k) X cK]
    exact (Work.ThomBordism.KeyLocal.tubePairingConvert (V := V) E C g hg hR hbox δ hδ X).symm
  -- the tube inverse of the ambient chart model class is the ambient standard class
  have hstd : (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
        (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
        (fun y hy => hy) ℤ (8 + k)).hom
        (Work.ThomBordism.ambientValueClass E C x)
      = Work.ThomBordism.ambientStandardClass E C x := by
    show (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
        (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
        (fun y hy => hy) ℤ (8 + k)).hom
        (Work.ThomBordism.chartModelClass E C x
          (Work.ThomBordism.continuous_chartAffine_cap E C x))
      = Work.ThomBordism.ambientStandardClass E C x
    exact Work.ThomBordism.ambientStandardClass_eq_chartModelClass E C x
      (Work.ThomBordism.continuous_chartAffine_cap E C x)
  -- the transport across the degree change commutes with the integer multiple
  have hcastsmul : Work.Tubular.relKronH (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        (Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
          (Nat.add_comm 8 k) (s • Work.ThomBordism.ambientStandardClass E C x)) δ
      = s * Work.Tubular.relKronH (TopCat.of ↥C.U)
          (Work.ThomBordism.tubeInvPunct E C) (k + 8)
          (Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
            (Nat.add_comm 8 k) (Work.ThomBordism.ambientStandardClass E C x)) δ := by
    rw [Work.ThomBordism.relKronH_cast_snd (Nat.add_comm 8 k)
          (s • Work.ThomBordism.ambientStandardClass E C x) δ,
      Work.ThomBordism.relKronH_cast_snd (Nat.add_comm 8 k)
          (Work.ThomBordism.ambientStandardClass E C x) δ]
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  -- the two class-level transports
  have hclassL : Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
        (Nat.add_comm 8 k) ((Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
          (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
          (fun y hy => hy) ℤ (8 + k)).hom
          (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) 8 k w Ucan))
      = Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
        (Nat.add_comm 8 k) (s • Work.ThomBordism.ambientStandardClass E C x) :=
    congrArg (Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
      (Nat.add_comm 8 k)) hcmp
  have hclassR : Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
        (Nat.add_comm 8 k) ((Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
          (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
          (fun y hy => hy) ℤ (8 + k)).hom
          (Work.ThomBordism.ambientValueClass E C x))
      = Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
        (Nat.add_comm 8 k) (Work.ThomBordism.ambientStandardClass E C x) :=
    congrArg (Work.ThomBordism.FrameSigns.RelCohCast (Work.ThomBordism.tubeInvPunct E C)
      (Nat.add_comm 8 k)) hstd
  have hsmul : collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j)
        (s • Work.ThomBordism.ambientValueClass E C x)
      = s * collapsePairingMap (k := k) E C g hg hR (fun y hy j => hbox y hy j)
        (Work.ThomBordism.ambientValueClass E C x) := by
    rw [map_zsmul, smul_eq_mul]
  refine eq_of_collapseRelK8_pairing_eq hk E C q hU hR hbox g hg hg2 ?_
  rw [hsmul,
      keypair (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w Ucan),
      keypair (Work.ThomBordism.ambientValueClass E C x),
      hclassL, hclassR]
  exact hcastsmul


/-- **The per-datum tube comparison**, in the clean form in which the geometric argument proves it:
for every datum and every admissible degree-`8` class `w` of the normal total space, the pullback
of `mixedCup 8 k w Ucan` along the tube inverse is a *single* sign `s = ±1` times the determinate
ambient standard class of the tube.  Unlike the hypothesis of `keyLocal_of_tubeComparison` it does
not mention the collapse data (the identity does not depend on them), so it can be produced by the
local computation on a chart of the normal datum. -/
def TubeCompare (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
      (w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E))),
      Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 →
      (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
          (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
          (fun y hy => hy) ℤ (8 + k)).hom
        (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) 8 k w
          (Work.ThomBordism.gtdUWith E ND G hgm
            (Work.Thom.realThomClassOf hk
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.tautologicalBundle_horiO k))))
        = s • Work.ThomBordism.ambientStandardClass E C x

/-- **`TubeCompare` implies the target.**  The collapse data required by
`keyLocal_of_tubeComparison` are produced by `Work.ThomBordism.tubeChart_collapseToOnePoint_data`. -/
theorem keyLocal_of_tubeCompare (k : ℕ) (hk : 1 ≤ k) (H : TubeCompare k hk) :
    Work.ThomBordism.KeyLocal k hk := by
  obtain ⟨s, hs, H'⟩ := H
  refine keyLocal_of_tubeComparison k hk ⟨s, hs, ?_⟩
  intro V _ E ND G hgm hbp hvec ε C x w hw
  haveI : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.compactSpace_normalDiscSub E ε
  obtain ⟨q, R, hR, hbox, g, hg2, hg⟩ :=
    Work.ThomBordism.tubeChart_collapseToOnePoint_data (V := V) hk E C
  exact ⟨q, C.isCompact_U, R, hR, hbox, g, hg, hg2, H' E ND G hgm hbp hvec C x w hw⟩

/-- **The requested lemma.**

The last mile is now a chain of proved statements:

* `Work.ThomBordism.KeyLocal.chartCompareAll` — the four geometric pieces assembled on a chart of
  the normal datum (`chartCompare`);
* `Work.ThomBordism.KeyLocal.tubePointRelative` — the pair-mismatch step moving that comparison to
  the whole tube relative to the point `E.e x`;
* `Work.ThomBordism.KeyLocal.perDatum` — the passage from the point-relative comparison of the bump
  class `π^*(relToAbs o)` to the per-datum comparison of *every* admissible class `w`, using the
  uniqueness of the admissible class;
* `Work.ThomBordism.KeyLocal.tubeCompareAll` — the resulting `TubeCompareAll k hk`;
* `keyLocal_of_tubeCompare` above — `TubeCompare` (the same statement) implies `KeyLocal`. -/
theorem keyLocalProof (k : ℕ) (hk : 1 ≤ k) : Work.ThomBordism.KeyLocal k hk :=
  keyLocal_of_tubeCompare k hk (KeyLocal.tubeCompareAll k hk)

end

end Work.ThomBordism
