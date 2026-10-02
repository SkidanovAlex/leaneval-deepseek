import Mathlib
import Submission.Work.Thom.pieceMap
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.naturalModelClass
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-!
# The chart local Thom class is natural under a pullback of the bundle

For a real bundle `Z → B` with model fibre `F` of rank `n` and a chart index `i`, the explicit local
Thom class `Work.Thom.localThomOfChart Z n e i W hW` over a subset `W ⊆ Z.baseSet i` is built from
the natural model class `Work.Thom.Mpun n ↥W` of the punctured trivial bundle by pulling back along
the chart homeomorphism `↥(Z.proj ⁻¹' W) ≃ₜ ↥W × ℝⁿ`
(`Submission/Work/Thom/ChartOrientation.lean`).

The present file proves that this construction is natural under a *pullback of the bundle*: for a
continuous map `f : C(B', B)` and subsets `W ⊆ Z.baseSet i`, `W' ⊆ (f^*Z).baseSet i` with
`f '' W' ⊆ W`, the pullback of `localThomOfChart Z … W` along the canonical map of the pieces
`Work.Thom.pieceMap` is `localThomOfChart (bundleComap Z f) … W'`.

Unwinding the definitions, this is the statement that the natural model class `Mpun` of the punctured
trivial bundle is natural in the base not only for *inclusions* `↥W × ℝⁿ → B × ℝⁿ` of a subset (which
is `Work.Thom.Mpun_natural`) but for an *arbitrary* continuous map `g : C(B', B)`.  The base change
of the trivial bundle is the map `Work.Thom.comapProdMap g F : B' × F → B × F`, `(x, v) ↦ (g x, v)`.

The proof is by the same induction as in `Submission/Work/Thom/naturalModelClass.lean`, run for a
general base change instead of an inclusion:

* `comapDiscFullMap_comp`, `comapCapMapPairSph_comp`, `comapProdSubsetHomeoA_symm_comp` — the base
  change commutes with the three structural maps of the model induction (all definitional);
* `baseChange_stepDisc_natural`, `baseChange_stepSph_natural`, `baseChange_step_natural` — the
  naturality of the disc transfer, of the cap transfer, and of the inductive step;
* `baseChange_Mn_natural` — the naturality of the model class `Mn` by induction on `n`;
* `jMap_comp_comapProdMap`, `comapProdMap_sph_comp_jMap` — the two squares comparing the pullback of
  a punctured class with the pullback of the corresponding sphere-pair class;
* `baseChange_Mpun_natural` — the naturality of `Mpun`, obtained from `baseChange_Mn_natural` by
  the characterisation `Mpun_spec` of `Mpun` and the injectivity of the pair inclusion
  `(B × ℝⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × (ℝⁿ∖0))` (`bijective_jMap`).
-/

namespace Work.Thom

open CategoryTheory

noncomputable section

/-! ## The base change of a product

`Work.Thom.comapProdMap g F` is the map `(x, v) ↦ (g x, v)` from `B' × F` to `B × F`; it is `g` on
the base and the identity on the fibre.  It is the map along which the trivial bundle with fibre `F`
is pulled back. -/

/-- **The base change of a product along `g`**: the map `B' × F → B × F`, `(x, v) ↦ (g x, v)`. -/
def comapProdMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] (g : C(B', B))
    (F : Type) [TopologicalSpace F] : C(B' × F, B × F) :=
  ⟨fun p => (g p.1, p.2), g.continuous.comp continuous_fst |>.prodMk continuous_snd⟩

theorem comapProdMap_apply {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (F : Type) [TopologicalSpace F] (p : B' × F) :
    comapProdMap g F p = (g p.1, p.2) := rfl

/-! ## Commutation with the structural maps of the model induction -/

/-- The disc-transfer map `CleanA.discFullMap` commutes with the base change. -/
theorem comapDiscFullMap_comp {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ) :
    (CleanA.discFullMap B n).comp (comapProdMap g (MBall n))
      = (comapProdMap g (EuclideanSpace ℝ (Fin n))).comp (CleanA.discFullMap B' n) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- The cap map `capMapPairSph` commutes with the base change. -/
theorem comapCapMapPairSph_comp {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ) :
    (capMapPairSph B n).comp (comapProdMap g (MBall n))
      = (comapProdMap g (MSph (n + 1))).comp (capMapPairSph B' n) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- The homeomorphism `prodSubsetHomeoA.symm` commutes with the base change. -/
theorem comapProdSubsetHomeoA_symm_comp {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ) :
    (comapProdMap g (MSph (n + 1))).comp
        ((prodSubsetHomeoA B' (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1))).symm :
          C(↥(Sph B' (n + 1)), B' × MSph (n + 1)))
      = ((prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1))).symm :
          C(↥(Sph B (n + 1)), B × MSph (n + 1))).comp
        (restrictMap (comapProdMap g (EuclideanSpace ℝ (Fin (n + 1))))
          (Sph B' (n + 1)) (Sph B (n + 1)) (fun _ h => h)) := by
  apply ContinuousMap.ext
  intro p
  rfl

/-! ## Naturality of the three steps of the model induction -/

/-- **Naturality of the disc transfer `stepDisc` under a base change.** -/
theorem baseChange_stepDisc_natural {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    (relCohMap (comapProdMap g (MBall n))
        (DiscB B' n) (DiscB B n) (fun _ h => h) ℤ n).hom (stepDisc B n τ)
      = stepDisc B' n
          ((relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
            (Sph B' n) (Sph B n) (fun _ h => h) ℤ n).hom τ) := by
  rw [stepDisc, stepDisc]
  rw [relCohMap_compA_apply (DiscB B' n) (DiscB B n) (Sph B n) (comapProdMap g (MBall n))
        (CleanA.discFullMap B n) (fun _ h => h) (CleanA.discFullMap_mem B n) (fun _ h => h) ℤ n τ]
  rw [relCohMap_compA_apply (DiscB B' n) (Sph B' n) (Sph B n) (CleanA.discFullMap B' n)
        (comapProdMap g (EuclideanSpace ℝ (Fin n))) (CleanA.discFullMap_mem B' n)
        (fun _ h => h) (fun _ h => h) ℤ n τ]
  have hm : relCohMap ((CleanA.discFullMap B n).comp (comapProdMap g (MBall n)))
        (DiscB B' n) (Sph B n) (fun _ h => h) ℤ n
      = relCohMap ((comapProdMap g (EuclideanSpace ℝ (Fin n))).comp (CleanA.discFullMap B' n))
        (DiscB B' n) (Sph B n) (fun _ h => h) ℤ n :=
    relCohMap_congrA (DiscB B' n) (Sph B n) (comapDiscFullMap_comp g n)
      (fun _ h => h) (fun _ h => h) ℤ n
  rw [hm]

/-- **Naturality of the cap transfer `stepSph` under a base change.** -/
theorem baseChange_stepSph_natural {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    (relCohMap (comapProdMap g (MSph (n + 1)))
        (SphB B' n) (SphB B n) (fun _ h => h) ℤ n).hom (stepSph B n τ)
      = stepSph B' n
          ((relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
            (Sph B' n) (Sph B n) (fun _ h => h) ℤ n).hom τ) := by
  have hinj : Function.Injective ((relCohMap (capMapPairSph B' n) (DiscB B' n) (SphB B' n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n).hom) :=
    (CleanA.capRelCohIso B' n n).1
  apply hinj
  rw [relCohMap_compA_apply (DiscB B' n) (SphB B' n) (SphB B n) (capMapPairSph B' n)
        (comapProdMap g (MSph (n + 1))) (CleanA.capMapPairSph_mem_mLower n) (fun _ h => h)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n (stepSph B n τ)]
  rw [stepSph_spec B' n
        ((relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
          (Sph B' n) (Sph B n) (fun _ h => h) ℤ n).hom τ)]
  have hm2 : relCohMap ((comapProdMap g (MSph (n + 1))).comp (capMapPairSph B' n))
        (DiscB B' n) (SphB B n)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n
      = relCohMap ((capMapPairSph B n).comp (comapProdMap g (MBall n)))
        (DiscB B' n) (SphB B n)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n :=
    relCohMap_congrA (DiscB B' n) (SphB B n) (comapCapMapPairSph_comp g n).symm
      (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx)
      (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n
  rw [hm2]
  rw [← relCohMap_compA_apply (DiscB B' n) (DiscB B n) (SphB B n) (comapProdMap g (MBall n))
        (capMapPairSph B n) (fun _ h => h) (CleanA.capMapPairSph_mem_mLower n)
        (fun x hx => CleanA.capMapPairSph_mem_mLower n x hx) ℤ n (stepSph B n τ)]
  rw [stepSph_spec B n τ]
  rw [baseChange_stepDisc_natural g n τ]

/-- **The inductive step `step` is natural under a base change.** -/
theorem baseChange_step_natural {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    step B' n
        ((relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
          (Sph B' n) (Sph B n) (fun _ h => h) ℤ n).hom τ)
      = (relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin (n + 1))))
          (Sph B' (n + 1)) (Sph B (n + 1)) (fun _ h => h) ℤ (n + 1)).hom (step B n τ) := by
  rw [step, step]
  rw [pairDeltaNatural_restrict (comapProdMap g (EuclideanSpace ℝ (Fin (n + 1))))
        (Sph B' (n + 1)) (Sph B (n + 1)) (fun _ h => h) n]
  refine congrArg (fun w => (pairδC (Sph B' (n + 1)) n).hom w) ?_
  rw [← baseChange_stepSph_natural g n τ]
  rw [relCohMap_relToAbs_apply (comapProdMap g (MSph (n + 1)))
        (SphB B' n) (SphB B n) (fun _ h => h) ℤ n (stepSph B n τ)]
  rw [CohMap_comp_apply
        ((prodSubsetHomeoA B' (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1))).symm :
          C(↥(Sph B' (n + 1)), B' × MSph (n + 1)))
        (comapProdMap g (MSph (n + 1))) ℤ n
        ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ))]
  rw [comapProdSubsetHomeoA_symm_comp g n]
  rw [CohMap_comp_apply
        (restrictMap (comapProdMap g (EuclideanSpace ℝ (Fin (n + 1))))
          (Sph B' (n + 1)) (Sph B (n + 1)) (fun _ h => h))
        ((prodSubsetHomeoA B (EuclideanSpace ℝ (Fin (n + 1))) (mSph (n + 1))).symm :
          C(↥(Sph B (n + 1)), B × MSph (n + 1))) ℤ n
        ((relToAbs ℤ (SphB B n) n).hom (stepSph B n τ))]

/-! ## Naturality of the model class `Mn` -/

/-- **The model class `Mn` is natural in the base along an arbitrary continuous map.** -/
theorem baseChange_Mn_natural (n : ℕ) :
    ∀ (B : Type) [TopologicalSpace B] (B' : Type) [TopologicalSpace B'] (g : C(B', B)),
      (relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
        (Sph B' n) (Sph B n) (fun _ h => h) ℤ n).hom (Mn n B) = Mn n B' := by
  induction n with
  | zero =>
      intro B _ B' _ g
      apply (bijective_relToAbs_sphZero B').1
      rw [relCohMap_relToAbs_apply (comapProdMap g (EuclideanSpace ℝ (Fin 0)))
            (Sph B' 0) (Sph B 0) (fun _ h => h) ℤ 0 (Mn 0 B)]
      rw [Mn_zero_spec B, Mn_zero_spec B']
      exact CohMap_oneH (comapProdMap g (EuclideanSpace ℝ (Fin 0)))
  | succ m ih =>
      intro B _ B' _ g
      show (relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin (m + 1))))
            (Sph B' (m + 1)) (Sph B (m + 1)) (fun _ h => h) ℤ (m + 1)).hom
          (step B m (Mn m B)) = step B' m (Mn m B')
      rw [← baseChange_step_natural g m (Mn m B), ih B B' g]

/-! ## Naturality of the punctured model class `Mpun` -/

/-- **The pair inclusion commutes with the base change** (the sphere-pair form): pulling a punctured
class back along `comapProdMap g` and then applying the isomorphism
`(B × ℝⁿ, B × Sⁿ⁻¹) → (B × ℝⁿ, B × (ℝⁿ∖0))` gives the same as pulling the class back along
`comapProdMap g` viewed as a map of sphere-bundle pairs. -/
theorem jMap_comp_comapProdMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (x : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    (relCohMap (ContinuousMap.id (B' × EuclideanSpace ℝ (Fin n)))
        (Sph B' n) (Punct B' n) (mem_Sph_punct B' n) ℤ n).hom
        ((relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
          (Punct B' n) (Punct B n) (fun _ hp => hp) ℤ n).hom x)
      = (relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
          (Sph B' n) (Punct B n) (fun y hy => mem_Sph_punct B' n y hy) ℤ n).hom x := by
  rw [relCohMap_compA_apply (Sph B' n) (Punct B' n) (Punct B n)
        (ContinuousMap.id (B' × EuclideanSpace ℝ (Fin n)))
        (comapProdMap g (EuclideanSpace ℝ (Fin n)))
        (mem_Sph_punct B' n) (fun _ hp => hp) (fun y hy => mem_Sph_punct B' n y hy) ℤ n x]
  rw [relCohMap_congrA (Sph B' n) (Punct B n)
        (ContinuousMap.comp_id (comapProdMap g (EuclideanSpace ℝ (Fin n))))
        (fun y hy => mem_Sph_punct B' n y hy) (fun y hy => mem_Sph_punct B' n y hy) ℤ n]

/-- **The other square**: pulling a punctured class back along `comapProdMap g` (as a map of sphere
pairs into the punctured pair) equals pulling its image under the pair inclusion back as a map of
sphere-bundle pairs. -/
theorem comapProdMap_sph_comp_jMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) (n : ℕ)
    (x : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Punct B n)) :
    (relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
        (Sph B' n) (Punct B n) (fun y hy => mem_Sph_punct B' n y hy) ℤ n).hom x
      = (relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
          (Sph B' n) (Sph B n) (fun _ h => h) ℤ n).hom
          ((relCohMap (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
            (Sph B n) (Punct B n) (mem_Sph_punct B n) ℤ n).hom x) := by
  rw [relCohMap_compA_apply (Sph B' n) (Sph B n) (Punct B n)
        (comapProdMap g (EuclideanSpace ℝ (Fin n)))
        (ContinuousMap.id (B × EuclideanSpace ℝ (Fin n)))
        (fun _ h => h) (mem_Sph_punct B n)
        (fun y hy => mem_Sph_punct B' n y hy) ℤ n x]
  rw [relCohMap_congrA (Sph B' n) (Punct B n)
        (ContinuousMap.id_comp (comapProdMap g (EuclideanSpace ℝ (Fin n))))
        (fun y hy => mem_Sph_punct B' n y hy) (fun y hy => mem_Sph_punct B' n y hy) ℤ n]

/-- **The punctured model class `Mpun` is natural in the base along an arbitrary continuous
map.**  This is the statement that the `Classical.choose` defining `Mpun` (`Work.Thom.Mpun_spec`)
commutes with a base change, and it is what makes the explicit chart class
`Work.Thom.localThomOfChart` natural under a pullback of the bundle. -/
theorem baseChange_Mpun_natural (n : ℕ) :
    ∀ (B : Type) [TopologicalSpace B] (B' : Type) [TopologicalSpace B'] (g : C(B', B)),
      (relCohMap (comapProdMap g (EuclideanSpace ℝ (Fin n)))
        (Punct B' n) (Punct B n) (fun _ hp => hp) ℤ n).hom (Mpun n B) = Mpun n B' := by
  intro B _ B' _ g
  apply (bijective_jMap B' n n).1
  rw [jMap_comp_comapProdMap g n (Mpun n B), Mpun_spec n B']
  rw [comapProdMap_sph_comp_jMap g n (Mpun n B), Mpun_spec n B]
  exact baseChange_Mn_natural n B B' g

/-! ## The chart local Thom class is natural under a pullback of the bundle -/

theorem localThomOfChart_comap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (f : C(B', B))
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i : ι)
    {W : Set B} {W' : Set B'} (hW : W ⊆ Z.baseSet i)
    (hW' : W' ⊆ (Work.Thom.bundleComap Z f).baseSet i) (hWf : ∀ x ∈ W', f x ∈ W) :
    (Work.Thom.relCohMap (Work.Thom.pieceMap Z f hWf)
      (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W') (Work.Thom.pieceZero Z W)
      (fun p hp => by
        show (show F from ((Work.Thom.pieceMap Z f hWf p : Z.TotalSpace)).2) ≠ 0
        have h1 : (show F from ((Work.Thom.pieceMap Z f hWf p : Z.TotalSpace)).2)
            = (show F from p.1.2) := by
          rw [Work.Thom.pieceMap_apply]
        rw [h1]
        exact hp) ℤ n).hom (Work.Thom.localThomOfChart Z n e i W hW).τ
      = (Work.Thom.localThomOfChart (Work.Thom.bundleComap Z f) n e i W' hW').τ := by
  let fr : C(↥W', ↥W) :=
    ⟨fun x => ⟨f x, hWf x x.2⟩,
      Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) (fun x => hWf x x.2)⟩
  have hgen : ∀ (h : ∀ p ∈ Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W',
        Work.Thom.pieceMap Z f hWf p ∈ Work.Thom.pieceZero Z W),
      (Work.Thom.relCohMap (Work.Thom.pieceMap Z f hWf)
        (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W') (Work.Thom.pieceZero Z W)
        h ℤ n).hom (Work.Thom.localThomOfChart Z n e i W hW).τ
      = (Work.Thom.localThomOfChart (Work.Thom.bundleComap Z f) n e i W' hW').τ := by
    intro h
    rw [Work.Thom.localThomOfChart_tau, Work.Thom.localThomOfChart_tau]
    have hZ : ∀ p ∈ Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W',
        (Work.Thom.chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
          (Work.Thom.pieceMap Z f hWf p) ∈ Work.Thom.Punct ↥W n :=
      fun p hp => Work.Thom.chartHomeo_mem Z n e i W hW _ (h p hp)
    have hMpun : (Work.Thom.relCohMap (comapProdMap fr (EuclideanSpace ℝ (Fin n)))
          (Work.Thom.Punct ↥W' n) (Work.Thom.Punct ↥W n) (fun _ hp => hp) ℤ n).hom
        (Work.Thom.Mpun n ↥W) = Work.Thom.Mpun n ↥W' :=
      baseChange_Mpun_natural n ↥W ↥W' fr
    have hpoint : ∀ p : ↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
        (comapProdMap fr (EuclideanSpace ℝ (Fin n)))
            ((Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW') p)
          = (Work.Thom.chartHomeo Z n e i W hW) (Work.Thom.pieceMap Z f hWf p) := by
      intro p
      have harg : (Work.Thom.pieceMap Z f hWf p)
          = (⟨⟨f p.1.1, p.1.2⟩, hWf p.1.1 p.2⟩ : ↥(Z.proj ⁻¹' W)) :=
        Subtype.ext (Work.Thom.pieceMap_apply Z f hWf p)
      rw [harg]
      simp only [comapProdMap, Work.Thom.chartHomeo_apply]
      rfl
    have hmap : (comapProdMap fr (EuclideanSpace ℝ (Fin n))).comp
          (Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW' :
            C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
              ↥W' × EuclideanSpace ℝ (Fin n)))
        = (Work.Thom.chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))).comp
          (Work.Thom.pieceMap Z f hWf) := by
      apply ContinuousMap.ext
      intro p
      exact hpoint p
    have hcomp : ∀ p ∈ Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W',
        (comapProdMap fr (EuclideanSpace ℝ (Fin n)))
          ((Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW') p)
          ∈ Work.Thom.Punct ↥W n := by
      intro p hp
      rw [hpoint p]
      exact hZ p hp
    have hL : (Work.Thom.relCohMap (Work.Thom.pieceMap Z f hWf)
          (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W') (Work.Thom.pieceZero Z W)
          h ℤ n).hom
        ((Work.Thom.relCohMap (Work.Thom.chartHomeo Z n e i W hW :
            C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
          (Work.Thom.pieceZero Z W) (Work.Thom.Punct ↥W n)
          (Work.Thom.chartHomeo_mem Z n e i W hW) ℤ n).hom (Work.Thom.Mpun n ↥W))
        = (Work.Thom.relCohMap
            ((Work.Thom.chartHomeo Z n e i W hW :
              C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))).comp
              (Work.Thom.pieceMap Z f hWf))
            (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
            (Work.Thom.Punct ↥W n) hZ ℤ n).hom (Work.Thom.Mpun n ↥W) :=
      Work.Thom.relCohMap_compA_apply _ _ _
        (Work.Thom.pieceMap Z f hWf)
        (Work.Thom.chartHomeo Z n e i W hW :
          C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n)))
        h (Work.Thom.chartHomeo_mem Z n e i W hW) hZ ℤ n (Work.Thom.Mpun n ↥W)
    have hR1 : (Work.Thom.relCohMap
          (Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW' :
            C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
              ↥W' × EuclideanSpace ℝ (Fin n)))
          (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
          (Work.Thom.Punct ↥W' n)
          (Work.Thom.chartHomeo_mem (Work.Thom.bundleComap Z f) n e i W' hW') ℤ n).hom
          (Work.Thom.Mpun n ↥W')
        = (Work.Thom.relCohMap
            (Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW' :
              C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
                ↥W' × EuclideanSpace ℝ (Fin n)))
            (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
            (Work.Thom.Punct ↥W' n)
            (Work.Thom.chartHomeo_mem (Work.Thom.bundleComap Z f) n e i W' hW') ℤ n).hom
          ((Work.Thom.relCohMap (comapProdMap fr (EuclideanSpace ℝ (Fin n)))
            (Work.Thom.Punct ↥W' n) (Work.Thom.Punct ↥W n) (fun _ hp => hp) ℤ n).hom
            (Work.Thom.Mpun n ↥W)) := by
      rw [hMpun]
    have hR2 : (Work.Thom.relCohMap
          (Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW' :
            C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
              ↥W' × EuclideanSpace ℝ (Fin n)))
          (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
          (Work.Thom.Punct ↥W' n)
          (Work.Thom.chartHomeo_mem (Work.Thom.bundleComap Z f) n e i W' hW') ℤ n).hom
          ((Work.Thom.relCohMap (comapProdMap fr (EuclideanSpace ℝ (Fin n)))
            (Work.Thom.Punct ↥W' n) (Work.Thom.Punct ↥W n) (fun _ hp => hp) ℤ n).hom
            (Work.Thom.Mpun n ↥W))
        = (Work.Thom.relCohMap
            ((comapProdMap fr (EuclideanSpace ℝ (Fin n))).comp
              (Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW' :
                C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
                  ↥W' × EuclideanSpace ℝ (Fin n))))
            (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
            (Work.Thom.Punct ↥W n) hcomp ℤ n).hom (Work.Thom.Mpun n ↥W) :=
      Work.Thom.relCohMap_compA_apply _ _ _
        (Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW' :
          C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
            ↥W' × EuclideanSpace ℝ (Fin n)))
        (comapProdMap fr (EuclideanSpace ℝ (Fin n)))
        (Work.Thom.chartHomeo_mem (Work.Thom.bundleComap Z f) n e i W' hW')
        (fun _ hp => hp) hcomp ℤ n (Work.Thom.Mpun n ↥W)
    have hR3 : (Work.Thom.relCohMap
          ((comapProdMap fr (EuclideanSpace ℝ (Fin n))).comp
            (Work.Thom.chartHomeo (Work.Thom.bundleComap Z f) n e i W' hW' :
              C(↥((Work.Thom.bundleComap Z f).proj ⁻¹' W'),
                ↥W' × EuclideanSpace ℝ (Fin n))))
          (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
          (Work.Thom.Punct ↥W n) hcomp ℤ n).hom (Work.Thom.Mpun n ↥W)
        = (Work.Thom.relCohMap
            ((Work.Thom.chartHomeo Z n e i W hW :
              C(↥(Z.proj ⁻¹' W), ↥W × EuclideanSpace ℝ (Fin n))).comp
              (Work.Thom.pieceMap Z f hWf))
            (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
            (Work.Thom.Punct ↥W n) hZ ℤ n).hom (Work.Thom.Mpun n ↥W) :=
      congrArg (fun φ => φ.hom (Work.Thom.Mpun n ↥W))
        (Work.Thom.relCohMap_congrA (Work.Thom.pieceZero (Work.Thom.bundleComap Z f) W')
          (Work.Thom.Punct ↥W n) hmap hcomp hZ ℤ n)
    exact hL.trans (hR1.trans (hR2.trans hR3)).symm
  exact hgen _

end

end Work.Thom
