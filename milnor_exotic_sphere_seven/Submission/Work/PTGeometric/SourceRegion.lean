import Submission.Work.PTGeometric.ContinuousToPreData
import Submission.Work.PTGeometric.ConcreteCollapse

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the source construction in *region* form

`Work.PTGeometric.ConcreteLastMileSource` (`ConcreteCollapse.lean`) is the residual geometric
statement of the last mile: from the null-homotopy of the `m`-fold genuine collapse class of a family,
produce the ambient collapse-end data (`AmbientCollapseEnd`) of a positive multiple of the family, plus
the orientation datum (`AmbientOrientationData`).

The ambient collapse-end data, however, *contain a manifold-with-boundary structure* (`M` with
`ChartedSpace (EuclideanHalfSpace (9+k))` and `IsManifold (𝓡∂ (9+k)) ∞`), and that structure is a
*consequence* of the geometry, not an input to it: the source is the regular region
`{Φ ≤ 0} ⊆ A` cut out in the annulus by a defining function of the core preimage of the
null-homotopy.  This file makes that split explicit:

* `Work.PTGeometric.RegionManifoldTheorem N` — the **region-charting theorem** (a Mathlib gap): a
  smooth function on a compact smooth manifold `A` with boundary whose zero set is a regular level set
  (a submersion) and which is *one-sided* at the boundary (`Φ ≤ 0` holds in a neighbourhood of the
  points of `∂A ∩ {Φ = 0}`) cuts out a compact `T2` smooth manifold with boundary `{Φ ≤ 0}`, with the
  inclusion smooth and the submersivity of maps transported along it.  This is the honest stand-in for
  the differential-topology input the workspace lacks (the analogue, for *regions*, of
  `Work.PTGeometric.LocalLevelPreimageTheorem` for *level sets*).

* `Work.PTGeometric.RegionSourceData k ι Fam` — the geometric residual, stated **without any manifold
  structure**: an annulus `A` (already a compact `T2` smooth manifold with boundary, so nothing has to
  be built), a smooth `Φ : A → ℝ` with the regularity and one-sidedness hypotheses of the
  region-charting theorem, the ambient fields `(P, v)` of the null-homotopy (continuous, `P` a rank-`k`
  projection, `P v = v`), a collar on which `(P, v)` are `C^∞`, the collapse end `S` identified with the
  pieces, and the prescribed boundary charts at the boundary zeros of `v` — *all of them as data on the
  annulus*, with the region entered only through the hypotheses on `Φ`.

* `Work.PTGeometric.continuousAmbientData_of_region` — the assembly: the region-charting theorem turns
  the region data into `Work.PTGeometric.ContinuousAmbientData`, whose chain to
  `ConcreteLastMileSource` (`ambientCollapseEnd_of_continuous'`, `exists_nullBordismFamily_of_...`) is
  already proved in this directory.

## Main definitions

* `Work.PTGeometric.RegionManifoldTheorem`
* `Work.PTGeometric.RegionSourceData`

## Main results

* `Work.PTGeometric.continuousAmbientData_of_region`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism
open Work.ThomBordism.PontryaginThom

/-- **The region-charting theorem.**

Let `A` be a compact `T2` smooth `(9+k)`-manifold with boundary (modelled on the half-space) and let
`Φ : A → ℝ` be `C^∞`.  Suppose

* `Φ` is a submersion at every point of its zero set (`hΦ_sub`);
* at every *boundary* point of `A` on which `Φ` vanishes, there is a chart `e` of the maximal atlas
  around the point whose zeroth coordinate cuts out `∂A` and with respect to which the differential of
  `Φ` is a **strictly negative multiple of the differential of that coordinate** (`hΦ_one`;
  equivalently: `{Φ = 0}` is *tangent* to `∂A` there and the region lies on the interior side).  This is the
  condition that rules out a corner where `∂A` meets `{Φ = 0}`, and it is exactly what the cusp
  defining function `Φ = g - δη(t)` of the source construction satisfies: at the pieces `∇g = 0` and
  `∇Φ = -δη'(1)∇t`, a negative multiple of the normalised `t`-coordinate's differential.
  (Two weaker/other formulations were tried and refuted by delegates, see README §18.4: "`{Φ ≤ 0}`
  contains a neighbourhood of the point" is *false* for the cusp, and "`{Φ < 0}` lies in the interior"
  alone allows the region to degenerate to `∂A`.)

Then `M := {x | Φ x ≤ 0}` is a compact `T2` smooth `(9+k)`-manifold with boundary, together with a
homeomorphism `e : M ≃ₜ ↥{x | Φ x ≤ 0}`, such that

* (`bdry`) `m ∈ ∂M` exactly when `(e m) ∈ ∂A` or `Φ (e m) = 0`;
* (`sm`) the inclusion `m ↦ (e m)` is `C^∞` (post-composition of a `C^∞` map on `A`);
* (`smOn`) the same for `ContMDiffOn` on a set `W ⊆ A` (the composite is `C^∞` on `e ⁻¹' W`);
* (`sub`) a map on `A` that is submersive at `e m` has submersive post-composition with `e` at `m`,
  **provided `e m` is an interior point of `A`** (equivalently `m` is an interior point of `M`, since
  `bdry` identifies the boundary).  The interior restriction is not cosmetic: Mathlib's
  `IsSubmersionAt` is the *local normal form* notion, so at a boundary point a submersion's fibre
  through the point must be *its* boundary locally, and the region's boundary and `∂A` need not agree
  (they are only tangent at the pieces — see
  `Submission/Work/PTGeometric/submersionAt_boundary_fibre.lean`, where the mechanism is proved and
  the failure exhibited).  This is why the *boundary* case is a separate hypothesis of the assembly
  and why `subBdry` below is stated on the boundary manifolds alone;
* (`subBdry`) the same for the *boundary* manifolds, at a boundary point whose image lies on `∂A`.

This is the honest stand-in for the differential-topology input the workspace lacks (the analogue, for
*regions*, of `Work.PTGeometric.LocalLevelPreimageTheorem` for *level sets*). -/
def RegionManifoldTheorem (k : ℕ) : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) A]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ A] [CompactSpace A] [T2Space A] (Φ : A → ℝ),
    ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ →
    (∀ x : A, Φ x = 0 → IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ x) →
    (∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary A, Φ x = 0 →
      ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace ((8 + k) + 1))) (c : ℝ),
        e ∈ IsManifold.maximalAtlas (𝓡∂ ((8 + k) + 1)) ∞ A ∧ x ∈ e.source ∧ c < 0 ∧
        (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ ((8 + k) + 1)).boundary A) ∧
        mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) Φ x
          = c • mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) (fun y : A => (e y).1 0) x) →
    ∃ (M : Type) (_ : TopologicalSpace M)
      (_ : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M)
      (_ : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M) (_ : CompactSpace M) (_ : T2Space M)
      (e : M ≃ₜ ↥{x : A | Φ x ≤ 0}),
      (∀ m : M, m ∈ (𝓡∂ ((8 + k) + 1)).boundary M ↔
        ((e m : A) ∈ (𝓡∂ ((8 + k) + 1)).boundary A ∨ Φ (e m) = 0)) ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : A → F),
        ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f →
        ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ (fun m : M => f (e m))) ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : A → F) (W : Set A),
        ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f W →
        ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ (fun m : M => f (e m))
          {m : M | (e m : A) ∈ W}) ∧
      (∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : A → F) (m : M),
        m ∉ (𝓡∂ ((8 + k) + 1)).boundary M →
        IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f (e m) →
        IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ (fun y : M => f (e y)) m) ∧
      (∀ (f : A → EuclideanSpace ℝ (Fin k)) (m : M)
        (hm : m ∈ (𝓡∂ ((8 + k) + 1)).boundary M)
        (he : (e m : A) ∈ (𝓡∂ ((8 + k) + 1)).boundary A),
        IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
          (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary A) => f y) ⟨e m, he⟩ →
        IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
          (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => f (e y)) ⟨m, hm⟩)

/-- **The geometric residual of the source construction, in region form.**

Everything is data on a compact `T2` smooth `(9+k)`-manifold with boundary `A` (the annulus, whose
existence is already proved: `Work.PTGeometric.nonempty_halfBallSource`), and the *source* is the
region `{Φ ≤ 0}`:

* `Φ`, smooth, a submersion on its zero set and *tangent to the boundary with the correct sign* at the
  boundary zeros (the `hΦ_one` of `RegionManifoldTheorem`; see the docstring there) — so that
  `RegionManifoldTheorem` applies and produces the source manifold;
* `P` and `v`, the ambient coordinates of the null-homotopy (continuous on `A`, `P` a rank-`k`
  orthogonal projection, `P v = v`);
* a closed collar `Sh ⊆ A` containing the boundary of the region in its interior, on which (an open
  neighbourhood `V` of) `(P, v)` is `C^∞`;
* the collapse end `S ⊆ ∂A` — with `v = 0` on `∂A ∩ {Φ ≤ 0}` exactly along `S`, and `v ≠ 0` on the
  rest of the boundary of the region — identified with the pieces;
* finitely many prescribed boundary charts at the boundary zeros, on which `v` is transverse to the
  zero section (this is TUBULAR's tube data at the pieces).

Nothing in this structure mentions the manifold structure of `{Φ ≤ 0}`: it is produced by
`Work.PTGeometric.RegionManifoldTheorem`. -/
structure RegionSourceData (n k : ℕ) (ι : Type) [Fintype ι] (Fam : ι → Man8) where
  /-- the ambient manifold (the annulus) -/
  A : Type
  [topologicalSpace : TopologicalSpace A]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) A]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ A]
  [compactSpace : CompactSpace A]
  [t2Space : T2Space A]
  /-- the defining function of the region -/
  Φ : A → ℝ
  hΦ : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ
  hΦ_sub : ∀ x : A, Φ x = 0 → IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ Φ x
  hΦ_one : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary A, Φ x = 0 →
    ∃ (e : OpenPartialHomeomorph A (EuclideanHalfSpace ((8 + k) + 1))) (c : ℝ),
      e ∈ IsManifold.maximalAtlas (𝓡∂ ((8 + k) + 1)) ∞ A ∧ x ∈ e.source ∧ c < 0 ∧
      (∀ y ∈ e.source, (e y).1 0 = 0 ↔ y ∈ (𝓡∂ ((8 + k) + 1)).boundary A) ∧
      mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) Φ x
        = c • mfderiv (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) (fun y : A => (e y).1 0) x
  hΦ_ne : ∃ x : A, Φ x ≤ 0
  /-- the matrix part of the ambient coordinates -/
  P : A → EndOp n
  hP : Continuous P
  isProj : ∀ x, P x ∈ Gr n k
  /-- the vector part -/
  v : A → Amb n
  hv : Continuous v
  mem : ∀ x, P x (v x) = v x
  /-- the collar of the boundary of the region on which the data are already smooth -/
  Sh : Set A
  isClosed_Sh : IsClosed Sh
  hSh : ∀ x : A, Φ x ≤ 0 → (x ∈ (𝓡∂ ((8 + k) + 1)).boundary A ∨ Φ x = 0) →
    x ∈ interior Sh
  V : Set A
  isOpen_V : IsOpen V
  Sh_subset_V : Sh ⊆ V
  hPsmV : ContMDiffOn (𝓡∂ ((8 + k) + 1))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞ P V
  hvsmV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v V
  /-- the collapse end (the part of `∂A` carrying the pieces) -/
  S : Set A
  isClosed_S : IsClosed S
  S_subset_bdry : S ⊆ (𝓡∂ ((8 + k) + 1)).boundary A
  S_subset_region : S ⊆ {x : A | Φ x ≤ 0}
  /-- on the region's boundary inside `∂A`, the zero set of `v` is exactly the collapse end -/
  hZero_bdry : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary A, Φ x ≤ 0 → (v x = 0 ↔ x ∈ S)
  /-- the zero set of `v` meets `{Φ = 0}` only inside `∂A` -/
  hZero_Phi : ∀ x : A, Φ x = 0 → v x = 0 → x ∈ (𝓡∂ ((8 + k) + 1)).boundary A
  endHomeo : ↥(S ∩ {x : A | v x = 0}) ≃ₜ (Σ i : ι, (Fam i).pt)
  avoid : ∀ x : A,
    ((x ∈ (𝓡∂ ((8 + k) + 1)).boundary A ∧ Φ x ≤ 0) ∨ Φ x = 0) → x ∉ S → v x ≠ 0
  /-- the prescribed boundary charts at the boundary zeros -/
  mE : ℕ
  ellE : Fin mE → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin k)
  UE : Fin mE → Set A
  isOpen_UE : ∀ j, IsOpen (UE j)
  UE_subset_Sh : ∀ j, UE j ⊆ Sh
  ellE_inj : ∀ j y, y ∈ UE j → ∀ z : EuclideanSpace ℝ (Fin n),
    P y z = z → ellE j z = 0 → z = 0
  ellE_inj_cl : ∀ j, closure (UE j) ⊆
    {y : A | ∀ z : EuclideanSpace ℝ (Fin n), P y z = z → ellE j z = 0 → z = 0}
  bndZero_cov : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary A, Φ x ≤ 0 → v x = 0 → ∃ j, x ∈ UE j
  bndZero_trans : ∀ j, ∀ x ∈ UE j, ∀ (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary A),
    Φ x ≤ 0 → v x = 0 →
    IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y => ellE j (v y)) x ∧
    IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
      (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary A) => ellE j (v y)) ⟨x, hx⟩

attribute [instance] RegionSourceData.topologicalSpace RegionSourceData.chartedSpace
  RegionSourceData.isManifold RegionSourceData.compactSpace RegionSourceData.t2Space
theorem continuousAmbientData_of_region {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (h : RegionManifoldTheorem k) (D : RegionSourceData n k ι Fam)
    (hbd : ∀ (M' : Type) [TopologicalSpace M']
      [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M']
      [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M'] (e' : M' ≃ₜ ↥{x : D.A | D.Φ x ≤ 0})
      (m' : M') (hm' : m' ∈ (𝓡∂ ((8 + k) + 1)).boundary M')
      (he' : (e' m' : D.A) ∈ (𝓡∂ ((8 + k) + 1)).boundary D.A)
      (f : D.A → EuclideanSpace ℝ (Fin k)),
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞ f (e' m') →
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞
        (fun y : M' => f (e' y)) m') :
    Nonempty (ContinuousAmbientData n k ι Fam) := by
  classical
  obtain ⟨M, tM, cM, iM, compM, t2M, e, hbdry, hsm, hsmOn, hsub, hsubB⟩ :=
    h D.A D.Φ D.hΦ D.hΦ_sub D.hΦ_one
  letI := tM
  letI := cM
  letI := iM
  letI := compM
  letI := t2M
  have hec : Continuous fun m : M => (e m : D.A) := continuous_subtype_val.comp e.continuous
  have hreg : ∀ m : M, D.Φ (e m) ≤ 0 := fun m => (e m).2
  have hSh1 : {m : M | (e m : D.A) ∈ interior D.Sh} ⊆
      interior {m : M | (e m : D.A) ∈ D.Sh} := by
    intro m hm
    obtain ⟨t, ht_sub, ht_open, ht_mem⟩ := mem_interior.mp hm
    exact mem_interior.mpr ⟨{y : M | (e y : D.A) ∈ t}, fun y hy => ht_sub hy,
      ht_open.preimage hec, ht_mem⟩
  have hbdry_Sh : (𝓡∂ ((8 + k) + 1)).boundary M ⊆ interior {m : M | (e m : D.A) ∈ D.Sh} := by
    intro m hm
    exact hSh1 (D.hSh (e m) (hreg m) ((hbdry m).mp hm))
  haveI hne : Nonempty M := by
    obtain ⟨x, hx⟩ := D.hΦ_ne
    exact ⟨e.symm ⟨x, hx⟩⟩
  have hEnd : Nonempty ((↥({m : M | (e m : D.A) ∈ D.S} ∩ {m : M | D.v (e m) = 0})) ≃ₜ
      (Σ i : ι, (Fam i).pt)) := by
    have hset : ({m : M | (e m : D.A) ∈ D.S} ∩ {m : M | D.v (e m) = 0})
        = {m : M | (e m : D.A) ∈ (D.S ∩ {x : D.A | D.v x = 0})} := by
      ext m
      exact ⟨fun hx => ⟨hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2⟩⟩
    rw [hset]
    have hc1 : Continuous (fun x : ↥{m : M | (e m : D.A) ∈ (D.S ∩ {x : D.A | D.v x = 0})} =>
        (⟨(e x : D.A), x.2⟩ : ↥(D.S ∩ {x : D.A | D.v x = 0}))) :=
      Continuous.subtype_mk (hec.comp continuous_subtype_val) _
    have hc2 : Continuous (fun y : ↥(D.S ∩ {x : D.A | D.v x = 0}) =>
        (⟨e.symm (⟨y.1, D.S_subset_region y.2.1⟩ : ↥{x : D.A | D.Φ x ≤ 0}),
          show (e (e.symm (⟨y.1, D.S_subset_region y.2.1⟩ : ↥{x : D.A | D.Φ x ≤ 0})) : D.A)
            ∈ (D.S ∩ {x : D.A | D.v x = 0}) by
            rw [e.apply_symm_apply]
            exact y.2⟩ :
          ↥{m : M | (e m : D.A) ∈ (D.S ∩ {x : D.A | D.v x = 0})})) :=
      Continuous.subtype_mk ((e.symm.continuous).comp
        (Continuous.subtype_mk continuous_subtype_val _)) _
    refine ⟨Homeomorph.trans (Homeomorph.mk ?_ ?_ ?_) D.endHomeo⟩
    · refine ⟨fun x => ⟨(e x : D.A), x.2⟩, fun y =>
        ⟨e.symm (⟨y.1, D.S_subset_region y.2.1⟩ : ↥{x : D.A | D.Φ x ≤ 0}),
          show (e (e.symm (⟨y.1, D.S_subset_region y.2.1⟩ : ↥{x : D.A | D.Φ x ≤ 0})) : D.A)
            ∈ (D.S ∩ {x : D.A | D.v x = 0}) by
            rw [e.apply_symm_apply]
            exact y.2⟩, ?_, ?_⟩
      · intro x
        apply Subtype.ext
        have h3 : (⟨(e x : D.A), D.S_subset_region x.2.1⟩ : ↥{x : D.A | D.Φ x ≤ 0}) = e x :=
          Subtype.ext rfl
        show e.symm (⟨(e x : D.A), D.S_subset_region x.2.1⟩ : ↥{x : D.A | D.Φ x ≤ 0}) = (x : M)
        rw [h3, e.symm_apply_apply]
      · intro y
        apply Subtype.ext
        show (e (e.symm (⟨y.1, D.S_subset_region y.2.1⟩ : ↥{x : D.A | D.Φ x ≤ 0})) : D.A) = (y : D.A)
        rw [e.apply_symm_apply]
    · exact hc1
    · exact hc2
  refine ⟨(⟨M, (fun m => D.P (e m)), D.hP.comp hec, (fun m => D.isProj (e m)),
      (fun m => D.v (e m)), D.hv.comp hec, (fun m => D.mem (e m)),
      {m : M | (e m : D.A) ∈ D.Sh}, D.isClosed_Sh.preimage hec, hbdry_Sh,
      {m : M | (e m : D.A) ∈ D.V}, D.isOpen_V.preimage hec, (fun m hm => D.Sh_subset_V hm),
      hsmOn _ D.P D.V D.hPsmV, hsmOn _ D.v D.V D.hvsmV,
      {m : M | (e m : D.A) ∈ D.S}, D.isClosed_S.preimage hec,
      (fun m hm => (hbdry m).mpr (Or.inl (D.S_subset_bdry hm))),
      hEnd.some, ?avoid, D.mE, D.ellE, (fun j => {m : M | (e m : D.A) ∈ D.UE j}),
      (fun j => (D.isOpen_UE j).preimage hec), ?UE_subset_Sh,
      ?ellE_inj, ?ellE_inj_cl, ?bndZero_cov, ?bndZero_trans⟩ :
    ContinuousAmbientData n k ι Fam)⟩
  case avoid =>
    intro m hm hmS hmv
    exact D.avoid (e m) (Or.elim ((hbdry m).mp hm) (fun hh => Or.inl ⟨hh, hreg m⟩) Or.inr)
      (fun hh => hmS hh) hmv
  case UE_subset_Sh =>
    intro j m hm
    exact D.UE_subset_Sh j hm
  case ellE_inj =>
    intro j y hy z hz h0
    exact D.ellE_inj j (e y) hy z hz h0
  case ellE_inj_cl =>
    intro j m hm z hz h0
    have h1 : (e m : D.A) ∈ closure (D.UE j) := by
      let S : Set ↥{x : D.A | D.Φ x ≤ 0} := Subtype.val ⁻¹' D.UE j
      have h2 : (e m : ↥{x : D.A | D.Φ x ≤ 0}) ∈ closure S :=
        closure_mono (Set.image_preimage_subset (⇑e) S)
          (image_closure_subset_closure_image e.continuous (s := ⇑e ⁻¹' S) ⟨m, hm, rfl⟩)
      have h4 : Subtype.val '' S ⊆ D.UE j :=
        fun y hy => by obtain ⟨x, hx, hxy⟩ := hy; rw [← hxy]; exact hx
      rw [IsEmbedding.closure_eq_preimage_closure_image
        (IsEmbedding.subtypeVal (X := D.A) (p := fun x : D.A => D.Φ x ≤ 0)) S] at h2
      exact closure_mono h4 h2
    exact D.ellE_inj_cl j h1 z hz h0
  case bndZero_cov =>
    intro m hm hmv
    have hmem : (e m : D.A) ∈ (𝓡∂ ((8 + k) + 1)).boundary D.A := by
      rcases (hbdry m).mp hm with hh | hh
      · exact hh
      · exact D.hZero_Phi (e m) hh hmv
    obtain ⟨j, hj⟩ := D.bndZero_cov (e m) hmem (hreg m) hmv
    exact ⟨j, hj⟩
  case bndZero_trans =>
    intro j m hmUE hmB hmv
    have hmem : (e m : D.A) ∈ (𝓡∂ ((8 + k) + 1)).boundary D.A := by
      rcases (hbdry m).mp hmB with hh | hh
      · exact hh
      · exact D.hZero_Phi (e m) hh hmv
    obtain ⟨h1, h2⟩ := D.bndZero_trans j (e m) hmUE hmem (hreg m) hmv
    refine ⟨hbd M e m hmB hmem (fun y => D.ellE j (D.v y)) h1, ?_⟩
    have h2' : IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
        (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary D.A) => D.ellE j (D.v ↑y))
        (⟨(e m : D.A), hmem⟩ : ↥((𝓡∂ ((8 + k) + 1)).boundary D.A)) := h2
    exact hsubB (fun y => D.ellE j (D.v y)) m hmB hmem h2'


/-- **The ambient collapse end produced by the region data** (a chosen witness, so that a caller can
*name* it, e.g. to state the orientation datum of the situation). -/
noncomputable def ambientCollapseEnd_of_region {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}
    (hreg : RegionManifoldTheorem k) (hk : k ≤ n) (R : RegionSourceData n k ι Fam)
    (hbd : ∀ (M' : Type) [TopologicalSpace M']
      [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M']
      [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M'] (e' : M' ≃ₜ ↥{x : R.A | R.Φ x ≤ 0})
      (m' : M') (hm' : m' ∈ (𝓡∂ ((8 + k) + 1)).boundary M')
      (he' : (e' m' : R.A) ∈ (𝓡∂ ((8 + k) + 1)).boundary R.A)
      (f : R.A → EuclideanSpace ℝ (Fin k)),
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞ f (e' m') →
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞
        (fun y : M' => f (e' y)) m') :
    AmbientCollapseEnd n k ι Fam :=
  Classical.choice ((continuousAmbientData_of_region hreg R hbd).elim
    (fun D => ⟨ambientCollapseEnd_of_continuous' hk D⟩))

/-- **The source construction in region form**: for every family, every genuine collapse datum of it
and every `m > 0` with the `m`-th power of the product of the pieces' genuine classes trivial, a
positive multiple of the family carries *region data* (`RegionSourceData`, i.e. a smooth defining
function and the ambient fields on the annulus, without any manifold structure) whose associated
ambient collapse end carries the orientation datum of the situation
(`Work.PTGeometric.AmbientOrientationDataFree`).

This is `ConcreteLastMileSource` with `AmbientCollapseEnd` replaced by the region data: the
manifold-with-boundary structure of the source is *produced* by `RegionManifoldTheorem` rather than
being asked for. -/
def RegionRealisationSource (k : ℕ) (D : ThomTarget k) (hreg : RegionManifoldTheorem k) : Prop :=
  letI : Nonempty (Fin (k + 8)) := ⟨⟨0, by omega⟩⟩
  letI : Nontrivial (Fin (k + 8)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  letI : CommMonoid (Quotient (GenLoop.Homotopic.setoid (Fin (k + 8)) D.t₀)) :=
    inferInstanceAs (CommMonoid (HomotopyGroup (Fin (k + 8)) D.T D.t₀))
  ∀ (ι : Type) [Fintype ι] (Fam : ι → Man8) (G : GenuineTubeGeometry k D ι Fam) (m : ℕ),
    0 < m → (∏ i, tubeAlpha (G.rep i)) ^ m = 1 →
      ∃ N' : ℕ, 0 < N' ∧
        ∃ R : RegionSourceData (k + G.mU) k (Fin N' × ι) (fun x => Fam x.2),
          ∃ (hbd : ∀ (M' : Type) [TopologicalSpace M']
            [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M']
            [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M'] (e' : M' ≃ₜ ↥{x : R.A | R.Φ x ≤ 0})
            (m' : M') (hm' : m' ∈ (𝓡∂ ((8 + k) + 1)).boundary M')
            (he' : (e' m' : R.A) ∈ (𝓡∂ ((8 + k) + 1)).boundary R.A)
            (f : R.A → EuclideanSpace ℝ (Fin k)),
            IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞ f (e' m') →
            IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin k))) ∞
              (fun y : M' => f (e' y)) m'),
            AmbientOrientationDataFree (ambientCollapseEnd_of_region hreg (Nat.le_add_right k G.mU) R hbd)

/-- **The source construction reduces to the region form**: the region data plus the region-charting
theorem produce the ambient collapse end (`continuousAmbientData_of_region` and
`ambientCollapseEnd_of_continuous'`), so `ConcreteLastMileSource` follows from
`RegionRealisationSource`. -/
theorem concreteLastMileSource_of_region {k : ℕ} {D : ThomTarget k}
    (hreg : RegionManifoldTheorem k) (h : RegionRealisationSource k D hreg) :
    ConcreteLastMileSource k D := by
  intro ι _ Fam G m hm hpow
  obtain ⟨N', hN', R, hbd, hOr⟩ := h ι Fam G m hm hpow
  exact ⟨N', hN', ambientCollapseEnd_of_region hreg (Nat.le_add_right k G.mU) R hbd, hOr⟩

end

end Work.PTGeometric
