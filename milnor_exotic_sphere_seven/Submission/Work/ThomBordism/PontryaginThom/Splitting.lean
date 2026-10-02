import Submission.Work.ThomBordism.PontryaginThom.ComplementBundle
import Submission.Work.ThomBordism.PontryaginThom.BundleIsoLocal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The splitting `TV ⊕ ν ≅ ε^{k+8}` from the complement data

`ComplementBundle.lean` builds the complement bundle `ν` from a family of projections/insertions of
the complement of a plane (`ComplementData`), and `BundleIsoLocal.lean` converts a fibrewise linear
isomorphism with continuous chart expressions into a `Work.Thom.BundleIso`.

This file assembles the two into the **splitting of the trivial bundle along an immersion**:
`TV ⊕ ν ≅ ε^{k+8}`, i.e. the fact that `ν` is a complement of the tangent bundle.  The fibrewise
isomorphism is `(v, w) ↦ A v + I w`, with inverse `z ↦ (Ainv z, P z)`.

The data is the bundle `Zt` of rank `8` (the tangent bundle), the complement data `D` of rank `k`,
the **frames** `A i x` of the plane in the chart `i` (`ιT`-indexed, like the charts), and the
**frame-coordinate extraction** `Ainv i x` (the coordinates, in the frame `A i x`, of the component
of a vector in the plane).  The hypotheses are exactly the linear algebra of the splitting:

* `ker_eq_range` — the kernel of the projection `P j x` is the plane spanned by the frame (`A i x`),
  i.e. `Complement.ker_planeProj`;
* `Ainv_left`, `Ainv_proj` — `Ainv i x` is a left inverse of `coeffMap (A i x)` and
  `coeffMap (A i x) ∘ Ainv i x` is the projection onto the plane along `ν`;
* `Pi_agree` — the complement projection `I j x ∘ P j x` does not depend on the chart `j`
  (geometrically: the *same* complement of the plane is used in every chart);
* `A_compat` — the frames of different charts express the same tangent vectors (the chain rule,
  `A i = A (indexAt x) ∘ transition`);
* `Ainv_compat` — likewise for `Ainv`;
* `contOn_A`, `contOn_Ainv` — continuity of the frames.

Everything is proved here; producing the data from an immersion is the geometric input.
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type*} [TopologicalSpace B] {k : ℕ} {ι ιT : Type*}

/-! ## The frame coordinate map, as a continuous linear map -/

/-- `Work.ThomBordism.Grassmann.coeffMap` of a frame, as a continuous linear map. -/
def coeffMapCLM (f : Fin 8 → Euc (8 + k)) : (Fin 8 → ℝ) →L[ℝ] (Fin (8 + k) → ℝ) :=
  LinearMap.toContinuousLinearMap (coeffMap f)

@[simp] theorem coeffMapCLM_apply (f : Fin 8 → Euc (8 + k)) (v : Fin 8 → ℝ) :
    coeffMapCLM f v = coeffMap f v := rfl

/-- The value of `coeffMap` on the `j`-th basis vector is the `j`-th column of the frame. -/
theorem coeffMap_single (f : Fin 8 → Euc (8 + k)) (j : Fin 8) :
    coeffMap f (Pi.single j 1) = fun r => EuclideanSpace.proj (𝕜 := ℝ) r (f j) := by
  funext r
  rw [coeffMap_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem continuousOn_coeffMapCLM {X : Type*} [TopologicalSpace X] {s : Set X}
    (F : X → Fin 8 → Euc (8 + k)) (hF : ContinuousOn F s) :
    ContinuousOn (fun x => coeffMapCLM (F x)) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : s => LinearMap.toContinuousLinearMap (coeffMap (F p.1)))
  rw [continuous_toContinuousLinearMap_iff]
  intro j
  have hcol : (fun p : s => coeffMap (F p.1) (Pi.single j 1))
      = fun p : s => fun r => EuclideanSpace.proj (𝕜 := ℝ) r (F p.1 j) := by
    funext p; exact coeffMap_single (F p.1) j
  rw [hcol, continuous_pi_iff]
  intro r
  exact (EuclideanSpace.proj (𝕜 := ℝ) r).continuous.comp
    ((continuous_apply j).comp hF.domRestrict)

/-! ## The canonical identification of `ℝⁿ` with `Fin n → ℝ` -/

/-- The canonical continuous linear map `ℝⁿ → (Fin n → ℝ)`. -/
def eucToFun (n : ℕ) : Euc n →L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ

/-- Its inverse. -/
def funToEuc (n : ℕ) : (Fin n → ℝ) →L[ℝ] Euc n := (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp] theorem eucToFun_apply (n : ℕ) (x : Euc n) : eucToFun n x = WithLp.ofLp x := rfl

@[simp] theorem funToEuc_apply (n : ℕ) (y : Fin n → ℝ) : funToEuc n y = WithLp.toLp 2 y := rfl

@[simp] theorem eucToFun_funToEuc (n : ℕ) (y : Fin n → ℝ) : eucToFun n (funToEuc n y) = y :=
  ContinuousLinearEquiv.apply_symm_apply (EuclideanSpace.equiv (Fin n) ℝ) y

@[simp] theorem funToEuc_eucToFun (n : ℕ) (x : Euc n) : funToEuc n (eucToFun n x) = x :=
  ContinuousLinearEquiv.symm_apply_apply (EuclideanSpace.equiv (Fin n) ℝ) x

/-! ## The transition of `Zt` in plain coordinates -/

/-- The transition function of `Zt`, in the plain coordinate space `Fin 8 → ℝ`: it maps the plain
coordinates of the chart `i` to those of the preferred chart at `x`. -/
def tCoord (Zt : RealBundle B (Euc 8) ιT) (i : ιT) (x : B) :
    (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  (eucToFun 8).comp ((Zt.coordChange i (Zt.indexAt x) x).comp (funToEuc 8))

/-- The inverse transition, from the plain coordinates of the preferred chart at `x` to those of the
chart `i`. -/
def tCoordInv (Zt : RealBundle B (Euc 8) ιT) (i : ιT) (x : B) :
    (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  (eucToFun 8).comp ((Zt.coordChange (Zt.indexAt x) i x).comp (funToEuc 8))

theorem tCoord_apply (Zt : RealBundle B (Euc 8) ιT) (i : ιT) (x : B) (v : Fin 8 → ℝ) :
    tCoord Zt i x v
      = eucToFun 8 (Zt.coordChange i (Zt.indexAt x) x (funToEuc 8 v)) := rfl

theorem tCoordInv_apply (Zt : RealBundle B (Euc 8) ιT) (i : ιT) (x : B) (v : Fin 8 → ℝ) :
    tCoordInv Zt i x v
      = eucToFun 8 (Zt.coordChange (Zt.indexAt x) i x (funToEuc 8 v)) := rfl

theorem tCoordInv_comp_tCoord (Zt : RealBundle B (Euc 8) ιT) (i : ιT) (x : B)
    (hx : x ∈ Zt.baseSet i) :
    (tCoordInv Zt i x).comp (tCoord Zt i x) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  show eucToFun 8 (Zt.coordChange (Zt.indexAt x) i x
      (funToEuc 8 (eucToFun 8 (Zt.coordChange i (Zt.indexAt x) x (funToEuc 8 v))))) = v
  rw [funToEuc_eucToFun,
    Zt.coordChange_comp i (Zt.indexAt x) i x ⟨⟨hx, Zt.mem_baseSet_at x⟩, hx⟩,
    Zt.coordChange_self i x hx, eucToFun_funToEuc]

/-! ## The fibrewise linear maps of the splitting -/

/-- The forward fibrewise map `(v, w) ↦ coeffMap (A i x) v + I j x w`, in the plain coordinates of
the ambient space. -/
def splitFwdP (D : ComplementData B k ι) (A : ιT → B → Fin 8 → Euc (8 + k))
    (i : ιT) (j : ι) (x : B) : Euc 8 × (Fin k → ℝ) →L[ℝ] (Fin (8 + k) → ℝ) :=
  (coeffMapCLM (A i x)).comp ((eucToFun 8).comp (ContinuousLinearMap.fst ℝ (Euc 8) (Fin k → ℝ)))
    + (D.I j x).comp (ContinuousLinearMap.snd ℝ (Euc 8) (Fin k → ℝ))

/-- The forward fibrewise map of the splitting, into the ambient euclidean space. -/
def splitFwd (D : ComplementData B k ι) (A : ιT → B → Fin 8 → Euc (8 + k))
    (i : ιT) (j : ι) (x : B) : Euc 8 × (Fin k → ℝ) →L[ℝ] Euc (8 + k) :=
  (funToEuc (8 + k)).comp (splitFwdP D A i j x)

theorem splitFwdP_apply (D : ComplementData B k ι) (A : ιT → B → Fin 8 → Euc (8 + k))
    (i : ιT) (j : ι) (x : B) (v : Euc 8) (w : Fin k → ℝ) :
    splitFwdP D A i j x (v, w) = coeffMap (A i x) (eucToFun 8 v) + D.I j x w := by
  simp [splitFwdP]

theorem splitFwd_apply (D : ComplementData B k ι) (A : ιT → B → Fin 8 → Euc (8 + k))
    (i : ιT) (j : ι) (x : B) (v : Euc 8) (w : Fin k → ℝ) :
    splitFwd D A i j x (v, w)
      = funToEuc (8 + k) (coeffMap (A i x) (eucToFun 8 v) + D.I j x w) := by
  simp [splitFwd, splitFwdP_apply]

/-- The backward fibrewise map `z ↦ (Ainv i x z, P j x z)` of the splitting. -/
def splitBwd (D : ComplementData B k ι) (Ainv : ιT → B → (Fin (8 + k) → ℝ) →L[ℝ] (Fin 8 → ℝ))
    (i : ιT) (j : ι) (x : B) : Euc (8 + k) →L[ℝ] Euc 8 × (Fin k → ℝ) :=
  ((funToEuc 8).comp ((Ainv i x).comp (eucToFun (8 + k)))).prod
    ((D.P j x).comp (eucToFun (8 + k)))

theorem splitBwd_apply (D : ComplementData B k ι)
    (Ainv : ιT → B → (Fin (8 + k) → ℝ) →L[ℝ] (Fin 8 → ℝ))
    (i : ιT) (j : ι) (x : B) (z : Euc (8 + k)) :
    splitBwd D Ainv i j x z
      = (funToEuc 8 (Ainv i x (eucToFun (8 + k) z)), D.P j x (eucToFun (8 + k) z)) := by
  simp [splitBwd]

theorem continuousOn_splitFwdP (Zt : RealBundle B (Euc 8) ιT) (D : ComplementData B k ι)
    (A : ιT → B → Fin 8 → Euc (8 + k))
    (contOn_A : ∀ i, ContinuousOn (fun x => A i x) (Zt.baseSet i)) (i : ιT) (j : ι) :
    ContinuousOn (fun x => splitFwdP D A i j x) (Zt.baseSet i ∩ D.baseSet j) := by
  have h1 : ContinuousOn (fun x => coeffMapCLM (A i x)) (Zt.baseSet i ∩ D.baseSet j) :=
    (continuousOn_coeffMapCLM (A i) (contOn_A i)).mono Set.inter_subset_left
  have h2 : ContinuousOn (fun x => D.I j x) (Zt.baseSet i ∩ D.baseSet j) :=
    (D.continuousOn_I j).mono Set.inter_subset_right
  have h3 : ContinuousOn (fun x => (eucToFun 8).comp (ContinuousLinearMap.fst ℝ (Euc 8)
      (Fin k → ℝ))) (Zt.baseSet i ∩ D.baseSet j) := continuousOn_const
  have h4 : ContinuousOn (fun x => ContinuousLinearMap.snd ℝ (Euc 8) (Fin k → ℝ))
      (Zt.baseSet i ∩ D.baseSet j) := continuousOn_const
  have hmain : ContinuousOn (fun x =>
      (coeffMapCLM (A i x)).comp ((eucToFun 8).comp (ContinuousLinearMap.fst ℝ (Euc 8)
        (Fin k → ℝ))) + (D.I j x).comp (ContinuousLinearMap.snd ℝ (Euc 8) (Fin k → ℝ)))
      (Zt.baseSet i ∩ D.baseSet j) := (h1.clm_comp h3).add (h2.clm_comp h4)
  refine hmain.congr (fun x hx => ?_)
  rfl

theorem continuousOn_splitBwd (Zt : RealBundle B (Euc 8) ιT) (D : ComplementData B k ι)
    (Ainv : ιT → B → (Fin (8 + k) → ℝ) →L[ℝ] (Fin 8 → ℝ))
    (contOn_Ainv : ∀ i, ContinuousOn (fun x => Ainv i x) (Zt.baseSet i)) (i : ιT) (j : ι) :
    ContinuousOn (fun x => splitBwd D Ainv i j x) (Zt.baseSet i ∩ D.baseSet j) := by
  have h1 : ContinuousOn (fun x => Ainv i x) (Zt.baseSet i ∩ D.baseSet j) :=
    (contOn_Ainv i).mono Set.inter_subset_left
  have h2 : ContinuousOn (fun x => D.P j x) (Zt.baseSet i ∩ D.baseSet j) :=
    (D.continuousOn_P j).mono Set.inter_subset_right
  have ha : ContinuousOn (fun x => (funToEuc 8).comp ((Ainv i x).comp (eucToFun (8 + k))))
      (Zt.baseSet i ∩ D.baseSet j) := continuousOn_const.clm_comp (h1.clm_comp continuousOn_const)
  have hb : ContinuousOn (fun x => (D.P j x).comp (eucToFun (8 + k)))
      (Zt.baseSet i ∩ D.baseSet j) := h2.clm_comp continuousOn_const
  have hmain : ContinuousOn (fun x =>
      ((funToEuc 8).comp ((Ainv i x).comp (eucToFun (8 + k)))).prod
        ((D.P j x).comp (eucToFun (8 + k)))) (Zt.baseSet i ∩ D.baseSet j) :=
    (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn (ha.prodMk hb)
  refine hmain.congr (fun x hx => ?_)
  rfl

/-! ## The splitting -/

/-- **The splitting `TV ⊕ ν ≅ ε^{k+8}`.**  From the complement data `D` (the normal bundle), a
rank-`8` bundle `Zt` (the tangent bundle), the frames `A i x` of the plane and the frame-coordinate
extraction `Ainv i x` (with the hypotheses listed in the module docstring), the fibrewise maps
`(v, w) ↦ A v + I w` and `z ↦ (Ainv z, P z)` are mutually inverse and have continuous chart
expressions, so they define a `Work.Thom.BundleIso`. -/
theorem nonempty_bundleIso_splitting (Zt : RealBundle B (Euc 8) ιT) (D : ComplementData B k ι)
    (A : ιT → B → Fin 8 → Euc (8 + k))
    (Ainv : ιT → B → (Fin (8 + k) → ℝ) →L[ℝ] (Fin 8 → ℝ))
    (contOn_A : ∀ i, ContinuousOn (fun x => A i x) (Zt.baseSet i))
    (contOn_Ainv : ∀ i, ContinuousOn (fun x => Ainv i x) (Zt.baseSet i))
    (ker_eq_range : ∀ (j : ι) (i : ιT) (x : B), x ∈ D.baseSet j → x ∈ Zt.baseSet i →
      LinearMap.ker ((D.P j x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ)))
        = LinearMap.range (coeffMap (A i x)))
    (Ainv_left : ∀ (i : ιT) (x : B), x ∈ Zt.baseSet i → ∀ v : Fin 8 → ℝ,
      Ainv i x (coeffMap (A i x) v) = v)
    (Ainv_proj : ∀ (i : ιT) (j : ι) (x : B), x ∈ Zt.baseSet i → x ∈ D.baseSet j →
      ∀ u : Fin (8 + k) → ℝ, coeffMap (A i x) (Ainv i x u) = u - D.I j x (D.P j x u))
    (Pi_agree : ∀ (i j : ι) (x : B), x ∈ D.baseSet i → x ∈ D.baseSet j →
      ∀ u : Fin (8 + k) → ℝ, D.I i x (D.P i x u) = D.I j x (D.P j x u))
    (A_compat : ∀ (i : ιT) (x : B), x ∈ Zt.baseSet i → ∀ v : Fin 8 → ℝ,
      coeffMap (A i x) v = coeffMap (A (Zt.indexAt x) x) (tCoord Zt i x v))
    (Ainv_compat : ∀ (i : ιT) (x : B), x ∈ Zt.baseSet i → ∀ u : Fin (8 + k) → ℝ,
      Ainv i x u = tCoordInv Zt i x (Ainv (Zt.indexAt x) x u)) :
    Nonempty (BundleIso (Zt.sum D.toRealBundle)
      (RealBundle.trivial B (Euc (8 + k)) Unit)) := by
  classical
  -- the plane is exactly the kernel of the projection
  have hplane : ∀ (j : ι) (i : ιT) (x : B), x ∈ D.baseSet j → x ∈ Zt.baseSet i →
      ∀ v : Fin 8 → ℝ, D.P j x (coeffMap (A i x) v) = 0 := by
    intro j i x hj hi v
    have hker := ker_eq_range j i x hj hi
    have hmem : coeffMap (A i x) v ∈ LinearMap.ker
        ((D.P j x : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin k → ℝ))) := by
      rw [hker]; exact LinearMap.mem_range_self _ v
    simpa using hmem
  -- the frame coordinate map is injective
  have hinj : ∀ (i : ιT) (x : B), x ∈ Zt.baseSet i →
      Function.Injective (coeffMap (A i x)) := by
    intro i x hi u v huv
    have h : Ainv i x (coeffMap (A i x) u) = Ainv i x (coeffMap (A i x) v) := by rw [huv]
    rwa [Ainv_left i x hi u, Ainv_left i x hi v] at h
  -- `Ainv` kills the normal part
  have hkill : ∀ (i : ιT) (j : ι) (x : B), x ∈ Zt.baseSet i → x ∈ D.baseSet j →
      ∀ w : Fin k → ℝ, Ainv i x (D.I j x w) = 0 := by
    intro i j x hi hj w
    apply hinj i x hi
    rw [Ainv_proj i j x hi hj (D.I j x w), map_zero]
    have h := congrFun (congrArg DFunLike.coe (D.P_comp_I j x)) w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    rw [h, sub_self]
  -- the complement projection is chart-independent
  have hnorm : ∀ (j : ι) (x : B), x ∈ D.baseSet j → ∀ u : Fin (8 + k) → ℝ,
      D.I (D.indexAt x) x (D.P (D.indexAt x) x u) = D.I j x (D.P j x u) := fun j x hj u =>
    Pi_agree (D.indexAt x) j x (D.mem_baseSet_at x) hj u
  let T : B → Euc 8 × (Fin k → ℝ) →L[ℝ] Euc (8 + k) :=
    fun x => splitFwd D A (Zt.indexAt x) (D.indexAt x) x
  let U : B → Euc (8 + k) →L[ℝ] Euc 8 × (Fin k → ℝ) :=
    fun x => splitBwd D Ainv (Zt.indexAt x) (D.indexAt x) x
  refine nonempty_bundleIso_of_clm (Zt.sum D.toRealBundle)
    (RealBundle.trivial B (Euc (8 + k)) Unit) T U ?_ ?_ ?_ ?_
  · intro i₁ i₂
    obtain ⟨i, j⟩ := i₁
    have hset : (RealBundle.sum Zt D.toRealBundle).baseSet (i, j)
        ∩ (RealBundle.trivial B (Euc (8 + k)) Unit).baseSet i₂ = Zt.baseSet i ∩ D.baseSet j := by
      rw [RealBundle.sum_baseSet, ComplementData.toRealBundle_baseSet, RealBundle.trivial_baseSet,
        Set.inter_univ]
    rw [hset]
    have hc : ContinuousOn (fun x => splitFwd D A i j x) (Zt.baseSet i ∩ D.baseSet j) :=
      continuousOn_const.clm_comp (continuousOn_splitFwdP Zt D A contOn_A i j)
    refine hc.congr (fun x hx => ?_)
    have hcc : (Zt.sum D.toRealBundle).coordChange (i, j) ((Zt.sum D.toRealBundle).indexAt x) x
        = (Zt.coordChange i (Zt.indexAt x) x).prodMap (D.coordChange j (D.indexAt x) x) := by
      rw [RealBundle.sum_coordChange, RealBundle.sum_indexAt,
        ComplementData.toRealBundle_coordChange, ComplementData.toRealBundle_indexAt]
    rw [hcc, RealBundle.trivial_coordChange, ContinuousLinearMap.id_comp,
      show D.coordChange j (D.indexAt x) x = (D.P (D.indexAt x) x).comp (D.I j x) from
        D.coordChange_of_mem j (D.indexAt x) x ⟨hx.2, D.mem_baseSet_at x⟩]
    refine ContinuousLinearMap.ext fun p => ?_
    obtain ⟨v, w⟩ := p
    rw [show T x = splitFwd D A (Zt.indexAt x) (D.indexAt x) x from rfl,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap']
    simp only [Prod.map, ContinuousLinearMap.comp_apply, splitFwd_apply]
    rw [show funToEuc (8 + k) (coeffMap (A (Zt.indexAt x) x)
          (eucToFun 8 (Zt.coordChange i (Zt.indexAt x) x v))
          + D.I (D.indexAt x) x ((D.P (D.indexAt x) x) (D.I j x w)))
        = funToEuc (8 + k) (coeffMap (A i x) (eucToFun 8 v) + D.I j x w) from by
        have hP : (D.P j x) ((D.I j x) w) = w := by
          rw [← ContinuousLinearMap.comp_apply, D.P_comp_I]
          rfl
        rw [show eucToFun 8 (Zt.coordChange i (Zt.indexAt x) x v)
              = tCoord Zt i x (eucToFun 8 v) from by rw [tCoord_apply, funToEuc_eucToFun],
          ← A_compat i x hx.1 (eucToFun 8 v),
          hnorm j x hx.2 (D.I j x w), hP]]
  · intro i₂ i₁
    obtain ⟨i, j⟩ := i₁
    have hset : (RealBundle.trivial B (Euc (8 + k)) Unit).baseSet i₂
        ∩ (RealBundle.sum Zt D.toRealBundle).baseSet (i, j) = Zt.baseSet i ∩ D.baseSet j := by
      rw [RealBundle.trivial_baseSet, Set.univ_inter, RealBundle.sum_baseSet,
        ComplementData.toRealBundle_baseSet]
    rw [hset]
    have hc : ContinuousOn (fun x => splitBwd D Ainv i j x) (Zt.baseSet i ∩ D.baseSet j) :=
      continuousOn_splitBwd Zt D Ainv contOn_Ainv i j
    refine hc.congr (fun x hx => ?_)
    have hcc : (Zt.sum D.toRealBundle).coordChange ((Zt.sum D.toRealBundle).indexAt x) (i, j) x
        = (Zt.coordChange (Zt.indexAt x) i x).prodMap (D.coordChange (D.indexAt x) j x) := by
      rw [RealBundle.sum_coordChange, RealBundle.sum_indexAt,
        ComplementData.toRealBundle_coordChange, ComplementData.toRealBundle_indexAt]
    rw [hcc, RealBundle.trivial_coordChange, ContinuousLinearMap.comp_id]
    refine ContinuousLinearMap.ext fun z => ?_
    rw [ContinuousLinearMap.comp_apply,
      show U x = splitBwd D Ainv (Zt.indexAt x) (D.indexAt x) x from rfl,
      ContinuousLinearMap.coe_prodMap', splitBwd_apply]
    simp only [Prod.map]
    have h2 : D.coordChange (D.indexAt x) j x ((D.P (D.indexAt x) x) (eucToFun (8 + k) z))
        = D.P j x (eucToFun (8 + k) z) := by
      rw [D.coordChange_of_mem (D.indexAt x) j x ⟨D.mem_baseSet_at x, hx.2⟩,
        ContinuousLinearMap.comp_apply, hnorm j x hx.2 (eucToFun (8 + k) z)]
      show (D.P j x) ((D.I j x) ((D.P j x) (eucToFun (8 + k) z)))
        = D.P j x (eucToFun (8 + k) z)
      rw [← ContinuousLinearMap.comp_apply, D.P_comp_I]
      rfl
    have h1 : Zt.coordChange (Zt.indexAt x) i x
        (funToEuc 8 (Ainv (Zt.indexAt x) x (eucToFun (8 + k) z)))
        = funToEuc 8 (Ainv i x (eucToFun (8 + k) z)) := by
      have h : eucToFun 8 (Zt.coordChange (Zt.indexAt x) i x
          (funToEuc 8 (Ainv (Zt.indexAt x) x (eucToFun (8 + k) z))))
          = Ainv i x (eucToFun (8 + k) z) := by
        rw [← tCoordInv_apply]
        exact (Ainv_compat i x hx.1 (eucToFun (8 + k) z)).symm
      calc Zt.coordChange (Zt.indexAt x) i x
            (funToEuc 8 (Ainv (Zt.indexAt x) x (eucToFun (8 + k) z)))
          = funToEuc 8 (eucToFun 8 (Zt.coordChange (Zt.indexAt x) i x
              (funToEuc 8 (Ainv (Zt.indexAt x) x (eucToFun (8 + k) z))))) :=
            (funToEuc_eucToFun 8 _).symm
        _ = funToEuc 8 (Ainv i x (eucToFun (8 + k) z)) := by rw [h]
    rw [splitBwd_apply, h1, h2]
  · intro b x
    obtain ⟨v, w⟩ := x
    show splitBwd D Ainv (Zt.indexAt b) (D.indexAt b) b
        (splitFwd D A (Zt.indexAt b) (D.indexAt b) b (v, w)) = (v, w)
    have h1 : Ainv (Zt.indexAt b) b (coeffMap (A (Zt.indexAt b) b) (eucToFun 8 v)
        + D.I (D.indexAt b) b w) = eucToFun 8 v := by
      rw [map_add, Ainv_left (Zt.indexAt b) b (Zt.mem_baseSet_at b) (eucToFun 8 v),
        hkill (Zt.indexAt b) (D.indexAt b) b (Zt.mem_baseSet_at b) (D.mem_baseSet_at b) w,
        add_zero]
    have h2 : D.P (D.indexAt b) b (coeffMap (A (Zt.indexAt b) b) (eucToFun 8 v)
        + D.I (D.indexAt b) b w) = w := by
      rw [map_add, hplane (D.indexAt b) (Zt.indexAt b) b (D.mem_baseSet_at b)
        (Zt.mem_baseSet_at b) (eucToFun 8 v), zero_add, ← ContinuousLinearMap.comp_apply,
        D.P_comp_I]
      rfl
    simp only [splitFwd_apply, splitBwd_apply, eucToFun_funToEuc, h1, h2, funToEuc_eucToFun]
  · intro b z
    show splitFwd D A (Zt.indexAt b) (D.indexAt b) b
        (splitBwd D Ainv (Zt.indexAt b) (D.indexAt b) b z) = z
    have h1 := Ainv_proj (Zt.indexAt b) (D.indexAt b) b (Zt.mem_baseSet_at b)
      (D.mem_baseSet_at b) (eucToFun (8 + k) z)
    simp only [splitBwd_apply, splitFwd_apply, eucToFun_funToEuc, h1, sub_add_cancel,
      funToEuc_eucToFun]

end

end Work.ThomBordism.PontryaginThom
