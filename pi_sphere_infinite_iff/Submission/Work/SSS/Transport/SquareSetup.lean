import Mathlib
import Submission.Work.SSS.serreE1Transport
import Submission.Work.SSS.Transport.Basic

/-!
# The square pullback of a Serre fibration and its corners

Given a Serre fibration `p : E → B` and a homotopy `G : I × I → B` of paths, this file sets up the
geometric objects used to compare the fibre transports along the two horizontal edges: the square
pullback `Pullback p G`, its four corner fibres, the embeddings of the pullbacks along the edges, the
canonical homeomorphisms between edge fibres and corner fibres, and the two slice maps
`fibre p b → Pullback p G` whose homotopy relates the two ends of the bottom/top edges.
-/

set_option autoImplicit false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.SSS

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The contraction of the square to a point -/

/-- The underlying function of the straight-line contraction of the square `I × I` to a point `c`,
as a map `(I × I) × I → I × I`. -/
def sqContrFun (c : unitInterval × unitInterval)
    (z : (unitInterval × unitInterval) × unitInterval) : unitInterval × unitInterval :=
  (⟨(z.1.1 : ℝ) * (1 - (z.2 : ℝ)) + (c.1 : ℝ) * (z.2 : ℝ), by
    have h1 : (0 : ℝ) ≤ (z.1.1 : ℝ) := (z.1.1.2).1
    have h2 : (z.1.1 : ℝ) ≤ 1 := (z.1.1.2).2
    have h3 : (0 : ℝ) ≤ (c.1 : ℝ) := (c.1.2).1
    have h4 : (c.1 : ℝ) ≤ 1 := (c.1.2).2
    have h5 : (0 : ℝ) ≤ (z.2 : ℝ) := (z.2.2).1
    have h6 : (z.2 : ℝ) ≤ 1 := (z.2.2).2
    constructor <;> nlinarith⟩,
   ⟨(z.1.2 : ℝ) * (1 - (z.2 : ℝ)) + (c.2 : ℝ) * (z.2 : ℝ), by
    have h1 : (0 : ℝ) ≤ (z.1.2 : ℝ) := (z.1.2.2).1
    have h2 : (z.1.2 : ℝ) ≤ 1 := (z.1.2.2).2
    have h3 : (0 : ℝ) ≤ (c.2 : ℝ) := (c.2.2).1
    have h4 : (c.2 : ℝ) ≤ 1 := (c.2.2).2
    have h5 : (0 : ℝ) ≤ (z.2 : ℝ) := (z.2.2).1
    have h6 : (z.2 : ℝ) ≤ 1 := (z.2.2).2
    constructor <;> nlinarith⟩)

/-- The straight-line contraction of the square `I × I` to a point `c`, as a map
`(I × I) × I → I × I`. -/
def sqContr (c : unitInterval × unitInterval) :
    C((unitInterval × unitInterval) × unitInterval, unitInterval × unitInterval) where
  toFun := sqContrFun c
  continuous_toFun := by
    unfold sqContrFun
    apply Continuous.prodMk <;> apply Continuous.subtype_mk <;> fun_prop

@[simp]
theorem sqContr_apply (c z) : sqContr c z = sqContrFun c z := rfl

@[simp]
theorem sqContr_zero (c z : unitInterval × unitInterval) : sqContr c (z, 0) = z := by
  refine Prod.ext ?_ ?_ <;> (apply Subtype.ext; simp only [sqContr_apply, sqContrFun,
    Set.Icc.coe_zero, Set.Icc.coe_one]; ring)

@[simp]
theorem sqContr_one (c z : unitInterval × unitInterval) : sqContr c (z, 1) = c := by
  refine Prod.ext ?_ ?_ <;> (apply Subtype.ext; simp only [sqContr_apply, sqContrFun,
    Set.Icc.coe_zero, Set.Icc.coe_one]; ring)

@[simp]
theorem sqContr_self (c : unitInterval × unitInterval) (u : unitInterval) : sqContr c (c, u) = c := by
  refine Prod.ext ?_ ?_ <;> (apply Subtype.ext; simp only [sqContr_apply, sqContrFun,
    Set.Icc.coe_zero, Set.Icc.coe_one]; ring)

/-! ## The corner fibres of the square pullback -/

/-- The fibre of the square pullback `Pullback p G → I × I` over the point `c`. -/
def sqCorner (p : C(E, B)) (G : C(unitInterval × unitInterval, B))
    (c : unitInterval × unitInterval) : Set (Work.StemsB.Pullback p G) :=
  {x | Work.StemsB.pullbackSnd p G x = c}

/-- The corner inclusion is a homology isomorphism: the pair of the square pullback with a corner
fibre has vanishing relative homology, because the square is contractible to the corner. -/
theorem isIso_homologyMap_sqCornerIncl (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (c : unitInterval × unitInterval) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p G)) (sqCorner p G c)) j) :=
  Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
    (fun m => Work.Serre.isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd p G)
      (fun i => Work.StemsB.hasHLP_pullback p G (hp i)) c (sqContr c)
      (sqContr_zero c) (sqContr_one c) (sqContr_self c) m) j

/-- The homology isomorphism induced by the inclusion of a corner fibre of the square pullback. -/
def sqCornerInclIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (G : C(unitInterval × unitInterval, B)) (c : unitInterval × unitInterval) (j : ℕ) :
    (Work.PiS.HZ ↥(sqCorner p G c) j) ≅ (Work.PiS.HZ (Work.StemsB.Pullback p G) j) :=
  haveI := isIso_homologyMap_sqCornerIncl p hp G c j
  asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p G)) (sqCorner p G c)) j)

/-! ## Edge fibres and the embedding of the edge pullbacks into the square -/

/-- The fibre of the pullback along a path over a point of the interval. -/
def edgeFibre (p : C(E, B)) (γ : C(unitInterval, B)) (s₀ : unitInterval) :
    Set (Work.StemsB.Pullback p γ) := {x | Work.StemsB.pullbackSnd p γ x = s₀}

/-- The embedding of the pullback along a path into the square pullback along the slice `t₀`. -/
def sliceEmb (p : C(E, B)) (G : C(unitInterval × unitInterval, B)) (t₀ : unitInterval)
    (γ : C(unitInterval, B)) (hγ : ∀ s, G (t₀, s) = γ s) :
    C(Work.StemsB.Pullback p γ, Work.StemsB.Pullback p G) where
  toFun x := ⟨(x.1.1, (t₀, x.1.2)), by
    show p x.1.1 = G (t₀, x.1.2)
    rw [hγ x.1.2]
    exact x.2⟩
  continuous_toFun := by fun_prop

/-- The canonical homeomorphism between the fibre of the path pullback over `s₀` and the corner
fibre of the square pullback over `(t₀, s₀)`. -/
def sliceFibreHomeo (p : C(E, B)) (G : C(unitInterval × unitInterval, B)) (t₀ : unitInterval)
    (γ : C(unitInterval, B)) (hγ : ∀ s, G (t₀, s) = γ s) (s₀ : unitInterval) :
    ↥(edgeFibre p γ s₀) ≃ₜ ↥(sqCorner p G (t₀, s₀)) where
  toFun x := ⟨sliceEmb p G t₀ γ hγ x.1, by
    have h : (x.1 : Work.StemsB.Pullback p γ).1.2 = s₀ := x.2
    show (t₀, (x.1 : Work.StemsB.Pullback p γ).1.2) = (t₀, s₀)
    rw [h]⟩
  invFun y := ⟨⟨(y.1.1.1, s₀), by
      calc p y.1.1.1 = G y.1.1.2 := y.1.2
        _ = G (t₀, s₀) := by rw [show y.1.1.2 = (t₀, s₀) from y.2]
        _ = γ s₀ := by rw [hγ s₀]⟩, rfl⟩
  left_inv x := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    exact (show (x.1 : Work.StemsB.Pullback p γ).1.2 = s₀ from x.2).symm
  right_inv y := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    exact (show y.1.1.2 = (t₀, s₀) from y.2).symm
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The canonical homeomorphism between the fibre of `p` over `b` and the corner fibre of the
square pullback over `c`, when `G c = b`. -/
def fibreCornerHomeo (p : C(E, B)) (G : C(unitInterval × unitInterval, B))
    (c : unitInterval × unitInterval) (b : B) (h : G c = b) :
    Work.StemsB.fibre p b ≃ₜ ↥(sqCorner p G c) where
  toFun e := ⟨⟨(e.1, c), e.2.trans h.symm⟩, rfl⟩
  invFun y := ⟨y.1.1.1, by
    calc p y.1.1.1 = G y.1.1.2 := y.1.2
      _ = G c := by rw [show y.1.1.2 = c from y.2]
      _ = b := h⟩
  left_inv e := by
    refine Subtype.ext ?_
    rfl
  right_inv y := by
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    exact (show y.1.1.2 = c from y.2).symm
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ## The composite homeomorphisms at the two ends of an edge -/

/-- At the starting end of an edge: composing the canonical homeomorphism of fibres, the inverse of
`pullbackFibreHomeo` and the edge-to-corner homeomorphism gives the canonical homeomorphism from the
fibre of `p` over the endpoint to the corner fibre. -/
theorem homeoFibreEq_trans_sliceFibreHomeo (p : C(E, B)) (G : C(unitInterval × unitInterval, B))
    (t₀ s₀ : unitInterval) (γ : C(unitInterval, B)) (hγ : ∀ s, G (t₀, s) = γ s) (b : B)
    (hb : γ s₀ = b) (h : G (t₀, s₀) = b) :
    ((homeoFibreEq p hb.symm).trans (pullbackFibreHomeo p γ s₀).symm).trans
        (sliceFibreHomeo p G t₀ γ hγ s₀) =
      fibreCornerHomeo p G (t₀, s₀) b h := by
  refine Homeomorph.ext (fun e => ?_)
  exact Subtype.ext (Subtype.ext rfl)

/-- At the ending end of an edge: composing the inverse of the edge-to-corner homeomorphism, the
`pullbackFibreHomeo` and the canonical homeomorphism of fibres gives the inverse of the canonical
homeomorphism from the fibre of `p` over the endpoint to the corner fibre. -/
theorem sliceFibreHomeo_symm_trans_homeoFibreEq (p : C(E, B)) (G : C(unitInterval × unitInterval, B))
    (t₀ s₀ : unitInterval) (γ : C(unitInterval, B)) (hγ : ∀ s, G (t₀, s) = γ s) (b : B)
    (hb : γ s₀ = b) (h : G (t₀, s₀) = b) :
    ((sliceFibreHomeo p G t₀ γ hγ s₀).symm.trans (pullbackFibreHomeo p γ s₀)).trans
        (homeoFibreEq p hb) =
      (fibreCornerHomeo p G (t₀, s₀) b h).symm := by
  rw [← homeoFibreEq_trans_sliceFibreHomeo p G t₀ s₀ γ hγ b hb h]
  have hs : (homeoFibreEq p hb.symm).symm = homeoFibreEq p hb :=
    Homeomorph.ext (fun e => Subtype.ext rfl)
  rw [show ((homeoFibreEq p hb.symm).trans (pullbackFibreHomeo p γ s₀).symm |>.trans
        (sliceFibreHomeo p G t₀ γ hγ s₀)).symm =
      ((sliceFibreHomeo p G t₀ γ hγ s₀).symm.trans (pullbackFibreHomeo p γ s₀)).trans
        (homeoFibreEq p hb.symm).symm from rfl, hs]

/-! ## The slice maps and their homotopy -/

/-- The map `fibre p b → Pullback p G` sending `e` to `(e, (t, s₀))`, for a point `s₀` of the
interval such that `G (u, s₀) = b` for all `u`. -/
def sideMap (p : C(E, B)) (G : C(unitInterval × unitInterval, B)) {b : B} (s₀ : unitInterval)
    (h : ∀ u, G (u, s₀) = b) (t : unitInterval) :
    C(Work.StemsB.fibre p b, Work.StemsB.Pullback p G) where
  toFun e := ⟨(e.1, (t, s₀)), by
    show p e.1 = G (t, s₀)
    rw [h t]
    exact e.2⟩
  continuous_toFun := by fun_prop

/-- The slice maps `e ↦ (e, (t, s₀))` for `t = 0` and `t = 1` are homotopic. -/
def sideMapHomotopy (p : C(E, B)) (G : C(unitInterval × unitInterval, B)) {b : B}
    (s₀ : unitInterval) (h : ∀ u, G (u, s₀) = b) :
    (sideMap p G s₀ h 0).Homotopy (sideMap p G s₀ h 1) :=
  ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨(z.2.1, (z.1, s₀)), by
      show p z.2.1 = G (z.1, s₀)
      rw [h z.1]
      exact z.2.2⟩, by fun_prop⟩
    (fun e => rfl) (fun e => rfl)

/-- The two slice maps induce the same map on homology, being homotopic. -/
theorem homologyMap_sideMap_eq (p : C(E, B)) (G : C(unitInterval × unitInterval, B)) {b : B}
    (s₀ : unitInterval) (h : ∀ u, G (u, s₀) = b) (j : ℕ) :
    HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.fibre p b))
          (TopCat.of (Work.StemsB.Pullback p G)) (TopCat.ofHom (sideMap p G s₀ h 0))) j =
      HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of (Work.StemsB.fibre p b))
          (TopCat.of (Work.StemsB.Pullback p G)) (TopCat.ofHom (sideMap p G s₀ h 1))) j := by
  have hh : TopCat.Homotopy (TopCat.ofHom (sideMap p G s₀ h 0))
      (TopCat.ofHom (sideMap p G s₀ h 1)) := sideMapHomotopy p G s₀ h
  exact Homotopy.homologyMap_eq (hh.singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)) j

/-! ## The straight-line contraction of the interval -/

/-- The straight-line contraction of the interval to a point `c`. -/
def intervalContrFun (c : unitInterval) (z : unitInterval × unitInterval) : unitInterval :=
  ⟨(z.1 : ℝ) * (1 - (z.2 : ℝ)) + (c : ℝ) * (z.2 : ℝ), by
    have h1 : (0 : ℝ) ≤ (z.1 : ℝ) := (z.1.2).1
    have h2 : (z.1 : ℝ) ≤ 1 := (z.1.2).2
    have h3 : (0 : ℝ) ≤ (c : ℝ) := (c.2).1
    have h4 : (c : ℝ) ≤ 1 := (c.2).2
    have h5 : (0 : ℝ) ≤ (z.2 : ℝ) := (z.2.2).1
    have h6 : (z.2 : ℝ) ≤ 1 := (z.2.2).2
    constructor <;> nlinarith⟩

/-- The straight-line contraction of the interval to a point `c`, as a map `I × I → I`. -/
def intervalContr (c : unitInterval) : C(unitInterval × unitInterval, unitInterval) where
  toFun := intervalContrFun c
  continuous_toFun := by
    unfold intervalContrFun
    apply Continuous.subtype_mk
    fun_prop

@[simp]
theorem intervalContr_apply (c z) : intervalContr c z = intervalContrFun c z := rfl

@[simp]
theorem intervalContr_zero (c z : unitInterval) : intervalContr c (z, 0) = z := by
  apply Subtype.ext
  simp only [intervalContr_apply, intervalContrFun, Set.Icc.coe_zero, Set.Icc.coe_one]
  ring

@[simp]
theorem intervalContr_one (c z : unitInterval) : intervalContr c (z, 1) = c := by
  apply Subtype.ext
  simp only [intervalContr_apply, intervalContrFun, Set.Icc.coe_zero, Set.Icc.coe_one]
  ring

@[simp]
theorem intervalContr_self (c u : unitInterval) : intervalContr c (c, u) = c := by
  apply Subtype.ext
  simp only [intervalContr_apply, intervalContrFun, Set.Icc.coe_zero, Set.Icc.coe_one]
  ring

/-! ## The fibre inclusions of a path pullback -/

/-- The inclusion of a fibre of the path pullback is a homology isomorphism. -/
theorem isIso_homologyMap_edgeIncl (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (γ : C(unitInterval, B)) (s₀ : unitInterval) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p γ)) (edgeFibre p γ s₀)) j) :=
  Work.Serre.isIso_inclChains_homologyMap_of_isZero_relChains _
    (fun m => Work.Serre.isZero_relChains_fibre_of_contraction (Work.StemsB.pullbackSnd p γ)
      (fun i => Work.StemsB.hasHLP_pullback p γ (hp i)) s₀ (intervalContr s₀)
      (intervalContr_zero s₀) (intervalContr_one s₀) (intervalContr_self s₀) m) j

/-- The homology isomorphism induced by the inclusion of a fibre of the path pullback. -/
def edgeInclIso (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (γ : C(unitInterval, B)) (s₀ : unitInterval) (j : ℕ) :
    (Work.PiS.HZ ↥(edgeFibre p γ s₀) j) ≅ (Work.PiS.HZ (Work.StemsB.Pullback p γ) j) :=
  haveI := isIso_homologyMap_edgeIncl p hp γ s₀ j
  asIso (HomologicalComplex.homologyMap
    (Work.Cohomology.inclChains (TopCat.of (Work.StemsB.Pullback p γ)) (edgeFibre p γ s₀)) j)

/-- The transport of `Work.SSS.pullbackTransportIso` is the composite of the two fibre inclusions,
with the `IsIso` instances chosen by hand so that the definitional unfolding is available. -/
theorem pullbackTransportIso_eq (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (γ : C(unitInterval, B)) (j : ℕ) :
    pullbackTransportIso p hp γ j = edgeInclIso p hp γ 0 j ≪≫ (edgeInclIso p hp γ 1 j).symm := by
  unfold pullbackTransportIso edgeInclIso
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom]
  congr 1


end

end Work.SSS
