import Mathlib
import Submission.Work.Pi6.SRANGE.HomQuot
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The concrete model `Zᵢ ⧸ Bᵢ` of the homology of a chain complex of `R`-modules

For a chain complex `K` of `R`-modules (over a commutative ring `R`) the `i`-th homology
`K.homology i` is the quotient of the `i`-cycles by the `i`-boundaries.  This file records the
concrete model of that quotient, in the shape needed by `Work.Pi6.SRANGE.homQuot`:

* `Work.Pi6.SRANGE.cycKer` and `Work.Pi6.SRANGE.cycBnd` — the concrete cycles `Zᵢ` and the
  boundaries `Bᵢ ⊆ Zᵢ` (as the preimage in `Zᵢ` of the range of `dᵢ₊₁`);
* `Work.Pi6.SRANGE.bndMap` — the differential `Xᵢ₊₁ → Zᵢ`, whose range is `Bᵢ`
  (`Work.Pi6.SRANGE.cycBnd_eq_range`);
* `Work.Pi6.SRANGE.cycIso` — `K.cycles i ≅ Zᵢ` (underlying elements unchanged,
  `Work.Pi6.SRANGE.cycIso_hom_val`);
* `Work.Pi6.SRANGE.homQuotIso` — `Hᵢ(K) ≅ Zᵢ ⧸ Bᵢ`, with the computation rules
  `Work.Pi6.SRANGE.homQuotIso_apply` and `Work.Pi6.SRANGE.homQuotIso_inv_apply`.

The statements are the `R`-coefficient analogue of `Work.Kunneth.cycKer`, `Work.Kunneth.homBnd`,
`Work.Kunneth.cycIso`, `Work.Kunneth.homQuotIso` (which are stated over `ℤ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.SRANGE

noncomputable section

variable {R : Type} [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ)

/-- The predecessor of `n` in the chain shape `ComplexShape.down ℕ` is `n + 1`. -/
private theorem down_prev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  ComplexShape.prev_eq' _ (ComplexShape.down_mk (n + 1) n rfl)

/-- The successor of `n` in the chain shape `ComplexShape.down ℕ` is `n - 1`. -/
private theorem down_next (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases n with _ | k
  · exact ComplexShape.next_eq_self' _ 0 (by intro i hi; simp [ComplexShape.down] at hi)
  · rw [ComplexShape.next_eq' _ (ComplexShape.down_mk (k + 1) k rfl)]
    omega

/-- The concrete `i`-cycles of a chain complex: the kernel of the differential `dᵢ`. -/
abbrev cycKer (i : ℕ) : Submodule R ↥(K.X i) := LinearMap.ker (K.d i (i-1)).hom

/-- The concrete `i`-boundaries *inside the cycles*: the preimage in `Zᵢ` of the range of
`dᵢ₊₁`.  This is exactly the submodule whose quotient is `Work.Pi6.SRANGE.homQuot`. -/
abbrev cycBnd (i : ℕ) : Submodule R ↥(cycKer K i) :=
  (LinearMap.range (K.d (i+1) i).hom).comap (cycKer K i).subtype

/-- The differential `Xᵢ₊₁ → Zᵢ`, i.e. `dᵢ₊₁` viewed as a map into the cycles.  Its range is
the submodule of boundaries inside the cycles. -/
abbrev bndMap (i : ℕ) : ↥(K.X (i+1)) →ₗ[R] ↥(cycKer K i) :=
  (K.d (i+1) i).hom.codRestrict (cycKer K i) (fun x => by
    show (K.d i (i-1)).hom ((K.d (i+1) i).hom x) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d K (i+1) i (i-1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x)

/-- The boundaries inside the cycles are the range of the concrete map `Zᵢ₊₁ → Zᵢ`. -/
theorem cycBnd_eq_range (i : ℕ) : cycBnd K i = LinearMap.range (bndMap K i) := by
  rw [cycBnd, bndMap, LinearMap.range_codRestrict]

/-- **The cycles as the concrete kernel of the differential.** -/
def cycIso (i : ℕ) : K.cycles i ≅ ModuleCat.of R ↥(cycKer K i) :=
  (K.cyclesIsoSc' (i+1) i (i-1) (down_prev i) (down_next i)) ≪≫
    ShortComplex.moduleCatCyclesIso (K.sc' (i+1) i (i-1))

/-- **The homology as the concrete quotient `Zᵢ ⧸ Bᵢ`.** -/
def homQuotIso (i : ℕ) :
    K.homology i ≅ ModuleCat.of R (↥(cycKer K i) ⧸ LinearMap.range (bndMap K i)) :=
  (K.homologyIsoSc' (i+1) i (i-1) (down_prev i) (down_next i)) ≪≫
    ShortComplex.moduleCatHomologyIso (K.sc' (i+1) i (i-1))

/-- The projection onto the left homology data of the degree-`i` short complex is the quotient
map `Zᵢ → Zᵢ ⧸ Bᵢ`. -/
theorem LHD_pi_eq (i : ℕ) :
    (ShortComplex.moduleCatLeftHomologyData (K.sc' (i+1) i (i-1))).π
      = ModuleCat.ofHom (LinearMap.range (bndMap K i)).mkQ := by
  rw [ModuleCat.hom_ext_iff, ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl

/-- **The computation rule for `cycIso`**: it does not change the underlying element. -/
theorem cycIso_hom_val (i : ℕ) (c : ↥(K.cycles i)) :
    ((cycIso K i).hom c : ↥(K.X i)) = (K.iCycles i).hom c := by
  have h : (cycIso K i).hom ≫
      (ShortComplex.moduleCatLeftHomologyData (K.sc' (i+1) i (i-1))).i = K.iCycles i := by
    rw [cycIso, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
      HomologicalComplex.cyclesIsoSc'_hom_iCycles]
  have h2 := congrArg (fun (m : K.cycles i ⟶ K.X i) => ModuleCat.Hom.hom m c) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- The inverse of a `ModuleCat`-isomorphism composed with it is the identity, on elements. -/
theorem homIso_inv_apply {M N : ModuleCat.{0} R} (e : M ≅ N) (x : ↥M) :
    e.inv.hom (e.hom.hom x) = x := by
  have h1 : e.inv.hom.comp e.hom.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp e.hom e.inv, Iso.hom_inv_id, ModuleCat.hom_id]
  exact LinearMap.congr_fun h1 x

/-- The interpretation rule of an isomorphism: `e (e⁻¹ y) = y`. -/
theorem homIso_hom_apply {M N : ModuleCat.{0} R} (e : M ≅ N) (y : ↥N) :
    e.hom.hom (e.inv.hom y) = y := by
  have h1 : e.hom.hom.comp e.inv.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp e.inv e.hom, Iso.inv_hom_id, ModuleCat.hom_id]
  exact LinearMap.congr_fun h1 y

/-- **The computation rule for `homQuotIso`**: the class of a cycle is the class of the same
element of `Zᵢ ⧸ Bᵢ`. -/
theorem homQuotIso_apply (i : ℕ) (c : ↥(K.cycles i)) :
    (homQuotIso K i).hom.hom ((K.homologyπ i).hom c)
      = (LinearMap.range (bndMap K i)).mkQ ((cycIso K i).hom c) := by
  have h : (K.homologyπ i) ≫ (homQuotIso K i).hom
      = (cycIso K i).hom ≫ ModuleCat.ofHom (LinearMap.range (bndMap K i)).mkQ := by
    simp only [homQuotIso, Iso.trans_hom, Category.assoc, cycIso,
      HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
    rw [LHD_pi_eq K i]
  have h2 := congrArg (fun (m : K.cycles i ⟶ ModuleCat.of R
      (↥(cycKer K i) ⧸ LinearMap.range (bndMap K i))) => ModuleCat.Hom.hom m c) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h2

/-- **The inverse computation rule for `homQuotIso`**: the class of `z` is sent to the class of
the cycle with underlying element `z`. -/
theorem homQuotIso_inv_apply (i : ℕ) (z : ↥(cycKer K i)) :
    (homQuotIso K i).inv.hom ((LinearMap.range (bndMap K i)).mkQ z)
      = (K.homologyπ i).hom ((cycIso K i).inv z) := by
  have h1 := homQuotIso_apply K i ((cycIso K i).inv z)
  rw [homIso_hom_apply (cycIso K i) z] at h1
  have h2 := congrArg (fun w => (homQuotIso K i).inv.hom w) h1
  rw [homIso_inv_apply (homQuotIso K i)] at h2
  exact h2.symm

/-- The restriction of the `i`-th component of a chain map to the cycles. -/
abbrev restrictMap {K L : ChainComplex (ModuleCat.{0} R) ℕ} (h : K ⟶ L) (i : ℕ) :
    ↥(cycKer K i) →ₗ[R] ↥(cycKer L i) :=
  LinearMap.restrict (h.f i).hom (p := cycKer K i) (q := cycKer L i) (fun x hx => by
    simp only [LinearMap.mem_ker] at hx ⊢
    have hc := congrArg (fun (g : K.X i ⟶ L.X (i-1)) => g.hom x) (h.comm i (i-1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    rw [hc, hx, map_zero])

/-- `restrictMap` does not change the underlying element. -/
theorem restrictMap_apply_val {K L : ChainComplex (ModuleCat.{0} R) ℕ} (h : K ⟶ L) (i : ℕ)
    (z : ↥(cycKer K i)) : (restrictMap h i z : ↥(L.X i)) = (h.f i).hom z := rfl

end

end Work.Pi6.SRANGE
