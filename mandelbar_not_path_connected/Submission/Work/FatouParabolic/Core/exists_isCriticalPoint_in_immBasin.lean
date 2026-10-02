/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# Fatou's theorem on the *immediate* parabolic basin (design `gaps2` §2.1, Q6)

For a polynomial map `F : ℂ → ℂ` of degree `≥ 2`, a fixed point `z₀` of multiplier `1` with a
Leau–Fatou flower `fl`, and a petal point `p₀ ∈ fl.Pa`, the **immediate basin**

`immBasin F z₀ p₀ = connectedComponentIn (interior (basin F z₀)) p₀`

contains a critical point of `F`.  This is the corrected form of Fatou's theorem in which the
simple-connectivity hypothesis `ParabolicBasinSimplyConnected` of `Core/Main.lean` is replaced by
the covering/lifting argument on the immediate basin (the design of
`Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §2.1).

The proof is the classical one, split as in the design:

* **Q1** (`exists_immBasin_basics` below): the immediate basin `Ω` is open, contains the petal, is
  `F`-invariant, bounded (escape condition), and is relatively closed in `interior (basin F z₀)`;
* **Q2** (`exists_isCoveringMap_immBasinIterate` below): if `Ω` has no critical point of `F`, then
  every iterate `F^[n] : Ω → Ω` is a covering map (closedness of `F^[n]`, finiteness of its
  fibres, and local biholomorphy of `F^[n]` on `Ω`);
* **Q3** (`Core/exists_petalInverse`): the inverse Fatou coordinate of the petal exists on the tail
  of every horizontal strip; here it is packaged through the canonical inverse
  `petalInv = Function.invFunOn fl.φa fl.Pa` into the single function `Φ` of the next step;
* **Q4–Q6** (`Core/ImmBasin/false_of_petalInverse_of_covering`): lifting `Φ` through the coverings
  produces a bounded entire function that is injective on a tail strip, contradicting Liouville.

Everything here is proved outright, with no placeholders.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.exists_petalInverse
import Submission.Work.FatouParabolic.Core.isBounded_puncturedBasin_of_escape
import Submission.Work.FatouParabolic.Core.isOpen_puncturedBasin
import Submission.Work.FatouParabolic.Core.isLocalHomeomorphOn_of_deriv_ne_zero
import Submission.Work.FatouParabolic.Core.isProperMap_of_escapeBound
import Submission.Work.FatouParabolic.Core.ImmBasin.false_of_petalInverse_of_covering
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_basinEscape
import Submission.Work.SeedDyn.isLocalHomeomorph_subtypeMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

set_option linter.unusedVariables false

namespace Work.FatouParabolic.Core

noncomputable section

/-! ## The canonical inverse of the Fatou coordinate on the petal -/

/-- **The canonical petal inverse**: the point of the petal whose Fatou coordinate is `τ`, when it
exists (`Function.invFunOn` picks an arbitrary preimage, but `fl.φa_fatou.2` makes it unique).
This is the single function `Φ` which satisfies the petal-inverse properties
`Core/exists_petalInverse` on the tail of *every* horizontal strip simultaneously. -/
def petalInv {F g : ℂ → ℂ} {z₀ : ℂ} (fl : Work.FatouParabolic.FlowerImageFix F g z₀) : ℂ → ℂ :=
  Function.invFunOn fl.φa fl.Pa

/-- **The canonical petal inverse satisfies all the properties of `exists_petalInverse`, with a
single function for all heights `B > 0`.** -/
theorem petalInv_spec {F g : ℂ → ℂ} {z₀ : ℂ} (fl : Work.FatouParabolic.FlowerImageFix F g z₀)
    (hF : Differentiable ℂ F) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| < B →
      petalInv fl τ ∈ fl.Pa ∧ fl.φa (petalInv fl τ) = τ ∧
      F (petalInv fl τ) = petalInv fl (τ + 1) ∧ DifferentiableAt ℂ (petalInv fl) τ := by
  obtain ⟨C, Ψ₀, hΨ₀⟩ := exists_petalInverse fl hF hB
  -- on the tail strip of height `B`, `petalInv` agrees with the witness `Ψ₀`
  have agree : ∀ σ : ℂ, C < σ.re → |σ.im| < B → petalInv fl σ = Ψ₀ σ := by
    intro σ h1 h2
    obtain ⟨hmem, hφ, -, -⟩ := hΨ₀ σ h1 h2
    have hex : ∃ z ∈ fl.Pa, fl.φa z = σ := ⟨Ψ₀ σ, hmem, hφ⟩
    exact fl.φa_fatou.2 (Function.invFunOn_mem hex) hmem
      (by rw [Function.invFunOn_eq hex, hφ])
  refine ⟨C, fun τ hτ1 hτ2 => ?_⟩
  have hadd : C < (τ + 1).re ∧ |(τ + 1).im| < B :=
    ⟨by simp only [Complex.add_re, Complex.one_re]; linarith, by simpa using hτ2⟩
  obtain ⟨hmem, hφ, hFτ, hd⟩ := hΨ₀ τ hτ1 hτ2
  refine ⟨agree τ hτ1 hτ2 ▸ hmem, agree τ hτ1 hτ2 ▸ hφ, ?_, ?_⟩
  · rw [agree τ hτ1 hτ2, agree (τ + 1) hadd.1 hadd.2]
    exact hFτ
  · refine hd.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_tailStrip C B).mem_nhds ⟨hτ1, hτ2⟩] with σ hσ
    exact agree σ hσ.1 hσ.2

/-! ## Polynomial maps: openness and finiteness of the fibres -/

/-- A polynomial map of degree `≥ 2` is an open map (directly, since a nonconstant polynomial is
an open quotient map of `ℂ`). -/
theorem exists_isOpenMap_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) : IsOpenMap F := by
  obtain ⟨P, hPdeg, hPF⟩ := hF
  have hne : P.natDegree ≠ 0 := by omega
  rw [show F = fun z : ℂ => P.eval z from funext hPF]
  exact (Polynomial.isOpenQuotientMap_eval P hne).isOpenMap

/-- A polynomial map of degree `≥ 2` has finite fibres (it pulls the cofinite filter back to the
cofinite filter). -/
theorem exists_tendstoCofinite_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) : Filter.TendstoCofinite F := by
  obtain ⟨P, hPdeg, hPF⟩ := hF
  have hne : P.natDegree ≠ 0 := by omega
  rw [show F = fun z : ℂ => P.eval z from funext hPF]
  exact Polynomial.tendstoCofinite_of_natDegree_ne_zero P hne

/-- Every iterate of a polynomial map of degree `≥ 2` has finite fibres. -/
theorem exists_tendstoCofinite_iterate_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (n : ℕ) :
    Filter.TendstoCofinite (F^[n]) := by
  have hFc : Filter.TendstoCofinite F :=
    exists_tendstoCofinite_of_isPolynomialMapOfDegreeAtLeastTwo hF
  induction n with
  | zero => simpa using (Filter.TendstoCofinite.id (α := ℂ))
  | succ n ih =>
      have hcomp : F^[n.succ] = F ∘ F^[n] := by
        funext z
        simp [Function.comp_apply, Function.iterate_succ_apply']
      rw [hcomp]
      exact Filter.TendstoCofinite.comp (F^[n]) F

/-- The fibre of an iterate of a polynomial map of degree `≥ 2` over any point is finite. -/
theorem exists_finite_fiber_iterate_of_isPolynomialMapOfDegreeAtLeastTwo {F : ℂ → ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (n : ℕ) (a : ℂ) :
    ((F^[n]) ⁻¹' {a}).Finite :=
  (Filter.tendstoCofinite_iff_finite_preimage_singleton (F^[n])).mp
    (exists_tendstoCofinite_iterate_of_isPolynomialMapOfDegreeAtLeastTwo hF n) a

/-! ## Q1: the structural data of the immediate basin -/

/-- The immediate basin is open (it is a connected component of the open set
`interior (basin F z₀)`). -/
theorem exists_isOpen_immBasin (F : ℂ → ℂ) (z₀ p₀ : ℂ) : IsOpen (immBasin F z₀ p₀) :=
  isOpen_interior.connectedComponentIn

/-- The petal of a Leau–Fatou flower lies in the immediate basin: it is open and contained in the
basin, hence in `interior (basin)`, and preconnected through `p₀`. -/
theorem exists_pa_subset_immBasin {F g : ℂ → ℂ} {z₀ : ℂ}
    (fl : Work.FatouParabolic.FlowerImageFix F g z₀) {p₀ : ℂ} (hp₀ : p₀ ∈ fl.Pa) :
    fl.Pa ⊆ immBasin F z₀ p₀ := by
  have hPa_basin : fl.Pa ⊆ Work.FatouParabolic.basin F z₀ :=
    fun z hz => Work.FatouParabolic.mem_basin.mpr (fl.tendsto_Pa z hz)
  have hPa_int : fl.Pa ⊆ interior (Work.FatouParabolic.basin F z₀) :=
    interior_maximal hPa_basin fl.isOpen_Pa
  exact fl.isPreconnected_Pa.subset_connectedComponentIn hp₀ hPa_int

/-- The immediate basin is invariant under `F`. -/
theorem exists_mapsTo_immBasin {F g : ℂ → ℂ} {z₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F)
    (fl : Work.FatouParabolic.FlowerImageFix F g z₀) {p₀ : ℂ} (hp₀ : p₀ ∈ fl.Pa) :
    Set.MapsTo F (immBasin F z₀ p₀) (immBasin F z₀ p₀) := by
  have hopenmap : IsOpenMap F := exists_isOpenMap_of_isPolynomialMapOfDegreeAtLeastTwo hF
  have hcont : Continuous F := (Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF).continuous
  have hPaimm : fl.Pa ⊆ immBasin F z₀ p₀ := exists_pa_subset_immBasin fl hp₀
  have hFp₀ : F p₀ ∈ immBasin F z₀ p₀ := hPaimm (fl.mapsTo_Pa hp₀)
  -- `F '' Ω` is open and contained in the basin, hence in `interior (basin)`
  have hFΩ_int : F '' (immBasin F z₀ p₀) ⊆ interior (Work.FatouParabolic.basin F z₀) := by
    refine interior_maximal ?_ (hopenmap _ (exists_isOpen_immBasin F z₀ p₀))
    rintro _ ⟨z, hz, rfl⟩
    have hzbasin : z ∈ Work.FatouParabolic.basin F z₀ := immBasin_subset_basin hz
    rw [Work.FatouParabolic.mem_basin] at hzbasin ⊢
    rw [show (fun k : ℕ => (F^[k]) (F z)) = (fun k : ℕ => (F^[k + 1]) z) from
      funext fun k => (Function.iterate_succ_apply F k z).symm]
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => (F^[k]) z) 1).mpr hzbasin
  have himg : F '' (immBasin F z₀ p₀) ⊆
      connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) (F p₀) :=
    (isPreconnected_connectedComponentIn.image F hcont.continuousOn).subset_connectedComponentIn
      ⟨p₀, hPaimm hp₀, rfl⟩ hFΩ_int
  rw [← connectedComponentIn_eq hFp₀] at himg
  intro z hz
  exact himg ⟨z, hz, rfl⟩

/-- The immediate basin is bounded: it is contained in the basin, which the escape condition
confines to a disc. -/
theorem exists_isBounded_immBasin {F : ℂ → ℂ} {z₀ p₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) :
    Bornology.IsBounded (immBasin F z₀ p₀) := by
  obtain ⟨R, hRpos, hR⟩ := Work.FatouParabolic.Poly.isPolynomialMap_basinEscape hF
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (norm_lt_of_mem_basin_of_escape hRpos hR (immBasin_subset_basin hz))

/-- **Backwards invariance of `interior (basin)`**: if `F^[m] x` lies in the interior of the
basin, so does `x`.  Indeed `F^[m] x ∈ basin` forces `x ∈ basin` (shift the orbit), and then a
whole neighbourhood of `x` is mapped by `F^[m]` into the open set `interior (basin)`, hence lies
in the basin. -/
theorem exists_preimage_interior_basin {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (m : ℕ) :
    ∀ x : ℂ, (F^[m]) x ∈ interior (Work.FatouParabolic.basin F z₀) →
      x ∈ interior (Work.FatouParabolic.basin F z₀) := by
  have hdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  have hsub : (F^[m]) ⁻¹' interior (Work.FatouParabolic.basin F z₀)
      ⊆ Work.FatouParabolic.basin F z₀ := by
    intro y hy
    have hyb : (F^[m]) y ∈ Work.FatouParabolic.basin F z₀ := interior_subset hy
    rw [Work.FatouParabolic.mem_basin] at hyb ⊢
    have hshift : (fun k : ℕ => (F^[k]) ((F^[m]) y)) = fun k : ℕ => (F^[k + m]) y := by
      funext k
      exact (Function.iterate_add_apply F k m y).symm
    rw [hshift] at hyb
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => (F^[k]) y) m).mp hyb
  intro x hx
  have hnhds : (F^[m]) ⁻¹' interior (Work.FatouParabolic.basin F z₀) ∈ 𝓝 x :=
    ((hdiff.continuous.iterate m).continuousAt).preimage_mem_nhds (isOpen_interior.mem_nhds hx)
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hnhds hsub)

/-- **The immediate basin is relatively closed in `interior (basin)`**: any point of
`interior (basin)` in the closure of the component of `p₀` belongs to it. -/
theorem exists_immBasin_closed_in_interior (F : ℂ → ℂ) (z₀ p₀ : ℂ) :
    ∀ x ∈ interior (Work.FatouParabolic.basin F z₀),
      x ∈ closure (immBasin F z₀ p₀) → x ∈ immBasin F z₀ p₀ := by
  intro x hx hxcl
  by_contra hxnot
  have hCx : IsOpen (connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) x) :=
    isOpen_interior.connectedComponentIn
  have hxCx : x ∈ connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) x :=
    mem_connectedComponentIn hx
  obtain ⟨y, hyx, hyΩ⟩ := mem_closure_iff.mp hxcl _ hCx hxCx
  have h1 : connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) x
      = connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) y :=
    connectedComponentIn_eq hyx
  have h2 : connectedComponentIn (interior (Work.FatouParabolic.basin F z₀)) y
      = immBasin F z₀ p₀ := (connectedComponentIn_eq hyΩ).symm
  exact hxnot (h1.trans h2 ▸ hxCx)

/-! ## Q2: the iterates are coverings of the critical-point-free immediate basin -/

/-- **A closed map that is saturated along a set `P` restricts to a closed self-map of `Ω`.**

Let `Ω, P ⊆ ℂ` with `Ω ⊆ P`, let `G : ℂ → ℂ` be a closed map, suppose `G` does not leave `P`
backwards (`G x ∈ P → x ∈ P`), and suppose `Ω` is closed inside `P`.  Then any self-map `g` of
`Ω` whose underlying map is `G` is a closed map. -/
private theorem exists_isClosedMap_of_coe_eq {Ω P : Set ℂ} {G : ℂ → ℂ} {g : ↥Ω → ↥Ω}
    (hG : IsClosedMap G) (hcoe : ∀ x : ↥Ω, (g x : ℂ) = G x.1)
    (hpre : ∀ x : ℂ, G x ∈ P → x ∈ P) (hΩP : Ω ⊆ P)
    (hcl : ∀ x ∈ P, x ∈ closure Ω → x ∈ Ω) : IsClosedMap g := by
  rw [isClosedMap_iff_closure_image]
  intro s y hy
  have hy' : (y : ℂ) ∈ closure (Subtype.val '' (g '' s)) := by
    have h := Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image (g '' s)
    rw [h] at hy
    exact hy
  have himg : Subtype.val '' (g '' s) = G '' (Subtype.val '' s) := by
    ext z
    constructor
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x.1, ⟨x, hx, rfl⟩, (hcoe x).symm⟩
    · rintro ⟨z', ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨g x, ⟨x, hx, rfl⟩, hcoe x⟩
  rw [himg] at hy'
  have hyD : (y : ℂ) ∈ G '' closure (Subtype.val '' s) :=
    hG.closure_image_subset (Subtype.val '' s) hy'
  rcases hyD with ⟨x, hxclD, hxGx⟩
  have hxP : x ∈ P := hpre x (by rw [hxGx]; exact hΩP y.2)
  have hxclΩ : x ∈ closure Ω := closure_mono (by rintro _ ⟨x, -, rfl⟩; exact x.2) hxclD
  have hxΩ : x ∈ Ω := hcl x hxP hxclΩ
  refine ⟨⟨x, hxΩ⟩, ?_, ?_⟩
  · have h := Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image s
    rw [h]
    exact hxclD
  · exact Subtype.ext (by rw [hcoe]; exact hxGx)

/-- **Every iterate `F^[n] : Ω → Ω` of a critical-point-free immediate basin is a covering map.**

* the local homeomorphism `F^[n] : Ω → Ω` comes from `deriv F ≠ 0` on `Ω` and the openness of
  `Ω` (`Work.SeedDyn.isLocalHomeomorph_subtypeMap`);
* `F^[n] : Ω → Ω` is closed, by the saturation lemma above with `P = interior (basin F z₀)`;
* its fibres are finite, being contained in the fibres of the polynomial map `F^[n]`. -/
theorem exists_isCoveringMap_immBasinIterate {F : ℂ → ℂ} {z₀ p₀ : ℂ} (n : ℕ)
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (hopen : IsOpen (immBasin F z₀ p₀))
    (hmap : Set.MapsTo F (immBasin F z₀ p₀) (immBasin F z₀ p₀))
    (hΩP : immBasin F z₀ p₀ ⊆ interior (Work.FatouParabolic.basin F z₀))
    (hcl : ∀ x ∈ interior (Work.FatouParabolic.basin F z₀),
      x ∈ closure (immBasin F z₀ p₀) → x ∈ immBasin F z₀ p₀)
    (hbdd : Bornology.IsBounded (immBasin F z₀ p₀))
    (hnocrit : ∀ w ∈ immBasin F z₀ p₀, deriv F w ≠ 0) :
    IsCoveringMap (immBasinIterate (immBasin F z₀ p₀) F hmap n) := by
  have hFdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  have hesc : Work.FatouParabolic.BasinEscape F :=
    Work.FatouParabolic.Poly.isPolynomialMap_basinEscape hF
  -- `F^[n]` is closed, being a proper map of `ℂ`
  have hproperF : IsProperMap F := isProperMap_of_escapeBound hFdiff.continuous hesc
  have hclosedN : IsClosedMap (F^[n]) := by
    induction n with
    | zero => rw [Function.iterate_zero]; exact IsClosedMap.id
    | succ k ih => rw [Function.iterate_succ']; exact hproperF.isClosedMap.comp ih
  have hclosed : IsClosedMap (immBasinIterate (immBasin F z₀ p₀) F hmap n) :=
    exists_isClosedMap_of_coe_eq hclosedN (fun x => immBasinIterate_coe x)
      (exists_preimage_interior_basin hF n) hΩP hcl
  -- the fibres of the restriction are finite
  have hfin : ∀ y : ↥(immBasin F z₀ p₀),
      (immBasinIterate (immBasin F z₀ p₀) F hmap n ⁻¹' {y}).Finite := by
    intro y
    have hfiber : ((F^[n]) ⁻¹' {y.1}).Finite :=
      exists_finite_fiber_iterate_of_isPolynomialMapOfDegreeAtLeastTwo hF n y.1
    refine (hfiber.preimage Subtype.val_injective.injOn).subset ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [← hx, immBasinIterate_coe]
  -- `F^[n]` is a local homeomorphism on `Ω`, hence so is its restriction to the subtype
  have hlocF : IsLocalHomeomorphOn F (immBasin F z₀ p₀) :=
    isLocalHomeomorphOn_of_deriv_ne_zero hFdiff hnocrit
  have hlocFn : ∀ m : ℕ, IsLocalHomeomorphOn (F^[m]) (immBasin F z₀ p₀) := by
    intro m
    induction m with
    | zero =>
        simpa [Function.iterate_zero] using
          (Homeomorph.refl ℂ).isLocalHomeomorph.isLocalHomeomorphOn (s := immBasin F z₀ p₀)
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hlocF.comp ih (Work.FatouCoord.mapsTo_iterate_of_mapsTo hmap k)
  have hloc : IsLocalHomeomorph (immBasinIterate (immBasin F z₀ p₀) F hmap n) :=
    Work.SeedDyn.isLocalHomeomorph_subtypeMap hopen hopen
      (fun z hz => Work.FatouCoord.mapsTo_iterate_of_mapsTo hmap n hz) (hlocFn n)
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hclosed (fun y _ => hfin y)
    hloc.isLocalHomeomorphOn

/-! ## Fatou's theorem on the immediate basin -/

/-- **Fatou's theorem on parabolic cycles, immediate-basin form.**  Let `F` be a polynomial map of
degree `≥ 2` with a fixed point `z₀` of multiplier `1`, `fl` a Leau–Fatou flower of `F` at `z₀`
with its petal-image strip property, and `p₀` a point of the petal.  Then the *immediate* basin of
`z₀` — the connected component of the interior of the basin through `p₀` — contains a critical
point of `F`.

No simple-connectivity hypothesis on any basin is used: the argument is the covering/lifting one
of the design `NOTES_LEAD_mandelbar_gaps2.md` §2.1 (Q2, Q4–Q6). -/
theorem exists_isCriticalPoint_in_immBasin {F g : ℂ → ℂ} {z₀ : ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hfix : F z₀ = z₀)
    (h1 : deriv F z₀ = 1) (fl : Work.FatouParabolic.FlowerImageFix F g z₀) {p₀ : ℂ}
    (hp₀ : p₀ ∈ fl.Pa) :
    ∃ w ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀, deriv F w = 0 := by
  -- suppose the immediate basin is free of critical points
  by_contra hcon
  push_neg at hcon
  have hFdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  -- Q1: the structural facts about the immediate basin
  have hopen : IsOpen (immBasin F z₀ p₀) := exists_isOpen_immBasin F z₀ p₀
  have hPa_sub : fl.Pa ⊆ immBasin F z₀ p₀ := exists_pa_subset_immBasin fl hp₀
  have hmap : Set.MapsTo F (immBasin F z₀ p₀) (immBasin F z₀ p₀) :=
    exists_mapsTo_immBasin hF fl hp₀
  have hbdd : Bornology.IsBounded (immBasin F z₀ p₀) := exists_isBounded_immBasin (z₀ := z₀) hF
  -- Q2: every iterate is a covering of the critical-point-free immediate basin
  have hcover : ∀ n : ℕ, IsCoveringMap (immBasinIterate (immBasin F z₀ p₀) F hmap n) :=
    fun n => exists_isCoveringMap_immBasinIterate n hF hfix hopen hmap
      (connectedComponentIn_subset _ _) (exists_immBasin_closed_in_interior F z₀ p₀) hbdd hcon
  -- Q3: the canonical petal inverse supplies the hypothesis of the strip-lifting argument
  have hpetal : ∃ Φ : ℂ → ℂ, ∀ B : ℝ, 0 < B → ∃ C : ℝ,
      (∀ τ : ℂ, C < τ.re → |τ.im| < B →
        Φ τ ∈ immBasin F z₀ p₀ ∧
        F (Φ τ) = Φ (τ + 1) ∧ DifferentiableAt ℂ Φ τ) ∧
      Set.InjOn Φ (tailStrip C B) := by
    refine ⟨petalInv fl, fun B hB => ?_⟩
    obtain ⟨C, hC⟩ := petalInv_spec fl hFdiff hB
    refine ⟨C, ⟨fun τ h1' h2' => ?_, fun τ1 h1' τ2 h2' heq => ?_⟩⟩
    · obtain ⟨hmem, -, hFτ, hdτ⟩ := hC τ h1' h2'
      exact ⟨hPa_sub hmem, hFτ, hdτ⟩
    · have hφ1 := (hC τ1 h1'.1 h1'.2).2.1
      have hφ2 := (hC τ2 h2'.1 h2'.2).2.1
      rw [← hφ1, heq, hφ2]
  -- Q4–Q6: the bounded entire function obtained by lifting `Φ` contradicts Liouville
  exact Work.FatouParabolic.Core.ImmBasin.false_of_petalInverse_of_covering
    hFdiff hmap hcover hbdd hcon hpetal

end

end Work.FatouParabolic.Core
