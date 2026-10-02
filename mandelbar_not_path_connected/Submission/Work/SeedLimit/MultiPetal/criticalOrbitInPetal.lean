/-
# `Work.SeedLimit.MultiPetal.criticalOrbitInPetal`

Given a polynomial map `F` of degree `≥ 2` with `F 0 = 0` and `F'(0) = 1`, and an attracting
petal `Pa` of the parabolic fixed point `0` carrying an injective holomorphic Fatou coordinate
`φa` (Abel equation, image exhausting the tail of every horizontal strip), some critical point of
`F` has an orbit which enters `Pa`.

The proof is the petal/Liouville argument of `Submission/Work/FatouParabolic/` run on the
**saturation** `B = ⋃_n F^{-n}(Pa)` of the petal (rather than on the immediate basin): if `B`
contained no critical point, every iterate `F^[n] : B → B` would be a covering map; lifting the
inverse Fatou coordinate `Φ = φa⁻¹` of the petal through those coverings produces a bounded entire
function which is injective on a tail strip, contradicting Liouville.  The critical point so found
lies in `B`, i.e. some iterate of it lies in `Pa`.

The general-domain version of the Liouville step is `false_of_petalInverse_of_covering_general` in
`Submission/Work/SeedLimit/MultiPetal/GeneralLiouville.lean`.
-/
import Mathlib
import Submission.Work.SeedLimit.MultiPetal.GeneralLiouville
import Submission.Work.FatouParabolic.All
import Submission.Work.SeedDyn.isLocalHomeomorph_subtypeMap
import Submission.Work.ELRig.deriv_ne_zero_of_injOn
import Submission.Work.FatouCoord.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.SeedLimit.MultiPetal

noncomputable section

/-! ## The saturation of a petal -/

/-- The **saturation** of `Pa` under `F`: the points of `ℂ` some iterate of which lies in `Pa`. -/
def satPa (F : ℂ → ℂ) (Pa : Set ℂ) : Set ℂ := {z : ℂ | ∃ n : ℕ, (F^[n]) z ∈ Pa}

@[simp] theorem mem_satPa {F : ℂ → ℂ} {Pa : Set ℂ} {z : ℂ} :
    z ∈ satPa F Pa ↔ ∃ n : ℕ, (F^[n]) z ∈ Pa := Iff.rfl

theorem satPa_isOpen {F : ℂ → ℂ} {Pa : Set ℂ} (hF : Continuous F) (hPa : IsOpen Pa) :
    IsOpen (satPa F Pa) := by
  have h : satPa F Pa = ⋃ n : ℕ, (F^[n]) ⁻¹' Pa := by
    ext z
    simp only [mem_satPa, Set.mem_iUnion, Set.mem_preimage]
  rw [h]
  exact isOpen_iUnion (fun n => hPa.preimage (hF.iterate n))

/-- `F` maps the saturation of `Pa` into itself when `F (Pa) ⊆ Pa`. -/
theorem satPa_mapsTo {F : ℂ → ℂ} {Pa : Set ℂ} (hmap : MapsTo F Pa Pa) :
    MapsTo F (satPa F Pa) (satPa F Pa) := by
  intro z hz
  obtain ⟨n, hn⟩ := mem_satPa.mp hz
  refine mem_satPa.mpr ⟨n, ?_⟩
  have h : (F^[n]) (F z) = F ((F^[n]) z) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  rw [h]
  exact hmap hn

/-- The saturation is backwards invariant: a preimage of a point of the saturation lies in it. -/
theorem satPa_preimage {F : ℂ → ℂ} {Pa : Set ℂ} :
    ∀ x : ℂ, F x ∈ satPa F Pa → x ∈ satPa F Pa := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_satPa.mp hx
  refine mem_satPa.mpr ⟨n + 1, ?_⟩
  have h : (F^[n + 1]) x = (F^[n]) (F x) := Function.iterate_succ_apply F n x
  rw [h]
  exact hn

/-- The saturation is backwards invariant under every iterate of `F`. -/
theorem satPa_preimage_iterate {F : ℂ → ℂ} {Pa : Set ℂ} :
    ∀ (n : ℕ) (x : ℂ), (F^[n]) x ∈ satPa F Pa → x ∈ satPa F Pa := by
  intro n x hx
  obtain ⟨m, hm⟩ := mem_satPa.mp hx
  refine mem_satPa.mpr ⟨m + n, ?_⟩
  have h : (F^[m + n]) x = (F^[m]) ((F^[n]) x) := Function.iterate_add_apply F m n x
  rw [h]
  exact hm

/-- The saturation is contained in the basin of `0`. -/
theorem satPa_subset_basin {F : ℂ → ℂ} {Pa : Set ℂ}
    (htend : ∀ z ∈ Pa, Tendsto (fun n : ℕ => (F^[n]) z) atTop (nhds 0)) :
    satPa F Pa ⊆ Work.FatouParabolic.basin F 0 := by
  intro z hz
  obtain ⟨n, hn⟩ := mem_satPa.mp hz
  rw [Work.FatouParabolic.mem_basin]
  have h1 : Tendsto (fun k : ℕ => (F^[k]) ((F^[n]) z)) atTop (nhds 0) := htend _ hn
  have h2 : (fun k : ℕ => (F^[k]) ((F^[n]) z)) = fun k : ℕ => (F^[k + n]) z := by
    funext k; rw [Function.iterate_add_apply]
  rw [h2] at h1
  exact (Filter.tendsto_add_atTop_iff_nat (f := fun k : ℕ => (F^[k]) z) n).mp h1

/-- The saturation of an attracting petal of a polynomial of degree `≥ 2` is bounded. -/
theorem satPa_isBounded {F : ℂ → ℂ} {Pa : Set ℂ}
    (htend : ∀ z ∈ Pa, Tendsto (fun n : ℕ => (F^[n]) z) atTop (nhds 0))
    (hesc : Work.FatouParabolic.BasinEscape F) :
    Bornology.IsBounded (satPa F Pa) := by
  obtain ⟨R, hRpos, hR⟩ := hesc
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (Work.FatouParabolic.Core.norm_lt_of_mem_basin_of_escape hRpos hR
    (satPa_subset_basin htend hz))

/-- `0` is not in an attracting petal with an Abel coordinate (`φa (F 0) = φa 0 + 1`). -/
theorem zero_notMem_Pa {F : ℂ → ℂ} {Pa : Set ℂ} {φa : ℂ → ℂ}
    (h0 : F 0 = 0) (habel : ∀ z ∈ Pa, φa (F z) = φa z + 1) : (0 : ℂ) ∉ Pa := by
  intro hmem
  have h := habel 0 hmem
  rw [h0] at h
  have hh : (0 : ℂ) = 1 := by
    have := congrArg (fun x : ℂ => x - φa 0) h
    simpa using this
  exact zero_ne_one hh

/-! ## A closed self-map of a subtype -/

/-- **A closed map which is saturated along `P` restricts to a closed self-map of `Ω`.** -/
private theorem isClosedMap_of_coe_eq {Ω P : Set ℂ} {G : ℂ → ℂ} {g : ↥Ω → ↥Ω}
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

/-! ## The iterates of `F` are coverings of a critical-point-free saturation -/

/-- **Every iterate `F^[n] : B → B` of a critical-point-free saturation is a covering map.**

* the local homeomorphism comes from `deriv F ≠ 0` on `B` and openness of `B`;
* `F^[n] : B → B` is closed (the saturation lemma above, with `P = B`);
* its fibres are finite, being contained in the fibres of the polynomial `F^[n]`. -/
theorem isCoveringMap_iterate_satPa {F : ℂ → ℂ} {Pa : Set ℂ}
    (hF : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F) (hPa : IsOpen Pa)
    (hmapB : MapsTo F (satPa F Pa) (satPa F Pa)) (n : ℕ)
    (hnocrit : ∀ w ∈ satPa F Pa, deriv F w ≠ 0) :
    IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate (satPa F Pa) F hmapB n) := by
  have hFdiff : Differentiable ℂ F := Work.FatouParabolic.Poly.isPolynomialMap_differentiable hF
  have hesc : Work.FatouParabolic.BasinEscape F :=
    Work.FatouParabolic.Poly.isPolynomialMap_basinEscape hF
  have hproperF : IsProperMap F :=
    Work.FatouParabolic.Core.isProperMap_of_escapeBound hFdiff.continuous hesc
  have hclosedN : IsClosedMap (F^[n]) := by
    induction n with
    | zero => rw [Function.iterate_zero]; exact IsClosedMap.id
    | succ k ih => rw [Function.iterate_succ']; exact hproperF.isClosedMap.comp ih
  have hopen : IsOpen (satPa F Pa) := satPa_isOpen hFdiff.continuous hPa
  have hclosed : IsClosedMap
      (Work.FatouParabolic.Core.immBasinIterate (satPa F Pa) F hmapB n) :=
    isClosedMap_of_coe_eq hclosedN (fun x => Work.FatouParabolic.Core.immBasinIterate_coe x)
      (fun x hx => satPa_preimage_iterate n x hx) (fun x hx => hx) (fun x hx _ => hx)
  have hfin : ∀ y : ↥(satPa F Pa),
      (Work.FatouParabolic.Core.immBasinIterate (satPa F Pa) F hmapB n ⁻¹' {y}).Finite := by
    intro y
    have hfiber : ((F^[n]) ⁻¹' {y.1}).Finite :=
      Work.FatouParabolic.Core.exists_finite_fiber_iterate_of_isPolynomialMapOfDegreeAtLeastTwo
        hF n y.1
    refine (hfiber.preimage Subtype.val_injective.injOn).subset ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
    rw [← hx, Work.FatouParabolic.Core.immBasinIterate_coe]
  have hlocF : IsLocalHomeomorphOn F (satPa F Pa) :=
    Work.FatouParabolic.Core.isLocalHomeomorphOn_of_deriv_ne_zero hFdiff hnocrit
  have hlocFn : ∀ m : ℕ, IsLocalHomeomorphOn (F^[m]) (satPa F Pa) := by
    intro m
    induction m with
    | zero =>
        simpa [Function.iterate_zero] using
          (Homeomorph.refl ℂ).isLocalHomeomorph.isLocalHomeomorphOn (s := satPa F Pa)
    | succ k ih =>
        rw [Function.iterate_succ']
        exact hlocF.comp ih (Work.FatouCoord.mapsTo_iterate_of_mapsTo hmapB k)
  have hloc : IsLocalHomeomorph
      (Work.FatouParabolic.Core.immBasinIterate (satPa F Pa) F hmapB n) :=
    Work.SeedDyn.isLocalHomeomorph_subtypeMap hopen hopen
      (fun z hz => Work.FatouCoord.mapsTo_iterate_of_mapsTo hmapB n hz) (hlocFn n)
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hclosed (fun y _ => hfin y)
    hloc.isLocalHomeomorphOn

/-! ## The main theorem -/

theorem criticalOrbitInPetal (F : ℂ → ℂ)
    (hF : ∃ P : Polynomial ℂ, 2 ≤ P.natDegree ∧ ∀ z : ℂ, F z = P.eval z)
    (h0 : F 0 = 0) (h1 : deriv F 0 = 1)
    (Pa : Set ℂ) (φa : ℂ → ℂ)
    (hisOpen : IsOpen Pa) (hne : Pa.Nonempty) (hmap : Set.MapsTo F Pa Pa)
    (htend : ∀ z ∈ Pa, Filter.Tendsto (fun n : ℕ => (F^[n]) z) Filter.atTop (nhds 0))
    (hdiff : DifferentiableOn ℂ φa Pa) (hinj : Set.InjOn φa Pa)
    (habel : ∀ z ∈ Pa, φa (F z) = φa z + 1)
    (hstrip : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B → ∃ z ∈ Pa, φa z = τ)
    (hpre : IsPreconnected Pa) :
    ∃ w : ℂ, deriv F w = 0 ∧ ∃ K : ℕ, (F^[K]) w ∈ Pa := by
  have hFpoly : Work.FatouParabolic.IsPolynomialMapOfDegreeAtLeastTwo F := hF
  have hFdiff : Differentiable ℂ F :=
    Work.FatouParabolic.Poly.isPolynomialMap_differentiable hFpoly
  have hesc : Work.FatouParabolic.BasinEscape F :=
    Work.FatouParabolic.Poly.isPolynomialMap_basinEscape hFpoly
  have hmapB : MapsTo F (satPa F Pa) (satPa F Pa) := satPa_mapsTo hmap
  have hbdd : Bornology.IsBounded (satPa F Pa) := satPa_isBounded htend hesc
  by_contra hcon
  -- the negation of the conclusion: no critical orbit enters `Pa`
  have hnocrit : ∀ w ∈ satPa F Pa, deriv F w ≠ 0 := by
    intro w hw hdw
    obtain ⟨K, hK⟩ := mem_satPa.mp hw
    exact hcon ⟨w, hdw, K, hK⟩
  -- every iterate is a covering of the saturation
  have hcover : ∀ n : ℕ, IsCoveringMap
      (Work.FatouParabolic.Core.immBasinIterate (satPa F Pa) F hmapB n) :=
    fun n => isCoveringMap_iterate_satPa hFpoly hisOpen hmapB n hnocrit
  -- the inverse Fatou coordinate of the petal on the tail of every horizontal strip
  have hpetal : ∃ Φ : ℂ → ℂ, ∀ H : ℝ, 0 < H → ∃ C : ℝ,
      StripPropG (satPa F Pa) F Φ C H ∧
      Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip C H) := by
    refine ⟨Function.invFunOn φa Pa, fun H hH => ?_⟩
    obtain ⟨C, hC⟩ := hstrip H (le_of_lt hH)
    refine ⟨C, ?_, ?_⟩
    · intro τ hτre hτim
      have hex : ∃ z ∈ Pa, φa z = τ := hC τ hτre (le_of_lt hτim)
      have hmem : Function.invFunOn φa Pa τ ∈ Pa := Function.invFunOn_mem hex
      have hval : φa (Function.invFunOn φa Pa τ) = τ := Function.invFunOn_eq hex
      have hex1 : ∃ z ∈ Pa, φa z = τ + 1 :=
        hC (τ + 1) (by simp only [Complex.add_re, Complex.one_re]; linarith)
          (by simpa using le_of_lt hτim)
      have hmem1 : Function.invFunOn φa Pa (τ + 1) ∈ Pa := Function.invFunOn_mem hex1
      have hval1 : φa (Function.invFunOn φa Pa (τ + 1)) = τ + 1 := Function.invFunOn_eq hex1
      refine ⟨mem_satPa.mpr ⟨0, by simpa using hmem⟩, ?_, ?_⟩
      · have hmaps : F (Function.invFunOn φa Pa τ) ∈ Pa := hmap hmem
        have habel' : φa (F (Function.invFunOn φa Pa τ))
            = φa (Function.invFunOn φa Pa τ) + 1 := habel _ hmem
        refine hinj hmaps hmem1 ?_
        rw [habel', hval, hval1]
      · have hmem_nhds : Pa ∈ 𝓝 (Function.invFunOn φa Pa τ) := hisOpen.mem_nhds hmem
        have han : AnalyticAt ℂ φa (Function.invFunOn φa Pa τ) :=
          (hdiff.analyticOn hisOpen).analyticAt hmem_nhds
        have hsd : HasStrictDerivAt φa (deriv φa (Function.invFunOn φa Pa τ))
            (Function.invFunOn φa Pa τ) := han.hasStrictDerivAt
        have hne : deriv φa (Function.invFunOn φa Pa τ) ≠ 0 :=
          Work.ELRig.deriv_ne_zero_of_injOn hdiff hisOpen hinj hmem
        have hev : ∀ᶠ x in 𝓝 (Function.invFunOn φa Pa τ),
            Function.invFunOn φa Pa (φa x) = x := by
          filter_upwards [hmem_nhds] with x hx
          have hex' : ∃ z ∈ Pa, φa z = φa x := ⟨x, hx, rfl⟩
          exact hinj (Function.invFunOn_mem hex') hx (Function.invFunOn_eq hex')
        have hsds := hsd.to_local_left_inverse hne hev
        have hd : DifferentiableAt ℂ (Function.invFunOn φa Pa)
            (φa (Function.invFunOn φa Pa τ)) := hsds.hasDerivAt.differentiableAt
        rwa [hval] at hd
    · intro τ₁ hτ₁ τ₂ hτ₂ heq
      have hex1 : ∃ z ∈ Pa, φa z = τ₁ := hC τ₁ hτ₁.1 (le_of_lt hτ₁.2)
      have hex2 : ∃ z ∈ Pa, φa z = τ₂ := hC τ₂ hτ₂.1 (le_of_lt hτ₂.2)
      have h1 : φa (Function.invFunOn φa Pa τ₁) = τ₁ := Function.invFunOn_eq hex1
      have h2 : φa (Function.invFunOn φa Pa τ₂) = τ₂ := Function.invFunOn_eq hex2
      calc τ₁ = φa (Function.invFunOn φa Pa τ₁) := h1.symm
        _ = φa (Function.invFunOn φa Pa τ₂) := by rw [heq]
        _ = τ₂ := h2
  exact false_of_petalInverse_of_covering_general hFdiff hmapB hcover hbdd hnocrit hpetal

end

end Work.SeedLimit.MultiPetal
