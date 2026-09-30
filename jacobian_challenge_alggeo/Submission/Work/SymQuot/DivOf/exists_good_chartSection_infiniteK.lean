import Mathlib
import Submission.Work.SymQuot.DivOf.goodChartSectionAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.DivOf

open Work.CurveBasics
open Work.SpecLin (CurveFPt ptToPoint ptLeft)

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ} [NeZero n]
  [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]

/-! ## The compatibility of `secAlpha` with the structure maps

The pullback `C_F ⟶ C` of sections commutes with the structure constants. -/
theorem secAlpha_algebraMap (F : Type u) [Field F] [Algebra K F] (W : C.left.Opens)
    (hW : IsAffineOpen W) (c : K) :
    secAlpha C F W (algebraMap K Γ(C.left, W) c) = secConst C F W (algebraMap K F c) := by
  have hpb := Work.CurveBasics.BaseChange.isPullback_spec_affine (C := C) F W hW
  have hw := hpb.toCommSq.w
  have hring : CommRingCat.ofHom (algebraMap K ↑(C.left.presheaf.obj (Opposite.op W))) ≫
        Scheme.Hom.app (C.baseChangeFst F) W =
      CommRingCat.ofHom (algebraMap K F) ≫ CommRingCat.ofHom
        (algebraMap F ↑((C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F W)))) := by
    apply AlgebraicGeometry.Spec.map_injective
    simp only [Spec.map_comp]
    rw [show (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K F)) :
        AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) =
        Work.CurveBasics.Curve.specMap K F from rfl]
    exact hw
  have hhom := congrArg CommRingCat.Hom.hom hring
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at hhom
  have h4 := congrArg
    (fun (f : K →+* Γ(C.baseChangeLeft F, C.baseChangeFst F ⁻¹ᵁ W)) => f c) hhom
  rw [RingHom.comp_apply, RingHom.comp_apply] at h4
  rw [Work.SymQuot.DivOf.secAlpha_eq_app, Work.SymQuot.DivOf.secConst_apply]
  exact h4

/-! ## The main statement -/

theorem exists_good_chartSection_infiniteK {K : Type u} [Field K] [Infinite K]
    {C : Work.CurveBasics.Curve K} {n : ℕ}
    [NeZero n] [Work.SymQuot.CurveAffineCover C] {F : Type u} [Field F] [Algebra K F]
    {p : Work.SpecLin.FPt (Work.SymQuot.Sym C n) F}
    (d : Work.SymQuot.DivOf.ChartPt C n p) (x : Fin n → Work.SpecLin.CurveFPt C F)
    (h : Work.SymQuot.DivOf.LandsInChart d x)
    (hs : ∀ m : Fin n, Set.range (x m).left.base ⊆ (d.V : Set C.left)) (m₀ : Fin n)
    (hmem : Work.SpecLin.ptToPoint (x m₀) ∈ C.bcOpens F d.V) :
    ∃ b : C.left.presheaf.obj (Opposite.op d.V),
      Work.SymQuot.DivOf.secAlpha C F d.V b -
          Work.SymQuot.DivOf.secConst C F d.V (Work.SymQuot.DivOf.valAt d x h m₀ b) ∉
        (Work.SymQuot.DivOf.placeIdeal (C.baseChange F) (C.bcOpens F d.V)
          ⟨Work.SpecLin.ptToPoint (x m₀), Work.SpecLin.Points.ptToPoint_isClosed (x m₀)⟩ hmem) ^ 2
      ∧ ∀ m : Fin n, x m ≠ x m₀ →
          Work.SymQuot.DivOf.valAt d x h m b ≠ Work.SymQuot.DivOf.valAt d x h m₀ b := by
  classical
  -- A section with a simple zero at the point over `x m₀`.
  obtain ⟨b₀, hb₀⟩ := exists_delta_secAlpha_ne_zero d x h hs m₀ hmem
  -- The chart ring and the base-changed chart ring.
  let R := C.left.presheaf.obj (Opposite.op d.V)
  let S := (C.baseChange F).left.presheaf.obj (Opposite.op (C.bcOpens F d.V))
  let I : Ideal S := Pzero d (x m₀) hmem
  let Q := S ⧸ I ^ 2
  letI : Algebra K Q := ((algebraMap F Q).comp (algebraMap K F)).toAlgebra
  -- `valAt m` as a `K`-algebra homomorphism.
  let φ : Fin n → R →ₐ[K] F := fun m =>
    AlgHom.mk' (valAt d x h m) (fun c b => by
      rw [Algebra.smul_def, map_mul, valAt_algebraMap, Algebra.smul_def])
  -- The `K`-linear difference of two value maps.
  let g : Fin n → R →ₗ[K] F := fun m => (φ m).toLinearMap - (φ m₀).toLinearMap
  -- The `K`-linear "delta" functional measuring simple vanishing.
  let D : R →ₗ[K] Q :=
    { toFun := fun b => delta d (x m₀) hmem (secAlpha C F d.V b)
      map_add' := fun a b => by
        rw [map_add (secAlpha C F d.V), delta_add]
      map_smul' := fun c b => by
        show delta d (x m₀) hmem (secAlpha C F d.V (c • b))
          = c • delta d (x m₀) hmem (secAlpha C F d.V b)
        rw [Algebra.smul_def, map_mul,
          secAlpha_algebraMap (K := K) F d.V d.isAffineOpen_V c, Algebra.smul_def]
        rw [delta_mul, ev_secConst, delta_secConst, mul_zero, add_zero]
        have hker : algebraMap K Q c = Ideal.Quotient.mk (I ^ 2)
            (secConst C F d.V (algebraMap K F c)) := by
          show algebraMap F Q (algebraMap K F c)
            = Ideal.Quotient.mk (I ^ 2) (secConst C F d.V (algebraMap K F c))
          rw [← Ideal.Quotient.mk_algebraMap F (I ^ 2) (algebraMap K F c)]
          rfl
        rw [hker] }
  -- `D` does not vanish identically.
  have hDne : D ≠ 0 := by
    intro hD0
    have h : D b₀ = 0 := by
      simpa only [LinearMap.zero_apply] using congrArg (fun (f : R →ₗ[K] Q) => f b₀) hD0
    exact hb₀ h
  -- The difference maps do not vanish.
  have hgne : ∀ (m : Fin n), x m ≠ x m₀ → g m ≠ 0 := by
    intro m hm hg0
    obtain ⟨b, hb⟩ := exists_valAt_ne d x h hs hm
    refine hb ?_
    have hbz := congrArg (fun (f : R →ₗ[K] F) => f b) hg0
    change valAt d x h m b - valAt d x h m₀ b = 0 at hbz
    exact sub_eq_zero.mp hbz
  -- The bad sets are proper subspaces; a vector space over the infinite field `K`
  -- is not a finite union of proper subspaces.
  let p : ({m : Fin n // x m ≠ x m₀} ⊕ Unit) → Submodule K R := fun i =>
    match i with
    | Sum.inl m => LinearMap.ker (g m.1)
    | Sum.inr _ => LinearMap.ker D
  have hp : ∀ i, p i ≠ ⊤ := by
    rintro (⟨m, hm⟩ | ⟨⟩)
    · exact fun hh => hgne m hm (LinearMap.ker_eq_top.mp hh)
    · exact fun hh => hDne (LinearMap.ker_eq_top.mp hh)
  obtain ⟨b, hb⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨b, ?_, ?_⟩
  · -- The simple-vanishing condition.
    have hbD : D b ≠ 0 := fun h0 => hb (Sum.inr ()) (LinearMap.mem_ker.mpr h0)
    have hDval : D b = Ideal.Quotient.mk (I ^ 2)
        (secAlpha C F d.V b - secConst C F d.V (valAt d x h m₀ b)) := by
      show delta d (x m₀) hmem (secAlpha C F d.V b) = _
      rw [delta]
      congr 1
      rw [ev_congr d (x m₀) hmem
        (ptToPoint_mem_bcOpens d (x m₀) (hs m₀ ⟨_, rfl⟩)),
        ev_secAlpha d x h hs m₀ b]
    rw [hDval] at hbD
    intro hmemI
    exact hbD (Ideal.Quotient.eq_zero_iff_mem.mpr hmemI)
  · -- The value-separation condition.
    intro m hm
    have hbm : b ∉ p (Sum.inl ⟨m, hm⟩) := hb (Sum.inl ⟨m, hm⟩)
    have hgm : g m b ≠ 0 := fun h0 => hbm (LinearMap.mem_ker.mpr h0)
    have hsub : valAt d x h m b - valAt d x h m₀ b ≠ 0 := by
      change valAt d x h m b - valAt d x h m₀ b ≠ 0 at hgm
      exact hgm
    exact sub_ne_zero.mp hsub

end Work.SymQuot.DivOf
