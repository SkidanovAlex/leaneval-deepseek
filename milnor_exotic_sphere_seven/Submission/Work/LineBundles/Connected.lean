import Submission.Work.LineBundles.Basic
import Submission.Work.LineBundles.Divis
import Submission.Work.Cohomology.exists_smul_oneH
import Submission.Work.Thom.CohMap_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Additivity of `c₁` on the tensor product over a path connected base

`Work.LineBundles.tensorLine_c1_additive_connected`: for complex line bundles `L`, `M` over a
**path connected** base `B`, `c₁(L ⊗ M) = c₁(L) + c₁(M)`.

The proof uses the divisibility `Work.LineBundles.Divisibility` over the auxiliary base `B × B`
(where the `H⁰`-witness is a single integer, `Work.Cohomology.exists_smul_oneH`), the slice
`B × {b} ↪ B × B` (whose second factor pulls back to the pullback of `M` along the constant map to
`b`, which has vanishing `c₁` by `Work.LineBundles.c1_bundleComap_const`) and the diagonal
`Δ : B → B × B`.

This file also records the `H⁰`-module calculus used: the graded cup product is additive, vanishes
on `0`, and `H⁰(B;ℤ) ≅ ℤ` acts through the integer coefficients.
-/

namespace Work.LineBundles

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The `H⁰`-action through the unit -/

/-- The graded cup product is additive in its first variable. -/
theorem cup₀₂_add_left (a b : Work.Thom.Coh ℤ 0 B) (x : Work.Thom.Coh ℤ 2 B) :
    cup₀₂ B (a + b) x = cup₀₂ B a x + cup₀₂ B b x := by
  simp only [cup₀₂, Work.Whitney.cupChern_def]
  rw [Work.Cohomology.cupH'_add_left ℤ (Work.Whitney.ssB B) (2 * 0) (2 * 1) a b x]
  exact (Work.Thom.cohTransportLM _).map_add _ _

/-- The graded cup product vanishes on the zero class. -/
theorem cup₀₂_zero_left (x : Work.Thom.Coh ℤ 2 B) :
    cup₀₂ B (0 : Work.Thom.Coh ℤ 0 B) x = 0 := by
  simp only [cup₀₂, Work.Whitney.cupChern_def]
  rw [Work.Cohomology.cupH'_zero_left ℤ (Work.Whitney.ssB B) (2 * 0) (2 * 1) x]
  exact (Work.Thom.cohTransportLM _).map_zero

/-- The unit law of the graded cup product, in the form used here. -/
theorem cup₀₂_one_left (x : Work.Thom.Coh ℤ 2 B) :
    cup₀₂ B (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B))) x = x := by
  simp only [cup₀₂, Work.Whitney.cupChern_def]
  rw [Work.Cohomology.cupH'_one_left ℤ (Work.Whitney.ssB B) (2 * 1) x]
  rw [show (Nat.mul_add 2 0 1).symm = rfl from Subsingleton.elim _ _,
    Work.Thom.cohTransport_rfl]

/-- `cup₀₂` is odd in its first variable. -/
theorem cup₀₂_neg_left (w : Work.Thom.Coh ℤ 0 B) (x : Work.Thom.Coh ℤ 2 B) :
    cup₀₂ B (-w) x = -cup₀₂ B w x := by
  have h := cup₀₂_add_left w (-w) x
  rw [add_neg_cancel, cup₀₂_zero_left] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- `m ⌣ x = m • x` for an integer `m`. -/
theorem cup₀₂_zsmul_one (m : ℤ) (x : Work.Thom.Coh ℤ 2 B) :
    cup₀₂ B (m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B))) x = m • x := by
  induction m using Int.induction_on with
  | zero => rw [zero_zsmul, cup₀₂_zero_left, zero_zsmul]
  | succ n ih =>
      rw [add_one_zsmul, cup₀₂_add_left, ih, cup₀₂_one_left, add_one_zsmul]
  | pred n ih =>
      rw [show (-↑n - 1 : ℤ) = (-↑n) + (-1) from by ring, add_zsmul, cup₀₂_add_left, ih,
        neg_one_zsmul, cup₀₂_neg_left, cup₀₂_one_left,
        show -↑n • x + -x = (-↑n + -1) • x from by
          rw [add_zsmul, neg_zsmul, neg_one_zsmul]]

/-- The pullback of a scalar multiple of the unit class is the scalar multiple of the unit class. -/
theorem CohMap_zsmul_one {B' : Type} [TopologicalSpace B'] (f : C(B', B)) (m : ℤ) :
    (CohMap f ℤ 0).hom (m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)))
      = m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B')) := by
  rw [← Int.cast_smul_eq_zsmul (R := ℤ) m
    (Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)))]
  rw [LinearMap.map_smul, Work.Thom.CohMap_oneH]
  rw [Int.cast_smul_eq_zsmul]

/-- The graded cup product vanishes on the zero class in its second variable. -/
theorem cup₀₂_zero_right (x : Work.Thom.Coh ℤ 0 B) :
    cup₀₂ B x (0 : Work.Thom.Coh ℤ 2 B) = 0 := by
  simp only [cup₀₂, Work.Whitney.cupChern_def]
  rw [Work.Cohomology.cupH'_zero_right ℤ (Work.Whitney.ssB B) (2 * 0) (2 * 1) x]
  exact (Work.Thom.cohTransportLM _).map_zero

/-! ## The main result over a path connected base -/

/-- **Additivity of `c₁` on the tensor product of line bundles over a path connected base.** -/
theorem tensorLine_c1_additive_connected (hDiv : Divisibility)
    [PathConnectedSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : LineCore B ι₁) (M : LineCore B ι₂) :
    c1 (Work.Gen.tensorLine L M) = c1 L + c1 M := by
  obtain ⟨b⟩ : Nonempty B := inferInstance
  haveI : PathConnectedSpace (B × B) := inferInstance
  -- the auxiliary base `B × B` and the external tensor product
  set pr₁ : C(B × B, B) := ⟨Prod.fst, continuous_fst⟩ with hpr₁
  set pr₂ : C(B × B, B) := ⟨Prod.snd, continuous_snd⟩ with hpr₂
  set A : LineCore (B × B) ι₁ := bundleComap L pr₁ with hA
  set B' : LineCore (B × B) ι₂ := bundleComap M pr₂ with hB'
  obtain ⟨x, hx⟩ := hDiv A B'
  obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of (B × B)) x
  -- the relation over `B × B`, pulled back along a map `f : B → B × B`
  have hrel : ∀ (f : C(B, B × B)) (g : C(B, B)) (hf₁ : pr₁.comp f = ContinuousMap.id B)
      (hf₂ : pr₂.comp f = g),
      c1 (Work.Gen.tensorLine L (bundleComap M g))
        = c1 (bundleComap M g) + cup₀₂ B ((CohMap f ℤ 0).hom x) (c1 L) := by
    intro f g hf₁ hf₂
    have h1 : (CohMap f ℤ 2).hom (c1 (Work.Gen.tensorLine A B'))
        = c1 (Work.Gen.tensorLine L (bundleComap M g)) := by
      rw [c1_bundleComap (Work.Gen.tensorLine A B') f, Work.Gen.tensorLine_bundleComap,
        hA, hB', Work.Thom.bundleComap_comp, Work.Thom.bundleComap_comp, hf₁, hf₂,
        Work.Thom.bundleComap_id]
    have h2 : (CohMap f ℤ 2).hom (c1 B') = c1 (bundleComap M g) := by
      rw [c1_bundleComap B' f, hB', Work.Thom.bundleComap_comp, hf₂]
    have h3 : (CohMap f ℤ 2).hom (cup₀₂ (B × B) x (c1 A))
        = cup₀₂ B ((CohMap f ℤ 0).hom x) (c1 L) := by
      show (CohMap f ℤ (2 * (0 + 1))).hom (Work.Whitney.cupChern 0 1 x (c1 A))
        = Work.Whitney.cupChern 0 1 ((CohMap f ℤ (2 * 0)).hom x) (c1 L)
      rw [Work.Whitney.cupChern_CohMap f 0 1 x (c1 A), c1_bundleComap A f, hA,
        Work.Thom.bundleComap_comp, hf₁, Work.Thom.bundleComap_id]
    have h4 := congrArg (fun z => (CohMap f ℤ 2).hom z) hx
    rw [map_add, h1, h2, h3] at h4
    exact h4
  -- the pullback of the `H⁰`-witness is the same integer multiple of the unit
  have hf0 : ∀ (f : C(B, B × B)), (CohMap f ℤ 0).hom x
      = m • Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)) := fun f => by
    rw [hm, CohMap_zsmul_one f m]
  -- the diagonal and the slice
  set diag : C(B, B × B) := ⟨fun z => (z, z), continuous_id.prodMk continuous_id⟩ with hdiag
  set slic : C(B, B × B) := ⟨fun z => (z, b), continuous_id.prodMk continuous_const⟩ with hslic
  have hdiag₁ : pr₁.comp diag = ContinuousMap.id B := by ext z; rfl
  have hdiag₂ : pr₂.comp diag = ContinuousMap.id B := by ext z; rfl
  have hslic₁ : pr₁.comp slic = ContinuousMap.id B := by ext z; rfl
  have hslic₂ : pr₂.comp slic = ContinuousMap.const B b := by ext z; rfl
  have hdiagrel := hrel diag (ContinuousMap.id B) hdiag₁ hdiag₂
  have hslicrel := hrel slic (ContinuousMap.const B b) hslic₁ hslic₂
  rw [hf0 diag, cup₀₂_zsmul_one m (c1 L)] at hdiagrel
  rw [hf0 slic, cup₀₂_zsmul_one m (c1 L), c1_bundleComap_const M b, zero_add] at hslicrel
  -- the slice shows that the integer is `1` on the relevant class
  have hslice : c1 L = m • c1 L := by
    obtain ⟨z, hz⟩ := hDiv (bundleComap M (ContinuousMap.const B b)) L
    have hcup : cup₀₂ B z (c1 (bundleComap M (ContinuousMap.const B b))) = 0 := by
      rw [c1_bundleComap_const M b]
      exact cup₀₂_zero_right z
    have hz' : c1 (Work.Gen.tensorLine (bundleComap M (ContinuousMap.const B b)) L)
        = c1 L := by
      rw [hz, hcup, add_zero]
    have hswap : c1 (Work.Gen.tensorLine L (bundleComap M (ContinuousMap.const B b)))
        = c1 (Work.Gen.tensorLine (bundleComap M (ContinuousMap.const B b)) L) :=
      c1_tensorLine_comm L _
    calc c1 L = c1 (Work.Gen.tensorLine (bundleComap M (ContinuousMap.const B b)) L) := hz'.symm
      _ = c1 (Work.Gen.tensorLine L (bundleComap M (ContinuousMap.const B b))) := hswap.symm
      _ = m • c1 L := hslicrel
  -- conclusion
  have hm_eq : m • c1 L = c1 L := hslice.symm
  rw [hm_eq, add_comm] at hdiagrel
  exact hdiagrel

end

end Work.LineBundles
