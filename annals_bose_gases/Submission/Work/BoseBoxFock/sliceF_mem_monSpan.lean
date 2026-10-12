import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sectorSliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceF_mem_monSpan` — the sector slice lies in the mode-monomial span

The sector slice `sliceF e S Φ y` of `sectorSliceDefs` is the `S`-sector part of a state `Φ`,
read as a function of the `S`-configuration `u`, with the complementary slots frozen at `y`:

    `sliceF e S Φ y u = slotExact e S Φ (pairCoord S u y)`.

Because the projection kernel `PV e x z = Σ_l e l x * star (e l z)` is *linear in each of its
two arguments separately*, expanding the finite product `Π_{i ∈ T} PV e (x i) (z i)` occurring
in the sector sum turns the slice into a finite sum of scalar multiples of the tensor monomials
`u ↦ Π_{i : Fin S.card} e (l i) (u i)`.  This module proves that membership.

The proof has three ingredients:

* `prod_PV_eq_sum` — the expansion of a product of `PV`-kernels into a sum over multi-indices;
* `prod_subtype_sdiff` — the splitting of a product over the subtype `↥T` into the parts over
  `↥S` and `↥(T \ S)` when `S ⊆ T`;
* `integrable_pairG` — the integrand produced by the expansion is continuous with compact
  support, hence integrable, which allows the finite sum to be pulled out of the fibre integral
  (`MeasureTheory.integral_finsetSum`).

The bulk of the argument is the pointwise identity `slotProj_pairCoord_eq_sum`: the dependence
of `slotProj e T Φ (pairCoord S u y)` on `u` is *only* through the `S`-slots, and each of those
appears as a single mode factor `e (L i) (u i)`, the complementary slots being absorbed into the
integral over the fibre variables `z`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Products over a subtype, and over a subtype and its complement -/

/-- A product over the subtype `↥T` of a Finset is the product over `T` of the corresponding
proof-dependent function (with the value `1` off `T`, which is irrelevant on `T`). -/
lemma prod_subtype_eq_prod {n : ℕ} {β : Type*} [CommMonoid β] (T : Finset (Fin n))
    (g : (i : Fin n) → i ∈ T → β) :
    (∏ i : {i // i ∈ T}, g i.1 i.2) = ∏ i ∈ T, (if h : i ∈ T then g i h else 1) := by
  rw [← Finset.prod_attach T (f := fun i => if h : i ∈ T then g i h else 1)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [dif_pos i.2]

/-- A product over the subtype `↥T` splits, for `S ⊆ T`, into the product over `↥S` and the
product over `↥(T \ S)`. -/
lemma prod_subtype_sdiff {m n : ℕ} (e : Fin m → Ω → ℂ) {S T : Finset (Fin n)} (hST : S ⊆ T)
    (L : {i // i ∈ T} → Fin m) (x : Fin n → Ω) :
    (∏ i : {i // i ∈ T}, e (L i) (x i.1)) =
      (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (x i.1)) *
        (∏ i : {i // i ∈ T \ S}, e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) (x i.1)) := by
  rw [prod_subtype_eq_prod T (fun i h => e (L ⟨i, h⟩) (x i)),
      prod_subtype_eq_prod S (fun i h => e (L ⟨i, hST h⟩) (x i)),
      prod_subtype_eq_prod (T \ S) (fun i h => e (L ⟨i, (Finset.mem_sdiff.mp h).1⟩) (x i))]
  have hS : (∏ i ∈ S, (if h : i ∈ S then e (L ⟨i, hST h⟩) (x i) else 1))
      = ∏ i ∈ S, (if h : i ∈ T then e (L ⟨i, h⟩) (x i) else 1) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [dif_pos hi, dif_pos (hST hi)]
  have hTS : (∏ i ∈ T \ S, (if h : i ∈ T \ S then e (L ⟨i, (Finset.mem_sdiff.mp h).1⟩) (x i) else 1))
      = ∏ i ∈ T \ S, (if h : i ∈ T then e (L ⟨i, h⟩) (x i) else 1) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [dif_pos hi, dif_pos (Finset.mem_sdiff.mp hi).1]
  rw [hS, hTS, mul_comm]
  exact (Finset.prod_sdiff hST).symm

/-! ## 2. Expanding a product of `PV` kernels -/

/-- The product of the projection kernels `PV e (a i) (b i)` expands into the sum over
multi-indices `L : ι → Fin m` of the products of the individual mode factors. -/
lemma prod_PV_eq_sum {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin m → Ω → ℂ) (a b : ι → Ω) :
    ∏ i, PV e (a i) (b i) = ∑ L : ι → Fin m, ∏ i, (e (L i) (a i) * star (e (L i) (b i))) := by
  simp only [PV]
  rw [Finset.prod_univ_sum]
  simp

/-! ## 3. The constant part of an expanded summand, and its integrability -/

/-- The `u`-independent part of the summand indexed by the multi-index `L` in the expansion of
`slotProj e T Φ (pairCoord S u y)`: the `y`-factors of the slots in `T \ S`, the conjugates of
the fibre variables `z`, and the state evaluated at the `y`-complemented configuration. -/
def pairG {m n : ℕ} (e : Fin m → Ω → ℂ) (S T : Finset (Fin n)) (hST : S ⊆ T)
    (Φ : (Fin n → Ω) → ℂ) (y : {i // i ∉ S} → Ω) (L : {i // i ∈ T} → Fin m)
    (z : {i // i ∈ T} → Ω) : ℂ :=
  (∏ i : {i // i ∈ T \ S},
      e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) (y ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩)) *
    (∏ i : {i // i ∈ T}, star (e (L i) (z i))) *
    Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩)

/-- The fibre integral of `pairG`: the coefficient of the monomial `Π_{i ∈ S} e (L i) (u i)`. -/
def pairConst {m n : ℕ} (e : Fin m → Ω → ℂ) (S T : Finset (Fin n)) (hST : S ⊆ T)
    (Φ : (Fin n → Ω) → ℂ) (y : {i // i ∉ S} → Ω) (L : {i // i ∈ T} → Fin m) : ℂ :=
  ∫ z : {i // i ∈ T} → Ω, pairG e S T hST Φ y L z

/-- `pairG` is continuous with compact support (the compact support coming from the product of
the conjugated modes), hence integrable. -/
lemma integrable_pairG {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (y : {i // i ∉ S} → Ω) (L : {i // i ∈ T} → Fin m) :
    Integrable (pairG e S T hST Φ y L) := by
  classical
  have hcontΦ : Continuous (fun z : {i // i ∈ T} → Ω =>
      Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩)) := by
    refine hΦ.comp (continuous_pi (fun j => ?_))
    by_cases h : j ∈ T
    · have hfun : (fun a : {i // i ∈ T} → Ω =>
          if h' : j ∈ T then a ⟨j, h'⟩ else y ⟨j, fun hj => h' (hST hj)⟩) = fun a => a ⟨j, h⟩ := by
        funext a
        rw [dif_pos h]
      rw [hfun]
      exact continuous_apply (⟨j, h⟩ : {i : Fin n // i ∈ T})
    · have hfun : (fun a : {i // i ∈ T} → Ω =>
          if h' : j ∈ T then a ⟨j, h'⟩ else y ⟨j, fun hj => h' (hST hj)⟩)
            = fun _ => y ⟨j, fun hj => h (hST hj)⟩ := by
        funext a
        rw [dif_neg h]
      rw [hfun]
      exact continuous_const
  have hcontStar : Continuous
      (fun z : {i // i ∈ T} → Ω => ∏ i : {i // i ∈ T}, star (e (L i) (z i))) :=
    continuous_finsetProd _ (fun i _ => (he (L i)).star.comp (continuous_apply i))
  have hcsStar : HasCompactSupport
      (fun z : {i // i ∈ T} → Ω => ∏ i : {i // i ∈ T}, star (e (L i) (z i))) := by
    refine HasCompactSupport.intro
      (isCompact_univ_pi (fun i => (hec (L i)).isCompact)) (fun z hz => ?_)
    rw [Set.mem_univ_pi] at hz
    push Not at hz
    obtain ⟨i, hi⟩ := hz
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [image_eq_zero_of_notMem_tsupport hi, star_zero]
  have hcont : Continuous (pairG e S T hST Φ y L) := by
    unfold pairG
    exact (continuous_const.mul hcontStar).mul hcontΦ
  have hcs : HasCompactSupport (pairG e S T hST Φ y L) := by
    unfold pairG
    exact (hcsStar.mul_left (f := fun _ : {i // i ∈ T} → Ω =>
      ∏ i : {i // i ∈ T \ S},
        e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) (y ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩))).mul_right
  exact hcont.integrable_of_hasCompactSupport hcs

/-! ## 4. The pointwise expansion of a `slotProj` slice -/

/-- **The key computation.**  For `S ⊆ T`, the value of `slotProj e T Φ` at a configuration
`pairCoord S u y` which agrees with `u` on `S` and with `y` outside `S` depends on `u` only
through the monomials `Π_{i ∈ S} e (L i) (u i)`, with coefficients given by the fibre integral
`pairConst`. -/
lemma slotProj_pairCoord_eq_sum {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (y : {i // i ∉ S} → Ω) (u : {i // i ∈ S} → Ω) :
    slotProj e T Φ (pairCoord S u y) =
      ∑ L : {i // i ∈ T} → Fin m,
        (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) * pairConst e S T hST Φ y L := by
  have hI : (fun z : {i // i ∈ T} → Ω =>
      (∏ i : {i // i ∈ T}, PV e (pairCoord S u y i.1) (z i)) *
        Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else pairCoord S u y j))
      = fun z => ∑ L : {i // i ∈ T} → Fin m,
          (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) * pairG e S T hST Φ y L z := by
    funext z
    rw [prod_PV_eq_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [Finset.prod_mul_distrib]
    rw [prod_subtype_sdiff (e := e) hST L (pairCoord S u y)]
    have hSp : (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (pairCoord S u y i.1))
        = ∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [pairCoord_mem S u y i.1 i.2]
    have hTSp : (∏ i : {i // i ∈ T \ S},
          e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) (pairCoord S u y i.1))
        = ∏ i : {i // i ∈ T \ S},
          e (L ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩) (y ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [pairCoord_notMem S u y i.1 (Finset.mem_sdiff.mp i.2).2]
    have hPhi : Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else pairCoord S u y j)
        = Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else y ⟨j, fun hj => h (hST hj)⟩) := by
      congr 1
      funext j
      by_cases h : j ∈ T
      · simp [h]
      · simp only [dif_neg h]
        exact pairCoord_notMem S u y j (fun hj => h (hST hj))
    rw [hSp, hTSp, hPhi]
    simp only [pairG]
    ring
  calc slotProj e T Φ (pairCoord S u y)
      = ∫ z : {i // i ∈ T} → Ω, (∏ i : {i // i ∈ T}, PV e (pairCoord S u y i.1) (z i)) *
          Φ (fun j => if h : j ∈ T then z ⟨j, h⟩ else pairCoord S u y j) := by
          rw [slotProj]
    _ = ∫ z : {i // i ∈ T} → Ω, ∑ L : {i // i ∈ T} → Fin m,
          (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) * pairG e S T hST Φ y L z := by
          rw [hI]
    _ = ∑ L : {i // i ∈ T} → Fin m, ∫ z : {i // i ∈ T} → Ω,
          (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) * pairG e S T hST Φ y L z := by
        rw [MeasureTheory.integral_finsetSum]
        intro L _
        exact (integrable_pairG e he hec Φ hΦ hΦc hST y L).const_mul _
    _ = ∑ L : {i // i ∈ T} → Fin m,
        (∏ i : {i // i ∈ S}, e (L ⟨i.1, hST i.2⟩) (u i)) * pairConst e S T hST Φ y L := by
        refine Finset.sum_congr rfl (fun L _ => ?_)
        rw [MeasureTheory.integral_const_mul]
        rfl

/-- The `T`-summand of the sector decomposition of the slice lies in the span of the mode
monomials. -/
lemma slotProj_pairCoord_mem_span {m n : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (Φ : (Fin n → Ω) → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    {S T : Finset (Fin n)} (hST : S ⊆ T) (y : {i // i ∉ S} → Ω) :
    (fun u : {i // i ∈ S} → Ω => slotProj e T Φ (pairCoord S u y)) ∈
      Submodule.span ℂ (Set.range (fun M : {i // i ∈ S} → Fin m =>
        fun u : {i // i ∈ S} → Ω => ∏ i, e (M i) (u i))) := by
  have hpt : (fun u : {i // i ∈ S} → Ω => slotProj e T Φ (pairCoord S u y))
      = ∑ L : {i // i ∈ T} → Fin m, (pairConst e S T hST Φ y L) •
          (fun u : {i // i ∈ S} → Ω => ∏ i, e (L ⟨i.1, hST i.2⟩) (u i)) := by
    funext u
    rw [slotProj_pairCoord_eq_sum e he hec Φ hΦ hΦc hST y u]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun L _ => by simp [smul_eq_mul, mul_comm])
  rw [hpt]
  refine Submodule.sum_mem _ (fun L _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨fun i => L ⟨i.1, hST i.2⟩, rfl⟩

/-- **The sector slice lies in the span of the mode monomials.**  The slice
`sliceF e S Φ y` of the `S`-sector of `Φ` at the complement configuration `y` is a finite linear
combination of the tensor monomials `x ↦ Π_{i : Fin S.card} e (l i) (x i)`. -/
theorem sliceF_mem_monSpan {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.sliceF e S Φ y ∈ Submodule.span ℂ (Set.range (fun l : Fin S.card → Fin m =>
        fun x : Fin S.card → EuclideanSpace ℝ (Fin 3) => ∏ i, e (l i) (x i))) := by
  classical
  have hSlice : sectorSlice e S Φ y ∈
      Submodule.span ℂ (Set.range (fun M : {i // i ∈ S} → Fin m =>
        fun u : {i // i ∈ S} → Ω => ∏ i, e (M i) (u i))) := by
    have hEq : sectorSlice e S Φ y =
        ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
          ((-1 : ℂ) ^ (T.card - S.card)) • (fun u : {i // i ∈ S} → Ω =>
            slotProj e T Φ (pairCoord S u y)) := by
      funext u
      simp only [sectorSlice, slotExact, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    refine Submodule.sum_mem _ (fun T hT => ?_)
    rw [Finset.mem_filter] at hT
    exact Submodule.smul_mem _ _ (slotProj_pairCoord_mem_span e he hec Φ hΦ hΦc hT.2 y)
  have key : ∀ f ∈ (Submodule.span ℂ (Set.range (fun M : {i // i ∈ S} → Fin m =>
        fun u : {i // i ∈ S} → Ω => ∏ i, e (M i) (u i)))),
      (fun u' : Fin S.card → Ω => f (fun i => u' (S.equivFin i))) ∈
        Submodule.span ℂ (Set.range (fun l : Fin S.card → Fin m =>
          fun x : Fin S.card → Ω => ∏ i, e (l i) (x i))) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨M, rfl⟩ := hf
        refine Submodule.subset_span ⟨fun j => M (S.equivFin.symm j), ?_⟩
        funext u'
        exact (Fintype.prod_equiv S.equivFin _ _
          (fun i => by simp)).symm
    | zero => exact Submodule.zero_mem _
    | add f g _ _ ihf ihg =>
        have hfun : (fun u' : Fin S.card → Ω => (f + g) (fun i => u' (S.equivFin i)))
            = (fun u' : Fin S.card → Ω => f (fun i => u' (S.equivFin i))) +
              (fun u' : Fin S.card → Ω => g (fun i => u' (S.equivFin i))) := by
          funext u'
          simp
        rw [hfun]
        exact Submodule.add_mem _ ihf ihg
    | smul c f _ ihf =>
        have hfun : (fun u' : Fin S.card → Ω => (c • f) (fun i => u' (S.equivFin i)))
            = c • (fun u' : Fin S.card → Ω => f (fun i => u' (S.equivFin i))) := by
          funext u'
          simp
        rw [hfun]
        exact Submodule.smul_mem _ _ ihf
  exact key (sectorSlice e S Φ y) hSlice

end Work.BoseBoxFock
