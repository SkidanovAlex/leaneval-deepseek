import Mathlib
import Submission.Work.ThomBordism.h0SignUnit
import Submission.Work.ThomBordism.localThom_unit_relation
import Submission.Work.ThomBordism.span_localThom_singleton

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000


/-!
# The coefficient of a normalized/chart-normalized Thom class is `±1`

Let `Z → B` be a real bundle of rank `n` and `T` a Thom class of `Z`.  Suppose that, over each
piece `Z.baseSet i` of the cover, the restriction of `T.τ` is the local Thom map of the explicit
chart class with *coefficient* `d i ∈ H⁰(Z.baseSet i)`:

  `T.τ|_i = π_i^*(d i) ⌣ 𝔱_i`,

and that there is a further class `σ` of the Thom pair whose restrictions have coefficients `s i`
with `s i ⌣ s i = 1`.

**The point of the lemma.**  The coefficient `d i` of a *Thom class* over a chart is a **unit** of
`H⁰(Z.baseSet i)`, hence — since `H⁰` is the ring of locally constant `ℤ`-valued functions — it takes
the values `±1` pointwise.  The argument is short and uses only the *surjectivity* half of the Thom
isomorphism in degree `0`:

* `σ = π^*(x) ⌣ T.τ` for some global class `x ∈ H⁰(B)` (surjectivity at `k = 0`);
* restricting to the piece `i` (`Work.Thom.thomMap_restrict`) and rewriting the coefficient of
  `T.τ|_i` (`Work.ThomBordism.localThomMap_cup_general`) gives two expressions for `σ|_i`, namely
  `π_i^*(x_i) ⌣ π_i^*(d i) ⌣ 𝔱_i = localThomMap(𝔱_i)(x_i ⌣ d i)` and
  `localThomMap(𝔱_i)(s i)`;
* the local Thom map of the chart class is injective, so `x_i ⌣ d i = s i`;
* hence `1 = s i ⌣ s i = (x_i ⌣ d i) ⌣ (x_i ⌣ d i)`, so at every point
  `(ptEv p x_i · ptEv p (d i))² = 1`, and an integer whose product with another integer is `±1` is
  itself `±1`.

The only bookkeeping is the degree cast `0 + n = n` between the degree in which the hypothesis
`hd`/`hσ` are stated and the degree `0 + n` in which `Work.Thom.thomMap_restrict` and
`Work.ThomBordism.localThomMap_cup_general` live; it is handled by the two cast lemmas below.
-/

namespace Work.ThomBordism

open CategoryTheory

noncomputable section

/-- Cancelling the degree cast `n → 0 + n` against its inverse. -/
private lemma coeff_pm_one_cast_self_symm {P : ℕ → Type*} {a b : ℕ} (h : a = b) (x : P b) :
    (h ▸ (h.symm ▸ x) : P b) = x := by cases h; rfl

/-- A degree cast is injective. -/
private lemma coeff_pm_one_cast_injective {P : ℕ → Type*} {a b : ℕ} (h : a = b) :
    Function.Injective (fun x : P a => (h ▸ x : P b)) := by cases h; intro x y hxy; exact hxy

/-- **Degree-cast compatibility of the restriction of a piece class** (the form needed below): the
restriction of `y` to the piece `W` in degree `n` is the transport by `Nat.zero_add n` of the
restriction of the transport of `y` to degree `0 + n`. -/
private lemma coeff_pm_one_pieceRes_zeroAdd {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (W : Set B) (n : ℕ)
    (y : Work.Thom.OpenThom Z n) :
    (ModuleCat.Hom.hom (Work.Thom.PieceRes Z W n)) y
      = (Nat.zero_add n) ▸ ((ModuleCat.Hom.hom (Work.Thom.PieceRes Z W (0+n)))
          ((Nat.zero_add n).symm ▸ y)) := by
  conv_lhs => rw [show y = (Nat.zero_add n) ▸ ((Nat.zero_add n).symm ▸ y) from
    (coeff_pm_one_cast_self_symm (P := fun k => Work.Thom.OpenThom Z k) (Nat.zero_add n) y).symm]
  exact Work.Thom.pdCohRes_cast (TopCat.of Z.TotalSpace) (Work.Thom.zeroComplement Z)
    (Z.proj ⁻¹' W) n ((Nat.zero_add n).symm ▸ y)

/-- **The coefficient of a Thom class over a chart piece is inverted by the coefficient of any other
local description of the same class.**  If `σ` is any class of the Thom pair whose restrictions have
coefficients `s` with respect to the same chart class, then there is `x ∈ H⁰(W;ℤ)` with

  `s = x ⌣ d`.

The class `x` is the restriction to `W` of the global class produced by the *surjectivity* of the
Thom isomorphism of `T` in degree `0`. -/
private theorem coeff_pm_one_main_step {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (T : Work.Thom.ThomClass Z n)
    (W : Set B) (τc : Work.Thom.PieceCoh Z W n)
    (hτc : Function.Injective (Work.Thom.localThomMap Z n W τc 0))
    (d s : Work.Thom.Coh ℤ 0 ↥W)
    (hd : (ModuleCat.Hom.hom (Work.Thom.PieceRes Z W n)) T.τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τc 0 d))
    (σ : Work.Thom.OpenThom Z n)
    (hσ : (ModuleCat.Hom.hom (Work.Thom.PieceRes Z W n)) σ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τc 0 s)) :
    ∃ xW : Work.Thom.Coh ℤ 0 ↥W,
      (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0) xW d = s := by
  classical
  -- the surjectivity half of the Thom isomorphism in degree `0`
  obtain ⟨x, hx⟩ := (T.isThom 0).2 ((Nat.zero_add n).symm ▸ σ)
  -- restriction of the global relation to the piece `W`
  have hrestrict := Work.Thom.thomMap_restrict Z n 0 W T.τ x
  rw [hx] at hrestrict
  set xW : Work.Thom.Coh ℤ 0 ↥W := (Work.Thom.CohMap (Work.Thom.subtypeMap W) ℤ 0).hom x
    with hxW
  -- the two expressions for `σ|_W` agree
  have hmain : (ModuleCat.Hom.hom (Work.Thom.PieceRes Z W n)) σ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n W τc 0
          ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) 0 0) xW d)) := by
    rw [coeff_pm_one_pieceRes_zeroAdd Z W n σ, hrestrict, hd,
      Work.ThomBordism.localThomMap_cup_general Z n W τc d 0 xW]
  -- cancel the degree cast and use injectivity of the local Thom map
  have heq := (coeff_pm_one_cast_injective (P := fun k => Work.Thom.PieceCoh Z W k)
    (Nat.zero_add n)) (hmain.symm.trans hσ)
  exact ⟨xW, hτc heq⟩

theorem coeff_pm_one_of_normalized {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (T : Work.Thom.ThomClass Z n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (d s : (i : ι) → Work.Thom.Coh ℤ 0 ↥(Z.baseSet i))
    (hd : ∀ i : ι, (ModuleCat.Hom.hom (Work.Thom.PieceRes Z (Z.baseSet i) n)) T.τ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
            ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0 (d i)))
    (hs : ∀ i : ι, ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0)
            (s i) (s i)) = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))))
    (σ : Work.Thom.OpenThom Z n)
    (hσ : ∀ i : ι, (ModuleCat.Hom.hom (Work.Thom.PieceRes Z (Z.baseSet i) n)) σ
        = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
            ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ) 0 (s i))) :
    ∀ (i : ι) (p : ↥(Z.baseSet i)), Work.Thom.ptEv p (d i) = 1 ∨ Work.Thom.ptEv p (d i) = -1 := by
  intro i p
  obtain ⟨xW, hxW⟩ := coeff_pm_one_main_step Z T (Z.baseSet i)
    ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).τ)
    ((Work.Thom.localThomOfChart Z n e i (Z.baseSet i) (fun _ hx => hx)).isThom 0).1
    (d i) (s i) (hd i) σ (hσ i)
  -- `s i ⌣ s i = 1` and `s i = xW ⌣ d i`
  have hsq : (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0)
      ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0) xW (d i))
      ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0) xW (d i))
      = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) := by
    rw [hxW]; exact hs i
  have h1 := Work.Thom.ptEv_cup p
    ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0) xW (d i))
    ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of ↥(Z.baseSet i))) 0 0) xW (d i))
  rw [hsq, Work.Thom.ptEv_one] at h1
  rw [Work.Thom.ptEv_cup p xW (d i)] at h1
  -- `(ptEv p xW * ptEv p (d i))² = 1`
  have hpm : Work.Thom.ptEv p xW * Work.Thom.ptEv p (d i) = 1 ∨
      Work.Thom.ptEv p xW * Work.Thom.ptEv p (d i) = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one h1.symm
  rcases hpm with h | h
  · exact Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact h)
  · have h' : Work.Thom.ptEv p (d i) * (-(Work.Thom.ptEv p xW)) = 1 := by
      rw [mul_neg, mul_comm (Work.Thom.ptEv p (d i)) (Work.Thom.ptEv p xW), h, neg_neg]
    exact Int.eq_one_or_neg_one_of_mul_eq_one h'

end

end Work.ThomBordism
