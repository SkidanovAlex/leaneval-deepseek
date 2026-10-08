import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_l22c1Defs
import Submission.Work.BG.s02_gram
import Submission.Work.BG.s02_classSumSquare
import Submission.Work.BG.s02_classSumSquare_vanish
import Submission.Work.BG.s02_pairCount_sum
import Submission.Work.BG.s02_pairCount_conj
import Submission.Work.BG.s02_pairCount_T_card
import Submission.Work.BG.s02_dcf_mem_irr
import Submission.Work.BG.s02_indDiff
import Submission.Work.BG.Lemma13
import Submission.Work.BG.H0Conj
import Submission.Work.BG.CharBridge
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.sconjLam
import Submission.Work.BG.indexTwoInduceIrreducible
import Submission.Work.BG.indexTwoMackey
import Submission.Work.BG.Lambda

/-!
# Area BG: Bender–Glauberman 1981, Lemma 2.2, first case (`Lemma22CaseOneProp`)

This file proves `Work.BG.Lemma22CaseOneProp C`, the `Prop`-valued statement of the design
layer `Submission/Work/BG/S02.lean`: for `μ, ν ∈ Irr(H₀)` with `ν = λ_β μ` (`LamEquiv C μ ν`)
and `μ^s ≠ μ`, `ν^s ≠ ν`,

`∑_{x,y ∈ t^G} (μ - ν)^G(xy) = 0`.

## The mathematics (Bender–Glauberman 1981, p. 205, Lemma 2.2 case 1)

Write `δ := μ - ν ∈ CF(H₀)`; it vanishes off `T = H₀ ∖ U` because `ν = λ_β μ` and `λ_β` is
trivial on `U`.  Let `δ^H := Ind_{H₀}^{H} δ` (the area's `dcf C (μ - ν)`), so that
`δ^G = Ind_H^G δ^H` by induction in stages (`ind_eq_induce_dcf`).  Let

`f(g) := #{(x,y) ∈ t^G × t^G : xy = g}`

be the pair-count weight, which is a class function of `G` (`s02_pairCount_conj`) and turns the
double sum into a single one (`s02_pairCount_sum`):

`∑_{x,y ∈ t^G} δ^G(xy) = ∑_g f(g) δ^G(g) = |G|·⟨δ^G, f⟩_G`.

Frobenius reciprocity (`ClassFunction.inner_induce_eq_inner_restrict`) gives
`⟨δ^G, f⟩_G = ⟨δ^H, Res_H f⟩_H`, so

`∑_{x,y ∈ t^G} δ^G(xy) = (|G|/|H|) ∑_{h ∈ H} δ^H(h) f(h)`

(the scalar is harmless: `f` takes real values, so no complex conjugation intervenes).
On `T` the weight `f` may be computed inside `H`: if `x, y ∈ G` are involutions with
`xy = h ∈ T`, then `x h x⁻¹ = h⁻¹ ∈ T`, so `x, y ∈ N_G(T) = H` by the TI property, and
`x, y ∉ H₀` since `t` is the only involution of `H₀` — hence `f(h)` counts exactly the pairs
of involutions of `H ∖ H₀` with product `h` (`s02_pairCount_T_card`).  Since `δ^H` vanishes
off `T`, this turns the `H`-sum into `∑_{x,y ∈ XH} δ^H(xy)`, with `XH C` the `Finset` of
involutions of `H ∖ H₀` (our `s02_l22c1Defs.XH`); and off `U` the two sums agree because
`δ^H` vanishes on `U ⊆ H₀ ∖ T` (its Mackey expression is `(1-λ_β)μ`, killed by `λ_β|_U = 1`).

Finally `μ^s ≠ μ` and `ν^s ≠ ν` make `μ^H = dcf C μ` and `ν^H = dcf C ν` irreducible
(`s02_dcf_mem_irr`, BG Remark 1.4), and both vanish off `H₀ ⊇ XH`; the class-sum-square
identity (BG Lemma 2.2-a, `s02_classSumSquare`) applied with `X = XH` gives
`θ(1)·∑_{x,y ∈ XH} θ(xy) = (∑_{x ∈ XH} θ(x))² = 0` for `θ = dcf C μ` and `θ = dcf C ν`, hence
`∑_{x,y ∈ XH} δ^H(xy) = 0` and with it the claim.

## Layout

* `l22c1_tClass_conj`, `l22c1_XH_conj`, `l22c1_dcf_sub` — elementary helpers;
* `s02_lemma22CaseOne` — the theorem.

The five delegated leaves live in `s02_pairCount_sum`, `s02_pairCount_conj`,
`s02_pairCount_T_card`, `s02_classSumSquare_vanish` and `s02_dcf_mem_irr`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

set_option linter.style.haveILetI false

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary helpers -/

/-- `t^G` (the `G`-class of `t`, a `Finset` of `G`) is conjugation-invariant. -/
theorem l22c1_tClass_conj (C : Sec2Ctx G) [Fintype G] :
    ∀ g x : G, x ∈ tClass C → g * x * g⁻¹ ∈ tClass C := by
  intro g x hx
  simp only [tClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  refine isConj_iff.mpr ⟨c * g⁻¹, ?_⟩
  rw [show c * g⁻¹ * (g * x * g⁻¹) * (c * g⁻¹)⁻¹ = c * x * c⁻¹ from by group, hc]

/-- `XH C` (the involutions of `H` outside `H₀`) is conjugation-invariant in `↥H`. -/
theorem l22c1_XH_conj (C : Sec2Ctx G) [Fintype ↥C.P.H] :
    ∀ g x : ↥C.P.H, x ∈ XH C → g * x * g⁻¹ ∈ XH C := by
  intro g x hx
  rw [mem_XH] at hx ⊢
  refine ⟨?_, ?_⟩
  · intro hmem
    refine hx.1 ((mem_H0_conj_iff C.P g (x : G)).mp ?_)
    simpa using hmem
  · calc (g * x * g⁻¹) ^ 2 = (g * x * g⁻¹) * (g * x * g⁻¹) := by rw [pow_two]
      _ = g * (x * x) * g⁻¹ := by group
      _ = g * 1 * g⁻¹ := by rw [← pow_two, hx.2]
      _ = 1 := by group

/-- `dcf` (`Ind_{H₀}^{H}`, whence `Ind_{H₀}^{G}` by stages) is additive. -/
theorem l22c1_dcf_sub {G : Type} [Group G] [Finite G] [Fintype G] (C : Sec2Ctx G)
    [Fintype ↥C.P.H] [Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ)]
    (a b : ClassFunction ↥C.P.H0 ℂ) : dcf C (a - b) = dcf C a - dcf C b := by
  have h1 : (a - b : ClassFunction ↥C.P.H0 ℂ) = a + (-1 : ℂ) • b := by
    ext x; simp [sub_eq_add_neg]
  rw [h1]
  simp only [dcf]
  rw [ClassFunction.compHom_add, ClassFunction.compHom_smul, ClassFunction.induce_add,
    ClassFunction.induce_smul]
  ext x
  simp [sub_eq_add_neg]

/-! ## The main theorem -/

/-- **Bender–Glauberman 1981, Lemma 2.2, case one** (`Work.BG.Lemma22CaseOneProp`): for
`μ, ν ∈ Irr(H₀)` in the same `Λ`-orbit (`LamEquiv C μ ν`) with `μ^s ≠ μ` and `ν^s ≠ ν`,
the induced difference `(μ - ν)^G` satisfies `∑_{x,y ∈ t^G} (μ - ν)^G(xy) = 0`. -/
theorem s02_lemma22CaseOne {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.BG.Lemma22CaseOneProp C := by
  intro μ ν hμ hν hlam hμs hνs
  haveI : Fintype ↥C.P.H := Fintype.ofFinite _
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Fintype ↥(C.P.H0.subgroupOf C.P.H) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥C.P.H : ℂ) := invertible_natCard_subgroup _
  haveI : Invertible (Nat.card ↥(C.P.H0.subgroupOf C.P.H) : ℂ) := invertible_natCard_subgroup _
  -- The pair-count class function on `G`: `f(g) = #{(x,y) ∈ t^G × t^G : xy = g}`.
  have hFconj : ∀ g h : G,
      ((pairSet (tClass C) (h * g * h⁻¹)).card : ℂ) = ((pairSet (tClass C) g).card : ℂ) := by
    intro g h
    have h := s02_pairCount_conj (X := tClass C) (l22c1_tClass_conj C) g h
    exact_mod_cast h
  let F : ClassFunction G ℂ :=
    ⟨fun g => ((pairSet (tClass C) g).card : ℂ), hFconj⟩
  have hFapply : ∀ g : G, F g = ((pairSet (tClass C) g).card : ℂ) := fun g => rfl
  have hFstar : ∀ g : G, star (F g) = F g := by
    intro g; rw [hFapply g]; exact star_natCast _
  -- Step 1: rewrite the double sum as a single sum against the pair count.
  have hS1 : (∑ x ∈ tClass C, ∑ y ∈ tClass C, ind C (μ - ν) (x * y)) =
      ∑ g : G, F g * ind C (μ - ν) g := by
    have h := s02_pairCount_sum (X := tClass C) (ψ := ind C (μ - ν))
    rw [h]
  -- Step 2: `Σ_g F g * χ g = |G| * ⟨χ, F⟩` (`F` is real-valued, so `star` disappears).
  have hS2 : (∑ g : G, F g * ind C (μ - ν) g) =
      (Nat.card G : ℂ) * ClassFunction.inner (ind C (μ - ν)) F := by
    have h1 : ClassFunction.innerSum (ind C (μ - ν)) F =
        ∑ g : G, F g * ind C (μ - ν) g := by
      rw [ClassFunction.innerSum]
      exact Finset.sum_congr rfl (fun g _ => by rw [hFstar g, mul_comm])
    rw [ClassFunction.card_mul_inner, h1]
  -- Step 3: Frobenius reciprocity (induction in stages `H₀ → H → G`).
  have hrec : ClassFunction.inner (ind C (μ - ν)) F =
      ClassFunction.inner (dcf C (μ - ν)) (ClassFunction.restrict C.P.H F) := by
    rw [ind_eq_induce_dcf C (μ - ν)]
    exact ClassFunction.inner_induce_eq_inner_restrict C.P.H (dcf C (μ - ν)) F
  -- Step 4: expand the `H`-inner product.
  have hinner : ClassFunction.inner (dcf C (μ - ν)) (ClassFunction.restrict C.P.H F) =
      ⅟(Nat.card ↥C.P.H : ℂ) *
        ∑ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G) := by
    rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
    refine congrArg (fun z => ⅟(Nat.card ↥C.P.H : ℂ) * z) ?_
    exact Finset.sum_congr rfl (fun h _ => by
      rw [ClassFunction.restrict_apply, hFstar (h : G)])
  -- Step 5: on `T` the pair count may be computed inside `H` (TI argument), and `dcf` is
  -- supported on `T`, so the `H`-sum is the double sum over the involutions of `H ∖ H₀`.
  have hkey : (∑ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G)) =
      ∑ x ∈ XH C, ∑ y ∈ XH C, dcf C (μ - ν) (x * y) := by
    have hpoint : ∀ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G) =
        dcf C (μ - ν) h * ((pairSet (XH C) h).card : ℂ) := by
      intro h
      by_cases hh : (h : G) ∈ Tset C.P.H0 C.P.U
      · rw [hFapply (h : G), s02_pairCount_T_card C h hh]
      · rw [dcf_eq_zero_of_not_mem_T C hlam h hh, zero_mul, zero_mul]
    calc (∑ h : ↥C.P.H, dcf C (μ - ν) h * F (h : G))
        = ∑ h : ↥C.P.H, dcf C (μ - ν) h * ((pairSet (XH C) h).card : ℂ) :=
          Finset.sum_congr rfl (fun h _ => hpoint h)
      _ = ∑ h : ↥C.P.H, ((pairSet (XH C) h).card : ℂ) * dcf C (μ - ν) h :=
          Finset.sum_congr rfl (fun h _ => mul_comm _ _)
      _ = ∑ x ∈ XH C, ∑ y ∈ XH C, dcf C (μ - ν) (x * y) :=
          (s02_pairCount_sum (X := XH C) (ψ := dcf C (μ - ν))).symm
  -- Step 6: the double sum over the involutions of `H ∖ H₀` vanishes.
  have hvanish : (∑ x ∈ XH C, ∑ y ∈ XH C, dcf C (μ - ν) (x * y)) = 0 := by
    have hμirr : IsPmIrr (dcf C μ) := Or.inl (s02_dcf_mem_irr C hμ hμs)
    have hνirr : IsPmIrr (dcf C ν) := Or.inl (s02_dcf_mem_irr C hν hνs)
    have hμ0 : ∀ x ∈ XH C, dcf C μ x = 0 := by
      intro x hx
      rw [mem_XH] at hx
      have hxH : x ∉ C.P.H0.subgroupOf C.P.H := fun h => hx.1 (Subgroup.mem_subgroupOf.mp h)
      have := ClassFunction.induce_eq_zero_of_not_mem_normal
        (H := C.P.H0.subgroupOf C.P.H)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom μ) hxH
      simpa [dcf] using this
    have hν0 : ∀ x ∈ XH C, dcf C ν x = 0 := by
      intro x hx
      rw [mem_XH] at hx
      have hxH : x ∉ C.P.H0.subgroupOf C.P.H := fun h => hx.1 (Subgroup.mem_subgroupOf.mp h)
      have := ClassFunction.induce_eq_zero_of_not_mem_normal
        (H := C.P.H0.subgroupOf C.P.H)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe C.P.H0_le_H).toMonoidHom ν) hxH
      simpa [dcf] using this
    have hsumsub : (∑ x ∈ XH C, ∑ y ∈ XH C, (dcf C μ - dcf C ν) (x * y)) =
        (∑ x ∈ XH C, ∑ y ∈ XH C, dcf C μ (x * y)) -
          (∑ x ∈ XH C, ∑ y ∈ XH C, dcf C ν (x * y)) := by
      simp only [ClassFunction.sub_apply, Finset.sum_sub_distrib]
    rw [l22c1_dcf_sub C μ ν, hsumsub,
      s02_classSumSquare_vanish (X := XH C) (l22c1_XH_conj C) (dcf C μ) hμirr hμ0,
      s02_classSumSquare_vanish (X := XH C) (l22c1_XH_conj C) (dcf C ν) hνirr hν0,
      sub_zero]
  rw [hS1, hS2, hrec, hinner, hkey, hvanish]
  rw [mul_zero, mul_zero]

end Work.BG
