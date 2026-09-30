import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.SQM.bsRedDefs
import Submission.Work.Cohomology.pd_us_cycles_eq_of_class_eq
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `β₂ Sq² = Sq³` on `H³` (`BocksteinSqTwo`)

Design: `REFS/NOTES_LEAD_SQM.md` §3.  Fix a mod-2 cocycle `x` of degree 3, an integral lift `x̃`
of it (`red2 x̃ = x`) with `δx̃ = 2 z̃`, and put `z := red2 z̃`.  The integral cup-1 coboundary
formula (`Cup1CobR`, here a hypothesis) gives, with `W := x̃ ∪₁ x̃`,

  `δW = 2 • (x̃∪x̃ - z̃∪₁x̃ + x̃∪₁z̃)`    (an identity in `C⁶(X;ℤ)`),

so that `red2 ((δW)/2) = x∪x + z∪₁x + x∪₁z` in `C⁶(X;𝔽₂)`.  The mod-2 cup-2 coboundary formula
(`Cup2Cob`, again a hypothesis) rewrites `z∪₁x + x∪₁z = δ(z∪₂x)`.  Finally, if `[x∪₁x]` lifts to
a `ℤ/4`-cocycle `Y`, then for an integral lift `Ŷ` of `Y` and `U := W + δŵ` chosen so that
`red2 U = red2 Ŷ`, the difference `U - Ŷ` is twice a cochain `T` while `δŶ` is four times a
cochain `S`; hence

  `δT = (x̃∪x̃ - z̃∪₁x̃ + x̃∪₁z̃) - 2•S`,

and reducing mod 2 gives `δ(red2 T - z∪₂x) = x∪x`: the class `[x∪x]` is a coboundary.

Everything is proved here except the two hypotheses `Cup1CobR` and `Cup2Cob` (proved in
`Pi6/SQM/cup1CoboundaryR.lean` and `Pi6/SQM/cup2CoboundaryM.lean`) and the shared reduction
notions of `Pi6/SQM/bsRedDefs.lean`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff genEval_ext)

/-! Auxiliary cochain-level reductions and their calculus (private to this file's argument; kept
in its own namespace because the sibling files of area `SQM` have their own vocabulary). -/
namespace BS

/-! ## The differential of the cochain complex -/

theorem cochainDiff_add {R : Type} [CommRing R] {X : SSet} {n : ℕ}
    (α β : Cochain R X n) :
    cochainDiff R X (α + β) = cochainDiff R X α + cochainDiff R X β := by
  have h := map_add (Work.Cohomology.cochainDiffLM R X n) α β
  simpa only [Work.Cohomology.cochainDiffLM_apply] using h

theorem cochainDiff_smul {R : Type} [CommRing R] {X : SSet} {n : ℕ}
    (c : R) (α : Cochain R X n) :
    cochainDiff R X (c • α) = c • cochainDiff R X α := by
  have h := map_smul (Work.Cohomology.cochainDiffLM R X n) c α
  simpa only [Work.Cohomology.cochainDiffLM_apply] using h

theorem cochainDiff_neg {R : Type} [CommRing R] {X : SSet} {n : ℕ} (α : Cochain R X n) :
    cochainDiff R X (-α) = -cochainDiff R X α := by
  have h := map_neg (Work.Cohomology.cochainDiffLM R X n) α
  simpa only [Work.Cohomology.cochainDiffLM_apply] using h

theorem cochainDiff_sub {R : Type} [CommRing R] {X : SSet} {n : ℕ}
    (α β : Cochain R X n) :
    cochainDiff R X (α - β) = cochainDiff R X α - cochainDiff R X β := by
  have h := map_sub (Work.Cohomology.cochainDiffLM R X n) α β
  simpa only [Work.Cohomology.cochainDiffLM_apply] using h

/-- `δ ∘ δ = 0`. -/
theorem cochainDiff_comp {R : Type} [CommRing R] {X : SSet} {n : ℕ} (α : Cochain R X n) :
    cochainDiff R X (cochainDiff R X α) = 0 := by
  have h : ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom.comp
      (((X.chainComplex (ModuleCat.of R R)).d (n + 2) (n + 1)).hom) = 0 := by
    rw [← ModuleCat.hom_comp, HomologicalComplex.d_comp_d, ModuleCat.hom_zero]
  ext x
  have hx : ((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom
      (((X.chainComplex (ModuleCat.of R R)).d (n + 2) (n + 1)).hom x) = 0 := by
    have := LinearMap.congr_fun h x
    simpa using this
  show α (((X.chainComplex (ModuleCat.of R R)).d (n + 1) n).hom
    (((X.chainComplex (ModuleCat.of R R)).d (n + 2) (n + 1)).hom x)) = 0
  rw [hx, map_zero]

/-! ## Value level helpers -/

theorem bsEval_neg {R : Type} [CommRing R] {X : SSet} {k : ℕ} (f : Cochain R X k)
    (σ : X _⦋k⦌) : genEval R X (-f) σ = -genEval R X f σ := by
  simp only [genEval, LinearMap.neg_apply]

theorem bsEval_sub {R : Type} [CommRing R] {X : SSet} {k : ℕ} (f g : Cochain R X k)
    (σ : X _⦋k⦌) : genEval R X (f - g) σ = genEval R X f σ - genEval R X g σ := by
  simp only [genEval, LinearMap.sub_apply]

theorem bsEval_zero {R : Type} [CommRing R] {X : SSet} {k : ℕ} (σ : X _⦋k⦌) :
    genEval R X (0 : Cochain R X k) σ = 0 := by
  simp only [genEval, LinearMap.zero_apply]

theorem neg_one_pow_f2 (k : ℕ) : (-1 : F2) ^ k = 1 := by
  rw [show (-1 : F2) = 1 by decide, one_pow]

/-- In `𝔽₂`-modules, every element is its own negative. -/
theorem add_self_eq_zero_of_f2 {X : SSet} {n : ℕ} (γ : Cochain F2 X n) : γ + γ = 0 := by
  have h : (2 : F2) • γ = 0 := by rw [show (2 : F2) = 0 by decide, zero_smul]
  rwa [two_smul] at h

/-- Casting a cochain along a self-equality of degrees does nothing. -/
theorem eqRec_self_cast {M : ℕ → Type*} {a : ℕ} (h : a = a) (f : M a) : h ▸ f = f := by
  rw [show h = rfl from Subsingleton.elim h rfl]

/-! ## The reduction calculus -/

theorem red2_zero (X : SSet) {n : ℕ} : red2 X (0 : Cochain ℤ X n) = 0 := by
  apply genEval_ext; intro σ
  simp only [genEval_red2, bsEval_zero, Int.cast_zero]

theorem red2_add (X : SSet) {n : ℕ} (α β : Cochain ℤ X n) :
    red2 X (α + β) = red2 X α + red2 X β := by
  apply genEval_ext; intro σ
  simp only [genEval_red2, Work.Cohomology.genEval_add, Int.cast_add]

theorem red2_neg (X : SSet) {n : ℕ} (α : Cochain ℤ X n) : red2 X (-α) = -red2 X α := by
  apply genEval_ext; intro σ
  simp only [genEval_red2, bsEval_neg, Int.cast_neg]

theorem red2_sub (X : SSet) {n : ℕ} (α β : Cochain ℤ X n) :
    red2 X (α - β) = red2 X α - red2 X β := by
  apply genEval_ext; intro σ
  simp only [genEval_red2, bsEval_sub, Int.cast_sub]

theorem red2_two_smul (X : SSet) {n : ℕ} (γ : Cochain ℤ X n) :
    red2 X ((2 : ℤ) • γ) = 0 := by
  rw [two_zsmul, red2_add]
  apply genEval_ext; intro σ
  rw [Work.Cohomology.genEval_add]
  exact CharTwo.add_self_eq_zero _

theorem red2_cochainDiff (X : SSet) {n : ℕ} (α : Cochain ℤ X n) :
    red2 X (cochainDiff ℤ X α) = cochainDiff F2 X (red2 X α) := by
  apply genEval_ext; intro σ
  rw [genEval_red2, Work.Cohomology.genEval_cochainDiff, Work.Cohomology.genEval_cochainDiff]
  push_cast
  simp only [genEval_red2]

theorem red4_cochainDiff (X : SSet) {n : ℕ} (α : Cochain ℤ X n) :
    red4 X (cochainDiff ℤ X α) = cochainDiff (ZMod 4) X (red4 X α) := by
  apply genEval_ext; intro σ
  rw [genEval_red4, Work.Cohomology.genEval_cochainDiff, Work.Cohomology.genEval_cochainDiff]
  push_cast
  simp only [genEval_red4]

theorem red2_cup (X : SSet) {n m : ℕ} (α : Cochain ℤ X n) (β : Cochain ℤ X m) :
    red2 X (Work.Cohomology.cup ℤ X α β) =
      Work.Cohomology.cup F2 X (red2 X α) (red2 X β) := by
  apply genEval_ext; intro σ
  rw [genEval_red2, Work.Cohomology.cup_apply, Work.Cohomology.cup_apply,
    genEval_red2, genEval_red2]
  push_cast
  rfl

theorem red2_cup1 (X : SSet) {n m : ℕ} (α : Cochain ℤ X n) (β : Cochain ℤ X m) :
    red2 X (Work.Cohomology.cup1 ℤ X n m α β) =
      Work.Cohomology.cup1 F2 X n m (red2 X α) (red2 X β) := by
  apply genEval_ext; intro σ
  rw [genEval_red2, Work.Cohomology.genEval_cup1, Work.Cohomology.genEval_cup1]
  push_cast
  simp only [genEval_red2, neg_one_pow_f2, one_mul]

/-! ## The cup-2 product and the bridge to `Pi6.SQ.cup1`

`Work.Pi6.SQ.cup1m` is *defined* as the library's `cup1` with the arguments interchanged
(`Pi6/SQ/Defs.lean`); in the degrees where `n + m - 1` and `m + n - 1` are definitionally equal
the transported cochain is that same cochain, which is the bridge used below. -/

theorem cup2_zero_left (X : SSet) (n m : ℕ) (v : Cochain F2 X m) :
    Work.Pi6.SQ.cup2 X n m 0 v = 0 := by
  apply genEval_ext; intro σ
  simp only [Work.Pi6.SQ.genEval_cup2, bsEval_zero, zero_mul, mul_zero, Finset.sum_const_zero]

theorem cup2_zero_right (X : SSet) (n m : ℕ) (u : Cochain F2 X n) :
    Work.Pi6.SQ.cup2 X n m u 0 = 0 := by
  apply genEval_ext; intro σ
  simp only [Work.Pi6.SQ.genEval_cup2, bsEval_zero, zero_mul, mul_zero, Finset.sum_const_zero]

theorem cup1m_same (X : SSet) (n : ℕ) (u v : Cochain F2 X n) :
    Work.Pi6.SQ.cup1m X n n u v = Work.Cohomology.cup1 F2 X n n v u := rfl

theorem cup1m_43 (X : SSet) (z : Cochain F2 X 4) (x : Cochain F2 X 3) :
    Work.Pi6.SQ.cup1m X 4 3 z x = Work.Cohomology.cup1 F2 X 3 4 x z := rfl

theorem cup1m_34 (X : SSet) (x : Cochain F2 X 3) (z : Cochain F2 X 4) :
    Work.Pi6.SQ.cup1m X 3 4 x z = Work.Cohomology.cup1 F2 X 4 3 z x := rfl

theorem cup1_smul_left (R : Type) [CommRing R] (X : SSet) (n m : ℕ)
    (c : R) (α : Cochain R X n) (β : Cochain R X m) :
    Work.Cohomology.cup1 R X n m (c • α) β = c • Work.Cohomology.cup1 R X n m α β := by
  apply genEval_ext; intro σ
  rw [Work.Cohomology.genEval_cup1, Work.Cohomology.genEval_smul, Work.Cohomology.genEval_cup1,
    Finset.smul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [Work.Cohomology.genEval_smul]
  simp only [smul_eq_mul]
  ring

theorem cup1_smul_right (R : Type) [CommRing R] (X : SSet) (n m : ℕ)
    (c : R) (α : Cochain R X n) (β : Cochain R X m) :
    Work.Cohomology.cup1 R X n m α (c • β) = c • Work.Cohomology.cup1 R X n m α β := by
  apply genEval_ext; intro σ
  rw [Work.Cohomology.genEval_cup1, Work.Cohomology.genEval_smul, Work.Cohomology.genEval_cup1,
    Finset.smul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [Work.Cohomology.genEval_smul]
  simp only [smul_eq_mul]
  ring

/-! ## Lifts and halvings of cochains -/

theorem exists_lift2 (X : SSet) {n : ℕ} (x : Cochain F2 X n) :
    ∃ xt : Cochain ℤ X n, red2 X xt = x := by
  refine ⟨vals ℤ X n (fun σ => (ZMod.val (genEval F2 X x σ) : ℤ)), ?_⟩
  apply genEval_ext; intro σ
  rw [genEval_red2, genEval_vals]
  push_cast
  exact ZMod.natCast_zmod_val (genEval F2 X x σ)

theorem exists_half (X : SSet) {n : ℕ} (α : Cochain ℤ X n) (h : red2 X α = 0) :
    ∃ β : Cochain ℤ X n, α = (2 : ℤ) • β := by
  have hpt : ∀ σ : X _⦋n⦌, (2 : ℤ) ∣ genEval ℤ X α σ := by
    intro σ
    have h1 : ((genEval ℤ X α σ : ℤ) : F2) = 0 := by
      have h2 := congrArg (fun f => genEval F2 X f σ) h
      rwa [genEval_red2, bsEval_zero] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (genEval ℤ X α σ) 2).mp h1
  refine ⟨vals ℤ X n (fun σ => genEval ℤ X α σ / 2), ?_⟩
  apply genEval_ext; intro σ
  rw [Work.Cohomology.genEval_smul, genEval_vals, two_zsmul, ← two_mul,
    Int.mul_ediv_cancel' (hpt σ)]

theorem exists_quarter (X : SSet) {n : ℕ} (α : Cochain ℤ X n) (h : red4 X α = 0) :
    ∃ β : Cochain ℤ X n, α = (4 : ℤ) • β := by
  have hpt : ∀ σ : X _⦋n⦌, (4 : ℤ) ∣ genEval ℤ X α σ := by
    intro σ
    have h1 : ((genEval ℤ X α σ : ℤ) : ZMod 4) = 0 := by
      have h2 := congrArg (fun f => genEval (ZMod 4) X f σ) h
      rwa [genEval_red4, bsEval_zero] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (genEval ℤ X α σ) 4).mp h1
  refine ⟨vals ℤ X n (fun σ => genEval ℤ X α σ / 4), ?_⟩
  apply genEval_ext; intro σ
  rw [Work.Cohomology.genEval_smul, genEval_vals, zsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hpt σ)).symm

theorem two_smul_eq_zero_iff (X : SSet) {n : ℕ} (γ : Cochain ℤ X n) :
    (2 : ℤ) • γ = 0 ↔ γ = 0 := by
  constructor
  · intro h
    apply genEval_ext; intro σ
    have h1 := congrArg (fun f => genEval ℤ X f σ) h
    rw [Work.Cohomology.genEval_smul, bsEval_zero, two_zsmul, ← two_mul] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · norm_num at h2
    · exact h2
  · intro h; rw [h, smul_zero]

theorem zmodVal_f2 (v : ZMod 4) : ((ZMod.val v : ℤ) : F2) = r42 v := by
  rw [r42, ZMod.castHom_apply, ZMod.cast_eq_val]
  push_cast
  rfl

/-- **A `ℤ/4`-cocycle reducing to `y` has an integral lift whose coboundary is four times an
integral cochain.** -/
theorem exists_lift4 (X : SSet) {n : ℕ} (Y : Cochain (ZMod 4) X n) (y : Cochain F2 X n)
    (hred : ∀ σ : X _⦋n⦌, r42 (genEval (ZMod 4) X Y σ) = genEval F2 X y σ)
    (hY : cochainDiff (ZMod 4) X Y = 0) :
    ∃ Ŷ : Cochain ℤ X n, red2 X Ŷ = y ∧
      ∃ S : Cochain ℤ X (n + 1), cochainDiff ℤ X Ŷ = (4 : ℤ) • S := by
  have hval : ∀ σ : X _⦋n⦌,
      ((ZMod.val (genEval (ZMod 4) X Y σ) : ℤ) : F2) = genEval F2 X y σ := by
    intro σ; rw [zmodVal_f2]; exact hred σ
  refine ⟨vals ℤ X n (fun σ => (ZMod.val (genEval (ZMod 4) X Y σ) : ℤ)), ?_, ?_⟩
  · apply genEval_ext; intro σ
    rw [genEval_red2, genEval_vals]
    exact hval σ
  · have h4 : red4 X (vals ℤ X n (fun σ => (ZMod.val (genEval (ZMod 4) X Y σ) : ℤ))) = Y := by
      apply genEval_ext; intro σ
      rw [genEval_red4, genEval_vals]
      push_cast
      exact ZMod.natCast_zmod_val _
    have h5 : red4 X (cochainDiff ℤ X (vals ℤ X n
        (fun σ => (ZMod.val (genEval (ZMod 4) X Y σ) : ℤ)))) = 0 := by
      rw [red4_cochainDiff, h4, hY]
    obtain ⟨S, hS⟩ := exists_quarter X _ h5
    exact ⟨S, hS⟩

/-! ## Equal cohomology classes differ by a coboundary -/

theorem classEqCoboundary (R : Type) [CommRing R] (X : SSet) (n : ℕ)
    (α β : Cochain R X (n + 1))
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0)
    (h : Work.Cohomology.cohomologyClassOf R X α hα
        = Work.Cohomology.cohomologyClassOf R X β hβ) :
    ∃ w : Cochain R X n, cochainDiff R X w = α - β := by
  obtain ⟨y, hy⟩ := Work.Cohomology.pd_us_cycles_eq_of_class_eq
    (K := Work.Cohomology.SSetCochainComplex R X) (n := n)
    (Work.Cohomology.cocycleOf R X α hα) (Work.Cohomology.cocycleOf R X β hβ) h
  refine ⟨y, ?_⟩
  rw [← Work.Cohomology.SSetCochainComplex_d_apply R X n y, hy,
    Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.iCycles_cocycleOf]

theorem cohomologyClassOf_congr {R : Type} [CommRing R] {X : SSet} {n : ℕ}
    {α β : Cochain R X n} (h : α = β) (hα : cochainDiff R X α = 0)
    (hβ : cochainDiff R X β = 0) :
    Work.Cohomology.cohomologyClassOf R X α hα
      = Work.Cohomology.cohomologyClassOf R X β hβ := by
  subst h
  simp only [Work.Cohomology.cohomologyClassOf]

end BS

open BS

/-! ## The main statement -/

theorem bocksteinSqTwo_gen (hR : Cup1CobR) (h2 : Cup2Cob) (X : SSet)
    (x : Cochain F2 X 3) (hx : cochainDiff F2 X x = 0)
    (hxx : cochainDiff F2 X (Work.Pi6.SQ.cup1m X 3 3 x x) = 0)
    (hsq : cochainDiff F2 X (Work.Cohomology.cup F2 X x x) = 0)
    (hlift : ∃ (Y : Cochain (ZMod 4) X 5) (_ : cochainDiff (ZMod 4) X Y = 0)
      (y : Cochain F2 X 5) (hy : cochainDiff F2 X y = 0),
      Work.Cohomology.cohomologyClassOf F2 X y hy
        = Work.Cohomology.cohomologyClassOf F2 X (Work.Pi6.SQ.cup1m X 3 3 x x) hxx ∧
      ∀ σ : X _⦋5⦌, r42 (genEval (ZMod 4) X Y σ) = genEval F2 X y σ) :
    Work.Cohomology.cohomologyClassOf F2 X (Work.Cohomology.cup F2 X x x) hsq = 0 := by
  -- ## 1. An integral lift `xt` of `x`, and `zt` with `δxt = 2 • zt`
  obtain ⟨xt, hxt⟩ := exists_lift2 X x
  have hred_dxt : red2 X (cochainDiff ℤ X xt) = 0 := by
    rw [red2_cochainDiff, hxt, hx]
  obtain ⟨zt, hzt⟩ := exists_half X (cochainDiff ℤ X xt) hred_dxt
  have hzt_cyc : cochainDiff ℤ X zt = 0 := by
    have h : (2 : ℤ) • cochainDiff ℤ X zt = 0 := by
      rw [← cochainDiff_smul, ← hzt, cochainDiff_comp]
    exact (two_smul_eq_zero_iff X (cochainDiff ℤ X zt)).mp h
  set z : Cochain F2 X 4 := red2 X zt with hz
  have hzc : cochainDiff F2 X z = 0 := by
    rw [hz, ← red2_cochainDiff, hzt_cyc, red2_zero]
  -- ## 2. The integral identity for `δ(x̃ ∪₁ x̃)` and its mod-2 reduction
  set A : Cochain ℤ X 6 := Work.Cohomology.cup ℤ X xt xt
    - Work.Cohomology.cup1 ℤ X (3 + 1) 3 zt xt
    + Work.Cohomology.cup1 ℤ X 3 (3 + 1) xt zt with hA
  have hWc : cochainDiff ℤ X (Work.Cohomology.cup1 ℤ X 3 3 xt xt) = (2 : ℤ) • A := by
    rw [hA]
    have h := hR ℤ X 3 3 xt xt (by norm_num) (by norm_num)
    simp only at h
    rw [show (-1 : ℤ) ^ (3 * 3) = -1 by norm_num,
      show (-1 : ℤ) ^ (3 + 1) = 1 by norm_num] at h
    rw [hzt] at h
    rw [cup1_smul_left ℤ X (3 + 1) 3 (2 : ℤ) zt xt] at h
    rw [cup1_smul_right ℤ X 3 (3 + 1) (2 : ℤ) xt zt] at h
    simp only [neg_one_smul, one_smul, sub_neg_eq_add] at h
    rw [show Work.Cohomology.cup ℤ X xt xt + Work.Cohomology.cup ℤ X xt xt
      = (2 : ℤ) • (Work.Cohomology.cup ℤ X xt xt) from (two_smul ℤ _).symm] at h
    rw [← smul_sub, ← smul_add] at h
    exact h
  have hredA : red2 X A = Work.Cohomology.cup F2 X x x
      - Work.Cohomology.cup1 F2 X (3 + 1) 3 z x
      + Work.Cohomology.cup1 F2 X 3 (3 + 1) x z := by
    rw [hA, red2_add, red2_sub, red2_cup, red2_cup1, red2_cup1, hxt, ← hz]
  -- ## 3. The `ℤ/4`-lift `Y`, the correction `ŵ`, and `U`
  obtain ⟨Y, hY, y, hy, hcls, hval⟩ := hlift
  have hredW : red2 X (Work.Cohomology.cup1 ℤ X 3 3 xt xt) = Work.Pi6.SQ.cup1m X 3 3 x x := by
    rw [red2_cup1, hxt, ← cup1m_same X 3 x x]
  have hredWc : cochainDiff F2 X (red2 X (Work.Cohomology.cup1 ℤ X 3 3 xt xt)) = 0 := by
    rw [hredW]; exact hxx
  have hcls' : Work.Cohomology.cohomologyClassOf F2 X y hy
      = Work.Cohomology.cohomologyClassOf F2 X
          (red2 X (Work.Cohomology.cup1 ℤ X 3 3 xt xt)) hredWc := by
    rw [cohomologyClassOf_congr hredW hredWc hxx]
    exact hcls
  obtain ⟨w, hw⟩ := classEqCoboundary F2 X 4 y
    (red2 X (Work.Cohomology.cup1 ℤ X 3 3 xt xt)) hy hredWc hcls'
  obtain ⟨ŵ, hŵ⟩ := exists_lift2 X w
  obtain ⟨Ŷ, hŶ2, S, hS⟩ := exists_lift4 X Y y hval hY
  set U : Cochain ℤ X 5 := Work.Cohomology.cup1 ℤ X 3 3 xt xt + cochainDiff ℤ X ŵ with hU
  have hredU : red2 X U = y := by
    rw [hU, red2_add, red2_cochainDiff, hŵ, hw, hredW]
    abel
  set V : Cochain ℤ X 5 := U - Ŷ with hV
  have hredV : red2 X V = 0 := by
    rw [hV, red2_sub, hredU, hŶ2, sub_self]
  obtain ⟨T, hT⟩ := exists_half X V hredV
  -- ## 4. The key identity `δT = A - 2 • S`
  have hdelT : cochainDiff ℤ X T = A - (2 : ℤ) • S := by
    have hkey : (2 : ℤ) • (cochainDiff ℤ X T - (A - (2 : ℤ) • S)) = 0 := by
      rw [smul_sub]
      have h1 : (2 : ℤ) • cochainDiff ℤ X T = (2 : ℤ) • A - (4 : ℤ) • S := by
        rw [← cochainDiff_smul, ← hT, hV, cochainDiff_sub, hU, cochainDiff_add,
          cochainDiff_comp, add_zero, hS, hWc]
      have h2 : (2 : ℤ) • (A - (2 : ℤ) • S) = (2 : ℤ) • A - (4 : ℤ) • S := by
        rw [smul_sub, smul_smul, show (2 : ℤ) * 2 = 4 by norm_num]
      rw [h1, h2, sub_self]
    exact sub_eq_zero.mp ((two_smul_eq_zero_iff X _).mp hkey)
  have hdelT2 : cochainDiff F2 X (red2 X T) = red2 X A := by
    rw [← red2_cochainDiff, hdelT, red2_sub, red2_two_smul, sub_zero]
  -- ## 5. The mod-2 cup-2 coboundary formula
  have hcup2 : cochainDiff F2 X (Work.Pi6.SQ.cup2 X 4 3 z x)
      = Work.Cohomology.cup1 F2 X 3 4 x z
        + Work.Cohomology.cup1 F2 X 4 3 z x := by
    have h := h2 X 4 3 z x (by norm_num) (by norm_num)
    simp only at h
    rw [hzc, hx] at h
    rw [cup2_zero_left, cup2_zero_right, add_zero, add_zero] at h
    rw [cup1m_43 X z x, cup1m_34 X x z] at h
    exact h
  -- ## 6. The witness and the vanishing of the class
  have hdelv : cochainDiff F2 X (red2 X T - Work.Pi6.SQ.cup2 X 4 3 z x)
      = Work.Cohomology.cup F2 X x x := by
    have hP : (2 : ℤ) • (Work.Cohomology.cup1 F2 X 4 3 z x) = 0 := by
      rw [two_zsmul, add_self_eq_zero_of_f2]
    rw [cochainDiff_sub, hdelT2, hredA, hcup2]
    rw [show (Work.Cohomology.cup F2 X x x - Work.Cohomology.cup1 F2 X 4 3 z x
          + Work.Cohomology.cup1 F2 X 3 4 x z)
          - (Work.Cohomology.cup1 F2 X 3 4 x z + Work.Cohomology.cup1 F2 X 4 3 z x)
        = Work.Cohomology.cup F2 X x x
          - (2 : ℤ) • (Work.Cohomology.cup1 F2 X 4 3 z x) from by abel,
      hP, sub_zero]
  have hcyc : (Work.Cohomology.SSetCochainComplex F2 X).iCycles 6
      (Work.Cohomology.cocycleOf F2 X (Work.Cohomology.cup F2 X x x) hsq)
      = ((Work.Cohomology.SSetCochainComplex F2 X).d 5 6).hom
        (red2 X T - Work.Pi6.SQ.cup2 X 4 3 z x) := by
    rw [Work.Cohomology.iCycles_cocycleOf, Work.Cohomology.SSetCochainComplex_d_apply, hdelv]
  exact Work.Cohomology.homologyπ_eq_zero_of_d F2 X 6 5 _ _ hcyc

/-- **`β₂ Sq² = Sq³` on `H³`**: if `[x∪₁x]` lifts to `ℤ/4` then `[x∪x] = 0`. -/
theorem bocksteinSqTwo (hR : Work.Pi6.SQM.Cup1CobR) (h2 : Work.Pi6.SQM.Cup2Cob) :
    Work.Pi6.SQM.BocksteinSqTwo := by
  intro X _ x hx hxx hsq hlift
  exact bocksteinSqTwo_gen hR h2 (SX X) x hx hxx hsq hlift

end

end Work.Pi6.SQM
