import Mathlib
import Submission.Work.SSGRoute.free_lie_four_defs
import Submission.Work.SSGRoute.flg_defs
import Submission.Work.SSGRoute.CC.FlgFourLetters
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# The two-orbit (`|S| = 4`) case of the residual-generation statement

Let `a b c d` be four distinct letters with `σ a = b`, `σ c = d`, and `u ∈ Wsub X` be `σA`-fixed
with every support word using all four letters.  Then `u ∈ δW + flgThetaSpan X σA`.

The proof analyses the six elements `Bᵢ = ⁅⁅⁅a,πᵢ(b,c,d)⁆,·⁆,·⁆` spanning the "four-letter part"
`W'` of `Wsub`:  every permutation `<x,y,z,w>` of the four letters satisfies
`brk4 X (x,y,z,w) ∈ span{B₀,…,B₅}` (reduction with symmetry, Jacobi and the outer identity
`flg_brk4_swap34`).  Writing `u = ∑ yᵢ Bᵢ`, the equations `δ u = 0` are read off from the
coefficients of the three words `abcd`, `abdc`, `acbd`, and give
`y₀ + y₁ = y₂ + y₃ = y₄ + y₅`; then
`u = (y₀+y₁)·(B₀+B₂+B₄) + y₁·(B₀+B₁) + y₃·(B₂+B₃) + y₅·(B₄+B₅)`, and
`B₀+B₁ = δ B₀`, `B₀+B₂+B₄ = δ B₄` while `B₂+B₃ = Θ(⁅a,c⁆)` and `B₄+B₅ = Θ(⁅a,d⁆)`.
-/

namespace Work.SSGRoute.CC

open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## The injectivity of four-letter words -/

theorem flg_word4_eq_iff (X : Type) (x1 x2 x3 x4 y1 y2 y3 y4 : X) :
    (FreeMonoid.of x1 * FreeMonoid.of x2 * FreeMonoid.of x3 * FreeMonoid.of x4
        = FreeMonoid.of y1 * FreeMonoid.of y2 * FreeMonoid.of y3 * FreeMonoid.of y4)
      ↔ (x1 = y1 ∧ x2 = y2 ∧ x3 = y3 ∧ x4 = y4) := by
  constructor
  · intro h
    have h' := congrArg FreeMonoid.toList h
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.cons_append, List.singleton_append,
      List.nil_append] at h'
    simp only [List.cons.injEq, List.nil_eq, and_true] at h'
    exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem flg_single_coeff_eq (X : Type) [DecidableEq (FreeMonoid X)] (U : FreeMonoid X)
    (c : ZMod 2) (w : FreeMonoid X) :
    (MonoidAlgebra.single U c).coeff w = if U = w then c else 0 := by
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- Four pairwise distinct letters. -/
theorem flg_distinct_of_card4 (X : Type) [DecidableEq X] {x y z w : X}
    (h : ({x, y, z, w} : Finset X).card = 4) :
    x ≠ y ∧ x ≠ z ∧ x ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w := by
  have h3 : ∀ p q r : X, ({p, q, r} : Finset X).card ≤ 3 := by
    intro p q r
    have h2 : ({q, r} : Finset X).card ≤ 2 := by
      have := Finset.card_insert_le q ({r} : Finset X)
      simp only [Finset.card_singleton] at this
      omega
    have := Finset.card_insert_le p ({q, r} : Finset X)
    omega
  have key : ∀ p q r s : X, ({p, q, r, s} : Finset X).card = 4 →
      p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s := by
    intro p q r s hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro rfl
      have h1 : ({p, p, r, s} : Finset X).card ≤ 3 := by
        rw [show ({p, p, r, s} : Finset X) = ({p, r, s} : Finset X) from by
          ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact h3 p r s
      omega
    · rintro rfl
      have h1 : ({p, q, p, s} : Finset X).card ≤ 3 := by
        rw [show ({p, q, p, s} : Finset X) = ({p, q, s} : Finset X) from by
          ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact h3 p q s
      omega
    · rintro rfl
      have h1 : ({p, q, r, p} : Finset X).card ≤ 3 := by
        rw [show ({p, q, r, p} : Finset X) = ({p, q, r} : Finset X) from by
          ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact h3 p q r
      omega
    · rintro rfl
      have h1 : ({p, q, q, s} : Finset X).card ≤ 3 := by
        rw [show ({p, q, q, s} : Finset X) = ({p, q, s} : Finset X) from by
          ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact h3 p q s
      omega
    · rintro rfl
      have h1 : ({p, q, r, q} : Finset X).card ≤ 3 := by
        rw [show ({p, q, r, q} : Finset X) = ({p, q, r} : Finset X) from by
          ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact h3 p q r
      omega
    · rintro rfl
      have h1 : ({p, q, r, r} : Finset X).card ≤ 3 := by
        rw [show ({p, q, r, r} : Finset X) = ({p, q, r} : Finset X) from by
          ext t; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto]
        exact h3 p q r
      omega
  exact key x y z w h


/-! ## The two-orbit case -/

section FourLetters

variable (X : Type) [DecidableEq X] (σ : X ≃ X) (hσ : ∀ y, σ (σ y) = y)
  (a b c d : X) (ha : σ a = b) (hc : σ c = d)

include hσ ha hc in
theorem flg_sigmaA_brk4_six (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ x y, σA (x * y) = σA x * σA y) (hone : σA 1 = 1)
    (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1) :
    ∀ t : X × X × X × X,
      σA (brk4 X t) = brk4 X (σ t.1, σ t.2.1, σ t.2.2.1, σ t.2.2.2) :=
  fun t => flg_sigmaA_brk4 X σ σA hmul hone hgen t.1 t.2.1 t.2.2.1 t.2.2.2

end FourLetters


/-! ## The two-orbit case -/

section FourLetters

variable (X : Type) [DecidableEq X]

/-- The six "first slot `a`" commutators `Bᵢ`. -/
noncomputable def flgBV (X : Type) (a b c d : X) :
    Fin 6 → MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  ![brk4 X (a,b,c,d), brk4 X (a,b,d,c), brk4 X (a,c,b,d), brk4 X (a,c,d,b),
    brk4 X (a,d,b,c), brk4 X (a,d,c,b)]

/-- The span of the six `Bᵢ` (kept irreducible so that the case analysis below is cheap). -/
@[irreducible] noncomputable def flgS (X : Type) (a b c d : X) :
    Submodule (ZMod 2) (MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  Submodule.span (ZMod 2) (Set.range (flgBV X a b c d))

theorem flgS_eq (X : Type) (a b c d : X) :
    flgS X a b c d = Submodule.span (ZMod 2) (Set.range (flgBV X a b c d)) := by
  unfold flgS; rfl

/-- `brk4` of the permutation `abcd`. -/
theorem flg_mem_abcd (a b c d : X) : brk4 X (a, b, c, d) ∈ flgS X a b c d := by
  unfold flgS
  rw [show brk4 X (a, b, c, d) = (flgBV X a b c d 0 : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    from by simp [flgBV]]
  exact Submodule.subset_span (Set.mem_range_self (f := flgBV X a b c d) 0)
/-- `brk4` of the permutation `abdc`. -/
theorem flg_mem_abdc (a b c d : X) : brk4 X (a, b, d, c) ∈ flgS X a b c d := by
  unfold flgS
  rw [show brk4 X (a, b, d, c) = (flgBV X a b c d 1 : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    from by simp [flgBV]]
  exact Submodule.subset_span (Set.mem_range_self (f := flgBV X a b c d) 1)
/-- `brk4` of the permutation `acbd`. -/
theorem flg_mem_acbd (a b c d : X) : brk4 X (a, c, b, d) ∈ flgS X a b c d := by
  unfold flgS
  rw [show brk4 X (a, c, b, d) = (flgBV X a b c d 2 : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    from by simp [flgBV]]
  exact Submodule.subset_span (Set.mem_range_self (f := flgBV X a b c d) 2)
/-- `brk4` of the permutation `acdb`. -/
theorem flg_mem_acdb (a b c d : X) : brk4 X (a, c, d, b) ∈ flgS X a b c d := by
  unfold flgS
  rw [show brk4 X (a, c, d, b) = (flgBV X a b c d 3 : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    from by simp [flgBV]]
  exact Submodule.subset_span (Set.mem_range_self (f := flgBV X a b c d) 3)
/-- `brk4` of the permutation `adbc`. -/
theorem flg_mem_adbc (a b c d : X) : brk4 X (a, d, b, c) ∈ flgS X a b c d := by
  unfold flgS
  rw [show brk4 X (a, d, b, c) = (flgBV X a b c d 4 : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    from by simp [flgBV]]
  exact Submodule.subset_span (Set.mem_range_self (f := flgBV X a b c d) 4)
/-- `brk4` of the permutation `adcb`. -/
theorem flg_mem_adcb (a b c d : X) : brk4 X (a, d, c, b) ∈ flgS X a b c d := by
  unfold flgS
  rw [show brk4 X (a, d, c, b) = (flgBV X a b c d 5 : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    from by simp [flgBV]]
  exact Submodule.subset_span (Set.mem_range_self (f := flgBV X a b c d) 5)
/-- `brk4` of the permutation `bacd`. -/
theorem flg_mem_bacd (a b c d : X) : brk4 X (b, a, c, d) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X b a c d]
  exact flg_mem_abcd X a b c d
/-- `brk4` of the permutation `badc`. -/
theorem flg_mem_badc (a b c d : X) : brk4 X (b, a, d, c) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X b a d c]
  exact flg_mem_abdc X a b c d
/-- `brk4` of the permutation `bcad`. -/
theorem flg_mem_bcad (a b c d : X) : brk4 X (b, c, a, d) ∈ flgS X a b c d := by
  rw [flg_brk4_jacobi X b c a d, flg_brk4_symm X b a c d, flg_brk4_symm X c a b d]
  exact Submodule.add_mem _ (flg_mem_abcd X a b c d) (flg_mem_acbd X a b c d)
/-- `brk4` of the permutation `bcda`. -/
theorem flg_mem_bcda (a b c d : X) : brk4 X (b, c, d, a) ∈ flgS X a b c d := by
  rw [flg_brk4_swap34 X b c d a, flg_brk4_symm X d a b c, flg_brk4_symm X d a c b]
  exact Submodule.add_mem _ (Submodule.add_mem _ (flg_mem_bcad X a b c d) (flg_mem_adbc X a b c d)) (flg_mem_adcb X a b c d)
/-- `brk4` of the permutation `bdac`. -/
theorem flg_mem_bdac (a b c d : X) : brk4 X (b, d, a, c) ∈ flgS X a b c d := by
  rw [flg_brk4_jacobi X b d a c, flg_brk4_symm X b a d c, flg_brk4_symm X d a b c]
  exact Submodule.add_mem _ (flg_mem_abdc X a b c d) (flg_mem_adbc X a b c d)
/-- `brk4` of the permutation `bdca`. -/
theorem flg_mem_bdca (a b c d : X) : brk4 X (b, d, c, a) ∈ flgS X a b c d := by
  rw [flg_brk4_swap34 X b d c a, flg_brk4_symm X c a b d, flg_brk4_symm X c a d b]
  exact Submodule.add_mem _ (Submodule.add_mem _ (flg_mem_bdac X a b c d) (flg_mem_acbd X a b c d)) (flg_mem_acdb X a b c d)
/-- `brk4` of the permutation `cabd`. -/
theorem flg_mem_cabd (a b c d : X) : brk4 X (c, a, b, d) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X c a b d]
  exact flg_mem_acbd X a b c d
/-- `brk4` of the permutation `cadb`. -/
theorem flg_mem_cadb (a b c d : X) : brk4 X (c, a, d, b) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X c a d b]
  exact flg_mem_acdb X a b c d
/-- `brk4` of the permutation `cbad`. -/
theorem flg_mem_cbad (a b c d : X) : brk4 X (c, b, a, d) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X c b a d]
  exact flg_mem_bcad X a b c d
/-- `brk4` of the permutation `cbda`. -/
theorem flg_mem_cbda (a b c d : X) : brk4 X (c, b, d, a) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X c b d a]
  exact flg_mem_bcda X a b c d
/-- `brk4` of the permutation `dabc`. -/
theorem flg_mem_dabc (a b c d : X) : brk4 X (d, a, b, c) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X d a b c]
  exact flg_mem_adbc X a b c d
/-- `brk4` of the permutation `dacb`. -/
theorem flg_mem_dacb (a b c d : X) : brk4 X (d, a, c, b) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X d a c b]
  exact flg_mem_adcb X a b c d
/-- `brk4` of the permutation `dbac`. -/
theorem flg_mem_dbac (a b c d : X) : brk4 X (d, b, a, c) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X d b a c]
  exact flg_mem_bdac X a b c d
/-- `brk4` of the permutation `dbca`. -/
theorem flg_mem_dbca (a b c d : X) : brk4 X (d, b, c, a) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X d b c a]
  exact flg_mem_bdca X a b c d
/-- `brk4` of the permutation `cdab`. -/
theorem flg_mem_cdab (a b c d : X) : brk4 X (c, d, a, b) ∈ flgS X a b c d := by
  rw [flg_brk4_jacobi X c d a b, flg_brk4_symm X c a d b, flg_brk4_symm X d a c b]
  exact Submodule.add_mem _ (flg_mem_acdb X a b c d) (flg_mem_adcb X a b c d)
/-- `brk4` of the permutation `cdba`. -/
theorem flg_mem_cdba (a b c d : X) : brk4 X (c, d, b, a) ∈ flgS X a b c d := by
  rw [flg_brk4_swap34 X c d b a, flg_brk4_symm X b a c d, flg_brk4_symm X b a d c]
  exact Submodule.add_mem _ (Submodule.add_mem _ (flg_mem_cdab X a b c d) (flg_mem_abcd X a b c d)) (flg_mem_abdc X a b c d)
/-- `brk4` of the permutation `dcab`. -/
theorem flg_mem_dcab (a b c d : X) : brk4 X (d, c, a, b) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X d c a b]
  exact flg_mem_cdab X a b c d
/-- `brk4` of the permutation `dcba`. -/
theorem flg_mem_dcba (a b c d : X) : brk4 X (d, c, b, a) ∈ flgS X a b c d := by
  rw [flg_brk4_symm X d c b a]
  exact flg_mem_cdba X a b c d
/-- The 24 permutations of `(a,b,c,d)` all have their `brk4` in `flgS X a b c d`. -/
theorem flg_brk4_perm_mem (a b c d x y z w : X)
    (h : ({x, y, z, w} : Finset X) = ({a, b, c, d} : Finset X))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    brk4 X (x, y, z, w) ∈ flgS X a b c d := by
  classical
  have hcard : ({x, y, z, w} : Finset X).card = 4 := by
    rw [h]
    exact Finset.card_eq_four.mpr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  obtain ⟨hxy, hxz, hxw, hyz, hyw, hzw⟩ := flg_distinct_of_card4 X hcard
  have hx : x = a ∨ x = b ∨ x = c ∨ x = d := by
    have hm : x ∈ ({x, y, z, w} : Finset X) := by simp
    rw [h] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hy : y = a ∨ y = b ∨ y = c ∨ y = d := by
    have hm : y ∈ ({x, y, z, w} : Finset X) := by simp
    rw [h] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hz : z = a ∨ z = b ∨ z = c ∨ z = d := by
    have hm : z ∈ ({x, y, z, w} : Finset X) := by simp
    rw [h] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hw : w = a ∨ w = b ∨ w = c ∨ w = d := by
    have hm : w ∈ ({x, y, z, w} : Finset X) := by simp
    rw [h] at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hx with hxa | hxb | hxc | hxd
  · rw [hxa] at hxy hxz hxw ⊢
    rcases hy with hya | hyb | hyc | hyd
    · rw [hya] at hxy hyz hyw ⊢
      exact absurd rfl hxy
    · rw [hyb] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzb] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzc] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwd] at hxw hyw hzw ⊢
          exact flg_mem_abcd X a b c d
      · rw [hzd] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwc] at hxw hyw hzw ⊢
          exact flg_mem_abdc X a b c d
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hzw
    · rw [hyc] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzb] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwd] at hxw hyw hzw ⊢
          exact flg_mem_acbd X a b c d
      · rw [hzc] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzd] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwb] at hxw hyw hzw ⊢
          exact flg_mem_acdb X a b c d
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hzw
    · rw [hyd] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzb] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwc] at hxw hyw hzw ⊢
          exact flg_mem_adbc X a b c d
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hyw
      · rw [hzc] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwb] at hxw hyw hzw ⊢
          exact flg_mem_adcb X a b c d
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hyw
      · rw [hzd] at hxz hyz hzw ⊢
        exact absurd rfl hyz
  · rw [hxb] at hxy hxz hxw ⊢
    rcases hy with hya | hyb | hyc | hyd
    · rw [hya] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzb] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzc] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwd] at hxw hyw hzw ⊢
          exact flg_mem_bacd X a b c d
      · rw [hzd] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwc] at hxw hyw hzw ⊢
          exact flg_mem_badc X a b c d
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hzw
    · rw [hyb] at hxy hyz hyw ⊢
      exact absurd rfl hxy
    · rw [hyc] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwd] at hxw hyw hzw ⊢
          exact flg_mem_bcad X a b c d
      · rw [hzb] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzc] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzd] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact flg_mem_bcda X a b c d
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hzw
    · rw [hyd] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwc] at hxw hyw hzw ⊢
          exact flg_mem_bdac X a b c d
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hyw
      · rw [hzb] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzc] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact flg_mem_bdca X a b c d
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hyw
      · rw [hzd] at hxz hyz hzw ⊢
        exact absurd rfl hyz
  · rw [hxc] at hxy hxz hxw ⊢
    rcases hy with hya | hyb | hyc | hyd
    · rw [hya] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzb] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwd] at hxw hyw hzw ⊢
          exact flg_mem_cabd X a b c d
      · rw [hzc] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzd] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwb] at hxw hyw hzw ⊢
          exact flg_mem_cadb X a b c d
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hzw
    · rw [hyb] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwd] at hxw hyw hzw ⊢
          exact flg_mem_cbad X a b c d
      · rw [hzb] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzc] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzd] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact flg_mem_cbda X a b c d
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hzw
    · rw [hyc] at hxy hyz hyw ⊢
      exact absurd rfl hxy
    · rw [hyd] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwb] at hxw hyw hzw ⊢
          exact flg_mem_cdab X a b c d
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hyw
      · rw [hzb] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact flg_mem_cdba X a b c d
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hxw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hyw
      · rw [hzc] at hxz hyz hzw ⊢
        exact absurd rfl hxz
      · rw [hzd] at hxz hyz hzw ⊢
        exact absurd rfl hyz
  · rw [hxd] at hxy hxz hxw ⊢
    rcases hy with hya | hyb | hyc | hyd
    · rw [hya] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzb] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwc] at hxw hyw hzw ⊢
          exact flg_mem_dabc X a b c d
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hxw
      · rw [hzc] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwb] at hxw hyw hzw ⊢
          exact flg_mem_dacb X a b c d
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hxw
      · rw [hzd] at hxz hyz hzw ⊢
        exact absurd rfl hxz
    · rw [hyb] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwc] at hxw hyw hzw ⊢
          exact flg_mem_dbac X a b c d
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hxw
      · rw [hzb] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzc] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact flg_mem_dbca X a b c d
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hxw
      · rw [hzd] at hxz hyz hzw ⊢
        exact absurd rfl hxz
    · rw [hyc] at hxy hyz hyw ⊢
      rcases hz with hza | hzb | hzc | hzd
      · rw [hza] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwb] at hxw hyw hzw ⊢
          exact flg_mem_dcab X a b c d
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hxw
      · rw [hzb] at hxz hyz hzw ⊢
        rcases hw with hwa | hwb | hwc | hwd
        · rw [hwa] at hxw hyw hzw ⊢
          exact flg_mem_dcba X a b c d
        · rw [hwb] at hxw hyw hzw ⊢
          exact absurd rfl hzw
        · rw [hwc] at hxw hyw hzw ⊢
          exact absurd rfl hyw
        · rw [hwd] at hxw hyw hzw ⊢
          exact absurd rfl hxw
      · rw [hzc] at hxz hyz hzw ⊢
        exact absurd rfl hyz
      · rw [hzd] at hxz hyz hzw ⊢
        exact absurd rfl hxz
    · rw [hyd] at hxy hyz hyw ⊢
      exact absurd rfl hxy



end FourLetters

/-! ## The two-orbit case: the four-letter computation -/

section FourLettersMain

variable (X : Type) [DecidableEq X]

theorem flg_letters4_eq_insert (t : X × X × X × X) :
    flg_letters4 t = ({t.1, t.2.1, t.2.2.1, t.2.2.2} : Finset X) := by
  ext y
  simp only [flg_letters4, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem flg_sigmaA_brk (σ : X ≃ X)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ p q, σA (p * q) = σA p * σA q)
    (p q : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    σA (brk X p q) = brk X (σA p) (σA q) := by
  simp only [brk, map_add, hmul]

theorem flg_add_self_add {A : Type*} [Ring A] [Algebra (ZMod 2) A] (t : A) :
    t + (t + t) = t := by
  rw [flg_add_self, add_zero]

theorem flg_brk_mem_Tsub (p q : X) : brk X (flg_ltr X p) (flg_ltr X q) ∈ Tsub X := by
  have key : ∀ r s : X,
      (fun r : X × X => MonoidAlgebra.single (FreeMonoid.of r.1) (1 : ZMod 2)
        * MonoidAlgebra.single (FreeMonoid.of r.1) 1
      + (MonoidAlgebra.single (FreeMonoid.of r.2) 1 * MonoidAlgebra.single (FreeMonoid.of r.1) 1
        + MonoidAlgebra.single (FreeMonoid.of r.1) 1 * MonoidAlgebra.single (FreeMonoid.of r.2) 1))
      (r, s) ∈ Tsub X := fun r s => Submodule.subset_span ⟨(r, s), rfl⟩
  have hA : flg_ltr X p * flg_ltr X p ∈ Tsub X := by
    have hg := key p p
    convert hg using 1
    simp only [flg_ltr]
    rw [flg_add_self_add]
  have hpq : flg_ltr X p * flg_ltr X p + brk X (flg_ltr X p) (flg_ltr X q) ∈ Tsub X := by
    have hg := key p q
    convert hg using 1
    simp only [flg_ltr, brk]
    abel
  have hbr := Submodule.sub_mem _ hpq hA
  convert hbr using 1
  abel

end FourLettersMain

section FourLettersFinal

variable (X : Type) [DecidableEq X] (σ : X ≃ X) (hσ : ∀ y, σ (σ y) = y)
  (a b c d : X) (ha : σ a = b) (hc : σ c = d)
  (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
  (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X))
  (hmul : ∀ p q, σA (p * q) = σA p * σA q) (hone : σA 1 = 1)
  (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
    = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1)

local instance : DecidableEq (FreeMonoid X) := FreeMonoid.toList.injective.decidableEq

/-- The word `abcd`. -/
noncomputable def flgW1 : FreeMonoid X :=
  FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of c * FreeMonoid.of d
/-- The word `abdc`. -/
noncomputable def flgW2 : FreeMonoid X :=
  FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of d * FreeMonoid.of c
/-- The word `acbd`. -/
noncomputable def flgW3 : FreeMonoid X :=
  FreeMonoid.of a * FreeMonoid.of c * FreeMonoid.of b * FreeMonoid.of d

include hσ ha hc hab hcd hac had hbc hbd hmul hone hgen in
theorem flg_four_letters_local (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hu : u ∈ Wsub X)
    (hfix : σA u = u)
    (hsupp : ∀ w : FreeMonoid X, u.coeff w ≠ 0 →
      (∀ y ∈ w.toList, y = a ∨ y = b ∨ y = c ∨ y = d) ∧
      a ∈ w.toList ∧ b ∈ w.toList ∧ c ∈ w.toList ∧ d ∈ w.toList) :
    ∃ w ∈ Wsub X, u - (w + σA w) ∈ flgThetaSpan X σA := by
  classical
  have hb : σ b = a := by rw [← ha, hσ a]
  have hd : σ d = c := by rw [← hc, hσ c]
  have cw1_0 : (flgBV X a b c d 0).coeff (flgW1 X a b c d) = 1 := by
    rw [show (flgBV X a b c d 0 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, b, c, d)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW1]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw1_1 : (flgBV X a b c d 1).coeff (flgW1 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 1 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, b, d, c)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW1]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw1_2 : (flgBV X a b c d 2).coeff (flgW1 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 2 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, c, b, d)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW1]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw1_3 : (flgBV X a b c d 3).coeff (flgW1 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 3 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, c, d, b)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW1]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw1_4 : (flgBV X a b c d 4).coeff (flgW1 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 4 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, d, b, c)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW1]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw1_5 : (flgBV X a b c d 5).coeff (flgW1 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 5 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, d, c, b)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW1]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw2_0 : (flgBV X a b c d 0).coeff (flgW2 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 0 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, b, c, d)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW2]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw2_1 : (flgBV X a b c d 1).coeff (flgW2 X a b c d) = 1 := by
    rw [show (flgBV X a b c d 1 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, b, d, c)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW2]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw2_2 : (flgBV X a b c d 2).coeff (flgW2 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 2 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, c, b, d)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW2]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw2_3 : (flgBV X a b c d 3).coeff (flgW2 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 3 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, c, d, b)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW2]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw2_4 : (flgBV X a b c d 4).coeff (flgW2 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 4 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, d, b, c)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW2]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw2_5 : (flgBV X a b c d 5).coeff (flgW2 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 5 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, d, c, b)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW2]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw3_0 : (flgBV X a b c d 0).coeff (flgW3 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 0 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, b, c, d)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW3]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw3_1 : (flgBV X a b c d 1).coeff (flgW3 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 1 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, b, d, c)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW3]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw3_2 : (flgBV X a b c d 2).coeff (flgW3 X a b c d) = 1 := by
    rw [show (flgBV X a b c d 2 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, c, b, d)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW3]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw3_3 : (flgBV X a b c d 3).coeff (flgW3 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 3 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, c, d, b)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW3]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw3_4 : (flgBV X a b c d 4).coeff (flgW3 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 4 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, d, b, c)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW3]
    simp [hab, hac, had, hbc, hbd, hcd]
  have cw3_5 : (flgBV X a b c d 5).coeff (flgW3 X a b c d) = 0 := by
    rw [show (flgBV X a b c d 5 : MonoidAlgebra (ZMod 2) (FreeMonoid X)) = brk4 X (a, d, c, b)
      from by simp [flgBV]]
    rw [flg_brk4_expand]
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, flg_word4_eq_iff, flgW3]
    simp [hab, hac, had, hbc, hbd, hcd]
  exact flg_four_letters X σ hσ a b c d ha hc hab hcd hac had hbc hbd σA hmul hone hgen
    u hu hfix hsupp

end FourLettersFinal

end Work.SSGRoute.CC
