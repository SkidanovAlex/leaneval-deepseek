import Mathlib
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.szTilde_sq
import Submission.Work.ZassenhausSuzuki.szTilde_conj
import Submission.Work.ZassenhausSuzuki.SzAField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Reflections of two central involutions in the `θ`-fixed torus commute (BG 5.14, first half)

Let `G` carry a split rank-one Zassenhaus configuration `H = Q ⋊ D` with root group
`Q ≃* A(K,θ) = SzA K θ` (`K = GF(2^m)`, `θ ≠ 1` of odd order) through which `D = twoPoint H t`
acts by the standard torus `Λ = h(Kˣ)` (`htorus`), and let `∼ = szTilde hsplit` be the Suzuki
reflection map of the root group (`∼ x = g (g x)⁻¹`, BG 3.1 (j), `SzTildeDefs.lean`).

This file computes the reflection of a *central* involution of `Q` far enough to compare the
reflections of the two points `e.symm ⟨0,1⟩` and `e.symm (h_λ ⟨0,1⟩)` when `θ λ = λ`:

* `szTilde_coord_sq`: if `e a = ⟨0,b⟩` (`b ≠ 0`) then `e (∼ a) = ⟨c, ∗⟩` with `c · θ c = b`
  — the `e`-image of the square rule `(∼ a)² = a` (`szTilde_sq` = BG 5.13) together with
  `x * x = ⟨0, x.a · θ x.a⟩` in `A(K,θ)`;
* `szTilde_comm_of_fix`: for `θ λ = λ`, `λ ≠ 0, 1`, the reflections of `e.symm ⟨0,1⟩`
  (whose first coordinate is `1`, since `c·θc = 1` forces `c = 1`) and of
  `e.symm (h_λ ⟨0,1⟩)` (whose first coordinate is `λ`, since `c·θc = λ·θλ` and `x ↦ x·θx` is
  injective) commute — by the commutation criterion `szA_comm_iff` in `A(K,θ)`.

This is the first half of BG Lemma 5.14 (a) / Suzuki 1962 §11 (`szClassNumber_fixTheta`):
for `λ ∈ Fix θ ∖ {1}` the pair `(∼ e, ∼ e h_λ)` commutes, so that
`w⁻¹ · (∼ e) · (∼ e h_λ) ∈ Z(Q)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- **The `e`-coordinates of the reflection of a central involution.**  If `a ∈ Q` satisfies
`e a = ⟨0, b⟩` with `b ≠ 0` (i.e. `a` is a non-trivial involution of the root group, hence
central in `Q`), then the first coordinate `c` of `e (∼ a)` satisfies `c · θ c = b`: this is
the `e`-image of the square rule `(∼ a)² = a` (`szTilde_sq`, BG 5.13) combined with
`x * x = ⟨0, x.a · θ x.a⟩` in `A(K,θ)`. -/
lemma szTilde_coord_sq (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {a : Q} {b : GaloisField 2 m}
    (ha : e a = (⟨0, b⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) (hb : b ≠ 0) :
    (e (Work.ZassenhausSuzuki.szTilde hsplit a)).a
        * θ ((e (Work.ZassenhausSuzuki.szTilde hsplit a)).a) = b := by
  classical
  have ha0 : (e a).a = 0 := by rw [ha]
  have ha1 : e a ≠ 1 := by
    rw [ha]
    intro h
    exact hb (by simpa using congrArg Work.ZassenhausSuzuki.SzA.b h)
  have h := congrArg (fun z : Q => e z)
    (szTilde_sq hsplit hzass hθ1 hθodd htorus (a := a) ha0 ha1)
  rw [map_mul] at h
  rw [ha, Work.ZassenhausSuzuki.SzA.sq_eq θ] at h
  have hb' := congrArg Work.ZassenhausSuzuki.SzA.b h
  simpa using hb'

theorem szTilde_comm_of_fix {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {lam : GaloisField 2 m} (hfix : θ lam = lam) (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1) :
    Work.ZassenhausSuzuki.szTilde hsplit (e.symm (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA
        (GaloisField 2 m) θ))
      * Work.ZassenhausSuzuki.szTilde hsplit (e.symm (Work.ZassenhausSuzuki.SzA.hLam θ lam
          (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)))
    = Work.ZassenhausSuzuki.szTilde hsplit (e.symm (Work.ZassenhausSuzuki.SzA.hLam θ lam
          (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)))
      * Work.ZassenhausSuzuki.szTilde hsplit (e.symm (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA
          (GaloisField 2 m) θ)) := by
  classical
  -- The two points of the root group whose reflections are compared.
  set A : Q := e.symm (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) with hA
  set B : Q := e.symm (Work.ZassenhausSuzuki.SzA.hLam θ lam
    (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) with hB
  have heA : e A = (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    rw [hA, MulEquiv.apply_symm_apply]
  have heB : e B = (⟨0, lam * θ lam⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    rw [hB, MulEquiv.apply_symm_apply]
    ext <;> simp [Work.ZassenhausSuzuki.SzA.hLam_a, Work.ZassenhausSuzuki.SzA.hLam_b]
  have hθlam0 : θ lam ≠ 0 := fun h => hlam0 (θ.injective (by rw [h, map_zero]))
  -- The first coordinates of the two reflections: `1` and `lam`.
  have hua : (e (szTilde hsplit A)).a = 1 := by
    have hc := szTilde_coord_sq hsplit hzass hθ1 hθodd htorus (a := A) (b := 1) heA one_ne_zero
    refine eq_one_of_mul_map_eq_one θ hθodd (a := (e (szTilde hsplit A)).a) ?_ hc
    intro h0
    rw [h0, zero_mul] at hc
    exact one_ne_zero hc.symm
  have hvb : (e (szTilde hsplit B)).a = lam := by
    refine mul_theta_injective θ hθodd ?_
    exact szTilde_coord_sq hsplit hzass hθ1 hθodd htorus (a := B) (b := lam * θ lam) heB
      (mul_ne_zero hlam0 hθlam0)
  -- The commutation criterion in `A(K,θ)`: `⟨1,∗⟩` commutes with `⟨λ,∗⟩` when `θ λ = λ`.
  have hcomm : e (szTilde hsplit A) * e (szTilde hsplit B)
      = e (szTilde hsplit B) * e (szTilde hsplit A) := by
    refine (szA_comm_iff θ _ _).mpr ?_
    rw [hua, hvb, map_one, one_mul, mul_one]
    exact hfix
  apply e.injective
  rw [map_mul, map_mul]
  exact hcomm

end Work.ZassenhausSuzuki
