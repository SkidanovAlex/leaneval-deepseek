import Mathlib
import Submission.Work.Fitting.Main
import Submission.Work.ThmF.ChV12.Fitting_cyclic_fpf
import Submission.Work.ThmF.ChV12.fitting_card_lt_centralizer
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.centralizer_irreducible_isCyclic
import Submission.Work.ThmF.ChV12.transitive_orbit_basics
import Submission.Work.ThmF.ChV12.solvable_of_cyclic_normal_irreducible
import Submission.Work.PGroup.exists_prime_orderOf_two_eq
import Submission.Work.ThmF.ChV12.solvable_of_transitive_two_pow_six
import Submission.Work.ThmF.ChV12.solvable_of_transitive_of_odd_order
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12
-- **(2026-10-07, area owner).**  Per the lead's ruling the odd-order theorem may be assumed,
-- so this node carries `(hFT : FeitThompsonProp)`; the FT-free route survives as the
-- `PpdClosureProp`/`TransitiveLinearSolvable` definitions (`ChV12/ppdClosureProp_holds.lean`).


/-!
# `F(D)` acts irreducibly on `A`

`A` is a finite elementary abelian 2-group and `D` a finite group of odd order acting faithfully
(`ρ`) and transitively on `A ∖ {1}`.  The claim is that every nonzero `F(D)`-invariant subgroup of
`A` is all of `A`, i.e. that the Fitting subgroup acts **irreducibly**.

## The reduction (Feit--Thompson-free, complete)

* `Work.ThmF.ChV12.Fitting_cyclic_fpf` (Huppert's Appendix X): `F(D)` is cyclic and acts
  fixed-point-freely on `A`.
* Fitting's theorem (`Work.Fitting.centralizer_fitting_le`): `C_D(F(D)) ≤ F(D)` for *solvable* `D`.
* The orbit count (`Work.ThmF.ChV12.fitting_card_lt_centralizer`): a nonzero **proper**
  `F(D)`-invariant subgroup forces `|F(D)| < |C_D(F(D))|`.

Consequently, for `|A| ≥ 4`,

  `F(D)` is irreducible  ⟺  `D` is solvable.

(`⟸`: Fitting's theorem contradicts the orbit count, `fitting_irreducible_of_transitive_of_solvable`.
 `⟹`: `F(D)` irreducible makes `A` one-dimensional over the field `𝔽₂[F(D)] ≅ 𝔽_{2^k}`, so
 `C_D(F(D))` is cyclic, while `D / C_D(F(D)) ↪ Aut(F(D))` is abelian; hence `D` is metabelian.)

So the whole content of the theorem is

  **Zassenhaus/Hering, characteristic 2**: an odd-order group acting faithfully and transitively
  on the nonidentity elements of an elementary abelian 2-group is solvable.

This is the classical input that Feit--Thompson would give immediately (odd order ⇒ solvable); it
is the residual input `Work.ThmF.ChV12.TransitiveLinearSolvable` of `JformReduction.lean`
(hypothesis *type I* of Huppert--Blackburn III, XII §9.2), isolated here as
`Work.ThmF.ChV12.solvable_of_transitive_of_odd_order`.

## The Feit--Thompson-free route to the input, and where it stands

Writing `|A| = 2 ^ k`, the plan for `k ≥ 2` is

* if `k ≠ 6`, `2 ^ k - 1` has a primitive prime divisor `q`
  (`Work.PGroup.exists_prime_order_of_two_eq` — **proved**, Bang–Zsigmondy for base `2`);
  an element `x` of order `q` acts irreducibly (`Work.ThmF.ChV12.irreducible_of_orderOf_prime`) and
  `C_D(x)` is cyclic (`Work.ThmF.ChV12.centralizer_irreducible_isCyclic`).  The remaining step is
  that `⟨x⟩` is *normal* in `D` — equivalently that the Sylow `q`-subgroups of `D` are normal
  (`Work.ThmF.ChV12.pCore_ne_bot_of_primitive_prime`).  Note `O_q(D) ≤ F(D)` because `O_q(D)` is a
  normal nilpotent subgroup, and `q ∤ |F(D)|` as soon as `F(D)` is reducible; hence this step is
  *equivalent* to the input above and cannot be obtained independently of it;
* if `k = 6` (`2 ^ 6 - 1 = 63 = 3 ^ 2 · 7` has no primitive prime divisor), the same input is
  needed (`Work.ThmF.ChV12.solvable_of_transitive_two_pow_six`), e.g. via an element of order `9`
  (`ord_9(2) = 6`) or via the order-`7` fixed-space analysis.

The workspace isolates the same gap in its pure group-theoretic form as

```lean
Work.ThmF.ChV12.odd_ppd_normalizes :
  ∀ g ∈ G, ∃ i : ℤ, g * σ * g⁻¹ = σ ^ i        (`G ≤ MulAut A` odd order, `orderOf σ = q`)
```

(`Submission/Work/ThmF/ChV12/odd_ppd_normalizes.lean`, still a `sorry`), the natural home of the
step above: `⟨σ⟩ ⊴ G` is exactly `n_q = 1` for the Sylow `q`-subgroups.  The route to it that the
present file sets up is: `C_G(σ) ≤ 𝔽₂[σ]ˣ` (cyclic, order `2^k - 1`, proved as
`centralizer_irreducible_isCyclic`), `N_G(⟨σ⟩)/C_G(σ) ↪ C_k`, all order-`q` subgroups of `G` are
conjugate (`exists_conj_zpowers_of_card_eq_prime`, proved), `n_q ≡ 1 [MOD q]`, and
`|G| = n_q · |N_G(⟨σ⟩)| ≤ n_q · k · (2^k - 1)`.
-/

/-- **In the reducible case `D` cannot be solvable.**

A nonzero *proper* `F(D)`-invariant subgroup forces `|F(D)| < |C_D(F(D))|`
(`Work.ThmF.ChV12.fitting_card_lt_centralizer`), while a *solvable* `D` satisfies
`C_D(F(D)) ≤ F(D)` (Fitting's theorem, `Work.Fitting.centralizer_fitting_le`).  Hence any
counterexample to `fitting_irreducible_of_transitive` consists of a **non-solvable** group of odd
order. -/
theorem not_solvable_of_reducible_fitting {A D : Type} [Group A] [Group D] [Finite A]
    [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b)
    (hW : ∃ W : Subgroup A, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ t ∈ Work.Fitting.fitting D, ∀ x : A, x ∈ W → ρ t x ∈ W)) :
    ¬ Group.IsSolvable D := by
  intro hsol
  haveI : Group.IsSolvable D := hsol
  have hle : Nat.card ↥(Subgroup.centralizer (Work.Fitting.fitting D : Set D))
      ≤ Nat.card ↥(Work.Fitting.fitting D) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective
      (Work.Fitting.centralizer_fitting_le D))
  have hlt := fitting_card_lt_centralizer hA2 hAc hodd ρ hfaith htrans hW
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

/-- **The target, given solvability of `D`.**  Everything except solvability of the odd-order
group `D` is in place: if `D` is solvable, Fitting's theorem contradicts the orbit count. -/
theorem fitting_irreducible_of_transitive_of_solvable {A D : Type} [Group A] [Group D]
    [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b)
    (hsol : Group.IsSolvable D) :
    ∀ W : Subgroup A, W ≠ ⊥ →
      (∀ t ∈ Work.Fitting.fitting D, ∀ x ∈ W, ρ t x ∈ W) → W = ⊤ := by
  classical
  haveI : Group.IsSolvable D := hsol
  intro W hWne hWin
  by_contra hWtop
  have hwit : ∃ W : Subgroup A, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ t ∈ Work.Fitting.fitting D, ∀ x : A, x ∈ W → ρ t x ∈ W) :=
    ⟨W, hWne, hWtop, fun t ht x hx => hWin t ht x hx⟩
  have hle : Nat.card ↥(Subgroup.centralizer (Work.Fitting.fitting D : Set D))
      ≤ Nat.card ↥(Work.Fitting.fitting D) :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective
      (Work.Fitting.centralizer_fitting_le D))
  have hlt := fitting_card_lt_centralizer hA2 hAc hodd ρ hfaith htrans hwit
  exact absurd (lt_of_lt_of_le hlt hle) (lt_irrefl _)

/-- **The target, given Feit–Thompson.**  The project's sanctioned black box
`Submission.Blueprint.FeitThompsonProp` supplies solvability of the odd-order group `D`, and
then `fitting_irreducible_of_transitive_of_solvable` gives the requested statement. -/
theorem fitting_irreducible_of_transitive_of_FT (hFT : Submission.Blueprint.FeitThompsonProp)
    {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    ∀ W : Subgroup A, W ≠ ⊥ →
      (∀ t ∈ Work.Fitting.fitting D, ∀ x ∈ W, ρ t x ∈ W) → W = ⊤ :=
  fitting_irreducible_of_transitive_of_solvable hA2 hAc hodd ρ hfaith htrans (hFT D hodd)

/-- **`F(D)` acts irreducibly on `A`.**  The Fitting subgroup of the odd-order group `D` is
irreducible on every nonzero `F(D)`-invariant subgroup. -/
theorem fitting_irreducible_of_transitive (hFT : Submission.Blueprint.FeitThompsonProp) {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    ∀ W : Subgroup A, W ≠ ⊥ →
      (∀ t ∈ Work.Fitting.fitting D, ∀ x ∈ W, ρ t x ∈ W) → W = ⊤ := by
  obtain ⟨k, hk⟩ := card_eq_two_pow_of_mul_self_eq_one hA2
  rcases lt_or_ge k 2 with hklt | hkge
  · -- `|A| ≤ 2`, so a nonzero subgroup of `A` is all of `A`
    intro W hWne _
    have hle : Nat.card W ≤ 2 := by
      have h1 : Nat.card W ∣ 2 ^ k := by
        rw [← hk]; exact Subgroup.card_subgroup_dvd_card W
      have h2 : Nat.card W ≤ 2 ^ k :=
        Nat.le_of_dvd (pow_pos (by norm_num : (0 : ℕ) < 2) k) h1
      have h3 : (2 : ℕ) ^ k ≤ 2 := by interval_cases k <;> norm_num
      omega
    have hge : 2 ≤ Nat.card W := by
      obtain ⟨a, haW, ha1⟩ : ∃ a ∈ W, a ≠ 1 := by
        by_contra h
        exact hWne (bot_unique (fun x hx => by
          rw [Subgroup.mem_bot]
          by_contra hx1
          exact h ⟨x, hx, hx1⟩))
      have hord : orderOf (⟨a, haW⟩ : W) ≠ 1 := by
        rw [← Subgroup.orderOf_coe]
        intro h
        exact ha1 (orderOf_eq_one_iff.mp h)
      have hdvd' : orderOf (⟨a, haW⟩ : W) ∣ Nat.card W := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_subgroup_dvd_card _
      have hle' : orderOf (⟨a, haW⟩ : W) ≤ Nat.card W :=
        Nat.le_of_dvd Nat.card_pos hdvd'
      have hlt1 : 1 < orderOf (⟨a, haW⟩ : W) :=
        lt_of_le_of_ne (orderOf_pos _) (Ne.symm hord)
      omega
    have hWA : Nat.card W ≤ Nat.card A := by
      haveI : Fintype W := Fintype.ofFinite W
      haveI : Fintype A := Fintype.ofFinite A
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    have hA2' : Nat.card A ≤ 2 := by
      rw [hk]
      interval_cases k <;> norm_num
    have hW2 : Nat.card W = 2 := le_antisymm hle hge
    have hAcard2 : Nat.card A = 2 := le_antisymm hA2' (le_trans hge hWA)
    exact Subgroup.eq_top_of_card_eq W (by rw [hW2, hAcard2])
  · -- `2 ≤ k`: it suffices to know that the odd-order group `D` is solvable
    -- **(2026-10-07, area owner, second pass.)**  Solvability is `FeitThompsonProp` at `↥D`
    -- verbatim; the `ppd`/Zassenhaus detour through `solvable_of_transitive_of_odd_order` and
    -- `solvable_of_transitive_two_pow_six` belongs to the Feit–Thompson-free route (out of scope).
    have hsol : Group.IsSolvable D := hFT D hodd
    exact fitting_irreducible_of_transitive_of_solvable hA2 hAc hodd ρ hfaith htrans hsol

end Work.ThmF.ChV12
