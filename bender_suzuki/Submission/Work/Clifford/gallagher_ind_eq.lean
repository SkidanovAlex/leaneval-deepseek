import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.gallagher_ind_eq`

**Gallagher's formula** in the form that a character `θ` of a normal subgroup `N ⊴ G` which
*extends* to `χ ∈ Irr G` induces to the sum of the `χ`-twists of the regular character of the
quotient:

`Ind_N^G θ = ∑_{β ∈ Irr(G/N)} β(1) · (χ · infl β)`.

The proof is short once the two sides are evaluated pointwise.

* On `N` the defining sum of `Ind_N^G θ` runs over all of `G` (normality), every term equals
  `θ n = χ n`, and the factor `|N|⁻¹` turns `|G| · χ n` into `[G : N] · χ n`.  Off `N` no
  conjugate of `x` lies in `N`, so the induced function vanishes.

* The right hand side at `x` is `χ x` times `∑_{β ∈ Irr(G/N)} β(1) β(xN)`, which is the value
  at `xN` of the regular character of `G ⧸ N` — i.e. `|G ⧸ N|` for `x ∈ N` and `0` otherwise
  (`sum_irr_deg_mul_apply`, an immediate consequence of
  `Work.CharCore.regularChar_eq_sum`).

So both sides equal `χ x · |G ⧸ N|` on `N` and `0` off `N`.

Note the hypothesis `θ ∈ Irr N` is not needed: the identity holds for any `θ` that is the
restriction of a class function `χ` — irreducibility of `χ` enters only through `χ` being a
class function.
-/

noncomputable section

open Classical
open scoped Classical

namespace Work.Clifford

/-! ### The regular character as a sum over the irreducible characters -/

/-- **The value of the regular character**, in the form used below: for a finite group `H` and
`h : H`, `∑_{β ∈ Irr H} β(1) · β h` is `|H|` if `h = 1` and `0` otherwise.  This is
`Work.CharCore.regularChar_eq_sum` evaluated at `h`, with the multiplicities `irrDeg β` read as
the degrees `β 1`. -/
theorem sum_irr_deg_mul_apply {H : Type*} [Group H] [Fintype H] (h : H) :
    ∑ β ∈ Work.CharCore.Irr H, (β 1) * β h =
      if h = 1 then (Nat.card H : ℂ) else 0 := by
  classical
  have hreg := congrFun (Work.CharCore.regularChar_eq_sum (G := H)) h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hreg
  simp only [Work.CharCore.regularChar] at hreg
  have hsum : (∑ β ∈ Work.CharCore.Irr H, (β 1) * β h)
      = ∑ β ∈ Work.CharCore.Irr H, ((Work.CharCore.irrDeg β : ℂ)) * β h :=
    Finset.sum_congr rfl fun β hβ => by rw [Work.CharCore.irrDeg_spec hβ]
  rw [hsum, ← hreg]

/-- The value of the regular character at `1`. -/
theorem sum_irr_deg_mul_apply_one {H : Type*} [Group H] [Fintype H] :
    ∑ β ∈ Work.CharCore.Irr H, (β 1) * β (1 : H) = (Nat.card H : ℂ) := by
  rw [sum_irr_deg_mul_apply (H := H) 1, ite_eq_left rfl]

/-- The value of the regular character at `h ≠ 1`. -/
theorem sum_irr_deg_mul_apply_ne_one {H : Type*} [Group H] [Fintype H] {h : H} (hh : h ≠ 1) :
    ∑ β ∈ Work.CharCore.Irr H, (β 1) * β h = 0 := by
  rw [sum_irr_deg_mul_apply (H := H) h, ite_eq_right hh]

/-! ### Gallagher's formula -/

theorem gallagher_ind_eq {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal] [Fintype N]
    [Fintype (G ⧸ N)]
    {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G)
    (hext : Work.Clifford.Extends N χ θ) :
    Work.Clifford.indFun N θ
      = ∑ β ∈ Work.CharCore.Irr (G ⧸ N), (β 1) • (χ * Work.Clifford.inflateFun N β) := by
  classical
  have hch : Work.Clifford.IsClassFun χ := Work.Clifford.IsClassFun.of_mem_Irr hχ
  -- irreducibility of `θ` is used only to record it as a class function
  have hθcf : Work.Clifford.IsClassFun θ := Work.Clifford.IsClassFun.of_mem_Irr hθ
  -- `θ` is the restriction of `χ`
  have hθχ : ∀ z : N, θ z = χ (z : G) := fun z => (congrFun hext z).symm
  funext g
  -- the right hand side at `g`, with the factor `χ g` taken out
  have hRHS : (∑ β ∈ Work.CharCore.Irr (G ⧸ N), (β 1) • (χ * Work.Clifford.inflateFun N β)) g
      = χ g * (∑ β ∈ Work.CharCore.Irr (G ⧸ N), (β 1) * β (QuotientGroup.mk g)) := by
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by
      simp only [Pi.smul_apply, Pi.mul_apply, Work.Clifford.inflateFun, smul_eq_mul]
      ring
  rw [hRHS]
  by_cases hg : g ∈ N
  · -- `g ∈ N`: the induced function is `[G : N] · χ g` and the regular character is `|G ⧸ N|`
    have hmk : (QuotientGroup.mk g : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    rw [hmk, sum_irr_deg_mul_apply_one]
    have hsum : (∑ x : G, (if hx : x * g * x⁻¹ ∈ N then θ ⟨x * g * x⁻¹, hx⟩ else 0))
        = (Fintype.card G : ℂ) * χ g := by
      have hterm : ∀ x : G,
          (if hx : x * g * x⁻¹ ∈ N then θ ⟨x * g * x⁻¹, hx⟩ else 0) = χ g := by
        intro x
        rw [dite_eq_left ((inferInstance : N.Normal).conj_mem g hg x), hθχ]
        exact hch g x
      rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ]
    have hcard : (Nat.card N : ℂ)⁻¹ * ((Fintype.card G : ℂ) * χ g)
        = (Nat.card (G ⧸ N) : ℂ) * χ g := by
      have hG : (Nat.card G : ℂ) = (Nat.card (G ⧸ N) : ℂ) * (Nat.card N : ℂ) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.cast_mul]
      rw [← Nat.card_eq_fintype_card (α := G), hG]
      field_simp
    simp only [Work.Clifford.indFun]
    rw [hsum, hcard]
    ring
  · -- `g ∉ N`: the induced function vanishes, and so does the regular character at `gN ≠ 1`
    have hmk : (QuotientGroup.mk g : G ⧸ N) ≠ 1 := fun h => hg ((QuotientGroup.eq_one_iff g).mp h)
    rw [sum_irr_deg_mul_apply_ne_one hmk, mul_zero]
    have hterm : ∀ x : G,
        (if hx : x * g * x⁻¹ ∈ N then θ ⟨x * g * x⁻¹, hx⟩ else 0) = 0 := by
      intro x
      rw [dite_eq_right]
      intro hx
      exact hg (by
        have h : x⁻¹ * (x * g * x⁻¹) * (x⁻¹)⁻¹ ∈ N :=
          (inferInstance : N.Normal).conj_mem (x * g * x⁻¹) hx x⁻¹
        rwa [show x⁻¹ * (x * g * x⁻¹) * (x⁻¹)⁻¹ = g from by group] at h)
    simp only [Work.Clifford.indFun]
    rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const_zero, mul_zero]

end Work.Clifford
