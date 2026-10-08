import Mathlib
import Submission.Work.Frobenius.Induced.ConjChar

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The restriction of an induced class function to the normal subgroup

Let `K ⊴ G` be a normal subgroup and `H ≤ G` a complement of `K`
(`Subgroup.IsComplement' K H`: every `g : G` is uniquely a product `k * h` with `k ∈ K`,
`h ∈ H`).  For a class function `θ : K → ℂ` we compute the restriction of the induced
class function `indFun K θ` back to `K`:

`(Ind_K^G θ)|_K = ∑_{h ∈ H} θ^h`,

the sum of the `H`-conjugates `θ^h = conjChar K h θ` of `θ`.

Indeed, for `k ∈ K` normality of `K` makes every conjugate `x * k * x⁻¹` land in `K`, so

`Ind_K^G θ k = |K|⁻¹ * ∑_{x : G} θ (x k x⁻¹)`,

and writing `x = a * b` with `a ∈ K`, `b ∈ H` (using the complement) the class-function
property of `θ` turns the summand into `θ (b k b⁻¹) = conjChar K b θ k`.  Each `b : H`
therefore occurs `|K|` times, and the normalising factor `|K|⁻¹` cancels.

This is the input to `Work.Frobenius.Induced.frobenius_induced_irr`.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius.Induced

variable {G : Type*} [Group G]

/-- Conjugation by an element `a ∈ K` of a normal subgroup fixes every class function on `K`:
`(θ^a) = θ`. -/
theorem conjChar_eq_of_mem {K : Subgroup G} [K.Normal] {θ : K → ℂ} (hθ : IsClassFun θ)
    {a : G} (ha : a ∈ K) : conjChar K a θ = θ := by
  funext k
  exact hθ k ⟨a, ha⟩

variable [Fintype G]

/-- **Value of an induced function at an element of the normal subgroup.**  For `K ⊴ G`,
`k ∈ K` and any function `θ : K → ℂ`, `|K| * Ind_K^G θ k = ∑_{x : G} θ (x k x⁻¹)`: by
normality of `K` every conjugate `x * k * x⁻¹` lies in `K`, so no term of the defining sum
of `indFun` vanishes. -/
theorem card_mul_indFun_apply_of_normal {K : Subgroup G} [K.Normal] (θ : K → ℂ) (k : K) :
    (Nat.card K : ℂ) * indFun K θ (k : G) = ∑ x : G, conjChar K x θ k := by
  have hne : (Nat.card K : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  rw [indFun, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dite_eq_left ((inferInstance : K.Normal).conj_mem (k : G) k.2 x)]
  rfl

/-- **Decomposition of the orbit sum over the complement.**  If `H` is a complement of the
normal subgroup `K` and `θ` is a class function on `K`, then for `k ∈ K`
`∑_{x : G} θ (x k x⁻¹) = |K| * ∑_{h ∈ H} θ (h k h⁻¹)`: the terms only depend on the
`H`-component of `x` (the `K`-component is absorbed by the class-function property), and
each `h ∈ H` occurs once for every element of `K`. -/
theorem conjChar_sum_eq_card_mul {K H : Subgroup G} [K.Normal] [Fintype H]
    (hcomp : Subgroup.IsComplement' K H) {θ : K → ℂ} (hθ : IsClassFun θ) (k : K) :
    ∑ x : G, conjChar K x θ k = (Nat.card K : ℂ) * ∑ h : H, conjChar K h θ k := by
  have : Fintype K := Fintype.ofFinite K
  have hconj : ∀ (a : K) (b : H),
      conjChar K ((a : G) * (b : G)) θ k = conjChar K (b : G) θ k := by
    intro a b
    rw [conjChar_mul, conjChar_eq_of_mem hθ a.2]
  have h1 : ∑ x : G, conjChar K x θ k
      = ∑ p : K × H, conjChar K ((p.1 : G) * (p.2 : G)) θ k := by
    rw [← Equiv.sum_comp (hcomp.equiv.symm) (fun x : G => conjChar K x θ k)]
    exact Finset.sum_congr rfl fun p _ => by rw [Subgroup.IsComplement.equiv_symm_apply]
  calc ∑ x : G, conjChar K x θ k
      = ∑ p : K × H, conjChar K ((p.1 : G) * (p.2 : G)) θ k := h1
    _ = ∑ a : K, ∑ b : H, conjChar K ((a : G) * (b : G)) θ k :=
        Fintype.sum_prod_type (fun p : K × H => conjChar K ((p.1 : G) * (p.2 : G)) θ k)
    _ = ∑ a : K, ∑ b : H, conjChar K (b : G) θ k :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hconj a b
    _ = ∑ b : H, ∑ a : K, conjChar K (b : G) θ k := Finset.sum_comm
    _ = ∑ b : H, (Nat.card K : ℂ) * conjChar K (b : G) θ k := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ = (Nat.card K : ℂ) * ∑ b : H, conjChar K (b : G) θ k := by
        rw [Finset.mul_sum]

/-- **Restriction of an induced class function to the normal subgroup.**  For a normal
subgroup `K ⊴ G` with complement `H` and a class function `θ` on `K`, the restriction of the
induced class function `indFun K θ` to `K` is the sum of the conjugates `θ^h`, `h ∈ H`. -/
theorem resFun_indFun_eq_sum_conjChar {G : Type*} [Group G] [Fintype G] {K H : Subgroup G}
    [K.Normal] [Fintype H] (hcomp : Subgroup.IsComplement' K H) {θ : K → ℂ} (hθ : IsClassFun θ) :
    resFun K (indFun K θ) = ∑ h : H, conjChar K h θ := by
  funext k
  have : Fintype K := Fintype.ofFinite K
  have hne : (Nat.card K : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card, Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  simp only [resFun, Finset.sum_apply]
  exact mul_left_cancel₀ hne ((card_mul_indFun_apply_of_normal (K := K) θ k).trans
    (conjChar_sum_eq_card_mul (K := K) (H := H) hcomp hθ k))

end Work.Frobenius.Induced
