import Mathlib
import Submission.Work.FIArea2.Tsum_odd_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The substitution `(x,y) ↦ (y - ρx, y + ρx)` is injective, since `2` and `ρ` are units
(`ρ` is left-invertible by `ρ'`, and `2` is a unit by hypothesis). -/
private lemma uvMap_injective {N : ℕ} (ρ ρ' : ZMod N) (hρ' : ρ * ρ' = 1)
    (h2u : IsUnit (2 : ZMod N)) :
    Function.Injective (fun q : ZMod N × ZMod N => (q.2 - ρ * q.1, q.2 + ρ * q.1)) := by
  intro p q h
  have h₁ : p.2 - ρ * p.1 = q.2 - ρ * q.1 := congrArg Prod.fst h
  have h₂ : p.2 + ρ * p.1 = q.2 + ρ * q.1 := congrArg Prod.snd h
  have hy : p.2 = q.2 := by
    apply h2u.mul_left_cancel
    calc (2 : ZMod N) * p.2 = (p.2 - ρ * p.1) + (p.2 + ρ * p.1) := by ring
      _ = (q.2 - ρ * q.1) + (q.2 + ρ * q.1) := by rw [h₁, h₂]
      _ = 2 * q.2 := by ring
  have hx : p.1 = q.1 := by
    have hρ'ρ : ρ' * ρ = 1 := by rw [mul_comm, hρ']
    have h3 : ρ * p.1 = ρ * q.1 := by
      apply h2u.mul_left_cancel
      calc (2 : ZMod N) * (ρ * p.1) = (p.2 + ρ * p.1) - (p.2 - ρ * p.1) := by ring
        _ = (q.2 + ρ * q.1) - (q.2 - ρ * q.1) := by rw [h₁, h₂]
        _ = 2 * (ρ * q.1) := by ring
    calc p.1 = 1 * p.1 := (one_mul _).symm
      _ = (ρ' * ρ) * p.1 := by rw [hρ'ρ]
      _ = ρ' * (ρ * p.1) := by rw [mul_assoc]
      _ = ρ' * (ρ * q.1) := by rw [h3]
      _ = (ρ' * ρ) * q.1 := by rw [mul_assoc]
      _ = 1 * q.1 := by rw [hρ'ρ]
      _ = q.1 := one_mul _
  exact Prod.ext hx hy

/-- **The square case: the substitution `(x,y) ↦ (u,v) = (y - ρx, y + ρx)`.**  Let `p` be prime,
`ν ≥ 1`, `ρ` a square root in `ZMod (p^ν)` of the unit `a`, with `ρ' = ρ⁻¹` (`ρ * ρ' = 1`), and
let `α, β` solve `2α = h₂ - h₁ρ'` and `2β = h₂ + h₁ρ'` (`2` is a unit, hypothesis `h2u`).  The
substitution `(x,y) ↦ (u,v) := (y - ρx, y + ρx)` is a bijection of `ZMod (p^ν)²` (inverse
`x = (v-u)·(2ρ)⁻¹`, `y = (u+v)·2⁻¹`, using `ha` for `IsUnit ρ`), it carries `{y² = a x²}` onto
`{uv = 0}` (because `(y-ρx)(y+ρx) = y² - ρ²x²` together with `ρ² = a`), and it converts the
phase: `x h₁ + y h₂ = u α + v β`.  Hence, with `Work.FIArea2.Tsum_eq_sum_Phi` (which writes
`Tsum` as the character sum `∑_{y²=ax²} Φ (p^ν) (x h₁ + y h₂)`),

  `Tsum (p^ν) a h₁ h₂ = ∑_{u v = 0} Φ (p^ν) (u α + v β)`. -/
theorem Tsum_eq_uvSum {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (a h1 h2 : ℤ) (ρ ρ' α β : ZMod (p ^ ν)) (ha : IsUnit (a : ZMod (p ^ ν)))
    (h2u : IsUnit (2 : ZMod (p ^ ν))) (hρ : ρ ^ 2 = (a : ZMod (p ^ ν))) (hρ' : ρ * ρ' = 1)
    (hα : (2 : ZMod (p ^ ν)) * α = (h2 : ZMod (p ^ ν)) - (h1 : ZMod (p ^ ν)) * ρ')
    (hβ : (2 : ZMod (p ^ ν)) * β = (h2 : ZMod (p ^ ν)) + (h1 : ZMod (p ^ ν)) * ρ') :
    Tsum (p ^ ν) a h1 h2
      = ∑ u : ZMod (p ^ ν), ∑ v : ZMod (p ^ ν),
          (if u * v = 0 then Phi (p ^ ν) (u * α + v * β) else 0) := by
  -- the phase identities `α + β = h₂` and `ρ (β - α) = h₁`
  have hαβ : α + β = (h2 : ZMod (p ^ ν)) := by
    apply h2u.mul_left_cancel
    calc (2 : ZMod (p ^ ν)) * (α + β)
        = (2 : ZMod (p ^ ν)) * α + (2 : ZMod (p ^ ν)) * β := by ring
      _ = ((h2 : ZMod (p ^ ν)) - (h1 : ZMod (p ^ ν)) * ρ')
            + ((h2 : ZMod (p ^ ν)) + (h1 : ZMod (p ^ ν)) * ρ') := by rw [hα, hβ]
      _ = (2 : ZMod (p ^ ν)) * (h2 : ZMod (p ^ ν)) := by ring
  have hρα : ρ * (β - α) = (h1 : ZMod (p ^ ν)) := by
    have h2' : (2 : ZMod (p ^ ν)) * (β - α)
        = (2 : ZMod (p ^ ν)) * ((h1 : ZMod (p ^ ν)) * ρ') := by
      calc (2 : ZMod (p ^ ν)) * (β - α)
          = (2 : ZMod (p ^ ν)) * β - (2 : ZMod (p ^ ν)) * α := by ring
        _ = ((h2 : ZMod (p ^ ν)) + (h1 : ZMod (p ^ ν)) * ρ')
              - ((h2 : ZMod (p ^ ν)) - (h1 : ZMod (p ^ ν)) * ρ') := by rw [hα, hβ]
        _ = (2 : ZMod (p ^ ν)) * ((h1 : ZMod (p ^ ν)) * ρ') := by ring
    have h3 : β - α = (h1 : ZMod (p ^ ν)) * ρ' := h2u.mul_left_cancel h2'
    calc ρ * (β - α) = ρ * ((h1 : ZMod (p ^ ν)) * ρ') := by rw [h3]
      _ = (h1 : ZMod (p ^ ν)) * (ρ * ρ') := by ring
      _ = (h1 : ZMod (p ^ ν)) := by rw [hρ', mul_one]
  -- the substitution preserves both the condition and the phase, term by term
  have hkey : ∀ q : ZMod (p ^ ν) × ZMod (p ^ ν),
      (if (q.2 - ρ * q.1) * (q.2 + ρ * q.1) = 0
        then Phi (p ^ ν) ((q.2 - ρ * q.1) * α + (q.2 + ρ * q.1) * β) else 0)
      = (if q.2 ^ 2 = (a : ZMod (p ^ ν)) * q.1 ^ 2
        then Phi (p ^ ν) (q.1 * (h1 : ZMod (p ^ ν)) + q.2 * (h2 : ZMod (p ^ ν))) else 0) := by
    intro q
    have hcond : (q.2 - ρ * q.1) * (q.2 + ρ * q.1)
        = q.2 ^ 2 - (a : ZMod (p ^ ν)) * q.1 ^ 2 := by
      rw [← hρ]; ring
    have hphase : (q.2 - ρ * q.1) * α + (q.2 + ρ * q.1) * β
        = q.1 * (h1 : ZMod (p ^ ν)) + q.2 * (h2 : ZMod (p ^ ν)) := by
      have hexp : (q.2 - ρ * q.1) * α + (q.2 + ρ * q.1) * β
          = q.2 * (α + β) + (ρ * (β - α)) * q.1 := by ring
      rw [hexp, hαβ, hρα]; ring
    by_cases hc : q.2 ^ 2 = (a : ZMod (p ^ ν)) * q.1 ^ 2
    · rw [if_pos (by rw [hcond, hc, sub_self]), if_pos hc, hphase]
    · rw [if_neg (by rw [hcond]; intro hz; exact hc (sub_eq_zero.mp hz)), if_neg hc]
  -- the substitution is a bijection of `ZMod (p^ν)²`
  have hinj : Function.Injective (fun q : ZMod (p ^ ν) × ZMod (p ^ ν) =>
      (q.2 - ρ * q.1, q.2 + ρ * q.1)) := uvMap_injective (N := p ^ ν) ρ ρ' hρ' h2u
  have hφ : Function.Bijective (fun q : ZMod (p ^ ν) × ZMod (p ^ ν) =>
      (q.2 - ρ * q.1, q.2 + ρ * q.1)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, rfl⟩
  rw [Tsum_eq_sum_Phi,
      ← Fintype.sum_prod_type (f := fun q : ZMod (p ^ ν) × ZMod (p ^ ν) =>
        (if q.2 ^ 2 = (a : ZMod (p ^ ν)) * q.1 ^ 2
          then Phi (p ^ ν) (q.1 * (h1 : ZMod (p ^ ν)) + q.2 * (h2 : ZMod (p ^ ν))) else 0)),
      ← Fintype.sum_prod_type (f := fun q : ZMod (p ^ ν) × ZMod (p ^ ν) =>
        (if q.1 * q.2 = 0 then Phi (p ^ ν) (q.1 * α + q.2 * β) else 0))]
  exact (Finset.sum_congr rfl (fun q _ => (hkey q).symm)).trans
    (Equiv.sum_comp (Equiv.ofBijective (fun q : ZMod (p ^ ν) × ZMod (p ^ ν) =>
        (q.2 - ρ * q.1, q.2 + ρ * q.1)) hφ)
      (fun q : ZMod (p ^ ν) × ZMod (p ^ ν) =>
        (if q.1 * q.2 = 0 then Phi (p ^ ν) (q.1 * α + q.2 * β) else 0)))

end

end Work.FIArea2
