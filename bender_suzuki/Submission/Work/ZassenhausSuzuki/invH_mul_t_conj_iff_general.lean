import Mathlib
import Submission.Work.ZassenhausSuzuki.GenHypSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `invH_mul_t_conj_iff` under the weakened hypothesis bundle `GenHyp`

The lemma `Work.ZassenhausSuzuki.invH_mul_t_conj_iff` (Suzuki 1962, Prop. 13, second half) is
stated for `SzHyp`, but its proof uses only the fields `split`, `zass`, `two` -- i.e. exactly the
bundle `GenHyp`.  This file records the corresponding statement for `GenHyp`, whose three
preparatory results (`H ⊓ C_G(t) = 1`, `(u t)² ≠ 1`, `C_G(u t)` abelian of odd order and inverted
by `t`) live in `GenHypSetup`.

If `u, u'` are involutions of `H` and `u * t` is conjugate to `u' * t`, then `u = u'`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- An element of order two is an involution. -/
private lemma sq_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [hx] at h
  simpa [pow_two] using h

/-- **Suzuki 1962, Proposition 13 (second half), weakened bundle.**
If `u, u'` are involutions of `H` and `u * t` is conjugate to `u' * t`, then `u = u'`. -/
theorem invH_mul_t_conj_iff_general {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Work.ZassenhausSuzuki.GenHyp H Q t) :
    ∀ u u' : G, u ∈ Submission.Blueprint.involutions (H : Set G) →
      u' ∈ Submission.Blueprint.involutions (H : Set G) →
      (∃ g : G, g * (u * t) * g⁻¹ = u' * t) → u = u' := by
  intro u u' hu hu' ⟨g, hg⟩
  obtain ⟨huH, hu2⟩ := hu
  obtain ⟨hu'H, hu'2⟩ := hu'
  have huu : u * u = 1 := sq_eq_one_of_orderOf_eq_two hu2
  have hu'u' : u' * u' = 1 := sq_eq_one_of_orderOf_eq_two hu'2
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨hαinv, hαabel, hαodd⟩ := centralizer_mul_t_inv_general h ⟨huH, hu2⟩
  -- `w := g⁻¹ u' g` inverts `u * t`
  set w : G := g⁻¹ * u' * g with hwdef
  have hu'β : u' * (u' * t) * u'⁻¹ = (u' * t)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right hu'u', mul_inv_rev,
      inv_eq_of_mul_eq_one_right hu'u', inv_eq_of_mul_eq_one_right htt]
    calc u' * (u' * t) * u' = (u' * u') * t * u' := by group
      _ = (1 : G) * t * u' := by rw [hu'u']
      _ = t * u' := by rw [one_mul]
  have hginv : g * (u * t)⁻¹ * g⁻¹ = (u' * t)⁻¹ := by
    have hc : (g * (u * t) * g⁻¹)⁻¹ = (u' * t)⁻¹ := congrArg Inv.inv hg
    calc g * (u * t)⁻¹ * g⁻¹ = (g * (u * t) * g⁻¹)⁻¹ := by group
      _ = (u' * t)⁻¹ := hc
  have hwinv : w * (u * t) * w⁻¹ = (u * t)⁻¹ := by
    rw [hwdef]
    calc (g⁻¹ * u' * g) * (u * t) * (g⁻¹ * u' * g)⁻¹
        = g⁻¹ * (u' * (g * (u * t) * g⁻¹) * u'⁻¹) * g := by group
      _ = g⁻¹ * (u' * (u' * t) * u'⁻¹) * g := by rw [hg]
      _ = g⁻¹ * (u' * t)⁻¹ * g := by rw [hu'β]
      _ = (u * t)⁻¹ := by rw [← hginv]; group
  -- `u` lies in the generalized centralizer of `u * t` too
  have huinv : u * (u * t) * u⁻¹ = (u * t)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right huu, mul_inv_rev,
      inv_eq_of_mul_eq_one_right huu, inv_eq_of_mul_eq_one_right htt]
    calc u * (u * t) * u = (u * u) * t * u := by group
      _ = (1 : G) * t * u := by rw [huu]
      _ = t * u := by rw [one_mul]
  -- the two "reflections" `t * u` and `t * w` of `C*(u * t)`
  let A : Subgroup G := Subgroup.centralizer ({u * t} : Set G)
  have hcu_mem : t * u ∈ A := by
    show (t * u) ∈ Subgroup.centralizer ({u * t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (t * u) * (u * t) = 1 := by
      calc (t * u) * (u * t) = t * (u * u) * t := by group
        _ = t * (1 : G) * t := by rw [huu]
        _ = 1 := by rw [mul_one, htt]
    have h2 : (u * t) * (t * u) = 1 := by
      calc (u * t) * (t * u) = u * (t * t) * u := by group
        _ = u * (1 : G) * u := by rw [htt]
        _ = 1 := by rw [mul_one, huu]
    rw [h1, h2]
  have hcommA : ∀ x y : G, x ∈ A → y ∈ A → x * y = y * x := by
    intro x y hx hy
    haveI : IsMulCommutative ↥A := hαabel
    have hh := mul_comm' (M := ↥A) ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val hh
  have htwα : (t * w) * (u * t) * (t * w)⁻¹ = u * t := by
    have htα : t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right htt]
      calc t * (u * t) * t = t * u * (t * t) := by group
        _ = t * u := by rw [htt, mul_one]
        _ = (u * t)⁻¹ := by
              rw [mul_inv_rev, inv_eq_of_mul_eq_one_right huu,
                inv_eq_of_mul_eq_one_right htt]
    have htαinv : t * (u * t)⁻¹ * t⁻¹ = u * t := by
      rw [← htα]
      calc t * (t * (u * t) * t⁻¹) * t⁻¹ = (t * t) * (u * t) * (t⁻¹ * t⁻¹) := by group
        _ = (1 : G) * (u * t) * (1 : G) := by
              rw [htt]
              have h2 : t⁻¹ * t⁻¹ = 1 := by rw [htinv, htt]
              rw [h2]
        _ = u * t := by rw [one_mul, mul_one]
    calc (t * w) * (u * t) * (t * w)⁻¹
        = t * (w * (u * t) * w⁻¹) * t⁻¹ := by group
      _ = t * (u * t)⁻¹ * t⁻¹ := by rw [hwinv]
      _ = u * t := htαinv
  have hcw_mem : t * w ∈ A := by
    show (t * w) ∈ Subgroup.centralizer ({u * t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (t * w) * (u * t) = ((t * w) * (u * t) * (t * w)⁻¹) * (t * w) := by group
      _ = (u * t) * (t * w) := by rw [htwα]
  -- `e ∈ A` with `e² = (t * u) * (t * w)⁻¹`
  set di : G := (t * u) * (t * w)⁻¹ with hdi
  have hdi_mem : di ∈ A := A.mul_mem hcu_mem (A.inv_mem hcw_mem)
  have hdi_odd : Odd (orderOf di) := hαodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard A hdi_mem)
  obtain ⟨k, hk⟩ := hdi_odd
  set e : G := di ^ (k + 1) with he
  have he_mem : e ∈ A := Subgroup.pow_mem A hdi_mem (k + 1)
  have he_sq : e * e = di := by
    rw [he]
    calc di ^ (k + 1) * di ^ (k + 1) = di ^ ((k + 1) + (k + 1)) := by rw [← pow_add]
      _ = di ^ ((2 * k + 1) + 1) := by
            rw [show (k + 1) + (k + 1) = (2 * k + 1) + 1 by ring]
      _ = di ^ (2 * k + 1) * di := by rw [pow_succ]
      _ = di ^ (orderOf di) * di := by rw [← hk]
      _ = 1 * di := by rw [pow_orderOf_eq_one]
      _ = di := by rw [one_mul]
  -- `e` conjugates `u` to `w`
  have het : e * t = t * e⁻¹ := by
    have he_inv : t * e * t⁻¹ = e⁻¹ := hαinv e he_mem
    have h1 : t * e * t = e⁻¹ := by rwa [htinv] at he_inv
    have h2 : (e * t) * (e * t) = 1 := by
      calc (e * t) * (e * t) = e * (t * e * t) := by group
        _ = e * e⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel e
    have h3 : (e * t)⁻¹ = e * t := inv_eq_of_mul_eq_one_right h2
    rw [mul_inv_rev, htinv] at h3
    exact h3.symm
  have heu : e * u * e⁻¹ = w := by
    have hcu_eq : u = t * (t * u) := by rw [← mul_assoc, htt, one_mul]
    have hw_eq : w = t * (t * w) := by rw [← mul_assoc, htt, one_mul]
    have hee : e⁻¹ * e⁻¹ = di⁻¹ := by rw [← mul_inv_rev, he_sq]
    have hcudi : (t * u) * di⁻¹ = t * w := by
      have h1 : di⁻¹ = (t * w) * (t * u)⁻¹ := by rw [hdi, mul_inv_rev, inv_inv]
      rw [h1]
      calc (t * u) * ((t * w) * (t * u)⁻¹) = ((t * u) * (t * w)) * (t * u)⁻¹ := by group
        _ = ((t * w) * (t * u)) * (t * u)⁻¹ := by rw [hcommA (t * u) (t * w) hcu_mem hcw_mem]
        _ = (t * w) * ((t * u) * (t * u)⁻¹) := by group
        _ = (t * w) * 1 := by rw [mul_inv_cancel]
        _ = t * w := by rw [mul_one]
    calc e * u * e⁻¹
        = e * (t * (t * u)) * e⁻¹ := by conv_lhs => rw [hcu_eq]
      _ = (e * t) * ((t * u) * e⁻¹) := by group
      _ = (t * e⁻¹) * ((t * u) * e⁻¹) := by rw [het]
      _ = t * (e⁻¹ * ((t * u) * e⁻¹)) := by group
      _ = t * ((e⁻¹ * (t * u)) * e⁻¹) := by group
      _ = t * (((t * u) * e⁻¹) * e⁻¹) := by
            rw [hcommA e⁻¹ (t * u) (A.inv_mem he_mem) hcu_mem]
      _ = t * ((t * u) * (e⁻¹ * e⁻¹)) := by group
      _ = t * ((t * u) * di⁻¹) := by rw [hee]
      _ = t * (t * w) := by rw [hcudi]
      _ = w := by rw [← hw_eq]
  -- `c₀ := g * e` centralizes `t` and conjugates `u` to `u'`, so lies in `H` and is `1`
  set c₀ : G := g * e with hc0
  have hc0u : c₀ * u * c₀⁻¹ = u' := by
    rw [hc0]
    calc (g * e) * u * (g * e)⁻¹ = g * (e * u * e⁻¹) * g⁻¹ := by group
      _ = g * w * g⁻¹ := by rw [heu]
      _ = u' := by rw [hwdef]; group
  have hc0α : c₀ * (u * t) * c₀⁻¹ = u' * t := by
    have hec : e * (u * t) * e⁻¹ = u * t := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp he_mem]
      group
    rw [hc0]
    calc (g * e) * (u * t) * (g * e)⁻¹ = g * (e * (u * t) * e⁻¹) * g⁻¹ := by group
      _ = g * (u * t) * g⁻¹ := by rw [hec]
      _ = u' * t := hg
  have hc0t : c₀ * t * c₀⁻¹ = t := by
    have h1 : c₀ * (u * t) * c₀⁻¹ = (c₀ * u * c₀⁻¹) * (c₀ * t * c₀⁻¹) := by group
    rw [hc0u, hc0α] at h1
    exact (mul_left_cancel h1).symm
  have hc0C : c₀ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c₀ * t = (c₀ * t * c₀⁻¹) * c₀ := by group
      _ = t * c₀ := by rw [hc0t]
  have hc0H : c₀ ∈ H := by
    have hmem : u' ∈ Submission.Blueprint.conj c₀ H := by
      rw [Work.ThreePoints.mem_conj_iff']
      exact ⟨u, huH, by rw [← hc0u]⟩
    have hconj :=
      Work.ThmF.conj_eq_self_of_involution_mem h.split.stronglyEmbedded hu'H hu'2 hmem
    have hnorm : c₀ ∈ Subgroup.normalizer (H : Set G) :=
      Work.Models.mem_normalizer_of_conj_eq hconj
    rwa [Work.Reductions.stronglyEmbedded_normalizer_eq h.split.stronglyEmbedded] at hnorm
  have hc0bot : c₀ ∈ H ⊓ Subgroup.centralizer ({t} : Set G) := ⟨hc0H, hc0C⟩
  rw [H_inf_centralizer_t_eq_bot_general h] at hc0bot
  have hc0one : c₀ = 1 := Subgroup.mem_bot.mp hc0bot
  rw [hc0one, one_mul, inv_one, mul_one] at hc0u
  exact hc0u

end Work.ZassenhausSuzuki
