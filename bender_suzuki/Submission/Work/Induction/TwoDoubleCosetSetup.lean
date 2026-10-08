import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.frobenius_reciprocity_transposed
import Submission.Work.Induction.Basic
import Submission.Work.Induction.sum_conj_eq_card_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Setup for the two-double-coset inner product formula

Shared definitions and structural lemmas for the computation of
`⟨Ind_H^G ψ, Ind_H^G ψ⟩_G` when `G = H ⊔ H t H` with `t * t = 1`, `t ∉ H`.

The subgroup `K = DCInf H t = H ∩ Hᵗ = H ∩ t H t⁻¹` and the conjugate class function
`psiT t hDmap ψ : K → ℂ`, `k ↦ ψ (t k t⁻¹)`, are used to state the formula.
-/

namespace Work.Induction

open Classical
open scoped Pointwise

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

/-- `K = H ∩ Hᵗ = H ∩ t H t⁻¹`, the intersection appearing in the two-double-coset formula. -/
abbrev DCInf (H : Subgroup G) (t : G) : Subgroup G := H ⊓ H.map (MulAut.conj t).toMonoidHom

section Structural

variable {H : Subgroup G} {t : G}

/-- Conjugation by an involution `t` (`t * t = 1`) is an involution. -/
theorem conj_conj_of_mul_self_eq_one (ht : t * t = 1) (x : G) :
    (MulAut.conj t) ((MulAut.conj t) x) = x := by
  have h2 : MulAut.conj t * MulAut.conj t = 1 := by rw [← map_mul, ht, map_one]
  have h3 : ((MulAut.conj t) * (MulAut.conj t)) x = x := by rw [h2]; rfl
  rwa [show ((MulAut.conj t) * (MulAut.conj t)) x =
      (MulAut.conj t) ((MulAut.conj t) x) from rfl] at h3

/-- Membership in the conjugate `Hᵗ = t H t⁻¹`, when `t` is an involution: `x ∈ Hᵗ ↔ t x t⁻¹ ∈ H`. -/
theorem mem_map_conj_iff (ht : t * t = 1) (x : G) :
    x ∈ H.map (MulAut.conj t).toMonoidHom ↔ (MulAut.conj t) x ∈ H := by
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom] at hyx
    exact (by rw [← hyx, conj_conj_of_mul_self_eq_one ht y]; exact hy)
  · intro hx
    rw [Subgroup.mem_map]
    exact ⟨(MulAut.conj t) x, hx, by rw [MulEquiv.coe_toMonoidHom, conj_conj_of_mul_self_eq_one ht]⟩

/-- Membership in `K = H ∩ Hᵗ`: `x ∈ K ↔ x ∈ H ∧ t x t⁻¹ ∈ H`. -/
theorem mem_DCInf_iff (ht : t * t = 1) (x : G) :
    x ∈ DCInf H t ↔ x ∈ H ∧ (MulAut.conj t) x ∈ H := by
  rw [DCInf, Subgroup.mem_inf, mem_map_conj_iff ht]

/-- `K = H ∩ Hᵗ` is invariant under conjugation by the involution `t`. -/
theorem conj_mem_DCInf (ht : t * t = 1) (k : ↥(DCInf H t)) :
    (MulAut.conj t) (k : G) ∈ DCInf H t := by
  rw [mem_DCInf_iff ht]
  exact ⟨((mem_DCInf_iff ht (k : G)).mp k.2).2,
    by rw [conj_conj_of_mul_self_eq_one ht]; exact ((mem_DCInf_iff ht (k : G)).mp k.2).1⟩

/-- With `G = H ⊔ H t H`, an element outside `H` is exactly an element of the double coset
`H t H`. -/
theorem notMem_H_iff (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a:G) * t * (b:G)) (x : G) :
    x ∉ H ↔ ∃ a b : H, x = (a:G) * t * (b:G) := by
  constructor
  · intro hx
    rcases hcover x with h | h
    · exact absurd h hx
    · exact h
  · rintro ⟨a, b, rfl⟩ hmem
    apply htH
    have hmem' : (a:G)⁻¹ * ((a:G)*t*(b:G)) * (b:G)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem a.2) hmem) (H.inv_mem b.2)
    have heq : (a:G)⁻¹ * ((a:G)*t*(b:G)) * (b:G)⁻¹ = t := by group
    rwa [heq] at hmem'

end Structural

section Fibre

variable {H : Subgroup G} [Fintype ↥H] {t : G}

/-- The fibre of `(a, b) ↦ a t b` over `a₀ t b₀` has the cardinality of `K = H ∩ Hᵗ`.

Explicitly, the bijection sends `k ∈ K` to `(a₀ k, (t k⁻¹ t⁻¹) b₀)`; the inverse sends a
solution `(u, v)` of `u t v = a₀ t b₀` to `a₀⁻¹ u ∈ K`. -/
theorem card_fiber_doubleCoset (t : G) (ht : t * t = 1) (a₀ b₀ : H) :
    Fintype.card ↥(DCInf H t)
      = Fintype.card {p : H × H // (p.1:G)*t*(p.2:G) = (a₀:G)*t*(b₀:G)} := by
  have hcc := conj_conj_of_mul_self_eq_one ht (G := G)
  have memK := mem_DCInf_iff (H := H) ht
  have conjK := conj_mem_DCInf (H := H) ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hder : ∀ (u v : H), (u:G)*t*(v:G) = (a₀:G)*t*(b₀:G) →
      (a₀:G)⁻¹ * (u:G) = (MulAut.conj t) ((b₀:G) * (v:G)⁻¹) := by
    intro u v huv
    have h1 : (a₀:G)⁻¹ * (u:G) * t * (v:G) = t * (b₀:G) := by
      calc (a₀:G)⁻¹ * (u:G) * t * (v:G) = (a₀:G)⁻¹ * ((u:G) * t * (v:G)) := by group
        _ = (a₀:G)⁻¹ * ((a₀:G) * t * (b₀:G)) := by rw [huv]
        _ = t * (b₀:G) := by group
    calc (a₀:G)⁻¹ * (u:G)
        = (a₀:G)⁻¹ * (u:G) * t * (v:G) * ((v:G)⁻¹ * t⁻¹) := by group
      _ = t * (b₀:G) * ((v:G)⁻¹ * t⁻¹) := by rw [h1]
      _ = (MulAut.conj t) ((b₀:G) * (v:G)⁻¹) := by rw [MulAut.conj_apply]; group
  refine Fintype.card_congr ?_
  refine
  { toFun := fun k => ⟨(⟨(a₀:G) * (k:G), H.mul_mem a₀.2 ((memK (k:G)).mp k.2).1⟩,
        ⟨(MulAut.conj t) ((k⁻¹ : ↥(DCInf H t)) : G) * (b₀:G),
          H.mul_mem ((memK _).mp (conjK k⁻¹)).1 b₀.2⟩), ?_⟩
    invFun := fun p => ⟨(a₀:G)⁻¹ * (p.1.1:G), ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · change (a₀:G) * (k:G) * t * ((MulAut.conj t) ((k⁻¹ : ↥(DCInf H t)) : G) * (b₀:G)) =
      (a₀:G) * t * (b₀:G)
    rw [show ((k⁻¹ : ↥(DCInf H t)) : G) = (k:G)⁻¹ from Subgroup.coe_inv (DCInf H t) k]
    rw [MulAut.conj_apply, htinv]
    have e : (a₀:G) * (k:G) * t * ((t * (k:G)⁻¹ * t) * (b₀:G))
        = (a₀:G) * (k:G) * (t*t) * (k:G)⁻¹ * t * (b₀:G) := by group
    rw [e, ht]; group
  · change (a₀:G)⁻¹ * (p.1.1:G) ∈ DCInf H t
    rw [memK]
    exact ⟨H.mul_mem (H.inv_mem a₀.2) p.1.1.2,
      by rw [hder p.1.1 p.1.2 p.2, hcc]; exact H.mul_mem b₀.2 (H.inv_mem p.1.2.2)⟩
  · intro k
    apply Subtype.ext
    change (a₀:G)⁻¹ * ((a₀:G) * (k:G)) = (k:G)
    group
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change (a₀:G) * ((a₀:G)⁻¹ * (p.1.1:G)) = (p.1.1:G)
      group
    · apply Subtype.ext
      change (MulAut.conj t) (((a₀:G)⁻¹ * (p.1.1:G))⁻¹) * (b₀:G) = (p.1.2:G)
      rw [hder p.1.1 p.1.2 p.2, map_inv, hcc]
      group

/-- **Reindexing the double coset `H t H`.**  For a function `F` on `G` supported on `H t H`,
the sum over `G` equals `|K|` times the sum over `H × H` of `(a,b) ↦ a t b`.  Equivalently
the map `(a,b) ↦ a t b : H × H → H t H` is `|K|`-to-one. -/
theorem doubleCoset_sum_reindex (t : G) (ht : t * t = 1) (F : G → ℂ)
    (hF : ∀ x : G, (∀ a b : H, x ≠ (a : G) * t * (b : G)) → F x = 0) :
    ∑ p : H × H, F ((p.1 : G) * t * (p.2 : G))
      = (Nat.card ↥(DCInf H t) : ℂ) * ∑ x : G, F x := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (H × H))
        (fun p : H × H => (p.1 : G) * t * (p.2 : G)) (fun p => F ((p.1 : G) * t * (p.2 : G)))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : ∃ a b : H, j = (a:G)*t*(b:G)
  · obtain ⟨a₀, b₀, rfl⟩ := hj
    have hcard : (Finset.univ.filter (fun p : H × H =>
          (p.1:G)*t*(p.2:G) = (a₀:G)*t*(b₀:G))).card = Nat.card ↥(DCInf H t) := by
      rw [Nat.card_eq_fintype_card,
        ← Fintype.card_subtype (fun p : H × H => (p.1:G)*t*(p.2:G) = (a₀:G)*t*(b₀:G))]
      exact (card_fiber_doubleCoset t ht a₀ b₀).symm
    have h1 : ∑ p ∈ Finset.univ.filter (fun p : H × H =>
            (p.1:G)*t*(p.2:G) = (a₀:G)*t*(b₀:G)), F ((p.1:G)*t*(p.2:G))
        = ∑ p ∈ Finset.univ.filter (fun p : H × H =>
            (p.1:G)*t*(p.2:G) = (a₀:G)*t*(b₀:G)), F ((a₀:G)*t*(b₀:G)) :=
      Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])
    rw [h1, Finset.sum_const, hcard, nsmul_eq_mul]
  · have hj' : ∀ a b : H, j ≠ (a:G)*t*(b:G) := fun a b hab => hj ⟨a, b, hab⟩
    rw [Finset.sum_eq_zero (fun p hp => by
        rw [Finset.mem_filter] at hp; rw [hp.2, hF j hj']), hF j hj']
    simp

end Fibre

section Defs

variable {H : Subgroup G} [Fintype ↥H] {t : G}

/-- The class function `k ↦ t k t⁻¹` on `K = H ∩ Hᵗ`, read in `H` (via `H ≤ G`). -/
def psiT (t : G)
    (hDmap : ∀ d : ↥(DCInf H t), (MulAut.conj t) (d : G) ∈ DCInf H t) (ψ : H → ℂ) :
    ↥(DCInf H t) → ℂ :=
  fun d => ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩

/-- The summand for a pair `(a, b) ∈ H × H` in the double-coset sum: the value
`ψ ((a t b) h (a t b)⁻¹)`, read in `H`, if that conjugate lies in `H`, and `0` otherwise. -/
def atbSummand (t : G) (ψ : H → ℂ) (h : H) (p : H × H) : ℂ :=
  dite ((((p.1 : G) * t * (p.2 : G)) * (h : G) * (((p.1 : G) * t * (p.2 : G)))⁻¹) ∈ H)
    (fun hc => ψ ⟨((p.1 : G) * t * (p.2 : G)) * (h : G)
      * (((p.1 : G) * t * (p.2 : G)))⁻¹, hc⟩) (fun _ => 0)

/-- The summand `ψt (y h y⁻¹)` for `y ∈ H` when `y h y⁻¹ ∈ K = H ∩ Hᵗ`, and `0` otherwise. -/
def corrSummand (t : G) (ψt : ↥(DCInf H t) → ℂ) (h : H) (y : H) : ℂ :=
  dite (((y : G) * (h : G) * (y : G)⁻¹) ∈ DCInf H t)
    (fun hy => ψt ⟨(y : G) * (h : G) * (y : G)⁻¹, hy⟩) (fun _ => 0)

/-- The second Mackey component `Ind_K^H (k ↦ ψ (t k t⁻¹))`, written out as a sum over `H`
(the induced function from the subgroup `K = H ∩ Hᵗ` of `H`). -/
def corrOf (t : G) (ψt : ↥(DCInf H t) → ℂ) : H → ℂ :=
  fun h => (Nat.card ↥(DCInf H t) : ℂ)⁻¹ * ∑ y : H, corrSummand t ψt h y

/-- Summand of the induced-function sum at `x`: the value `ψ (x h x⁻¹)` read in `H` when
`x h x⁻¹ ∈ H`, and `0` otherwise. -/
def resSummand (H : Subgroup G) (h : H) (ψ : H → ℂ) (x : G) : ℂ :=
  dite (x * (h : G) * x⁻¹ ∈ H) (fun hc => ψ ⟨x * (h : G) * x⁻¹, hc⟩) (fun _ => 0)

/-- `resSummand`, killed off the double coset `H t H` (so that it is supported exactly on
`H t H = {x | x ∉ H}`). -/
def coverSummand (H : Subgroup G) (t : G) (h : H) (ψ : H → ℂ) (x : G) : ℂ :=
  dite (∃ a b : H, x = (a : G) * t * (b : G)) (fun _ => resSummand H h ψ x) (fun _ => 0)

end Defs

section Computations

variable {H : Subgroup G} [Fintype ↥H] {t : G}

/-- **The double-coset double sum.**  For fixed `h ∈ H`, the sum of `atbSummand` over `H × H`
equals `|H|` times the sum of `corrSummand` over `H`.  This is the termwise computation
`(a t b) h (a t b)⁻¹ ∈ H ↔ b h b⁻¹ ∈ K` together with the class-function property of `ψ`. -/
theorem atbSummand_sum_eq (ht : t * t = 1)
    (hDmap : ∀ d : ↥(DCInf H t), (MulAut.conj t) (d : G) ∈ DCInf H t)
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) (h : H) :
    ∑ p : H × H, atbSummand t ψ h p
      = (Nat.card ↥H : ℂ) * ∑ y : H, corrSummand t (psiT t hDmap ψ) h y := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have hterm : ∀ p : H × H, atbSummand t ψ h p
      = corrSummand t (psiT t hDmap ψ) h p.2 := by
    intro p
    obtain ⟨a, b⟩ := p
    have hVeq : ((a:G) * t * (b:G)) * (h:G) * ((a:G) * t * (b:G))⁻¹
        = (a:G) * (MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹) * (a:G)⁻¹ := by
      rw [MulAut.conj_apply]
      rw [show ((a:G)*t*(b:G))⁻¹ = (b:G)⁻¹ * t * (a:G)⁻¹ from by
        rw [mul_inv_rev, mul_inv_rev, htinv]; group]
      rw [htinv]
      group
    have hbhH : ((b:G) * (h:G) * (b:G)⁻¹) ∈ H := H.mul_mem (H.mul_mem b.2 h.2) (H.inv_mem b.2)
    unfold atbSummand corrSummand
    by_cases hC2 : ((b:G) * (h:G) * (b:G)⁻¹) ∈ DCInf H t
    · have hWH : (MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹) ∈ H :=
        (mem_map_conj_iff (H := H) ht ((b:G) * (h:G) * (b:G)⁻¹)).mp
          (Subgroup.mem_inf.mp hC2).2
      have hC1 : ((a:G) * t * (b:G)) * (h:G) * ((a:G) * t * (b:G))⁻¹ ∈ H := by
        rw [hVeq]; exact H.mul_mem (H.mul_mem a.2 hWH) (H.inv_mem a.2)
      rw [dite_eq_left hC1, dite_eq_left hC2]
      have step1 : ψ ⟨((a:G) * t * (b:G)) * (h:G) * ((a:G) * t * (b:G))⁻¹, hC1⟩
          = ψ ⟨(MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹), hWH⟩ := by
        have hsub : (⟨((a:G) * t * (b:G)) * (h:G) * ((a:G) * t * (b:G))⁻¹, hC1⟩ : H)
            = ⟨(a:G), a.2⟩ * ⟨(MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹), hWH⟩
              * (⟨(a:G), a.2⟩)⁻¹ := by
          apply Subtype.ext
          exact hVeq
        rw [hsub]
        exact hψ _ _
      rw [step1]
      unfold psiT
      exact congrArg ψ (Subtype.ext rfl)
    · have hC1 : ¬ ((a:G) * t * (b:G)) * (h:G) * ((a:G) * t * (b:G))⁻¹ ∈ H := by
        intro hV
        have hV' : (a:G) * (MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹) * (a:G)⁻¹ ∈ H := by
          rw [← hVeq]; exact hV
        have hWH : (MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹) ∈ H := by
          have := H.mul_mem (H.mul_mem (H.inv_mem a.2) hV') a.2
          rwa [show (a:G)⁻¹ * ((a:G) * (MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹) * (a:G)⁻¹)
                * (a:G) = (MulAut.conj t) ((b:G) * (h:G) * (b:G)⁻¹) from by group] at this
        exact hC2 (Subgroup.mem_inf.mpr ⟨hbhH,
          (mem_map_conj_iff (H := H) ht ((b:G) * (h:G) * (b:G)⁻¹)).mpr hWH⟩)
      rw [dite_eq_right hC1, dite_eq_right hC2]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- **Reindexing a conjugate.**  For fixed `y ∈ H`, summing `ψ h · conj (ψt (y h y⁻¹))` over
`h ∈ H` (with `ψt` read on `K = H ∩ Hᵗ`) equals the sum over `K`; the substitution
`h ↦ y h y⁻¹` is a bijection and `ψ` is a class function. -/
theorem sum_psi_corrSummand [Fintype ↥(DCInf H t)] (ht : t * t = 1)
    (hDmap : ∀ d : ↥(DCInf H t), (MulAut.conj t) (d : G) ∈ DCInf H t)
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) (y : H) :
    ∑ h : H, ψ h * star (corrSummand t (psiT t hDmap ψ) h y)
      = ∑ z : ↥(DCInf H t), ψ ⟨(z:G), (Subgroup.mem_inf.mp z.2).1⟩ * star (psiT t hDmap ψ z) := by
  have hzero : ∀ h : H, ¬ (((y:G)*(h:G)*(y:G)⁻¹) ∈ DCInf H t) →
      ψ h * star (corrSummand t (psiT t hDmap ψ) h y) = 0 := by
    intro h hh
    rw [corrSummand, dite_eq_right hh, star_zero, mul_zero]
  have hfilter : ∑ h : H, ψ h * star (corrSummand t (psiT t hDmap ψ) h y)
      = ∑ h ∈ Finset.univ.filter (fun h : H => ((y:G)*(h:G)*(y:G)⁻¹) ∈ DCInf H t),
          ψ h * star (corrSummand t (psiT t hDmap ψ) h y) := by
    rw [eq_comm]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro h _ hh
    exact hzero h (by simpa using hh)
  rw [hfilter]
  refine Finset.sum_bij
    (fun h hh => ⟨(y:G)*(h:G)*(y:G)⁻¹, (Finset.mem_filter.mp hh).2⟩) ?_ ?_ ?_ ?_
  · intro h hh; exact Finset.mem_univ _
  · intro h₁ hh₁ h₂ hh₂ heq
    apply Subtype.ext
    have hval := Subtype.ext_iff.mp heq
    show (h₁:G) = (h₂:G)
    have hcongr := congrArg (fun z : G => (y:G)⁻¹ * z * (y:G)) hval
    simpa using hcongr
  · intro z _
    refine ⟨⟨(y:G)⁻¹ * (z:G) * (y:G), H.mul_mem (H.mul_mem (H.inv_mem y.2)
        (Subgroup.mem_inf.mp z.2).1) y.2⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show ((y:G) * ((y:G)⁻¹ * (z:G) * (y:G)) * (y:G)⁻¹) ∈ DCInf H t
      rw [show (y:G) * ((y:G)⁻¹ * (z:G) * (y:G)) * (y:G)⁻¹ = (z:G) from by group]
      exact z.2
    · apply Subtype.ext
      show (y:G) * ((y:G)⁻¹ * (z:G) * (y:G)) * (y:G)⁻¹ = (z:G)
      group
  · intro h hh
    have hYh : ((y:G)*(h:G)*(y:G)⁻¹) ∈ DCInf H t := (Finset.mem_filter.mp hh).2
    show ψ h * star (corrSummand t (psiT t hDmap ψ) h y)
        = ψ ⟨(y:G)*(h:G)*(y:G)⁻¹, _⟩ * star (psiT t hDmap ψ ⟨(y:G)*(h:G)*(y:G)⁻¹, _⟩)
    have hconj : ψ h = ψ ⟨(y:G)*(h:G)*(y:G)⁻¹, (Subgroup.mem_inf.mp hYh).1⟩ := by
      have hx : (h : H) = (y⁻¹ : H)
          * ⟨(y:G)*(h:G)*(y:G)⁻¹, (Subgroup.mem_inf.mp hYh).1⟩ * ((y⁻¹ : H))⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      exact (congrArg ψ hx).trans (hψ ⟨(y:G)*(h:G)*(y:G)⁻¹, (Subgroup.mem_inf.mp hYh).1⟩ (y⁻¹))
    rw [hconj, corrSummand, dite_eq_left hYh]

/-- **The inner product of `ψ` with the second Mackey component.**  Specialised Frobenius
reciprocity: `⟨ψ, Ind_K^H (k ↦ ψ (t k t⁻¹))⟩_H = ⟨Res_K^H ψ, k ↦ ψ (t k t⁻¹)⟩_K`. -/
theorem cfInner_corrOf [Fintype ↥(DCInf H t)] (ht : t * t = 1)
    (hDmap : ∀ d : ↥(DCInf H t), (MulAut.conj t) (d : G) ∈ DCInf H t)
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner ψ (corrOf t (psiT t hDmap ψ))
      = (Nat.card ↥(DCInf H t) : ℂ)⁻¹ *
          ∑ d : ↥(DCInf H t), ψ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
            star (psiT t hDmap ψ d) := by
  have hcorr : corrOf t (psiT t hDmap ψ)
      = (Nat.card ↥(DCInf H t) : ℂ)⁻¹ •
          (fun h : H => ∑ y : H, corrSummand t (psiT t hDmap ψ) h y) := by
    funext h; rw [corrOf]; rfl
  rw [hcorr, CharCore.cfInner_smul_right]
  rw [show starRingEnd ℂ ((Nat.card ↥(DCInf H t) : ℂ)⁻¹)
      = (Nat.card ↥(DCInf H t) : ℂ)⁻¹ from by rw [map_inv₀, map_natCast]]
  rw [CharCore.cfInner_apply]
  congr 1
  have hH : (Fintype.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  have hstarθ : ∀ h : H, star (∑ y : H, corrSummand t (psiT t hDmap ψ) h y)
      = ∑ y : H, star (corrSummand t (psiT t hDmap ψ) h y) :=
    fun h => map_sum (starRingEnd ℂ) (fun y => corrSummand t (psiT t hDmap ψ) h y) Finset.univ
  have hbeta : ∀ y : H, (∑ h : H, ψ h * star (corrSummand t (psiT t hDmap ψ) h y))
      = ∑ z : ↥(DCInf H t), ψ ⟨(z:G), (Subgroup.mem_inf.mp z.2).1⟩ * star (psiT t hDmap ψ z) :=
    fun y => sum_psi_corrSummand ht hDmap ψ hψ y
  have hterm : ∀ h : H, ψ h * star (∑ y : H, corrSummand t (psiT t hDmap ψ) h y)
      = ∑ y : H, ψ h * star (corrSummand t (psiT t hDmap ψ) h y) := by
    intro h; rw [hstarθ h, Finset.mul_sum]
  rw [show (∑ x : H, ψ x * (starRingEnd ℂ) (∑ y : H, corrSummand t (psiT t hDmap ψ) x y))
      = ∑ x : H, ∑ y : H, ψ x * star (corrSummand t (psiT t hDmap ψ) x y) from
    Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun y _ => hbeta y)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hH, one_mul]

end Computations

section Reciprocity

variable {H : Subgroup G} [Fintype ↥H]

/-- `Work.CharCore.cfInner` does not depend on the chosen `Fintype` instance (both are
`(Nat.card · : ℂ)⁻¹` times the sum over all elements). -/
theorem cfInner_congr_fintype {G : Type*} [Group G] (i₁ i₂ : Fintype G) (f g : G → ℂ) :
    @Work.CharCore.cfInner G i₁ f g = @Work.CharCore.cfInner G i₂ f g := by
  rw [@Work.CharCore.cfInner_apply G _ i₁ f g, @Work.CharCore.cfInner_apply G _ i₂ f g]
  congr 1
  · rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  · apply Finset.sum_congr
    · apply Finset.ext; intro x; simp
    · intro x _; rfl

/-- Frobenius reciprocity with the `Fintype ↥H` instance supplied as a hypothesis (the
Mathlib/workspace version hardcodes the canonical instance of `↥H`, which is not the one
carried by the hypotheses of the two-double-coset statement). -/
theorem frobenius_reciprocity_local (H : Subgroup G) [Fintype ↥H]
    (φ : H → ℂ) (ψ : G → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner (Work.Induction.indFun H φ) ψ
      = Work.CharCore.cfInner φ (Work.Induction.resFun H ψ) := by
  rw [frobenius_reciprocity H φ ψ hψ]
  exact cfInner_congr_fintype _ _ φ (Work.Induction.resFun H ψ)

end Reciprocity

end

end Work.Induction
