import Mathlib
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.gen_top

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.RankOneUniqueness.closure_Q_t_eq_top` — `G = ⟨Q, t⟩` for simple `G` (S2)

In a simple group with split rank-one data the root group `Q` and the involution `t` generate:
`⟨Q, t⟩ = ⊤`.

Proof.  Let `K := ⟨Q, tQt⟩`.  Then `K` is normalized by `Q`, by `t` and by `D = H ∩ H^t`:

* `t`: direct, `t K t = ⟨tQt, Q⟩ = K`;
* `Q`: for `q ∈ Q` and `x ∈ Q` one has `q t q⁻¹ = (q·t q⁻¹ t)·t` with `q·t q⁻¹ t ∈ Q·tQt ⊆ K`,
  so `q (t x t) q⁻¹ = c (t x' t) (t c t)` with `c ∈ K`, `x' ∈ Q`, is in `K` (as `t` normalizes
  `K`);
* `D`: for `d ∈ D` and `x ∈ Q`, using `δ = t d t ∈ H ≤ N(Q)` and `d = t δ t` one gets
  `d (t x t) d⁻¹ = t (δ x δ⁻¹) t ∈ tQt`.

Since `G = ⟨H, t⟩ = ⟨Q, D, t⟩` (`gen_top` plus `H = Q ⋊ D`), `K ⊴ G`; `K ≠ 1` because `Q ≠ 1`
(otherwise `D = H` would be both odd and even), so by simplicity `K = ⊤`, and
`⟨Q, t⟩ ⊇ K`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.RankOneUniqueness

theorem closure_Q_t_eq_top {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Subgroup.closure ((Q : Set G) ∪ {t}) = ⊤ := by
  have h2 : t * t = 1 := mul_self_eq_one h
  -- `t (t x t) t = x` and `t (t x t) t⁻¹ = x`
  have hconj : ∀ x : G, t * (t * x * t) * t = x := fun x =>
    (by simpa only [inv_eq_self h] using involution_conj (e := x) h2)
  have hconj' : ∀ x : G, t * (t * x * t) * t⁻¹ = x := by
    intro x
    rw [inv_eq_self h]
    exact hconj x
  -- the subgroup `K = ⟨Q, tQt⟩`
  let T : Set G := {y : G | ∃ x ∈ Q, y = t * x * t}
  let K : Subgroup G := Subgroup.closure ((Q : Set G) ∪ T)
  have hQK : Q ≤ K := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have htTK : ∀ x ∈ Q, t * x * t ∈ K :=
    fun x hx => Subgroup.subset_closure (Or.inr ⟨x, hx, rfl⟩)
  -- a generic closure extension: conjugation by `d` on the generators gives it on `K`
  have hclos : ∀ (d : G), (∀ x ∈ (Q : Set G) ∪ T, d * x * d⁻¹ ∈ K) →
      ∀ n ∈ K, d * n * d⁻¹ ∈ K := by
    intro d hgen n hn
    refine Subgroup.closure_induction (p := fun n _ => d * n * d⁻¹ ∈ K)
      (fun x hx => hgen x hx) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) hn
    · simp
    · rw [show d * (x * y) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) from by group]
      exact K.mul_mem ihx ihy
    · rw [show d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ from by group]
      exact K.inv_mem ihx
  -- (1) `t` normalizes `K`
  have htgen : (Q : Set G) ∪ T ⊆ {x : G | t * x * t⁻¹ ∈ K} := by
    intro x hx
    rcases hx with hx | hx
    · show t * x * t⁻¹ ∈ K
      rw [inv_eq_self h]
      exact htTK x hx
    · obtain ⟨y, hy, rfl⟩ := hx
      show t * (t * y * t) * t⁻¹ ∈ K
      rw [hconj' y]
      exact hQK hy
  have htN : ∀ n ∈ K, t * n * t ∈ K := by
    intro n hn
    have := hclos t htgen n hn
    simpa only [inv_eq_self h] using this
  -- (2) `Q` normalizes `K`
  have hQN : ∀ q ∈ Q, ∀ n ∈ K, q * n * q⁻¹ ∈ K := by
    intro q hq
    apply hclos q
    intro x hx
    rcases hx with hx | hx
    · exact hQK (Q.mul_mem (Q.mul_mem hq hx) (Q.inv_mem hq))
    · obtain ⟨y, hy, rfl⟩ := hx
      have hcK : q * (t * q⁻¹ * t) ∈ K := K.mul_mem (hQK hq) (htTK q⁻¹ (Q.inv_mem hq))
      have hy'Q : q * y * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hq hy) (Q.inv_mem hq)
      have hstep : q * (t * y * t) * q⁻¹
          = (q * (t * q⁻¹ * t)) * (t * (q * y * q⁻¹) * t)
            * (t * (q * (t * q⁻¹ * t)) * t) := by
        have h1 : q * t * q⁻¹ = (q * (t * q⁻¹ * t)) * t := by
          simp only [mul_assoc, h2, mul_self_mul h, mul_one, one_mul]
        rw [show q * (t * y * t) * q⁻¹
            = (q * t * q⁻¹) * (q * y * q⁻¹) * (q * t * q⁻¹) from by group, h1]
        simp only [mul_assoc, h2, mul_self_mul h, mul_one, one_mul]
      rw [hstep]
      exact K.mul_mem (K.mul_mem hcK (htTK _ hy'Q)) (htN _ hcK)
  -- (3) `D` normalizes `K`
  have hDN : ∀ d ∈ twoPoint H t, ∀ n ∈ K, d * n * d⁻¹ ∈ K := by
    intro d hd
    apply hclos d
    intro x hx
    rcases hx with hx | hx
    · exact hQK (conj_mem_of_mem h (mem_twoPoint_iff.mp hd).1 hx)
    · obtain ⟨y, hy, rfl⟩ := hx
      have hδH : t * d * t ∈ H := t_mul_mul_t_mem_of_mem_twoPoint h2 hd
      have hδQ : (t * d * t) * y * (t * d * t)⁻¹ ∈ Q := conj_mem_of_mem h hδH hy
      have hstep' : ∀ δ : G,
          (t * δ * t) * (t * y * t) * (t * δ * t)⁻¹ = t * (δ * y * δ⁻¹) * t := by
        intro δ
        simp only [mul_assoc, h2, mul_self_mul h, mul_one, one_mul, mul_inv_rev, inv_inv,
          inv_eq_self h]
      have hdt : d = t * (t * d * t) * t := (hconj d).symm
      have hstep : d * (t * y * t) * d⁻¹
          = t * ((t * d * t) * y * (t * d * t)⁻¹) * t := by
        have h := hstep' (t * d * t)
        rwa [← hdt] at h
      rw [hstep]
      exact htTK _ hδQ
  -- `G = ⟨Q, D, t⟩`
  have hHle : H ≤ Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t}) := by
    have hQD : Q ⊔ twoPoint H t ≤ Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t}) := by
      refine sup_le ?_ ?_
      · intro q hq
        exact Subgroup.subset_closure (Or.inl (Or.inl hq))
      · intro d hd
        exact Subgroup.subset_closure (Or.inl (Or.inr hd))
    rwa [h.sup_eq] at hQD
  have htop : Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t}) = ⊤ := by
    have hsubset : ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t}) ⊆ (H : Set G) ∪ {t} := by
      intro x hx
      rcases hx with (hx | hx) | hx
      · exact Or.inl (h.sup_eq ▸ Subgroup.mem_sup_left hx)
      · exact Or.inl (h.sup_eq ▸ Subgroup.mem_sup_right hx)
      · exact Or.inr hx
    have h1 : Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t})
        ≤ Subgroup.closure ((H : Set G) ∪ {t}) := Subgroup.closure_mono hsubset
    have h2 : Subgroup.closure ((H : Set G) ∪ {t})
        ≤ Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t}) :=
      (Subgroup.closure_le _).mpr (fun x hx => by
        rcases hx with hx | hx
        · exact hHle hx
        · exact Subgroup.subset_closure (Or.inr hx))
    rw [← gen_top h]
    exact le_antisymm h1 h2
  -- `K ⊴ G`: normalize the generators, then the whole group
  have hgen_norm : ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t}) ⊆
      {g : G | (∀ n ∈ K, g * n * g⁻¹ ∈ K) ∧ (∀ n ∈ K, g⁻¹ * n * g ∈ K)} := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact ⟨fun n hn => hQN x hx n hn, fun n hn => by
        have h := hQN x⁻¹ (Q.inv_mem hx) n hn
        simpa only [inv_inv] using h⟩
    · exact ⟨fun n hn => hDN x hx n hn, fun n hn => by
        have h := hDN x⁻¹ ((twoPoint H t).inv_mem hx) n hn
        simpa only [inv_inv] using h⟩
    · have hxt : x = t := Set.mem_singleton_iff.mp hx
      refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · rw [hxt, inv_eq_self h]
        exact htN n hn
      · rw [hxt, inv_eq_self h]
        exact htN n hn
  have hG_norm : ∀ g : G,
      (∀ n ∈ K, g * n * g⁻¹ ∈ K) ∧ (∀ n ∈ K, g⁻¹ * n * g ∈ K) := by
    intro g
    have hmem : g ∈ Subgroup.closure ((Q : Set G) ∪ (twoPoint H t : Set G) ∪ {t}) := by
      rw [htop]
      exact Subgroup.mem_top g
    refine Subgroup.closure_induction
      (p := fun g _ => (∀ n ∈ K, g * n * g⁻¹ ∈ K) ∧ (∀ n ∈ K, g⁻¹ * n * g ∈ K))
      (fun x hx => hgen_norm hx) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) hmem
    · exact ⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn⟩
    · refine ⟨fun n hn => ?_, fun n hn => ?_⟩
      · rw [show (x * y) * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ from by group]
        exact ihx.1 _ (ihy.1 n hn)
      · rw [show (x * y)⁻¹ * n * (x * y) = y⁻¹ * (x⁻¹ * n * x) * y from by group]
        exact ihy.2 _ (ihx.2 n hn)
    · exact ⟨fun n hn => by
          have h := ihx.2 n hn
          simpa only [inv_inv] using h,
        fun n hn => by
          have h := ihx.1 n hn
          simpa only [inv_inv] using h⟩
  have hKnormal : K.Normal := ⟨fun n hn g => (hG_norm g).1 n hn⟩
  -- `K ≠ 1`
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    have hDH : twoPoint H t = H := by
      have hsup := h.sup_eq
      rw [hQbot, bot_sup_eq] at hsup
      exact hsup
    have hodd : Odd (Nat.card H) := hDH ▸ h.stronglyEmbedded.2.2 t h.not_mem
    exact (Nat.not_even_iff_odd.mpr hodd) h.stronglyEmbedded.2.1
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hQle : Q ≤ (⊥ : Subgroup G) := by rw [← hKbot]; exact hQK
    exact hQne (le_bot_iff.mp hQle)
  have hKtop : K = ⊤ := hKnormal.eq_bot_or_eq_top.resolve_left hKne
  -- conclude
  refine le_antisymm le_top ?_
  rw [← hKtop]
  refine (Subgroup.closure_le _).mpr ?_
  intro y hy
  rcases hy with hy | hy
  · exact Subgroup.subset_closure (Or.inl hy)
  · obtain ⟨x, hx, rfl⟩ := hy
    exact mul_mem (mul_mem (Subgroup.subset_closure (Or.inr rfl))
      (Subgroup.subset_closure (Or.inl hx))) (Subgroup.subset_closure (Or.inr rfl))

end Work.RankOneUniqueness
