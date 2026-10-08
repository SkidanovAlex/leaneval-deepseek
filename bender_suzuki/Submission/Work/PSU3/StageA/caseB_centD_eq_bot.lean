import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.RankOneUniqueness.closure_Q_t_eq_top
import Submission.Work.PSU3.StageA.centD_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.PSU3.StageA

open scoped Pointwise

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-!
# case (b) is the Zassenhaus case (Peterfalvi II, Ch. VI §2 p. 261 and §3 p. 264)

In case (b) of the Proposition of Ch. VI §1 — `Q` non-abelian of order `|Q₀|²`, `s * t` of
order 5, `W = 1` — the set `G₀ := (Q · K) ∪ (Q · K · t · Q)` with `K = J(D,t) = Work.ThmF.Kset H t`
is a subgroup of `G` (Ch. VI §2: `t x t ∈ QKtQ` for every `x ∈ Q#`, i.e. `h(x) ∈ K`).

Since `⟨Q, t⟩ = ⊤` in this situation (`Work.RankOneUniqueness.closure_Q_t_eq_top`), the carrier of
`G₀` is all of `G`.  As `V ⊆ H` while `QKtQ ∩ H = ∅`, this forces `V ⊆ QK`; and `QK ∩ D = K`
together with `V ∩ K = 1` (`t` inverts `K`, centralises `V`, and `|D|` is odd) gives `V = 1`.

## Structure of the proof here

* `caseB_Ksub_eq_Kset` — Peterfalvi II Ch. V §1 Proposition 2 in the branch `W = 1`:
  `K = J(D,t)` *is* a subgroup, `Ksub H t = Kset H t`.
* `caseB_tQt_subset` — Peterfalvi II Ch. VI §2 Proposition: `t x t ∈ Q · K · t · Q` for `x ∈ Q`.
* `G0set_subgroup` — the elementary closure of `G₀ = QK ∪ QKtQ` given `tQt ⊆ QKtQ` (below).
* the assembly: `G₀` contains `Q` and `t`, hence equals `G`; then `H ⊆ QK`, so `twoPoint H t ⊆ QK`
  and (as `twoPoint H t` is `t`-stable and `t ∉ H`) `twoPoint H t ⊆ QK ∩ (QK)^t = K`; then
  `V ≤ Kset H t` and `V ∩ Kset H t = 1` give `V = ⊥`, contradicting `centD_ne_bot`.

⚠ **The Ch. V §1 Prop. 2 input is genuinely needed and is not F–T-free** in the source
(Appendix X).  It is isolated as `caseB_Ksub_eq_Kset`.
-/

-- Superseded (2026): the hole-carrying `caseB_Ksub_eq_Kset` was removed by the hole sweep.
-- The proved replacement of the branch is `Work.PSU3.StageA.caseB_false` (Ch. V §1 Prop. 2 in
-- this branch is Appendix X / Feit–Thompson, cf. `ThmF.ChV12.Ksub_cyclic_normal`).

-- Superseded (2026): the hole-carrying `caseB_tQt_subset` was removed by the hole sweep.

variable {G : Type} [Group G] {H Q K : Subgroup G} {t : G}

/-- The carrier of the "Suzuki subgroup" `G₀ = QK ∪ QK·t·Q`. -/
private def G0set (Q K : Subgroup G) (t : G) : Set G :=
  ((Q ⊔ K : Subgroup G) : Set G) ∪
    {x : G | ∃ p : G, p ∈ (Q ⊔ K : Subgroup G) ∧ ∃ q : G, q ∈ Q ∧ x = p * t * q}

private theorem mem_G0set {Q K : Subgroup G} {t x : G} :
    x ∈ G0set Q K t ↔ x ∈ (Q ⊔ K : Subgroup G) ∨
      ∃ p : G, p ∈ (Q ⊔ K : Subgroup G) ∧ ∃ q : G, q ∈ Q ∧ x = p * t * q :=
  Iff.rfl

/-- `Kset H t` is closed under inverses. -/
private theorem Kset_inv_mem' {k : G} (hk : k ∈ Work.ThmF.Kset H t) :
    k⁻¹ ∈ Work.ThmF.Kset H t := by
  obtain ⟨hkD, hkinv⟩ := Work.ThmF.mem_Kset_iff.mp hk
  refine Work.ThmF.mem_Kset_iff.mpr ⟨(twoPoint H t).inv_mem hkD, ?_⟩
  rw [show t * k⁻¹ * t⁻¹ = (t * k * t⁻¹)⁻¹ by group, hkinv, inv_inv]

/-- **The closure of `G₀ = QK ∪ QK·t·Q`.**  If `t` is an involution inverting a subgroup `K ≤ H`
elementwise, `Q ⊴ H`, and `t Q t ⊆ Q·K·t·Q`, then `G₀` is the carrier of a subgroup. -/
private theorem G0set_subgroup (ht2 : t * t = 1) (hKH : K ≤ H)
    (hQH : H ≤ Subgroup.normalizer (Q : Set G))
    (hKinv : ∀ k ∈ K, t * k * t = k⁻¹)
    (hQt : ∀ x ∈ Q, ∃ a ∈ Q, ∃ k ∈ K, ∃ b ∈ Q, t * x * t = a * k * t * b) :
    ∃ S : Subgroup G, (S : Set G) = G0set Q K t := by
  classical
  have hKN : K ≤ Subgroup.normalizer (Q : Set G) := hKH.trans hQH
  set P : Subgroup G := Q ⊔ K with hPdef
  have hPK : ((P : Set G)) = (Q : Set G) * (K : Set G) := by
    rw [hPdef]; exact Subgroup.coe_mul_of_right_le_normalizer_left Q K hKN
  have memP : ∀ x : G, x ∈ (P : Set G) ↔ ∃ q ∈ Q, ∃ k ∈ K, q * k = x := by
    intro x
    rw [hPK, Set.mem_mul]
    exact ⟨fun h => h, fun h => h⟩
  set A : Set G := {x : G | ∃ p : G, p ∈ (P : Set G) ∧ ∃ q : G, q ∈ Q ∧ x = p * t * q}
    with hAdef
  have memA : ∀ x : G, x ∈ A ↔ ∃ p ∈ (P : Set G), ∃ q ∈ Q, x = p * t * q := fun x => Iff.rfl
  have hKt : ∀ k ∈ K, k * t = t * k⁻¹ := by
    intro k hk
    have h2 : t * (t * k * t) * t = k := by
      rw [show t * (t * k * t) * t = (t * t) * k * (t * t) from by group]
      simp only [ht2, one_mul, mul_one]
    calc k * t = (t * (t * k * t) * t) * t := by rw [h2]
      _ = t * (t * k * t) := by rw [mul_assoc, ht2, mul_one]
      _ = t * k⁻¹ := by rw [hKinv k hk]
  have hKt' : ∀ k ∈ K, t * k = k⁻¹ * t := by
    intro k hk
    calc t * k = t * k * (t * t) := by rw [ht2, mul_one]
      _ = (t * k * t) * t := by group
      _ = k⁻¹ * t := by rw [hKinv k hk]
  have hQtA : ∀ x ∈ Q, t * x * t ∈ A := by
    intro x hx
    obtain ⟨a, ha, k, hk, b, hb, h⟩ := hQt x hx
    exact (memA _).mpr ⟨a * k, P.mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hk),
      b, hb, h⟩
  have hPtP : ∀ p ∈ (P : Set G), ∀ y ∈ (P : Set G), p * t * y ∈ A := by
    intro p hp y hy
    obtain ⟨q₁, hq₁, k₁, hk₁, h₁⟩ := (memP p).mp hp
    obtain ⟨q₂, hq₂, k₂, hk₂, h₂⟩ := (memP y).mp hy
    obtain ⟨a, ha, k, hk, b, hb, hc₁⟩ := hQt q₂ hq₂
    obtain ⟨a', ha', k', hk', b', hb', hc₂⟩ := hQt b hb
    have hkey : k₁ * t * q₂ = (k₁ * a * k * a' * k') * t * b' := by
      calc k₁ * t * q₂ = k₁ * (t * q₂ * t) * t := by
            rw [show k₁ * (t * q₂ * t) * t = k₁ * t * q₂ * (t * t) from by group, ht2, mul_one]
        _ = k₁ * (a * k * t * b) * t := by rw [hc₁]
        _ = (k₁ * a * k) * (t * b * t) := by group
        _ = (k₁ * a * k) * (a' * k' * t * b') := by rw [hc₂]
        _ = (k₁ * a * k * a' * k') * t * b' := by group
    have hk₂inv : k₂⁻¹ ∈ K := K.inv_mem hk₂
    have hnorm : k₂⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hKN hk₂inv
    have hkq : k₂⁻¹ * b' * k₂ ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp hnorm b').mp hb'
    have hb'k₂ : b' * k₂ = k₂ * (k₂⁻¹ * b' * k₂) := by group
    refine (memA _).mpr ⟨q₁ * (k₁ * a * k * a' * k') * k₂⁻¹, ?_, k₂⁻¹ * b' * k₂, hkq, ?_⟩
    · have h1 : k₁ ∈ (P : Set G) := Subgroup.mem_sup_right hk₁
      have h2 : k₁ * a ∈ (P : Set G) := P.mul_mem h1 (Subgroup.mem_sup_left ha)
      have h3 : k₁ * a * k ∈ (P : Set G) := P.mul_mem h2 (Subgroup.mem_sup_right hk)
      have h4 : k₁ * a * k * a' ∈ (P : Set G) := P.mul_mem h3 (Subgroup.mem_sup_left ha')
      have h5 : k₁ * a * k * a' * k' ∈ (P : Set G) :=
        P.mul_mem h4 (Subgroup.mem_sup_right hk')
      have h6 : q₁ * (k₁ * a * k * a' * k') ∈ (P : Set G) :=
        P.mul_mem (Subgroup.mem_sup_left hq₁) h5
      exact P.mul_mem h6 (Subgroup.mem_sup_right hk₂inv)
    · rw [← h₁, ← h₂]
      calc q₁ * k₁ * t * (q₂ * k₂) = q₁ * (k₁ * t * q₂) * k₂ := by group
        _ = q₁ * ((k₁ * a * k * a' * k') * t * b') * k₂ := by rw [hkey]
        _ = (q₁ * (k₁ * a * k * a' * k') * k₂⁻¹) * t * (k₂⁻¹ * b' * k₂) := by
              calc q₁ * ((k₁ * a * k * a' * k') * t * b') * k₂
                  = q₁ * (k₁ * a * k * a' * k') * t * (b' * k₂) := by group
                _ = q₁ * (k₁ * a * k * a' * k') * t * (k₂ * (k₂⁻¹ * b' * k₂)) := by
                      rw [hb'k₂]
                _ = q₁ * (k₁ * a * k * a' * k') * (t * k₂) * (k₂⁻¹ * b' * k₂) := by group
                _ = q₁ * (k₁ * a * k * a' * k') * (k₂⁻¹ * t) * (k₂⁻¹ * b' * k₂) := by
                      rw [hKt' k₂ hk₂]
                _ = (q₁ * (k₁ * a * k * a' * k') * k₂⁻¹) * t * (k₂⁻¹ * b' * k₂) := by group
  have hAP : ∀ a ∈ A, ∀ b ∈ (P : Set G), a * b ∈ A := by
    intro a ha b hb
    obtain ⟨p, hp, q, hq, rfl⟩ := (memA a).mp ha
    have h : p * t * q * b = p * t * (q * b) := by group
    rw [h]
    exact hPtP p hp (q * b) (P.mul_mem (Subgroup.mem_sup_left hq) hb)
  have hPA : ∀ a ∈ (P : Set G), ∀ b ∈ A, a * b ∈ A := by
    intro a ha b hb
    obtain ⟨p, hp, q, hq, rfl⟩ := (memA b).mp hb
    exact (memA _).mpr ⟨a * p, P.mul_mem ha hp, q, hq, by group⟩
  have hAA : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A := by
    intro a ha b hb
    obtain ⟨p, hp, q, hq, rfl⟩ := (memA a).mp ha
    obtain ⟨p', hp', q', hq', rfl⟩ := (memA b).mp hb
    have h1 : p * t * q * (p' * t * q') = p * (t * (q * p') * t) * q' := by group
    rw [h1]
    have hmid : t * (q * p') * t ∈ A := by
      obtain ⟨q₃, hq₃, k₃, hk₃, h₃⟩ :=
        (memP (q * p')).mp (P.mul_mem (Subgroup.mem_sup_left hq) hp')
      have h4 : t * (q₃ * k₃) * t = (t * q₃ * t) * k₃⁻¹ := by
        rw [show t * (q₃ * k₃) * t = t * q₃ * (k₃ * t) from by group]
        rw [hKt k₃ hk₃]
        group
      rw [← h₃, h4]
      exact hAP (t * q₃ * t) (hQtA q₃ hq₃) k₃⁻¹ (Subgroup.mem_sup_right (K.inv_mem hk₃))
    exact hAP (p * (t * (q * p') * t)) (hPA p hp (t * (q * p') * t) hmid) q'
      (Subgroup.mem_sup_left hq')
  have hAinv : ∀ a ∈ A, a⁻¹ ∈ A := by
    intro a ha
    obtain ⟨p, hp, q, hq, rfl⟩ := (memA a).mp ha
    obtain ⟨q₁, hq₁, k₁, hk₁, h₁⟩ := (memP p).mp hp
    have hk1inv : k₁⁻¹ ∈ K := K.inv_mem hk₁
    have hnorm : k₁⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hKN hk1inv
    have hqQ : k₁⁻¹ * q⁻¹ * k₁ ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp hnorm q⁻¹).mp (Q.inv_mem hq)
    refine (memA _).mpr ⟨k₁ * (k₁⁻¹ * q⁻¹ * k₁), ?_, q₁⁻¹, Q.inv_mem hq₁, ?_⟩
    · exact P.mul_mem (Subgroup.mem_sup_right hk₁) (Subgroup.mem_sup_left hqQ)
    · rw [← h₁]
      calc (q₁ * k₁ * t * q)⁻¹ = q⁻¹ * t * k₁⁻¹ * q₁⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right ht2]
              group
        _ = q⁻¹ * (t * k₁⁻¹) * q₁⁻¹ := by group
        _ = q⁻¹ * (k₁ * t) * q₁⁻¹ := by rw [hKt' k₁⁻¹ hk1inv]; group
        _ = (k₁ * (k₁⁻¹ * q⁻¹ * k₁)) * t * q₁⁻¹ := by group
  refine ⟨{ carrier := (P : Set G) ∪ A
            one_mem' := Or.inl (P.one_mem)
            mul_mem' := ?_
            inv_mem' := ?_ }, ?_⟩
  · intro a b ha hb
    rw [Set.mem_union] at ha hb ⊢
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (P.mul_mem ha hb)
    · exact Or.inr (hPA a ha b hb)
    · exact Or.inr (hAP a ha b hb)
    · exact Or.inr (hAA a ha b hb)
  · intro a ha
    rw [Set.mem_union] at ha ⊢
    rcases ha with ha | ha
    · exact Or.inl (P.inv_mem ha)
    · exact Or.inr (hAinv a ha)
  · rfl

-- Superseded (2026): the hole-carrying `caseB_centD_eq_bot` was removed by the hole sweep;
-- its proved replacements are `Work.PSU3.StageA.caseB_false` and
-- `Work.PSU3.StageA.caseB_centD_eq_bot_of_Ksub_of_canonical` (both in `StageA/`).

end Work.PSU3.StageA
