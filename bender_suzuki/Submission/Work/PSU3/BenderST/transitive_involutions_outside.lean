import Mathlib
import Submission.Work.ThmF.ChV12.canonicalForm
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.BenderST

/-- Peterfalvi II Ch. V §2, remark after Lemma 1: for split rank-one data `(H,Q,t)` in a finite
group in which the involution `t` inverts the two-point stabiliser `D = H ∩ H^t`, the subgroup
`H` is transitive on the involutions of `G` outside `H`.  Proof: `canonicalForm` writes
`t' = a * t * q` (`a ∈ H`, `q ∈ Q`); `t'² = 1` forces `q * a ∈ D`; writing `q * a = u * d`
(`u ∈ Q`, `d ∈ D`) the same identity forces `u = 1`, so `t' = a * t * d * a⁻¹`, and a square
root of `d` in the odd-order group `D` conjugates `t` to `t'`.  See
`Submission/Work/PSU3/BenderST/ROUTE.md`. -/
theorem transitive_involutions_outside {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hinv : ∀ d ∈ Submission.Blueprint.twoPoint H t, t * d * t = d⁻¹)
    {t' : G} (ht' : orderOf t' = 2) (ht'H : t' ∉ H) :
    ∃ h ∈ H, t' = h * t * h⁻¹ := by
  -- `t` is an involution, hence `t⁻¹ = t`
  have hti : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self h
  -- `t'` is an involution
  have ht'2 : t' * t' = 1 := by
    have h1 := pow_orderOf_eq_one t'
    rw [ht', pow_two] at h1
    exact h1
  -- canonical form of `t' ∉ H`: `t' = a * t * q` with `a ∈ H`, `q ∈ Q`
  have hex : ∃ a ∈ H, ∃ q ∈ Q, a * t * q = t' := by
    obtain ⟨p, hp, _huniq⟩ :=
      Work.ThmF.ChV12.canonicalForm (Work.ThmF.IsSplitRankOne.toData h) t' ht'H
    exact ⟨p.1, hp.1, p.2, hp.2.1, hp.2.2⟩
  obtain ⟨a, ha, q, hq, haq⟩ := hex
  -- `t'² = 1` forces `t * (q * a) * t = (q * a)⁻¹`
  have hkey : t * (q * a) * t = (q * a)⁻¹ := by
    have h1 : a * t * q * (a * t * q) = 1 := by rw [haq, ht'2]
    rw [mul_inv_rev]
    calc t * (q * a) * t = a⁻¹ * (a * t * q * (a * t * q)) * q⁻¹ := by group
      _ = a⁻¹ * 1 * q⁻¹ := by rw [h1]
      _ = a⁻¹ * q⁻¹ := by group
  have hqaH : q * a ∈ H := H.mul_mem (h.le hq) ha
  -- hence `q * a ∈ D = H ∩ Hᵗ`
  have hqaD : q * a ∈ Submission.Blueprint.twoPoint H t := by
    have hmem : t⁻¹ * (q * a) * t ∈ H := by
      rw [hti, hkey]
      exact H.inv_mem hqaH
    exact ⟨hqaH, Work.Models.mem_conj_iff.mpr hmem⟩
  -- write `a = q₁ * d₁` with `q₁ ∈ Q`, `d₁ ∈ D`
  obtain ⟨q₁, hq₁, d₁, hd₁, haq₁⟩ := Work.RankOneUniqueness.fact_exists h ha
  have hqd : q * a = (q * q₁) * d₁ := by rw [haq₁]; group
  have huQ : q * q₁ ∈ Q := Q.mul_mem hq hq₁
  have huD : q * q₁ ∈ Submission.Blueprint.twoPoint H t := by
    have hsplit : q * q₁ = (q * a) * d₁⁻¹ := by rw [hqd]; group
    rw [hsplit]
    exact (Submission.Blueprint.twoPoint H t).mul_mem hqaD
      ((Submission.Blueprint.twoPoint H t).inv_mem hd₁)
  -- `Q ∩ D = 1` forces `q * q₁ = 1`, i.e. `q * a = d₁`
  have hu1 : q * q₁ = 1 := by
    have hmem : q * q₁ ∈ Q ⊓ Submission.Blueprint.twoPoint H t := ⟨huQ, huD⟩
    rw [h.inf_eq] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hqad : q * a = d₁ := by rw [hqd, hu1, one_mul]
  have ha' : a = q⁻¹ * d₁ := by
    have h2 : q * a = q * (q⁻¹ * d₁) := by rw [hqad]; group
    exact mul_left_cancel h2
  -- `D` has odd order, so `d₁` has a square root `s ∈ D`
  have hDodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
    Work.ThmF.split_odd_card_twoPoint h
  have hsqbij : Function.Bijective
      (fun x : ↥(Submission.Blueprint.twoPoint H t) => x ^ 2) :=
    Nat.Coprime.pow_left_bijective (Nat.coprime_two_right.mpr hDodd)
  obtain ⟨s, hs⟩ := hsqbij.2 ⟨d₁, hd₁⟩
  have hsD : (s : G) ∈ Submission.Blueprint.twoPoint H t := s.2
  have hsH : (s : G) ∈ H := (Subgroup.mem_inf.mp s.2).1
  have hsq : (s : G) * (s : G) = d₁ := by
    have h := congrArg (fun z : ↥(Submission.Blueprint.twoPoint H t) => (z : G)) hs
    simpa [pow_two] using h
  -- `s` conjugates `t` to `d₁ * t`
  have hsconj : (s : G) * t * (s : G)⁻¹ = d₁ * t := by
    have hst : t * (s : G) * t⁻¹ = (s : G)⁻¹ := by
      rw [hti]; exact hinv (s : G) hsD
    have h1 : t * (s : G)⁻¹ * t⁻¹ = (s : G) := by
      calc t * (s : G)⁻¹ * t⁻¹ = (t * (s : G) * t⁻¹)⁻¹ := by group
        _ = ((s : G)⁻¹)⁻¹ := by rw [hst]
        _ = (s : G) := inv_inv _
    calc (s : G) * t * (s : G)⁻¹
        = (s : G) * (t * (s : G)⁻¹ * t⁻¹) * t := by group
      _ = (s : G) * (s : G) * t := by rw [h1]
      _ = d₁ * t := by rw [hsq]
  -- conclude, with the conjugating element `q⁻¹ * s ∈ H`
  refine ⟨q⁻¹ * (s : G), H.mul_mem (H.inv_mem (h.le hq)) hsH, ?_⟩
  have hh : q⁻¹ * (s : G) * t * (q⁻¹ * (s : G))⁻¹ = t' := by
    calc q⁻¹ * (s : G) * t * (q⁻¹ * (s : G))⁻¹
        = q⁻¹ * ((s : G) * t * (s : G)⁻¹) * q := by group
      _ = q⁻¹ * (d₁ * t) * q := by rw [hsconj]
      _ = q⁻¹ * d₁ * t * q := by group
      _ = a * t * q := by rw [ha']
      _ = t' := haq
  exact hh.symm

end Work.PSU3.BenderST
