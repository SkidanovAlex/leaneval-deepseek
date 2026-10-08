import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.BenderST.transitive_involutions_outside
import Submission.Work.PSU3.Model.psu3_isSplitRankOne

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.BST

open LeanEval.GroupTheory.Defs Submission.Blueprint

/-- **Peterfalvi II Ch. V §2 (generalised).**  For split rank-one data `(H,Q,t)` in a finite
group, the subgroup `H` is transitive on the involutions of `G` outside `H`: every involution
`t' ∉ H` is conjugate to `t` by an element of `H`.

This is `Work.PSU3.BenderST.transitive_involutions_outside` with the hypothesis
`t * d * t = d⁻¹` (`∀ d ∈ twoPoint H t`) removed.  That hypothesis is unnecessary: it is used
in the original proof only to get `t s t⁻¹ = s⁻¹` where `s ∈ D = twoPoint H t` is the square
root of `qa ∈ D`.  But `t s t⁻¹ ∈ D` and `(t s t⁻¹)² = t (qa) t⁻¹ = (qa)⁻¹ = (s⁻¹)²` (the
middle identity is automatic from `t'² = 1`, and `t = t⁻¹`), so injectivity of squaring on the
odd-order group `D` already gives `t s t⁻¹ = s⁻¹`.  This matters for `PSU(3,2ⁿ)`, where the
Weyl element does *not* invert (`twoPoint psu3B psu3Weyl = psu3T`): it acts on the torus as
`a ↦ a^{-q}`. -/
theorem transitive_involutions_outside' {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {t' : G} (ht' : orderOf t' = 2) (ht'H : t' ∉ H) :
    ∃ h ∈ H, t' = h * t * h⁻¹ := by
  have hti : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self h
  have htt : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one h
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
  -- hence `q * a ∈ D = twoPoint H t`
  have hqaD : q * a ∈ Submission.Blueprint.twoPoint H t := by
    refine Subgroup.mem_inf.mpr ⟨hqaH, ?_⟩
    rw [Work.Models.mem_conj_iff, hti, hkey]
    exact H.inv_mem hqaH
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
    have hh := congrArg (fun z : ↥(Submission.Blueprint.twoPoint H t) => (z : G)) hs
    simpa [pow_two] using hh
  -- `t s t⁻¹ ∈ D`
  have hnormD : t * (s : G) * t⁻¹ ∈ Submission.Blueprint.twoPoint H t := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hti]
      exact Work.RankOneUniqueness.t_mul_mul_t_mem_of_mem_twoPoint htt hsD
    · rw [Work.Models.mem_conj_iff]
      have h2 : t⁻¹ * (t * (s : G) * t⁻¹) * t = (s : G) := by
        rw [hti]
        calc t * (t * (s : G) * t) * t = (t * t) * (s : G) * (t * t) := by group
          _ = 1 * (s : G) * 1 := by rw [htt]
          _ = (s : G) := by group
      rw [h2]
      exact hsH
  -- the identity `t * s * t⁻¹ = s⁻¹` from injectivity of squaring on `D`
  have hx2 : (t * (s : G) * t⁻¹) * (t * (s : G) * t⁻¹) = (s : G)⁻¹ * (s : G)⁻¹ := by
    calc (t * (s : G) * t⁻¹) * (t * (s : G) * t⁻¹)
        = t * ((s : G) * (s : G)) * t⁻¹ := by group
      _ = t * d₁ * t⁻¹ := by rw [hsq]
      _ = d₁⁻¹ := by rw [← hqad, hti]; exact hkey
      _ = ((s : G) * (s : G))⁻¹ := by rw [hsq]
      _ = (s : G)⁻¹ * (s : G)⁻¹ := by rw [mul_inv_rev]
  have hst : t * (s : G) * t⁻¹ = (s : G)⁻¹ := by
    have hsub : (⟨t * (s : G) * t⁻¹, hnormD⟩ : ↥(Submission.Blueprint.twoPoint H t)) =
        ⟨(s : G)⁻¹, (Submission.Blueprint.twoPoint H t).inv_mem hsD⟩ := by
      apply hsqbij.1
      show (⟨t * (s : G) * t⁻¹, hnormD⟩ : ↥(Submission.Blueprint.twoPoint H t)) ^ 2 =
        (⟨(s : G)⁻¹, (Submission.Blueprint.twoPoint H t).inv_mem hsD⟩ :
          ↥(Submission.Blueprint.twoPoint H t)) ^ 2
      rw [pow_two, pow_two]
      apply Subtype.ext
      simpa using hx2
    exact Subtype.ext_iff.mp hsub
  -- `s` conjugates `t` to `d₁ * t`
  have hsconj : (s : G) * t * (s : G)⁻¹ = d₁ * t := by
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

theorem psu3_wTrans (n : ℕ) (hn : 2 ≤ n) :
    ∀ w : LeanEval.GroupTheory.Defs.PSU3Model n,
      orderOf w = 2 → w ∉ (Submission.PSU3.psu3BenderPair n hn).B →
      ∃ b ∈ (Submission.PSU3.psu3BenderPair n hn).B,
        b * w * b⁻¹ = (Submission.PSU3.psu3BenderPair n hn).w := by
  intro w hw hwB
  set P := Submission.PSU3.psu3BenderPair n hn with hP
  have hsplit : Submission.Blueprint.IsSplitRankOne P.B P.U P.w :=
    Work.PSU3.Model.psu3_isSplitRankOne n hn
  obtain ⟨b, hb, hbw⟩ := transitive_involutions_outside' hsplit hw hwB
  exact ⟨b⁻¹, P.B.inv_mem hb, by rw [hbw]; group⟩

end Work.PSU3.BST
