import Mathlib
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.centDLowerCentralizerS`

Peterfalvi II, Ch. V §2 Lemma 3 a) (the half of it that is needed here): in split rank-one
data `H = Q ⋊ D`, `D = H ∩ Hᵗ`, if `s ∈ Q` is the *distinguished involution* of `Q` relative
to `t` — i.e. there is `r ∈ Q` with the structure identity

  `t * s * t = r⁻¹ * t * r`   (Peterfalvi's Ch. V §2 Lemma 1 b)

— then `V = C_D(t) = D ⊓ C_G(t)` centralises `s`:

  `centD H t ≤ Subgroup.centralizer {s}`.

Proof of the inclusion. Let `d ∈ C_D(t)`. Conjugating the structure identity by `d` (which
fixes `t`) gives a second solution `(d s d⁻¹, d r d⁻¹)` of the same identity; by uniqueness of
the solution (`Work.ThmF.ChV12.structureIdentity`), `d s d⁻¹ = s`, i.e. `d` centralises `s`.

The counting half of the source's Lemma 3 a) (`|D ⊓ C_G(s)| ≤ |C_D(t)|`, giving the reverse
inclusion) is not needed for the `≤` statement requested here.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.Prove

open Submission.Blueprint

theorem centDLowerCentralizerS {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q)
    (hsr : t * s * t = r⁻¹ * t * r) :
    Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({s} : Set G) := by
  classical
  -- ## The involution `t` and the distinguished pair `(s, r)`
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [hsplit.invol, pow_two] at h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨p, _hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hsplit)
  have hsr' : t * s * t⁻¹ = r⁻¹ * t * (r⁻¹)⁻¹ := by
    rw [htinv, inv_inv]
    exact hsr
  have hsp : s = p.1 := by
    have h1 : (s, r⁻¹) = p := huniq (s, r⁻¹) ⟨hs, hs2, Q.inv_mem hr, hsr'⟩
    exact congrArg Prod.fst h1
  -- ## `C_D(t) ≤ D ⊓ C_G(s)`
  have hle : Submission.Blueprint.centD H t ≤
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
    refine le_inf inf_le_left ?_
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨hdD, hdC⟩ := Subgroup.mem_inf.mp hd
    have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
    have hdQ : ∀ x ∈ Q, d * x * d⁻¹ ∈ Q :=
      fun x hx => (Subgroup.mem_normalizer_iff.mp (hsplit.normal hdH) x).mp hx
    have hds2 : orderOf (d * s * d⁻¹) = 2 := by
      rw [Work.ThmF.Bender.orderOf_conj_eq, hs2]
    -- conjugating the structure identity by `d` (which centralises `t`) gives another solution
    have hconj : t * (d * s * d⁻¹) * t⁻¹ =
        (d * r * d⁻¹)⁻¹ * t * ((d * r * d⁻¹)⁻¹)⁻¹ := by
      have hdt' : t * d = d * t := hdt.symm
      have hdtd : d * t * d⁻¹ = t := by rw [hdt]; group
      have hdinv : d⁻¹ * t = t * d⁻¹ := by
        have h := congrArg Inv.inv hdt
        exact (by simpa [mul_inv_rev, htinv] using h : t * d⁻¹ = d⁻¹ * t).symm
      rw [htinv]
      calc t * (d * s * d⁻¹) * t
          = (t * d) * s * (d⁻¹ * t) := by group
        _ = (d * t) * s * (t * d⁻¹) := by rw [hdt', hdinv]
        _ = d * (t * s * t) * d⁻¹ := by group
        _ = d * (r⁻¹ * t * r) * d⁻¹ := by rw [hsr]
        _ = (d * r⁻¹ * d⁻¹) * (d * t * d⁻¹) * (d * r * d⁻¹) := by group
        _ = (d * r * d⁻¹)⁻¹ * t * ((d * r * d⁻¹)⁻¹)⁻¹ := by
              rw [hdtd, inv_inv]
              group
    have hds : d * s * d⁻¹ = s :=
      (congrArg Prod.fst (huniq (d * s * d⁻¹, (d * r * d⁻¹)⁻¹)
        ⟨hdQ s hs, hds2, Q.inv_mem (hdQ r hr), hconj⟩)).trans hsp.symm
    exact mul_inv_eq_iff_eq_mul.mp hds
  exact hle.trans inf_le_right

end Work.ThmF.Prove
