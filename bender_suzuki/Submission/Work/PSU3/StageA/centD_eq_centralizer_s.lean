import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.ChV12.structureIdentity
import Submission.Work.ThreePoints.Sec2b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.centD_eq_centralizer_s`

Peterfalvi II, Ch. V §2, Lemma 3 a): in the situation `PSU3Hyp H Q t`, if `s ∈ Q` is the
*distinguished involution* of `Q` relative to `t` — i.e. there is `r ∈ Q` with

  `t * s * t = r⁻¹ * t * r`   (Peterfalvi's structure identity, Ch. V §2 Lemma 1 b) —

then the centraliser in the two-point stabiliser `D = H ∩ Hᵗ` of `t` equals its centraliser
of `s`:

  `V = C_D(t) = D ⊓ C_G(s)`.

The two inclusions are proved as follows.

* `C_D(t) ⊆ C_G(s)`: if `d ∈ D` centralises `t`, then conjugating the structure identity by
  `d` gives another solution `(d s d⁻¹, d r d⁻¹)` of the same identity; the pair is *unique*
  (`Work.ThmF.ChV12.structureIdentity`), so `d s d⁻¹ = s`.
* `D ⊓ C_G(s) ⊆ C_D(t)`: `C_D(t) ⊆ D ⊓ C_G(s)` and `|D ⊓ C_G(s)| ≤ |C_D(t)|` by counting:
  `|D| = |C_D(t)| · |K|` with `K = J(D,t)` (Peterfalvi I, App. I (1)(b)) and
  `|K| ≤ |D : D ⊓ C_G(s)|` (Peterfalvi I, Ch. I §2 Lemma 1, the map `k ↦ k s k⁻¹` being
  injective on `K`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageA

open Submission.Blueprint

/-- Peterfalvi I, Ch. I §2 Prop. 2 (b) together with App. I (1) (b), in the form used for
`centD_eq_centralizer_s`: for an involution `u ∈ H` (with `H` strongly embedded and `t ∉ H` an
involution), the centraliser `D ⊓ C_G(u)` of `u` inside `D = H ⊓ Hᵗ` has at most `|C_D(t)|`
elements.

Indeed `|D| = |C_D(t)| · |K|` where `K = J(D,t)` (App. I (1)(b)) and `|K| ≤ |D : D ⊓ C_G(u)|`
because `k ↦ k * u * k⁻¹` is injective on `K` (Ch. I §2 Lemma 1) with image inside the orbit of
`u` under `D`-conjugation. -/
theorem card_twoPoint_inf_centralizer_le_centD {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {t u : G} (hH : IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H) (hu : u ∈ H)
    (hu2 : orderOf u = 2) :
    Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤
      Nat.card (centD H t) := by
  classical
  have hDcard : Nat.card (twoPoint H t) =
      Nat.card (centD H t) * (invertedBy (twoPoint H t) t).ncard :=
    Work.ThreePoints.card_twoPoint_eq_card_centD_mul_ncard_invertedBy hH ht htH
  -- `|K| ≤ |D : D ⊓ C(u)|`: the map `k ↦ k * u * k⁻¹` is injective on `K` with image in the
  -- orbit of `u` under conjugation by `D`.
  have hindex : (invertedBy (twoPoint H t) t).ncard ≤
      ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (twoPoint H t)).index := by
    set D : Subgroup G := twoPoint H t with hD
    have hinj : Set.InjOn (fun y : G => y * u * y⁻¹) (invertedBy D t : Set G) := by
      simpa only [Work.ThmF.Kset, ← hD] using
        (Work.ThmF.Bender.Kset_conj_injective (H := H) (t := t) hH ht htH hu hu2)
    letI : MulAction ↥D G := MulAction.compHom G (MulAut.conj.comp D.subtype)
    have hsmul : ∀ (x : ↥D) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := by
      intro x g
      rw [show x • g = (MulAut.conj (x : G)) • g from rfl, MulAut.smul_def, MulAut.conj_apply]
    have hstab : MulAction.stabilizer ↥D u
        = (D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D := by
      ext x
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        rw [hsmul] at h
        exact ⟨x.2, (mul_inv_eq_iff_eq_mul.mp h)⟩
      · rintro ⟨-, hx⟩
        rw [hsmul]
        exact mul_inv_eq_iff_eq_mul.mpr hx
    have hsub : ((fun y : G => y * u * y⁻¹) '' (invertedBy D t : Set G))
        ⊆ MulAction.orbit ↥D u := by
      rintro w ⟨y, hy, rfl⟩
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨y, hy.1⟩, ?_⟩
      rw [hsmul]
    calc (invertedBy D t).ncard
        = ((fun y : G => y * u * y⁻¹) '' (invertedBy D t : Set G)).ncard :=
          (hinj.ncard_image).symm
      _ ≤ (MulAction.orbit ↥D u).ncard := Set.ncard_le_ncard hsub
      _ = ((D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D).index := by
            rw [← hstab, MulAction.index_stabilizer]
  -- `|D| = [D : D ⊓ C(u)] · |D ⊓ C(u)|`
  have hCeq : Nat.card ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
        (twoPoint H t))
      = Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : _ ≤ twoPoint H t)).toEquiv
  have hDcard' : Nat.card (twoPoint H t) =
      ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (twoPoint H t)).index *
        Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
    have h := Subgroup.card_mul_index
      ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (twoPoint H t))
    rw [hCeq] at h
    exact h.symm.trans (Nat.mul_comm _ _)
  have hKpos : 0 < (invertedBy (twoPoint H t) t).ncard := by
    refine (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, ?_⟩
    exact ⟨(twoPoint H t).one_mem, by simp⟩
  refine Nat.le_of_mul_le_mul_left ?_ hKpos
  calc (invertedBy (twoPoint H t) t).ncard *
        Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G)
      ≤ ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (twoPoint H t)).index *
        Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
        Nat.mul_le_mul_right _ hindex
    _ = Nat.card (twoPoint H t) := hDcard'.symm
    _ = Nat.card (centD H t) * (invertedBy (twoPoint H t) t).ncard := hDcard
    _ = (invertedBy (twoPoint H t) t).ncard * Nat.card (centD H t) := Nat.mul_comm _ _

theorem centD_eq_centralizer_s {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {s r : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q)
    (hsr : t * s * t = r⁻¹ * t * r) :
    Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
  classical
  have hH : IsStronglyEmbedded H := hS.split.stronglyEmbedded
  have ht : orderOf t = 2 := hS.split.invol
  have htH : t ∉ H := hS.split.not_mem
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- The structure identity of Ch. V §2 Lemma 1 b): the pair `(s, ρ)` with `s ∈ Inv Q`,
  -- `ρ ∈ Q` and `t s t⁻¹ = ρ t ρ⁻¹` is unique.
  obtain ⟨p, hp, huniq⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hS.split)
  -- `(s, r⁻¹)` is such a pair, so it *is* `p`.
  have hsr' : t * s * t⁻¹ = r⁻¹ * t * (r⁻¹)⁻¹ := by
    rw [htinv, inv_inv]
    exact hsr
  have hsp : s = p.1 := by
    have h1 : (s, r⁻¹) = p := huniq (s, r⁻¹) ⟨hs, hs2, Q.inv_mem hr, hsr'⟩
    exact congrArg Prod.fst h1
  -- ## First inclusion: `V = C_D(t) ≤ D ⊓ C_G(s)`
  have hVle : Submission.Blueprint.centD H t ≤
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) := by
    refine le_inf inf_le_left ?_
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdD : d ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hd).1
    have hdC : d ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hd).2
    have hdt : d * t = t * d := Subgroup.mem_centralizer_singleton_iff.mp hdC
    have hdH : d ∈ H := (Subgroup.mem_inf.mp hdD).1
    have hdNQ : d ∈ Subgroup.normalizer (Q : Set G) := hS.split.normal hdH
    have hdQ : ∀ x ∈ Q, d * x * d⁻¹ ∈ Q :=
      fun x hx => (Subgroup.mem_normalizer_iff.mp hdNQ x).mp hx
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
    have hds : d * s * d⁻¹ = s := by
      have h1 : (d * s * d⁻¹, (d * r * d⁻¹)⁻¹) = p :=
        huniq _ ⟨hdQ s hs, hds2, Q.inv_mem (hdQ r hr), hconj⟩
      have h2 : d * s * d⁻¹ = p.1 := congrArg Prod.fst h1
      rw [h2, ← hsp]
    exact mul_inv_eq_iff_eq_mul.mp hds
  -- ## Counting: `|D ⊓ C_G(s)| ≤ |V|`
  have hcard : Nat.card (Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer ({s} : Set G) : Subgroup G) ≤
      Nat.card (Submission.Blueprint.centD H t) :=
    card_twoPoint_inf_centralizer_le_centD hH ht htH (hS.split.le hs) hs2
  exact Subgroup.eq_of_le_of_card_ge hVle hcard

end Work.PSU3.StageA
