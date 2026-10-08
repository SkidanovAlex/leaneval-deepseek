import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.ChV12.prop3

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.nm_injective_on_fixed`

The map `nm : Eˣ → Eˣ` of a `CoarseFrame` is Peterfalvi's action of `K = Ksub H t` on
`Q₀ = Z(Q) ≅ F` (Ch. VII §2): `act_zc_K` says that conjugation by `d ∈ Ksub` acts on
`Q₀ = zc(F)` by multiplication by `nm (κ d)`.

Since `κ : KW ↪ Eˣ` carries `Ksub` bijectively onto the `σE`-fixed units of `E n` (`K_surj`
plus `mem_K_iff`) and `zc` carries the `σE`-fixed units bijectively onto
`Inv(H) = Q₀ ∖ {1}`, the frame *forces*

  `|Ksub H t| = |F*| = |Inv(H)| = |Kset H t|`,

so `Kset H t = Ksub H t` (as `Kset ⊆ closure (Kset) = Ksub`).  Hence a nontrivial `d ∈ Ksub`
acts fixed-point-freely on `Inv(H)` (`Kset_conj_injective`), and therefore `nm` is injective
on `F*`: if `nm a = 1`, the element `d ∈ Ksub` with `κ d = a` centralises `Q₀`, in particular
the involution `s = zc 1 ∈ Inv(H)`, so `d = 1` and `a = κ d = 1`.

The key point is that the upper bound `|Ksub| ≤ |F*|` is *not* an extra group-theoretic
hypothesis (Ch. V §1 Prop. 2 / App. X): it is already contained in the frame's `κ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.ThmF

namespace Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- The `σE`-fixed units of `E n = GF(2^(2n))`: the units of the fixed field
`F = GF(2ⁿ)`. -/
noncomputable def fixedUnits (n : ℕ) : Type :=
  {a : (Work.PSU3.E n)ˣ //
    Work.PSU3.σE (a : Work.PSU3.E n) = (a : Work.PSU3.E n)}

/-! ## `κ` maps `Ksub` bijectively onto `F*` -/

/-- `κ` restricted to `Ksub H t` is a bijection onto the `σE`-fixed units of `E n`. -/
lemma kappa_bijective_fixedUnits (fr : Work.PSU3.CoarseFrame H Q t n) :
    Function.Bijective (fun d : ↥(Ksub H t) =>
      (⟨fr.κ ((Subgroup.inclusion fr.K_le) d),
          (fr.mem_K_iff ((Subgroup.inclusion fr.K_le) d)).mp (by simpa using d.2)⟩ :
        fixedUnits n)) := by
  constructor
  · intro d d' h
    have h1 : fr.κ ((Subgroup.inclusion fr.K_le) d) =
        fr.κ ((Subgroup.inclusion fr.K_le) d') := congrArg Subtype.val h
    have h2 : (Subgroup.inclusion fr.K_le) d = (Subgroup.inclusion fr.K_le) d' :=
      fr.κ_injective h1
    exact Subtype.ext (by
      simpa [Subgroup.coe_inclusion] using congrArg (fun x : fr.KW => (x : G)) h2)
  · intro a
    obtain ⟨d0, hd0⟩ := fr.K_surj a.1 a.2
    have hmem : (d0 : G) ∈ Ksub H t := (fr.mem_K_iff d0).mpr (by rw [hd0]; exact a.2)
    refine ⟨⟨(d0 : G), hmem⟩, ?_⟩
    apply Subtype.ext
    show fr.κ ((Subgroup.inclusion fr.K_le) (⟨(d0 : G), hmem⟩ : ↥(Ksub H t))) = a.1
    have hKL : (Subgroup.inclusion fr.K_le) (⟨(d0 : G), hmem⟩ : ↥(Ksub H t)) = d0 :=
      Subtype.ext rfl
    rw [hKL, hd0]

/-! ## `zc` maps `F*` bijectively onto `Inv(H)` -/

/-- For a `σE`-fixed unit `a`, the element `zc a` is an involution of `H`. -/
lemma zc_fixedUnit_mem_involutions (hS : Work.PSU3.PSU3Hyp H Q t)
    (fr : Work.PSU3.CoarseFrame H Q t n) {a : (Work.PSU3.E n)ˣ}
    (ha : Work.PSU3.σE (a : Work.PSU3.E n) = (a : Work.PSU3.E n)) :
    fr.zc (a : Work.PSU3.E n) ∈ involutions (H : Set G) := by
  have hQ0 : fr.zc (a : Work.PSU3.E n) ∈ fr.Q0 := fr.zc_mem _ ha
  have hQ : fr.zc (a : Work.PSU3.E n) ∈ Q := fr.Q0_le hQ0
  have hsq : fr.zc (a : Work.PSU3.E n) ^ 2 = 1 := (fr.mem_Q0_iff _ hQ).mp hQ0
  have hne : fr.zc (a : Work.PSU3.E n) ≠ 1 := by
    intro h1
    exact Units.ne_zero a (eq_zero_of_zc_eq_one fr ha h1)
  refine ⟨hS.split.le hQ, ?_⟩
  have hdvd : orderOf (fr.zc (a : Work.PSU3.E n)) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hsq)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

/-- `zc` induces a bijection from the `σE`-fixed units of `E n` onto `Inv(H)`. -/
lemma fixedUnits_bijective_involutions (hS : Work.PSU3.PSU3Hyp H Q t)
    (fr : Work.PSU3.CoarseFrame H Q t n) :
    Function.Bijective (fun a : fixedUnits n =>
      (⟨fr.zc (a.1 : Work.PSU3.E n), zc_fixedUnit_mem_involutions hS fr a.2⟩ :
        ↥(involutions (H : Set G)))) := by
  constructor
  · intro a a' h
    have h1 : fr.zc (a.1 : Work.PSU3.E n) = fr.zc (a'.1 : Work.PSU3.E n) :=
      congrArg Subtype.val h
    exact Subtype.ext (Units.ext (fr.zc_inj (a.1 : Work.PSU3.E n) (a'.1 : Work.PSU3.E n)
      a.2 a'.2 h1))
  · intro x
    have hxH : (x : G) ∈ H := x.2.1
    have hx2 : (x : G) ^ 2 = 1 := by
      rw [← x.2.2]; exact pow_orderOf_eq_one (x : G)
    have hxQ : (x : G) ∈ Q := mem_Q_of_sq_eq_one hS hxH hx2
    have hxQ0 : (x : G) ∈ fr.Q0 := (fr.mem_Q0_iff (x : G) hxQ).mpr hx2
    obtain ⟨y, hyfix, hyzc⟩ := fr.zc_surj (x : G) hxQ0
    have hy0 : y ≠ 0 := by
      intro h0
      have hx1 : (x : G) = 1 := by rw [← hyzc, h0, zc_zero]
      have h2 := x.2.2
      rw [hx1, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    refine ⟨⟨Units.mk0 y hy0, by simpa using hyfix⟩, ?_⟩
    apply Subtype.ext
    show fr.zc ((Units.mk0 y hy0 : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = (x : G)
    simpa using hyzc

/-! ## `Kset H t = Ksub H t` -/

/-- **`Kset H t = Ksub H t`.**  The frame's `κ` bounds `|Ksub H t|` by `|F*|`, and
`|F*| = |Inv(H)| = |Kset H t|`: hence `Kset H t ⊆ Ksub H t` has equal cardinality. -/
lemma Kset_eq_Ksub (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) :
    (Kset H t : Set G) = (Ksub H t : Set G) := by
  have hbij1 := kappa_bijective_fixedUnits (H := H) (Q := Q) (t := t) (n := n) fr
  have hbij2 := fixedUnits_bijective_involutions (H := H) (Q := Q) (t := t) (n := n) hS fr
  have hcard :=
    Bender.cardKsetEqInv (H := H) hS.split.stronglyEmbedded hS.split.invol hS.split.not_mem
  have hKsub : Nat.card ↥(Ksub H t) = (Kset H t).ncard :=
    ((Nat.card_congr (Equiv.ofBijective _ hbij1)).trans
      ((Nat.card_congr (Equiv.ofBijective _ hbij2)).trans
        ((Nat.card_coe_set_eq (involutions (H : Set G))).trans hcard.symm)))
  have hEq : (Kset H t).ncard = (Ksub H t : Set G).ncard := by
    rw [← hKsub]
    exact Nat.card_coe_set_eq (Ksub H t : Set G)
  exact Set.eq_of_subset_of_ncard_le (Subgroup.subset_closure) (le_of_eq hEq.symm)

/-- `s = zc 1` lies in `H` and has order `2`. -/
lemma frameS_mem_H (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) :
    frameS fr ∈ H ∧ orderOf (frameS fr) = 2 := by
  refine ⟨hS.split.le (frameS_mem_Q fr), ?_⟩
  have hdvd : orderOf (frameS fr) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using frameS_sq_eq_one fr)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (frameS_ne_one fr)
  · exact h

theorem nm_injective_on_fixed {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) :
    ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a → fr.nm a = 1 → a = 1 := by
  intro a ha hnm
  -- the element `d ∈ Ksub H t` with `κ d = a`
  obtain ⟨d, hd⟩ := (kappa_bijective_fixedUnits (H := H) (Q := Q) (t := t) (n := n) fr).2
    (⟨a, ha⟩ : fixedUnits n)
  have hdval : fr.κ ((Subgroup.inclusion fr.K_le) d) = a := congrArg Subtype.val hd
  -- `d` centralises `s = zc 1` by `act_zc_K` and `nm a = 1`
  have hcent : (((Subgroup.inclusion fr.K_le) d : fr.KW) : G)⁻¹ * frameS fr *
      (((Subgroup.inclusion fr.K_le) d : fr.KW) : G) = frameS fr := by
    have h := fr.act_zc_K ((Subgroup.inclusion fr.K_le) d)
      (by simpa using d.2) 1 (by simp)
    rw [hdval, hnm] at h
    simpa [frameS] using h
  -- hence `d * s * d⁻¹ = s`
  have hconj : (d : G) * frameS fr * (d : G)⁻¹ = frameS fr := by
    have h2 : (((Subgroup.inclusion fr.K_le) d : fr.KW) : G) = (d : G) :=
      Subgroup.coe_inclusion fr.K_le d
    rw [h2] at hcent
    -- hcent : d⁻¹ * s * d = s, hence `d` commutes with `s`
    have hcomm : (d : G) * frameS fr = frameS fr * (d : G) := by
      have hms := congrArg (fun z => (d : G) * z) hcent
      simpa [mul_assoc] using hms.symm
    calc (d : G) * frameS fr * (d : G)⁻¹
        = frameS fr * (d : G) * (d : G)⁻¹ := by rw [hcomm]
      _ = frameS fr := by group
  -- `d ∈ Kset H t`
  have hdKset : (d : G) ∈ Kset H t := by
    rw [Kset_eq_Ksub hS fr]
    exact d.2
  -- the action of `Kset H t` on `Inv(H)` is fixed-point-free
  have hinj := Bender.Kset_conj_injective (H := H) hS.split.stronglyEmbedded hS.split.invol
    hS.split.not_mem (frameS_mem_H hS fr).1 (frameS_mem_H hS fr).2
  have hd1 : (d : G) = 1 :=
    hinj hdKset (one_mem_Kset H t) (by simpa using hconj)
  have hd_eq : d = 1 := Subtype.ext (by simpa using hd1)
  calc a = fr.κ ((Subgroup.inclusion fr.K_le) d) := hdval.symm
    _ = fr.κ ((Subgroup.inclusion fr.K_le) 1) := by rw [hd_eq]
    _ = 1 := by simp

end Work.PSU3.StageB
