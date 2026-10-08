/-
# `Work.PSU3.StageB.ThetaOmega` — the canonical data of `ω` and the value of `h(ω⁻¹)`

Peterfalvi II, Ch. VII §2–§3, in the vocabulary of `Work.PSU3.CoarseFrame`.

Given a coarse frame `fr`, a split rank-one datum `H Q t`, and `ω` satisfying `OmegaHyp fr ω`
(so that the canonical data of `x = ω` are `f(x) = (x⁻¹)^ζ`, `h(x) ∈ W`), this module pins
down the canonical maps at `x`:

* `g(x)`, `h(x)`, `f(x)` are *completely determined* by the equation
  `t x t = g h t (ζ⁻¹ x⁻¹ ζ)` (uniqueness of the canonical form, `canon_unique''`);
* applying `(f ∘ j)³ = x ↦ x^{h(x)^{-1}}` (H5) to `x` and computing the left-hand side by
  three applications of H3 one obtains `ζ³ x ζ⁻³ = h(x) x h(x)⁻¹`, whence `h(x) = ζ³`
  (semiregularity of `W` on `Q ∖ Q₀`, `W_semireg`) and finally
  `h(x⁻¹) = h(x)^{-t} = ζ⁻³` (§3 (1)).

The main statement is `ThetaOmega`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Theta
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3.StageB

open Work.ThmF
open Work.PSU3

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- The iterated computation `(f ∘ j)³(x) = ζ³ x ζ⁻³` for an `x ∈ Q#` with `f(x) = (x⁻¹)^ζ`
(Peterfalvi II, Ch. VII §2 (2), §3 (1)): three applications of H3
(`fcan_qconj`) to `x⁻¹`, using `t ζ t = ζ`. -/
lemma fcan_jjj_zeta_of (fr : CoarseFrame H Q t n)
    (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {x : ↥Q} (hx : (x : G) ≠ 1)
    (hf : (fcan h x : G) = (fr.ζ : G)⁻¹ * (x : G)⁻¹ * (fr.ζ : G)) :
    (fcan h ((fcan h ((fcan h (x⁻¹))⁻¹))⁻¹) : G) =
      ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G)) * (x : G) *
        ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ := by
  have hzD : (fr.ζ : G) ∈ twoPoint H t := zeta_mem_D fr
  have hziD : (fr.ζ : G)⁻¹ ∈ twoPoint H t := (twoPoint H t).inv_mem hzD
  have hz2iD : ((fr.ζ : G) * (fr.ζ : G))⁻¹ ∈ twoPoint H t :=
    (twoPoint H t).inv_mem ((twoPoint H t).mul_mem hzD hzD)
  have hxinv : ((x⁻¹ : ↥Q) : G) ≠ 1 := inv_ne_one hx
  have hsub1 : fcan h x = qconj h ⟨(fr.ζ : G), hzD⟩ (x⁻¹) := by
    apply Subtype.ext
    rw [qconj_coe, hf]
    rfl
  -- **(1)** `f(x⁻¹) = ζ x ζ⁻¹`
  have h1 : (fcan h (x⁻¹) : G) = (fr.ζ : G) * (x : G) * (fr.ζ : G)⁻¹ := by
    have hconj1 := fcan_qconj h (x := x⁻¹) hxinv ⟨(fr.ζ : G), hzD⟩
    rw [t_zeta_t h fr] at hconj1
    have hff : (fcan h (fcan h x) : G) = (x : G) := (fcan_fcan h hx).1
    rw [← hsub1, hff] at hconj1
    rw [hconj1]
    group
  -- **(2)** `f((f x⁻¹)⁻¹) = ζ² x ζ⁻²`
  have hsub2 : (fcan h (x⁻¹))⁻¹ = qconj h ⟨(fr.ζ : G)⁻¹, hziD⟩ (x⁻¹) := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, h1, qconj_coe]
    push_cast
    group
  have h2 : (fcan h ((fcan h (x⁻¹))⁻¹) : G) =
      ((fr.ζ : G) * (fr.ζ : G)) * (x : G) * ((fr.ζ : G) * (fr.ζ : G))⁻¹ := by
    have hconj2 := fcan_qconj h (x := x⁻¹) hxinv ⟨(fr.ζ : G)⁻¹, hziD⟩
    rw [t_zeta_inv_t h fr] at hconj2
    rw [← hsub2, h1] at hconj2
    rw [hconj2]
    group
  have htζ2 : t * ((fr.ζ : G) * (fr.ζ : G)) * t = (fr.ζ : G) * (fr.ζ : G) := by
    rw [conj_mul_self (mul_self_eq_one h) (fr.ζ : G) (fr.ζ : G), t_zeta_t h fr]
  -- **(3)** `f((f((f x⁻¹)⁻¹))⁻¹) = ζ³ x ζ⁻³`
  have hsub3 : (fcan h ((fcan h (x⁻¹))⁻¹))⁻¹ =
      qconj h ⟨((fr.ζ : G) * (fr.ζ : G))⁻¹, hz2iD⟩ (x⁻¹) := by
    apply Subtype.ext
    rw [Subgroup.coe_inv, h2, qconj_coe]
    push_cast
    group
  have h3 : (fcan h ((fcan h ((fcan h (x⁻¹))⁻¹))⁻¹) : G) =
      ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G)) * (x : G) *
        ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ := by
    have ht3 : t * (⟨((fr.ζ : G) * (fr.ζ : G))⁻¹, hz2iD⟩ : ↥(twoPoint H t)) * t =
        ((fr.ζ : G) * (fr.ζ : G))⁻¹ := by
      show t * ((fr.ζ : G) * (fr.ζ : G))⁻¹ * t = ((fr.ζ : G) * (fr.ζ : G))⁻¹
      rw [← Work.PSU3.RankOne.tdt_inv_eq (a := (fr.ζ : G) * (fr.ζ : G))
        (mul_self_eq_one h), htζ2]
    have hconj3 := fcan_qconj h (x := x⁻¹) hxinv ⟨((fr.ζ : G) * (fr.ζ : G))⁻¹, hz2iD⟩
    rw [ht3] at hconj3
    rw [← hsub3, h1] at hconj3
    rw [hconj3]
    simp only [inv_inv, mul_inv_rev]
    group
  exact h3

/-- **`ThetaOmega`** (Peterfalvi II, Ch. VII §3, the proposition's preliminary computation).
If `t ω t = g h t (ζ⁻¹ ω⁻¹ ζ)` with `g ∈ Q`, `h ∈ W#` and `ω` satisfies `OmegaHyp`, then the
canonical maps at `x = ω` are `g(x) = g`, `h(x) = h`, `f(x) = ζ⁻¹ ω⁻¹ ζ`, and
`h(x⁻¹) = ζ⁻³`. -/
theorem ThetaOmega {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) (h : Submission.Blueprint.IsSplitRankOne H Q t)
    {ω : G} (hω : Work.PSU3.OmegaHyp fr ω) {g : G} (hg : g ∈ Q) {hh : G}
    (hhW : hh ∈ Work.ThmF.W H t)
    (heq : t * ω * t = g * hh * t * ((fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G))) :
    (Work.PSU3.StageB.gcan h (Work.PSU3.StageB.omQ fr hω) : G) = g ∧
    (Work.PSU3.StageB.hcan h (Work.PSU3.StageB.omQ fr hω) : G) = hh ∧
    (Work.PSU3.StageB.fcan h (Work.PSU3.StageB.omQ fr hω) : G) =
      (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) ∧
    (Work.PSU3.StageB.hcan h ((Work.PSU3.StageB.omQ fr hω)⁻¹) : G) =
      (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ := by
  have hωQ : ω ∈ Q := hω.1
  have hωQ0 : ω ∉ fr.Q0 := hω.2.1
  have hx : ((omQ fr hω : ↥Q) : G) ≠ 1 := omQ_ne_one fr hω
  have hxG : ((omQ fr hω : ↥Q) : G) = ω := omQ_coe fr hω
  have hzD : (fr.ζ : G) ∈ twoPoint H t := zeta_mem_D fr
  have hzH : (fr.ζ : G) ∈ H := twoPoint_le_left H t hzD
  have hhmem : (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) ∈ Q := by
    have hc := conj_mem_of_mem h (H.inv_mem hzH) (Q.inv_mem hωQ)
    simpa using hc
  have hhD : hh ∈ twoPoint H t := (Subgroup.mem_inf.mp (W_le_centD H t hhW)).1
  have key := canon_unique'' h hx (g := ⟨g, hg⟩) (d := ⟨hh, hhD⟩)
      (y := ⟨(fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G), hhmem⟩) (by rw [hxG]; exact heq)
  have hgc : (gcan h (omQ fr hω) : G) = g := by simpa using key.1.symm
  have hhc : (hcan h (omQ fr hω) : G) = hh := by simpa using key.2.1.symm
  have hfc : (fcan h (omQ fr hω) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) := by
    simpa using key.2.2.symm
  refine ⟨hgc, hhc, hfc, ?_⟩
  -- `h(ω) = ζ³`, hence `h(ω⁻¹) = h(ω)^{-t} = ζ⁻³`
  have hjj := fcan_jjj h hx
  rw [hhc, hxG] at hjj
  have hzeta := fcan_jjj_zeta_of fr h hx hfc
  rw [hxG] at hzeta
  rw [hzeta] at hjj
  -- `hjj : ζ³ ω ζ⁻³ = hh ω hh⁻¹`
  have hcentral : (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh) * ω *
      (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh)⁻¹ = ω := by
    have h1 : (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh) * ω *
        (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh)⁻¹
        = ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * (hh * ω * hh⁻¹) *
          ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G)) := by
      simp only [mul_inv_rev, inv_inv]
      group
    rw [h1, ← hjj]
    simp only [mul_inv_rev]
    group
  have huW : ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh ∈ W H t :=
    (W H t).mul_mem ((W H t).inv_mem ((W H t).mul_mem
      ((W H t).mul_mem fr.ζ_mem_W fr.ζ_mem_W) fr.ζ_mem_W)) hhW
  have hu1 : ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh = 1 := by
    by_contra hne
    have hcomm : (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh) * ω =
        ω * (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh) := by
      have h3 := congrArg (fun z => z * (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh)) hcentral
      simpa [mul_assoc] using h3
    exact hωQ0 (fr.W_semireg _ huW hne ω hωQ hcomm)
  have hζ3 : hh = (fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G) := by
    calc hh = ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G)) *
          (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G))⁻¹ * hh) := by group
      _ = (fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G) := by rw [hu1, mul_one]
  -- `h(ω⁻¹) = h(ω)^{-t} = hh⁻¹ = ζ⁻³`
  have hinv := hcan_inv h hx
  rw [hhc] at hinv
  have ht_hh : t * hh * t = hh := by
    have hcomm_t : t * hh = hh * t :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (W_le_centD H t hhW)).2) t
        (Set.mem_singleton t)
    rw [hcomm_t, mul_assoc, mul_self_eq_one h, mul_one]
  have ht_hh_inv : t * hh⁻¹ * t = hh⁻¹ := by
    rw [← Work.PSU3.RankOne.tdt_inv_eq (a := hh) (mul_self_eq_one h), ht_hh]
  rw [hinv, ht_hh_inv, hζ3]
  group

end Work.PSU3.StageB
