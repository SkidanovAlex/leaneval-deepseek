/-
# `Work.PSU3.StageB.ThetaOmegaAux` — the conjugation (H3) form of the canonical maps

The canonical maps `f, g, h : Q# → Q#` of Peterfalvi II Ch. VII §1 satisfy

* **H3.** `f(x^a) = f(x)^{a^t}`, `g(x^a) = g(x)^{a^t}` and `h(x^a) = a^{-t} h(x) a` for `a ∈ D`,

where `x^a = a⁻¹ x a`.  The raw form `Work.PSU3.StageB.canon_conj_fun` states these for an
existentially quantified conjugate `xa`; here we package them for the *concrete* conjugate
`qconj a x = a⁻¹ x a`, which is what the iterated computation of `(f ∘ j)³` in
`ThetaOmega.lean` needs.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Theta

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

/-- The conjugate `a⁻¹ x a` of `x ∈ Q` by `a ∈ D = H ∩ H^t`, as an element of `Q`
(`Q ⊴ H`). -/
noncomputable def qconj (h : IsSplitRankOne H Q t) (a : ↥(twoPoint H t)) (x : ↥Q) : ↥Q :=
  ⟨(a : G)⁻¹ * (x : G) * (a : G), by
    have hc := conj_mem_of_mem h (H.inv_mem (twoPoint_le_left H t a.2)) x.2
    simpa using hc⟩

@[simp] lemma qconj_coe (h : IsSplitRankOne H Q t) (a : ↥(twoPoint H t)) (x : ↥Q) :
    (qconj h a x : G) = (a : G)⁻¹ * (x : G) * (a : G) := rfl

/-- **H3, `f`-component**, concrete form. -/
lemma fcan_qconj (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1)
    (a : ↥(twoPoint H t)) :
    (fcan h (qconj h a x) : G) =
      (t * (a : G) * t)⁻¹ * (fcan h x : G) * (t * (a : G) * t) := by
  obtain ⟨xa, hxa, hf, _, _⟩ := canon_conj_fun h hx a
  have hsub : xa = qconj h a x := Subtype.ext (by rw [hxa]; rfl)
  rwa [hsub] at hf

/-- **H3, `g`-component**, concrete form. -/
lemma gcan_qconj (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1)
    (a : ↥(twoPoint H t)) :
    (gcan h (qconj h a x) : G) =
      (t * (a : G) * t)⁻¹ * (gcan h x : G) * (t * (a : G) * t) := by
  obtain ⟨xa, hxa, _, hg, _⟩ := canon_conj_fun h hx a
  have hsub : xa = qconj h a x := Subtype.ext (by rw [hxa]; rfl)
  rwa [hsub] at hg

/-- **H3, `h`-component** (H4a), concrete form. -/
lemma hcan_qconj (h : IsSplitRankOne H Q t) {x : ↥Q} (hx : (x : G) ≠ 1)
    (a : ↥(twoPoint H t)) :
    (hcan h (qconj h a x) : G) =
      (t * (a : G) * t)⁻¹ * (hcan h x : G) * (a : G) := by
  obtain ⟨xa, hxa, _, _, hh⟩ := canon_conj_fun h hx a
  have hsub : xa = qconj h a x := Subtype.ext (by rw [hxa]; rfl)
  rwa [hsub] at hh

/-! ## The element `ζ` of the frame -/

lemma zeta_mem_D (fr : CoarseFrame H Q t n) : (fr.ζ : G) ∈ twoPoint H t :=
  (Subgroup.mem_inf.mp (W_le_centD H t fr.ζ_mem_W)).1

lemma zeta_mem_centD (fr : CoarseFrame H Q t n) : (fr.ζ : G) ∈ centD H t :=
  W_le_centD H t fr.ζ_mem_W

/-- `ζ ∈ W ≤ C_D(t)`, so conjugation by the involution `t` fixes `ζ`. -/
lemma t_zeta_t (h : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) :
    t * (fr.ζ : G) * t = (fr.ζ : G) := by
  have hcomm : (fr.ζ : G) * t = t * (fr.ζ : G) :=
    ((Subgroup.mem_inf.mp (zeta_mem_centD fr)).2 t (Set.mem_singleton t)).symm
  calc t * (fr.ζ : G) * t = t * ((fr.ζ : G) * t) := by rw [mul_assoc]
    _ = t * (t * (fr.ζ : G)) := by rw [hcomm]
    _ = (t * t) * (fr.ζ : G) := by rw [mul_assoc]
    _ = (fr.ζ : G) := by rw [mul_self_eq_one h, one_mul]

lemma t_zeta_inv_t (h : IsSplitRankOne H Q t) (fr : CoarseFrame H Q t n) :
    t * (fr.ζ : G)⁻¹ * t = (fr.ζ : G)⁻¹ := by
  rw [← Work.PSU3.RankOne.tdt_inv_eq (mul_self_eq_one h), t_zeta_t h fr]

/-- `w ∈ W#` fixing a point of `Q ∖ Q₀` by conjugation is trivial. -/
lemma eq_one_of_mem_W_of_mul_inv (fr : CoarseFrame H Q t n) {w x : G}
    (hw : w ∈ W H t) (hx : x ∈ Q) (hx0 : x ∉ fr.Q0) (h : w * x * w⁻¹ = x) : w = 1 := by
  by_contra hne
  have h2 : w * x = x * w := by
    have h3 := congrArg (fun z => z * w) h
    simpa [mul_assoc] using h3
  exact hx0 (fr.W_semireg w hw hne x hx h2)

end Work.PSU3.StageB
