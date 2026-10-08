import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.twoPoint_conj_inf_eq_bot`

In a Zassenhaus group: distinct two-point stabilisers meet trivially.  Concretely, for the
split rank-one datum `(H, Q, t)` with `H` Zassenhaus (the pointwise stabiliser of three
distinct points of `Ω = G ⧸ H` is trivial), the two-point stabiliser `D = twoPoint H t` and
its conjugate `D^g` are either equal or meet in `⊥`.

The proof is the geometric argument on `Ω = G ⧸ H`, no character theory:

* `D` is the pointwise stabiliser of the two distinct points `∞ = H` and `t • ∞` (this uses
  `t ∉ H`), and `D^g = g D g⁻¹` is the pointwise stabiliser of `g • ∞` and `g • (t • ∞)`.
* If `1 ≠ x ∈ D ⊓ D^g`, then `x` fixes the four points `∞, t • ∞, g • ∞, g • (t • ∞)`.
  Because `x ≠ 1` fixes at most two points (`IsZassenhaus`), the two pairs must coincide, so
  `g` permutes `{∞, t • ∞}`; hence it conjugates `D` to itself, contradicting the hypothesis.
-/

set_option autoImplicit false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G]

/-! ## The geometry of `Ω = G ⧸ H` -/

/-- `x` fixes the base point `∞ = H` of `Ω = G ⧸ H` iff `x ∈ H`. -/
lemma mem_H_iff_smul_pt {H : Subgroup G} {x : G} :
    x ∈ H ↔ x • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H := by
  rw [Work.DoubleTransitivity.smul_pt, Work.DoubleTransitivity.mk_one_eq_iff]

/-- `x ∈ H^a = conj a H` iff `x` fixes the point `a • ∞`. -/
lemma mem_conj_iff_smul_pt {H : Subgroup G} {a x : G} :
    x ∈ conj a H ↔
      x • (a • Work.DoubleTransitivity.pt H) = a • Work.DoubleTransitivity.pt H := by
  rw [Work.DoubleTransitivity.mem_conj_iff_smul_fixed, Work.DoubleTransitivity.smul_pt]

/-- A conjugate of `H` depends only on the point it stabilises. -/
lemma conj_eq_of_smul_pt_eq {H : Subgroup G} {a b : G}
    (h : a • Work.DoubleTransitivity.pt H = b • Work.DoubleTransitivity.pt H) :
    conj a H = conj b H := by
  ext z
  rw [mem_conj_iff_smul_pt, mem_conj_iff_smul_pt, h]

/-- `(H^t)^g = H^{gt}`. -/
theorem conj_conj_eq (H : Subgroup G) (g t : G) :
    conj g (conj t H) = conj (g * t) H := by
  ext x
  rw [Work.DoubleTransitivity.mem_conj, Work.DoubleTransitivity.mem_conj,
    Work.DoubleTransitivity.mem_conj]
  rw [show t⁻¹ * (g⁻¹ * x * g) * t = (g * t)⁻¹ * x * (g * t) from by group]

/-- Conjugation distributes over the defining intersection of the two-point stabiliser. -/
theorem conj_twoPoint_eq (H : Subgroup G) (g t : G) :
    conj g (twoPoint H t) = conj g H ⊓ conj g (conj t H) := by
  show (H ⊓ conj t H).map (MulAut.conj g).toMonoidHom = conj g H ⊓ conj g (conj t H)
  exact Subgroup.map_inf H (conj t H) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

/-- Membership in the two-point stabiliser, read off the action on `Ω = G ⧸ H`. -/
lemma mem_twoPoint_iff_smul {H : Subgroup G} {t x : G} :
    x ∈ twoPoint H t ↔
      x • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H ∧
      x • (t • Work.DoubleTransitivity.pt H) = t • Work.DoubleTransitivity.pt H := by
  rw [twoPoint, Subgroup.mem_inf, mem_H_iff_smul_pt, mem_conj_iff_smul_pt]

/-- Conjugation by an element of `H` fixes `H`. -/
lemma conj_eq_self_of_mem_H {H : Subgroup G} {x : G} (hx : x ∈ H) : conj x H = H :=
  (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer x H).mpr (Subgroup.le_normalizer hx)

/-! ## The key step -/

/-- If a non-identity element lies in `D ⊓ D^g`, then `D^g = D`.  Equivalently: a nontrivial
element of `D` has fixed point set exactly `{∞, t • ∞}`, so it can only lie in the two-point
stabilisers of the pair `{∞, t • ∞}` and its reverse — that is, in `D` and its conjugates
which permute the pair. -/
theorem conj_eq_self_of_mem_inf {H Q : Subgroup G} {t g x : G}
    (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (hx1 : x ≠ 1)
    (hxD : x ∈ twoPoint H t) (hxgD : x ∈ conj g (twoPoint H t)) :
    conj g (twoPoint H t) = twoPoint H t := by
  have hxtp := mem_twoPoint_iff_smul.mp hxD
  have hx_pt : x • Work.DoubleTransitivity.pt H = Work.DoubleTransitivity.pt H := hxtp.1
  have hx_tpt : x • (t • Work.DoubleTransitivity.pt H) = t • Work.DoubleTransitivity.pt H :=
    hxtp.2
  rw [conj_twoPoint_eq] at hxgD
  obtain ⟨hxgH, hxgtH⟩ := Subgroup.mem_inf.mp hxgD
  have hx_gpt : x • (g • Work.DoubleTransitivity.pt H) = g • Work.DoubleTransitivity.pt H :=
    mem_conj_iff_smul_pt.mp hxgH
  have hx_gtpt : x • (g • (t • Work.DoubleTransitivity.pt H))
      = g • (t • Work.DoubleTransitivity.pt H) := by
    rw [conj_conj_eq] at hxgtH
    have h' := mem_conj_iff_smul_pt.mp hxgtH
    rwa [mul_smul] at h'
  -- `∞ ≠ t • ∞` because `t ∉ H`
  have hab : Work.DoubleTransitivity.pt H ≠ t • Work.DoubleTransitivity.pt H := by
    intro hcon
    exact h.not_mem (mem_H_iff_smul_pt.mpr hcon.symm)
  -- a non-identity element fixes at most the two points `∞` and `t • ∞`
  have hfix : ∀ ω : G ⧸ H, x • ω = ω →
      ω = Work.DoubleTransitivity.pt H ∨ ω = t • Work.DoubleTransitivity.pt H := by
    intro ω hω
    by_contra hcon
    rw [not_or] at hcon
    exact hx1 (hZ (Work.DoubleTransitivity.pt H) (t • Work.DoubleTransitivity.pt H) ω
      hab (Ne.symm hcon.1) (Ne.symm hcon.2) x hx_pt hx_tpt hω)
  have hgpt := hfix _ hx_gpt
  have hgtpt := hfix _ hx_gtpt
  have hne : g • Work.DoubleTransitivity.pt H ≠ g • (t • Work.DoubleTransitivity.pt H) := by
    intro hcon
    have h2 : Work.DoubleTransitivity.pt H = t • Work.DoubleTransitivity.pt H := by
      have h3 := congrArg (fun ω : G ⧸ H => g⁻¹ • ω) hcon
      simpa only [inv_smul_smul] using h3
    exact hab h2
  rcases hgpt with h1 | h1 <;> rcases hgtpt with h2 | h2
  · -- `g • ∞ = ∞` and `g • (t • ∞) = ∞`, impossible
    exact absurd (h1.trans h2.symm) hne
  · -- `g` fixes both points: `D^g = D`
    have hcH : conj g H = H :=
      conj_eq_self_of_mem_H ((mem_H_iff_smul_pt (H := H) (x := g)).mpr h1)
    have hctH : conj g (conj t H) = conj t H := by
      rw [conj_conj_eq]
      exact conj_eq_of_smul_pt_eq (by rw [mul_smul]; exact h2)
    rw [conj_twoPoint_eq, hcH, hctH]
  · -- `g` swaps the two points: `D^g = D` as well
    have hcH : conj g H = conj t H := conj_eq_of_smul_pt_eq h1
    have hctH : conj g (conj t H) = H := by
      rw [conj_conj_eq]
      have haux : conj (g * t) H = conj (1 : G) H :=
        conj_eq_of_smul_pt_eq (by rw [mul_smul, h2, one_smul])
      rw [haux, conj_eq_self_of_mem_H (H := H) (x := 1) H.one_mem]
    rw [conj_twoPoint_eq, hcH, hctH]
    exact inf_comm _ _
  · -- `g • ∞ = t • ∞` and `g • (t • ∞) = t • ∞`, impossible
    exact absurd (h1.trans h2.symm) hne

/-! ## The theorem -/

theorem twoPoint_conj_inf_eq_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t g : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hg : Submission.Blueprint.conj g (Submission.Blueprint.twoPoint H t) ≠
      Submission.Blueprint.twoPoint H t) :
    Submission.Blueprint.twoPoint H t ⊓
      Submission.Blueprint.conj g (Submission.Blueprint.twoPoint H t) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxD, hxgD⟩ := Subgroup.mem_inf.mp hx
  exact hg (conj_eq_self_of_mem_inf h hZ hx1 hxD hxgD)

end Work.ZassenhausSuzuki
