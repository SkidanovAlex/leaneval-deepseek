import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.Frobenius.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.twoPoint_ne_bot`

In a finite simple group with a split BN-pair of rank one (`IsSplitRankOne H Q t`) the two-point
stabiliser `D = twoPoint H t = H ∩ Hᵗ` is nontrivial.  (The Zassenhaus hypothesis `IsZassenhaus H`
is not needed; the lemma is a special case of "a finite simple group has no Frobenius
complement".)

The argument is elementary, and does not use anything about `Q`:

* if `twoPoint H t = ⊥`, then by 2-transitivity of `G` on `Ω = G ⧸ H` (equivalently, by
  transitivity of `H` on `Ω ∖ {∞}`) *every* two point stabiliser is trivial: for `g ∉ H` choose
  `a ∈ H` with `a • (g • ∞) = t • ∞`; then `Stab_H(g • ∞) = a⁻¹ Stab_H(t • ∞) a = 1`.  Hence
  `H ⊓ g H g⁻¹ = ⊥` for every `g ∉ H`, and with `H ≠ ⊥` (strong embedding makes `|H|` even) and
  `H ≠ ⊤` this says that **`H` is a Frobenius complement**;
* Frobenius' theorem (`Work.Frobenius.frobenius_theorem`, proved from character theory in area
  A8) then produces a normal subgroup `K ⊴ G` with `K ⊓ H = ⊥`: `K ≠ ⊥` (its order is `[G : H]`
  and `H ≠ ⊤`) and `K ≠ ⊤` (since `H ≠ ⊥`), contradicting the simplicity of `G`.

Equivalently: a finite simple group cannot act sharply 2-transitively on more than two points.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `MulAut.conj g • H` (the conjugation action of `Work.Frobenius`) is the blueprint's
`conj g H = g H g⁻¹`. -/
lemma mulAut_conj_smul_eq_conj (H : Subgroup G) (g : G) :
    MulAut.conj g • H = Submission.Blueprint.conj g H := by
  ext x
  rw [Work.Frobenius.mem_conj_smul_iff, IsTIQ.mem_conj_iff_inv]

/-- If the two-point stabiliser `D = H ∩ Hᵗ` is trivial then `H` is a Frobenius complement: in a
2-transitive action every two-point stabiliser is conjugate to `D`, hence trivial. -/
lemma isFrobeniusComplement_of_twoPoint_eq_bot (h : IsSplitRankOne H Q t)
    (hbot : twoPoint H t = ⊥) : Work.Frobenius.IsFrobeniusComplement H := by
  refine ⟨?_, h.stronglyEmbedded.1, ?_⟩
  · -- `H ≠ ⊥` because `|H|` is even
    intro hHb
    have hev := h.stronglyEmbedded.2.1
    rw [hHb] at hev
    rw [Subgroup.card_bot] at hev
    exact absurd hev (by decide)
  · -- `H ⊓ g H g⁻¹ = ⊥` for `g ∉ H`
    intro g hg
    rw [mulAut_conj_smul_eq_conj]
    rw [Subgroup.eq_bot_iff_forall]
    intro d hd
    rw [Subgroup.mem_inf] at hd
    obtain ⟨hdH, hdC⟩ := hd
    -- `d ∈ H ∩ gHg⁻¹` fixes the point `g • ∞`
    have hdfix : d • (g : G ⧸ H) = (g : G ⧸ H) :=
      ((IsTIQ.mem_twoPoint_iff_smul H g d).mp ⟨hdH, hdC⟩).2
    -- move that point to `t • ∞` by an element `a` of `H`
    have hgpt : (g : G ⧸ H) ≠ IsTIQ.basePt H := (IsTIQ.basePt_ne_iff H g).mpr hg
    have htpt : (t : G ⧸ H) ≠ IsTIQ.basePt H := (IsTIQ.basePt_ne_iff H t).mpr h.not_mem
    obtain ⟨a, haH, ha⟩ := IsTIQ.h_transitive h (g : G ⧸ H) (t : G ⧸ H) hgpt htpt
    -- so `a d a⁻¹ ∈ twoPoint H t = ⊥`
    have hmem : a * d * a⁻¹ ∈ twoPoint H t := by
      rw [IsTIQ.mem_twoPoint_iff_smul H t]
      refine ⟨H.mul_mem (H.mul_mem haH hdH) (H.inv_mem haH), ?_⟩
      calc (a * d * a⁻¹) • (t : G ⧸ H)
          = (a * d * a⁻¹) • (a • (g : G ⧸ H)) := by rw [ha]
        _ = (a * d) • (g : G ⧸ H) := by
              rw [← mul_smul, show (a * d * a⁻¹) * a = a * d by group]
        _ = a • (d • (g : G ⧸ H)) := by rw [mul_smul]
        _ = a • (g : G ⧸ H) := by rw [hdfix]
        _ = (t : G ⧸ H) := ha
    have hone : a * d * a⁻¹ = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem)
    calc d = a⁻¹ * (a * d * a⁻¹) * a := by group
      _ = 1 := by rw [hone]; group

/-- A finite simple group has no Frobenius complement: Frobenius' theorem exhibits the kernel as a
normal subgroup that is neither trivial nor the whole group. -/
theorem no_isFrobeniusComplement_of_isSimpleGroup {G : Type} [Group G] [Finite G]
    {H : Subgroup G} [IsSimpleGroup G] : ¬ Work.Frobenius.IsFrobeniusComplement H := by
  intro hcomp
  obtain ⟨K, hK, hKn, _⟩ := Work.Frobenius.frobenius_theorem hcomp
  have hKne : K ≠ ⊥ := Work.Frobenius.kernel_ne_bot hcomp hK
  have hKtop : K ≠ ⊤ := by
    intro htop
    have hinf := Work.Frobenius.frobenius_inf_eq_bot hcomp hK
    exact hcomp.ne_bot (by rw [← hinf, htop, top_inf_eq])
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ _ K hKn with h1 | h1
  · exact hKne h1
  · exact hKtop h1

theorem twoPoint_ne_bot {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    [IsSimpleGroup G] (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) : Submission.Blueprint.twoPoint H t ≠ ⊥ := by
  intro hbot
  exact no_isFrobeniusComplement_of_isSimpleGroup
    (isFrobeniusComplement_of_twoPoint_eq_bot h hbot)

end Work.ZassenhausTwoGroup
