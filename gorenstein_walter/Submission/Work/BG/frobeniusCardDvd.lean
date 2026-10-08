import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.cardDvdOfFree

/-!
# `Work.BG.frobeniusCardDvd`: `|B| ∣ |F| - 1` for a Frobenius group `F ⋊ B`

Let `BF = F ⋊ B` be a Frobenius group with kernel `F` and complement `B`, in the sense of
`Work.GW2.IsFrobeniusWith`: `F ≤ BF`, `F` normal in `BF`, `B ⊔ F = BF`, `B ⊓ F = ⊥`, and
`F ⊓ C_G(b) = ⊥` for every `1 ≠ b ∈ B`.

Then `B` acts on `F` by conjugation, and every `1 ≠ b ∈ B` has only the identity of `F` as a
fixed point (a fixed point `f` of `b` commutes with `b`, so lies in `F ⊓ C_G(b) = ⊥`).  Hence
all orbits of `B` on `F \ {1}` have cardinality `|B|`, and `|B| ∣ |F| - 1`.

The orbit counting is the existing lemma `Work.BG.cardDvdOfFree`; the content here is to build
the conjugation action of `B` on `F` and to verify its two hypotheses (the global fixed point
`1`, and freeness away from `1`).
-/

namespace Work.BG

set_option linter.style.haveILetI false

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
theorem frobeniusCardDvd {G : Type} [Group G] [Finite G]
    (BF F B : Subgroup G) (h : Work.GW2.IsFrobeniusWith BF F B) :
    Nat.card B ∣ Nat.card F - 1 := by
  classical
  obtain ⟨hFle, hN, hsup, hdisj, hFne, hBne, hfree⟩ := h
  -- `B ≤ BF`, since `B ⊔ F = BF`
  have hBle : B ≤ BF := hsup ▸ le_sup_left
  -- `F` is invariant under conjugation by elements of `B`
  have hconj : ∀ b ∈ B, ∀ f ∈ F, b * f * b⁻¹ ∈ F := fun b hb f hf =>
    (Subgroup.normal_subgroupOf_iff hFle).mp hN f b hf (hBle hb)
  -- the conjugation action of `B` on `F`
  let smulFn : ↥B → ↥F → ↥F := fun b f =>
    ⟨(b : G) * (f : G) * (b : G)⁻¹, hconj b b.2 f f.2⟩
  have hsmul_one : ∀ f : ↥F, smulFn 1 f = f := fun f => Subtype.ext (by simp [smulFn])
  have hsmul_mul : ∀ b c : ↥B, ∀ f : ↥F, smulFn (b * c) f = smulFn b (smulFn c f) := by
    intro b c f
    apply Subtype.ext
    simp only [smulFn, Subgroup.coe_mul]
    group
  letI : MulAction ↥B ↥F := { smul := smulFn, one_smul := hsmul_one, mul_smul := hsmul_mul }
  -- the value of the action on underlying elements of `G`
  have hsmul_val : ∀ (b : ↥B) (f : ↥F), ((b • f : ↥F) : G) = (b : G) * (f : G) * (b : G)⁻¹ :=
    fun _ _ => rfl
  -- `1 ∈ F` is a global fixed point
  have hfix : ∀ b : ↥B, b • (1 : ↥F) = (1 : ↥F) := by
    intro b
    apply Subtype.ext
    rw [hsmul_val]
    simp
  -- the action is free away from `1`
  have hfree' : ∀ b : ↥B, b ≠ 1 → ∀ x : ↥F, x ≠ 1 → b • x ≠ x := by
    intro b hb x hx hcon
    have hbG : (b : G) ≠ 1 := fun hh => hb (Subtype.ext hh)
    have hxG : (x : G) ≠ 1 := fun hh => hx (Subtype.ext hh)
    -- `b` commutes with the fixed point `x`
    have hval : (b : G) * (x : G) * (b : G)⁻¹ = (x : G) := by
      rw [← hsmul_val b x]
      exact congrArg Subtype.val hcon
    have hcomm : (b : G) * (x : G) = (x : G) * (b : G) := by
      calc (b : G) * (x : G)
          = (b : G) * (x : G) * (b : G)⁻¹ * (b : G) := by group
        _ = (x : G) * (b : G) := by rw [hval]
    -- so `x ∈ F ⊓ C_G(b) = ⊥`, i.e. `x = 1`
    have hmem : (x : G) ∈ F ⊓ Subgroup.centralizer ({(b : G)} : Set G) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [hfree (b : G) b.2 hbG, Subgroup.mem_bot] at hmem
    exact hxG hmem
  exact cardDvdOfFree (G := ↥B) (X := ↥F) (1 : ↥F) hfix hfree'

end Work.BG
