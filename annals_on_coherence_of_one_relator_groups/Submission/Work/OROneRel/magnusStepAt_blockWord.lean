/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2) of the
formalisation of Jaikin-Zapirain--Linton, "On the coherence of one-relator groups
and their group algebras".

# The Magnus step for the two-letter block word `a ^ p * b ^ q`

The target of this file is `Work.OROneRel.magnusStepAt_blockWord`: for distinct letters `a ≠ b` of
an arbitrary generating type `α`, for `p, q ≥ 1` coprime and `l ≥ 1`, the one-relator group
`⟨α | (a ^ p * b ^ q) ^ l⟩` is an HNN extension of a one-relator group `⟨β | v ^ l⟩` with `v` not a
proper power, `relatorNorm v < relatorNorm (a ^ p * b ^ q)`, and the class of `a ^ p * b ^ q`
conjugate to the class of `v` in the base.

## The two steps of the proof

1. **The two-element case at the ambient universe.**  `twoElementMagnusStep` produces the datum for
   the generating type `ULift.{u} (Fin 2)` -- the two-element type in the ambient universe `u`.  The
   input is `Work.OROneRel.twoLetter_magnusData`, the Magnus step for the block word over
   `Fin 2` (which lives in `Type 0`), proved from the colleague's `twoLetter_hnnData`.  It is
   transported from `β₀ : Type` to `β := ULift.{u} β₀` along the isomorphism of free groups
   `FreeGroup.freeGroupCongr Equiv.ulift`, using the cross-universe presentation isomorphism
   `presentedGroup_pow_mulEquiv_gen` and `hnnExtension_iso_of_baseMulEquiv` for the HNN side.

2. **The free-factor step.**  `hasMagnusStepAt_map_of_injective` transports the two-element datum
   along the injective relabelling `f : ULift.{u} (Fin 2) → α` sending the two generators of the
   two-element type to `a` and `b`; the target presentation `⟨α | (a ^ p * b ^ q) ^ l⟩` is the
   coproduct of `⟨x, y | (x ^ p * y ^ q) ^ l⟩` with the free group on `α ∖ {a, b}`, and an HNN
   extension splits over such a free factor.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.twoLetter_hnnData
import Submission.Work.OROneRel.twoLetter_amalgam_tietze
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv
import Submission.Work.OROneRel.hasMagnusStepAt_map_of_injective
import Submission.Work.OROneRel.presentedGroup_pow_mulEquiv_gen
import Submission.Work.OROneRel.isProperPower_map_of_injective
import Submission.Work.OROneRel.twoLetter_magnusData

namespace Work.OROneRel

universe u v

/-- The two-letter word `x ^ p * y ^ q` on the generators `ULift.{u} (Fin 2)`. -/
def twowordULift (p q : ℕ) : FreeGroup (ULift.{u} (Fin 2)) :=
  FreeGroup.of (ULift.up (0 : Fin 2)) ^ p * FreeGroup.of (ULift.up (1 : Fin 2)) ^ q

/-- The equation-free form of `presentedGroup_pow_mulEquiv_gen`: given `ψ x = y`, the induced
isomorphism of one-relator presentations may be stated directly with `x` and `y` on the two sides,
so that no dependent rewriting is needed at the point of use. -/
theorem presentedGroup_pow_mulEquiv_gen' {σ : Type u} {τ : Type v}
    (ψ : FreeGroup σ ≃* FreeGroup τ) (x : FreeGroup σ) (y : FreeGroup τ) (hy : ψ x = y) (l : ℕ) :
    ∃ e : PresentedGroup ({x ^ l} : Set (FreeGroup σ)) ≃*
        PresentedGroup ({y ^ l} : Set (FreeGroup τ)),
      e (PresentedGroup.mk ({x ^ l} : Set (FreeGroup σ)) x) =
        PresentedGroup.mk ({y ^ l} : Set (FreeGroup τ)) y := by
  subst hy
  exact presentedGroup_pow_mulEquiv_gen ψ x l

/-- **The two-element Magnus step at universe `u`.**  The Magnus step for the block word
`x ^ p * y ^ q` on the two-element generating type `ULift.{u} (Fin 2)`, with base group
`⟨β | v ^ l⟩` for a `β` in the ambient universe `u`. -/
theorem twoElementMagnusStep (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧
      relatorNorm v < relatorNorm (twowordULift p q : FreeGroup (ULift.{u} (Fin 2))) ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({(twowordULift p q) ^ l} : Set (FreeGroup (ULift.{u} (Fin 2)))) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({(twowordULift p q) ^ l} : Set (FreeGroup (ULift.{u} (Fin 2))))
              (twowordULift p q)) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  -- ### the two-letter datum over `Fin 2` (universe `0`)
  obtain ⟨β₀, v₀, hpp₀, hnorm₀, A₀, B₀, φ₀, e₀, c₀, hc₀⟩ :=
    twoLetter_magnusData p q l hp hq hl hcop
  -- ### the lifted root `v := ULift.up v₀` and the base isomorphism `⟨β | v ^ l⟩ ≃* ⟨β₀ | v₀ ^ l⟩`
  let ρβ : FreeGroup (ULift.{u} β₀) ≃* FreeGroup β₀ := FreeGroup.freeGroupCongr Equiv.ulift
  let v : FreeGroup (ULift.{u} β₀) := ρβ.symm v₀
  have hρβ : ρβ v = v₀ := ρβ.apply_symm_apply v₀
  have hv_eq : v = FreeGroup.map (ULift.up : β₀ → ULift.{u} β₀) v₀ := by
    show ρβ.symm v₀ = FreeGroup.map (ULift.up : β₀ → ULift.{u} β₀) v₀
    rw [show ρβ = FreeGroup.freeGroupCongr Equiv.ulift from rfl, FreeGroup.freeGroupCongr_symm,
      FreeGroup.freeGroupCongr_apply]
    rfl
  obtain ⟨ιβ, hιβ⟩ := presentedGroup_pow_mulEquiv_gen' ρβ v v₀ hρβ l
  -- ### the induced HNN isomorphism, with its value on the stable letter
  obtain ⟨A₁, B₁, φ₁, E, -, -, hE_of, -⟩ :=
    hnnExtension_iso_of_baseMulEquiv ιβ.symm A₀ B₀ φ₀
  have hιβ_symm : ιβ.symm (PresentedGroup.mk ({v₀ ^ l} : Set (FreeGroup β₀)) v₀) =
      PresentedGroup.mk ({v ^ l} : Set (FreeGroup (ULift.{u} β₀))) v := by
    rw [← hιβ, MulEquiv.symm_apply_apply]
  -- ### the block word over the two-element type `ULift.{u} (Fin 2)`
  let ρσ : FreeGroup (ULift.{u} (Fin 2)) ≃* FreeGroup (Fin 2) := FreeGroup.freeGroupCongr Equiv.ulift
  have hρσ : ρσ (twowordULift p q) = FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q := by
    simp only [ρσ, twowordULift, FreeGroup.freeGroupCongr_apply, Equiv.ulift_apply, map_mul, map_pow,
      FreeGroup.map.of]
  obtain ⟨ισ, hισ⟩ := presentedGroup_pow_mulEquiv_gen' ρσ (twowordULift p q)
    (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) hρσ l
  refine ⟨ULift.{u} β₀, v, ?_, ?_, A₁, B₁, φ₁, ισ.trans (e₀.trans E), E c₀, ?_⟩
  · -- the lifted root is not a proper power
    intro hp
    rw [hv_eq] at hp
    exact hpp₀ ((isProperPower_map_of_injective (f := (ULift.up : β₀ → ULift.{u} β₀))
      ULift.up_injective v₀).mp hp)
  · -- the norm bound
    have hv : relatorNorm v = relatorNorm v₀ := by
      rw [hv_eq, relatorNorm_map_of_injective (f := (ULift.up : β₀ → ULift.{u} β₀))
        ULift.up_injective v₀]
    have hu : relatorNorm (twowordULift p q : FreeGroup (ULift.{u} (Fin 2))) =
        relatorNorm (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) := by
      have h := relatorNorm_map_of_injective (f := (ULift.down : ULift.{u} (Fin 2) → Fin 2))
        ULift.down_injective (twowordULift p q)
      have hmap : (FreeGroup.map (ULift.down : ULift.{u} (Fin 2) → Fin 2)) (twowordULift p q)
          = FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q := by
        simpa only [ρσ, FreeGroup.freeGroupCongr_apply, Equiv.ulift_apply] using hρσ
      rw [hmap] at h
      exact h.symm
    rw [hv, hu]
    exact hnorm₀
  · -- the class of the block word is conjugate to the class of the lifted root
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hισ, hc₀, map_mul, map_mul, map_inv, hE_of,
      hιβ_symm]

theorem magnusStepAt_blockWord {α : Type u} (a b : α) (hab : a ≠ b) (p q l : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l) (hcop : Nat.Coprime p q) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v <
        Work.OROneRel.relatorNorm (FreeGroup.of a ^ p * FreeGroup.of b ^ q) ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup
            ({(FreeGroup.of a ^ p * FreeGroup.of b ^ q) ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({(FreeGroup.of a ^ p * FreeGroup.of b ^ q) ^ l} : Set (FreeGroup α))
              (FreeGroup.of a ^ p * FreeGroup.of b ^ q)) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  have hσ := twoElementMagnusStep.{u} p q l hp hq hl hcop
  -- ### the injective relabelling `x ↦ a`, `y ↦ b`
  let f : ULift.{u} (Fin 2) → α := fun x => if x.down = 0 then a else b
  have hf0 : f (ULift.up (0 : Fin 2)) = a := by simp [f]
  have hf1 : f (ULift.up (1 : Fin 2)) = b := by simp [f]
  have hfinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨i⟩ := x
    obtain ⟨j⟩ := y
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hmapf : FreeGroup.map f (twowordULift p q) = FreeGroup.of a ^ p * FreeGroup.of b ^ q := by
    simp only [twowordULift, map_mul, map_pow, FreeGroup.map.of, hf0, hf1]
  -- ### the free-factor transport
  obtain ⟨β, v, hpp, hlt, A, B, φ, e, c, hc⟩ :=
    hasMagnusStepAt_map_of_injective f hfinj (twowordULift p q) l hl hσ
  refine ⟨β, v, hpp, ?_, ?_⟩
  · rw [hmapf] at hlt
    exact hlt
  · rw [← hmapf]
    exact ⟨A, B, φ, e, c, hc⟩

end Work.OROneRel
