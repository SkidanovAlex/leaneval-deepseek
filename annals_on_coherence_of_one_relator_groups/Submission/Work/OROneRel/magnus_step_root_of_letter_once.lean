/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus--Moldavanskii step when the root contains a generator exactly once

If the cyclically reduced word `u` contains a generator `x` exactly once (`count (x, b) = 1` and
`count (x, !b) = 0`), then `u = A * x^ε * B` where `A`, `B` involve only the remaining generators
`Y = α \ {x}`.  In the one-relator group `G = ⟨α | u ^ l⟩` this substitution exhibits `u` as a
*new* generator `t` with `t ^ l = 1`, so that

  `G ≅ F(Y) ∗ ℤ/l`

(the generator `x` being recovered as `x = (A⁻¹ t B⁻¹)^ε`).  This is a free product with a *cyclic*
factor, so it splits off one free generator: choosing `y ∈ Y`, the group `F(Y) ∗ ℤ/l` is obtained
from `F(Y \ {y}) ∗ ℤ/l` by adjoining one free generator.  Presenting the vertex as

  `P = ⟨β | v ^ l⟩`  with `β = Y` and `v = of y`

identifies `P ≅ F(Y \ {y}) ∗ ℤ/l` (the class of `v` being the `ℤ/l`-generator), so that the HNN
extension `HNN(P, ⊥, ⊥, id) = P ∗ ℤ` is again `F(Y) ∗ ℤ/l` and hence isomorphic to `G`; the
generator `u` of `G` corresponds to the class of the vertex relator `v`.

The isomorphism is constructed explicitly as a pair of mutually inverse homomorphisms (checked on
generators), and the class of `u` is `of (mk v)`, i.e. the required conjugacy holds with `c = 1`.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod
import Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported
import Submission.Work.OROneRel.hnn_bot_presentedGroup_single_iso_freeGroup
import Submission.Work.OROneRel.letter_once_iso_freeGroup
import Submission.Work.OROneRel.letterPow
import Submission.Work.OROneRel.not_isProperPower_of
import Submission.Work.OROneRel.FreiheitssatzCases
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.mk_conj_zpow_of_eq
import Submission.Work.OROneRel.exists_letter_once_data

universe u

namespace Work.OROneRel

theorem magnus_step_root_of_letter_once {α : Type u} [DecidableEq α] (u : FreeGroup α) (l : ℕ)
    (hl : 1 ≤ l) (x : α) (b : Bool)
    (hb : (x, b) ∈ FreeGroup.toWord u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hcount : (FreeGroup.toWord u).count (x, b) = 1 ∧
      (FreeGroup.toWord u).count (x, Bool.not b) = 0)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  obtain ⟨L₁, L₂, ε, y, hsplit, hnotin, hxε, hu, heps⟩ := exists_letter_once_data u x b hcount hn
  have hεε : ε * ε = 1 := by rcases heps with h | h <;> rw [h] <;> norm_num
  let Y : Set α := {a : α | a ≠ x}
  -- the two outer words, as elements of `F(Y)`
  have hmem₁ : FreeGroup.mk L₁ ∈ Subgroup.closure (FreeGroup.of '' Y) :=
    mk_mem_closure (fun a c h => hnotin (a, c) (List.mem_append.mpr (Or.inl h)))
  have hmem₂ : FreeGroup.mk L₂ ∈ Subgroup.closure (FreeGroup.of '' Y) :=
    mk_mem_closure (fun a c h => hnotin (a, c) (List.mem_append.mpr (Or.inr h)))
  obtain ⟨u', hu'⟩ : ∃ w' : FreeGroup ↥Y,
      FreeGroup.lift (fun a : ↥Y => FreeGroup.of (a : α)) w' = FreeGroup.mk L₁ :=
    exists_lift_of_supportedOn (Z := Y) ((letters_closure_iff _ Y).mp hmem₁)
  obtain ⟨v', hv'⟩ : ∃ w' : FreeGroup ↥Y,
      FreeGroup.lift (fun a : ↥Y => FreeGroup.of (a : α)) w' = FreeGroup.mk L₂ :=
    exists_lift_of_supportedOn (Z := Y) ((letters_closure_iff _ Y).mp hmem₂)
  -- the vertex relator
  let v : FreeGroup ↥Y := FreeGroup.of y
  have hv_np : ¬ IsProperPower v := not_isProperPower_of y
  have hv_lt : relatorNorm v < relatorNorm u := by
    have h1 : relatorNorm v = 1 := by
      show relatorNorm (FreeGroup.of y) = 1
      simp [relatorNorm, FreeGroup.norm]
    omega
  let P : Type u := PresentedGroup ({v ^ l} : Set (FreeGroup ↥Y))
  let φ : (⊥ : Subgroup P) ≃* (⊥ : Subgroup P) := MulEquiv.refl _
  let H : Type u := HNNExtension P ⊥ ⊥ φ
  let g : P := PresentedGroup.mk ({v ^ l} : Set (FreeGroup ↥Y)) v
  have hg : g = PresentedGroup.of y := rfl
  -- the "coinclusion" of the remaining generators into the vertex group
  let F : FreeGroup ↥Y →* H :=
    FreeGroup.lift (fun a : ↥Y =>
      if a = y then HNNExtension.t else HNNExtension.of (PresentedGroup.of a : P))
  have hF_of (a : ↥Y) : F (FreeGroup.of a) =
      (if a = y then HNNExtension.t else HNNExtension.of (PresentedGroup.of a : P)) :=
    FreeGroup.lift_apply_of
  -- the generator map of `Φ : ⟨α | u^l⟩ →* H`
  let f : α → H := fun a =>
    if ha : a = x then ((F u')⁻¹ * HNNExtension.of g * (F v')⁻¹) ^ ε
    else F (FreeGroup.of ⟨a, ha⟩)
  have hfx : f x = ((F u')⁻¹ * HNNExtension.of g * (F v')⁻¹) ^ ε := dif_pos rfl
  have hfY : ∀ a : ↥Y, f (a : α) = F (FreeGroup.of a) := by
    intro a
    have h : f (a : α) = F (FreeGroup.of ⟨(a : α), a.2⟩) := dif_neg a.2
    rw [h]
  have hcompι : (FreeGroup.lift f).comp (FreeGroup.lift (fun a : ↥Y => FreeGroup.of (a : α))) = F := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show FreeGroup.lift f (FreeGroup.of (a : α)) = F (FreeGroup.of a)
    rw [FreeGroup.lift_apply_of, hfY a]
  have hF1 : FreeGroup.lift f (FreeGroup.mk L₁) = F u' := by
    rw [← hu', ← MonoidHom.comp_apply, hcompι]
  have hF2 : FreeGroup.lift f (FreeGroup.mk L₂) = F v' := by
    rw [← hv', ← MonoidHom.comp_apply, hcompι]
  -- `f` kills the relator
  have hliftu : FreeGroup.lift f u = HNNExtension.of g := by
    have h2 : ∀ r : H, (r ^ ε) ^ ε = r := by
      intro r
      rw [← zpow_mul, hεε, zpow_one]
    rw [hu, map_mul, map_mul, map_zpow]
    rw [FreeGroup.lift_apply_of, hfx, hF1, hF2, h2]
    group
  have hgl : g ^ l = 1 := by
    show (PresentedGroup.mk ({v ^ l} : Set (FreeGroup ↥Y)) v) ^ l = 1
    rw [← map_pow]
    exact PresentedGroup.one_of_mem (Set.mem_singleton _)
  have hrel : ∀ r ∈ ({u ^ l} : Set (FreeGroup α)), FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [map_pow, hliftu, ← map_pow, hgl, map_one]
  -- the forward map
  let Φ : PresentedGroup ({u ^ l} : Set (FreeGroup α)) →* H :=
    PresentedGroup.toGroup (f := f) hrel
  have hΦ_of (a : α) : Φ (PresentedGroup.of a) = f a := PresentedGroup.toGroup.of hrel
  have hΦcomp : Φ.comp (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) = FreeGroup.lift f := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show Φ (PresentedGroup.of a) = FreeGroup.lift f (FreeGroup.of a)
    rw [FreeGroup.lift_apply_of]
    exact hΦ_of a
  have hΦ_mk (w : FreeGroup α) :
      Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) w) = FreeGroup.lift f w := by
    rw [← MonoidHom.comp_apply, hΦcomp]
  have hΦ_mku : Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) = HNNExtension.of g := by
    rw [hΦ_mk, hliftu]
  -- the backward map
  let ψfun : ↥Y → PresentedGroup ({u ^ l} : Set (FreeGroup α)) := fun a =>
    if a = y then PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u
    else PresentedGroup.of (a : α)
  have hψrel : ∀ r ∈ ({v ^ l} : Set (FreeGroup ↥Y)), FreeGroup.lift ψfun r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [map_pow, FreeGroup.lift_apply_of]
    have hy' : ψfun y = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u := dif_pos rfl
    rw [hy', ← map_pow]
    exact PresentedGroup.one_of_mem (Set.mem_singleton _)
  let ψP : P →* PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
    PresentedGroup.toGroup (f := ψfun) hψrel
  have hψP_of (a : ↥Y) : ψP (PresentedGroup.of a) = ψfun a := PresentedGroup.toGroup.of hψrel
  have hψP_y : ψP (PresentedGroup.of y) = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u := by
    rw [hψP_of y]
    exact dif_pos rfl
  have hψP_g : ψP g = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u := by
    rw [hg, hψP_y]
  let Ψ : H →* PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
    HNNExtension.lift ψP (PresentedGroup.of (y : α)) (by
      intro a
      have ha : ((a : P)) = 1 := Subgroup.mem_bot.mp a.2
      have hb2 : (((φ a : (⊥ : Subgroup P)) : P)) = 1 := Subgroup.mem_bot.mp (φ a).2
      rw [ha, hb2, map_one, mul_one, one_mul])
  have hΨ_of (p : P) : Ψ (HNNExtension.of p) = ψP p := HNNExtension.lift_of _ _ _ p
  have hΨ_t : Ψ HNNExtension.t = PresentedGroup.of (y : α) := HNNExtension.lift_t _ _ _
  -- `Ψ ∘ F` is the inclusion of `F(Y)` into `⟨α | u^l⟩`
  have hΨF : Ψ.comp F = (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))).comp
      (FreeGroup.lift (fun a : ↥Y => FreeGroup.of (a : α))) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show Ψ (F (FreeGroup.of a)) = PresentedGroup.mk _ (FreeGroup.lift _ (FreeGroup.of a))
    rw [hF_of a, FreeGroup.lift_apply_of]
    by_cases ha : a = y
    · rw [if_pos ha, hΨ_t, ha]
      rfl
    · rw [if_neg ha, hΨ_of, hψP_of]
      exact dif_neg ha
  have hΨF_apply (w : FreeGroup ↥Y) : Ψ (F w) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
        (FreeGroup.lift (fun a : ↥Y => FreeGroup.of (a : α)) w) := by
    rw [← MonoidHom.comp_apply, hΨF, MonoidHom.comp_apply]
  -- `Ψ ∘ Φ = id`
  have hΨΦ : Ψ.comp Φ = MonoidHom.id (PresentedGroup ({u ^ l} : Set (FreeGroup α))) := by
    refine PresentedGroup.ext fun a => ?_
    show Ψ (Φ (PresentedGroup.of a)) = PresentedGroup.of a
    rw [hΦ_of]
    by_cases ha : a = x
    · subst ha
      rw [hfx, map_zpow]
      have h1 : Ψ ((F u')⁻¹ * HNNExtension.of g * (F v')⁻¹) =
          (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.mk L₁))⁻¹
            * PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u
            * (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (FreeGroup.mk L₂))⁻¹ := by
        rw [map_mul, map_mul, map_inv, map_inv, hΨ_of, hΨF_apply, hΨF_apply, hu', hv', hψP_g]
      rw [h1]
      exact mk_conj_zpow_of_eq _ hu hεε
    · rw [show f a = F (FreeGroup.of ⟨a, ha⟩) from dif_neg ha, hΨF_apply,
        FreeGroup.lift_apply_of]
      rfl
  -- `Φ ∘ Ψ = id`
  have hΦΨ : Φ.comp Ψ = MonoidHom.id H := by
    refine HNNExtension.hom_ext ?_ ?_
    · rw [MonoidHom.comp_assoc, MonoidHom.id_comp]
      refine PresentedGroup.ext fun a => ?_
      show Φ (Ψ (HNNExtension.of (PresentedGroup.of a))) = HNNExtension.of (PresentedGroup.of a)
      rw [hΨ_of, hψP_of]
      show Φ (if a = y then PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u
        else PresentedGroup.of (a : α)) = HNNExtension.of (PresentedGroup.of a)
      by_cases ha : a = y
      · rw [if_pos ha, hΦ_mku, ha, hg]
      · rw [if_neg ha, hΦ_of, hfY a, hF_of, if_neg ha]
    · rw [MonoidHom.comp_apply, MonoidHom.id_apply, hΨ_t, hΦ_of, hfY y, hF_of, if_pos rfl]
  have he_mk : (MonoidHom.toMulEquiv Φ Ψ hΨΦ hΦΨ)
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
        HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup ↥Y)) v) := by
    show Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) = HNNExtension.of g
    exact hΦ_mku
  refine ⟨↥Y, v, hv_np, hv_lt, ⊥, ⊥, MulEquiv.refl _, MonoidHom.toMulEquiv Φ Ψ hΨΦ hΦΨ, 1, ?_⟩
  rw [he_mk]
  group

end Work.OROneRel
