import Mathlib
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.szTilde_conj
import Submission.Work.ZassenhausSuzuki.szTildeConjZc
import Submission.Work.ZassenhausSuzuki.szTildeNotSelf
import Submission.Work.ZassenhausSuzuki.szTildeMainStep
import Submission.Work.ZassenhausSuzuki.pow_four_of_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem szTilde_sq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {a : Q} (ha : (e a).a = 0) (ha1 : e a ≠ 1) :
    Work.ZassenhausSuzuki.szTilde hsplit a * Work.ZassenhausSuzuki.szTilde hsplit a = a := by
  classical
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  have ha_ne : (a : G) ≠ 1 := by
    intro h
    exact ha1 (by rw [← map_one e]; exact congrArg (fun z : Q => e z) (Subtype.ext h))
  have ha2 : a * a = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    rw [show e a = (⟨0, (e a).b⟩ : SzA (GaloisField 2 m) θ) from SzA.ext ha rfl]
    ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]
  have hacen : a ∈ Subgroup.center Q := by
    rw [mem_center_iff_map e]
    rw [show e a = (⟨0, (e a).b⟩ : SzA (GaloisField 2 m) θ) from SzA.ext ha rfl]
    exact SzA.mk_zero_mem_center θ _
  have h4 : ∀ x : Q, x ^ 4 = 1 := pow_four_of_mulEquiv θ e
  have hne : tildeOf (szCanon hsplit) a ≠ a := by
    intro hself
    have hall : ∀ c : Q, (e c).a = 0 → e c ≠ 1 → szTilde hsplit c = c := by
      intro c hc hc1
      have hccen : c ∈ Subgroup.center Q := by
        rw [mem_center_iff_map e]
        rw [show e c = (⟨0, (e c).b⟩ : SzA (GaloisField 2 m) θ) from SzA.ext hc rfl]
        exact SzA.mk_zero_mem_center θ _
      obtain ⟨b, hb⟩ := exists_eq_zc_of_mem_center e hθ1 hccen
      have hb0 : b ≠ 0 := by
        rw [← zc_ne_one_iff e]
        intro h
        exact hc1 (by simp [hb, h])
      have haez : a = zc e (e a).b := by
        have h' : e a = (⟨0, (e a).b⟩ : SzA (GaloisField 2 m) θ) := SzA.ext ha rfl
        conv_lhs => rw [← e.symm_apply_apply a]
        rw [h']
        rfl
      have hab0 : (e a).b ≠ 0 := by
        intro h
        apply ha1
        rw [show e a = (⟨0, (e a).b⟩ : SzA (GaloisField 2 m) θ) from SzA.ext ha rfl, h]
        rfl
      obtain ⟨d, hd, hdconj⟩ := szTildeConjZc hsplit hzass h2 hθ1 hθodd htorus hab0 hb0
      have hcoe : (c : G) = d * (a : G) * d⁻¹ := by
        rw [hb, haez]
        exact hdconj
      have hconj := szTilde_conj hsplit hzass h2 hd (a := c) (b := a) hcoe
      have hsaG : ((szTilde hsplit a : Q) : G) = (a : G) := by
        rw [szTilde_eq_tildeOf]
        exact congrArg (fun z : Q => (z : G)) hself
      have hcG : ((szTilde hsplit c : Q) : G) = (c : G) := by
        rw [hconj, hsaG, hcoe]
      exact Subtype.ext hcG
    exact szTildeNotSelf hsplit hzass h2 hθ1 hθodd htorus hall
  rw [szTilde_eq_tildeOf]
  exact szTildeMainStep hsplit hzass h2 hθ1 hθodd htorus (szCanon hsplit)
    ha_ne ha2 hacen h4 hne

end Work.ZassenhausSuzuki
