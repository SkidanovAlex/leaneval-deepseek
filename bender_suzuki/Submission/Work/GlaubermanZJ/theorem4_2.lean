import Mathlib
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.theorem3_2_defs
import Submission.Work.GlaubermanZJ.cor3_1
import Submission.Work.GlaubermanZJ.lemma3_5_a
import Submission.Work.GlaubermanZJ.lemma3_5_b
import Submission.Work.GlaubermanZJ.frattini_sylow
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_ZJ
import Submission.Work.GlaubermanZJ.thompsonJ_eq
import Submission.Work.GlaubermanZJ.ZJ_family
import Submission.Work.GlaubermanZJ.pstable_step
import Submission.Work.GlaubermanZJ.sylow_frattini_sup_normalizer_inf
import Submission.Work.GlaubermanZJ.maxAbelianSubgroup_le_of_pstable_step
import Submission.Work.GlaubermanZJ.cor4_1
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped Classical Pointwise

namespace Work.GlaubermanZJ

/-!
# Glauberman 1968, Theorem 4.2 (p. 1113)

For `p` an odd prime, `S` a Sylow `p`-subgroup of a finite group `X`, `B ⊴ X` a normal
`p`-subgroup of `X` of nilpotence class at most two (`[B,B] ≤ Z(B)`) with
`[B,B] ≤ Z(J(S))`, and `X` `p`-stable, the subgroup `Z(J(S)) ∩ B` is normal in `X`.

The proof is, exactly as Glauberman says on p. 1113, the proof of Theorem 3.2
(`Submission.Work.GlaubermanZJ.theorem3_2`) with Corollary 3.1 replaced by Corollary 4.1:
Corollary 3.1 produces `A ∈ 𝒜(S)` with `[B,A,A] = 1` for *abelian* `B` of maximal order
normalised by `B`, and Corollary 4.1 produces the same `A` for `B` of class at most two with
`[B,B] ≤ Z(B) ∩ Z(J(S))`.  No other step of the proof of Theorem 3.2 uses the abelianness of
`B`:

* the `p`-stability step (3.5) (`Work.GlaubermanZJ.pstable_step`) only uses that `C = Z(J(S)) ∩ B`
  is contained in the normal `p`-subgroup `C₁ = B`;
* (3.6)–(3.8) use `A ∈ 𝒜(S)` with `A ≤ L` (`A = A₀` above) so that `d(L ∩ S) = d(S)` and
  `C ≤ Z(J(L ∩ S))`;
* the final paragraph (`Work.GlaubermanZJ.maxAbelianSubgroup_le_of_pstable_step`) is a pure
  replacement-theorem argument with the normal abelian `p`-subgroup
  `V = (Z(J(L ∩ S))).normalCore`, which contains `C` and lies in `Z(J(L ∩ S))`.

So the only new ingredient here is Corollary 4.1, whose second half gives the required `A₀`.
-/

/-- **The body of Glauberman's Theorem 4.2**, from the single input that some maximal-order
abelian subgroup `A₀ ∈ 𝒜(S)` satisfies `[B,A₀,A₀] = 1`.  For abelian `B` this input is
Corollary 3.1, and the proof below is then literally the proof of Theorem 3.2 (see
`Work.GlaubermanZJ.theorem3_2`); for `B` of nilpotence class at most two with
`[B,B] ≤ Z(J(S))` it is Corollary 4.1. -/
theorem theorem4_2_of_exists_maxAbelian {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hpne : p ≠ 2) (hstab : Work.GlaubermanZJ.IsPStable p X) (S : Sylow p X)
    (B : Subgroup X) [B.Normal] (hBp : IsPGroup p B)
    (hex : ∃ A : Subgroup X, Work.GlaubermanZJ.IsMaxAbelianSubgroup (S : Subgroup X) A ∧
      ⁅⁅B, A⁆, A⁆ = ⊥) :
    (Submission.Blueprint.ZJ (S : Subgroup X) ⊓ B).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `C = Z(J(S)) ∩ B`, and `L = core_X(N_X(C))`: the largest normal subgroup of `X` inside the
  -- normalizer of `C`, as in the proof of Theorem 3.2.
  let Laux : Subgroup X := (Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X)).normalCore
  have hLnorm : Laux.Normal := Subgroup.normalCore_normal _
  have hLle : Laux ≤ Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X) :=
    Subgroup.normalCore_le _
  have hLmax : ∀ K : Subgroup X, K.Normal →
      K ≤ Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X) → K ≤ Laux := by
    intro K hK hKle
    haveI : K.Normal := hK
    exact Subgroup.normal_le_normalCore.mpr hKle
  -- ## The Sylow subgroup and `B`
  have hS_pg : IsPGroup p (S : Subgroup X) := S.isPGroup'
  have hBS : B ≤ (S : Subgroup X) := IsPGroup.le_sylow_of_normal hBp S
  have hS_NC : (S : Subgroup X) ≤
      Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X) := le_normalizer_ZJcore S B
  -- ## Corollary 4.1: `𝒜(S)` contains `A₀` with `[B,A₀,A₀] = 1`
  obtain ⟨A₀, hA₀max, hA₀c⟩ := hex
  have hA₀S : A₀ ≤ (S : Subgroup X) := hA₀max.1
  have hA₀p : IsPGroup p A₀ := hS_pg.to_le hA₀S
  -- ## Step (3.5) with `C₁ = B`: `A₀ ≤ L`
  have hA₀L : A₀ ≤ Laux :=
    pstable_step hp hstab S B B inferInstance hBp (ZJcore_le_B S B) A₀ hA₀S hA₀p hA₀c
  -- ## Lemma 3.5(a): `Z(J(S)) ≤ A₀` and `Z(J(S)) ≤ Z(J(L ∩ S))`
  have hA₀T : A₀ ≤ Laux ⊓ (S : Subgroup X) := le_inf hA₀L hA₀S
  have hZJS_le : Submission.Blueprint.ZJ (S : Subgroup X) ≤
      Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X)) :=
    (lemma3_5_a (S : Subgroup X) (Laux ⊓ (S : Subgroup X)) A₀ hA₀max hA₀T inf_le_right).2
  have hC_le_X₀ : ZJcore S B ≤ Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X)) :=
    (ZJcore_le_ZJ S B).trans hZJS_le
  -- ## The subgroup `V = (Z(J(L ∩ S))).normalCore`, the abelian normal `p`-subgroup of the
  -- final paragraph: `V ≤ Z(J(L ∩ S))` by definition and `C ≤ V` below.
  have hVnorm : (Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))).normalCore.Normal :=
    Subgroup.normalCore_normal _
  have hVle : (Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))).normalCore ≤
      Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X)) := Subgroup.normalCore_le _
  have hVleS : (Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))).normalCore ≤
      (S : Subgroup X) :=
    hVle.trans (((blueprint_ZJ_le_thompsonJ (Laux ⊓ (S : Subgroup X))).trans
      (blueprint_thompsonJ_le (Laux ⊓ (S : Subgroup X)))).trans inf_le_right)
  have hVp : IsPGroup p ((Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))).normalCore) :=
    hS_pg.to_le hVleS
  have hVab : Submission.Blueprint.IsAbelianSubgroup
      ((Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))).normalCore) :=
    isAbelianSubgroup_mono hVle (isAbelianSubgroup_ZJ (Laux ⊓ (S : Subgroup X)))
  -- (3.8): every conjugate of `C` lies in `Z(J(L ∩ S))`.  By Frattini `X = N(L∩S) · L`; elements
  -- of `L` fix `C` and elements of `N(L∩S)` preserve `Z(J(L∩S))`, which is characteristic in
  -- `L ∩ S`.
  have hCV : ZJcore S B ≤ (Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))).normalCore := by
    intro c hc g
    have hfr : Laux ⊔ Subgroup.normalizer ((Laux ⊓ (S : Subgroup X) : Subgroup X) : Set X) =
        ⊤ := sylow_frattini_sup_normalizer_inf (L := Laux) hp S
    have hmul : ((Subgroup.normalizer ((Laux ⊓ (S : Subgroup X) : Subgroup X) : Set X) ⊔ Laux :
        Subgroup X) : Set X) =
        (Subgroup.normalizer ((Laux ⊓ (S : Subgroup X) : Subgroup X) : Set X) : Set X) *
          (Laux : Set X) := Subgroup.mul_normal _ Laux
    have hmem : g ∈
        (Subgroup.normalizer ((Laux ⊓ (S : Subgroup X) : Subgroup X) : Set X) : Set X) *
          (Laux : Set X) := by
      rw [← hmul, ← sup_comm, hfr]
      exact Subgroup.mem_top g
    rw [Set.mem_mul] at hmem
    obtain ⟨n, hn, l, hl, rfl⟩ := hmem
    have hnX₀ : n ∈ Subgroup.normalizer
        ((Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))) : Set X) :=
      normalizer_le_normalizer_ZJ (Laux ⊓ (S : Subgroup X)) hn
    have hlC : l ∈ Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X) := hLle hl
    have hcl : l * c * l⁻¹ ∈ Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X)) :=
      hC_le_X₀ ((Subgroup.mem_normalizer_iff.mp hlC c).mp hc)
    rw [show n * l * c * (n * l)⁻¹ = n * (l * c * l⁻¹) * n⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp hnX₀ (l * c * l⁻¹)).mp hcl
  -- ## The final paragraph (3.3)/(3.9): no element of `𝒜(S)` avoids `L`
  have hall : ∀ A : Subgroup X, IsMaxAbelianSubgroup (S : Subgroup X) A → A ≤ Laux :=
    maxAbelianSubgroup_le_of_pstable_step hp hpne S (ZJcore S B)
      ((Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X))).normalCore) Laux
      hLnorm hVnorm hVp hVab hVle hCV (pstable_step hp hstab S B)
  -- ## `J(S) ≤ L ∩ S`, hence `J(S) = J(L ∩ S)` by Lemma 3.5(b)
  have hJL : Submission.Blueprint.thompsonJ (S : Subgroup X) ≤ Laux := by
    rw [thompsonJ_eq_iSup_ZJfam]
    exact iSup_le fun A => iSup_le fun hA => hall A hA
  have hJT : Submission.Blueprint.thompsonJ (S : Subgroup X) ≤ Laux ⊓ (S : Subgroup X) :=
    le_inf hJL (blueprint_thompsonJ_le _)
  have hJeq : Submission.Blueprint.thompsonJ (S : Subgroup X) =
      Submission.Blueprint.thompsonJ (Laux ⊓ (S : Subgroup X)) := by
    have h1 : Work.PGroup.thompsonJ (S : Subgroup X) ≤ Laux ⊓ (S : Subgroup X) := by
      rw [← thompsonJ_eq (S : Subgroup X)]
      exact hJT
    rw [thompsonJ_eq (S : Subgroup X), thompsonJ_eq (Laux ⊓ (S : Subgroup X))]
    exact lemma3_5_b (S : Subgroup X) (Laux ⊓ (S : Subgroup X)) h1 inf_le_right
  -- ## `N(L ∩ S) ≤ N(C)`
  have hZJeq : Submission.Blueprint.ZJ (Laux ⊓ (S : Subgroup X)) =
      Submission.Blueprint.ZJ (S : Subgroup X) := by
    rw [Submission.Blueprint.ZJ, Submission.Blueprint.ZJ, hJeq]
  have hN_NC : Subgroup.normalizer ((Laux ⊓ (S : Subgroup X) : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((ZJcore S B : Subgroup X) : Set X) := by
    intro g hg
    have hgX₀ : g ∈ Subgroup.normalizer ((Submission.Blueprint.ZJ (S : Subgroup X)) : Set X) := by
      have h := normalizer_le_normalizer_ZJ (Laux ⊓ (S : Subgroup X)) hg
      rwa [hZJeq] at h
    have hgB : g ∈ Subgroup.normalizer (B : Set X) := by
      rw [Subgroup.normalizer_eq_top B]
      exact Subgroup.mem_top g
    exact normalizer_inf_le_normalizer_inf (Submission.Blueprint.ZJ (S : Subgroup X)) B
      ⟨hgX₀, hgB⟩
  -- ## Conclusion: `X = L · N(L ∩ S) ≤ N(C)`, so `C ⊴ X`
  have htop : (⊤ : Subgroup X) ≤
      Subgroup.normalizer ((Submission.Blueprint.ZJ (S : Subgroup X) ⊓ B : Subgroup X) : Set X) := by
    rw [← sylow_frattini_sup_normalizer_inf (L := Laux) hp S]
    exact sup_le hLle hN_NC
  exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm htop le_top).symm

-- Glauberman 1968, Theorem 4.2 (p. 1113): `p` odd, `S` a Sylow `p`-subgroup of a finite group
-- `G`, `B ⊴ G` a normal `p`-subgroup of nilpotence class at most two with `[B,B] ⊆ Z(J(S))`;
-- if `G` is `p`-stable then `Z(J(S)) ∩ B ⊴ G`.  (Proof: substitute Corollary 4.1 — see
-- `Submission.Work.GlaubermanZJ.cor4_1` and `theorem4_1` — for Corollary 3.1 in the proof of
-- Theorem 3.2, pp. 1109-1110.)
theorem theorem4_2 {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2)
    (hps : Work.HallHigman.IsPSolvable p X)
    (h2 : 5 ≤ p ∨ Work.GlaubermanZJ.HasAbelianSylowTwo X)
    (hstab : Work.GlaubermanZJ.IsPStable p X) (S : Sylow p X)
    (B : Subgroup X) [B.Normal] (hBp : IsPGroup p B)
    (hclass : ⁅B, B⁆ ≤ Work.PGroup.centerIn B)
    (hcenter : ⁅B, B⁆ ≤ Submission.Blueprint.ZJ (S : Subgroup X)) :
    (Submission.Blueprint.ZJ (S : Subgroup X) ⊓ B).Normal := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hS_pg : IsPGroup p (S : Subgroup X) := S.isPGroup'
  have hBS : B ≤ (S : Subgroup X) := IsPGroup.le_sylow_of_normal hBp S
  have hBn : (S : Subgroup X) ≤ Subgroup.normalizer (B : Set X) := by
    rw [Subgroup.normalizer_eq_top B]
    exact le_top
  obtain ⟨A₀, hA₀⟩ :=
    (cor4_1 p hp hpne (S : Subgroup X) B hS_pg hBS hBn hBp hclass hcenter).2
  exact theorem4_2_of_exists_maxAbelian hp hpne hstab S B hBp ⟨A₀, hA₀⟩

end Work.GlaubermanZJ
