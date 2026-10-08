import Mathlib
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThreePoints.P3NeBot

/-!
# Peterfalvi I Ch. II §4 Lemma 1 (p. 169), forward half

If `X ≤ V = C_D(t)` and `k ∈ K = J(D,t)` normalises `X`, then `k ∈ F₁ = ⟨Inv C_G(X)⟩`.

The source proves this by quoting Ch. II §4 Prop. 1 ("`N_G(X)` has a single class of
involutions", p. 169), an invocation of the whole (B0)–(B2) machinery.  There is however a
direct argument that does not use Prop. 1 at all, and that is the one formalised here.

Put `s = t * k`.  Since `t k t = k⁻¹` (equivalently `t * k = k⁻¹ * t`), `s` is an involution
with `s * t = k⁻¹`; and `t * s = k` has **odd** order, because `k ∈ K ⊆ D = H ⊓ H^t` and `D` has
odd order.  So `t` and `s` are conjugate by an involution of `⟨t, s⟩` — this is Peterfalvi I
Ch. I §2 Prop. 1 (a), `Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul`.  Now `t`
centralises `X` (as `X ≤ V ≤ C_G(t)`), while `k`, hence `s = t * k`, normalises `X`; so the
conjugating involution `u` lies in `⟨t, s⟩ ≤ N_G(X)`.  As `C_G(X)` is `N_G(X)`-invariant,
`s = u t u⁻¹ ∈ C_G(X)`; both `t` and `s` are involutions of `C_G(X)`, whence
`k = t * s ∈ F₁ = ⟨Inv C_G(X)⟩`.

In particular no use is made of the (B0)–(B2) inputs `hFT, hC, hA, hBrSz, hS`: the statement is
about `D`, `K` and `X` alone.
-/

/-- `C_G(X)` is invariant under conjugation by elements of `N_G(X)`: if `g` normalises `X`, then
`g u g⁻¹` centralises `X` for every `u` centralising `X`. -/
theorem conj_mem_centralizer_of_mem_normalizer {G : Type} [Group G] {X : Subgroup G} {g u : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hu : u ∈ Subgroup.centralizer (X : Set G)) :
    g * u * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  have hu' := Subgroup.mem_centralizer_iff.mp hu
  have hy' : g⁻¹ * y * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hg y).mp hy
  have h := hu' (g⁻¹ * y * g) hy'
  calc y * (g * u * g⁻¹) = g * ((g⁻¹ * y * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
    _ = (g * u * g⁻¹) * y := by group

/-- Peterfalvi I Ch. II §4 Lemma 1 (p. 169), forward half: if `X ≤ V = C_D(t)` and
`k ∈ K = J(D,t)` normalises `X`, then `k ∈ F₁ = ⟨Inv C_G(X)⟩`.
(NOTE: `3 ≤ (fixedPts H X).ncard` follows from `X ≤ centD H t` and must be re-proved here; see
`Work.ThreePoints.three_le_ncard_fixedPts_centD` in the `hole`-carrying
`Submission.Work.ThreePoints.centD_eq_centralizer_of_involution`, or reproduce it directly.)
Do not import any module whose closure still contains `hole`. -/
theorem p3_lemma1 {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ Submission.Blueprint.centD H t) {k : G}
    (hk : k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t)
    (hkn : k ∈ Subgroup.normalizer (X : Set G)) :
    k ∈ Work.ThreePoints.p3F1 X := by
  -- ### elementary facts about `t`, `k` and `D = H ⊓ H^t`
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := hk.1
  have hkt : t * k * t = k⁻¹ := by simpa [htinv] using hk.2
  -- `D = H ⊓ H^t` has odd order, hence so does `orderOf k`
  have hoddD : Odd (Nat.card (Submission.Blueprint.twoPoint H t : Subgroup G)) :=
    IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hdvd : orderOf k ∣ Nat.card (Submission.Blueprint.twoPoint H t : Subgroup G) := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hkD)
  have hoddk : Odd (orderOf k) := Odd.of_dvd hdvd hoddD
  -- ### `t` centralises `X`, because `X ≤ V = C_D(t)`
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (mem_centD.mp (hX hx)).2.2
  have htN : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) htC
  -- ### `t * k` is an involution
  have htk_ne : t * k ≠ 1 := by
    intro hcon
    have htk_eq : t = k⁻¹ := eq_inv_of_mul_eq_one_left hcon
    refine htH ?_
    rw [htk_eq]
    exact (show Submission.Blueprint.twoPoint H t ≤ H from inf_le_left)
      ((Submission.Blueprint.twoPoint H t).inv_mem hkD)
  have htkinv : (t * k)⁻¹ = t * k := by
    rw [mul_inv_rev, htinv, ← hkt, mul_assoc, ht2, mul_one]
  have htk_mul : (t * k) * (t * k) = 1 := by
    have h := mul_inv_cancel (t * k)
    rwa [htkinv] at h
  have htk2 : orderOf (t * k) = 2 := orderOf_eq_two_of htk_ne htk_mul
  -- ### `t * (t * k) = k` has odd order, so `t` and `t * k` are conjugate by an involution
  --     of `⟨t, t * k⟩` (Peterfalvi I Ch. I §2 Prop. 1 (a))
  have hmul : t * (t * k) = k := by rw [← mul_assoc, ht2, one_mul]
  have hodd_tk : Odd (orderOf (t * (t * k))) := by rw [hmul]; exact hoddk
  obtain ⟨u, -, huconj, hucl⟩ := exists_involution_conj_of_odd_orderOf_mul ht htk2 hodd_tk
  -- ### that involution lies in `N_G(X)`, hence `t * k ∈ C_G(X)`
  have htkN : t * k ∈ Subgroup.normalizer (X : Set G) := Subgroup.mul_mem _ htN hkn
  have hcl : Subgroup.closure ({t, t * k} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htN
    · exact htkN
  have huN : u ∈ Subgroup.normalizer (X : Set G) := hcl hucl
  have htkC : t * k ∈ Subgroup.centralizer (X : Set G) := by
    rw [← huconj]
    exact conj_mem_centralizer_of_mem_normalizer huN htC
  -- ### conclude: `k = t * (t * k)` is a product of two involutions of `C_G(X)`
  have htF : t ∈ Work.ThreePoints.p3F1 X := mem_p3F1_of_mem_involutions ⟨htC, ht⟩
  have htkF : t * k ∈ Work.ThreePoints.p3F1 X :=
    mem_p3F1_of_mem_involutions ⟨htkC, htk2⟩
  have hprod : t * (t * k) ∈ Work.ThreePoints.p3F1 X := Subgroup.mul_mem _ htF htkF
  rwa [hmul] at hprod

end Work.ThreePoints.P3NeBot
