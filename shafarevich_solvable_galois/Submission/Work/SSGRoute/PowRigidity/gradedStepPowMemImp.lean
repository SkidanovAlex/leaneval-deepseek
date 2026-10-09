import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.prop5Data_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `2`-power rigidity step of the graded step

This file proves `Work.SSGRoute.PowRigidity.gradedStepPowMemImp`: for a free group `F = FreeGroup X`
on a finite set, if `u` lies in the paper's `γ_j = centralSeries F j` and the `2^k`-th power of `u`
lies in the refined term `F_{(j+k, j+1)} = (P_{j+k} ∩ γ_{j+1})P_{j+k+1}`, then `u ∈ P_{j+1}`.

This is the "`2`-power rigidity" used for the injectivity of the map
`ψ : E(j,j) → E(j+k,j)`, `[u] ↦ [u^{2^k}]`, of the `p = 2` correction (Schmidt–Wingberg,
arXiv:math/9809211, §2 and the correction note).

The proof is purely group-theoretic:

* writing `u^{2^k} = x·y` with `x ∈ P_{j+k} ∩ γ_{j+1}` and `y ∈ P_{j+k+1}`, one has
  `y = x⁻¹u^{2^k} ∈ γ_j`;
* Lemma 4(ii) of Schmidt–Wingberg (`Work.SSGRoute.prop5.pSeries_inter_lcs_subset`) gives
  `y ∈ ⟨γ_j^{2^{k+1}}⟩·γ_{j+1}`, and since the image of `γ_j` modulo `γ_{j+1}` is abelian this
  single-power refinement `y = w^{2^{k+1}}·g` holds with `g ∈ γ_{j+1}`;
* conjugating `x` by `w^{2^{k+1}}` (and using that `γ_{j+1}` is normal) gives
  `u^{2^k} = w^{2^{k+1}}·g'` with `g' ∈ γ_{j+1}`;
* the torsion-freeness of the lower central factors of a free group
  (`Work.SSGRoute.prop5.lowerCentralSeries_torsionFree`) then yields `u ≡ w² mod γ_{j+1}`, i.e.
  `u ∈ γ_j²·γ_{j+1} ⊆ P_{j+1}`.
-/

set_option linter.unusedVariables false

namespace Work.SSGRoute.PowRigidity

open Work.CohomologicalShrinking

open scoped commutatorElement

/-- **Single `q`-th power out of a power subgroup.**  Let `A, B ≤ P` with `B` normal and
`⁅A, A⁆ ≤ B` (so that the image of `A` in `P/B` is abelian).  Then every element of
`powSubgroup q A ⊔ B` is a single `q`-th power of an element of `A` times an element of `B`. -/
theorem exists_pow_mul_of_mem_powSubgroup_sup {P : Type*} [Group P] (A B : Subgroup P) [B.Normal]
    (hAB : ⁅A, A⁆ ≤ B) (q : ℕ) {y : P}
    (hy : y ∈ Work.Shrinking.powSubgroup q A ⊔ B) :
    ∃ w ∈ A, ∃ g ∈ B, y = w ^ q * g := by
  classical
  let π : P →* P ⧸ B := QuotientGroup.mk' B
  have hker : π.ker = B := QuotientGroup.ker_mk' B
  -- the image of `A` in `P/B` is abelian
  have hcomm : ∀ a ∈ Subgroup.map π A, ∀ b ∈ Subgroup.map π A, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hmem : ⁅a, b⁆ ∈ B := hAB (Subgroup.commutator_mem_commutator ha hb)
    have h1 : π ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff ⁅a, b⁆).mpr hmem
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_commute.mp h1
  -- in an abelian image the power subgroup is the set of `q`-th powers
  have hkey : ∀ z : P ⧸ B, z ∈ Work.Shrinking.powSubgroup q (Subgroup.map π A) ↔
      ∃ a ∈ A, (π a) ^ q = z := by
    intro z
    constructor
    · intro hz
      refine Subgroup.closure_induction (p := fun z _ => ∃ a ∈ A, (π a) ^ q = z) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨ā, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · exact ⟨1, A.one_mem, by simp⟩
      · rintro y z hy hz ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        have hc : Commute (π a) (π b) :=
          hcomm (π a) (Subgroup.mem_map_of_mem π ha) (π b) (Subgroup.mem_map_of_mem π hb)
        exact ⟨a * b, A.mul_mem ha hb, by rw [map_mul, hc.mul_pow]⟩
      · rintro y hy ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha, by rw [map_inv, inv_pow]⟩
    · rintro ⟨a, ha, rfl⟩
      exact Subgroup.subset_closure ⟨π a, Subgroup.mem_map_of_mem π ha, rfl⟩
  -- the class of `y` is a `q`-th power of the class of an element of `A`
  have hmapB : Subgroup.map π B = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    rw [hker]
  have hyπ : π y ∈ Work.Shrinking.powSubgroup q (Subgroup.map π A) := by
    have h1 : π y ∈ Subgroup.map π (Work.Shrinking.powSubgroup q A ⊔ B) :=
      Subgroup.mem_map_of_mem π hy
    rwa [Subgroup.map_sup, Work.Shrinking.map_powSubgroup, hmapB, sup_bot_eq] at h1
  obtain ⟨a, ha, haq⟩ := (hkey (π y)).mp hyπ
  refine ⟨a, ha, (a ^ q)⁻¹ * y, ?_, by group⟩
  refine (QuotientGroup.eq_one_iff ((a ^ q)⁻¹ * y)).mp ?_
  show π ((a ^ q)⁻¹ * y) = 1
  rw [map_mul, map_inv, map_pow, haq, inv_mul_cancel]

/-- **Root extraction modulo the next lower central term.**  If `u, w ∈ γ_j` and
`u^{2^k} ≡ w^{2^{k+1}} mod γ_{j+1}`, then `u ≡ w² mod γ_{j+1}`.  This is the torsion-freeness of
the lower central factor `γ_j/γ_{j+1}` of a free group. -/
theorem exists_gamma_succ_mul_sq (X : Type) [Fintype X] (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    {u w g : FreeGroup X}
    (hu : u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (hw : w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j)
    (h : u ^ (2 ^ k) = w ^ (2 ^ (k + 1)) * g) :
    ∃ s ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j, u = s * w ^ 2 := by
  classical
  let π : FreeGroup X →* FreeGroup X ⧸ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j :=
    QuotientGroup.mk' ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j)
  have hg1 : π g = 1 :=
    (QuotientGroup.eq_one_iff (N := (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j) g).mpr hg
  -- `π u` and `π w` commute: the image of `γ_j` is abelian
  have huw : Commute (π u) (π w) := by
    have hmem : ⁅u, w⁆ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
      have h0 : ⁅u, w⁆ ∈ ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
          (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)⁆ :=
        Subgroup.commutator_mem_commutator hu hw
      have hle : ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
          (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)⁆ ≤
          (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
        rw [show (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j =
            ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1), ⊤⁆ from by
          rw [← Subgroup.lowerCentralSeries_succ (⊤ : Subgroup (FreeGroup X)) (j - 1),
            show j - 1 + 1 = j from by omega]]
        exact Subgroup.commutator_mono le_rfl le_top
      exact hle h0
    have h1 : π ⁅u, w⁆ = 1 :=
      (QuotientGroup.eq_one_iff (N := (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j) ⁅u, w⁆).mpr
        hmem
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_commute.mp h1
  have hwin : Commute (π u) (π (w ^ 2)⁻¹) := by
    have h2 : Commute (π u) (π w ^ 2) := huw.pow_right 2
    simpa using h2.inv_right
  -- the class of `(u * (w^2)⁻¹)^(2^k)` is trivial
  have hmain : π ((u * (w ^ 2)⁻¹) ^ (2 ^ k)) = 1 := by
    rw [map_pow, map_mul, hwin.mul_pow]
    have h1 : π u ^ (2 ^ k) = π w ^ (2 ^ (k + 1)) := by
      rw [← map_pow, h, map_mul, map_pow, hg1, mul_one]
    have h2 : (π (w ^ 2)⁻¹) ^ (2 ^ k) = (π w ^ (2 ^ (k + 1)))⁻¹ := by
      rw [map_inv, map_pow, inv_pow]
      congr 1
      rw [← pow_mul]
      rw [show 2 * 2 ^ k = 2 ^ (k + 1) from by rw [pow_succ]; ring]
    rw [h1, h2, mul_inv_cancel]
  have hs : u * (w ^ 2)⁻¹ ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (Subgroup.pow_mem _ hw 2))
  have hsp : (u * (w ^ 2)⁻¹) ^ (2 ^ k) ∈
      (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j :=
    (QuotientGroup.eq_one_iff (N := (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j)
      ((u * (w ^ 2)⁻¹) ^ (2 ^ k))).mp hmain
  exact ⟨u * (w ^ 2)⁻¹,
    Work.SSGRoute.prop5.lowerCentralSeries_torsionFree X j hj _ hs (2 ^ k)
      (pow_pos (by norm_num) k) hsp,
    by group⟩

/-- **The `2`-power rigidity, at the small universe.**  For `X : Type` (and `Fintype X`), if
`u ∈ γ_j` and `u^{2^k} ∈ (P_{j+k} ∩ γ_{j+1})P_{j+k+1}` with `j ≥ 2`, `k ≥ 1`, then `u ∈ P_{j+1}`. -/
theorem gradedStepPowMemImp_small (X : Type) [Fintype X] (j k : ℕ) (hj : 2 ≤ j) (hk : 1 ≤ k)
    {u : FreeGroup X}
    (hu : u ∈ centralSeries (FreeGroup X) j)
    (h : u ^ (2 ^ k) ∈ refinedTerm 2 (FreeGroup X) (j + k) (j + 1)) :
    u ∈ pSeries 2 (FreeGroup X) (j + 1) := by
  have hj1 : 1 ≤ j := by omega
  -- decompose the hypothesis
  obtain ⟨x, hx, y, hy, hxy⟩ := (Subgroup.mem_sup_of_normal_right
    (s := pSeries 2 (FreeGroup X) (j+k) ⊓ centralSeries (FreeGroup X) (j+1))
    (t := pSeries 2 (FreeGroup X) (j+k+1))).mp h
  have hxγ : x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := hx.2
  have hyP : y ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup X) (j + k) := hy
  have hzγ : u ^ (2 ^ k) ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
    Subgroup.pow_mem _ hu _
  -- `y = x⁻¹u^{2^k}` lies in `γ_j`
  have hyγ : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) := by
    have hxγ' : x ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1) :=
      Subgroup.lowerCentralSeries_antitone _ (by omega : j - 1 ≤ j) hxγ
    have hyx : y = x⁻¹ * u ^ (2 ^ k) := by rw [← hxy]; group
    rw [hyx]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxγ') hzγ
  -- Lemma 4(ii) of Schmidt-Wingberg
  have h4ii := Work.SSGRoute.prop5.pSeries_inter_lcs_subset 2 X (j + k + 1) j hj1 (by omega)
  rw [show j + k + 1 - j = k + 1 from by omega] at h4ii
  have hyPow : y ∈ Work.Shrinking.powSubgroup (2 ^ (k+1))
        ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j :=
    h4ii (Subgroup.mem_inf.mpr ⟨by simpa using hyP, hyγ⟩)
  -- the image of `γ_j` modulo `γ_{j+1}` is abelian
  have hAB : ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1),
              (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)⁆ ≤
            (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := by
    rw [show (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j =
        ⁅(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1), ⊤⁆ from by
      rw [← Subgroup.lowerCentralSeries_succ (⊤ : Subgroup (FreeGroup X)) (j - 1),
        show j - 1 + 1 = j from by omega]]
    exact Subgroup.commutator_mono le_rfl le_top
  have hN : ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j).Normal :=
    Subgroup.lowerCentralSeries_normal _ j
  -- a single `2^{k+1}`-st power
  obtain ⟨w, hwγ, g₁, hg₁, hyw⟩ := exists_pow_mul_of_mem_powSubgroup_sup
    ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
    ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j) hAB (2 ^ (k+1)) hyPow
  -- conjugate the `γ_{j+1}`-part of the decomposition
  have hconj : (w ^ (2 ^ (k+1)))⁻¹ * x * ((w ^ (2 ^ (k+1)))⁻¹)⁻¹ ∈
      (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j := hN.conj_mem (n := x) hxγ _
  have hg : ((w ^ (2 ^ (k+1)))⁻¹ * x * w ^ (2 ^ (k+1))) * g₁ ∈
      (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries j :=
    Subgroup.mul_mem _ (by simpa using hconj) hg₁
  have hdecomp : u ^ (2 ^ k) =
      w ^ (2 ^ (k+1)) * ((w ^ (2 ^ (k+1)))⁻¹ * x * w ^ (2 ^ (k+1)) * g₁) := by
    rw [← hxy, hyw]; group
  -- root extraction
  obtain ⟨s, hs, hsu⟩ := exists_gamma_succ_mul_sq X j k hj1 hk hu hwγ hg hdecomp
  have hsP : s ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup X) j :=
    Work.ProP.lowerCentralSeries_le_pCentralSeries 2 (FreeGroup X) j hs
  have hwP : w ^ 2 ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup X) j := by
    have hwPj : w ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup X) (j - 1) :=
      Work.ProP.lowerCentralSeries_le_pCentralSeries 2 (FreeGroup X) (j - 1) hwγ
    have hstep : Work.Shrinking.pCentralSeries 2 (FreeGroup X) j =
        Work.Shrinking.pCentralStep 2 (Work.Shrinking.pCentralSeries 2 (FreeGroup X) (j - 1)) := by
      rw [← Work.Shrinking.pCentralSeries_succ 2 (FreeGroup X) (j - 1),
        show j - 1 + 1 = j from by omega]
    rw [hstep]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨w, hwPj, rfl⟩)
  rw [hsu]
  exact Subgroup.mul_mem _ hsP hwP

/-- **The `2`-power rigidity step of the graded step** (the statement requested by the consumer).

If `u ∈ γ_j` and `u^{2^k}` lies in the refined term `F_{(j+k,j+1)} = (P_{j+k} ∩ γ_{j+1})P_{j+k+1}`
for `j ≥ 2` and `k ≥ 1`, then `u ∈ P_{j+1}`.

The statement is universe-polymorphic in `X`; the free groups appearing in the available Magnus
and torsion-freeness lemmas of the workspace are at universe `0`, so the proof reduces to the case
`X = Fin (Fintype.card X)` (`gradedStepPowMemImp_small`) via the free group isomorphism induced by
`Fintype.equivFin`. -/
theorem gradedStepPowMemImp (X : Type*) [Fintype X]
    (j k : ℕ) (hj : 2 ≤ j) (hk : 1 ≤ k) {u : FreeGroup X}
    (hu : u ∈ Work.CohomologicalShrinking.centralSeries (FreeGroup X) j)
    (h : u ^ (2 ^ k) ∈ Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) (j + k) (j + 1)) :
    u ∈ Work.CohomologicalShrinking.pSeries 2 (FreeGroup X) (j + 1) := by
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let E : FreeGroup X ≃* FreeGroup (Fin (Fintype.card X)) := FreeGroup.freeGroupCongr e
  have hu' : E u ∈ centralSeries (FreeGroup (Fin (Fintype.card X))) j := by
    have hm := map_centralSeries_eq_of_surjective
      (E : FreeGroup X →* FreeGroup (Fin (Fintype.card X))) E.surjective j
    rw [← hm]
    exact Subgroup.mem_map_of_mem _ hu
  have h' : (E u) ^ (2 ^ k) ∈
      refinedTerm 2 (FreeGroup (Fin (Fintype.card X))) (j + k) (j + 1) := by
    have hm := map_refinedTerm_le_of_surjective 2
      (E : FreeGroup X →* FreeGroup (Fin (Fintype.card X))) E.surjective (j + k) (j + 1)
    refine hm ?_
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem _ h
  have hv := gradedStepPowMemImp_small (Fin (Fintype.card X)) j k hj hk hu' h'
  have hback := Work.Shrinking.map_pCentralSeries_surjective 2
    (E.symm : FreeGroup (Fin (Fintype.card X)) →* FreeGroup X) E.symm.surjective j
  show u ∈ Work.Shrinking.pCentralSeries 2 (FreeGroup X) j
  rw [← hback]
  exact ⟨E u, hv, by simp⟩

end Work.SSGRoute.PowRigidity
