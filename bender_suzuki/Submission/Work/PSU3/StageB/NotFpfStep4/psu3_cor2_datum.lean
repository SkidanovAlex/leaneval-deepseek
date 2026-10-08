import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.Model.psu3_datum
import Submission.Work.PSU3.StageB.NotFpfStep4.psu3_cor2_W
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageA.centD_le_W_psu3Model
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Abstract.eq_U_of_isSplitRankOne
import Submission.Work.PSU3.BenderST.transport
import Submission.Work.PSU3.BST.psu3_wTrans
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs

/-! ## Conjugation of `twoPoint` and of `V = C_D(t)` -/

private lemma conj_mem_twoPoint {G : Type} [Group G] {H : Subgroup G} {t x g : G}
    (hx : x ∈ Submission.Blueprint.twoPoint H t) :
    g * x * g⁻¹ ∈ Submission.Blueprint.twoPoint
      (Submission.Blueprint.conj g H) (g * t * g⁻¹) := by
  rw [Work.Models.mem_twoPoint_iff] at hx ⊢
  obtain ⟨hxH, hxt⟩ := hx
  refine ⟨?_, ?_⟩
  · refine Work.Models.mem_conj_iff.mpr ?_
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x from by group]
  · refine Work.Models.mem_conj_iff.mpr ?_
    rwa [show g⁻¹ * ((g * t * g⁻¹)⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)) * g = t⁻¹ * x * t
      from by group]

private lemma conj_mem_centD {G : Type} [Group G] {H : Subgroup G} {t ζ g : G}
    (hζ : ζ ∈ Submission.Blueprint.centD H t) :
    g * ζ * g⁻¹ ∈ Submission.Blueprint.centD
      (Submission.Blueprint.conj g H) (g * t * g⁻¹) := by
  simp only [Submission.Blueprint.centD, Subgroup.mem_inf] at hζ ⊢
  obtain ⟨hζD, hζc⟩ := hζ
  refine ⟨conj_mem_twoPoint hζD, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hζc ⊢
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hcomm : ζ * t = t * ζ := (hζc t (Set.mem_singleton t)).symm
  calc (g * t * g⁻¹) * (g * ζ * g⁻¹)
      = g * (t * ζ) * g⁻¹ := by group
    _ = g * (ζ * t) * g⁻¹ := by rw [hcomm]
    _ = (g * ζ * g⁻¹) * (g * t * g⁻¹) := by group

theorem psu3_cor2_datum {n : ℕ} (hn : 2 ≤ n) {B U : Subgroup (LeanEval.GroupTheory.Defs.PSU3Model n)}
    {w : LeanEval.GroupTheory.Defs.PSU3Model n} (h : Submission.Blueprint.IsSplitRankOne B U w)
    {ζ : LeanEval.GroupTheory.Defs.PSU3Model n} (hζ : ζ ∈ Submission.Blueprint.centD B w)
    (hζ1 : ζ ≠ 1) :
    ∃ ω : ↥U, ((ω : LeanEval.GroupTheory.Defs.PSU3Model n) *
        (ω : LeanEval.GroupTheory.Defs.PSU3Model n) ≠ 1) ∧
      ((Work.PSU3.StageB.fcan h ω : ↥U) : LeanEval.GroupTheory.Defs.PSU3Model n)
        = ζ⁻¹ * (ω : LeanEval.GroupTheory.Defs.PSU3Model n)⁻¹ * ζ ∧
      ((Work.PSU3.StageB.hcan h ω : ↥(Submission.Blueprint.twoPoint B w)) :
        LeanEval.GroupTheory.Defs.PSU3Model n) = ζ ^ 3 := by
  classical
  -- The standard split rank-one datum of the model.
  have h0 : Submission.Blueprint.IsSplitRankOne (Submission.PSU3.psu3B n)
      (Submission.PSU3.psu3U n) (Submission.PSU3.psu3Weyl n) :=
    Work.PSU3.Model.psu3_isSplitRankOne n hn
  -- ## Step 1. `B` is a conjugate of the standard Borel.
  obtain ⟨g, hg⟩ := Work.Models.Abstract.exists_conj_eq (Submission.PSU3.psu3BenderPair n hn)
    h.stronglyEmbedded
  have hgB : B = Submission.Blueprint.conj g (Submission.PSU3.psu3B n) := hg
  -- ## Step 2. Transport the datum by `g⁻¹`; its unipotent radical is `psu3U n`.
  have h1 : Submission.Blueprint.IsSplitRankOne (Submission.Blueprint.conj g⁻¹ B)
      (Submission.Blueprint.conj g⁻¹ U) (g⁻¹ * w * g) := by
    have h1' := Work.PSU3.BenderST.isSplitRankOne_map
      (MulAut.conj g⁻¹ : PSU3Model n ≃* PSU3Model n) h
    rw [show (MulAut.conj g⁻¹ : PSU3Model n ≃* PSU3Model n) w = g⁻¹ * w * g from by
      rw [MulAut.conj_apply, inv_inv]] at h1'
    exact h1'
  have hB' : Submission.Blueprint.conj g⁻¹ B = Submission.PSU3.psu3B n := by
    rw [hgB, Work.Models.conj_inv_conj]
  rw [hB'] at h1
  have hU' : Submission.Blueprint.conj g⁻¹ U = Submission.PSU3.psu3U n :=
    Work.Models.Abstract.eq_U_of_isSplitRankOne (Submission.PSU3.psu3BenderPair n hn) h1
  have hU'' : Submission.Blueprint.conj g (Submission.PSU3.psu3U n) = U := by
    have hh := congrArg (Submission.Blueprint.conj g) hU'
    rw [Work.Models.conj_conj_inv] at hh
    exact hh.symm
  -- ## Step 3. `g⁻¹ w g` is an involution outside the standard Borel, so it is
  -- `B̄`-conjugate to `w̄`.
  have hw'2 : orderOf (g⁻¹ * w * g) = 2 := by
    rw [show g⁻¹ * w * g = (MulAut.conj g⁻¹ : PSU3Model n ≃* PSU3Model n) w from by
      rw [MulAut.conj_apply, inv_inv]]
    rw [MulEquiv.orderOf_eq, h.invol]
  have hw'B : g⁻¹ * w * g ∉ Submission.PSU3.psu3B n := by
    intro hmem
    apply h.not_mem
    have h2 : w ∈ Submission.Blueprint.conj g (Submission.PSU3.psu3B n) :=
      Subgroup.mem_map.mpr ⟨g⁻¹ * w * g, hmem, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rw [← hgB] at h2
    exact h2
  obtain ⟨b, hb, hbw⟩ := Work.PSU3.BST.transitive_involutions_outside' h0 hw'2 hw'B
  -- ## Step 4. `g' = g b` conjugates the standard datum onto our datum.
  let g' : PSU3Model n := g * b
  have hbB0 : Submission.Blueprint.conj b (Submission.PSU3.psu3B n) = Submission.PSU3.psu3B n :=
    Work.Models.conj_self_of_mem_normalizer (Subgroup.le_normalizer hb)
  have hbU0 : Submission.Blueprint.conj b (Submission.PSU3.psu3U n) = Submission.PSU3.psu3U n :=
    Work.Models.conj_self_of_mem_normalizer (h0.normal hb)
  have hg'B : Submission.Blueprint.conj g' (Submission.PSU3.psu3B n) = B := by
    show Submission.Blueprint.conj (g * b) (Submission.PSU3.psu3B n) = B
    rw [Work.Models.conj_mul, hbB0]
    exact hgB.symm
  have hg'U : Submission.Blueprint.conj g' (Submission.PSU3.psu3U n) = U := by
    show Submission.Blueprint.conj (g * b) (Submission.PSU3.psu3U n) = U
    rw [Work.Models.conj_mul, hbU0]
    exact hU''
  have hg'w : g' * Submission.PSU3.psu3Weyl n * g'⁻¹ = w := by
    show (g * b) * Submission.PSU3.psu3Weyl n * (g * b)⁻¹ = w
    rw [show (g * b) * Submission.PSU3.psu3Weyl n * (g * b)⁻¹
          = g * (b * Submission.PSU3.psu3Weyl n * b⁻¹) * g⁻¹ from by group,
      show b * Submission.PSU3.psu3Weyl n * b⁻¹ = g⁻¹ * w * g from hbw.symm]
    group
  -- ## Step 5. `ζ' = g'⁻¹ ζ g'` lies in `V = W` of the standard datum.
  let ζ' : PSU3Model n := g'⁻¹ * ζ * g'
  have hζ'eq : ζ' = g'⁻¹ * ζ * g' := rfl
  have hζ'D : ζ' ∈ Submission.Blueprint.centD (Submission.PSU3.psu3B n)
      (Submission.PSU3.psu3Weyl n) := by
    have h := conj_mem_centD (g := g'⁻¹) hζ
    have hB'' : Submission.Blueprint.conj g'⁻¹ B = Submission.PSU3.psu3B n := by
      rw [← hg'B, Work.Models.conj_inv_conj]
    have hw'' : g'⁻¹ * w * (g'⁻¹)⁻¹ = Submission.PSU3.psu3Weyl n := by
      rw [inv_inv]
      calc g'⁻¹ * w * g'
          = g'⁻¹ * (g' * Submission.PSU3.psu3Weyl n * g'⁻¹) * g' := by rw [hg'w]
        _ = Submission.PSU3.psu3Weyl n := by group
    rw [hB'', hw''] at h
    rw [hζ'eq]
    simpa only [inv_inv] using h
  have hζ'W : ζ' ∈ Work.ThmF.W (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n) :=
    Work.PSU3.StageA.centD_le_W_psu3Model n hζ'D
  have hζ'1 : ζ' ≠ 1 := by
    intro hz
    apply hζ1
    have hζeq : ζ = g' * ζ' * g'⁻¹ := by rw [hζ'eq]; group
    rw [hζeq, hz, mul_one, mul_inv_cancel]
  -- ## Step 6. The model corollary for the standard datum.
  obtain ⟨ω₀, hω₀2, hf₀, hh₀⟩ := psu3_cor2_W hn hζ'W hζ'1
  have hω₀ne : (ω₀ : PSU3Model n) ≠ 1 := by
    intro hω1
    exact hω₀2 (by rw [hω1, mul_one])
  -- ## Step 7. Conjugate back.
  have hmemω : g' * (ω₀ : PSU3Model n) * g'⁻¹ ∈ U := by
    have h2 : g' * (ω₀ : PSU3Model n) * g'⁻¹ ∈
        Submission.Blueprint.conj g' (Submission.PSU3.psu3U n) :=
      Subgroup.mem_map.mpr ⟨(ω₀ : PSU3Model n), ω₀.2, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [hg'U] at h2
  let ω : ↥U := ⟨g' * (ω₀ : PSU3Model n) * g'⁻¹, hmemω⟩
  have hωcoe : (ω : PSU3Model n) = g' * (ω₀ : PSU3Model n) * g'⁻¹ := rfl
  have hωω : (ω : PSU3Model n) * (ω : PSU3Model n) ≠ 1 := by
    intro hcon
    apply hω₀2
    calc (ω₀ : PSU3Model n) * (ω₀ : PSU3Model n)
        = g'⁻¹ * ((ω : PSU3Model n) * (ω : PSU3Model n)) * g' := by
          rw [hωcoe]; group
      _ = g'⁻¹ * 1 * g' := by rw [hcon]
      _ = 1 := by group
  have hωne : (ω : PSU3Model n) ≠ 1 := by
    intro h1
    exact hωω (by rw [h1, mul_one])
  -- ## Step 8. The canonical relation of `ω`, conjugated from that of `ω₀`.
  have hs₀ := Work.PSU3.StageB.canon_spec h0 hω₀ne
  have heq : w * (ω : PSU3Model n) * w
      = (g' * ((Work.PSU3.StageB.gcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n) * g'⁻¹)
        * (g' * ((Work.PSU3.StageB.hcan h0 ω₀
              : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
                  (Submission.PSU3.psu3Weyl n))) : PSU3Model n) * g'⁻¹)
        * w
        * (g' * ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n) * g'⁻¹) := by
    have hL : w * (ω : PSU3Model n) * w
        = g' * (Submission.PSU3.psu3Weyl n * (ω₀ : PSU3Model n)
            * Submission.PSU3.psu3Weyl n) * g'⁻¹ := by
      rw [hωcoe, show w = g' * Submission.PSU3.psu3Weyl n * g'⁻¹ from hg'w.symm]
      group
    have hR : (g' * ((Work.PSU3.StageB.gcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n) * g'⁻¹)
        * (g' * ((Work.PSU3.StageB.hcan h0 ω₀
              : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
                  (Submission.PSU3.psu3Weyl n))) : PSU3Model n) * g'⁻¹)
        * w
        * (g' * ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n) * g'⁻¹)
        = g' * (((Work.PSU3.StageB.gcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
            * ((Work.PSU3.StageB.hcan h0 ω₀
                : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
                    (Submission.PSU3.psu3Weyl n))) : PSU3Model n)
            * Submission.PSU3.psu3Weyl n
            * ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)) * g'⁻¹ := by
      rw [show w = g' * Submission.PSU3.psu3Weyl n * g'⁻¹ from hg'w.symm]
      group
    rw [hL, hR, hs₀]
  have hG₀U : g' * ((Work.PSU3.StageB.gcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
      * g'⁻¹ ∈ U := by
    have h2 : g' * ((Work.PSU3.StageB.gcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
        * g'⁻¹ ∈ Submission.Blueprint.conj g' (Submission.PSU3.psu3U n) :=
      Subgroup.mem_map.mpr
        ⟨((Work.PSU3.StageB.gcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n),
          (Work.PSU3.StageB.gcan h0 ω₀).2, by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [hg'U] at h2
  have hY₀U : g' * ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
      * g'⁻¹ ∈ U := by
    have h2 : g' * ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
        * g'⁻¹ ∈ Submission.Blueprint.conj g' (Submission.PSU3.psu3U n) :=
      Subgroup.mem_map.mpr
        ⟨((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n),
          (Work.PSU3.StageB.fcan h0 ω₀).2, by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [hg'U] at h2
  have hD₀T : g' * ((Work.PSU3.StageB.hcan h0 ω₀
      : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n)))
      : PSU3Model n) * g'⁻¹ ∈ Submission.Blueprint.twoPoint B w := by
    have hc := (Work.PSU3.StageB.hcan h0 ω₀).2
    rw [Work.Models.mem_twoPoint_iff] at hc ⊢
    obtain ⟨hc1, hc2⟩ := hc
    refine ⟨?_, ?_⟩
    · have h2 : g' * ((Work.PSU3.StageB.hcan h0 ω₀
            : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
                (Submission.PSU3.psu3Weyl n))) : PSU3Model n) * g'⁻¹ ∈
          Submission.Blueprint.conj g' (Submission.PSU3.psu3B n) :=
        Subgroup.mem_map.mpr
          ⟨((Work.PSU3.StageB.hcan h0 ω₀
              : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
                  (Submission.PSU3.psu3Weyl n))) : PSU3Model n), hc1, by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      rwa [hg'B] at h2
    · have h2 : w⁻¹ * (g' * ((Work.PSU3.StageB.hcan h0 ω₀
            : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
                (Submission.PSU3.psu3Weyl n))) : PSU3Model n) * g'⁻¹) * w ∈
          Submission.Blueprint.conj g' (Submission.PSU3.psu3B n) := by
        refine Subgroup.mem_map.mpr
          ⟨(Submission.PSU3.psu3Weyl n)⁻¹
              * ((Work.PSU3.StageB.hcan h0 ω₀
                  : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
                      (Submission.PSU3.psu3Weyl n))) : PSU3Model n)
              * Submission.PSU3.psu3Weyl n, hc2, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show w = g' * Submission.PSU3.psu3Weyl n * g'⁻¹ from hg'w.symm]
        group
      rwa [hg'B] at h2
  obtain ⟨hgcan_eq, hhcan_eq, hfcan_eq⟩ := Work.PSU3.StageB.canon_unique'' h hωne
    (g := ⟨g' * ((Work.PSU3.StageB.gcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
      * g'⁻¹, hG₀U⟩)
    (d := ⟨g' * ((Work.PSU3.StageB.hcan h0 ω₀
      : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
          (Submission.PSU3.psu3Weyl n))) : PSU3Model n) * g'⁻¹, hD₀T⟩)
    (y := ⟨g' * ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
      * g'⁻¹, hY₀U⟩) heq
  have hf₀' : ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n)) : PSU3Model n)
      = ζ'⁻¹ * (ω₀ : PSU3Model n)⁻¹ * ζ' := hf₀
  have hh₀' : ((Work.PSU3.StageB.hcan h0 ω₀
      : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n)
          (Submission.PSU3.psu3Weyl n))) : PSU3Model n) = ζ' ^ 3 := hh₀
  have hζconj : ζ = g' * ζ' * g'⁻¹ := by rw [hζ'eq]; group
  have hfcan_val : g' * ((Work.PSU3.StageB.fcan h0 ω₀ : ↥(Submission.PSU3.psu3U n))
      : PSU3Model n) * g'⁻¹ = ζ⁻¹ * (ω : PSU3Model n)⁻¹ * ζ := by
    rw [hf₀', hζconj, hωcoe]
    group
  have hhcan_val : g' * ((Work.PSU3.StageB.hcan h0 ω₀
      : ↥(Submission.Blueprint.twoPoint (Submission.PSU3.psu3B n) (Submission.PSU3.psu3Weyl n)))
      : PSU3Model n) * g'⁻¹ = ζ ^ 3 := by
    rw [hh₀', hζconj]
    simp only [pow_three]
    group
  exact ⟨ω, hωω, by rw [← hfcan_eq]; exact hfcan_val, by rw [← hhcan_eq]; exact hhcan_val⟩

end Work.PSU3.StageB.NotFpfStep4
