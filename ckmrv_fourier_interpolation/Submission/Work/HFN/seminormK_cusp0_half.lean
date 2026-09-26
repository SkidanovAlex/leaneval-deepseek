/-
# The `r`-seminorm bound for the CKMRV transform on the cusp-`0` half-tile

Target: `Work.Asymptotics.seminormK_cusp0_half`, the uniform bound for the `r`-seminorms
`|r|^k ‖∂_r^l (s ↦ kernelTransform (Kfun ℓ d) w s) r‖` on the bounded cusp-`0` tile
`Tregion = {w ∈ 𝒟 : 1/2 ≤ Im(S·w) ≤ 2}` (defined in `seminormK_cusp0_defs.lean`).

## Structure

`Tregion = BLregion(1) ∪ BLregion(-1) ∪ arcT ∪ Kcomp`, where

* `BLregion(±1)` is the part of the tile within `1/10` of the two bad-line points `±1 + i`
  (`Work.Asymptotics.seminormK_cusp0_badline`, middle-range side);
* `arcT` is the part within `1/10` of the two tangency arcs `{|w ∓ 1/2| = 1/2}`
  (`Work.Asymptotics.seminormK_cusp0_arc_clean`, proved below);
* `Kcomp` is the complement, which is *compact and contained in* `𝒟`
  (`Work.Asymptotics.Kcomp_isCompact_subset`), so the compact part of CKMRV Proposition 4.6
  applies (`Work.Asymptotics.kernelTransform_seminorm_on_compact`).

The tile itself is *not* relatively compact in `𝒟`: its closure meets `∂𝒟` along the tangency
arcs and at `±1 + i`, and there a pole of `z ↦ Kfun ℓ d w z` grazes the contour `z = i(0,∞)`.
Those two grazing loci are exactly what the first two lemmas above handle; the *signed* contour
integral stays bounded even though `∫‖K‖` blows up like `log(1/δ)`.

## The workspace's import clash

The workspace contains two families of modules that cannot be imported into the same file:
`Work.Asymptotics.MiddleRange.Main` and `Work.Asymptotics.KPlusXiDefs` both declare
`Work.Asymptotics.continuous_jInvariantFun`.  The bad-line and compact bounds live on the
former side, so the tangency-arc bound is *reproved here on that side*, using the "clean"
replacements `arcT_classify`, `arcT_key_bound`, `arcT_branch_bound`, `arcT_smallT`,
`arcT_graze_vanish`, `arcT_jprime_dense`, `Graze.Vanishing` of the `KPlusXiDefs`-tainted
originals `arcT_flat`, `Graze.KeyBound`, `Graze.KfunClear_vanish_of_phiPair_uncond`,
`exists_jprime_ne_zero_near`.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.seminormK_cusp0_defs
import Submission.Work.Asymptotics.Kcomp_isCompact_subset
import Submission.Work.HFN.seminormK_cusp0_badline
import Submission.Work.HFN.kernelTransform_seminorm_on_compact
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.arcRegion
import Submission.Work.Asymptotics.arcT_classify
import Submission.Work.Asymptotics.arcT_classify_ge
import Submission.Work.Asymptotics.arcT_key_bound
import Submission.Work.Asymptotics.arcT_branch_bound
import Submission.Work.Asymptotics.arcT_smallT
import Submission.Work.HFN.arcT_tail
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.paperLayer_local_seminorm
import Submission.Work.Asymptotics.layerLow_local_seminorm
import Submission.Work.Asymptotics.layerTrunc_local_seminorm
import Submission.Work.Asymptotics.highPart_seminorm_scaled
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.Asymptotics.Compact.local_agreement
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.KaxisMid.LocalMiddle
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

set_option maxHeartbeats 3200000

open UpperHalfPlane ModularGroup ModularForm
open scoped MatrixGroups UpperHalfPlane Topology ContDiff

namespace Work.HFN
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

noncomputable section

/-! ## The tangency-arc region on the `MiddleRange`-compatible side -/

/-- `arcT` is bounded, since its closure is compact (`isCompact_closure_arcT'`). -/
lemma isBounded_arcT_clean : Bornology.IsBounded (arcT : Set ℍ) :=
  isCompact_closure_arcT'.isBounded.subset subset_closure

/-- **The kernel is bounded on the "middle range" `ε ≤ t ≤ 1` for `τ ∈ closure arcT`.**

This is the clean-side copy of `Work.Asymptotics.arcT_middle` (`arcT_flat.lean`), whose only
`KPlusXiDefs`-tainted inputs are `Graze.key_bound_arc` and `Graze.graze_vanish`, replaced here
by their clean copies `Graze.key_bound_arc'` and `Graze.graze_vanish'`; the orbit
classification and the geometric prerequisites come from `Work.Asymptotics.ArcClassify`. -/
lemma arcT_middle_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ closure arcT → ε ≤ t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  have hK : IsCompact (closure (arcT : Set ℍ)) := isCompact_closure_arcT'
  have hP : IsCompact (KaxisMid.Pspace (closure arcT) ε) := KaxisMid.isCompact_Pspace hK ε
  have hloc : ∀ p : KaxisMid.Pspace (closure arcT) ε, ∃ C : ℝ,
      0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ (q : KaxisMid.Pspace (closure arcT) ε),
        ‖((q.1).1 : ℂ) - ((p.1).1 : ℂ)‖ < r → |(q.1).2 - (p.1).2| < r →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ C := by
    intro p
    obtain ⟨hpK, hpε, hp1⟩ := KaxisMid.mem_Pspace.mp p.2
    by_cases hcoin : Work.Kernels.jInvariantFun (p.1).1
        = Work.Kernels.jInvariantFun (KaxisMid.pz hε (p.1) p.2)
    · -- a coincidence
      have hpt : 0 < (p.1).2 := lt_of_lt_of_le hε hpε
      have hpzeq : KaxisMid.pz hε (p.1) p.2 = Work.Kernels.imagAxis (p.1).2 hpt :=
        UpperHalfPlane.ext rfl
      obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq hcoin
      have hτcl : γ • Work.Kernels.imagAxis (p.1).2 hpt ∈ closure arcT := by
        rw [← hpzeq, hγ]; exact hpK
      have hgraze := ArcClassify.arcT_orbit_classification γ (p.1).2 hpt hp1 hτcl
      obtain ⟨δ, hδg, hδact⟩ := isGrazeElem_exists' γ hgraze
      have hδp : δ • (KaxisMid.pz hε (p.1) p.2) = (p.1).1 := by
        rw [hδact, hγ]
      by_cases ht1 : (p.1).2 = 1
      · -- `t = 1`: the point is a tangency point of `𝒟`
        have hI : δ • UpperHalfPlane.I = (p.1).1 := by
          rw [← hδp]
          congr 1
          apply UpperHalfPlane.ext
          rw [KaxisMid.pz_coe, ht1, UpperHalfPlane.coe_I]
          norm_num
        have hpp : KaxisMid.pz hε (p.1) p.2 = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext
          rw [KaxisMid.pz_coe, ht1, UpperHalfPlane.coe_I]
          norm_num
        rcases graze_I_eq' δ hδg with hδR | hδL
        · obtain ⟨ρ, C', hρ, hC', hkey⟩ := Graze.key_bound_arc' ℓ d hd
            (ModularGroup.T * ModularGroup.S * ModularGroup.T) (Or.inl rfl)
          refine ⟨max C' 1, lt_of_lt_of_le one_pos (le_max_right C' 1), ρ, hρ, ?_⟩
          intro q hq1 hq2
          rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
          refine le_trans (hkey (q.1).1 (KaxisMid.pz hε (q.1) q.2) ?_ ?_) (le_max_left C' 1)
          · have hA : ((ModularGroup.T * ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I : ℍ)
                = (p.1).1 := by
              rw [← hI, hδR]
              rfl
            rw [hA]; exact hq1
          · rw [← UpperHalfPlane.coe_I, ← hpp, KaxisMid.norm_pz_sub hε q.2 p.2]
            exact hq2
        · obtain ⟨ρ, C', hρ, hC', hkey⟩ := Graze.key_bound_arc' ℓ d hd
            (ModularGroup.S * ModularGroup.T) (Or.inr rfl)
          refine ⟨max C' 1, lt_of_lt_of_le one_pos (le_max_right C' 1), ρ, hρ, ?_⟩
          intro q hq1 hq2
          rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
          refine le_trans (hkey (q.1).1 (KaxisMid.pz hε (q.1) q.2) ?_ ?_) (le_max_left C' 1)
          · have hA : ((ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I : ℍ) = (p.1).1 := by
              rw [← hI, hδL]
              rfl
            rw [hA]; exact hq1
          · rw [← UpperHalfPlane.coe_I, ← hpp, KaxisMid.norm_pz_sub hε q.2 p.2]
            exact hq2
      · -- `t ≠ 1`: the pole on the branch is removable
        obtain ⟨C', hC', r, hr, H⟩ := KaxisMid.exists_local_bound_branch_aux ℓ d hd hK hε (p.1) p.2 ht1
          (Z := fun τ : ℍ => δ⁻¹ • τ)
          (by rw [← hδp, ← mul_smul, inv_mul_cancel, one_smul])
          (by intro τ
              have h := Graze.graze_vanish' ℓ d hd δ hδg (δ⁻¹ • τ)
              rwa [← mul_smul, mul_inv_cancel, one_smul] at h)
          (by intro τ; exact jInvariantFun_smul_of_slash δ⁻¹ τ)
          (by
            obtain ⟨δZ, cZ, hδZ, hcZ, hb⟩ := exists_lipschitz_smul' δ⁻¹ (p.1).1
            exact ⟨δZ, cZ, hδZ, hcZ, hb⟩)
        refine ⟨C', hC', r, hr, ?_⟩
        intro q hq1 hq2
        rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
        exact H q.1 q.2 hq1 hq2
    · -- no coincidence
      obtain ⟨C, hC, r, hr, H⟩ := KaxisMid.exists_local_bound_clean ℓ d hd hK hε (p.1) p.2
        (fun h => hcoin h)
      refine ⟨C, hC, r, hr, ?_⟩
      intro q hq1 hq2
      rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
      refine H (q.1) q.2 hq1 ?_
      rw [KaxisMid.norm_pz_sub hε q.2 p.2]
      exact hq2
  classical
  let Cf : KaxisMid.Pspace (closure arcT) ε → ℝ := fun p => Classical.choose (hloc p)
  have hCfpos : ∀ p, 0 < Cf p := fun p => (Classical.choose_spec (hloc p)).1
  let rf : KaxisMid.Pspace (closure arcT) ε → ℝ :=
    fun p => Classical.choose (Classical.choose_spec (hloc p)).2
  have hrfpos : ∀ p, 0 < rf p :=
    fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).1
  have hbound : ∀ (p q : KaxisMid.Pspace (closure arcT) ε),
      ‖((q.1).1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p → |(q.1).2 - (p.1).2| < rf p →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ Cf p :=
    fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).2
  have hopen : ∀ p : KaxisMid.Pspace (closure arcT) ε, IsOpen {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p} := by
    intro p
    have h1 : IsOpen {q : ℍ × ℝ | ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p} :=
      isOpen_lt (Continuous.norm ((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
        continuous_const)) continuous_const
    have h2 : IsOpen {q : ℍ × ℝ | |q.2 - (p.1).2| < rf p} :=
      isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const
    exact h1.inter h2
  have hcover : KaxisMid.Pspace (closure arcT) ε ⊆ ⋃ p : KaxisMid.Pspace (closure arcT) ε,
      {q : ℍ × ℝ | ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p} := by
    intro q hq
    refine Set.mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩
    exact ⟨by simpa using hrfpos ⟨q, hq⟩, by simpa using hrfpos ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hP.elim_finite_subcover
    (fun p : KaxisMid.Pspace (closure arcT) ε => {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p})
    hopen hcover
  have hsum : (0:ℝ) < (∑ p ∈ s, Cf p) + 1 := by
    have := Finset.sum_nonneg (s := s) (f := Cf) (fun p _ => (hCfpos p).le)
    linarith
  refine ⟨(∑ p ∈ s, Cf p) + 1, hsum, fun τ t hτT hεt ht1 => ?_⟩
  have hq : (τ, t) ∈ KaxisMid.Pspace (closure arcT) ε := ⟨hτT, hεt, ht1⟩
  have hmem := hs hq
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨p, hps, hpU⟩ := hmem
  have hle := hbound p ⟨(τ, t), hq⟩ hpU.1 hpU.2
  refine le_trans hle ?_
  have := Finset.single_le_sum (s := s) (f := Cf) (fun x _ => (hCfpos x).le) hps
  linarith

/-- **Flatness of the kernel on the tangency-arc region.**  Clean-side copy of
`Work.Asymptotics.arcT_flat`. -/
lemma arcT_flat_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.arcT → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N := by
  intro N hN
  obtain ⟨δ, hδ, hcusp⟩ := HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd isBounded_arcT_clean
  obtain ⟨c1, hc1, hcusp'⟩ := hcusp N hN
  have hε : 0 < min δ (1/2) := lt_min hδ (by norm_num)
  obtain ⟨C, hC, hmid⟩ := arcT_middle_clean ℓ d hd hε
  refine ⟨max c1 (C * (min δ (1/2)) ^ (-N)), ?_, fun τ t hτ ht ht1 => ?_⟩
  · exact lt_of_lt_of_le hc1 (le_max_left _ _)
  · by_cases hlt : t ≤ min δ (1/2)
    · refine le_trans (hcusp' τ t hτ ht (le_trans hlt (min_le_left _ _))) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le N)
    · rw [not_le] at hlt
      have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C :=
        hmid τ t (subset_closure hτ) (le_of_lt hlt) ht1
      have h2 : (min δ (1/2)) ^ N ≤ t ^ N := Real.rpow_le_rpow hε.le (le_of_lt hlt) hN
      have h3 : C ≤ C * (min δ (1/2)) ^ (-N) * t ^ N := by
        have h4 : C * (min δ (1/2)) ^ (-N) * (min δ (1/2)) ^ N
            ≤ C * (min δ (1/2)) ^ (-N) * t ^ N :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC.le (Real.rpow_nonneg hε.le _))
        have h5 : C * (min δ (1/2)) ^ (-N) * (min δ (1/2)) ^ N = C := by
          rw [mul_assoc, ← Real.rpow_add hε, neg_add_cancel, Real.rpow_zero, mul_one]
        linarith [h4, h5.le, h5.ge]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := h1
        _ ≤ C * (min δ (1/2)) ^ (-N) * t ^ N := h3
        _ ≤ max c1 (C * (min δ (1/2)) ^ (-N)) * t ^ N :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le N)

/-! ## The layer seminorms on `arcT` -/

/-- **The `r`-seminorm bound for the paper layer `paperLayer G ℓ d τ ·` on `arcT`.**

Clean-side copy of `Work.Asymptotics.arcT_paperLayer_seminorm`: the neutral originals
`layerLow_local_seminorm`, `layerTrunc_local_seminorm`, `highPart_seminorm_scaled`,
`layerPieces_contDiff_of_mem` and `punctured_iteratedDeriv` are used instead of the
(import-incompatible) `paperLayer_local_seminorm`. -/
lemma arcT_paperLayer_seminorm_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn DomainD (G i j))
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpoly : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ arcT →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => paperLayer G ℓ d τ s) r‖
        ≤ c := by
  intro k l
  obtain ⟨c1, hc1, h1⟩ := layerLow_local_seminorm ℓ d hd (K := arcT) hflat k l
  obtain ⟨c2, hc2, h2⟩ := layerTrunc_local_seminorm ℓ d hd G (K := arcT) hpoly k l
  obtain ⟨c3, N3, hc3, h3⟩ := highPart_seminorm_scaled G hG k l
  have h3' : ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ arcT →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
        ≤ c3 * max (14 ^ N3) 1 := by
    intro τ r hτ
    have hb := h3 τ r (arcT_subset_DomainD hτ)
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsB : Work.Kernels.scale τ ≤ 14 := arcT_scale_le hτ
    have hN : (Work.Kernels.scale τ) ^ N3 ≤ max (14 ^ N3) 1 := by
      rcases le_or_gt 0 N3 with h | h
      · exact le_trans (Real.rpow_le_rpow (le_trans zero_le_one hs1) hsB h) (le_max_left _ _)
      · have h2'' : (Work.Kernels.scale τ) ^ N3 ≤ (1 : ℝ) ^ N3 :=
          Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1) hs1 (le_of_lt h)
        rw [Real.one_rpow] at h2''
        exact h2''.trans (le_max_right _ _)
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
        ≤ c3 * (Work.Kernels.scale τ) ^ N3 := hb
      _ ≤ c3 * max (14 ^ N3) 1 := mul_le_mul_of_nonneg_left hN hc3
  refine ⟨c1 + c2 + c3 * max (14 ^ N3) 1, by positivity, fun τ r hτ => ?_⟩
  obtain ⟨hcdL, hcdT, hcdH⟩ := layerPieces_contDiff_of_mem ℓ d hd G (K := arcT) hflat hpoly τ hτ
  have hsplitL : iteratedDeriv l
        (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r :=
    iteratedDeriv_add (f := fun s : ℝ => layerLow ℓ d τ s)
      (g := fun s : ℝ => layerTrunc G ℓ d τ s)
      ((hcdL.contDiffAt).of_le le_top) ((hcdT.contDiffAt).of_le le_top)
  have hsplit : iteratedDeriv l (fun s : ℝ => paperLayer G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r := by
    have hfun : (fun s : ℝ => paperLayer G ℓ d τ s)
        = fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s + highPart G τ s := by
      funext s; rw [paperLayer]
    have hE : (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s + highPart G τ s)
        = (fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s)
          + (fun s : ℝ => highPart G τ s) := rfl
    rw [hfun, hE, iteratedDeriv_add
      (f := fun s : ℝ => layerLow ℓ d τ s + layerTrunc G ℓ d τ s)
      (g := fun s : ℝ => highPart G τ s)
      (((hcdL.add hcdT).contDiffAt).of_le le_top) ((hcdH.contDiffAt).of_le le_top), hsplitL]
  rw [hsplit]
  have ha := h1 τ r hτ
  have hb := h2 τ r hτ
  have hc := h3' τ r hτ
  have htri : ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
      ≤ ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖ := by
    linarith [norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r),
      norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => highPart G τ s) r)]
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d τ s) r‖
        + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerTrunc G ℓ d τ s) r‖
        + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart G τ s) r‖ := by ring
    _ ≤ c1 + c2 + c3 * max (14 ^ N3) 1 := by linarith

/-- **The `r`-seminorm bound for the punctured layer `layer G ℓ d τ ·` on `arcT`.**

Clean-side copy of `Work.Asymptotics.arcT_layer_seminorm`; the evenness and smoothness inputs
are `paperLayer_neg` and `paperLayer_contDiff_of_mem` from
`Submission/Work/Asymptotics/kernelTransform_seminorm_on_compact.lean`. -/
lemma arcT_layer_seminorm_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn DomainD (G i j))
    (hflat : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpoly : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ arcT → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ arcT →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layer G ℓ d τ s) r‖
        ≤ c := by
  intro k l
  obtain ⟨c, hc, hb⟩ := arcT_paperLayer_seminorm_clean ℓ d hd G hG hflat hpoly k l
  refine ⟨c, hc, ?_⟩
  intro τ r hτ
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        have hz : layer G ℓ d τ 0 = 0 := by rw [layer]; simp
        simp only [iteratedDeriv_zero, hz, norm_zero, mul_zero]
        exact hc
      · have hfun : (fun s : ℝ => layer G ℓ d τ s)
            = fun s : ℝ => (if s = 0 then 0 else paperLayer G ℓ d τ s) := by
          funext s; rw [layer]
        rw [hfun, punctured_iteratedDeriv (paperLayer_neg G ℓ d τ)
          ((paperLayer_contDiff_of_mem ℓ d hd G hflat hpoly τ hτ).differentiable (by simp))
          l hl]
        simpa using hb τ 0 hτ
    · have hz : (0 : ℝ) ^ k = 0 := zero_pow hk.ne'
      simp only [abs_zero, hz, zero_mul]
      exact hc
  · have heq : (fun s : ℝ => layer G ℓ d τ s)
        =ᶠ[𝓝 r] (fun s : ℝ => paperLayer G ℓ d τ s) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs
      rw [layer, if_neg hs]
    rw [iteratedDeriv_congr_of_eventuallyEq heq l]
    exact hb τ r hτ

/-- **The tangency-arc seminorm bound** (clean-side copy of
`Work.Asymptotics.seminormK_cusp0_arc`). -/
theorem seminormK_cusp0_arc_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im → (ModularGroup.S • w).im ≤ 2 →
        (‖(w : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10 ∨
          ‖(w : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10) →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖ ≤ C := by
  intro k l
  set G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ := Gcusp ℓ d with hGdef
  have hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn DomainD (G i j) :=
    fun i j => GcuspInP (ℓ := ℓ) d i j
  have h8 : d = 8 → ∀ j : Fin 2, G 1 j = 0 := by
    intro h8d j
    rw [hGdef, Gcusp, if_pos h8d]
    funext τ
    fin_cases j <;> simp [Gcusp8]
  have hflat := arcT_flat_clean ℓ d hd
  have hpoly := arcT_tail ℓ d hd
  have hlayer := arcT_layer_seminorm_clean ℓ d hd G hG hflat hpoly
  have h0 : ∀ τ : UpperHalfPlane, τ ∈ arcT →
      layer G ℓ d τ 0 = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0 := by
    intro τ _
    have h1 : layer G ℓ d τ 0 = 0 := by rw [layer]; simp
    have h2 : Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ 0 = 0 := by
      simp [Work.Kernels.kernelTransform]
    rw [h1, h2]
  have hagr : ∀ τ : UpperHalfPlane, τ ∈ arcT → ∀ r : ℝ, r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
        layer G ℓ d τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
    intro τ hτ r hr hInt
    rw [layer, if_neg hr]
    exact Work.Asymptotics.Compact.local_agreement ℓ d hd G hG h8 hflat hpoly τ r hτ hr hInt
  obtain ⟨C, hC, hbound⟩ :=
    kernelTransform_seminorm_of_layer_on_compact ℓ d (fun τ r => layer G ℓ d τ r) h0 hagr hlayer k l
  exact ⟨C, hC, fun w r hw h1 h2 h3 => hbound w r ⟨hw, h1, h2, h3⟩⟩

/-! ## The compact piece and the assembly -/

/-- **The compact part of CKMRV Proposition 4.6 on `Kcomp`.** -/
theorem Kcomp_seminorm_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Kcomp →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖ ≤ C := by
  obtain ⟨hKc, hKs⟩ := Kcomp_isCompact_subset
  exact kernelTransform_seminorm_on_compact ℓ d hd hKc hKs

/-- **CKMRV Proposition 4.6 on the cusp-`0` half tile** (the requested lemma). -/
theorem seminormK_cusp0_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ Work.Asymptotics.DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im → (ModularGroup.S • w).im ≤ 2 →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖ ≤ C := by
  intro k l
  obtain ⟨C₁, hC₁, h₁⟩ := Kcomp_seminorm_bound ℓ d hd k l
  obtain ⟨C₂, hC₂, h₂⟩ := seminormK_cusp0_badline ℓ d hd k l
  obtain ⟨C₃, hC₃, h₃⟩ := seminormK_cusp0_arc_clean ℓ d hd k l
  refine ⟨max C₁ (max C₂ C₃), le_trans hC₁ (le_max_left C₁ (max C₂ C₃)), ?_⟩
  have hC₂' : C₂ ≤ max C₁ (max C₂ C₃) :=
    le_trans (le_max_left C₂ C₃) (le_max_right C₁ (max C₂ C₃))
  have hC₃' : C₃ ≤ max C₁ (max C₂ C₃) :=
    le_trans (le_max_right C₂ C₃) (le_max_right C₁ (max C₂ C₃))
  have hC₁' : C₁ ≤ max C₁ (max C₂ C₃) := le_max_left C₁ (max C₂ C₃)
  intro w r hw hlo hhi
  by_cases hbad : ‖(w : ℂ) - ((1 : ℂ) + Complex.I)‖ < 1 / 10 ∨
      ‖(w : ℂ) - ((-1 : ℂ) + Complex.I)‖ < 1 / 10
  · exact le_trans (h₂ w r hw hlo hhi hbad) hC₂'
  · by_cases harc : ‖(w : ℂ) - (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10 ∨
        ‖(w : ℂ) + (1 / 2 : ℂ)‖ < 1 / 2 + 1 / 10
    · exact le_trans (h₃ w r hw hlo hhi harc) hC₃'
    · have hbad' := not_or.mp hbad
      have harc' := not_or.mp harc
      have hwK : w ∈ Kcomp := subset_closure ⟨⟨hw, hlo, hhi⟩,
        not_lt.mp hbad'.1, not_lt.mp hbad'.2, not_lt.mp harc'.1, not_lt.mp harc'.2⟩
      exact le_trans (h₁ w r hwK) hC₁'

end

end Work.HFN
