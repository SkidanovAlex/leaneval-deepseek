import ChallengeDeps
import Submission.Work.BoseB7AK.K15R.hatChiSq_double_sum_nonneg
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseB7AK.W1rows.W1hat_even_contDiff
import Submission.Work.BoseGateFS.AbsoluteK0
import Submission.Work.BoseGateFS.KinkInputHonest
import Submission.Work.BoseGateFS.LabAdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.KinkFSHonest` — the corrected bundle at the honest model

This module **inhabits** `KinkFS` (`Defs.lean` §3bis) at the honest box model
`HonestModes`/`tildeDataHon`/`KzEnvHon`, i.e. it produces the input port of the
gate from rows that are *true* at the honest data.  Nothing here mentions
`Work.BoseK15.K15Input`, whose F1-unsatisfiable rows (`kmom_add`, `hasKernel`
with the `P_H`-only guard, `fL_supp` with radius `K_L√(μa)`) are the reason the
bundle was rebuilt.

Rows *proved* here (they are the honest model's own geometry):

* `W1_le`, `W1_even` — from the `Ŵ₁` rows of the potential (`Cw`), the UV cut
  `ζ_{Λ_N}` (`0 ≤ ζ ≤ 1`) and `a ≥ 0`;
* `kmom_neg`, `hatChi_eq`, `hatChiSq_eq`, and from them `|χ̂| ≤ 1`, `|χ̂²| ≤ 1`
  and their evenness — the χ-pins (`ChiPin.chat_chiFun_eq`, `honE_hatChi`,
  `honE_hatChiSq`) together with the normalisation `∫χ_ℓ² = ℓ³`;
* `fL_nonneg`, `fL_le_one`, `fL_even`, `fL_supp2` — the `LowCut` profile
  (`f = 1` on `(-∞,1]`, `f = 0` on `[2,∞)`), so FS's own support radius
  `2K_L√(μa)` (finding F7);
* `kmom_subW`, `kmom_subL`, `hasKernelW` — the guarded label arithmetic and the
  commutator identity, from `LabAdd.kmomLab_sub_of_norm_le`: the `f_L` support
  (`‖s‖ ≤ 2K_L√(μa)`) and the *UV cut* (`W1 k ≠ 0 → ‖k‖ ≤ 2Λ_N`) confine the
  labels strictly inside the lattice range (finding F1), and the box-model
  equation `ChiPin.hon_box` gives the kernel;
* `hatChiSq_form_psd` — the corpus's Bochner/Schur nonnegativity
  (`Work.BoseB7AK.K15R.hatChiSq_double_sum_nonneg`).

Rows taken as *hypotheses* (they are FS's analysis, §11/§12 `eq:1Q-integral`
and `eq:defW_12`): the `Ŵ₁` bound `hW1abs`, its evenness `hW1even`, and the two
`Ŵ₁ω(0)` rows `hW1om0nn`/`hW1om0le`; plus `FSParamsView` (the scalars) and the
cube-size condition `4K_L√(μa) ≤ Λ_N` (the design's §2.3 requirement, which
`uvRad` is *defined* to meet for large `N`).
-/

noncomputable section

open scoped BigOperators Pointwise Real

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut} {HM : ∀ μ : ℝ, HonestModes v μ}
variable {μ : ℝ}

/-! ## 0. The honest setup -/

/-- The hypotheses under which the corrected bundle is inhabited at the honest
model: FS's parameters (`FSParamsView`), the diluteness `μ > 0`, `a > 0`, and the
cube-size condition `4K_L√(μa) ≤ Λ_N` of the design §2.3 (which `uvRad ℓ N` is
defined to satisfy for large `N`). -/
structure HonSetup (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v) (fc fu : LowCut)
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) where
  /-- FS's scattering length is positive. -/
  hav : 0 < a v
  /-- the chemical potential is positive. -/
  hμ : 0 < μ
  /-- FS's scalars satisfy their parameter conditions. -/
  hv : FSParamsView (honE v h fc fu HM μ)
  /-- the cube is big enough for the UV cut to dominate the `f_L` support. -/
  h4κ : 4 * ((honE v h fc fu HM μ).KL
      * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
    ≤ uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N

/-! ## 1. The honest environment, unfolded -/

section Env

/-- The honest box side is `sideAt μ (a v)`. -/
theorem ellH_eq_sideAt (S : HonSetup v h fc fu HM μ) :
    Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (a v) := by
  rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos S.hμ S.hav)]

/-- The honest environment's `ℓ` is `ellH v μ`. -/
lemma honE_ell (S : HonSetup v h fc fu HM μ) :
    (honE v h fc fu HM μ).ell = Work.BoseBoxFock.ellH v μ := by
  rw [ellH_eq_sideAt S]
  rfl

/-- The honest Fock data's momentum map is `kmomLab`. -/
lemma honF_kmom (k : Lab (HM μ).N) :
    (honF v h fc fu HM μ).kmom k
      = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k := by
  simp only [honF, Work.BoseBoxFock.HonestBoxFam, Work.BoseB4.boxFockData,
    Work.BoseB4.b7FockDataBox]

/-- The honest environment's `aScat` is `a v`. -/
lemma honE_aScat : (honE v h fc fu HM μ).aScat = a v := rfl

/-- The honest `Ŵ₁` at a mode. -/
lemma honE_W1_apply (S : HonSetup v h fc fu HM μ) (k : Lab (HM μ).N) :
    (honE v h fc fu HM μ).W1 k = uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
      ((honF v h fc fu HM μ).kmom k)
      * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
          ((honF v h fc fu HM μ).kmom k) := by
  rw [ellH_eq_sideAt S]
  rfl

end Env

/-! ## 2. The `f_L` profile rows (`LowCut`, finding F7) -/

section FL

/-- `κ = K_L√(μa) > 0` at admissible parameters. -/
theorem kappa_pos (S : HonSetup v h fc fu HM μ) :
    0 < (honE v h fc fu HM μ).KL
      * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat) :=
  mul_pos (lt_of_lt_of_le one_pos S.hv.one_le_KL)
    (Real.sqrt_pos.mpr
      (mul_pos (Work.BoseB7.mu_pos (honE v h fc fu HM μ) S.hv) S.hv.a_pos))

/-- The honest `f_L` is the `LowCut` profile. -/
lemma honE_fL_apply (k : Lab (HM μ).N) :
    (honE v h fc fu HM μ).fL k
      = fc.f (‖(honF v h fc fu HM μ).kmom k‖
          / ((honE v h fc fu HM μ).KL
              * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))) :=
  rfl

/-- **FS's support** (F7): `f_L` vanishes off `2K_L√(μa)`. -/
theorem honE_fL_supp2 (S : HonSetup v h fc fu HM μ) (k : Lab (HM μ).N)
    (hk : (honE v h fc fu HM μ).fL k ≠ 0) :
    ‖(honF v h fc fu HM μ).kmom k‖
      ≤ 2 * ((honE v h fc fu HM μ).KL
          * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)) := by
  have hκpos := kappa_pos S
  rw [show (honE v h fc fu HM μ).fL k
      = fc.f (‖(honF v h fc fu HM μ).kmom k‖
          / ((honE v h fc fu HM μ).KL
              * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
      from rfl] at hk
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ≤ ‖(honF v h fc fu HM μ).kmom k‖
      / ((honE v h fc fu HM μ).KL
          * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)) := by
    rw [le_div_iff₀ hκpos]; linarith
  exact hk (fc.zero _ h2)

end FL

/-! ## 3. The label arithmetic and the kernel (`LabAdd`, finding F1) -/

section Labels

/-- The UV cut is positive at the honest model. -/
theorem uvRad_pos (S : HonSetup v h fc fu HM μ) :
    0 < uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := by
  set κ := (honE v h fc fu HM μ).KL
    * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat) with hκ
  have hκpos : 0 < κ := kappa_pos S
  have h4 : 4 * κ ≤ uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := S.h4κ
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  rw [uvRad] at h4 ⊢
  nlinarith [h4, hκpos, hℓ, Real.pi_pos]

/-- The cube is nontrivial. -/
theorem one_le_N (S : HonSetup v h fc fu HM μ) : 1 ≤ (HM μ).N := by
  set κ := (honE v h fc fu HM μ).KL
    * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat) with hκ
  have hκpos : 0 < κ := kappa_pos S
  have h4 : 4 * κ ≤ uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := S.h4κ
  by_contra hcon
  push_neg at hcon
  have hN0 : (HM μ).N = 0 := Nat.lt_one_iff.mp hcon
  rw [uvRad, hN0] at h4
  simp only [Nat.cast_zero, mul_zero, div_zero, zero_div] at h4
  linarith

/-- `supp W1` is inside the cut ball: the guard of the repaired label row. -/
theorem honE_W1_supp (S : HonSetup v h fc fu HM μ) {k : Lab (HM μ).N}
    (hk : (honE v h fc fu HM μ).W1 k ≠ 0) :
    ‖(honF v h fc fu HM μ).kmom k‖ ≤ 2 * uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := by
  rw [show (honE v h fc fu HM μ).W1 k
      = uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
          ((honF v h fc fu HM μ).kmom k)
        * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
            ((honF v h fc fu HM μ).kmom k) from honE_W1_apply S k, mul_ne_zero_iff] at hk
  have hΛ : 0 < uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := uvRad_pos S
  have hζ : fu.f (‖(honF v h fc fu HM μ).kmom k‖
      / uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N) ≠ 0 := hk.1
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ≤ ‖(honF v h fc fu HM μ).kmom k‖
      / uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := by
    rw [le_div_iff₀ hΛ]; linarith
  exact hζ (fu.zero _ h2)

/-- The cube-size condition in the form `LabAdd` consumes,
`ℓ(2K_L√(μa) + 2Λ_N)/(2π) ≤ N`. -/
theorem lab_XY (S : HonSetup v h fc fu HM μ) :
    Work.BoseBoxFock.ellH v μ * (2 * ((honE v h fc fu HM μ).KL
        * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
      + 2 * uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N) / (2 * π)
    ≤ ((HM μ).N : ℝ) := by
  set κ := (honE v h fc fu HM μ).KL
    * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat) with hκ
  set L := Work.BoseBoxFock.ellH v μ with hL
  have hκpos : 0 < κ := kappa_pos S
  have h4 : 4 * κ ≤ uvRad L (HM μ).N := S.h4κ
  have hℓ : 0 < L := Work.BoseBoxFock.ellH_pos v μ
  have hπ : 0 < π := Real.pi_pos
  rw [uvRad] at h4 ⊢
  have hexp : L * (2 * κ + 2 * (2 * π / L * ((HM μ).N : ℝ) / 4)) / (2 * π)
      = L * κ / π + ((HM μ).N : ℝ) / 2 := by
    field_simp
    ring
  rw [hexp]
  have hkey : L * κ / π ≤ ((HM μ).N : ℝ) / 2 := by
    have hπN : 0 < π * ((HM μ).N : ℝ) := by
      have hNpos : (0 : ℝ) < ((HM μ).N : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_N S)
      exact mul_pos hπ hNpos
    have h8 : 8 * (L * κ) ≤ π * ((HM μ).N : ℝ) := by
      have hL4 : 0 < 4 * L := by linarith
      have heq : 2 * π * ((HM μ).N : ℝ) / (4 * L) = 2 * π / L * ((HM μ).N : ℝ) / 4 := by
        field_simp
      have hmain : 4 * κ ≤ 2 * π * ((HM μ).N : ℝ) / (4 * L) := by
        rw [heq]; exact h4
      have hclear : 4 * κ * (4 * L) ≤ 2 * π * ((HM μ).N : ℝ) :=
        (le_div_iff₀ hL4).mp hmain
      linarith
    rw [div_le_iff₀ hπ]
    linarith
  have hN0 : (0 : ℝ) ≤ ((HM μ).N : ℝ) := Nat.cast_nonneg _
  linarith

/-- **The guarded label arithmetic** (finding F1) at the honest model. -/
theorem honE_kmom_subW (S : HonSetup v h fc fu HM μ) (s k : Lab (HM μ).N)
    (hs : (honE v h fc fu HM μ).fL s ≠ 0)
    (hk : k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ))
    (hW : (honE v h fc fu HM μ).W1 k ≠ 0) :
    (honF v h fc fu HM μ).kmom (s - k)
      = (honF v h fc fu HM μ).kmom s - (honF v h fc fu HM μ).kmom k := by
  rw [honF_kmom,
    honF_kmom,
    honF_kmom]
  exact kmomLab_sub_of_norm_le (Work.BoseBoxFock.ellH v μ)
    (Work.BoseBoxFock.ellH_pos v μ) (HM μ).N (one_le_N S) s k _ _
    (honE_fL_supp2 S s hs) (honE_W1_supp S hW) (lab_XY S)

/-- The inner additivity: both labels are localised. -/
theorem honE_kmom_subL (S : HonSetup v h fc fu HM μ) (s s' : Lab (HM μ).N)
    (hs : (honE v h fc fu HM μ).fL s ≠ 0)
    (hs' : (honE v h fc fu HM μ).fL s' ≠ 0) :
    (honF v h fc fu HM μ).kmom (s - s')
      = (honF v h fc fu HM μ).kmom s - (honF v h fc fu HM μ).kmom s' := by
  have hκ : 0 < (honE v h fc fu HM μ).KL
      * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat) := kappa_pos S
  have hκΛ : (honE v h fc fu HM μ).KL
      * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)
      ≤ uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N := by
    have h := S.h4κ
    rw [uvRad] at h ⊢
    nlinarith [h, hκ, Real.pi_pos, Work.BoseBoxFock.ellH_pos v μ]
  have hXY : Work.BoseBoxFock.ellH v μ * (2 * ((honE v h fc fu HM μ).KL
        * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
      + 2 * ((honE v h fc fu HM μ).KL
          * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
      / (2 * π) ≤ ((HM μ).N : ℝ) := by
    refine le_trans ?_ (lab_XY S)
    have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
    have h2π : 0 < 2 * π := by positivity
    refine div_le_div_of_nonneg_right ?_ h2π.le
    refine mul_le_mul_of_nonneg_left ?_ hℓ.le
    linarith
  rw [honF_kmom,
    honF_kmom,
    honF_kmom]
  exact kmomLab_sub_of_norm_le (Work.BoseBoxFock.ellH v μ)
    (Work.BoseBoxFock.ellH_pos v μ) (HM μ).N (one_le_N S) s s' _ _
    (honE_fL_supp2 S s hs) (honE_fL_supp2 S s' hs') hXY

/-- **The kernel identity on the F1-guarded pairs**, from the box-model equation. -/
theorem honE_hasKernelW (S : HonSetup v h fc fu HM μ) (i j : Lab (HM μ).N)
    (hi : (honE v h fc fu HM μ).fL i ≠ 0)
    (hj : j ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ))
    (hW : (honE v h fc fu HM μ).W1 j ≠ 0) :
    (honF v h fc fu HM μ).ccrK i j
      = (honE v h fc fu HM μ).hatChiSq (i - j)
        - (honE v h fc fu HM μ).hatChi i * (honE v h fc fu HM μ).hatChi j := by
  refine Work.BoseK15.hasKernel_of_noWrap (honF v h fc fu HM μ).kmom
    (fun a b => hon_box HM μ S.hμ S.hav a b)
    (honE_hatChiSq S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N)
    (honE_hatChi S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N) ?_
  show (honF v h fc fu HM μ).kmom (i - j)
    = (honF v h fc fu HM μ).kmom i - (honF v h fc fu HM μ).kmom j
  exact honE_kmom_subW S i j hi hj hW

end Labels

/-! ## 4. The `χ̂²`-form (`Bochner + Schur`) -/

section Psd

/-- **The PSD half of the χ̂²-form** at the honest model. -/
theorem honE_hatChiSq_form_psd (S : HonSetup v h fc fu HM μ)
    (Ss : Finset (Lab (HM μ).N)) (c : Lab (HM μ).N → ℝ)
    (w : Lab (HM μ).N → (honF v h fc fu HM μ).H)
    (hguard : ∀ s ∈ Ss, c s ≠ 0 → (honE v h fc fu HM μ).fL s ≠ 0) :
    0 ≤ ∑ s ∈ Ss, ∑ s' ∈ Ss, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
      * (honF v h fc fu HM μ).bp (w s') (w s) := by
  classical
  set T : Finset (Lab (HM μ).N) := Ss.filter (fun s => c s ≠ 0) with hT
  have hTsub : T ⊆ Ss := Finset.filter_subset _ _
  have hmem : ∀ s ∈ T, c s ≠ 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hfL : ∀ s ∈ T, (honE v h fc fu HM μ).fL s ≠ 0 :=
    fun s hs => hguard s (hTsub hs) (hmem s hs)
  have houter : (∑ s ∈ Ss, ∑ s' ∈ Ss, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s))
      = ∑ s ∈ T, ∑ s' ∈ Ss, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s) := by
    refine (Finset.sum_subset hTsub ?_).symm
    intro s hsS hsT
    have hc : c s = 0 := by
      by_contra hc
      exact hsT (Finset.mem_filter.mpr ⟨hsS, hc⟩)
    simp [hc]
  have hinner : ∀ s ∈ T, (∑ s' ∈ Ss, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s))
      = ∑ s' ∈ T, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s) := by
    intro s _
    refine (Finset.sum_subset hTsub ?_).symm
    intro s' hs'S hs'T
    have hc : c s' = 0 := by
      by_contra hc
      exact hs'T (Finset.mem_filter.mpr ⟨hs'S, hc⟩)
    simp [hc]
  have hrewrite : (∑ s ∈ T, ∑ s' ∈ Ss, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s))
      = ∑ s ∈ T, ∑ s' ∈ T,
          c s * c s' * Work.BoseK15.corpusBox.hatChiSq
            ((Work.BoseBoxFock.ellH v μ • (honF v h fc fu HM μ).kmom s')
              - (Work.BoseBoxFock.ellH v μ • (honF v h fc fu HM μ).kmom s))
          * (honF v h fc fu HM μ).bp (w s') (w s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hinner s hs]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    have hadd := honE_kmom_subL S s' s (hfL s' hs') (hfL s hs)
    rw [show (honE v h fc fu HM μ).hatChiSq (s' - s)
        = Work.BoseK15.corpusBox.hatChiSq
            ((honE v h fc fu HM μ).ell • (honF v h fc fu HM μ).kmom (s' - s))
        from honE_hatChiSq S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N (s' - s),
      hadd, honE_ell S, smul_sub]
  rw [houter, hrewrite]
  exact Work.BoseB7AK.K15R.hatChiSq_double_sum_nonneg (honF v h fc fu HM μ)
    (fun s => Work.BoseBoxFock.ellH v μ • (honF v h fc fu HM μ).kmom s) T c w

end Psd

/-! ## 5. The bundle -/

section Main

/-- **The corrected τ-free bundle at the honest model.** -/
theorem exists_KinkFS_honest (S : HonSetup v h fc fu HM μ) (Cw Cw' : ℝ)
    (hW1abs : ∀ p : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p|
      ≤ Cw * a v)
    (hW1even : ∀ p : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (-p)
        = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p)
    (hW1om0nn : 0 ≤ (honE v h fc fu HM μ).W1omega0)
    (hW1om0le : (honE v h fc fu HM μ).W1omega0 ≤ Cw' * (honE v h fc fu HM μ).aScat) :
    KinkFS (max Cw Cw') (honF v h fc fu HM μ) (honT v h fc fu HM μ)
      (honE v h fc fu HM μ) where
  W1_le := fun k => by
    rw [honE_W1_apply S k]
    have hζ1 : uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        ((honF v h fc fu HM μ).kmom k) ≤ 1 := fu.le_one _
    have hζ0 : (0 : ℝ) ≤ uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
        ((honF v h fc fu HM μ).kmom k) := fu.nonneg _
    calc |uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
            ((honF v h fc fu HM μ).kmom k)
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              ((honF v h fc fu HM μ).kmom k)|
        = uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
            ((honF v h fc fu HM μ).kmom k)
          * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              ((honF v h fc fu HM μ).kmom k)| := by
          rw [abs_mul, abs_of_nonneg hζ0]
      _ ≤ 1 * (Cw * a v) := mul_le_mul hζ1 (hW1abs _) (abs_nonneg _) (by norm_num)
      _ ≤ max Cw Cw' * (honE v h fc fu HM μ).aScat := by
          rw [one_mul, honE_aScat]
          exact le_mul_mono_of_nonneg le_rfl (le_max_left _ _) (le_of_lt S.hav)
  W1_even := fun k => by
    rw [honE_W1_apply S k,
      honE_W1_apply S (-k),
      show (honF v h fc fu HM μ).kmom (-k) = -((honF v h fc fu HM μ).kmom k) from by
        rw [honF_kmom,
          honF_kmom]
        exact Work.BoseBoxFock.kmomLab_neg (Work.BoseBoxFock.ellH v μ) (HM μ).N k]
    rw [show uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
          (-((honF v h fc fu HM μ).kmom k))
        = uvCut fu (uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N)
          ((honF v h fc fu HM μ).kmom k) from by simp only [uvCut, norm_neg],
      hW1even]
  aScat_nonneg := by
    rw [honE_aScat]
    exact le_of_lt S.hav
  kmom_neg := fun k => by
    rw [honF_kmom,
      honF_kmom]
    exact Work.BoseBoxFock.kmomLab_neg (Work.BoseBoxFock.ellH v μ) (HM μ).N k
  fL_nonneg := fun s => by
    rw [show (honE v h fc fu HM μ).fL s
        = fc.f (‖(honF v h fc fu HM μ).kmom s‖
            / ((honE v h fc fu HM μ).KL
                * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
        from rfl]
    exact fc.nonneg _
  fL_le_one := fun s => by
    rw [show (honE v h fc fu HM μ).fL s
        = fc.f (‖(honF v h fc fu HM μ).kmom s‖
            / ((honE v h fc fu HM μ).KL
                * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
        from rfl]
    exact fc.le_one _
  fL_even := fun s => by
    rw [show (honE v h fc fu HM μ).fL s
        = fc.f (‖(honF v h fc fu HM μ).kmom s‖
            / ((honE v h fc fu HM μ).KL
                * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
        from rfl,
      show (honE v h fc fu HM μ).fL (-s)
        = fc.f (‖(honF v h fc fu HM μ).kmom (-s)‖
            / ((honE v h fc fu HM μ).KL
                * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
        from rfl,
      show (honF v h fc fu HM μ).kmom (-s) = -((honF v h fc fu HM μ).kmom s) from by
        rw [honF_kmom,
          honF_kmom]
        exact Work.BoseBoxFock.kmomLab_neg (Work.BoseBoxFock.ellH v μ) (HM μ).N s,
      norm_neg]
  fL_supp2 := fun s hs => honE_fL_supp2 S s hs
  kmom_subW := fun s k hs hk hW => honE_kmom_subW S s k hs hk hW
  kmom_subL := fun s s' hs hs' => honE_kmom_subL S s s' hs hs'
  hasKernelW := fun i j hi hj hW => honE_hasKernelW S i j hi hj hW
  hatChi_eq := fun k => honE_hatChi S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N k
  hatChiSq_eq := fun k => honE_hatChiSq S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N k
  W1omega0_nonneg := hW1om0nn
  W1omega0_le := by
    have ha : (0 : ℝ) ≤ (honE v h fc fu HM μ).aScat := by
      rw [honE_aScat]
      exact le_of_lt S.hav
    exact le_mul_mono_of_nonneg hW1om0le (le_max_right _ _) ha
  hatChiSq_form_psd := fun Ss c w hguard => honE_hatChiSq_form_psd S Ss c w hguard

end Main

/-! ## 6. Non-vacuity: the cube-size condition is satisfiable, and the
`HonestRows` bundle at the honest environment -/

section Compose

/-- **The cube-size condition of `HonSetup` is satisfiable.**  For every admissible
`μ` there is a cube size `N` with `4K_L√(μa) ≤ Λ_N = (2π/ℓ)N/4` (design §2.3: the
honest family may use *any* cube at each `μ`). -/
theorem exists_N_uvRad (S : HonSetup v h fc fu HM μ) :
    ∃ N : ℕ, 4 * ((honE v h fc fu HM μ).KL
        * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
      ≤ uvRad (Work.BoseBoxFock.ellH v μ) N := by
  have hκ : (0 : ℝ) < (honE v h fc fu HM μ).KL
      * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat) := kappa_pos S
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hπ : 0 < π := Real.pi_pos
  obtain ⟨N, hN⟩ := exists_nat_ge (16 * ((honE v h fc fu HM μ).KL
    * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
      * Work.BoseBoxFock.ellH v μ / (2 * π))
  refine ⟨N, ?_⟩
  have hN' : 16 * ((honE v h fc fu HM μ).KL
      * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
        * Work.BoseBoxFock.ellH v μ / (2 * π) ≤ (N : ℝ) := hN
  have hclear : 16 * ((honE v h fc fu HM μ).KL
      * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat))
        * Work.BoseBoxFock.ellH v μ ≤ 2 * π * (N : ℝ) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * π)).mp hN'
    linarith
  rw [uvRad]
  have heq : 2 * π / Work.BoseBoxFock.ellH v μ * (N : ℝ) / 4
      = 2 * π * (N : ℝ) / (4 * Work.BoseBoxFock.ellH v μ) := by
    field_simp
  rw [heq, le_div_iff₀ (by linarith : (0 : ℝ) < 4 * Work.BoseBoxFock.ellH v μ)]
  linarith

/-- **`HonestRows` at the honest environment**, from the honest §11/§12 rows: the
τ-free bundle is *derived* (`exists_KinkFS_honest` + `KinkFS.mono`), the τ̃-pin is
`honE_tau`, the box-model equation is `ChiPin.hon_box` and the kinetic domination
`hτ` is `HonestInhab.exists_hon_tau` (with its threshold `tGe` and the smallness
row `aK_H/(sℓ) ≤ 1/32`). -/
theorem exists_HonestRows_honest (S : HonSetup v h fc fu HM μ) (Cw Cw' K₀ : ℝ)
    (hK₀0 : 0 ≤ K₀) (hK₀ : max Cw Cw' ≤ K₀)
    (hW1abs : ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p|
        ≤ Cw * a v)
    (hW1even : ∀ p : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (-p)
        = Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p)
    (hW1om0nn : 0 ≤ (honE v h fc fu HM μ).W1omega0)
    (hW1om0le : (honE v h fc fu HM μ).W1omega0 ≤ Cw' * (honE v h fc fu HM μ).aScat)
    (hW1low : ∀ k : Lab (HM μ).N, ‖(honF v h fc fu HM μ).kmom k‖
      ≤ 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) →
      0 ≤ (honE v h fc fu HM μ).W1 k)
    (hα : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ p q : Lab (HM μ).N,
      (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat p →
      (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
      |(KzEnvAt (honE v h fc fu HM μ) ρ).alpha p - (KzEnvAt (honE v h fc fu HM μ) ρ).alpha q|
        ≤ K₀ * (honE v h fc fu HM μ).lille
          * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
          * ‖(honF v h fc fu HM μ).kmom p - (honF v h fc fu HM μ).kmom q‖)
    (hint : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ →
      |ρ * (honE v h fc fu HM μ).W1omega0 - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
            (honE v h fc fu HM μ).W1 k * (KzEnvAt (honE v h fc fu HM μ) ρ).alpha k|
        ≤ K₀ * ρ * (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH⁻¹)
    (hq2 : ∀ ρ : ℝ, AdmRho (honE v h fc fu HM μ) ρ → ∀ Ψ : (honF v h fc fu HM μ).H,
      2 * ρ * (honE v h fc fu HM μ).W1omega0 * (honF v h fc fu HM μ).qw Ψ
          ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
        ≤ (honF v h fc fu HM μ).qw Ψ ((honF v h fc fu HM μ).Q2ex (KzEnvAt (honE v h fc fu HM μ) ρ))
          + ((honE v h fc fu HM μ).b / 400) * (honF v h fc fu HM μ).qw Ψ
              ((honT v h fc fu HM μ).gapOpT (KzEnvAt (honE v h fc fu HM μ) ρ))
          + (1 / 2) * (honF v h fc fu HM μ).qw Ψ
              ((honF v h fc fu HM μ).dNumOpR (KzEnvAt (honE v h fc fu HM μ) ρ)
                (fun k => rHi (honF v h fc fu HM μ) (honE v h fc fu HM μ) k
                  ∧ ¬ (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH
                      (honE v h fc fu HM μ).aScat k)))
    (hhatChi_small : ∀ q : Lab (HM μ).N,
      (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
      |(honE v h fc fu HM μ).hatChi q| ≤ K₀ * eta (honE v h fc fu HM μ))
    (hccrX_small : ∀ s q : Lab (HM μ).N, (honE v h fc fu HM μ).fL s ≠ 0 →
      (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
      |(honT v h fc fu HM μ).ccrX s q| ≤ K₀ * eta (honE v h fc fu HM μ))
    (hsum : ∑ s ∈ excited (Lab (HM μ).N), |(honE v h fc fu HM μ).hatChiSq s| ≤ K₀)
    (htail : ∑ s ∈ excited (Lab (HM μ).N),
        |(honE v h fc fu HM μ).hatChiSq s| * (1 - (honE v h fc fu HM μ).fL s)
      ≤ K₀ * ((honE v h fc fu HM μ).Kl * (honE v h fc fu HM μ).KL)
          ^ (-((honE v h fc fu HM μ).intM : ℝ)))
    (hform_upper : ∀ (Ss : Finset (Lab (HM μ).N)) (c : Lab (HM μ).N → ℝ)
      (w : Lab (HM μ).N → (honF v h fc fu HM μ).H),
      (∑ s ∈ Ss, ∑ s' ∈ Ss, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s))
        ≤ K₀ * ∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s))
    (hcount : (((excited (Lab (HM μ).N)).filter
        (fun s => (honE v h fc fu HM μ).fL s ≠ 0)).card : ℝ)
      ≤ K₀ * ((honE v h fc fu HM μ).Kl * (honE v h fc fu HM μ).KL) ^ 3)
    (hsumW1sq : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ q ∈ (excited (Lab (HM μ).N)).filter
          ((honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat),
          (honE v h fc fu HM μ).W1 q ^ 2 / ‖(honF v h fc fu HM μ).kmom q‖ ^ 2
      ≤ K₀ * (honE v h fc fu HM μ).aScat) :
    ∃ tGe : ℝ, 0 < tGe ∧ (S.hv.t ≤ tGe →
      (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
        / ((honE v h fc fu HM μ).s * (honE v h fc fu HM μ).ell) ≤ 1 / 32 →
      Nonempty (HonestRows K₀ (honF v h fc fu HM μ) (honT v h fc fu HM μ)
        (honE v h fc fu HM μ))) := by
  obtain ⟨tGe, htGe0, htGe⟩ := exists_hon_tau K₀ hK₀0
  refine ⟨tGe, htGe0, fun hthr hsmall => ⟨honestRows_of_rows ?_ S.hv ?_ hW1low ?_ hα hint hq2
    hhatChi_small hccrX_small hsum htail hform_upper hcount hsumW1sq⟩⟩
  · exact (exists_KinkFS_honest S Cw Cw' hW1abs hW1even hW1om0nn hW1om0le).mono hK₀
  · exact htGe (F := honF v h fc fu HM μ) (T := honT v h fc fu HM μ)
      (honE_tau HM μ) S.hv hthr hsmall
  · exact fun i j => hon_box HM μ S.hμ S.hav i j

end Compose

/-! ## 7. Discharging the two `Ŵ₁` rows from FS §4 -/

section Potential

/-- **The bundle at the honest model from the potential's own régime rows.**  FS
`eq:1Q-integral` (`Work.BoseB7AK.W1rows.W1hat_abs_le`, constant `16π`) and the
evenness of `Ŵ₁` (`W1hat_even_contDiff`) discharge `hW1abs`/`hW1even`, so only
the two `Ŵ₁ω(0)` rows remain. -/
theorem exists_KinkFS_honest_of_potential (S : HonSetup v h fc fu HM μ)
    (R : ℝ) (hR : 0 < R) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (Cw' : ℝ) (hW1om0nn : 0 ≤ (honE v h fc fu HM μ).W1omega0)
    (hW1om0le : (honE v h fc fu HM μ).W1omega0 ≤ Cw' * (honE v h fc fu HM μ).aScat) :
    KinkFS (max (16 * π) Cw') (honF v h fc fu HM μ) (honT v h fc fu HM μ)
      (honE v h fc fu HM μ) :=
  exists_KinkFS_honest S (16 * π) Cw'
    (fun p => Work.BoseB7AK.W1rows.W1hat_abs_le hR (Work.BoseBoxFock.ellH_pos v μ)
      hv_nonneg hvrad hv_supp h hRℓ p)
    ((Work.BoseB7AK.W1rows.W1hat_even_contDiff hR (Work.BoseBoxFock.ellH_pos v μ)
      hv_nonneg hvrad hv_supp h hRℓ).1)
    hW1om0nn hW1om0le

end Potential

end Work.BoseGateFS
