import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.wlInf_divz_slotsB
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundCore
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyA
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.hkmem_pieces_own =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

theorem hkmem_N0pieces_own {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 f z))
    (h0 : Work.Construction.L12 f 0 = 0)
    (m6 : Work.Spaces.HkMem α 6 f) (m7 : Work.Spaces.HkMem α 7 f) :
    Work.Spaces.HkMem α 6 (NP3 α f) ∧ Work.Spaces.HkMem α 6 (NP4a α f) ∧
    Work.Spaces.HkMem α 6 (NP4b α f) ∧ Work.Spaces.HkMem α 6 (NP5a α f) ∧
    Work.Spaces.HkMem α 6 (NP5b α f) ∧ Work.Spaces.HkMem α 6 (NP6 α f) := by
  -- ## the radial `L₁₂` machinery
  obtain ⟨Xi, Cpow, hXi, hCpow, hN6⟩ := Work.FTS.StrongPersist.N6_L12H
  have hL12mem : Work.Spaces.HkMem α 6 (fun z θ => Work.Construction.L12 f z) :=
    (hN6 α hα f ⟨hf, m6⟩ h0).1
  obtain ⟨C6, hC6pos, hsup6⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
  have hL12jet : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    fun j hj z hz => hsup6 α f hα hα1 hf m6 m7 h0 j hj z hz
  have hB0 : 0 ≤ C6 * Work.Spaces.HkNorm α 6 f :=
    mul_nonneg hC6pos.le (Work.Spaces.HkNorm_nonneg α 6 f)
  have hL12cd : ContDiffOn ℝ 6 (fun z : ℝ => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 6
        (Function.uncurry (fun z (_ : ℝ) => Work.Construction.L12 f z))
        Work.FTS.EllipticEst.Q0 := hL.forall 6
    have h2 : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
      ContDiffOn.prodMk contDiffOn_id contDiffOn_const
    have h3 := h1.comp h2 (fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩)
    refine h3.congr (fun z _ => ?_)
    rfl
  have hL12f : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * f z θ) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 α
      (C6 * Work.Spaces.HkNorm α 6 f) (fun z => Work.Construction.L12 f z) f
      hα hB0 hL12cd hL12jet hf m6
  have hDthmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dth f) :=
    Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 6) (f := f) (by linarith) hf m7
  have hL12dth : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 α
      (C6 * Work.Spaces.HkNorm α 6 f) (fun z => Work.Construction.L12 f z)
      (Work.Spaces.Dth f) hα hB0 hL12cd hL12jet hf.Dth hDthmem
  have hDzmem : Work.Spaces.HkMem α 6 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le (α := α) (k := 6) (f := f) hf m7
  have hL12dz : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dz f z θ) :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.HkMem_radial_mul6 α
      (C6 * Work.Spaces.HkNorm α 6 f) (fun z => Work.Construction.L12 f z)
      (Work.Spaces.Dz f) hα hB0 hL12cd hL12jet hf.Dz hDzmem
  -- ## the `F_*`-coefficient packages
  obtain ⟨CD, hCDpos, hDthFstar⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨CC, hCCpos, hc2mDz⟩ := Work.FTS.StrongPersist.H6Pair6Aux.c2mDzFstar_W6
  obtain ⟨CA, hCApos, hN0coef⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0coefA6_WlInf6
  obtain ⟨hN0coef_sm, hN0coef_w, hN0coef_le⟩ := hN0coef α hα hα1
  obtain ⟨Cc2, hCc2pos, hc2sm, hc2b, hc2jet⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
  obtain ⟨Cm6, hCm6pos, hang⟩ := Work.FTS.StrongPersist.angmul6
  have hangc2 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.c2m θ * (Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ)) :=
    (hang α hα hα1 (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dz f z θ) Cc2 hc2sm
      (fun θ hθ => hc2b θ hθ)
      (fun i hi hi6 θ hθ => hc2jet i hi (by omega) 0 θ hθ)
      (so_mul hL hf.Dz) hL12dz).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `NP3 = (1/α)·(L₁₂(f)·f)`
    refine HkMem_congr_Qd (f := fun z θ =>
      (1 / α) * (Work.Construction.L12 f z * f z θ)) ?_ ?_
    · intro z θ hzθ
      show (1 / α) * (Work.Construction.L12 f z * f z θ) = NP3 α f z θ
      simp only [NP3] <;> ring
    · exact Work.FTS.LocData.HkMem_const_mul α 6 (1 / α) hL12f
  · -- `NP4a = (3/2α)·(L₁₂(f)·D_θF_*)`
    refine HkMem_congr_Qd (f := fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      * ((3 / (2 * α)) * Work.Construction.L12 f z)) ?_ ?_
    · intro z θ hzθ
      show Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 f z) = NP4a α f z θ
      simp only [NP4a, NA4] <;> ring
    · exact HkMem_mul_of_WlInf6 hα hα1 (smoothOpen_Fstar α).Dth
        (hDthFstar α hα hα1).1 (so_const_mul (3 / (2 * α)) hL)
        (Work.FTS.LocData.HkMem_const_mul α 6 (3 / (2 * α)) hL12mem)
  · -- `NP4b = (3/2α)·(L₁₂(f)·D_θf)`
    refine HkMem_congr_Qd (f := fun z θ =>
      (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)) ?_ ?_
    · intro z θ hzθ
      show (3 / (2 * α)) * (Work.Construction.L12 f z * Work.Spaces.Dth f z θ)
        = NP4b α f z θ
      simp only [NP4b] <;> ring
    · exact Work.FTS.LocData.HkMem_const_mul α 6 (3 / (2 * α)) hL12dth
  · -- `NP5a = (-1)·(L₁₂(f)·(c2m·D_zF_*))`
    refine HkMem_congr_Qd (f := fun z θ =>
      (Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
        * (-1 * Work.Construction.L12 f z)) ?_ ?_
    · intro z θ hzθ
      show (Work.Construction.c2m θ * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
          * (-1 * Work.Construction.L12 f z) = NP5a α f z θ
      simp only [NP5a, NA5]
      ring
    · exact HkMem_mul_of_WlInf6 hα hα1
        (so_mul (so_snd contDiff_c2m) (smoothOpen_Fstar α).Dz)
        (hc2mDz α hα hα1).1 (so_const_mul (-1) hL)
        (Work.FTS.LocData.HkMem_const_mul α 6 (-1) hL12mem)
  · -- `NP5b = (-1)·(c2m·L₁₂(f)·D_zf)`
    refine HkMem_congr_Qd (f := fun z θ =>
      -1 * (Work.Construction.c2m θ * (Work.Construction.L12 f z
        * Work.Spaces.Dz f z θ))) ?_ ?_
    · intro z θ hzθ
      show -1 * (Work.Construction.c2m θ * (Work.Construction.L12 f z
          * Work.Spaces.Dz f z θ)) = NP5b α f z θ
      simp only [NP5b] <;> ring
    · exact Work.FTS.LocData.HkMem_const_mul α 6 (-1) hangc2
  · -- `NP6 = (-1)·(c2m·L₁₂(F_*)·D_zf)`
    refine HkMem_congr_Qd (f := fun z θ =>
      (-(2 * α / (1 + z)) * Work.Construction.c2m θ) * Work.Spaces.Dz f z θ) ?_ ?_
    · intro z θ hzθ
      show (-(2 * α / (1 + z)) * Work.Construction.c2m θ) * Work.Spaces.Dz f z θ
        = NP6 α f z θ
      have hz : 0 ≤ z := le_of_lt hzθ.1
      simp only [NP6, NA6]
      rw [Work.Construction.L12_Fstar_eq hα hα1 hz]
      ring
    · exact HkMem_mul_of_WlInf6 hα hα1 hN0coef_sm hN0coef_w hf.Dz hDzmem

end Work.FTS.StrongPersist.H6Pair6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.starDat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology

/-!
# `starDat` — the star data at order six

From a `StarPkg6 α Cs Φs` (the level-six star package, whose five fields bound
`((z+1)/z)·ℛ(Φ̃_*)`, `((z+1)/z)·𝒱(Φ̃_*)`, `((z+1)/z)·(𝒰(Φ̃_*)/sin 2θ)` and the two unweighted
counterparts in the paper's `𝒲^{6,∞}`-norm by `Cs·α`) this module extracts

* `SmoothOpen` of `ℛ(Φ̃_*)`, `𝒰(Φ̃_*)/sin 2θ` and `𝒱(Φ̃_*)` (`fields_smooth`,
  `smoothOpen_Rop`: the three fields are rational in `Φ̃_*` and its first derivatives and the
  only denominators `cos θ`, `sin 2θ` do not vanish on the open quadrant), and
* the pointwise slot bounds with the radial decay `z/(1+z)` and the flat angular factor
  `(α + sin 2θ)·sin(2θ)^{α/5}` in the mixed slots,

by writing each of the three fields as `z/(1+z) · G` with `G` the corresponding *weighted* star
field (so that `G` is the object priced by `StarPkg6`) and applying the proved multipliers
`divz_conj0`/`divz_conj2`.  The passage from `mixed j i (z/(1+z)·G)` to `mixed j i A` is the
locality of the mixed slots on the open quadrant (`mixed_congr_Qd`).
-/

theorem starDat : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (Φs : Work.FTS.Galerkin.Fn) (Cs : ℝ),
      Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
      Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) ∧
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ) ∧
      Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) ∧
      (∀ (A : Work.FTS.Galerkin.Fn),
          (A = Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) ∨
           A = (fun z θ => Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
             / Work.Construction.s2 θ) ∨
           A = Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs)) →
          ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            |Work.Spaces.mixed j i A z θ| ≤ C * (Cs * α) * (z / (1 + z)) *
              (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1)) := by
  have hCΦ : ∀ b : ℕ, b ≤ 6 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ 1000000 * (z / (1 + z)) :=
    fun b hb z θ hz => divz_DzIter_le b hb z θ hz
  have hleib : ∀ (j i : ℕ) (G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen G →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
                * Work.Spaces.mixed (j - b) i G z θ) :=
    fun j i G hG z θ hz hθ0 hθ1 =>
      divz_mixed_leibniz (fun z => z / (1 + z)) G j i smoothOpen_divz hG z θ hz hθ0 hθ1
  obtain ⟨C0, hC0pos, hC0⟩ := divz_conj0 1000000 (by norm_num) hCΦ hleib
  obtain ⟨C2, hC2pos, hC2⟩ := divz_conj2 1000000 (by norm_num) hCΦ hleib
  refine ⟨max C0 C2, lt_max_of_lt_left hC0pos, ?_⟩
  intro α hα Φs Cs hpkg
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φs := hpkg.smooth
  obtain ⟨hΦTs, hRw, hVop, hVw, hUs, hUsw, -⟩ :=
    Work.FTS.PhiStar.CoreAux.fields_smooth hαpos hα1 hsm
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hΦTs
  refine ⟨hR, hUs, hVop, ?_⟩
  -- The generic step: `A = z/(1+z) · G` with `G` priced by `StarPkg6`.
  have key : ∀ (B G : ℝ → ℝ → ℝ),
      (∀ z θ : ℝ, 0 < z → G z θ = (z + 1) / z * B z θ) →
      Work.FTS.EllipticEst.SmoothOpen G → Work.Spaces.WlInfMem α 6 G →
      Work.Spaces.WlInf α 6 G ≤ Cs * α →
      ∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed j i B z θ| ≤ max C0 C2 * (Cs * α) * (z / (1 + z)) *
          (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) else 1) := by
    intro B G hGdef hGsm hGmem hGbd j i hji z θ hz hθ0 hθ1
    have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
    -- locality: `z/(1+z) · G` and `B` agree on the open quadrant
    have hcongr : Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ
        = Work.Spaces.mixed j i B z θ := by
      refine Work.FTS.StrongPersist.H6Pair6Aux.mixed_congr_Qd
        (f := fun z θ => z / (1 + z) * G z θ) (f' := B) ?_ z θ hzθ j i
      intro z' θ' hz'θ'
      obtain ⟨hz', -⟩ := hz'θ'
      have hz'0 : 0 < z' := hz'
      have hz'ne : z' ≠ 0 := ne_of_gt hz'0
      have hz1ne : (1 + z') ≠ 0 := by positivity
      rw [hGdef z' θ' hz'0]
      field_simp
      ring
    have hKnn : 0 ≤ Cs * α := le_trans (Work.Spaces.WlInf_nonneg α 6 G hGmem) hGbd
    have hFnn : 0 ≤ z / (1 + z) := by positivity
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [if_neg (show ¬ (1 : ℕ) ≤ 0 by norm_num), mul_one]
      have hj6 : j ≤ 6 := by omega
      have h := hC0 α hα G (Cs * α) hGsm hGmem hGbd j hj6 z θ hz hθ0 hθ1
      rw [hcongr] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C0 C2) hKnn) hFnn
    · have hif : (if 1 ≤ i then (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
            else 1)
          = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := if_pos hipos
      rw [hif]
      have h := hC2 α hα G (Cs * α) hGsm hGmem hGbd j i hipos hji z θ hz hθ0 hθ1
      rw [hcongr] at h
      have hSnn : 0 ≤ Real.sin (2 * θ) :=
        Work.Spaces.sin_two_nonneg' ⟨le_of_lt hθ0, le_of_lt hθ1⟩
      have hYnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hSnn _)
      refine le_trans h ?_
      calc C2 * (Cs * α) * (z / (1 + z)) * (α + Real.sin (2 * θ))
            * (Real.sin (2 * θ)) ^ (α / 5)
          = (C2 * (Cs * α) * (z / (1 + z)))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
        _ ≤ (max C0 C2 * (Cs * α) * (z / (1 + z)))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            refine mul_le_mul_of_nonneg_right ?_ hYnn
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right C0 C2) hKnn) hFnn
  intro A hA
  rcases hA with rfl | rfl | rfl
  · exact key _ _ (fun z θ _ => rfl) hRw hpkg.RW6.1 hpkg.RW6.2
  · exact key _ _ (fun z θ _ => rfl) hUsw hpkg.UszW6.1 hpkg.UszW6.2
  · exact key _ _ (fun z θ _ => rfl) hVw hpkg.VzW6.1 hpkg.VzW6.2

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
