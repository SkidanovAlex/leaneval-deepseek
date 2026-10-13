import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.wlInf_divz_slotsB
import Submission.Work.FTS.PhiStar.CoreAux.fields_smooth
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux

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
