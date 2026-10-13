import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.supDzAvgLevel
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- **The a.e. pointwise bound on the `D_z`-iterates of the angular moment `FK f`.**

For a datum `f` of class `C^∞` on the open quadrant whose weighted `ℋ⁶`- and `ℋ⁷`-energy is
finite, and for `b ≤ 6`, the `b`-th `D_z`-iterate of the radial function `z ↦ FK f z`
(`FK f z = ∫_θ f z θ K θ dθ`, the angular moment) is bounded almost everywhere in `z` by
`C·HkSq α (b+1) f`, with a universal constant `C`.

The proof is the two-step reduction `D_z^b (FK f) = FK (D_z^b f)` a.e. (`DzIter_FK_eq_ae`),
the angular Cauchy–Schwarz `(FK g z)² ≤ 16 ∫_θ g z θ ² dθ` (`n5_FK_abs_le`), and the
uniform-in-`z` angular-average bound `∫_θ (D_z^b f z θ)² dθ ≤ C·HkSq α (b+1) f`
(`supDzAvgLevel`, the level-`k` form of the radial Hardy/window inequality). -/
theorem fkDzdIterSqLe : ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ} {f : Work.FTS.Galerkin.Fn},
    0 < α → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkMem α 7 f → ∀ b : ℕ, b ≤ 6 →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        ≤ C * Work.Spaces.HkSq α (b + 1) f := by
  obtain ⟨C₁, _hC₁pos, hC₁⟩ := supDzAvgLevel
  refine ⟨16 * C₁, by positivity, ?_⟩
  intro α f hα hsm hm6 hm7 b hb
  -- `ℋ^{b+1}`-membership, descending from `ℋ⁷`
  have hbmem : Work.Spaces.HkMem α (b + 1) f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm (b + 1) (by omega) hm7
  -- `D_z^b (FK f) = FK (D_z^b f)` a.e. in `z`
  have hae := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae hsm hm6 b hb
  have hae' := (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mp hae
  rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
  filter_upwards [hae', MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hid hne
  intro hzI
  have hzpos : 0 < z := lt_of_le_of_ne (Set.mem_Ici.mp hzI) (Ne.symm hne)
  -- angular Cauchy–Schwarz for the moment of the `b`-th derivative
  have hsq : (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      ≤ 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 :=
    FKdzIter_sq_le hsm hbmem b (Nat.le_succ b) hzpos
  -- the uniform angular-average bound at level `b+1`
  have havg : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
      ≤ C₁ * Work.Spaces.HkSq α (b + 1) f :=
    hC₁ α f (b + 1) b hα hsm hbmem (le_refl (b + 1)) z hzpos
  rw [hid hzI 0]
  calc (Work.Construction.FK (Work.Spaces.DzIter b f) z) ^ 2
      ≤ 16 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 := hsq
    _ ≤ 16 * (C₁ * Work.Spaces.HkSq α (b + 1) f) :=
        mul_le_mul_of_nonneg_left havg (by norm_num)
    _ = (16 * C₁) * Work.Spaces.HkSq α (b + 1) f := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
