import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.HkMem_mul_pth_flat
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotAbsHon
import Submission.Work.FTS.StrongPersist.N6Trans.IP4T1Honest
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.LeafSum
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.T1HonestGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open scoped Real Topology

set_option autoImplicit false

/-- **The level-four `T1` transport clause in the honest class, with *free* coercive step
coefficients.**

`Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂''` is the corrected coercive recursion of
`CoercivityFix` (`HkIPStep c₁ c₂ (HkIPStep c₁' c₂' (HkIPStep c₁'' c₂'' (H1IP α)))`), whose six
coefficients are chosen small at each of the three levels.  The slot domination
`IPGen.ip4SlotDomGen` bounds it by `CoefMax³ · 3³ · 10²² · leafSum α u g` *for nonnegative
coefficients*, and the honest-class leaf bound `T1Hon.leafSum_bound` controls the leaf sum of
the `D_θ`-transport pairing.  Composing the two, exactly as in `IP4T1Honest` (the unit
coefficient case), gives the clause with the constant `CoefMax³ · 3³ · 10²² · Cb · √10`. -/
theorem T1HonestGen (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (h₁' : 0 < c₁') (h₂' : 0 < c₂') (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.DecayAll 4 g →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
          ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
              * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  -- the slot domination, for the *general* nonnegative coefficients
  obtain ⟨hKpos, hD⟩ := Work.FTS.IPGen.ip4SlotDomGen (c₁ := c₁) (c₂ := c₂) (c₁' := c₁')
    (c₂' := c₂') (c₁'' := c₁'') (c₂'' := c₂'')
    (le_of_lt h₁) (le_of_lt h₂) (le_of_lt h₁') (le_of_lt h₂') (le_of_lt h₁'')
    (le_of_lt h₂'')
  -- the honest-class leaf bound for the `D_θ`-transport pairing
  obtain ⟨Cb, hCbpos, hCb⟩ := Work.FTS.StrongPersist.N6Trans.T1Hon.leafSum_bound
  set K : ℝ := max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3
      * 3 ^ 3 * 10 ^ 22 with hKdef
  refine ⟨K * Cb * Real.sqrt 10, 1, by positivity, one_pos, ?_⟩
  intro α hα f g hf hmemf hg hmemg hdecg
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hKb := hD α hα (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
    (Work.FTS.StrongPersist.N6Trans.SmoothOpen_mul hf hg.Dth) hg
  have hle := hCb α f g hαpos hα1 hf hmemf hg hmemg hdecg
  have hgam : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have hsqrt : 1 / Real.sqrt (Work.Spaces.gam α - 1)
      = Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
    rw [hgam, Real.sqrt_div hαpos.le 10, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.rpow_neg hαpos.le]
    field_simp
  have hmod : Work.Spaces.HkSq α 4 g = (Work.Spaces.HkNorm α 4 g) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 g)]
  have hstep : K * Work.FTS.TransportS.leafSum α
        (fun z θ => f z θ * Work.Spaces.Dth g z θ) g
      ≤ K * (Cb / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 4 g) :=
    mul_le_mul_of_nonneg_left hle hKpos.le
  have hstep2 : K * (Cb / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkSq α 4 g)
      = K * Cb * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
          * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
    rw [show Cb / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g
        = Cb * (1 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g by ring]
    rw [hmod, hsqrt]
    ring
  linarith [hKb, hstep, hstep2]

end Work.FTS.StrongEps.E4R3.N4C
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.SlotHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

open Work.FTS.TransportS
open Work.FTS.TransportS.SlotT2
open Work.FTS.TransportS.T2Sup

/-- **The honest per-slot transport bound** (the `D_z`-transport clause, one leaf at a time). -/
def T2SlotHon (C : ℝ) : Prop :=
  ∀ (α : ℝ) (f g : Fn), 0 < α → α ≤ 1 → HonF α f → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 4 g → Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → IsLeafW α a ρ →
      |slotPairing ρ a b (fun z θ => f z θ * Work.Spaces.Dz g z θ) g|
        ≤ C * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f)
            * Work.FTS.Nonlin.Xn α g ^ 2

/-- **`T2SlotHon` from the honest per-slot engine.** -/
theorem T2SlotHon_of_slotAbs (hTop : TopSlotHonProp) (hDel : DelicateHonProp) :
    ∃ C : ℝ, 0 < C ∧ T2SlotHon C := by
  obtain ⟨C, hC, hb⟩ := slotAbsBound_hon hTop hDel
  refine ⟨C, hC, ?_⟩
  intro α f g hα hα1 hsf hsg hmg4 hmg5 hdec a b ρ hab hleaf
  rcases hleaf with hρ | hρ | ⟨ha, hρ⟩
  · -- `ρ = leafEta = canonW η`
    have hρ' : ρ = canonW Work.Spaces.eta := by rw [hρ]; exact leafWeight_eq_canon.1
    rw [slotPairing, hρ']
    exact hb α f g a b Work.Spaces.eta hα hα1 hsf hsg hmg4 hmg5 hdec hab Work.Spaces.eta_pos.le
      (fun _ => le_rfl) (eta_le_gam hα) (Or.inl le_rfl)
  · -- `ρ = leafOne = canonW 0`
    have hρ' : ρ = canonW 0 := by rw [hρ]; exact leafWeight_eq_canon.2.1
    rw [slotPairing, hρ']
    exact hb α f g a b 0 hα hα1 hsf hsg hmg4 hmg5 hdec hab le_rfl
      (fun _ => Work.Spaces.eta_pos.le) (le_of_lt (Work.Spaces.gam_pos hα))
      (Or.inl Work.Spaces.eta_pos.le)
  · -- `ρ = leafGam α = canonW γ`, only at slots with `a ≥ 1`
    have hρ' : ρ = canonW (Work.Spaces.gam α) := by rw [hρ]; exact leafWeight_eq_canon.2.2 α
    rw [slotPairing, hρ']
    exact hb α f g a b (Work.Spaces.gam α) hα hα1 hsf hsg hmg4 hmg5 hdec hab
      (le_of_lt (Work.Spaces.gam_pos hα))
      (fun h0 => absurd h0 (by omega)) le_rfl (Or.inr rfl)

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
