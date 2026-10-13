import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.CoercivityFix.Transfer.main
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.IPGen.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.IPGen

theorem headline_IP4_of_errors
    (hE1 : ∃ κ₁ : ℝ, 0 ≤ κ₁ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 →
      ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E1 α f)
          ≤ α * κ₁ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (hE2 : ∃ κ₂ : ℝ, 0 ≤ κ₂ ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 →
      ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.CoerAdm α f →
        Work.Spaces.HkNorm α n (Work.FTS.CoercivityFix.Transfer.E2 α f)
          ≤ κ₂ * (Work.Spaces.HkNorm α n f + Work.Spaces.HkNorm α n (Work.Spaces.Dth f)))
    (CC₁ : ℝ) (hCC₁ : 0 < CC₁)
    (hCD₁ : ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 10 ^ 14) →
      Work.FTS.CoercivityFix.Assembly.CoerData2 α 1 (Work.Coercivity.H1IP α) 2 CC₁)
    (hok₁ : ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 1 (Work.Coercivity.H1IP α) CC₁)
    (hok₂ : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ : ℝ, 0 < c₂ →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 2
        (Work.FTS.CoercivityFix.Assembly.IP2 1 c₂ α) (3 * max 1 (max 1 c₂) * CC₁))
    (hok₃ : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ c₂ c₂' : ℝ, 0 < c₂ → 0 < c₂' →
      Work.FTS.CoercivityFix.Transfer.LevelPkg α 3
        (Work.FTS.CoercivityFix.Assembly.IP3 1 c₂ 1 c₂' α)
        (3 * max 1 (max 1 c₂') * (3 * max 1 (max 1 c₂) * CC₁))) :
    ∃ c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ,
      0 < c₁ ∧ 0 < c₂ ∧ 0 < c₁' ∧ 0 < c₂' ∧ 0 < c₁'' ∧ 0 < c₂'' ∧
      ∃ α₂ cc clo Cup Ccs : ℝ,
        Work.FTS.Nonlin.UnifIP
          (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ cc clo Cup Ccs := by
  -- the level-4 transfer data: the coefficients, the Cauchy–Schwarz constant and the
  -- coercivity constant of `IP4` (with `IP = IP4` explicit, unlike the existential headline)
  obtain ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'',
    αT, ccT, CCT, hαT, hccT, hCCT, hdat⟩ :=
    Work.FTS.CoercivityFix.Transfer.transfer_level4 hE1 hE2 CC₁ hCC₁ hCD₁ hok₁ hok₂ hok₃
  -- the `lo`/`up`/`Dz_self` constants on `CoerAdm`
  obtain ⟨αB, clo, Cup, Cdz, hαB, hclo, hCup, hCdz, hlo, hup, hdz⟩ :=
    Work.FTS.CoercivityFix.Assembly.V_bounds hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂''
  -- the membership-free/algebraic clauses
  obtain ⟨hsymm, hadd, hsmul, hcongr, hnonneg⟩ :=
    Work.FTS.CoercivityFix.Assembly.V_core (le_of_lt hc₁) (le_of_lt hc₂) (le_of_lt hc₁')
      (le_of_lt hc₂') (le_of_lt hc₁'') (le_of_lt hc₂'')
  refine ⟨c₁, c₂, c₁', c₂', c₁'', c₂'', hc₁, hc₂, hc₁', hc₂', hc₁'', hc₂'',
    min (1 / 4) (min αT αB), ccT, clo, Cup, max CCT Cdz, ?_⟩
  have hα₂ : 0 < min (1 / 4) (min αT αB) := lt_min (by norm_num) (lt_min hαT hαB)
  have hmemT : ∀ {α : ℝ}, α ∈ Set.Ioc 0 (min (1 / 4) (min αT αB)) →
      α ∈ Set.Ioc 0 αT := fun hα =>
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_left _ _))⟩
  have hmemB : ∀ {α : ℝ}, α ∈ Set.Ioc 0 (min (1 / 4) (min αT αB)) →
      α ∈ Set.Ioc 0 αB := fun hα =>
    ⟨hα.1, le_trans hα.2 (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hCCTl : CCT ≤ max CCT Cdz := le_max_left _ _
  have hCdzl : Cdz ≤ max CCT Cdz := le_max_right _ _
  refine ⟨⟨hα₂, hccT, hclo, hCup, lt_of_lt_of_le hCCT hCCTl⟩,
    hsymm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα f₁ f₂ g h₁ h₂ h₃
    exact hadd α hα.1 f₁ f₂ g h₁ h₂ h₃
  · intro α hα c f g h₁ h₂
    exact hsmul α hα.1 c f g h₁ h₂
  · intro α hα f f' g h₁ h₂ h
    exact hcongr α hα.1 f f' g h₁ h₂ h
  · intro α hα f hf
    exact hnonneg α hα.1 f hf
  · intro α hα f g hf hg
    have h := (hdat α (hmemT hα)).cs f g hf hg
    calc |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ CCT * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := h
      _ ≤ max CCT Cdz * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCCTl
            (Work.Spaces.HkNorm_nonneg α 4 f)) (Work.Spaces.HkNorm_nonneg α 4 g)
  · intro α hα f hf
    exact hlo α (hmemB hα) f hf
  · intro α hα f hf
    exact hup α (hmemB hα) f hf
  · intro α hα f hf
    exact (hdat α (hmemT hα)).coer f hf
  · intro α hα f hf
    have h := hdz α (hmemB hα) f hf
    have hsq : Work.Spaces.HkSq α 4 f = Work.FTS.Nonlin.Xn α f ^ 2 := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
        Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)]
    calc |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (Work.Spaces.Dz f) f|
        ≤ Cdz * Work.Spaces.HkSq α 4 f := h
      _ = Cdz * Work.FTS.Nonlin.Xn α f ^ 2 := by rw [hsq]
      _ ≤ max CCT Cdz * Work.FTS.Nonlin.Xn α f ^ 2 :=
          mul_le_mul_of_nonneg_right hCdzl (sq_nonneg _)

end Work.FTS.IPGen
