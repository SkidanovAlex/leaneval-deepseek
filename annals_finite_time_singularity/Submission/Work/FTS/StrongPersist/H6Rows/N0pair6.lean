import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45aRow
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T4bRowSlot
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0rowBndOwn
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdz
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ip4UnfoldSix
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfHardyA
import Submission.Work.FTS.StrongPersist.N6Trans_exists
import Submission.Work.FTS.StrongPersist.N6_L12H
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.hasDerivAt_wip_family
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `N0pair6` — the `N₀`-row of the level-six modulation table

Target (unchanged, as requested):

```
∃ K α₂, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
  ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ), H6Adm α f → HkMem α 7 f → Xn α f ≤ M →
  HkMem α 6 (N0 α (F_* + f) f) ∧
  |IP6 1…1 α (N0 α (F_* + f) f) f| ≤ K α^{-10} (1+M)^4 (1 + Sq6 α f)
```

## Route

`N0 α (F_*+f) f` splits (paper tex 1398–1422, `Construction.N0_eq_sum`) into the six terms
`N01+…+N06`; the two terms `N04`, `N05` split further (over `F = F_*+f`) into the `F_*`-halves
`N04a`, `N05a` and the `f`-halves `N04b`, `N05b`.  The seven pieces and their engines:

| piece | shape | engine |
|---|---|---|
| `N01+N02` | `8α² c2m z²Γ/(c(1+z)⁴)` | `FstarI12H6` (`HkMem` + norm `≤ Kα²`) |
| `N03` | `(1/α)·L₁₂(f)·f` | row `T3Row` (slot level) |
| `N04a` | `(3/(2α))·D_θF_*·L₁₂(f)` | `wprod6` + `IP6_cs_coeffs` |
| `N04b` | `(3/(2α))·L₁₂(f)·D_θf` | row `T4bRowSlot` |
| `N05a` | `c2m·D_zF_*·L₁₂(f)` | `wprod6` + `IP6_cs_coeffs` |
| `N05b` | `c2m·L₁₂(f)·D_zf` | row `T5bRow` |
| `N06` | `c2m·L₁₂(F_*)·D_zf` | row `T6RowGen` (`𝒲^{6,∞}` coefficient, `c2m_L12Fstar_W6`) |

The pairing `IP6 1…1 α (N0 …) f` is split with `IP6_congr` + `IP6_add`/`IP6_smul` (the
decomposition only holds on the open quadrant, which is all `IP6` sees), the row-pieces are
unfolded with `TransportS.ip4_unfold_bound` / `SlotSum_six_le`, and the `F_*`-coefficient pieces
are bounded by Cauchy–Schwarz (`IP6_cs_coeffs`) after the `𝒲^{6,∞}`-priced product rule
`wprod6`.
-/

/-- The full profile `F = F_* + f` of the modulation (`Construction.Ftot`). -/
def N0F (α : ℝ) (f : Work.FTS.Galerkin.Fn) : Work.FTS.Galerkin.Fn :=
  fun z θ => Work.Construction.Fstar α z θ + f z θ








/-- The additivity of `∂_θ` along `F_* + f` on the open quadrant. -/
theorem N0pair6_pth_add {α : ℝ} (f : Work.FTS.Galerkin.Fn)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (N0F α f) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth f z θ := by
  intro z θ hQ
  obtain ⟨hz, hθ⟩ := hQ
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have h1 : DifferentiableAt ℝ (fun θ' => Work.Construction.Fstar α z θ') θ :=
    ((hFsm.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have h2 : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    ((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  simp only [Work.Spaces.pth, N0F]
  exact deriv_add h1 h2

/-- The additivity of `z∂_z` along `F_* + f` on the open quadrant. -/
theorem N0pair6_Dz_add {α : ℝ} (f : Work.FTS.Galerkin.Fn)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz (N0F α f) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ := by
  intro z θ hQ
  obtain ⟨hz, hθ⟩ := hQ
  have hFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have h1 : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z :=
    ((hFsm.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have h2 : DifferentiableAt ℝ (fun z' => f z' θ) z :=
    ((hf.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hpz : Work.Spaces.pz (N0F α f) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz f z θ := by
    simp only [Work.Spaces.pz, N0F]
    exact deriv_add h1 h2
  simp only [Work.Spaces.Dz, hpz]
  ring


/-! ## From a per-slot row to the pairing

The rows `T3Row`, `T4bRowSlot`, `T5bRow`, `T6RowGen` (and the Cauchy–Schwarz route for the
`F_*`-coefficient pieces) all bound the *leaf slot pairings* of one piece `g` against `f`.
This lemma converts such a per-slot row into the bound on the whole pairing, through the
unfolding `IP6 1…1 α = IPn α 5` and `ip4_unfold_bound` / `SlotSum_six_le` (28 slots · 3 leaf
weights = 84). -/


/-- **The decomposition of `N₀ α (F_*+f) f` into the seven pieces of the row**, on the open
quadrant, in the `NA`/`NP` shapes consumed by the row engines. -/
theorem N0pair6_decompSum_Qd {α : ℝ} (f : Work.FTS.Galerkin.Fn)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (N0F α f) f z θ
        = Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0Sum α f z θ := by
  intro z θ hQ
  have hpth := N0pair6_pth_add (α := α) f hf z θ hQ
  have hDz := N0pair6_Dz_add (α := α) f hf z θ hQ
  simp only [Work.Construction.N0, Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0Sum,
    Work.FTS.StrongPersist.H6Pair6Aux.NA1, Work.FTS.StrongPersist.H6Pair6Aux.NP3,
    Work.FTS.StrongPersist.H6Pair6Aux.NP4a, Work.FTS.StrongPersist.H6Pair6Aux.NP4b,
    Work.FTS.StrongPersist.H6Pair6Aux.NP5a, Work.FTS.StrongPersist.H6Pair6Aux.NP5b,
    Work.FTS.StrongPersist.H6Pair6Aux.NP6, Work.FTS.StrongPersist.H6Pair6Aux.NA4,
    Work.FTS.StrongPersist.H6Pair6Aux.NA5, Work.FTS.StrongPersist.H6Pair6Aux.NA6,
    Pi.add_apply, Pi.sub_apply, N0F, Work.Construction.Fstar, Work.Spaces.Dth,
    Work.Construction.s2]
  rw [hpth, hDz]
  ring

theorem N0pair6 : ∃ K α₂ : ℝ, 0 < K ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.Spaces.HkMem α 7 f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      Work.Spaces.HkMem α 6
          (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) ∧
      |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f) f|
        ≤ K * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Sq6 α f) := by
  obtain ⟨CAdz, hCAdz, rowAdz⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6Aux.RowAdz
  obtain ⟨CNA, hCNA, hNA6sig⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6Aux.NA6sig
  obtain ⟨C3, hC3, row3r⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T3Row
  obtain ⟨C4b, hC4b, row4br⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T4bRowSlot
  obtain ⟨C5b, hC5b, row5br⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.row_l12_dz
  obtain ⟨C45, hC45, row45r⟩ := Work.FTS.StrongPersist.H6Pair6Aux.T45aRow
  obtain ⟨K12, hK12, hF12⟩ := Work.FTS.StrongPersist.H6Rows.FstarI12H6
  obtain ⟨Cd1, hCd1, hDthF⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨Cd2, hCd2, hDzF⟩ := Work.FTS.StrongPersist.H6Pair6Aux.c2mDzFstar_W6
  refine ⟨(3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * (84 * ((K12 + 1) + (C3 + 1)
      + ((3 / 2) * (C45 * Cd1 + 1)) + ((3 / 2) * (C4b + 1)) + (C45 * Cd2 + 1) + (C5b + 1)
      + (CAdz * CNA + 1))) + 1, 1, by positivity, one_pos, le_rfl, ?_⟩
  intro α hαIoc f M hAdm hm7 hXle
  have hα0 : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hsmf, hm6⟩ := hAdm.reg
  have hvan : Work.Spaces.VanishTheta f := hAdm.vanish
  have hax : ∀ θ ∈ Work.Spaces.Iθ, f 0 θ = 0 ∧ Work.Spaces.pz f 0 θ = 0 := hAdm.axis
  have hl12 : Work.Construction.L12 f 0 = 0 := hAdm.l12
  refine ⟨Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0mem6Own α f hAdm hm7 hα0 hα1, ?_⟩
  -- ## the smoothness of `L₁₂(f)` and of the pieces
  have hL7 : ContDiffOn ℝ 7 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) := by
    have h := Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 7 f hα0 hα1 hsmf hm7 (by norm_num)
    exact h.congr (fun z _ => (congrFun (Work.FTS.H2.constructionL12_eq_ellipticL12 f) z).symm)
  have hL6 : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 f z) (Set.Ioi 0) :=
    hL7.of_le (by norm_num)
  obtain ⟨hsm3, hsm4a, hsm4b, hsm5a, hsm5b, hsm6'⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0piecesSmooth (α := α) hsmf hL6
  have hf7 : ContDiffOn ℝ 7 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsmf 7
  have hf6 : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsmf 6
  have hu7 : ContDiffOn ℝ 7 (Function.uncurry (fun z θ =>
      Work.Construction.N0 α (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0SumSmooth (α := α) hsmf hL7).congr
      (fun p hp => by
        obtain ⟨z, θ⟩ := p
        exact N0pair6_decompSum_Qd f hsmf z θ hp)
  -- ## the memberships
  have h12mem : Work.Spaces.HkMem α 6 (fun z θ => Work.FTS.StrongPersist.H6Pair6Aux.NA1 α z θ) :=
    (hF12 α hα0 hα1).1
  have h12bd : Work.Spaces.HkNorm α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NA1 α)
      ≤ K12 * α ^ (2 : ℝ) := by
    have h := (hF12 α hα0 hα1).2
    rw [← Real.rpow_natCast α 2] at h
    exact h
  obtain ⟨hm3, hm4a, hm4b, hm5a, hm5b, hm6p⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0piecesMem6 hα0 hα1 hAdm hm7
  obtain ⟨hWl4mem, hWl4raw⟩ := hDthF α hα0 hα1
  obtain ⟨hWl5mem, hWl5⟩ := hDzF α hα0 hα1
  have hWl4 : Work.Spaces.WlInf α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NA4 α)
      ≤ Cd1 * α ^ (2 : ℝ) := by
    have h := hWl4raw
    rw [← Real.rpow_natCast α 2] at h
    exact h
  -- ## the rows instantiated at `f`
  have hrowcs : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => Work.FTS.StrongPersist.H6Pair6Aux.NA1 α z θ) f|
        ≤ Work.Spaces.HkNorm α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NA1 α)
          * Work.Spaces.HkNorm α 6 f :=
    fun a b ρ hab hρ => Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.slot_cs6 hα0 hab hρ
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α) hsmf h12mem hm6
  have hrow3 : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.L12 f z * f z θ) f|
        ≤ C3 * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) :=
    fun a b ρ hab hρ => row3r α hαIoc f a b ρ hsmf hm6 hm7 hvan hax hl12 hab hρ
  have hrow4b : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.L12 f z * Work.Spaces.Dth f z θ) f|
        ≤ C4b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) :=
    fun a b ρ hab hρ => row4br α hαIoc f a b ρ hsmf hm6 hm7 hvan hax hl12 hab hρ
  have hrow45 : ∀ (A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K → a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.L12 f z * A z θ) f|
        ≤ C45 * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) :=
    fun A a b ρ K hA hAmem hAle hab hρ =>
      row45r α hαIoc f A a b ρ K hsmf hm6 hm7 hvan hax hl12 hA hAmem hAle hab hρ
  have hrow5b : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 f z
          * Work.Spaces.Dz f z θ) f|
        ≤ C5b * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) :=
    fun a b ρ hab hρ => row5br α hαIoc f a b ρ hsmf hm6 hm7 hvan hax hl12 hab hρ
  have hrow6 : ∀ (A : ℝ → ℝ → ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → 0 ≤ K →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
        |Work.Spaces.mixed j i A z θ| ≤ K * (if i = 0 then 1 else Real.sin (2 * θ))) →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => A z θ * Work.Spaces.Dz f z θ) f|
        ≤ CAdz * K * α ^ (-(3 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f) :=
    fun A a b ρ K hA hK hAbd hab hρ =>
      rowAdz α hαIoc f A a b ρ K hsmf hm6 hm7 hA hK hAbd hab hρ
  have hNA6 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ j i : ℕ, i + j ≤ 6 →
      |Work.Spaces.mixed j i (Work.FTS.StrongPersist.H6Pair6Aux.NA6 α) z θ|
        ≤ (CNA * α) * (if i = 0 then 1 else Real.sin (2 * θ)) := by
    intro z θ hz h1 h2 j i hij
    have h := hNA6sig α hαIoc z θ hz h1 h2 j i hij
    simpa only [Work.FTS.StrongPersist.H6Pair6Aux.NA6] using h
  -- ## the per-slot bound
  have hslotSum : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0Sum α f z θ) f|
        ≤ ((K12 + 1) + (C3 + 1) + ((3 / 2) * (C45 * Cd1 + 1)) + ((3 / 2) * (C4b + 1))
            + (C45 * Cd2 + 1) + (C5b + 1) + (CAdz * (CNA * α) + 1))
          * Work.FTS.StrongPersist.H6Pair6Aux.NFact α f :=
    Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0rowBounds6 (α := α) hα0 hα1 hf6 hm6
      C3 C4b C5b C45 CAdz K12 Cd1 Cd2 (CNA * α) hC3.le hC4b.le hC5b.le hC45.le hCAdz.le
      hK12.le hCd1.le hCd2.le (mul_pos hCNA hα0).le
      hrowcs h12bd hrow3 hrow4b hrow45 hrow5b hrow6 hm3 hm4a hm4b hm5a hm5b hm6p
      hsm3 hsm4a hsm4b hsm5a hsm5b hsm6' hWl4mem hWl5mem hWl4 hWl5 h12mem hNA6
  set KS : ℝ := (K12 + 1) + (C3 + 1) + ((3 / 2) * (C45 * Cd1 + 1))
    + ((3 / 2) * (C4b + 1)) + (C45 * Cd2 + 1) + (C5b + 1) + (CAdz * CNA + 1) with hKS
  have hNFnn : (0 : ℝ) ≤ Work.FTS.StrongPersist.H6Pair6Aux.NFact α f := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NFact]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _) (by positivity))
      (by linarith [Work.Spaces.HkSq_nonneg α 6 f])
  have hslot : ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.N0 α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f|
        ≤ KS * Work.FTS.StrongPersist.H6Pair6Aux.NFact α f := by
    intro a b ρ hab hρ
    have h1 := hslotSum a b ρ hab hρ
    have h2 : Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.N0 α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f
        = Work.FTS.TransportS.slotPairing ρ a b
            (fun z θ => Work.FTS.StrongPersist.H6Rows.N0pair6Aux.N0Sum α f z θ) f :=
      Work.FTS.StrongPersist.H6Pair6Aux.slotPairing_congr_Qd
        (fun z θ hzθ => N0pair6_decompSum_Qd f hsmf z θ hzθ)
    rw [h2]
    refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ hNFnn)
    rw [hKS]
    have hstep : CAdz * (CNA * α) ≤ CAdz * CNA := by
      have hαC : CNA * α ≤ CNA * 1 := mul_le_mul_of_nonneg_left hα1 hCNA.le
      nlinarith [hαC, hCAdz]
    linarith
  -- ## the slot sum and the unfolding
  have hsum := Work.FTS.StrongPersist.SlotSum_six_le α
    (fun z θ => Work.Construction.N0 α
      (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f
    (KS * Work.FTS.StrongPersist.H6Pair6Aux.NFact α f)
    (mul_nonneg (by positivity) hNFnn) hslot
  have hunf := Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ip4UnfoldSix α
    (fun z θ => Work.Construction.N0 α
      (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f hu7 hf7
  have hIP6 := Work.FTS.StrongPersist.IP6_one_eq_IPn_five α
    (fun z θ => Work.Construction.N0 α
      (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f
  have hpair : |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      (fun z θ => Work.Construction.N0 α
        (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f|
      ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22
        * (84 * (KS * Work.FTS.StrongPersist.H6Pair6Aux.NFact α f)) := by
    rw [hIP6]
    calc |Work.FTS.TransportS.IPn α 5
          (fun z θ => Work.Construction.N0 α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f|
        ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22
            * Work.FTS.TransportS.SlotSum α 6
              (fun z θ => Work.Construction.N0 α
                (fun z θ => Work.Construction.Fstar α z θ + f z θ) f z θ) f := hunf
      _ ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22
            * (84 * (KS * Work.FTS.StrongPersist.H6Pair6Aux.NFact α f)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
  refine le_trans hpair ?_
  -- ## the arithmetic: `NFact α f ≤ α^{-10}(1+M)^4(1+Sq6 α f)`
  have hX0 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := by
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
    exact Real.sqrt_nonneg _
  have h1 : (1 + Work.FTS.Nonlin.Xn α f) ^ 4 ≤ (1 + M) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  have h2 : (0 : ℝ) ≤ α ^ (-(10 : ℝ)) := Real.rpow_nonneg hα0.le _
  have h3 : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 6 f :=
    by linarith [Work.Spaces.HkSq_nonneg α 6 f]
  have hNFstep : Work.FTS.StrongPersist.H6Pair6Aux.NFact α f
      ≤ α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NFact]
    calc α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4
          * (1 + Work.Spaces.HkSq α 6 f)
        = (α ^ (-(10 : ℝ)) * (1 + Work.FTS.Nonlin.Xn α f) ^ 4)
            * (1 + Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ (α ^ (-(10 : ℝ)) * (1 + M) ^ 4)
            * (1 + Work.Spaces.HkSq α 6 f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
      _ = α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f) := by ring
  calc (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22
        * (84 * (KS * Work.FTS.StrongPersist.H6Pair6Aux.NFact α f))
      = (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * (84 * KS)
          * Work.FTS.StrongPersist.H6Pair6Aux.NFact α f := by ring
    _ ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * (84 * KS)
          * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left hNFstep (by positivity)
    _ ≤ ((3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * (84 * ((K12 + 1) + (C3 + 1)
          + ((3 / 2) * (C45 * Cd1 + 1)) + ((3 / 2) * (C4b + 1)) + (C45 * Cd2 + 1)
          + (C5b + 1) + (CAdz * CNA + 1))) + 1)
          * (α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.Spaces.HkSq α 6 f)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hKS]
        linarith
    _ = ((3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * (84 * ((K12 + 1) + (C3 + 1)
          + ((3 / 2) * (C45 * Cd1 + 1)) + ((3 / 2) * (C4b + 1)) + (C45 * Cd2 + 1)
          + (C5b + 1) + (CAdz * CNA + 1))) + 1)
          * α ^ (-(10 : ℝ)) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Sq6 α f) := by
        rw [Work.FTS.StrongPersist.Sq6]; ring

end

end Work.FTS.StrongPersist.H6Rows
