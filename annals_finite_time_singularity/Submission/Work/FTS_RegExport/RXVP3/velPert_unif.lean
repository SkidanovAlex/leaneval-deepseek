import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXVP3

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **`v2_velPert` with a `τ`-uniform constant** (the perturbation half of
`RXVP3.velVanish2_unif`).

This is `Work.FTS_RegExport.RXT.Slots.v2_velPert`
(`Submission/Work/FTS_RegExport/RXT/Slots/v2_velPert.lean`, proved, `sorry`-free) with the
horizon removed: instead of `∀ S > 0, ∃ M, ∀ τ ∈ Icc 0 S`, one single `M` works for every
`τ ≥ 0`.  The proof is a verbatim re-run, with the horizon chosen *inside* the `∀ τ`:

IMPORT `Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert` (its helper lemmas
`velPert_FK_eq`, `velPert_continuousOn_K`, `velPert_contDiffOn_Theta`, `velPert_mixed_sub_three`,
`velPert_hkMem_bound`, `velPert_limit_bound` are already public in namespace
`Work.FTS_RegExport.RXT`, so do NOT re-prove them) and copy the body of the final theorem
`v2_velPert`, editing ONLY the quantifier plumbing, as follows.  Put the file in namespace
`Work.FTS_RegExport.RXVP3`, `set_option autoImplicit false`, `set_option maxHeartbeats 1600000`,
and keep every hypothesis exactly as below (including the unused `hSol`, which `v2_velPert`'s
proof never touches) so that the rest of the proof copies unchanged.  Since the statement lives
in `Work.FTS_RegExport.RXVP3`, open or fully qualify the `Work.FTS_RegExport.RXT` helpers.

The witness of `v2_velPert` is `C4 * (max Ce 0 * (max C₀ 0 * (pExp α)^2))`, where
`obtain ⟨C4, hC40, hC4⟩ := velPert_hkMem_bound (pExp α)(...)` — it does **not** contain `S`.
So replace

  `intro S hS`
  `obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 S hS`
  `... refine ⟨C4 * (...), ?_⟩`
  `intro τ hτ z θ hz hθ hθ2 Q hQ j i hji`

by

  `refine ⟨C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)), ?_⟩`
  `intro τ hτ z θ hz hθ hθ2 Q hQ j i hji`
  `have hS : 0 < max τ 1 := lt_of_lt_of_le zero_lt_one (le_max_right τ 1)`
  `have hτS : τ ∈ Set.Icc (0:ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩`
  `obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 (max τ 1) hS`

and then (this is the *only* other change) route every horizon-local use through `hτS`:
`hApprox n τ hτ` ↦ `hApprox n τ hτS` (also inside `hReg`), `hJet τ hτ j i hji z' θ' hzθ` ↦
`hJet τ hτS j i hji z' θ' hzθ`, and every `hτ.1` (the `0 ≤ τ` component of the interval
membership, e.g. in `hOK.1.1.c4 τ hτ.1`, `hOK.1.2 τ hτ.1`, `contDiffOn_slice_PhiR_Q0 ... τ
hτ.1`, `Ftau_bounds ... τ hτ.1`, `contDiffOn_Ftau_Q0 ... τ hτ.1`) ↦ `hτ`.  The closing calls
`hMP τ hτ z θ hz hθ hθ2 ...` already take `hτ : 0 ≤ τ` and are copied verbatim.  Nothing else
changes; in particular the `ℋ⁴ → L^∞` trade-off `velPert_hkMem_bound`, the uniform `ℋ⁴`-bounds
on the approximants (`hReg`), the jet-convergence stack
(`v2_L12DzIterTendsto`, `v2_thetaJetsTendsto`, `v2_SlotJetsTendsto`, `v2_paramC2`,
`contDiffOn_three_L12`), and the three `velPert_limit_bound` calls are copied line for line — all
their constants are already `τ`-free (`max Ce 0`, `max C₀ 0`, `C4`, `CA1`). -/
theorem velPert_unif {α Ce C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    {g : Work.FTS.Galerkin.Fam} (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∃ M : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ)))),
          Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))),
          fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice g τ) (E (Work.FTS.Galerkin.slice g τ))) z θ
            / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1 := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the `ℋ⁴ → L^∞` trade-offs
  obtain ⟨CA1, hCA10, hA1⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  obtain ⟨C4, hC40, hC4⟩ := Work.FTS_RegExport.RXT.velPert_hkMem_bound hαG hαG1
  refine ⟨C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)), ?_⟩
  intro τ hτ z θ hz hθ hθ2 Q hQ j i hji
  have hS : 0 < max τ 1 := lt_of_lt_of_le zero_lt_one (le_max_right τ 1)
  have hτS : τ ∈ Set.Icc (0:ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩
  -- the class-`C` approximants of `LimApprox`
  obtain ⟨gn, B, L, hApprox, _hLip, hJet, _hμ⟩ := hOK.2 (max τ 1) hS
  -- ## regularity of the class-`C` approximants
  have hReg : ∀ n : ℕ, ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 ∧ Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4
          (slice (gn n) τ) ∧
      Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) ∧
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    intro n
    obtain ⟨hCn, hXn, _⟩ := hApprox n τ hτS
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact ⟨hCn.reg.of_le (by norm_num),
      Work.FTS.IPGen.HkMem_mono_le hCn.reg 4 (by norm_num) hCn.mem,
      hCn.bdry_le_six (by norm_num), le_trans hXn h2⟩
  -- ## the limit slice and its data
  have hF4 : ContDiffOn ℝ 4 (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    hOK.1.1.c4 τ hτ
  have hFmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice g τ) :=
    hOK.1.1.mem4 τ hτ
  have hFnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice g τ)
      ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := by
    have h2 : C₀ * (Work.FTS.Regularity.pExp α) ^ 2
        ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))
    exact le_trans (hOK.1.2 τ hτ) h2
  -- the `E`-jets of the limit slice
  obtain ⟨_hBsl, hE3lim, hEconv⟩ := hEL3 (fun n => slice (gn n) τ) (slice g τ) B
    (fun n => (hApprox n τ hτS).1) (fun n => (hApprox n τ hτS).2.2) hF4
    (fun j i hji z' θ' hzθ => hJet τ hτS j i hji z' θ' hzθ)
  -- ## `𝔽K` and `L₁₂` of the limit slice
  have hFKlim : ContDiffOn ℝ 2 (Work.Construction.FK (slice g τ)) (Set.Ioi 0) := by
    have hF2 : ContDiffOn ℝ 2 (Function.uncurry (slice g τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hF4.of_le (by norm_num)
    have hbase : ∀ (b : ℕ), b ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |Work.Spaces.mixed b 0 (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
      intro b hb z' θ' hz' hθ' hθ'2
      have h1 := hC4 (slice g τ) (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) hF4 hFmem hFnorm b 0 (by omega) z' θ'
        hz' hθ' hθ'2
      have h2 : C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * min z' 1 ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (mul_nonneg hC40 (mul_nonneg (le_max_right C₀ 0) (sq_nonneg (Work.FTS.Regularity.pExp α))))
      linarith [h1, h2]
    have hb : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
        |slice g τ z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.Dz (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) ∧
        |Work.Spaces.DzIter 2 (slice g τ) z' θ'| ≤ C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
      fun z' θ' hz' hθ' hθ'2 =>
        ⟨by simpa using hbase 0 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 1 (by norm_num) z' θ' hz' hθ' hθ'2,
         by simpa using hbase 2 (by norm_num) z' θ' hz' hθ' hθ'2⟩
    exact Work.FTS_RegExport.RXT.Slots.v2_paramC2 (φ := Work.Spaces.K)
      (C := C4 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      Work.FTS_RegExport.RXT.velPert_continuousOn_K hF2 hb
  have hL12lim : ContDiffOn ℝ 3 (Work.Construction.L12 (slice g τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFKlim
  have hΘ3lim : ContDiffOn ℝ 3
      (Function.uncurry (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) hL12lim
  have hElim3 : ContDiffOn ℝ 3 (Function.uncurry (fun z θ => E (slice g τ) z θ))
      Work.FTS.EllipticEst.Q0 := hE3lim
  -- ## `𝔽K`-jets of the approximants and the `Θ`-jets
  have hL12jets : ∀ j : ℕ, j ≤ 3 → ∀ z' : ℝ, 0 < z' →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice (gn n) τ) z) z' 0) Filter.atTop
        (nhds (Work.Spaces.DzIter j
          (fun z _ => Work.Construction.L12 (slice g τ) z) z' 0)) := by
    intro j hj z' hz'
    refine Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto (C0 := CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2))
      (F := fun n => slice (gn n) τ) (G := slice g τ) (by positivity) ?_ hF4 ?_ ?_ j hj z' hz'
    · intro n; exact (hReg n).1
    · intro n b a hba z'' θ'' hz'' hθ'' hθ''2
      have h1 := hA1 (slice (gn n) τ) (hReg n).1 (hReg n).2.1 (hReg n).2.2.1 b a hba
        z'' θ'' hz'' hθ'' hθ''2
      have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
          ≤ max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2 := (hReg n).2.2.2
      have hA0 : 0 ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) :=
        mul_nonneg hCA10 (div_nonneg (Real.rpow_nonneg hz''.le _) (by positivity))
      calc |Work.Spaces.mixed b a (slice (gn n) τ) z'' θ''|
          ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2)
              * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) := h1
        _ ≤ CA1 * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
            mul_le_mul_of_nonneg_left h2 hA0
        _ = CA1 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) * (z'' ^ ((3 : ℝ) / 2) / (1 + z'') ^ 2) := by ring
    · intro b a hab z'' θ'' hz'' hθ'' hθ''2
      exact hJet τ hτS b a (by omega) z'' θ'' ⟨hz'', hθ'', hθ''2⟩
  have hΘconv : ∀ j i : ℕ, j + i ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)) z' θ')
        Filter.atTop
        (nhds (Work.Spaces.mixed j i
          (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ)) z' θ')) :=
    Work.FTS_RegExport.RXT.Slots.v2_thetaJetsTendsto (α := Work.FTS.Regularity.pExp α)
      (F := fun n => slice (gn n) τ) (G := slice g τ) hL12jets
  -- ## `C³`-regularity of the residuals
  have hΦ3 : ∀ n : ℕ, ContDiffOn ℝ 3
      (Function.uncurry (fun z θ => E (slice (gn n) τ) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    exact ((hEll _ (hApprox n τ hτS).1).1.smooth).of_le (by norm_num)
  have hΘ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry
      (Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ)))
      Work.FTS.EllipticEst.Q0 := by
    intro n
    refine Work.FTS_RegExport.RXT.velPert_contDiffOn_Theta (α := Work.FTS.Regularity.pExp α) ?_
    refine Work.FTS_RegExport.RXT.contDiffOn_three_L12 ?_
    have h1 : ContDiffOn ℝ 2 (fun z => 3 * Work.Elliptic.Fstar (slice (gn n) τ) z)
        (Set.Ioi 0) := contDiffOn_const.mul ((hApprox n τ hτS).1.fsm 2)
    refine h1.congr fun z' _ => ?_
    rw [Work.FTS_RegExport.RXT.velPert_FK_eq]
  have hΞ3 : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        (E (slice (gn n) τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    intro n
    refine ((hΦ3 n).sub (hΘ3 n)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  have hΞ3lim : ContDiffOn ℝ 3 (Function.uncurry (fun z θ =>
      Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
        (E (slice g τ)) z θ)) Work.FTS.EllipticEst.Q0 := by
    refine ((hElim3.sub hΘ3lim)).congr fun p _ => ?_
    rcases p with ⟨z', θ'⟩
    simp only [Function.uncurry, Pi.sub_apply, Work.Construction.PhiTil]
  -- ## the jets of the residuals converge
  have hΞconv : ∀ b a : ℕ, a + b ≤ 3 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ') Filter.atTop
        (nhds (Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ')) := by
    intro b a hba z' θ' hz' hθ' hθ'2
    have hfun : (fun n : ℕ => Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            (E (slice (gn n) τ)) z θ) z' θ')
        = fun n : ℕ => Work.Spaces.mixed b a (fun z θ => E (slice (gn n) τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice (gn n) τ) z θ)
                z' θ' := by
      funext n
      exact Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba (hΦ3 n) (hΘ3 n) hz' hθ' hθ'2
    have hlim : Work.Spaces.mixed b a (fun z θ =>
          Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice g τ)
            (E (slice g τ)) z θ) z' θ'
        = Work.Spaces.mixed b a (fun z θ => E (slice g τ) z θ) z' θ'
            - Work.Spaces.mixed b a (fun z θ =>
                Work.Construction.Theta (Work.FTS.Regularity.pExp α) (slice g τ) z θ)
                z' θ' :=
      Work.FTS_RegExport.RXT.velPert_mixed_sub_three (b := b) (a := a) hba hElim3 hΘ3lim hz' hθ' hθ'2
    rw [hfun, hlim]
    exact (hEconv b a (by omega) z' θ' ⟨hz', hθ', hθ'2⟩).sub
      (hΘconv b a (by omega) z' θ' hz' hθ' hθ'2)
  -- ## the slot jets converge
  have hslotconv := Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto (α := Work.FTS.Regularity.pExp α)
    (Ξ := fun n => fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice (gn n) τ) (E (slice (gn n) τ)) z θ)
    (Ξlim := fun z θ => Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
      (slice g τ) (E (slice g τ)) z θ) hΞ3 hΞ3lim hΞconv
  -- ## the final liminf, slotwise
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
  rcases hQ with rfl | rfl | rfl
  · -- the `ℛ`-slot
    refine Work.FTS_RegExport.RXT.velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτS
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.R.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.R.1.1.of_le (by norm_num)) hGo.R.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).1
  · -- the `𝒱`-slot
    refine Work.FTS_RegExport.RXT.velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτS
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (Work.Construction.Vop
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.V.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.V.1.1.of_le (by norm_num)) hGo.V.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).2.1
  · -- the `𝒰/sin 2θ`-slot
    refine Work.FTS_RegExport.RXT.velPert_limit_bound (M := C4 * (max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2)))
      (A := fun n => fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          (E (slice (gn n) τ))) z θ / Real.sin (2 * θ)) ?_ ?_ j i hji z θ hz hθ hθ2
    · intro n j' i' hji' z' θ' hz' hθ' hθ'2
      obtain ⟨hCn, _⟩ := hApprox n τ hτS
      obtain ⟨hGo, _⟩ := hEll _ hCn
      have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
        Work.Spaces.HkNorm_nonneg _ _ _
      have hkey : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
          (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
              (E (slice (gn n) τ))) z θ / Real.sin (2 * θ))
          ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) := by
        refine le_trans hGo.U.2 ?_
        calc Ce * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
            ≤ max Ce 0 * Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
              mul_le_mul_of_nonneg_right (le_max_left Ce 0) hXn0
          _ ≤ max Ce 0 * (max C₀ 0 * (Work.FTS.Regularity.pExp α) ^ 2) :=
              mul_le_mul_of_nonneg_left (hReg n).2.2.2 (le_max_right Ce 0)
      exact hC4 _ _ (hGo.U.1.1.of_le (by norm_num)) hGo.U.1.2 hkey j' i' hji'
        z' θ' hz' hθ' hθ'2
    · intro b a hba z' θ' hz' hθ' hθ'2
      exact (hslotconv b a hba z' θ' hz' hθ' hθ'2).2.2

end Work.FTS_RegExport.RXVP3
