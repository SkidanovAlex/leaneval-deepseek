import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.Slots.v2_starUop
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXVP3.velPert_unif

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXVP3

open Work.FTS.Galerkin (Fn Fam slice)

/-- **`velVanish2` with a `τ`-uniform constant.**  This is `Work.FTS_RegExport.RXT.velVanish2`
(`Submission/Work/FTS_RegExport/RXT/velVanish2.lean`) with the quantifier
`∀ S > 0, ∃ M, ∀ τ ∈ Icc 0 S` replaced by `∃ M, ∀ τ, 0 ≤ τ →`.

PROOF ROUTE (read the two files first).  `RXT/velVanish2.lean` splits
`Φ̃ = Φ̃_* + Φ̃_pert` (`v2_phiTil_split`) and combines the star bounds (`v2_starRop_mixed`,
`starVop`, `v2_starUop` — all `τ`-free already) with `v2_velPert` (which is horizon-local but whose
witness `C4 * (max Ce 0 * (max C₀ 0 * (pExp α)^2))` does **not** contain `S`).  So the uniform
statement follows by re-running the `v2_velPert` proof
(`Submission/Work/FTS_RegExport/RXT/Slots/v2_velPert.lean`, whose five helper lemmas
`velPert_FK_eq`, `velPert_continuousOn_K`, `velPert_contDiffOn_Theta`, `velPert_mixed_sub_three`,
`velPert_hkMem_bound`, `velPert_limit_bound` are public in namespace `Work.FTS_RegExport.RXT`)
with the horizon chosen *inside* the `∀ τ`: for each `τ ≥ 0` instantiate
`hOK.2 (max τ 1) (lt_of_lt_of_le zero_lt_one (le_max_right τ 1))` to get the class-`C`
approximants `gn` with `Xn α (slice (gn n) τ) ≤ C₀ α²` and the order-≤4 jet convergence
`hJet τ ⟨hτ, le_max_left τ 1⟩`, then take the liminf slotwise with
`velPert_limit_bound` at the constant `C4 * (max Ce 0 * (max C₀ 0 * (pExp α)^2))`
(`C4` from `velPert_hkMem_bound`) and the three slot-jet convergences
(`RXT.Slots.v2_SlotJetsTendsto`, `v2_L12DzIterTendsto`, `v2_thetaJetsTendsto`,
`v2_paramC2`, `contDiffOn_three_L12`, `contDiffOn_slice_PhiR_Q0` for the `E`-jets of the
limit slice via `hEL3`).  `hSol` and `hdat` are not needed for the perturbation half; `hμ` only
enters the star half (which is `τ`-free). -/
theorem velVanish2_unif {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    ∃ M : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ Q ∈ ({(Work.Construction.Rop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ)),
          Work.Construction.Vop
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ),
          fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g)
              (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ) z θ / Real.sin (2 * θ)} :
            Set (ℝ → ℝ → ℝ)),
        ∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i Q z θ| ≤ M * min z 1 := by
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the star half (already `τ`-free)
  have hStarR := Work.FTS_RegExport.RXT.v2_starRop_mixed hαG hαG1 hStar
  obtain ⟨CV, hCV0, hCV⟩ := Work.FTS_RegExport.RXT.starVop hαG hαG1 hStar
  obtain ⟨CU, hCU0, hCU⟩ := Work.FTS_RegExport.RXT.Slots.v2_starUop hαG hαG1 hStar
  -- the perturbation half, with a `τ`-uniform constant
  obtain ⟨MP, hMP⟩ := velPert_unif (Φs := Φs) (E := E) hα hα13 hEll hEL3 hSol hOK
  refine ⟨2 * 10 ^ 4 * (max Cs 1 * Work.FTS.Regularity.pExp α)
    + CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
    + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP, ?_⟩
  intro τ hτ z θ hz hθ hθ2 Q hQ j i hji
  -- the common infrastructure
  set CR : ℝ := 2 * 10 ^ 4 * (max Cs 1 * Work.FTS.Regularity.pExp α) with hCRdef
  have hQmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- the pointwise split of the stream functions on the quadrant
  have hsplit : ∀ z₁ θ₁ : ℝ, (z₁, θ₁) ∈ Work.FTS.EllipticEst.Q0 →
      Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ z₁ θ₁
        = Work.FTS_RegExport.RXT.v2_PhiStar α Φs z₁ θ₁
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ z₁ θ₁ :=
    fun z₁ θ₁ hp => Work.FTS_RegExport.RXT.v2_phiTil_split (C₀ := C₀) hα hα13 hOK hτ z₁ θ₁ hp
  have hsplitFun : Work.FTS_RegExport.RXR5.AgreeOnQ (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) :=
    fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => hsplit z₁ θ₁ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz₁, hθ₁, hθ₁2⟩)
  -- `C³` of the full and of the star residual, hence of the perturbation residual
  have hPhi3 : ContDiffOn ℝ 3
      (Function.uncurry (slice (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) τ))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_slice_PhiR_Q0 (α := α) (C₀ := C₀) (Cs := Cs)
      hEL3 hStar hOK τ hτ
  have hFK2 : ContDiffOn ℝ 2
      (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) := by
    obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXT.Ftau_bounds (Φs := Φs) (E := E) hα hα13 hOK τ hτ
    exact Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta (φ := Work.Spaces.K)
      Work.FTS_RegExport.RXT.v2_continuousOn_K_Iθ
      (Work.FTS_RegExport.RXT.contDiffOn_Ftau_Q0 (Φs := Φs) (E := E) hα hα13 hOK τ hτ)
      (fun z₁ θ₁ hz₁ hθ₁ hθ₁2 => ⟨(hC z₁ θ₁ hz₁ hθ₁ hθ₁2).1, (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.1,
        (hC z₁ θ₁ hz₁ hθ₁ hθ₁2).2.2⟩)
  have hL12 : ContDiffOn ℝ 3
      (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ)) (Set.Ioi 0) :=
    Work.FTS_RegExport.RXT.contDiffOn_three_L12 hFK2
  have hTheta3 : ContDiffOn ℝ 3 (Function.uncurry (Work.Construction.Theta
      (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) τ))) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ =>
        (1 / (4 * Work.FTS.Regularity.pExp α)) * Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul (Real.contDiff_sin.comp
        (contDiff_const.mul contDiff_snd)).contDiffOn
    have h2 : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) p.1) Work.FTS.EllipticEst.Q0 :=
      hL12.comp contDiffOn_fst (fun p hp => hp.1)
    refine (h1.mul h2).congr ?_
    intro p _
    simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  have hFull3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ))
      Work.FTS.EllipticEst.Q0 := hPhi3.sub hTheta3
  have hStar3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hPert3 : ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))
      Work.FTS.EllipticEst.Q0 := by
    refine (hFull3.sub hStar3).congr ?_
    intro p hp
    obtain ⟨z₁, θ₁⟩ := p
    simp only [Function.uncurry]
    linarith [hsplit z₁ θ₁ hp]
  have hStarC1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) Work.FTS.EllipticEst.Q0 :=
    hStar3.of_le (by norm_num)
  have hPertC1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) Work.FTS.EllipticEst.Q0 :=
    hPert3.of_le (by norm_num)
  have hstarR : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z₁ θ₁| ≤ CR * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 => by
      rw [hCRdef]
      exact hStarR j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2
  have hstarV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z₁ θ₁|
        ≤ (CV * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCV j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2
  have hstarU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)) z₁ θ₁|
        ≤ (CU * (max Cs 1 * Work.FTS.Regularity.pExp α)) * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 => hCU j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2
  have hpertR : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      hMP τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.FTS_RegExport.RXT.v2_SlotR α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) (by exact Or.inl rfl) j i hji
  have hpertV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      hMP τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.FTS_RegExport.RXT.v2_SlotV α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) (by exact Or.inr (Or.inl rfl)) j i hji
  have hpertU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z₁ θ₁ : ℝ, 0 < z₁ → 0 < θ₁ → θ₁ < Real.pi / 2 →
      |Work.Spaces.mixed j i (Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) z₁ θ₁| ≤ MP * min z₁ 1 :=
    fun j i hji z₁ θ₁ hz₁ hθ₁ hθ₁2 =>
      hMP τ hτ z₁ θ₁ hz₁ hθ₁ hθ₁2 (Work.FTS_RegExport.RXT.v2_SlotU α
        (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)) (by exact Or.inr (Or.inr rfl)) j i hji
  have hSC2R : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.NonlinRows.RopW_Rop (α := Work.FTS.Regularity.pExp α)
      (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).1).of_le
        (by simp [Work.Stability.smoothOrder])
  have hSC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hSC2U : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α
      (Work.FTS_RegExport.RXT.v2_PhiStar α Φs))) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.PhiStar.CoreAux.fields_smooth hαG hαG1 hStar.smooth).2.2.2.2.1.of_le
      (by simp [Work.Stability.smoothOrder])
  have hPC2R : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α
      (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop hPert3
  have hPC2V : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α
      (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hPert3
  have hPC2U : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α
      (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ))) Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
      (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := Work.FTS.Regularity.pExp α) hPert3)
  have hmm : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
  have hC0 : (0 : ℝ) ≤ CR := by
    rw [hCRdef]; positivity
  have harith : ∀ M₀ : ℝ,
      M₀ ≤ CR + CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
        + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP →
      M₀ * min z 1 ≤ (CR + CV * (max Cs 1 * Work.FTS.Regularity.pExp α)
        + CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP) * min z 1 :=
    fun M₀ hM₀ => mul_le_mul_of_nonneg_right hM₀ hmm
  have hCVa : 0 ≤ CV * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCV0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  have hCUa : 0 ≤ CU * (max Cs 1 * Work.FTS.Regularity.pExp α) :=
    mul_nonneg hCU0 (le_of_lt (mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right Cs 1)) hαG))
  -- the three cases
  have hQ' : Q = Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      ∨ Q = Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
      ∨ Q = Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ) := by
    have h := hQ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h
  rcases hQ' with hQ | hQ | hQ
  · -- the `ℛ`-slot
    subst hQ
    have heq : Set.EqOn
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
          + Work.FTS_RegExport.RXT.v2_SlotR α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      simp only [Function.uncurry, Pi.add_apply, Work.FTS_RegExport.RXT.v2_SlotR]
      rw [Work.FTS_RegExport.RXR5.Rop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
        (h := hsplitFun) (Φ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Φ' := Work.FTS_RegExport.RXT.v2_PhiStar α Φs
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
      exact Work.FTS_RegExport.RXT.v2_rop_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
    have hres := Work.FTS_RegExport.RXT.v2_slot_bound_of_split heq hSC2R hPC2R
      hstarR hpertR j i hji z θ hz hθ hθ2
    exact le_trans hres (harith (CR + MP) (by linarith [hCVa, hCUa]))
  · -- the `𝒱`-slot
    subst hQ
    have heq : Set.EqOn
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
          + Work.FTS_RegExport.RXT.v2_SlotV α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      simp only [Function.uncurry, Pi.add_apply, Work.FTS_RegExport.RXT.v2_SlotV]
      rw [Work.FTS_RegExport.RXR5.Vop_congr_of_agreeOnQ (h := hsplitFun)
        (Φ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Φ' := Work.FTS_RegExport.RXT.v2_PhiStar α Φs
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
      exact Work.FTS_RegExport.RXT.v2_vop_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
    have hres := Work.FTS_RegExport.RXT.v2_slot_bound_of_split heq hSC2V hPC2V
      hstarV hpertV j i hji z θ hz hθ hθ2
    exact le_trans hres
      (harith (CV * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP) (by linarith [hCUa]))
  · -- the `𝒰/sin 2θ`-slot
    subst hQ
    have heq : Set.EqOn
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α
          (Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)))
        (Function.uncurry (Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiStar α Φs)
          + Work.FTS_RegExport.RXT.v2_SlotU α (Work.FTS_RegExport.RXT.v2_PhiPert α E g τ)))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨z₁, θ₁⟩ := p
      obtain ⟨hz₁, hθ₁, hθ₁2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      simp only [Function.uncurry, Pi.add_apply, Work.FTS_RegExport.RXT.v2_SlotU]
      rw [Work.FTS_RegExport.RXR5.Uop_congr_of_agreeOnQ (α := Work.FTS.Regularity.pExp α)
        (h := hsplitFun) (Φ := Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ)
        (Φ' := Work.FTS_RegExport.RXT.v2_PhiStar α Φs
          + Work.FTS_RegExport.RXT.v2_PhiPert α E g τ) hz₁ hθ₁ hθ₁2]
      exact Work.FTS_RegExport.RXT.v2_uop_div_add_at hStarC1 hPertC1 ⟨hz₁, hθ₁, hθ₁2⟩
    have hres := Work.FTS_RegExport.RXT.v2_slot_bound_of_split heq hSC2U hPC2U
      hstarU hpertU j i hji z θ hz hθ hθ2
    exact le_trans hres
      (harith (CU * (max Cs 1 * Work.FTS.Regularity.pExp α) + MP) (by linarith [hCVa]))

end Work.FTS_RegExport.RXVP3
