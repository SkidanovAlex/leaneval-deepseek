import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompLeaf.fixRadon
import Submission.Work.EKLCompLeaf.step0_nontrivial
import Submission.Work.EKLCompLeaf.equiv_transfer
import Submission.Work.EKLCompLeaf.luzin_riesz_of_radon
import Submission.Work.EKLCompSetup.scaling_F1
import Submission.Work.EKLCompSetup.measurable_leafMass
import Submission.Work.EKLCompSetup.exists_X2
import Submission.Work.EKLCompSetup.exists_X3
import Submission.Work.EKLCompSetup.exists_Xrho
import Submission.Work.EKLContract.Lemmas.isHoro_Uij

/-!
# `Work.EKLCompSetup.exists_of` — Steps 1–4 of the low-entropy method

`C8Setup μ` (see `Submission/Work/EKLComp/C8Defs.lean`) bundles the data produced by
Steps 1–4 of EKL §4.2–4.5 (`ROUTE_LEAD.md` §5) together with the two facts (F1)/(F2) coming
from the `A`-covariance clause (U7) of `P_Leafwise` and Step 0:

* the leafwise system `ν` for `U_01`, finite on compacts everywhere (`fixRadon`);
* the conull set `X''` of (U7) on which the scaling relation (F1) and the centraliser
  identity (F2) hold, and on which Step 0 gives `ν (u s • x) ≠ ν x` for `s ≠ 0`;
* the constants `C, ε, ρ`;
* the Luzin compact `X₁`, the maximal-inequality set `X₂`, the set `𝒳(ρ)`, the flow-averaging
  compact `X₃`;
* the null set `N` and the conull cross-section set `B`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Matrix
open Work.EKLContract Work.EKLComp

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLCompSetup

/-! ## Auxiliary definitions and facts -/

/-- The exponent vector `t = (-1,1,0)`; `aDiag (τ • t0) = phi τ`. -/
def t0 : Fin 3 → ℝ := ![-1, 1, 0]

theorem isHoro_Uij_h01 : IsHoro (Uij Work.EKLComp.h01) :=
  Work.EKLContract.Lemmas.isHoro_Uij Work.EKLComp.h01

theorem tendsto_conj_Uij_h01 (u : SL3) (hu : u ∈ (Uij Work.EKLComp.h01 : Set SL3)) :
    Tendsto (fun n : ℕ => aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) atTop (𝓝 1) := by
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff Work.EKLComp.h01 u).mp hu
  exact Work.EKLContract.Lemmas.horoUij_tendsto_conj t0 Work.EKLComp.h01 (by norm_num [t0]) s

/-- `ballU Work.EKLComp.h01 0 = {1}`: the plaque of radius `0` is the identity. -/
theorem ballU_zero : (ballU Work.EKLComp.h01 0 : Set SL3) = {1} := by
  ext g
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs0 : s = 0 := by
      have := hs.1; have := hs.2; linarith
    subst hs0
    exact Work.EKLComp.u_zero
  · rintro rfl
    exact ⟨0, ⟨by norm_num, by norm_num⟩, Work.EKLComp.u_zero⟩

/-- `nuR` of the Dirac mass at the identity is the Dirac mass at `0`; stated on `[-1,1]`. -/
theorem nuR_dirac_one_Icc :
    (nuR (Measure.dirac (1 : SL3))).real (Set.Icc (-1) 1) = 1 := by
  have hmem : (1 : SL3) ∈ (Uij Work.EKLComp.h01 : Set SL3) := by
    rw [← Work.EKLComp.u_zero]; exact Work.EKLComp.u_mem 0
  have hbel : (1 : SL3) ∈
      Work.EKLComp.par ⁻¹' Set.Icc (-1 : ℝ) 1 ∩ (Uij Work.EKLComp.h01 : Set SL3) :=
    ⟨by simp only [Set.mem_preimage, Work.EKLComp.par_one]; norm_num, hmem⟩
  show ((nuR (Measure.dirac (1 : SL3))) (Set.Icc (-1) 1)).toReal = 1
  rw [Work.EKLComp.nuR, Measure.map_apply Work.EKLComp.measurable_par measurableSet_Icc,
    Measure.restrict_apply (Work.EKLComp.measurable_par measurableSet_Icc),
    Measure.dirac_apply_of_mem hbel, ENNReal.toReal_one]

/-- `nuR ν {0} = ν {1}`: the atom at `0` of the parameter measure is the atom at the identity. -/
theorem nuR_singleton_zero (ν : Measure SL3) : nuR ν {0} = ν ({1} : Set SL3) := by
  rw [Work.EKLComp.nuR, Measure.map_apply Work.EKLComp.measurable_par (measurableSet_singleton 0),
    Measure.restrict_apply (Work.EKLComp.measurable_par (measurableSet_singleton 0))]
  congr 1
  ext g
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
  constructor
  · rintro ⟨hp, hU⟩
    obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.horoUij_mem_iff Work.EKLComp.h01 g).mp hU
    rw [Work.EKLComp.par_uij_h01] at hp
    rw [hp]
    exact Work.EKLComp.u_zero
  · rintro rfl
    exact ⟨Work.EKLComp.par_one, by rw [← Work.EKLComp.u_zero]; exact Work.EKLComp.u_mem 0⟩

/-- The normalisation `nuR (fixRadon ν₀ X' x) [-1,1] = 1` holds for **every** `x`. -/
theorem norm_fixRadon {μ : Measure X3} [IsProbabilityMeasure μ]
    {ν₀ : X3 → Measure SL3} {X' : Set X3}
    (hL₀ : IsLeafwise μ (Uij Work.EKLComp.h01) ν₀ X') (x : X3) :
    (nuR (Work.EKLComp.fixRadon ν₀ X' x)).real (Set.Icc (-1) 1) = 1 := by
  by_cases hx : x ∈ X'
  · rw [Work.EKLComp.fixRadon_of_mem hx]
    have h := Work.EKLComp.nuR_normalised (hL₀.normalised x hx)
    show ((nuR (ν₀ x)) (Set.Icc (-1) 1)).toReal = 1
    rw [h, ENNReal.toReal_one]
  · rw [Work.EKLComp.fixRadon_of_notMem hx]
    exact nuR_dirac_one_Icc

end Work.EKLCompSetup

namespace Work.EKLCompSetup

theorem exists_of (hX3 : Work.EKLContract.P_X3) (hP : Work.EKLContract.P_Leafwise)
    (hML : Work.EKLContract.P_MaxLeaf) (hMF : Work.EKLContract.P_MaxFlow)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hNCS : ¬ Work.EKLContract.CrossSection μ (Work.EKLContract.Uij Work.EKLComp.h01))
    (hRel : Work.EKLContract.RelCrossSection μ
      (Work.EKLContract.Upar Work.EKLComp.h01 Work.EKLComp.h02 Work.EKLComp.h21)
      (Work.EKLContract.Uij Work.EKLComp.h01))
    (hninv : ¬ Work.EKLContract.IsUInvariant μ (Work.EKLContract.Uij Work.EKLComp.h01)) :
    Nonempty (Work.EKLComp.C8Setup μ) := by
  classical
  haveI hT2 : T2Space X3 := hX3.1
  haveI hPol : PolishSpace X3 := hX3.2.1
  have hAinv : IsAInvariant μ := hErg.1
  -- ## The leafwise layer
  obtain ⟨ν₀, X', hL₀⟩ :=
    (hP μ (Uij Work.EKLComp.h01) isHoro_Uij_h01 t0 (hErg.1 t0) tendsto_conj_Uij_h01).1
  obtain ⟨hU1, hU2, hU3, hU4, hU5₀, hU6₀, hU7₀, hU8₀, hU9₀⟩ :=
    (hP μ (Uij Work.EKLComp.h01) isHoro_Uij_h01 t0 (hErg.1 t0) tendsto_conj_Uij_h01).2 ν₀ X' hL₀
  obtain ⟨hL, hfin⟩ := Work.EKLCompLeaf.fixRadon (U := Uij Work.EKLComp.h01) hL₀
  set ν : X3 → Measure SL3 := Work.EKLComp.fixRadon ν₀ X' with hνdef
  have hmemX' : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff]; exact hL.conull
  have hU5 : U5clause μ ν := by
    filter_upwards [hU5₀, hmemX'] with x hx hmx
    rw [hνdef, Work.EKLComp.fixRadon_of_mem hmx]
    exact hx
  have hU6 : U6clause μ ν X' := by
    intro ε hε
    obtain ⟨K, hKc, hKX, hKμ, hKcont⟩ := hU6₀ ε hε
    refine ⟨K, hKc, hKX, hKμ, fun f => (hKcont f).congr (fun x hx => ?_)⟩
    rw [hνdef, Work.EKLComp.fixRadon_of_mem (hKX hx)]
  have hU7 : U7clause μ ν X' := by
    obtain ⟨X''₁, hX''₁X, hX''₁m, hX''₁μ, hX''₁cov⟩ := hU7₀ hErg.1
    refine ⟨X''₁, hX''₁X, hX''₁m, hX''₁μ, fun t x hx htx => ?_⟩
    obtain ⟨c, hc0, hct, hcov⟩ := hX''₁cov t x hx htx
    refine ⟨c, hc0, hct, ?_⟩
    rw [hνdef, Work.EKLComp.fixRadon_of_mem (hX''₁X hx),
      Work.EKLComp.fixRadon_of_mem (hX''₁X htx)]
    exact hcov
  have hU9 : U9clause μ ν := by
    intro hErg' hnot
    refine hU9₀ hErg' 0 1 Work.EKLComp.h01 rfl ?_
    intro hν0
    refine hnot ?_
    filter_upwards [hν0, hmemX'] with x hx hmx
    rw [hνdef, Work.EKLComp.fixRadon_of_mem hmx]
    exact hx
  have hU8 : IsAErgodic μ → CrossSection μ (Uij Work.EKLComp.h01) ∨ ∀ᵐ x ∂μ, ν x {1} = 0 := by
    intro hErg'
    rcases hU8₀ hErg' with hcs | hatom
    · exact Or.inl hcs
    · refine Or.inr ?_
      filter_upwards [hatom, hmemX'] with x hx hmx
      rw [hνdef, Work.EKLComp.fixRadon_of_mem hmx]
      exact hx
  have hradon : ∀ x, IsFiniteMeasureOnCompacts (ν x) := hfin
  have hnorm : ∀ x, (nuR (ν x)).real (Set.Icc (-1) 1) = 1 := norm_fixRadon hL₀
  -- ## (F1) / (F2) from (U7)
  obtain ⟨X''₁, hX''₁sub, hX''₁meas, hX''₁conull, hscale₁, hcentral₁⟩ := scaling_F1 hL hU7
  -- ## the relative cross-section set
  obtain ⟨B, hBmeas, hBconull, hBrel⟩ := hRel
  -- ## Step 0
  obtain ⟨N₀, hN₀null, hN₀sub, hN₀prop⟩ :=
    Work.EKLCompLeaf.step0_nontrivial (μ := μ) hErg hL hU5 hU9 hninv
  set N₀' : Set X3 := MeasureTheory.toMeasurable μ N₀ with hN₀'def
  have hN₀'sub : N₀ ⊆ N₀' := MeasureTheory.subset_toMeasurable μ N₀
  have hN₀'meas : MeasurableSet N₀' := MeasureTheory.measurableSet_toMeasurable μ N₀
  have hN₀'null : μ N₀' = 0 := by
    rw [hN₀'def, MeasureTheory.measure_toMeasurable, hN₀null]
  -- ## (U8): no atom at the identity
  have hAe1 : ∀ᵐ x ∂μ, ν x {1} = 0 := by
    rcases hU8 hErg with hcs | h
    · exact absurd hcs hNCS
    · exact h
  let G1 : Set X3 := {x | (ν x (ballU Work.EKLComp.h01 0)).toReal = 0}
  have hmeas01 : Measurable fun x : X3 => (ν x (ballU Work.EKLComp.h01 0)).toReal := by
    have h := Work.EKLCompLeaf.measurable_nu (μ := μ) (ν := ν) (X' := X') hL hradon 0
      (ballU Work.EKLComp.h01 0) ((isCompact_ballU 0).isClosed.measurableSet)
    simpa [Set.inter_self] using h
  have hG1meas : MeasurableSet G1 := by
    have h : MeasurableSet {x : X3 | (ν x (ballU Work.EKLComp.h01 0)).toReal = (fun _ : X3 => (0:ℝ)) x} :=
      measurableSet_eq_fun hmeas01 measurable_const
    simpa only [Pi.zero_apply] using h
  have hfin1 : ∀ x, ν x ({1} : Set SL3) ≠ ⊤ := fun x =>
    ((hradon x).lt_top_of_isCompact (isCompact_singleton)).ne
  have hG1conull : μ G1ᶜ = 0 := by
    have h1 : μ {x : X3 | ¬ (ν x {1} = 0)} = 0 := by
      rw [MeasureTheory.ae_iff] at hAe1; exact hAe1
    have hset : G1ᶜ = {x : X3 | ¬ (ν x {1} = 0)} := by
      ext x
      change ¬ ((ν x (ballU Work.EKLComp.h01 0)).toReal = 0) ↔
        ¬ (ν x ({1} : Set SL3) = 0)
      rw [ballU_zero]
      constructor
      · intro h h0; exact h (by simp [h0])
      · intro h h0
        exact h ((ENNReal.toReal_eq_zero_iff _).mp h0 |>.elim id
          (fun ht => absurd ht (hfin1 x)))
    rw [hset]; exact h1
  -- ## the conull set `X''`
  set X'' : Set X3 := X''₁ ∩ B ∩ N₀'ᶜ ∩ G1 with hX''def
  have hX''sub : X'' ⊆ X' := fun x hx => hX''₁sub (by rw [hX''def] at hx; exact hx.1.1.1)
  have hX''B : X'' ⊆ B := fun x hx => by rw [hX''def] at hx; exact hx.1.1.2
  have hX''meas : MeasurableSet X'' := by
    rw [hX''def]
    exact ((hX''₁meas.inter hBmeas).inter hN₀'meas.compl).inter hG1meas
  have hX''conull : μ X''ᶜ = 0 := by
    have hS : X''ᶜ ⊆ X''₁ᶜ ∪ Bᶜ ∪ N₀' ∪ G1ᶜ := by
      intro x hx
      rw [hX''def] at hx
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union, not_and_or] at hx ⊢
      tauto
    exact measure_mono_null hS (measure_union_null (measure_union_null
      (measure_union_null hX''₁conull hBconull) hN₀'null) hG1conull)
  have hscale : ∀ x ∈ X'', ∀ w σ : ℝ, phi w • x ∈ X'' →
      (nuR (ν (phi w • x))).real (Set.Icc (-σ) σ)
          * (nuR (ν x)).real (Set.Icc (-(Real.exp (2 * w))) (Real.exp (2 * w)))
        = (nuR (ν x)).real (Set.Icc (-(σ * Real.exp (2 * w))) (σ * Real.exp (2 * w)))
          * (nuR (ν (phi w • x))).real (Set.Icc (-1) 1) := by
    intro x hx w σ hpx
    rw [hX''def] at hx hpx
    exact hscale₁ x hx.1.1.1 w σ hpx.1.1.1
  have hcentral : ∀ x ∈ X'', ∀ s : ℝ, aPrime 2 s • x ∈ X'' → ν (aPrime 2 s • x) = ν x := by
    intro x hx s hsx
    rw [hX''def] at hx hsx
    exact hcentral₁ x hx.1.1.1 s hsx.1.1.1
  have hnontriv : ∀ x ∈ X'', ∀ s : ℝ, s ≠ 0 → u s • x ∈ X'' → ν (u s • x) ≠ ν x := by
    intro x hx s hs hsx
    rw [hX''def] at hx hsx
    exact hN₀prop x (fun h => hx.1.2 (hN₀'sub h)) s hs (fun h => hsx.1.2 (hN₀'sub h))
  have hnoAtom : ∀ x ∈ X'', (nuR (ν x)) {0} = 0 := by
    intro x hx
    have hxG1 : x ∈ G1 := by rw [hX''def] at hx; exact hx.2
    have hx1 : ν x ({1} : Set SL3) = 0 := by
      change (ν x (ballU Work.EKLComp.h01 0)).toReal = 0 at hxG1
      rw [ballU_zero] at hxG1
      exact (ENNReal.toReal_eq_zero_iff _).mp hxG1 |>.elim id
        (fun ht => absurd ht (hfin1 x))
    rw [nuR_singleton_zero]; exact hx1
  have htransfer : ∀ x ∈ X'', ∀ x' ∈ X'', ∀ s : ℝ, u s • x ∈ X'' →
      u s • x' ∈ X'' → nuR (ν x) = nuR (ν x') →
      nuR (ν (u s • x)) = nuR (ν (u s • x')) := by
    intro x hx x' hx' s hsx hsx' heq
    exact Work.EKLCompLeaf.equiv_transfer hL (hX''sub hx) (hX''sub hx') s
      (hX''sub hsx) (hX''sub hsx') heq
  -- ## the null set
  set N : Set X3 := X''ᶜ ∪ Bᶜ with hNdef
  have hNnull : μ N = 0 := by rw [hNdef]; exact measure_union_null hX''conull hBconull
  have hX''Nc : X'' ⊆ Nᶜ := by
    intro x hx
    rw [hNdef]
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨fun h => h hx, fun h => h (hX''B hx)⟩
  -- ## constants
  obtain ⟨C₀, hC₀pos, hC₀prop⟩ := hML
  set C : ℝ := max C₀ 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCge1 : 1 ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hC₀le : C₀ ≤ C := by rw [hCdef]; exact le_max_left _ _
  set ε : ℝ := min (1 / 100) (1 / (4 * (C + 2))) with hεdef
  have hC2pos : (0 : ℝ) < C + 2 := by linarith
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (by norm_num) (div_pos one_pos (by linarith))
  have hεsmall : ε ≤ 1 / 100 := by rw [hεdef]; exact min_le_left _ _
  have hεC : (C + 2) * ε ≤ 1 / 4 := by
    rw [hεdef]
    calc (C + 2) * min (1 / 100) (1 / (4 * (C + 2)))
        ≤ (C + 2) * (1 / (4 * (C + 2))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hC2pos)
      _ = 1 / 4 := by
          have h2 : (C + 2) ≠ 0 := ne_of_gt hC2pos
          field_simp
  have hε1 : ε ≤ 1 := le_trans hεsmall (by norm_num)
  have hε4 : ε ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hεpos) hε1
  have hε4nn : (0 : ℝ) ≤ 1 - ε ^ 4 := by linarith
  have hε4pos : (0 : ℝ) < ε ^ 4 := pow_pos hεpos 4
  -- ## the maximal inequality, with the constant `C`
  have hMLC : ∀ (f : X3 → ℝ), Measurable f → (∀ x, 0 ≤ f x) → Integrable f μ →
      ∀ α : ℝ, 0 < α →
        μ {x | x ∈ X' ∧ ∃ r : ℝ, 0 < r ∧
            α * (ν x (ballU Work.EKLComp.h01 r)).toReal
              < ∫ g in ballU Work.EKLComp.h01 r, f (g • x) ∂(ν x)}
          ≤ ENNReal.ofReal (C * (∫ x, f x ∂μ) / α) := by
    intro f hf hf0 hfi α hα
    refine le_trans (hC₀prop μ hAinv 0 1 Work.EKLComp.h01 ν X' hL f hf hf0 hfi α hα) ?_
    apply ENNReal.ofReal_le_ofReal
    have hInt : (0 : ℝ) ≤ ∫ x, f x ∂μ := integral_nonneg hf0
    have hαnn : (0 : ℝ) ≤ (∫ x, f x ∂μ) / α := div_nonneg hInt (le_of_lt hα)
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hC₀le hαnn
  -- ## `X₁` (Luzin)
  obtain ⟨K, hKcomp, hKsub, hKmeas, hKcont, hKlim⟩ :=
    Work.EKLCompLeaf.luzin_riesz_of_leafwise (μ := μ) hL hU6 (ε ^ 4 / 2)
      (div_pos hε4pos (by norm_num))
  let A : Set X3 := K ∩ X''
  have hAmeas : MeasurableSet A := hKcomp.measurableSet.inter hX''meas
  have hKle1 : μ K ≤ 1 := by
    calc μ K ≤ μ Set.univ := measure_mono (Set.subset_univ K)
      _ = 1 := measure_univ
  have hAne : μ A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans (measure_mono (Set.inter_subset_left)) hKle1)
  have hAeq : μ A = μ K := by
    have h : K \ X''ᶜ = A := by ext x; simp [A]
    rw [← h, MeasureTheory.measure_sdiff_null hX''conull]
  have hAle : 1 - ε ^ 4 / 2 < (μ A).toReal := by rw [hAeq]; exact hKmeas
  have hr : ENNReal.ofReal (1 - ε ^ 4) < μ A := by
    rw [← ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hAne,
      ENNReal.toReal_ofReal hε4nn]
    linarith
  obtain ⟨X₁, hX₁subA, hX₁comp, hX₁gt⟩ := hAmeas.exists_lt_isCompact_of_ne_top hAne hr
  have hX₁NeTop : μ X₁ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans (measure_mono (fun _ h => (hX₁subA h).1)) hKle1)
  have hX₁meas : 1 - ε ^ 4 < (μ X₁).toReal := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hX₁NeTop).mpr hX₁gt
    rwa [ENNReal.toReal_ofReal hε4nn] at h
  have hX₁sub : X₁ ⊆ X'' := fun x hx => (hX₁subA hx).2
  have hX₁subB : X₁ ⊆ X'' ∩ B := fun x hx => ⟨hX₁sub hx, hX''B (hX₁sub hx)⟩
  have hX₁cont : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ContinuousOn (fun x => ∫ g, f g ∂(ν x)) X₁ :=
    fun f => (hKcont f).mono (fun x hx => (hX₁subA hx).1)
  have hX₁lim : ∀ (y y' : X3) (ys ys' : ℕ → X3), (∀ n, ys n ∈ X₁) → (∀ n, ys' n ∈ X₁) →
      Tendsto ys atTop (𝓝 y) → Tendsto ys' atTop (𝓝 y') →
      (∀ n, ν (ys n) = ν (ys' n)) → ν y = ν y' :=
    fun y y' ys ys' h1 h2 => hKlim y y' ys ys'
      (fun n => (hX₁subA (h1 n)).1) (fun n => (hX₁subA (h2 n)).1)
  -- ## `X₂` (maximal inequality)
  have hleaf : ∀ R : ℝ, Measurable fun x => (leafMass ν X₁ R x).toReal :=
    fun R => (measurable_leafMass hL hradon hX₁comp.measurableSet R).ennreal_toReal
  obtain ⟨X₂, hX₂meas, hX₂def, hX₂bound⟩ :=
    exists_X2 (μ := μ) (ν := ν) (X' := X') (X'' := X'') (X₁ := X₁)
      hL hradon hX''meas hX''sub hX''conull hX₁comp.measurableSet hleaf hCpos hεpos hε1
      (le_of_lt hX₁meas) hMLC
  -- ## `𝓧(ρ)`
  obtain ⟨ρ, hρpos, hρsmall, hXrhomeas, hXrhobound⟩ :=
    exists_Xrho (μ := μ) (ν := ν) (X' := X') (X'' := X'') hL hradon hX''meas hX''conull
      hnoAtom hεpos
  let Xrho : Set X3 := {x | x ∈ X'' ∧ (nuR (ν x)).real (Set.Icc (-ρ) ρ) < (1 / 2 : ℝ)}
  have hXrhodef : ∀ x, x ∈ Xrho ↔ x ∈ X'' ∧
      (nuR (ν x)).real (Set.Icc (-ρ) ρ) < (1 / 2 : ℝ) := fun x => Iff.rfl
  -- ## `X₃` (flow-averaging maximal inequality)
  have hMF' : ∀ (f : X3 → ℝ), Measurable f → (∀ x, 0 ≤ f x) → Integrable f μ →
      ∀ α : ℝ, 0 < α →
        μ {x | ∃ T : ℝ, 0 < T ∧
            α * T < ∫ τ in (0 : ℝ)..T, f (Work.EKLComp.Phi τ x)}
          ≤ ENNReal.ofReal ((∫ x, f x ∂μ) / α) := by
    intro f hf hf0 hfi α hα
    simpa only [Work.EKLComp.Phi, Work.EKLComp.phi, t0] using
      hMF μ hAinv t0 f hf hf0 hfi α hα
  obtain ⟨X₃, hX₃comp, hX₃sub, hX₃meas, hX₃avg1, hX₃avg2⟩ :=
    exists_X3 (μ := μ) (X'' := X'') (X₂ := X₂) (Xrho := Xrho)
      hX''meas hX''conull hX₂meas hXrhomeas hCpos hεpos hX₂bound hXrhobound hMF'
  have hX₃sub' : X₃ ⊆ X'' ∩ Nᶜ := fun x hx => ⟨hX₃sub hx, hX''Nc (hX₃sub hx)⟩
  exact ⟨ν, X', hL, hradon, hnorm, X'', hX''sub, hX''conull, hscale, hcentral, hnontriv,
    hnoAtom, htransfer, ε, hεpos, hεsmall, ρ, hρpos, hρsmall, C, hCpos, hCge1, hεC,
    B, hBmeas, hBconull, hBrel, N, hNnull,
    X₁, hX₁comp, hX₁subB, hX₁meas, hX₁cont, hX₁lim, X₂, hX₂def, hX₂meas, hX₂bound,
    Xrho, hXrhodef, hXrhomeas, hXrhobound, X₃, hX₃comp, hX₃sub', hX₃meas, hX₃avg1,
    hX₃avg2⟩

end Work.EKLCompSetup
