import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.R1G.DecayInZ_gA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

/-! ## The mixed derivatives of a globally smooth profile are continuous

`D_z = z ∂_z` and `D_θ = sin(2θ)∂_θ` each cost one order of smoothness on an open set, so a
profile of class `C^9` on `ℝ²` has all its mixed derivatives of order `≤ 4` continuous. -/

private theorem contDiffOn_uncurry_Dz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hpz := Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pz_le hV n h
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
    contDiffOn_fst.mul hpz
  exact h1.congr (fun p _ => rfl)

private theorem contDiffOn_uncurry_Dth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {n : ℕ} (h : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hpth := Work.FTS.GalBasis.famAux_contDiffOn_uncurry_pth_le hV n h
  have hsin : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V := by fun_prop
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p) V :=
    hsin.mul hpth
  exact h1.congr (fun p _ => rfl)

private theorem contDiffOn_uncurry_DzIter (G : ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (a N : ℕ), ContDiffOn ℝ ((N + a : ℕ) : ℕ∞ω) (Function.uncurry G) V →
      ContDiffOn ℝ ((N : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.DzIter a G)) V := by
  intro a
  induction a with
  | zero => intro N h; simpa using h
  | succ n ih =>
      intro N h
      have h' : ContDiffOn ℝ ((N + 1 + n : ℕ) : ℕ∞ω) (Function.uncurry G) V := by
        rw [show N + 1 + n = N + (n + 1) from by omega]; exact h
      have h2 : ContDiffOn ℝ ((N + 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.DzIter n G)) V := ih (N + 1) h'
      have h3 : ContDiffOn ℝ ((N : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DzIter n G))) V :=
        contDiffOn_uncurry_Dz hV h2
      simpa [Work.Spaces.DzIter_succ] using h3

private theorem contDiffOn_uncurry_DthIter (G : ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (a N : ℕ), ContDiffOn ℝ ((N + a : ℕ) : ℕ∞ω) (Function.uncurry G) V →
      ContDiffOn ℝ ((N : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.DthIter a G)) V := by
  intro a
  induction a with
  | zero => intro N h; simpa using h
  | succ n ih =>
      intro N h
      have h' : ContDiffOn ℝ ((N + 1 + n : ℕ) : ℕ∞ω) (Function.uncurry G) V := by
        rw [show N + 1 + n = N + (n + 1) from by omega]; exact h
      have h2 : ContDiffOn ℝ ((N + 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.DthIter n G)) V := ih (N + 1) h'
      have h3 : ContDiffOn ℝ ((N : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.Dth (Work.Spaces.DthIter n G))) V :=
        contDiffOn_uncurry_Dth hV h2
      simpa [Work.Spaces.DthIter_succ] using h3

/-! ## A uniform pointwise bound for the mixed derivatives of the correction profile -/

/-- **A uniform bound for the mixed derivatives of `bump` on a compact set.**  The correction
profile is `C^∞` on all of `ℝ²`, so each `D_z^jD_θ^i bump` (`j + i ≤ 4`) is continuous, and the
sum of their absolute values is a continuous function whose bound on the compact `K` (supplied by
`IsCompact.exists_bound_of_continuousOn`) dominates every one of them. -/
theorem exists_bound_mixed_bump (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ p ∈ K,
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb := by
  have hcont : ∀ j i : ℕ, j ≤ 4 → i ≤ 4 → Continuous (fun p : ℝ × ℝ =>
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|) := by
    intro j i hj hi
    have h0 : ContDiffOn ℝ ((9 : ℕ) : ℕ∞ω)
        (Function.uncurry Work.FTS.StrongEps.bump) Set.univ :=
      contDiffOn_univ.mpr (Work.FTS.StrongEps.contDiff_bump 9)
    have hb : ContDiffOn ℝ ((9 - i : ℕ) : ℕ∞ω)
        (Function.uncurry (Work.Spaces.DthIter i Work.FTS.StrongEps.bump)) Set.univ := by
      refine contDiffOn_uncurry_DthIter Work.FTS.StrongEps.bump isOpen_univ i (9 - i) ?_
      rw [show 9 - i + i = 9 from by omega]
      exact h0
    have hc : ContDiffOn ℝ ((9 - i - j : ℕ) : ℕ∞ω)
        (Function.uncurry (Work.Spaces.DzIter j
          (Work.Spaces.DthIter i Work.FTS.StrongEps.bump))) Set.univ := by
      refine contDiffOn_uncurry_DzIter (Work.Spaces.DthIter i Work.FTS.StrongEps.bump)
        isOpen_univ j (9 - i - j) ?_
      rw [show 9 - i - j + j = 9 - i from by omega]
      exact hb
    exact (continuousOn_univ.mp hc.continuousOn).abs
  have hsum : Continuous (fun p : ℝ × ℝ => ∑ j ∈ Finset.range 5, ∑ i ∈ Finset.range 5,
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|) :=
    continuous_finsetSum _ (fun j hj => continuous_finsetSum _ (fun i hi =>
      hcont j i (by have := Finset.mem_range.mp hj; omega)
        (by have := Finset.mem_range.mp hi; omega)))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hsum.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro j i hji p hp
  have hj : j ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have hi : i ∈ Finset.range 5 := Finset.mem_range.mpr (by omega)
  have h1 : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
      ≤ ∑ i' ∈ Finset.range 5,
          |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2| :=
    Finset.single_le_sum
      (f := fun i' => |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2|)
      (fun i' _ => abs_nonneg _) hi
  have h2 : (∑ i' ∈ Finset.range 5,
        |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2|)
      ≤ ∑ j' ∈ Finset.range 5, ∑ i' ∈ Finset.range 5,
          |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2| :=
    Finset.single_le_sum
      (f := fun j' => ∑ i' ∈ Finset.range 5,
        |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2|)
      (fun j' _ => Finset.sum_nonneg (fun i' _ => abs_nonneg _)) hj
  have h3 : (∑ j' ∈ Finset.range 5, ∑ i' ∈ Finset.range 5,
        |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2|) ≤ M := by
    have hMp := hM p hp
    rw [Real.norm_eq_abs] at hMp
    exact le_trans (le_abs_self _) hMp
  linarith [le_max_left M 0]

/-! ## The `L₁₂`-zero-mode of the mollified profile -/

/-- **The `L₁₂`-value at `z = 0` of the mollified profile, uniformly in the profile.** There is a
constant `CL` (depending only on the kernel `ρ`) such that

  `|L₁₂ (J_ε Ψ)(0)| ≤ CL · KW`

for every `α ∈ (0,1]`, every `ε ∈ (0,1]`, every `KW ≥ 0` and every profile `Ψ` which is `C^∞` on
the open quadrant, lies in `ℋ⁴_α` and satisfies `|Ψ|_{ℋ⁴} ≤ KW`.

Chain: `|L₁₂ f 0| ≤ C₁ |f|_{ℋ⁴}` (`OpenPkg.l12zero_field`), `HkSq α 4 (J_ε Ψ) ≤ e^{C ε} HkSq α 4 Ψ`
(`HkSq_Jeps_le`, applicable because `J_ε Ψ` is again smooth and in `ℋ⁴`, by `HkMem_Jeps`), and
`√(e^{Cε}) = e^{Cε/2} ≤ e^{C/2}` since `0 < C` and `ε ≤ 1`. -/
theorem abs_L12_Jeps_le {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ {α ε KW : ℝ}, α ∈ Set.Ioc 0 1 → 0 < ε → ε ≤ 1 → 0 ≤ KW →
      ∀ {Ψ : ℝ → ℝ → ℝ},
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) Work.FTS.StrongEps.Quad) →
        Work.Spaces.HkMem α 4 Ψ → Work.Spaces.HkNorm α 4 Ψ ≤ KW →
        |Work.Construction.L12 (Jeps ρ ε Ψ) 0| ≤ CL * KW := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.OpenPkg.l12zero_field
  obtain ⟨CJ, hCJpos, hCJ⟩ := HkSq_Jeps_le ρ hρ.moll
  refine ⟨C₁ * Real.exp (CJ / 2), by positivity, ?_⟩
  intro α ε KW hα hε0 hε1 hKW Ψ hsm hmem hnorm
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (Jeps ρ ε Ψ) :=
    smoothOpen_Jeps ρ hρ hε0 hsm
  have hXmem : Work.Spaces.HkMem α 4 (Jeps ρ ε Ψ) :=
    HkMem_Jeps hρ.moll hα hε0 hsm hmem
  have hHkSq := hCJ α hα 4 ε hε0 hε1 Ψ hsm hmem hXmem
  have hnormX : Work.Spaces.HkNorm α 4 (Jeps ρ ε Ψ) ≤ Real.exp (CJ / 2) * KW := by
    have h1 : Work.Spaces.HkNorm α 4 (Jeps ρ ε Ψ)
        = Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ ε Ψ)) := rfl
    rw [h1]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Jeps ρ ε Ψ))
        ≤ Real.sqrt (Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 Ψ) := Real.sqrt_le_sqrt hHkSq
      _ = Real.sqrt (Real.exp (CJ * ε)) * Real.sqrt (Work.Spaces.HkSq α 4 Ψ) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (CJ * ε / 2) * Work.Spaces.HkNorm α 4 Ψ := by
          rw [Real.exp_half, Work.Spaces.HkNorm]
      _ ≤ Real.exp (CJ / 2) * KW := by
          refine mul_le_mul ?_ hnorm (Work.Spaces.HkNorm_nonneg _ _ _) (Real.exp_pos _).le
          exact Real.exp_le_exp.mpr (by nlinarith)
  calc |Work.Construction.L12 (Jeps ρ ε Ψ) 0|
      ≤ C₁ * Work.FTS.Nonlin.Xn α (Jeps ρ ε Ψ) := hC₁ α hα.1 hα.2 _ ⟨hXsm, hXmem⟩
    _ = C₁ * Work.Spaces.HkNorm α 4 (Jeps ρ ε Ψ) := rfl
    _ ≤ C₁ * (Real.exp (CJ / 2) * KW) := mul_le_mul_of_nonneg_left hnormX hC₁pos.le
    _ = C₁ * Real.exp (CJ / 2) * KW := by ring

/-! ## The target -/


end Work.FTS.StrongEps
