/-
# `Submission/Work/FTS/StrongEps/EpsRHSP_slotSup.lean` — sup-bounds for the projected right-hand side

The statement proved here is `Work.FTS.StrongEps.EpsRHSP_slotSup`: if the pre-mollified
right-hand side `epsWP` is bounded together with all its mixed derivatives `D_z^j D_θ^i`
(`j + i ≤ 4`) on a compact `K' ⊆ Q0` containing the `ε`-shifts of a compact `K ⊆ Q0`, and if
`HkNorm α 4 (epsWP s) ≤ KW` uniformly in `s ∈ [0,T]`, then the *projected, mollified* right-hand
side `epsRHSP s = Pz (J_ε (epsWP s))` has the same uniform bound on `K`.

The proof uses the definitional identity `epsRHSP s = J_ε (epsWP s) − (L₁₂(J_ε (epsWP s))(0) /
pzNorm) · bump` and bounds the two terms separately:

* **main term.**  `D_z^jD_θ^i (J_ε Ψ) = J_ε (D_z^jD_θ^i Ψ)` on the open quadrant (`mixed_Jeps`),
  and `J_ε` is the nonnegative-kernel average of the shifted values (`abs_Jeps_le_sup`); the
  shifted points lie in `K'` by hypothesis, so the main term is `≤ C`;
* **correction term.**  The fixed profile `bump` has uniformly bounded mixed derivatives on the
  compact `K` (`exists_bound_mixed_bump` below), and the scalar is controlled by
  `|L₁₂(J_ε Ψ)(0)| ≤ CL · |J_ε Ψ|_{ℋ⁴} ≤ CL · e^{Cε/2}|Ψ|_{ℋ⁴} ≤ CL · e^{C/2} · KW`
  (`abs_L12_Jeps_le` below, from `OpenPkg.l12zero_field`, `HkSq_Jeps_le` and `HkMem_Jeps`).

Everything here is complete (no placeholders).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Jeps_absCompactBound
import Submission.Work.FTS.StrongEps.JepsSmoothOpen
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.L12AbsLe
import Submission.Work.FTS.OpenPkg.l12zero_field
import Submission.Work.FTS.GalBasis.FamEAux.Basic

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

theorem EpsRHSP_slotSup {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ε ∈ Set.Ioc 0 1)
    (hreg : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hsup : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K',
        |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) p.1 p.2| ≤ C)
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T, ∀ p ∈ K,
      |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift, C₀, hC₀, hbdd⟩ := hsup
  obtain ⟨KW, hKW, hnorm'⟩ := hnorm
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump K hK
  obtain ⟨CL, hCL0, hCL⟩ := abs_L12_Jeps_le (ρ := ρ) hρ
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨C₀ + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb, ?_, ?_⟩
  · exact add_nonneg hC₀ (mul_nonneg (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le) hCb0)
  · intro j i hji s hs p hp
    obtain ⟨hmems, hnormbs⟩ := hnorm' s hs
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    have hz : 0 < p.1 := hpQ.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := ⟨hpQ.2.1, hpQ.2.2⟩
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
        Work.FTS.StrongEps.Quad := (hreg s hs).forall
    have hmain : |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
        ≤ C₀ := by
      rw [Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε.1 hsm hz hθ j i]
      refine Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ.moll hε.1 hz hθ ?_ hC₀
      intro q hq1 hq2
      exact hbdd j i hji s hs (Work.FTS.StrongEps.zShift p.1 q.1,
        Work.FTS.StrongEps.thShift p.2 q.2) (hshift p hp q hq1 hq2)
    have hcorr : |(Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0|
          ≤ CL * KW := hCL hα hε.1 hε.2 hKW hsm hmems hnormbs
      have hal : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ CL * KW / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb :=
        hbump j i hji p hp
      exact mul_le_mul hal hb (abs_nonneg _)
        (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le)
    have hsplit : Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2
        = Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2 := by
      rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP,
        Work.FTS.StrongEps.PZeroAux.mixed_Pz
          (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 hsm) hz hθ j i]
    rw [hsplit]
    calc |Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| := by
          have h := abs_add_le (Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2)
            (-((Work.Construction.L12
                (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                  / Work.FTS.StrongEps.pzNorm)
                * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2))
          simpa only [sub_eq_add_neg, abs_neg] using h
      _ ≤ C₀ + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb := add_le_add hmain hcorr

end Work.FTS.StrongEps
