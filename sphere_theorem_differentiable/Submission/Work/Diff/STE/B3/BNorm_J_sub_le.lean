import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le
import Submission.Work.Diff.STE.B3.BNorm_J_le
import Submission.Work.Diff.STE.CSq_trunc_sub_le
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.STruncC_contDiff_periodic
import Submission.Work.Diff.STE.B3.CSq_STruncC_sub
import Submission.Work.Diff.STE.B3.bump_expansion_fixed
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the commutator estimate `BNorm k (J ρ ε h - h) ≤ C ε BNorm (k+1) h`

This file proves `Work.Diff.STE.B3.BNorm_J_sub_le`: the Friedrichs mollifier
`J ρ ε h = Σ_i R_i*(S_ε (R_i h))` of `B3Data` differs from the identity by `O(ε)` in the composite
norm, measured against the *next* norm:

  `D.BNorm k (D.J ρ ε h - h) ≤ C · ε · D.BNorm (k+1) h`

for the profile `ρ` of a Friedrichs mollifier (`ρ = 1` on the closed unit ball of frequency space,
`‖ρ‖ ≤ 1` everywhere), `ε ∈ (0,1]` and `finrank ℝ E < 2k`.

## Route

1. **Reconstruction.**  `Σ_i R_i* (R_i h) = h` (`Rstar_R_eq_id`, without any `[I.Boundaryless]`
   hypothesis, which is not needed).
2. Hence `J ρ ε h - h = Σ_i R_i* (S_ε (R_i h) - R_i h)`, and the `j`-component of the `i`-th summand
   is `Σ_{cd} (lift of coeffFun) · w_{cd} ∘ tMapFun`, where `w = S_ε (R_i h) - R_i h`.  The
   *periodisation* of the difference only sees `w` at points of the cube (where the periodisation of
   `R_i h` agrees with `R_i h`), so it can be written in terms of the `1`-periodic function
   `truncDiff D ρ ε h i c d y = ((S_ε (R_i h)_{cd} y - per (R_i h)_{cd} y).re : ℂ)`.
3. The **chart transfer** `CSq_period_comp_arg_le_of_isOpen` (the `H^k` norm of the periodisation of
   `G · (u ∘ T)` is controlled by `H^k(u)`) applied to the globally smooth `G = lift ∘ coeffFun`
   (`bump_expansion_fixed`) and `T = tMapFun` on the open set `goodSet`, together with
   `CSq_sum_le`, gives the bound of `CSq k (fourierCoeff (Rper j (J ρ ε h - h) a b))` by
   `Cf · Σ_i Σ_{cd} CSq k (fourierCoeff (truncDiff ...))`.
4. The **truncation defect estimate** `CSq_STruncC_sub` gives, for every `i c d`,
   `CSq k (fourierCoeff (truncDiff D ρ ε h i c d)) ≤ 4 ε² CSq (k+1) (fourierCoeff (Rper i h c d))`,
   which sums to `4 ε² · D.BNorm (k+1) h ≤ 4 ε · D.BNorm (k+1) h` (as `ε ≤ 1`).
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory BigOperators
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter


namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. Elementary helper lemmas -/

/-- The support of a localised component lies in the open centred cube. -/
lemma R_support_cube (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun z hz => D.psi_supp i (fun h0 => hz (by
    simp only [B3Data.R, h0, zero_mul, mul_zero]))

/-- On the open centred cube the periodisation of a localised component is the component itself,
seen in `ℂ`. -/
lemma Rper_eq_of_mem_cube (D : B3Data (I := I) (M := M) ι₀ g₀)
    (h : Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    {y : Fin (Module.finrank ℝ E) → ℝ}
    (hy : ∀ k : Fin (Module.finrank ℝ E), y k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    D.Rper i h a b y = ((D.R i h a b y : ℝ) : ℂ) := by
  have hsupp : Function.support (fun z => ((D.R i h a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    refine R_support_cube D h i a b ?_
    rw [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by rw [h0, Complex.ofReal_zero])
  exact periodization_eq_self hsupp hy

/-- The chart component `R_i h`, viewed as a family of flat functions. -/
def compFun (D : B3Data (I := I) (M := M) ι₀ g₀) (h : Bil (I := I) (M := M)) (i : ι₀) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun a b z => D.R i h a b z

/-- The truncated chart component `(S_ε (R_i h)_{ab}).re`, viewed as a family of flat functions. -/
def truncComp (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (h : Bil (I := I) (M := M)) (i : ι₀) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun a b y => (Work.Diff.STE.STruncC ρ ε (D.R i h a b) y).re

/-- The **raw truncation defect** `S_ε (R_i h)_{cd} - (R_i h)_{cd}` (real valued). -/
def rawDiff (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (h : Bil (I := I) (M := M)) (i : ι₀) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun a b y => (Work.Diff.STE.STruncC ρ ε (D.R i h a b) y).re - D.R i h a b y

/-- The complex lift of the cross-chart coefficient `Work.Diff.STE.D.coeffFun`. -/
def coeffLift (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (c d : Fin (Module.finrank ℝ E)) :
    (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun z => ((Work.Diff.STE.D.coeffFun D i j a b c d z : ℝ) : ℂ)

/-- **The truncation defect, seen as a `ℂ`-valued periodic function.**  For a chart `i` and a
component index `(c,d)` this is `y ↦ ((S_ε (R_i h)_{cd} y - per (R_i h)_{cd} y).re : ℂ)`; it is
smooth and `1`-periodic, and its `H^k` norm is controlled by `4 ε² H^{k+1}` of the component. -/
def truncDiff (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (h : Bil (I := I) (M := M)) (i : ι₀)
    (c d : Fin (Module.finrank ℝ E)) : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
  fun y => (((Work.Diff.STE.STruncC ρ ε (D.R i h c d) y - D.Rper i h c d y).re : ℝ) : ℂ)

@[simp] lemma truncDiff_apply (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ) (h : Bil (I := I) (M := M)) (i : ι₀)
    (c d : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ) :
    truncDiff D ρ ε h i c d y
      = (((Work.Diff.STE.STruncC ρ ε (D.R i h c d) y - D.Rper i h c d y).re : ℝ) : ℂ) := rfl

/-- The truncation defect is smooth and `1`-periodic. -/
lemma truncDiff_contDiff_periodic (D : B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρb : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (h : Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d))
    (i : ι₀) (c d : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (truncDiff D ρ ε h i c d)
      ∧ Periodic1 (truncDiff D ρ ε h i c d) := by
  have hfC : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h c d y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hsm i c d)
  have hsuppC : Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h c d y : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    refine R_support_cube D h i c d ?_
    rw [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by rw [h0, Complex.ofReal_zero])
  obtain ⟨hg, hgp, -⟩ :=
    periodization_contDiff_periodic (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h c d y : ℝ) : ℂ)) hfC hsuppC
  obtain ⟨h1, h2⟩ :=
    STruncC_contDiff_periodic ρ hρb ε (D.R i h c d) (hsm i c d) (R_support_cube D h i c d)
  have hper_eq : D.Rper i h c d = fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ, ((D.R i h c d (y + iVec m) : ℝ) : ℂ) := rfl
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (h1.sub (by
      rw [hper_eq]; exact hg)))
  · have hp1 : ∀ (j : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ),
        (Work.Diff.STE.STruncC ρ ε (D.R i h c d) (y + Pi.single j 1)).re
          = (Work.Diff.STE.STruncC ρ ε (D.R i h c d) y).re := by
      intro j y
      rw [h2 j y]
    have hp2 : ∀ (j : Fin (Module.finrank ℝ E)) (y : Fin (Module.finrank ℝ E) → ℝ),
        D.Rper i h c d (y + Pi.single j 1) = D.Rper i h c d y := by
      intro j y
      show (∑' m : Fin (Module.finrank ℝ E) → ℤ,
          ((D.R i h c d ((y + Pi.single j 1) + iVec m) : ℝ) : ℂ))
        = (∑' m : Fin (Module.finrank ℝ E) → ℤ,
          ((D.R i h c d (y + iVec m) : ℝ) : ℂ))
      exact hgp j y
    intro j y
    show (((Work.Diff.STE.STruncC ρ ε (D.R i h c d) (y + Pi.single j 1)
        - D.Rper i h c d (y + Pi.single j 1)).re : ℝ) : ℂ)
      = (((Work.Diff.STE.STruncC ρ ε (D.R i h c d) y - D.Rper i h c d y).re : ℝ) : ℂ)
    simp only [Complex.sub_re]
    rw [hp1 j y, hp2 j y]

/-- `Rstar` is additive in the component family (used to push a subtraction inside). -/
lemma Rstar_sub (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u v : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ) :
    D.Rstar i (fun a b z => u a b z - v a b z) = D.Rstar i u - D.Rstar i v := by
  funext p
  ext X Y
  rw [Pi.sub_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rw [Rstar_apply D i (fun a b z => u a b z - v a b z) p X Y, Rstar_apply D i u p X Y,
    Rstar_apply D i v p X Y]
  rw [← mul_sub]
  congr 1
  have hpt : ∀ a b : Fin (Module.finrank ℝ E),
      (u a b (coord (I := I) (D.x₀ i) p) - v a b (coord (I := I) (D.x₀ i) p))
          * g₀.inner p X (D.e i a p) * g₀.inner p Y (D.e i b p)
        = u a b (coord (I := I) (D.x₀ i) p) * g₀.inner p X (D.e i a p)
            * g₀.inner p Y (D.e i b p)
          - v a b (coord (I := I) (D.x₀ i) p) * g₀.inner p X (D.e i a p)
            * g₀.inner p Y (D.e i b p) := fun a b => by ring
  simp only [hpt, Finset.sum_sub_distrib]

/-- **The reconstruction identity** `Σ_i R_i* (R_i h) = h` (no `[I.Boundaryless]` needed). -/
lemma Rstar_R_eq_id (D : B3Data (I := I) (M := M) ι₀ g₀) (h : Bil (I := I) (M := M)) :
    (∑ i : ι₀, D.Rstar i (fun (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ) => D.R i h a b z)) = h := by
  funext p
  ext X Y
  simp only [Finset.sum_apply, sum_apply]
  simp only [Rstar_R_eq_zeta_sq_free D h]
  rw [← Finset.sum_mul, D.hζsq p, one_mul]

/-- **The Friedrichs commutator estimate.**  For the profile `ρ` of a Friedrichs mollifier and
`ε ∈ (0,1]`, the mollifier `J ρ ε` differs from the identity by `O(ε)` in the composite `H^k` norm,
against the `H^{k+1}` norm. -/
theorem BNorm_J_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hρ1 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, (∑ i, (y i) ^ 2) ≤ 1 → ρ y = 1)
    (hρb : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (k : ℕ) (hk : Module.finrank ℝ E < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)) →
      D.BNorm k (D.J ρ ε h - h) ≤ C * ε * D.BNorm (k + 1) h := by
  classical
  -- For each `(j,a,b)` we bound the corresponding component of `J ρ ε h - h` by
  -- `O(ε) · D.BNorm (k+1) h`, with a constant uniform in `ε` and `h`.
  have hmain : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ h : Bil (I := I) (M := M),
          (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
            ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d)) →
          CSq k (fourierCoeff (D.Rper j (D.J ρ ε h - h) a b))
            ≤ Cf * (ε * D.BNorm (k + 1) h) := by
    intro j a b
    -- the coefficient window of the chart pair `(i,j)`, with the *fixed* transition `tMapFun`
    have hgood : ∀ i : ι₀, closure (Work.Diff.STE.D.Omega D i j)
        ⊆ Work.Diff.STE.D.goodSet D i j := fun i => closure_Omega_goodSet D i j
    have hopen : ∀ i : ι₀, IsOpen (Work.Diff.STE.D.goodSet D i j) :=
      fun i => (goodSet_smooth_noT2 D i j).1
    have hsmC : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        ContDiffOn ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.coeffFun D i j a b c d)
          (Work.Diff.STE.D.goodSet D i j) :=
      fun i c d => (goodSet_smooth_noT2 D i j).2.2 a b c d
    choose G hGsm hGsupp hGcomp hGsub hid using fun i : ι₀ =>
      bump_expansion_fixed D i j a b (hgood i) (hopen i) (hsmC i)
    -- `G` is the complex lift of the cross-chart coefficient `coeffFun`
    have hGeq : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ),
        G i c d z = ((Work.Diff.STE.D.coeffFun D i j a b c d z : ℝ) : ℂ) := by
      intro i c d z
      have hconst := hid i (fun c' d' (_ : Fin (Module.finrank ℝ E) → ℝ) =>
        if c' = c then (if d' = d then (1 : ℝ) else 0) else 0) z
      have hL : D.R j (D.Rstar i (fun c' d' (_ : Fin (Module.finrank ℝ E) → ℝ) =>
            if c' = c then (if d' = d then (1 : ℝ) else 0) else 0)) a b z
            = Work.Diff.STE.D.coeffFun D i j a b c d z := by
        rw [R_Rstar_expansion_pointwise_noT2 D i j a b _ z]
        rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single d]
          · simp
          · intro b' _ hb'; simp [hb']
          · intro h; exact absurd (Finset.mem_univ d) h
        · intro c' _ hc'; simp [hc']
        · intro h; exact absurd (Finset.mem_univ c) h
      have hR : (∑ c' : Fin (Module.finrank ℝ E), ∑ d' : Fin (Module.finrank ℝ E),
            G i c' d' z * ((if c' = c then (if d' = d then (1 : ℝ) else 0) else 0 : ℝ) : ℂ))
            = G i c d z := by
        rw [Finset.sum_eq_single c]
        · rw [Finset.sum_eq_single d]
          · simp
          · intro b' _ hb'; simp [hb']
          · intro h; exact absurd (Finset.mem_univ d) h
        · intro c' _ hc'; simp [hc']
        · intro h; exact absurd (Finset.mem_univ c) h
      rw [← hR, ← hconst, hL]
    have hlsm : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (coeffLift D i j a b c d) := by
      intro i c d
      have hfun : coeffLift D i j a b c d = G i c d :=
        funext fun z => (hGeq i c d z).symm
      rw [hfun]; exact hGsm i c d
    have hlsupp : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        Function.support (coeffLift D i j a b c d) ⊆
          Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
            Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
      intro i c d
      have hfun : coeffLift D i j a b c d = G i c d :=
        funext fun z => (hGeq i c d z).symm
      rw [hfun]; exact hGsupp i c d
    have hlcmp : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        IsCompact (tsupport (coeffLift D i j a b c d)) := by
      intro i c d
      have hfun : coeffLift D i j a b c d = G i c d :=
        funext fun z => (hGeq i c d z).symm
      rw [hfun]; exact hGcomp i c d
    have hlsub : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        tsupport (coeffLift D i j a b c d) ⊆ Work.Diff.STE.D.goodSet D i j := by
      intro i c d
      have hfun : coeffLift D i j a b c d = G i c d :=
        funext fun z => (hGeq i c d z).symm
      rw [hfun]; exact hGsub i c d
    -- the transfer constants (uniform in the periodic test function)
    choose Ct hCt using fun (i : ι₀) (c d : Fin (Module.finrank ℝ E)) =>
      CSq_period_comp_arg_le_of_isOpen (ι := Fin (Module.finrank ℝ E)) k (by simpa using hk)
        (Work.Diff.STE.D.tMapFun D i j) (coeffLift D i j a b c d)
        (hlsm i c d) (hlsupp i c d) (hlcmp i c d)
        (Work.Diff.STE.D.goodSet D i j) (hopen i) (hlsub i c d)
        (fun z hz => ((goodSet_smooth_noT2 D i j).2.1).contDiffAt ((hopen i).mem_nhds hz))
        (tMapFun_injOn_det D i j).1 (tMapFun_injOn_det D i j).2
    have hhom : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
        (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) u → Periodic1 u →
        CSq k (fourierCoeff (fun z => ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
          coeffLift D i j a b c d (z + iVec m)
            * u (Work.Diff.STE.D.tMapFun D i j (z + iVec m))))
          ≤ 2 * Ct i c d * CSq k (fourierCoeff u) :=
      fun i c d => homog_transfer k (Ct i c d) (hCt i c d).1
        (Work.Diff.STE.D.tMapFun D i j) (coeffLift D i j a b c d) (hCt i c d).2
    -- the pointwise expansion of `R_j (R_i* u)` at the fixed transition `tMapFun`, in terms of
    -- the coefficient lift
    have hid2 : ∀ (i : ι₀) (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (z : Fin (Module.finrank ℝ E) → ℝ),
        ((D.R j (D.Rstar i u) a b z : ℝ) : ℂ)
          = ∑ c, ∑ d, coeffLift D i j a b c d z
              * ((u c d (Work.Diff.STE.D.tMapFun D i j z) : ℝ) : ℂ) := by
      intro i u z
      rw [hid i u z]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      rw [show G i c d z = coeffLift D i j a b c d z from hGeq i c d z]
    refine ⟨(Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
      (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        2 * Ct t.1 t.2.1 t.2.2) * 4, ?_, ?_⟩
    · refine mul_nonneg (mul_nonneg ?_ ?_) (by norm_num)
      · positivity
      · exact Finset.sum_nonneg fun t _ => by
          have := (hCt t.1 t.2.1 t.2.2).1; linarith
    · intro ε hε hε1 h hsm
      ------------------------------------------------------------------------------------
      -- 1. the truncation defects are smooth and `1`-periodic
      ------------------------------------------------------------------------------------
      have htd : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞) (truncDiff D ρ ε h i c d)
            ∧ Periodic1 (truncDiff D ρ ε h i c d) :=
        fun i c d => truncDiff_contDiff_periodic D ρ hρb ε h hsm i c d
      ------------------------------------------------------------------------------------
      -- 2. the truncation-defect estimate and the summand bound
      ------------------------------------------------------------------------------------
      have hTrunc : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          CSq k (fourierCoeff (truncDiff D ρ ε h i c d))
            ≤ 4 * ε ^ 2 * CSq (k + 1) (fourierCoeff (D.Rper i h c d)) :=
        fun i c d => CSq_STruncC_sub ρ hρ1 hρb ε hε hε1 k (D.R i h c d) (hsm i c d)
          (R_support_cube D h i c d)
      have hBle : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          CSq (k + 1) (fourierCoeff (D.Rper i h c d)) ≤ D.BNorm (k + 1) h := by
        intro i c d
        refine (Finset.single_le_sum
          (f := fun b : Fin (Module.finrank ℝ E) =>
            CSq (k + 1) (fourierCoeff (D.Rper i h c b)))
          (fun b _ => CSq_nonneg (k + 1) _) (Finset.mem_univ d)).trans ?_
        refine (Finset.single_le_sum
          (f := fun a : Fin (Module.finrank ℝ E) => ∑ b : Fin (Module.finrank ℝ E),
            CSq (k + 1) (fourierCoeff (D.Rper i h a b)))
          (fun a _ => Finset.sum_nonneg fun b _ => CSq_nonneg (k + 1) _)
          (Finset.mem_univ c)).trans ?_
        refine (Finset.single_le_sum
          (f := fun j : ι₀ => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            CSq (k + 1) (fourierCoeff (D.Rper j h a b)))
          (fun j _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
            CSq_nonneg (k + 1) _)
          (Finset.mem_univ i)).trans ?_
        exact le_of_eq rfl
      ------------------------------------------------------------------------------------
      -- 3. the decomposition `J ρ ε h - h = Σ_i R_i* (S_ε (R_i h) - R_i h)`
      ------------------------------------------------------------------------------------
      have hJeq : D.J ρ ε h = ∑ i : ι₀, D.Rstar i (truncComp D ρ ε h i) := by
        rw [B3Data.J]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
      have hrecon : h = ∑ i : ι₀, D.Rstar i (compFun D h i) := (Rstar_R_eq_id D h).symm
      have hfun : D.J ρ ε h - h = ∑ i : ι₀, D.Rstar i (rawDiff D ρ ε h i) := by
        funext p
        rw [Pi.sub_apply, congrFun hJeq p, congrFun hrecon p,
          Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]
        refine (Finset.sum_sub_distrib
          (fun i : ι₀ => D.Rstar i (truncComp D ρ ε h i) p)
          (fun i : ι₀ => D.Rstar i (compFun D h i) p)).symm.trans ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        exact congrFun (Rstar_sub D i (truncComp D ρ ε h i) (compFun D h i)).symm p
      ------------------------------------------------------------------------------------
      -- 4. the raw and the periodic truncation defect agree where the coefficient lives
      ------------------------------------------------------------------------------------
      have hagree : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
          (y : Fin (Module.finrank ℝ E) → ℝ), coeffLift D i j a b c d y ≠ 0 →
          ((rawDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j y) : ℝ) : ℂ)
            = truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j y) := by
        intro i c d y hy
        have hc : Work.Diff.STE.D.coeffFun D i j a b c d y ≠ 0 := fun h0 =>
          hy (by simp only [coeffLift, h0, Complex.ofReal_zero])
        have hΩ : y ∈ Work.Diff.STE.D.Omega D i j :=
          support_coeffFun_subset_Omega D i j a b c d (Function.mem_support.mpr hc)
        have hlt : ‖Work.Diff.STE.D.tMapFun D i j y‖ < D.σ i := (D.hζsupp i _ hΩ.2).2
        have hcube : ∀ k : Fin (Module.finrank ℝ E),
            Work.Diff.STE.D.tMapFun D i j y k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
          intro k
          have h1 : ‖Work.Diff.STE.D.tMapFun D i j y k‖
              ≤ ‖Work.Diff.STE.D.tMapFun D i j y‖ := norm_le_pi_norm _ k
          have h2 : ‖Work.Diff.STE.D.tMapFun D i j y‖ < (1 / 2 : ℝ) := by
            have hσ := D.hσ2 i; linarith
          have h3 : |Work.Diff.STE.D.tMapFun D i j y k| < (1 / 2 : ℝ) := by
            rw [← Real.norm_eq_abs]; exact lt_of_le_of_lt h1 h2
          rw [Set.mem_Ioo]
          exact abs_lt.mp h3
        have hper := Rper_eq_of_mem_cube D h i c d hcube
        show ((((Work.Diff.STE.STruncC ρ ε (D.R i h c d)
              (Work.Diff.STE.D.tMapFun D i j y)).re
              - D.R i h c d (Work.Diff.STE.D.tMapFun D i j y) : ℝ)) : ℂ)
            = truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j y)
        rw [truncDiff_apply, Complex.sub_re, hper, Complex.ofReal_re]
      ------------------------------------------------------------------------------------
      -- 5. the pointwise expansion in `ℂ`
      ------------------------------------------------------------------------------------
      have hlin : ∀ y : Fin (Module.finrank ℝ E) → ℝ,
          ((D.R j (D.J ρ ε h - h) a b y : ℝ) : ℂ)
            = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                coeffLift D i j a b c d y
                  * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j y) := by
        intro y
        rw [hfun]
        rw [show D.R j (∑ i : ι₀, D.Rstar i (rawDiff D ρ ε h i)) a b y
            = ∑ i : ι₀, D.R j (D.Rstar i (rawDiff D ρ ε h i)) a b y from by
          simp only [B3Data.R, B3Data.mat, Finset.sum_apply, sum_apply, Finset.mul_sum]]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hid2 i (rawDiff D ρ ε h i) y]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        by_cases hy : coeffLift D i j a b c d y = 0
        · rw [hy]; simp
        · rw [hagree i c d y hy]
      ------------------------------------------------------------------------------------
      -- 6. the periodisation identity
      ------------------------------------------------------------------------------------
      have hpoint : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          D.Rper j (D.J ρ ε h - h) a b z =
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
                coeffLift D i j a b c d (z + iVec m)
                  * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j (z + iVec m)) := by
        intro z
        set N : Fin (Module.finrank ℝ E) → ℤ := fun i => ⌊|z i|⌋ + 2 with hNdef
        set S : Finset (Fin (Module.finrank ℝ E) → ℤ) :=
          Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hSdef
        have hsupp' : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
            Function.support (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              coeffLift D i j a b c d w
                * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j w)) ⊆
              Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
                Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
          intro i c d w hw
          refine hlsupp i c d (fun h0 => hw (by
            show coeffLift D i j a b c d w
              * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j w) = 0
            rw [h0, zero_mul]))
        have hzero : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
            (m : Fin (Module.finrank ℝ E) → ℤ), m ∉ S →
            coeffLift D i j a b c d (z + iVec m)
              * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j (z + iVec m)) = 0 := by
          intro i c d m hm
          by_contra hne
          have hmem : ∀ k : Fin (Module.finrank ℝ E), m k ∈ Finset.Icc (-(N k)) (N k) := by
            intro k
            have hlt : |m k| < N k := by
              have hh := abs_lt_floor_add_two_of_support (hsupp' i c d) (x := z) (y := z)
                (fun k => by rw [sub_self, abs_zero]; norm_num) hne k
              simpa [hNdef] using hh
            rw [Finset.mem_Icc]
            have h2 := abs_lt.mp hlt
            exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
          exact hm (by rw [hSdef, Fintype.mem_piFinset]; exact hmem)
        rw [show D.Rper j (D.J ρ ε h - h) a b z = ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
            ((D.R j (D.J ρ ε h - h) a b (z + iVec m) : ℝ) : ℂ) from rfl]
        rw [tsum_congr (fun m => hlin (z + iVec m))]
        rw [tsum_finset_sum_eq (f := fun (i : ι₀) (m : (Fin (Module.finrank ℝ E) → ℤ)) =>
              ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                coeffLift D i j a b c d (z + iVec m)
                  * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j (z + iVec m)))
            (fun i m hm => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ =>
              hzero i c d m hm)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [tsum_finset_sum_eq (f := fun (c : Fin (Module.finrank ℝ E))
              (m : (Fin (Module.finrank ℝ E) → ℤ)) =>
              ∑ d : Fin (Module.finrank ℝ E),
                coeffLift D i j a b c d (z + iVec m)
                  * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j (z + iVec m)))
            (fun c m hm => Finset.sum_eq_zero fun d _ => hzero i c d m hm)]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [tsum_finset_sum_eq (f := fun (d : Fin (Module.finrank ℝ E))
              (m : (Fin (Module.finrank ℝ E) → ℤ)) =>
                coeffLift D i j a b c d (z + iVec m)
                  * truncDiff D ρ ε h i c d (Work.Diff.STE.D.tMapFun D i j (z + iVec m)))
            (fun d m hm => hzero i c d m hm)]
      ------------------------------------------------------------------------------------
      -- 7. the terms of the finite sum and the Fourier assembly
      ------------------------------------------------------------------------------------
      set per : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun t z =>
        ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
          coeffLift D t.1 j a b t.2.1 t.2.2 (z + iVec m)
            * truncDiff D ρ ε h t.1 t.2.1 t.2.2
                (Work.Diff.STE.D.tMapFun D t.1 j (z + iVec m)) with hperdef
      have hperVal : ∀ (t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ),
          per t z = ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
            coeffLift D t.1 j a b t.2.1 t.2.2 (z + iVec m)
              * truncDiff D ρ ε h t.1 t.2.1 t.2.2
                  (Work.Diff.STE.D.tMapFun D t.1 j (z + iVec m)) := by
        intro t z; rw [hperdef]
      have hper_t : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ContDiff ℝ (⊤ : ℕ∞) (per t) ∧ Periodic1 (per t) := by
        intro t
        have hsmw : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            coeffLift D t.1 j a b t.2.1 t.2.2 w
              * truncDiff D ρ ε h t.1 t.2.1 t.2.2 (Work.Diff.STE.D.tMapFun D t.1 j w)) := by
          rw [contDiff_iff_contDiffAt]
          intro w
          by_cases hw : w ∈ tsupport (coeffLift D t.1 j a b t.2.1 t.2.2)
          · have hmem : w ∈ Work.Diff.STE.D.goodSet D t.1 j :=
              hlsub t.1 t.2.1 t.2.2 hw
            exact (hlsm t.1 t.2.1 t.2.2).contDiffAt.mul
              (((htd t.1 t.2.1 t.2.2).1.contDiffAt).comp w
                (((goodSet_smooth_noT2 D t.1 j).2.1).contDiffAt ((hopen t.1).mem_nhds hmem)))
          · have hev : coeffLift D t.1 j a b t.2.1 t.2.2
                =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hw
            refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
            filter_upwards [hev] with w' hw'
            show coeffLift D t.1 j a b t.2.1 t.2.2 w'
              * truncDiff D ρ ε h t.1 t.2.1 t.2.2 (Work.Diff.STE.D.tMapFun D t.1 j w') = 0
            rw [hw', zero_mul]
        have hsupw : Function.support (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            coeffLift D t.1 j a b t.2.1 t.2.2 w
              * truncDiff D ρ ε h t.1 t.2.1 t.2.2 (Work.Diff.STE.D.tMapFun D t.1 j w)) ⊆
            Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
              Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := fun w hw =>
          hlsupp t.1 t.2.1 t.2.2 (fun h0 => hw (by
            show coeffLift D t.1 j a b t.2.1 t.2.2 w
              * truncDiff D ρ ε h t.1 t.2.1 t.2.2 (Work.Diff.STE.D.tMapFun D t.1 j w) = 0
            rw [h0, zero_mul]))
        obtain ⟨h1, h2, -⟩ := periodization_contDiff_periodic _ hsmw hsupw
        rw [hperdef]
        exact ⟨h1, h2⟩
      have hfun2 : D.Rper j (D.J ρ ε h - h) a b = fun z => ∑ t, per t z := by
        funext z
        rw [hpoint z]
        refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun d _ => (hperVal (i, c, d) z).symm).trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type]
      have hcoeff : fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)
          = fun m => ∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              fourierCoeff (per t) m := by
        rw [hfun2]
        funext m
        rw [fourierCoeff_finset_sum_of_continuous _ (fun t => (hper_t t).1.continuous) m]
      -- the sum of the truncated defects
      have hsum_terms :
          (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (per t)))
            ≤ (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                2 * Ct t.1 t.2.1 t.2.2) * (4 * ε ^ 2 * D.BNorm (k + 1) h) := by
        have hstep : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            CSq k (fourierCoeff (per t))
              ≤ (2 * Ct t.1 t.2.1 t.2.2) * (4 * ε ^ 2 * D.BNorm (k + 1) h) := by
          intro t
          rw [hperdef]
          have h1 := hhom t.1 t.2.1 t.2.2 (truncDiff D ρ ε h t.1 t.2.1 t.2.2)
            (htd t.1 t.2.1 t.2.2).1 (htd t.1 t.2.1 t.2.2).2
          have hCt0 : 0 ≤ 2 * Ct t.1 t.2.1 t.2.2 := by
            have := (hCt t.1 t.2.1 t.2.2).1; linarith
          refine h1.trans ?_
          refine (mul_le_mul_of_nonneg_left (hTrunc t.1 t.2.1 t.2.2) hCt0).trans ?_
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hBle t.1 t.2.1 t.2.2)
              (mul_nonneg (by norm_num) (sq_nonneg ε))) hCt0
        calc (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (per t)))
            ≤ ∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                (2 * Ct t.1 t.2.1 t.2.2) * (4 * ε ^ 2 * D.BNorm (k + 1) h) :=
              Finset.sum_le_sum fun t _ => hstep t
          _ = (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                2 * Ct t.1 t.2.1 t.2.2) * (4 * ε ^ 2 * D.BNorm (k + 1) h) := by
              simp only [Finset.sum_mul]
      have hfin : CSq k (fourierCoeff (D.Rper j (D.J ρ ε h - h) a b))
          ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
              * ((∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    2 * Ct t.1 t.2.1 t.2.2) * (4 * ε ^ 2 * D.BNorm (k + 1) h)) := by
        calc CSq k (fourierCoeff (D.Rper j (D.J ρ ε h - h) a b))
            = CSq k (fun m => ∑ t, fourierCoeff (per t) m) := by rw [hcoeff]
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
                * ∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    CSq k (fourierCoeff (per t)) :=
              CSq_sum_le k _ (fun t => summable_weighted_fourierCoeff_of_contDiff (per t)
                (hper_t t).1 (hper_t t).2 k)
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
                * ((∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                      2 * Ct t.1 t.2.1 t.2.2) * (4 * ε ^ 2 * D.BNorm (k + 1) h)) :=
              mul_le_mul_of_nonneg_left hsum_terms (by positivity)
      ------------------------------------------------------------------------------------
      -- 8. the arithmetic: `ε² ≤ ε` and `ε ≤ 1`
      ------------------------------------------------------------------------------------
      have hε2 : ε ^ 2 ≤ ε := by
        calc ε ^ 2 = ε * ε := by ring
          _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hε.le
          _ = ε := mul_one ε
      have hKnn : (0 : ℝ) ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E)) : ℝ) *
          (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            2 * Ct t.1 t.2.1 t.2.2) * 4 := by
        refine mul_nonneg (mul_nonneg (by positivity) ?_) (by norm_num)
        exact Finset.sum_nonneg fun t _ => by have := (hCt t.1 t.2.1 t.2.2).1; linarith
      calc CSq k (fourierCoeff (D.Rper j (D.J ρ ε h - h) a b))
          ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
              * ((∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    2 * Ct t.1 t.2.1 t.2.2) * (4 * ε ^ 2 * D.BNorm (k + 1) h)) := hfin
        _ = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
              (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                2 * Ct t.1 t.2.1 t.2.2) * 4 * ε ^ 2) * D.BNorm (k + 1) h := by ring
        _ ≤ ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
              (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                2 * Ct t.1 t.2.1 t.2.2) * 4 * ε) * D.BNorm (k + 1) h := by
              refine mul_le_mul_of_nonneg_right ?_ ?_
              · calc (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                      Fin (Module.finrank ℝ E)) : ℝ) *
                    (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                      2 * Ct t.1 t.2.1 t.2.2) * 4 * ε ^ 2
                  = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                      Fin (Module.finrank ℝ E)) : ℝ) *
                    (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                      2 * Ct t.1 t.2.1 t.2.2) * 4) * ε ^ 2 := by ring
                _ ≤ ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                      Fin (Module.finrank ℝ E)) : ℝ) *
                    (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                      2 * Ct t.1 t.2.1 t.2.2) * 4) * ε :=
                    mul_le_mul_of_nonneg_left hε2 hKnn
                _ = (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                      Fin (Module.finrank ℝ E)) : ℝ) *
                    (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                      2 * Ct t.1 t.2.1 t.2.2) * 4 * ε := by ring
              · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ =>
                  Finset.sum_nonneg fun b _ => CSq_nonneg (k + 1) _
        _ = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
              (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                2 * Ct t.1 t.2.1 t.2.2) * 4) * (ε * D.BNorm (k + 1) h) := by ring
  --------------------------------------------------------------------------------------
  -- assembly over `(j,a,b)`
  --------------------------------------------------------------------------------------
  choose Cf hCf using hmain
  refine ⟨∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    Cf j a b, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => (hCf j a b).1
  · intro ε hε hε1 h hsm
    calc D.BNorm k (D.J ρ ε h - h)
        = ∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            CSq k (fourierCoeff (D.Rper j (D.J ρ ε h - h) a b)) := rfl
      _ ≤ ∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Cf j a b * (ε * D.BNorm (k + 1) h) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ =>
            Finset.sum_le_sum fun b _ => (hCf j a b).2 ε hε hε1 h hsm
      _ = (∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Cf j a b) * ε * D.BNorm (k + 1) h := by
          simp only [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => ?_
          ring

end Work.Diff.STE.B3
