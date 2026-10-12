import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.sum_normSq_bogBShift_le
import Submission.Work.BoseBoxFock.KzOpC
import Submission.Work.BoseBoxFock.bessel_honest
import Submission.Work.BoseBoxFock.honest_NH_qw_le
import Submission.Work.BoseBoxFock.qw_Q3T_window_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bddBelow_valFS_honest`

`bddBelow_valFS_honest`: the window Rayleigh quotients of FS's substituted Hamiltonian
`KzOpFS ρ` (`eq:Kz`) are bounded below on FS's spectral window `1_{[0,𝓜]}(n₊)`
(`eq:LocalizedAftercNumber`), at the concrete honest box family `HonestBoxFam` and for every
`ρ ≥ 0`.  This is the crudest form of FS `lem:Roughbounds`: it is what makes the infimum
`KzValFS`/`valFS` (an `⨅` in `ℝ`) non-junk, hence it is needed both for the truth of the
statement and for the step `ciInf_le`/`valFS_le_rayleigh`
(`Submission/Work/BoseBoxFock/KafzHonest.lean` §11).

## The bound

`KzOpFS ρ` is an **explicit** finite sum of monomials of degree `≤ 3` in the box mode
operators `a_k`, `a_k†` (the rows of `eq:SubstKz`/`eq:Kz`: the gaps `n₊`, `n₊^H`, the
`c`-number, FS's `𝒦^Bog`, the `n₊`-row of `Q₂^ex`, the linear word `Q₂^{ex}`, the cubic
`Q₃`), each row carrying a scalar deduced from `Q3Env` and `ρ`.  On the window every mode
sum is bounded by `Cn·𝓜·‖g‖²` (Bessel + `NWindow_bp_N_le`), so each row is bounded below
by `-(explicit constant)·‖g‖²`; summing the eight rows gives the stated `∃ K`.

The one non-trivial input (the failure of naive Cauchy–Schwarz on `a_k†`) is that a
lowering operator *preserves* the window (`NWindow_a`, `NWindow_shift`), so
`Σ_j ‖a_j(a_k g)‖² ≤ Cn·𝓜·‖a_k g‖²`; the daggered monomials are then handled by the
adjoint identity `⟨a_k† X, g⟩ = ⟨X, a_k g⟩`, never by a norm bound on `a_k† g`.

Rows: `slot_gap`, `slot_NH`, `slot_one`, `slot_KzBogFS_ge`, `slot_nPlus`, `slot_lin`,
`slot_Q2ex`, and the delegated `qw_Q3T_window_ge` (`BoseBoxFock/qw_Q3T_window_ge.lean`);
the assembly is `KzOpFS_window_ge`, and the honest data (`bessel_honest`, the `n₊^H` bound
`honest_NH_qw_le`, `NWindow_mono`) feeds the target.
-/

noncomputable section
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 0. Elementary helpers -/

lemma qw_finset_sum {ι : Type*} (F : Work.BoseB7.FockData Mode) (g : F.H) (s : Finset ι)
    (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw g (∑ i ∈ s, X i) = ∑ i ∈ s, F.qw g (X i) := by
  simp only [Work.BoseB7.FockData.qw, LinearMap.sum_apply, map_sum]

lemma qw_one (F : Work.BoseB7.FockData Mode) (g : F.H) :
    F.qw g (1 : F.H →ₗ[ℝ] F.H) = F.normSq g := rfl

lemma normSq_a_eq_qw_nOp (F : Work.BoseB7.FockData Mode) (k : Mode) (f : F.H) :
    F.normSq (F.a k f) = F.qw f (F.nOp k) := by
  simp only [Work.BoseB7.FockData.normSq, Work.BoseB7.FockData.qw,
    Work.BoseB7.FockData.nOp, LinearMap.comp_apply]
  exact (F.aDag_adjoint k (F.a k f) f).symm

lemma abs_qw_le (F : Work.BoseB7.FockData Mode) (g : F.H) (X : F.H →ₗ[ℝ] F.H) :
    |F.qw g X| ≤ (F.normSq (X g) + F.normSq g) / 2 := by
  have h := Work.BoseB7.SumABound.bp_abs_le F (X g) g
  simpa only [Work.BoseB7.FockData.qw, Work.BoseB7.FockData.normSq] using h

/-- A single summand is at most the sum (nonnegative terms). -/
lemma le_sum_of_nonneg {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ ∑ j : ι, f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

/-- Reindexing a finite sum over an additive commutative group by negation. -/
lemma sum_neg_index' {ι : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    (∑ i : ι, f (-i)) = ∑ i : ι, f i :=
  Equiv.sum_comp (Equiv.neg ι) f

/-- The window+Bessel sum bound: `Σ_k ⟨g, n_k g⟩ ≤ Cn·M·‖g‖²`. -/
lemma sum_qw_nOp_le (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    {M Cn : ℝ} (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {g : F.H} (hg : T.NWindow M g) :
    (∑ k : Mode, F.qw g (F.nOp k)) ≤ Cn * M * F.normSq g := by
  have hTN : F.bp (T.N g) g ≤ M * F.normSq g := Work.BoseB7A.NWindow_bp_N_le F T hM hg
  have h1 : F.bp ((∑ k : Mode, F.nOp k) g) g ≤ Cn * F.bp (T.N g) g := hBessel g
  have h2 : Cn * F.bp (T.N g) g ≤ Cn * (M * F.normSq g) :=
    mul_le_mul_of_nonneg_left hTN hCn0
  have h3 : (∑ k : Mode, F.qw g (F.nOp k)) = F.bp ((∑ k : Mode, F.nOp k) g) g := by
    rw [← qw_finset_sum]
    rfl
  rw [h3]
  linarith [h1, h2]

/-- The double-`a` sum bound: `Σ_j ‖a_j (a_k g)‖² ≤ Cn·M·‖a_k g‖²`. -/
lemma sum_normSq_a_comp_le (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    {M Cn : ℝ} (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {g : F.H} (hg : T.NWindow M g) (k : Mode) :
    (∑ j : Mode, F.normSq (F.a j (F.a k g))) ≤ Cn * M * F.normSq (F.a k g) := by
  have hwin : T.NWindow M (F.a k g) := T.NWindow_a k hg
  have hTN : F.bp (T.N (F.a k g)) (F.a k g) ≤ M * F.normSq (F.a k g) :=
    Work.BoseB7A.NWindow_bp_N_le F T hM hwin
  have h1 : F.bp ((∑ j : Mode, F.nOp j) (F.a k g)) (F.a k g)
      ≤ Cn * F.bp (T.N (F.a k g)) (F.a k g) := hBessel (F.a k g)
  have h2 : (∑ j : Mode, F.normSq (F.a j (F.a k g)))
      = F.bp ((∑ j : Mode, F.nOp j) (F.a k g)) (F.a k g) :=
    (Work.BoseBogFS.bp_nOp_sum_eq F (F.a k g)).symm
  have h3 : Cn * F.bp (T.N (F.a k g)) (F.a k g) ≤ Cn * (M * F.normSq (F.a k g)) :=
    mul_le_mul_of_nonneg_left hTN hCn0
  rw [h2]
  linarith [h1, h3]

/-- The abstract sign helper: if `0 ≤ X ≤ B·Q` and `B·Q ≥ 0`, then `-(|c|·B)·Q ≤ c·X`. -/
lemma neg_abs_mul_le_smul {c X B Q : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ B * Q) (hBQ : 0 ≤ B * Q) :
    -(|c| * B) * Q ≤ c * X := by
  by_cases hc : 0 ≤ c
  · have h2 : 0 ≤ c * X := mul_nonneg hc hX0
    have h3 : 0 ≤ |c| * B * Q := by
      rw [abs_of_nonneg hc, mul_assoc]
      exact mul_nonneg hc hBQ
    nlinarith [h2, h3]
  · have hcneg : c < 0 := not_le.mp hc
    have h2 : c * (B * Q) ≤ c * X := mul_le_mul_of_nonpos_left hX (le_of_lt hcneg)
    have h4 : |c| = -c := abs_of_neg hcneg
    nlinarith [h2, h4]


/-! ## 1. The slot bounds -/

/-- Slot 1: the gap row `c • T.N`. -/
lemma slot_gap (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (c M : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ c * F.qw g T.N :=
  ⟨-(|c| * M), fun g hg => neg_abs_mul_le_smul (T.N_nonneg g)
    (Work.BoseB7A.NWindow_bp_N_le F T hM hg) (mul_nonneg hM (F.normSq_nonneg g))⟩

/-- Slot 2: the `n₊^H` row `c • T.NH`. -/
lemma slot_NH (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (c KNH M : ℝ) (hM : 0 ≤ M) (hKNH : 0 ≤ KNH)
    (hNH : ∀ g : F.H, T.NWindow M g → F.bp (T.NH g) g ≤ KNH * F.normSq g) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ c * F.qw g T.NH :=
  ⟨-(|c| * KNH), fun g hg => neg_abs_mul_le_smul (T.NH_nonneg g) (hNH g hg)
    (mul_nonneg hKNH (F.normSq_nonneg g))⟩

/-- Slot 3: the `c`-number row `c • 1`. -/
lemma slot_one (F : Work.BoseB7.FockData Mode) (c : ℝ) :
    ∃ K : ℝ, ∀ g : F.H, K * F.normSq g ≤ c * F.qw g (1 : F.H →ₗ[ℝ] F.H) := by
  refine ⟨-|c|, fun g => ?_⟩
  rw [qw_one]
  have hQ := F.normSq_nonneg g
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]; nlinarith
  · rw [abs_of_neg (not_le.mp hc)]; ring_nf; nlinarith

/-- Slot 5: the `n₊` row `c • Σ_k n_k`. -/
lemma slot_nPlus (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (c Cn M : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g →
      K * F.normSq g ≤ c * (∑ k : Mode, F.qw g (F.nOp k)) :=
  ⟨-(|c| * (Cn * M)), fun g hg => neg_abs_mul_le_smul
    (Finset.sum_nonneg fun k _ => by
      rw [← normSq_a_eq_qw_nOp]; exact F.bp_nonneg _)
    (sum_qw_nOp_le F T hM hCn0 hBessel hg)
    (mul_nonneg (mul_nonneg hCn0 hM) (F.normSq_nonneg g))⟩

/-- Slot 7: the `Q₂^{ex}` row. -/
lemma slot_Q2ex (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ Cn M : ℝ)
    (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g →
      K * F.normSq g ≤ F.qw g (F.Q2ex (Work.BoseFixR.KzEnvAt E ρ)) := by
  set E' := Work.BoseFixR.KzEnvAt E ρ with hE'
  set φ : Mode → ℝ := fun k => E'.rho * (E'.W1omega k + E'.W1omega0) with hφ
  set Fs : ℝ := ∑ k ∈ Work.BoseB7.excited Mode, |φ k| with hFs
  have hFs0 : 0 ≤ Fs := by
    rw [hFs]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ⟨-(Fs * (Cn * M)), fun g hg => ?_⟩
  have hexp : F.qw g (F.Q2ex E')
      = ∑ k ∈ Work.BoseB7.excited Mode, φ k * F.qw g (F.nOp k) := by
    rw [Work.BoseB7.FockData.Q2ex, qw_finset_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Work.BoseB7.FockData.qw_smul]
  rw [hexp]
  have hxnn : ∀ k ∈ Work.BoseB7.excited Mode, 0 ≤ F.qw g (F.nOp k) := fun k _ => by
    rw [← normSq_a_eq_qw_nOp]; exact F.bp_nonneg _
  have hsub : (∑ k ∈ Work.BoseB7.excited Mode, F.qw g (F.nOp k)) ≤ Cn * M * F.normSq g :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun x _ _ => by rw [← normSq_a_eq_qw_nOp]; exact F.bp_nonneg _))
      (sum_qw_nOp_le F T hM hCn0 hBessel hg)
  have hφle : ∀ k ∈ Work.BoseB7.excited Mode, |φ k| ≤ Fs := fun k hk => by
    rw [hFs]
    calc |φ k| = ∑ i ∈ ({k} : Finset Mode), |φ i| := by simp
      _ ≤ ∑ i ∈ Work.BoseB7.excited Mode, |φ i| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.mpr hk) (fun i _ _ => abs_nonneg _)
  have hkey : -Fs * (∑ k ∈ Work.BoseB7.excited Mode, F.qw g (F.nOp k))
      ≤ ∑ k ∈ Work.BoseB7.excited Mode, φ k * F.qw g (F.nOp k) := by
    have hle : -(∑ k ∈ Work.BoseB7.excited Mode, |φ k| * F.qw g (F.nOp k))
        ≤ ∑ k ∈ Work.BoseB7.excited Mode, φ k * F.qw g (F.nOp k) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun k hk => by
        simpa only [neg_mul] using
          mul_le_mul_of_nonneg_right (neg_abs_le (φ k)) (hxnn k hk)
    have hbound : (∑ k ∈ Work.BoseB7.excited Mode, |φ k| * F.qw g (F.nOp k))
        ≤ Fs * (∑ k ∈ Work.BoseB7.excited Mode, F.qw g (F.nOp k)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk =>
        mul_le_mul_of_nonneg_right (hφle k hk) (hxnn k hk)
    linarith
  have hfinal : -(Fs * (Cn * M)) * F.normSq g
      ≤ -Fs * (∑ k ∈ Work.BoseB7.excited Mode, F.qw g (F.nOp k)) := by
    nlinarith [hsub, hFs0, F.normSq_nonneg g]
  linarith [hkey, hfinal]

/-- Slot 6: the linear row `T.linOpT`. -/
lemma slot_lin (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (ρ M : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g →
      K * F.normSq g ≤ F.qw g (T.linOpT (Work.BoseFixR.KzEnvAt E ρ)) := by
  set E' := Work.BoseFixR.KzEnvAt E ρ with hE'
  set d : ℝ := E'.rho * E'.z * E'.W1omega0 with hd
  set Es : ℝ := ∑ s ∈ Work.BoseB7.excited Mode, |E'.hatChiSq s| with hEs
  have hEs0 : 0 ≤ Es := by
    rw [hEs]; exact Finset.sum_nonneg fun s _ => abs_nonneg _
  have hS : ∀ s ∈ Work.BoseB7.excited Mode, s ≠ 0 := fun s hs =>
    (Finset.mem_erase.mp hs).1
  refine ⟨-(|d| * Es * (M + 1)), fun g hg => ?_⟩
  have hta : (∑ s ∈ Work.BoseB7.excited Mode, F.normSq (T.ta s g)) ≤ M * F.normSq g :=
    Work.BoseB7A.NWindow_ta_sum F T hM hg (Work.BoseB7.excited Mode) hS
  have hexp : F.qw g (T.linOpT E')
      = d * (∑ s ∈ Work.BoseB7.excited Mode,
          E'.hatChiSq s * (F.qw g (T.taDag s) + F.qw g (T.ta s))) := by
    rw [Work.BoseB7A.TildeData.linOpT, Work.BoseB7.FockData.qw_smul, qw_finset_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by
      rw [Work.BoseB7.FockData.qw_smul, Work.BoseB7.FockData.qw_add]
  have hsym : ∀ s : Mode, F.qw g (T.taDag s) = F.qw g (T.ta s) := fun s => by
    simp only [Work.BoseB7.FockData.qw]
    rw [T.taDag_adjoint, F.bp_symm]
  have habs : ∀ s : Mode,
      |F.qw g (T.taDag s) + F.qw g (T.ta s)| ≤ F.normSq (T.ta s g) + F.normSq g := by
    intro s
    have hb := abs_qw_le F g (T.ta s)
    rw [hsym s]
    have h := abs_add_le (F.qw g (T.ta s)) (F.qw g (T.ta s))
    have h2 : |F.qw g (T.ta s) + F.qw g (T.ta s)| ≤ 2 * |F.qw g (T.ta s)| := by
      nlinarith [h]
    have h3 : 2 * |F.qw g (T.ta s)| ≤ F.normSq (T.ta s g) + F.normSq g := by
      have h4 : |F.qw g (T.ta s)| ≤ (F.normSq (T.ta s g) + F.normSq g) / 2 := hb
      linarith
    linarith
  have htsum0 : 0 ≤ ∑ s ∈ Work.BoseB7.excited Mode, F.normSq (T.ta s g) :=
    Finset.sum_nonneg fun s _ => F.bp_nonneg _
  have hQ0 : 0 ≤ F.normSq g := F.normSq_nonneg g
  have hφle : ∀ s ∈ Work.BoseB7.excited Mode, |E'.hatChiSq s| ≤ Es := fun s hs => by
    rw [hEs]
    calc |E'.hatChiSq s| = ∑ i ∈ ({s} : Finset Mode), |E'.hatChiSq i| := by simp
      _ ≤ ∑ i ∈ Work.BoseB7.excited Mode, |E'.hatChiSq i| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.singleton_subset_iff.mpr hs) (fun i _ _ => abs_nonneg _)
  have h_abs : |∑ s ∈ Work.BoseB7.excited Mode,
        E'.hatChiSq s * (F.qw g (T.taDag s) + F.qw g (T.ta s))|
      ≤ Es * (M + 1) * F.normSq g := by
    calc |∑ s ∈ Work.BoseB7.excited Mode,
          E'.hatChiSq s * (F.qw g (T.taDag s) + F.qw g (T.ta s))|
        ≤ ∑ s ∈ Work.BoseB7.excited Mode,
            |E'.hatChiSq s * (F.qw g (T.taDag s) + F.qw g (T.ta s))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s ∈ Work.BoseB7.excited Mode,
            |E'.hatChiSq s| * |F.qw g (T.taDag s) + F.qw g (T.ta s)| := by
          exact Finset.sum_congr rfl fun s _ => abs_mul _ _
      _ ≤ ∑ s ∈ Work.BoseB7.excited Mode,
            |E'.hatChiSq s| * (F.normSq (T.ta s g) + F.normSq g) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (habs s) (abs_nonneg _)
      _ ≤ Es * ((∑ s ∈ Work.BoseB7.excited Mode, F.normSq (T.ta s g)) + F.normSq g) := by
          have hsplit : (∑ s ∈ Work.BoseB7.excited Mode,
                |E'.hatChiSq s| * (F.normSq (T.ta s g) + F.normSq g))
              = (∑ s ∈ Work.BoseB7.excited Mode, |E'.hatChiSq s| * F.normSq (T.ta s g))
                + Es * F.normSq g := by
            rw [hEs, Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
          rw [hsplit]
          have h1 : (∑ s ∈ Work.BoseB7.excited Mode,
                |E'.hatChiSq s| * F.normSq (T.ta s g))
              ≤ Es * (∑ s ∈ Work.BoseB7.excited Mode, F.normSq (T.ta s g)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun s hs =>
              mul_le_mul_of_nonneg_right (hφle s hs) (F.bp_nonneg _)
          nlinarith [h1, hEs0, hQ0]
      _ ≤ Es * ((M + 1) * F.normSq g) := by
          refine mul_le_mul_of_nonneg_left ?_ hEs0
          linarith [hta]
      _ = Es * (M + 1) * F.normSq g := by ring
  have hstep : -(|d| * Es * (M + 1)) * F.normSq g
      ≤ d * (∑ s ∈ Work.BoseB7.excited Mode,
          E'.hatChiSq s * (F.qw g (T.taDag s) + F.qw g (T.ta s))) := by
    have h1 : |d * (∑ s ∈ Work.BoseB7.excited Mode,
        E'.hatChiSq s * (F.qw g (T.taDag s) + F.qw g (T.ta s)))|
        ≤ |d| * (Es * (M + 1) * F.normSq g) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h_abs (abs_nonneg d)
    have h2 := neg_abs_le (d * (∑ s ∈ Work.BoseB7.excited Mode,
        E'.hatChiSq s * (F.qw g (T.taDag s) + F.qw g (T.ta s))))
    nlinarith [h1, h2]
  rw [hexp]
  exact hstep

/-! ## 2. The assembly -/

/-- **The assembly of `KzOpFS` on the window.**  From the window/Bessel data, an upper bound
for the honest `n₊^H` and the two delegated slot bounds (`KzBogFS`, `Q3T`), the substituted
Hamiltonian `KzOpFS ρ` is bounded below on FS's window `1_{[0,𝓜]}(n₊)`. -/
theorem KzOpFS_window_ge
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 ρ M Cn KNH : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn) (hKNH : 0 ≤ KNH)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (hNH : ∀ f : F.H, T.NWindow M f → F.bp (T.NH f) f ≤ KNH * F.normSq f)
    (hKBog : ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ F.qw g (KzBogFS F E ρ))
    (hQ3T : ∃ K : ℝ, ∀ g : F.H, T.NWindow M g →
      K * F.normSq g ≤ F.qw g (T.Q3T (Work.BoseFixR.KzEnvAt E ρ))) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ F.qw g (KzOpFS F T E gHat0 ρ) := by
  obtain ⟨K4, h4⟩ := hKBog
  obtain ⟨K8, h8⟩ := hQ3T
  obtain ⟨K1, h1⟩ := slot_gap F T (E.b / (2 * E.ell ^ 2)) M hM
  obtain ⟨K2, h2⟩ := slot_NH F T (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) KNH M hM hKNH hNH
  obtain ⟨K3, h3⟩ := slot_one F (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
      + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0))
  obtain ⟨K5, h5⟩ := slot_nPlus F T ((ρ - E.mu) * E.W1 0) Cn M hM hCn0 hBessel
  obtain ⟨K6, h6⟩ := slot_lin F T E ρ M hM
  obtain ⟨K7, h7⟩ := slot_Q2ex F T E ρ Cn M hM hCn0 hBessel
  refine ⟨K1 + K2 + K3 + K4 + K5 + K6 + K7 + K8, fun g hg => ?_⟩
  have h1' := h1 g hg
  have h2' := h2 g hg
  have h3' := h3 g
  have h4' := h4 g hg
  have h5' := h5 g hg
  have h6' := h6 g hg
  have h7' := h7 g hg
  have h8' := h8 g hg
  rw [qw_one] at h3'
  simp only [KzOpFS, Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_smul, qw_one,
    qw_finset_sum]
  have hsum : (K1 + K2 + K3 + K4 + K5 + K6 + K7 + K8) * F.normSq g
      = K1 * F.normSq g + K2 * F.normSq g + K3 * F.normSq g + K4 * F.normSq g
        + K5 * F.normSq g + K6 * F.normSq g + K7 * F.normSq g + K8 * F.normSq g := by ring
  rw [hsum]
  linarith [h1', h2', h3', h4', h5', h6', h7', h8']


/-! ## 2b. The `𝒦^Bog` row (`KzBogFS`)

FS `eq:BogHamPositive-1` split into its three rows: the diagonal `A_k(n_k+n_{-k})`, the
pairing `B_k(a_ka_{-k}+a_k†a_{-k}†)` (`A_k = τ_k+ρŴ₁(k)`, `B_k = ρŴ₁(k)`) and the linear
word `C_k(a_k+a_k†+a_{-k}+a_{-k}†)` (`C_k = (ρ−μ)Ŵ₁(0)χ̂_k·√(ρℓ³)`).  Each row is bounded
below by the absolute value of its coefficient times a window norm: `Σ_k ⟨g,n_kg⟩ ≤ Cn·𝓜‖g‖²`
for the first, the *pair* bound `Σ_k ‖a_ka_{-k}g‖² ≤ (Cn𝓜)²‖g‖²` (from `sum_normSq_a_comp_le`
at `-k`, using `NWindow_a`) for the h.c.-pairs, and Cauchy--Schwarz for the linear word. -/
theorem slot_KzBogFS_ge {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (ρ M Cn : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ K : ℝ, ∀ g : F.H, T.NWindow M g → K * F.normSq g ≤ F.qw g (KzBogFS F E ρ) := by
  set A : Mode → ℝ := fun k => E.tau k + ρ * E.W1 k with hA
  set B : Mode → ℝ := fun k => ρ * E.W1 k with hB
  set C : Mode → ℝ := fun k => (ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3) with hC
  set Aq : ℝ := ∑ k : Mode, |A k| with hAq
  set Bq : ℝ := ∑ k : Mode, |B k| with hBq
  set Cq : ℝ := ∑ k : Mode, |C k| with hCq
  set m0 : ℝ := (Fintype.card Mode : ℝ) with hm0
  have hAq0 : 0 ≤ Aq := by
    rw [hAq]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hBq0 : 0 ≤ Bq := by
    rw [hBq]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hCq0 : 0 ≤ Cq := by
    rw [hCq]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hAqle : ∀ k : Mode, |A k| ≤ Aq := fun k =>
    le_sum_of_nonneg (fun j => |A j|) (fun j => abs_nonneg _) k
  have hBqle : ∀ k : Mode, |B k| ≤ Bq := fun k =>
    le_sum_of_nonneg (fun j => |B j|) (fun j => abs_nonneg _) k
  have hCqle : ∀ k : Mode, |C k| ≤ Cq := fun k =>
    le_sum_of_nonneg (fun j => |C j|) (fun j => abs_nonneg _) k
  refine ⟨-(Aq * Cn * M + Bq * ((Cn * M) ^ 2 + m0) + Cq * (Cn * M + m0)),
    fun g hg => ?_⟩
  have hQ0 : 0 ≤ F.normSq g := F.normSq_nonneg g
  have hx0 : ∀ k : Mode, 0 ≤ F.qw g (F.nOp k) := fun k => by
    rw [← normSq_a_eq_qw_nOp]; exact F.bp_nonneg _
  have hx : (∑ k : Mode, F.qw g (F.nOp k)) ≤ Cn * M * F.normSq g :=
    sum_qw_nOp_le F T hM hCn0 hBessel hg
  have hy0 : ∀ k : Mode, 0 ≤ F.normSq (F.a k (F.a (-k) g)) := fun k => F.bp_nonneg _
  have hy0n : ∀ k : Mode, 0 ≤ F.normSq (F.a (-k) (F.a k g)) := fun k => F.bp_nonneg _
  have hy : (∑ k : Mode, F.normSq (F.a k (F.a (-k) g))) ≤ (Cn * M) ^ 2 * F.normSq g := by
    have h1 : ∀ k : Mode, F.normSq (F.a k (F.a (-k) g))
        ≤ Cn * M * F.normSq (F.a (-k) g) := fun k =>
      le_trans (le_sum_of_nonneg (fun j => F.normSq (F.a j (F.a (-k) g)))
          (fun j => F.bp_nonneg _) k)
        (sum_normSq_a_comp_le F T hM hCn0 hBessel hg (-k))
    have h2 : (∑ k : Mode, F.normSq (F.a (-k) g)) = ∑ k : Mode, F.qw g (F.nOp k) := by
      rw [sum_neg_index' (fun k => F.normSq (F.a k g))]
      exact Finset.sum_congr rfl fun k _ => normSq_a_eq_qw_nOp F k g
    calc (∑ k : Mode, F.normSq (F.a k (F.a (-k) g)))
        ≤ ∑ k : Mode, Cn * M * F.normSq (F.a (-k) g) := Finset.sum_le_sum fun k _ => h1 k
      _ = Cn * M * (∑ k : Mode, F.normSq (F.a (-k) g)) := by rw [Finset.mul_sum]
      _ = Cn * M * (∑ k : Mode, F.qw g (F.nOp k)) := by rw [h2]
      _ ≤ Cn * M * (Cn * M * F.normSq g) :=
          mul_le_mul_of_nonneg_left hx (mul_nonneg hCn0 hM)
      _ = (Cn * M) ^ 2 * F.normSq g := by ring
  have hxn : (∑ k : Mode, F.qw g (F.nOp (-k))) = ∑ k : Mode, F.qw g (F.nOp k) :=
    sum_neg_index' (fun k => F.qw g (F.nOp k))
  have hyn : (∑ k : Mode, F.normSq (F.a (-k) (F.a k g)))
      = ∑ k : Mode, F.normSq (F.a k (F.a (-k) g)) := by
    rw [← sum_neg_index' (fun k => F.normSq (F.a k (F.a (-k) g)))]
    exact Finset.sum_congr rfl fun k _ => by rw [neg_neg]
  have hQsum : (∑ _k : Mode, F.normSq g) = m0 * F.normSq g := by
    rw [hm0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2Q : (∑ _k : Mode, 2 * F.normSq g) = 2 * (m0 * F.normSq g) := by
    rw [hm0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- the expansion of `qw` over the mode lattice
  have hexp : F.qw g (KzBogFS F E ρ)
      = ∑ k : Mode, (1 / 2) * (A k * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
          + B k * (F.qw g (F.a k ∘ₗ F.a (-k)) + F.qw g (F.aDag k ∘ₗ F.aDag (-k)))
          + C k * (F.qw g (F.a k) + F.qw g (F.aDag k) + F.qw g (F.a (-k))
              + F.qw g (F.aDag (-k)))) := by
    simp only [KzBogFS, Work.BoseB7.FockData.qw_add, Work.BoseB7.FockData.qw_smul,
      qw_finset_sum, hA, hB, hC]
  -- the per-mode lower bound
  have hlin_k : ∀ k : Mode, F.qw g (F.aDag k) = F.qw g (F.a k) := fun k => by
    simp only [Work.BoseB7.FockData.qw]
    rw [F.aDag_adjoint, F.bp_symm]
  have hpair_k : ∀ k : Mode,
      F.qw g (F.aDag k ∘ₗ F.aDag (-k)) = F.qw g (F.a (-k) ∘ₗ F.a k) := fun k => by
    simp only [Work.BoseB7.FockData.qw, LinearMap.comp_apply]
    rw [F.aDag_adjoint k (F.aDag (-k) g) g, F.aDag_adjoint (-k) g (F.a k g), F.bp_symm]
  have hp1 : ∀ k : Mode,
      |F.qw g (F.a k ∘ₗ F.a (-k))| ≤ (F.normSq (F.a k (F.a (-k) g)) + F.normSq g) / 2 :=
    fun k => by
      have h := abs_qw_le F g (F.a k ∘ₗ F.a (-k))
      simpa only [LinearMap.comp_apply] using h
  have hp2 : ∀ k : Mode,
      |F.qw g (F.aDag k ∘ₗ F.aDag (-k))| ≤ (F.normSq (F.a (-k) (F.a k g)) + F.normSq g) / 2 :=
    fun k => by
      rw [hpair_k k]
      have h := abs_qw_le F g (F.a (-k) ∘ₗ F.a k)
      simpa only [LinearMap.comp_apply] using h
  have hlinb : ∀ k : Mode,
      |F.qw g (F.a k) + F.qw g (F.aDag k) + F.qw g (F.a (-k)) + F.qw g (F.aDag (-k))|
        ≤ F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g := fun k => by
    have h1 : |F.qw g (F.a k)| ≤ (F.normSq (F.a k g) + F.normSq g) / 2 := abs_qw_le F g (F.a k)
    have h2 : |F.qw g (F.aDag k)| ≤ (F.normSq (F.a k g) + F.normSq g) / 2 := by
      rw [hlin_k k]; exact abs_qw_le F g (F.a k)
    have h3 : |F.qw g (F.a (-k))| ≤ (F.normSq (F.a (-k) g) + F.normSq g) / 2 :=
      abs_qw_le F g (F.a (-k))
    have h4 : |F.qw g (F.aDag (-k))| ≤ (F.normSq (F.a (-k) g) + F.normSq g) / 2 := by
      rw [hlin_k (-k)]; exact abs_qw_le F g (F.a (-k))
    have h5 := abs_add_le (F.qw g (F.a k) + F.qw g (F.aDag k) + F.qw g (F.a (-k)))
      (F.qw g (F.aDag (-k)))
    have h6 := abs_add_le (F.qw g (F.a k) + F.qw g (F.aDag k)) (F.qw g (F.a (-k)))
    have h7 := abs_add_le (F.qw g (F.a k)) (F.qw g (F.aDag k))
    rw [normSq_a_eq_qw_nOp F k g] at h1 h2
    rw [normSq_a_eq_qw_nOp F (-k) g] at h3 h4
    linarith [h1, h2, h3, h4, h5, h6, h7, hQ0]
  have hper : ∀ k : Mode,
      -((1 / 2) * (|A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
        + |B k| * (F.normSq (F.a k (F.a (-k) g))
            + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g)
        + |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g)))
      ≤ (1 / 2) * (A k * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
          + B k * (F.qw g (F.a k ∘ₗ F.a (-k)) + F.qw g (F.aDag k ∘ₗ F.aDag (-k)))
          + C k * (F.qw g (F.a k) + F.qw g (F.aDag k) + F.qw g (F.a (-k))
              + F.qw g (F.aDag (-k)))) := fun k => by
    have hxA : 0 ≤ F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) := add_nonneg (hx0 k) (hx0 (-k))
    have h1 : -(|A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))))
        ≤ A k * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))) := by
      have h := neg_le_abs (A k * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))))
      rw [abs_mul, abs_of_nonneg hxA] at h
      linarith [h]
    have h2 : -(|B k| * (F.normSq (F.a k (F.a (-k) g))
          + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g))
        ≤ B k * (F.qw g (F.a k ∘ₗ F.a (-k)) + F.qw g (F.aDag k ∘ₗ F.aDag (-k))) := by
      have hZ : |F.qw g (F.a k ∘ₗ F.a (-k)) + F.qw g (F.aDag k ∘ₗ F.aDag (-k))|
          ≤ F.normSq (F.a k (F.a (-k) g)) + F.normSq (F.a (-k) (F.a k g))
            + 2 * F.normSq g := by
        have h5 := abs_add_le (F.qw g (F.a k ∘ₗ F.a (-k)))
          (F.qw g (F.aDag k ∘ₗ F.aDag (-k)))
        linarith [h5, hp1 k, hp2 k, hy0 k, hy0n k, hQ0]
      have h := neg_le_abs (B k * (F.qw g (F.a k ∘ₗ F.a (-k))
        + F.qw g (F.aDag k ∘ₗ F.aDag (-k))))
      rw [abs_mul] at h
      have hb := mul_le_mul_of_nonneg_left hZ (abs_nonneg (B k))
      linarith [h, hb]
    have h3 : -(|C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g))
        ≤ C k * (F.qw g (F.a k) + F.qw g (F.aDag k) + F.qw g (F.a (-k))
            + F.qw g (F.aDag (-k))) := by
      have h := neg_le_abs (C k * (F.qw g (F.a k) + F.qw g (F.aDag k)
        + F.qw g (F.a (-k)) + F.qw g (F.aDag (-k))))
      rw [abs_mul] at h
      have hb := mul_le_mul_of_nonneg_left (hlinb k) (abs_nonneg (C k))
      linarith [h, hb]
    linarith [h1, h2, h3]
  rw [hexp]
  have hSp : (∑ k : Mode, ((1 / 2) * (|A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
        + |B k| * (F.normSq (F.a k (F.a (-k) g))
            + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g)
        + |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g))))
      ≤ (Aq * Cn * M + Bq * ((Cn * M) ^ 2 + m0) + Cq * (Cn * M + m0))
        * F.normSq g := by
    have hAterm : (∑ k : Mode, |A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))))
        ≤ Aq * (2 * (Cn * M * F.normSq g)) := by
      calc (∑ k : Mode, |A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))))
          ≤ ∑ k : Mode, Aq * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))) :=
            Finset.sum_le_sum fun k _ =>
              mul_le_mul_of_nonneg_right (hAqle k) (add_nonneg (hx0 k) (hx0 (-k)))
        _ = Aq * (∑ k : Mode, (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))) := by
            rw [Finset.mul_sum]
        _ = Aq * (2 * (∑ k : Mode, F.qw g (F.nOp k))) := by
            rw [Finset.sum_add_distrib, hxn]; ring
        _ ≤ Aq * (2 * (Cn * M * F.normSq g)) :=
            mul_le_mul_of_nonneg_left (by linarith [hx]) hAq0
    have hBterm : (∑ k : Mode, |B k| * (F.normSq (F.a k (F.a (-k) g))
          + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g))
        ≤ Bq * (2 * ((Cn * M) ^ 2 * F.normSq g) + 2 * (m0 * F.normSq g)) := by
      calc (∑ k : Mode, |B k| * (F.normSq (F.a k (F.a (-k) g))
            + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g))
          ≤ ∑ k : Mode, Bq * (F.normSq (F.a k (F.a (-k) g))
              + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g) :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hBqle k)
              (by linarith [hy0 k, hy0n k, hQ0])
        _ = Bq * (∑ k : Mode, (F.normSq (F.a k (F.a (-k) g))
              + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g)) := by
            rw [Finset.mul_sum]
        _ = Bq * (2 * (∑ k : Mode, F.normSq (F.a k (F.a (-k) g)))
              + 2 * (m0 * F.normSq g)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hyn, h2Q]
            ring
        _ ≤ Bq * (2 * ((Cn * M) ^ 2 * F.normSq g) + 2 * (m0 * F.normSq g)) :=
            mul_le_mul_of_nonneg_left (by linarith [hy]) hBq0
    have hCterm : (∑ k : Mode, |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))
          + 2 * F.normSq g))
        ≤ Cq * (2 * (Cn * M * F.normSq g) + 2 * (m0 * F.normSq g)) := by
      calc (∑ k : Mode, |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g))
          ≤ ∑ k : Mode, Cq * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g) :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hCqle k)
              (by linarith [hx0 k, hx0 (-k), hQ0])
        _ = Cq * (∑ k : Mode, (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g)) := by
            rw [Finset.mul_sum]
        _ = Cq * (2 * (∑ k : Mode, F.qw g (F.nOp k)) + 2 * (m0 * F.normSq g)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hxn, h2Q]
            ring
        _ ≤ Cq * (2 * (Cn * M * F.normSq g) + 2 * (m0 * F.normSq g)) :=
            mul_le_mul_of_nonneg_left (by linarith [hx]) hCq0
    have hsplit : (∑ k : Mode, ((1 / 2) * (|A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
          + |B k| * (F.normSq (F.a k (F.a (-k) g))
              + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g)
          + |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g))))
        = (1 / 2) * ((∑ k : Mode, |A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))))
            + (∑ k : Mode, |B k| * (F.normSq (F.a k (F.a (-k) g))
                + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g))
            + (∑ k : Mode, |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k))
                + 2 * F.normSq g))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hsplit]
    nlinarith [hAterm, hBterm, hCterm, hQ0, hCn0, hM, hAq0, hBq0, hCq0,
      mul_nonneg hCn0 hM]
  have hneg : (∑ k : Mode, -((1 / 2) * (|A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
        + |B k| * (F.normSq (F.a k (F.a (-k) g))
            + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g)
        + |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g))))
      = -(∑ k : Mode, ((1 / 2) * (|A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
        + |B k| * (F.normSq (F.a k (F.a (-k) g))
            + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g)
        + |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g)))) := by
    rw [Finset.sum_neg_distrib]
  have hsum' : (∑ k : Mode, -((1 / 2) * (|A k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
        + |B k| * (F.normSq (F.a k (F.a (-k) g))
            + F.normSq (F.a (-k) (F.a k g)) + 2 * F.normSq g)
        + |C k| * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)) + 2 * F.normSq g))))
      ≤ ∑ k : Mode, (1 / 2) * (A k * (F.qw g (F.nOp k) + F.qw g (F.nOp (-k)))
          + B k * (F.qw g (F.a k ∘ₗ F.a (-k)) + F.qw g (F.aDag k ∘ₗ F.aDag (-k)))
          + C k * (F.qw g (F.a k) + F.qw g (F.aDag k) + F.qw g (F.a (-k))
              + F.qw g (F.aDag (-k)))) :=
    Finset.sum_le_sum fun k _ => hper k
  linarith [hsum', hneg, hSp]

/-! ## 3. The target -/

theorem bddBelow_valFS_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    ∀ ρ : ℝ, 0 ≤ ρ → BddBelow (Set.range (fun g :
        {g : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H //
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NWindow
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.bigM g ∧ g ≠ 0} =>
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw g.1
          (Work.BoseBoxFock.KzOpFS (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 ρ)
        / (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.normSq g.1)) := by
  intro ρ hρ
  set D : Work.BoseFixR.KzDatum := Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ with hD
  set M : ℝ := max D.E.bigM 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hwin : ∀ g : D.F.H, D.T.NWindow D.E.bigM g → D.T.NWindow M g := fun g hg =>
    D.T.NWindow_mono hg (le_max_left _ _)
  have hCn0 : (0 : ℝ) ≤ 48 / Real.pi := by positivity
  have hCn16 : 48 / Real.pi ≤ 16 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hBessel : ∀ f : D.F.H, D.F.bp ((∑ k : D.Mode, D.F.nOp k) f) f
      ≤ (48 / Real.pi) * D.F.bp (D.T.N f) f := by
    intro f
    simpa only [hD] using Work.BoseBoxFock.bessel_honest v h fc fu HM μ f
  have hNH : ∀ f : D.F.H, D.T.NWindow M f →
      D.F.bp (D.T.NH f) f ≤ ((1 / 32) * ((48 / Real.pi) * M)) * D.F.normSq f := by
    intro f hf
    have h1' : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
        ≤ (1 / 32) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) :=
      Work.BoseBoxFock.honest_NH_qw_le v h fc fu HM μ f
    have h1 : D.F.qw f D.T.NH
        ≤ (1 / 32) * D.F.qw f (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.nOp k) := by
      show (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
          ≤ (1 / 32) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw f
            (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
              (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k)
      exact h1'
    have hsplit : D.F.qw f (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.nOp k)
        = ∑ k ∈ Work.BoseB7.excited D.Mode, D.F.qw f (D.F.nOp k) :=
      qw_finset_sum D.F f _ _
    have hsub : (∑ k ∈ Work.BoseB7.excited D.Mode, D.F.qw f (D.F.nOp k))
        ≤ ∑ k : D.Mode, D.F.qw f (D.F.nOp k) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun x _ _ => by rw [← normSq_a_eq_qw_nOp]; exact D.F.bp_nonneg _)
    have hsum := sum_qw_nOp_le D.F D.T (M := M) hM0 hCn0 hBessel hf
    have h2 : D.F.qw f D.T.NH ≤ (1 / 32) * (∑ k : D.Mode, D.F.qw f (D.F.nOp k)) := by
      rw [hsplit] at h1
      linarith [h1, hsub]
    have h3 : (1 / 32) * (∑ k : D.Mode, D.F.qw f (D.F.nOp k))
        ≤ (1 / 32) * ((48 / Real.pi) * M * D.F.normSq f) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    have hone : D.F.bp (D.T.NH f) f = D.F.qw f D.T.NH := rfl
    rw [hone]
    nlinarith [h2, h3]
  have hKBog : ∃ K : ℝ, ∀ g : D.F.H, D.T.NWindow M g →
      K * D.F.normSq g ≤ D.F.qw g (KzBogFS D.F D.E ρ) :=
    Work.BoseBoxFock.slot_KzBogFS_ge D.F D.T D.E ρ M (48 / Real.pi) hM0 hCn0 hBessel
  have hQ3T : ∃ K : ℝ, ∀ g : D.F.H, D.T.NWindow M g →
      K * D.F.normSq g ≤ D.F.qw g (D.T.Q3T (Work.BoseFixR.KzEnvAt D.E ρ)) :=
    Work.BoseBoxFock.qw_Q3T_window_ge D.F D.T D.E M (48 / Real.pi) ρ hM0 hCn0 hCn16 hBessel
  obtain ⟨K, hK⟩ := Work.BoseBoxFock.KzOpFS_window_ge D.F D.T D.E D.gHat0 ρ M (48 / Real.pi)
    ((1 / 32) * ((48 / Real.pi) * M)) hM0 hCn0 (by positivity) hBessel hNH hKBog hQ3T
  refine ⟨K, ?_⟩
  rintro y ⟨g, rfl⟩
  have hnn : 0 ≤ D.F.normSq g.1 := D.F.normSq_nonneg g.1
  have hne : D.F.normSq g.1 ≠ 0 := fun hc => g.2.2 (D.F.bp_def g.1 hc)
  have hpos : 0 < D.F.normSq g.1 := lt_of_le_of_ne hnn (Ne.symm hne)
  exact (le_div_iff₀ hpos).mpr (hK g.1 (hwin g.1 g.2.1))

end Work.BoseBoxFock
