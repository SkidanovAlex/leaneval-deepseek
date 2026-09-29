import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMC13.Basic
import Submission.Work.TMC13.prufer_lift

/-!
# The fictitious Lipschitz estimate (C13, main computation)

Given the reducibility data at frequency `α` on a spectral interval
(`C (y + α) * tmR lam E y = rot (φ y) * C y`), and a continuous family of *projective lifts*
`h` of `C` (with uniformly bounded displacement and uniformly Lipschitz in the parameter),
the Prüfer rotation number at frequency `α'` is within `L |α' - α|` of `2 ∫ φ` plus an
integer.
-/

noncomputable section

namespace Work.TMC13

open Matrix Filter MeasureTheory
open scoped Topology

/-- The Prüfer step function is a projective lift of the transfer matrix `tmR`. -/
theorem isProjLift_tmR (lam E y : ℝ) :
    IsProjLift (Work.TMContract.tmR lam E y)
      (Work.TMContract.pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * y))) := by
  obtain ⟨hcont, hshift, _hmono, hdir⟩ :=
    prufer_lift (E - 2 * lam * Real.cos (2 * Real.pi * y))
  refine ⟨?_, hshift, fun t => ?_⟩
  · exact hcont.comp (continuous_const.prodMk continuous_id)
  · obtain ⟨c, hc, hc'⟩ := hdir t
    exact ⟨c, hc, by simpa [dvec, Work.TMContract.tmR] using hc'⟩

/-- The "half-turn" angle of the transfer matrix: `a y = E - 2 λ cos (2 π y)`. -/
def amoA (lam E y : ℝ) : ℝ := E - 2 * lam * Real.cos (2 * Real.pi * y)

lemma continuous_amoA (lam E : ℝ) : Continuous (amoA lam E) := by
  unfold amoA; fun_prop

/-- **Lift identity.**  For each `y`, the Prüfer lift of `tmR lam E y` conjugated by the
lifts `h` of `C` differs from the translation by `2 φ y` by an integer. -/
theorem prufer_conj_exists_int {α lam E : ℝ} {C : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {φ : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hC : ∀ y, IsProjLift (C y) (h y))
    (hprufer : ∀ y, IsProjLift (Work.TMContract.tmR lam E y) (Work.TMContract.pruferStep (amoA lam E y)))
    (hconj : ∀ y, C (y + α) * Work.TMContract.tmR lam E y = Work.TMContract.rot (φ y) * C y) :
    ∀ y, ∃ k : ℤ, ∀ t,
      h (y + α) (Work.TMContract.pruferStep (amoA lam E y) t) = h y t + 2 * φ y + k := by
  intro y
  have h1 : IsProjLift (C (y + α) * Work.TMContract.tmR lam E y)
      (h (y + α) ∘ Work.TMContract.pruferStep (amoA lam E y)) :=
    (hC (y + α)).comp (hprufer y)
  have h2 : IsProjLift (Work.TMContract.rot (φ y) * C y)
      ((fun t => t + 2 * φ y) ∘ h y) :=
    (isProjLift_rot (φ y)).comp (hC y)
  rw [hconj y] at h1
  obtain ⟨k, hk⟩ := h1.eq_add_int h2
  exact ⟨k, fun t => hk t⟩

/-- The integer above is independent of `y`, by continuity. -/
theorem prufer_conj_int {α lam E : ℝ}
    {φ : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hcont : Continuous (fun p : ℝ × ℝ => h p.1 p.2)) (hφc : Continuous φ)
    (hpruferc : Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2))
    (hper : ∀ y, ∃ k : ℤ, ∀ t,
      h (y + α) (Work.TMContract.pruferStep (amoA lam E y) t) = h y t + 2 * φ y + k) :
    ∃ k : ℤ, ∀ y t,
      h (y + α) (Work.TMContract.pruferStep (amoA lam E y) t) = h y t + 2 * φ y + k := by
  have hint : ∀ y : ℝ, ∃ k : ℤ,
      h (y + α) (Work.TMContract.pruferStep (amoA lam E y) 0) - h y 0 - 2 * φ y = k := by
    intro y
    obtain ⟨k, hk⟩ := hper y
    exact ⟨k, by rw [hk 0]; ring⟩
  have hgc : Continuous (fun y : ℝ =>
      h (y + α) (Work.TMContract.pruferStep (amoA lam E y) 0) - h y 0 - 2 * φ y) := by
    have h1 : Continuous (fun y : ℝ => h (y + α) (Work.TMContract.pruferStep (amoA lam E y) 0)) :=
      hcont.comp ((continuous_id.add continuous_const).prodMk
        (hpruferc.comp ((continuous_amoA lam E).prodMk continuous_const)))
    have h2 : Continuous (fun y : ℝ => h y 0) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    have h3 : Continuous (fun y : ℝ => 2 * φ y) := continuous_const.mul hφc
    exact (h1.sub h2).sub h3
  obtain ⟨k, hk⟩ := exists_int_eq_const hgc hint
  refine ⟨k, fun y t => ?_⟩
  obtain ⟨k', hk'⟩ := hper y
  have h0 : h (y + α) (Work.TMContract.pruferStep (amoA lam E y) 0) - h y 0 - 2 * φ y = k := hk y
  have h0' : h (y + α) (Work.TMContract.pruferStep (amoA lam E y) 0) - h y 0 - 2 * φ y
      = (k' : ℝ) := by rw [hk' 0]; ring
  rw [h0'] at h0
  have hkk : k' = k := by exact_mod_cast h0.symm.symm
  rw [hk' t, hkk]

/-- **Main propagation estimate.**  For `|α' - α| ≤ 1`, the Prüfer iterates at frequency `α'`
stay within `n L |α' - α| + M` of the "conjugated rotation" model
`h x 0 + 2 Σ_{j<n} φ (x + j α') + n k`. -/
theorem pruferIter_model_bound {α lam E α' : ℝ}
    {φ : ℝ → ℝ} {h : ℝ → ℝ → ℝ} {k : ℤ} {M L : ℝ}
    (hid : ∀ y t, h (y + α) (Work.TMContract.pruferStep (amoA lam E y) t) = h y t + 2 * φ y + k)
    (hM : ∀ y t, |h y t - t| ≤ M)
    (hL : ∀ y s β, |β| ≤ 1 → |h y s - h (y + β) s| ≤ L * |β|)
    (hε : |α' - α| ≤ 1) (x : ℝ) (n : ℕ) :
    |Work.TMContract.pruferIter α' lam E n x 0 -
        (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * k)| ≤
      (n : ℝ) * L * |α' - α| + M := by
  have key : ∀ n : ℕ,
      |h (x + (n : ℝ) * α') (Work.TMContract.pruferIter α' lam E n x 0) -
        (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * k)| ≤
        (n : ℝ) * L * |α' - α| := by
    intro n
    induction n with
    | zero => simpa [Work.TMContract.pruferIter] using continuous_const
    | succ m ih =>
      have hsum : (∑ j ∈ Finset.range (m + 1), φ (x + (j : ℝ) * α'))
          = (∑ j ∈ Finset.range m, φ (x + (j : ℝ) * α')) + φ (x + (m : ℝ) * α') :=
        Finset.sum_range_succ _ _
      have hs : Work.TMContract.pruferIter α' lam E (m + 1) x 0
          = Work.TMContract.pruferStep (amoA lam E (x + (m : ℝ) * α'))
              (Work.TMContract.pruferIter α' lam E m x 0) := rfl
      have hI : h (x + (m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0) =
          h (x + (m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0)
            + 2 * φ (x + (m : ℝ) * α') + k := by
        rw [hs]
        exact hid (x + (m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0)
      have hcoord : x + (m : ℝ) * α' + α + (α' - α) = x + (m : ℝ) * α' + α' := by ring
      have hL2 : |h (x + (m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
          h (x + (m : ℝ) * α' + α') (Work.TMContract.pruferIter α' lam E (m + 1) x 0)|
          ≤ L * |α' - α| := by
        have h := hL (x + (m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0)
          (α' - α) hε
        rwa [hcoord] at h
      push_cast
      rw [hsum]
      have hcastk : ((↑m : ℝ) + 1) * (↑k : ℝ) = (↑m : ℝ) * ↑k + ↑k := by ring
      rw [hcastk]
      have hdecomp : h (x + (↑m + 1) * α') (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
            (h x 0 + 2 * ((∑ j ∈ Finset.range m, φ (x + (j : ℝ) * α')) + φ (x + (↑m : ℝ) * α'))
              + ((↑m : ℝ) * ↑k + ↑k))
          = (h (x + (↑m + 1) * α') (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
              h (x + (↑m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0)) +
            (h (x + (↑m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
              (h (x + (↑m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0)
                + 2 * φ (x + (↑m : ℝ) * α') + ↑k)) +
            (h (x + (↑m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0) -
              (h x 0 + 2 * (∑ j ∈ Finset.range m, φ (x + (j : ℝ) * α')) + (↑m : ℝ) * ↑k)) := by
        ring
      rw [hdecomp]
      have hzero : |h (x + (↑m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
              (h (x + (↑m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0)
                + 2 * φ (x + (↑m : ℝ) * α') + ↑k)| = 0 := by
        rw [hI]; simp
      have hcoord2 : x + (↑m + 1) * α' = x + (↑m : ℝ) * α' + α' := by ring
      calc |(h (x + (↑m + 1) * α') (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
              h (x + (↑m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0)) +
            (h (x + (↑m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
              (h (x + (↑m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0)
                + 2 * φ (x + (↑m : ℝ) * α') + ↑k)) +
            (h (x + (↑m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0) -
              (h x 0 + 2 * (∑ j ∈ Finset.range m, φ (x + (j : ℝ) * α')) + (↑m : ℝ) * ↑k))|
          ≤ |h (x + (↑m + 1) * α') (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
              h (x + (↑m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0)| +
            |h (x + (↑m : ℝ) * α' + α) (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
              (h (x + (↑m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0)
                + 2 * φ (x + (↑m : ℝ) * α') + ↑k)| +
            |h (x + (↑m : ℝ) * α') (Work.TMContract.pruferIter α' lam E m x 0) -
              (h x 0 + 2 * (∑ j ∈ Finset.range m, φ (x + (j : ℝ) * α')) + (↑m : ℝ) * ↑k)|
            := abs_add_three _ _ _
        _ ≤ L * |α' - α| + 0 + (↑m : ℝ) * L * |α' - α| := by
              have hA1 : |h (x + (↑m + 1) * α') (Work.TMContract.pruferIter α' lam E (m + 1) x 0) -
                    h (x + (↑m : ℝ) * α' + α)
                      (Work.TMContract.pruferIter α' lam E (m + 1) x 0)| ≤ L * |α' - α| := by
                rw [hcoord2, abs_sub_comm]
                exact hL2
              exact add_le_add (add_le_add hA1 (le_of_eq hzero)) ih
        _ = ((↑m : ℝ) + 1) * L * |α' - α| := by ring
  have hMs : |Work.TMContract.pruferIter α' lam E n x 0 -
      h (x + (n : ℝ) * α') (Work.TMContract.pruferIter α' lam E n x 0)| ≤ M := by
    have h := hM (x + (n : ℝ) * α') (Work.TMContract.pruferIter α' lam E n x 0)
    rwa [abs_sub_comm]
  calc |Work.TMContract.pruferIter α' lam E n x 0 -
        (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * k)|
      ≤ |Work.TMContract.pruferIter α' lam E n x 0 -
          h (x + (n : ℝ) * α') (Work.TMContract.pruferIter α' lam E n x 0)| +
        |h (x + (n : ℝ) * α') (Work.TMContract.pruferIter α' lam E n x 0) -
          (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * k)| :=
        abs_sub_le _ _ _
    _ ≤ M + (n : ℝ) * L * |α' - α| := add_le_add hMs (key n)
    _ = (n : ℝ) * L * |α' - α| + M := by ring

/-- The Prüfer iterates are continuous in the initial point (for fixed `n`). -/
lemma continuous_pruferIter (hpruferc : Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2))
    (lam E : ℝ) (n : ℕ) (α : ℝ) :
    Continuous (fun x : ℝ => Work.TMContract.pruferIter α lam E n x 0) := by
  induction n with
  | zero => simpa [Work.TMContract.pruferIter] using continuous_const
  | succ m ih =>
    have hfun : (fun x : ℝ => Work.TMContract.pruferIter α lam E (m + 1) x 0)
        = fun x : ℝ => Work.TMContract.pruferStep (amoA lam E (x + (m : ℝ) * α))
            (Work.TMContract.pruferIter α lam E m x 0) := by
      funext x; rfl
    rw [hfun]
    exact hpruferc.comp (((continuous_amoA lam E).comp (continuous_id.add continuous_const)).prodMk ih)

/-- The integral of the model sum only depends on `∫ φ`. -/
lemma integral_shifted_sum {φ : ℝ → ℝ} (hφper : ∀ x, φ (x + 1) = φ x) (hφc : Continuous φ)
    (α' : ℝ) (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α'))
      = (n : ℝ) * ∫ x in (0 : ℝ)..1, φ x := by
  rw [intervalIntegral.integral_finsetSum]
  · have h1 : ∀ j : ℕ, ∫ x in (0 : ℝ)..1, φ (x + (j : ℝ) * α') = ∫ x in (0 : ℝ)..1, φ x := by
      intro j
      rw [intervalIntegral.integral_comp_add_right]
      have h2 : 0 + (j : ℝ) * α' = (j : ℝ) * α' := by ring
      have h3 : 1 + (j : ℝ) * α' = (j : ℝ) * α' + 1 := by ring
      rw [h2, h3]
      simpa using Function.Periodic.intervalIntegral_add_eq (fun x => hφper x) ((j : ℝ) * α') 0
    simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro j _
    exact (hφc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _

/-- **Fictitious Lipschitz estimate.**  Given the conjugacy data at frequency `α` and a
lift family `h` with uniformly bounded displacement and uniform Lipschitz constant `L`, the
Prüfer rotation number at frequency `α'` is within `L |α' - α|` of `2 ∫ φ + k`. -/
theorem rotLift_perturb {α lam E : ℝ}
    {φ : ℝ → ℝ} {h : ℝ → ℝ → ℝ} {k : ℤ} {M L : ℝ}
    (hpruferc : Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2))
    (hφper : ∀ x, φ (x + 1) = φ x) (hφc : Continuous φ)
    (hhc : Continuous (fun p : ℝ × ℝ => h p.1 p.2))
    (hid : ∀ y t, h (y + α) (Work.TMContract.pruferStep (amoA lam E y) t) = h y t + 2 * φ y + k)
    (hM : ∀ y t, |h y t - t| ≤ M)
    (hL : ∀ y s β, |β| ≤ 1 → |h y s - h (y + β) s| ≤ L * |β|)
    (hconv : ∀ α', Tendsto (fun n : ℕ =>
        (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0) / (n : ℝ)) atTop
        (𝓝 (Work.TMContract.rotLift α' lam E))) :
    ∀ α', |α' - α| ≤ 1 →
      |Work.TMContract.rotLift α' lam E - (2 * (∫ x in (0 : ℝ)..1, φ x) + k)| ≤ L * |α' - α| := by
  intro α' hε
  set P : ℝ := ∫ x in (0 : ℝ)..1, φ x with hP
  set Q : ℝ := ∫ x in (0 : ℝ)..1, h x 0 with hQ
  have hmain : ∀ n : ℕ, 0 < n →
      |(∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0) / (n : ℝ)
          - (2 * P + (k : ℝ))| ≤ L * |α' - α| + (M + |Q|) / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hIn : IntervalIntegrable (fun x : ℝ => Work.TMContract.pruferIter α' lam E n x 0)
        volume (0 : ℝ) 1 := (continuous_pruferIter hpruferc lam E n α').intervalIntegrable _ _
    have hsumc : Continuous (fun x : ℝ => ∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) :=
      continuous_finsetSum _ (fun j _ => hφc.comp (continuous_id.add continuous_const))
    have hmodelc : Continuous (fun x : ℝ =>
        h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * (k : ℝ)) := by
      have h1 : Continuous (fun x : ℝ => h x 0) :=
        hhc.comp (continuous_id.prodMk continuous_const)
      exact (h1.add (continuous_const.mul hsumc)).add continuous_const
    have hImodel : IntervalIntegrable (fun x : ℝ =>
        h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * (k : ℝ))
        volume (0 : ℝ) 1 := hmodelc.intervalIntegrable _ _
    -- pointwise bound integrated
    have hbnd : |∫ x in (0 : ℝ)..1, (Work.TMContract.pruferIter α' lam E n x 0 -
          (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * (k : ℝ)))| ≤
        (n : ℝ) * L * |α' - α| + M := by
      calc |∫ x in (0 : ℝ)..1, (Work.TMContract.pruferIter α' lam E n x 0 -
            (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * (k : ℝ)))|
          ≤ ∫ x in (0 : ℝ)..1, |Work.TMContract.pruferIter α' lam E n x 0 -
              (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * (k : ℝ))| :=
            intervalIntegral.abs_integral_le_integral_abs (by norm_num)
        _ ≤ ∫ x in (0 : ℝ)..1, ((n : ℝ) * L * |α' - α| + M) := by
            refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
            · exact (hIn.sub hImodel).abs
            · exact intervalIntegrable_const
            · intro x _
              exact pruferIter_model_bound hid hM hL hε x n
        _ = (n : ℝ) * L * |α' - α| + M := by
            rw [intervalIntegral.integral_const]
            norm_num
    have hIh : IntervalIntegrable (fun x : ℝ => h x 0) volume (0 : ℝ) 1 :=
      (hhc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    have hIsum : IntervalIntegrable
        (fun x : ℝ => ∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) volume (0 : ℝ) 1 :=
      hsumc.intervalIntegrable 0 1
    have hsub : ∫ x in (0 : ℝ)..1, (Work.TMContract.pruferIter α' lam E n x 0 -
          (h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * (k : ℝ)))
        = (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0)
          - (Q + 2 * (n : ℝ) * P + (n : ℝ) * (k : ℝ)) := by
      rw [intervalIntegral.integral_sub hIn hImodel]
      congr 1
      have s1 : (∫ x in (0 : ℝ)..1,
            h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')) + (n : ℝ) * (k : ℝ))
          = (∫ x in (0 : ℝ)..1, h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')))
            + (∫ x in (0 : ℝ)..1, (n : ℝ) * (k : ℝ)) :=
        intervalIntegral.integral_add (hIh.add (hIsum.const_mul 2)) intervalIntegrable_const
      have s2 : (∫ x in (0 : ℝ)..1, h x 0 + 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')))
          = (∫ x in (0 : ℝ)..1, h x 0)
            + (∫ x in (0 : ℝ)..1, 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α'))) :=
        intervalIntegral.integral_add hIh (hIsum.const_mul 2)
      have s3 : (∫ x in (0 : ℝ)..1, 2 * (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α')))
          = 2 * (∫ x in (0 : ℝ)..1, (∑ j ∈ Finset.range n, φ (x + (j : ℝ) * α'))) :=
        intervalIntegral.integral_const_mul 2 _
      rw [s1, s2, s3, integral_shifted_sum hφper hφc α' n, ← hQ, ← hP,
        intervalIntegral.integral_const]
      ring
    rw [hsub] at hbnd
    have hdiv : (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0) / (n : ℝ)
          - (2 * P + (k : ℝ))
        = ((∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0)
            - (Q + 2 * (n : ℝ) * P + (n : ℝ) * (k : ℝ))) / (n : ℝ) + Q / (n : ℝ) := by
      field_simp
      ring
    calc |(∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0) / (n : ℝ)
          - (2 * P + (k : ℝ))|
        = |((∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0)
            - (Q + 2 * (n : ℝ) * P + (n : ℝ) * (k : ℝ))) / (n : ℝ) + Q / (n : ℝ)| := by
          rw [hdiv]
      _ ≤ |((∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0)
            - (Q + 2 * (n : ℝ) * P + (n : ℝ) * (k : ℝ))) / (n : ℝ)| + |Q / (n : ℝ)| :=
          abs_add_le _ _
      _ = |(∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0)
            - (Q + 2 * (n : ℝ) * P + (n : ℝ) * (k : ℝ))| / (n : ℝ) + |Q| / (n : ℝ) := by
          rw [abs_div, abs_div, abs_of_pos hnpos]
      _ ≤ ((n : ℝ) * L * |α' - α| + M) / (n : ℝ) + |Q| / (n : ℝ) := by
          refine add_le_add ?_ le_rfl
          exact div_le_div_of_nonneg_right hbnd (le_of_lt hnpos)
      _ = L * |α' - α| + (M + |Q|) / (n : ℝ) := by
          field_simp
          ring
  -- pass to the limit
  have hlim : Tendsto (fun n : ℕ =>
      |(∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0) / (n : ℝ)
        - (2 * P + (k : ℝ))|) atTop
      (𝓝 |Work.TMContract.rotLift α' lam E - (2 * P + (k : ℝ))|) :=
    ((hconv α').sub tendsto_const_nhds).abs
  have hbound : Tendsto (fun n : ℕ => L * |α' - α| + (M + |Q|) / (n : ℝ)) atTop
      (𝓝 (L * |α' - α|)) := by
    have h0 : Tendsto (fun n : ℕ => (M + |Q|) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add h0
  have hev : ∀ᶠ n : ℕ in atTop,
      |(∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α' lam E n x 0) / (n : ℝ)
        - (2 * P + (k : ℝ))| ≤ L * |α' - α| + (M + |Q|) / (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact hmain n hn
  have := le_of_tendsto_of_tendsto hlim hbound hev
  simpa [hP, hQ] using this

end Work.TMC13
