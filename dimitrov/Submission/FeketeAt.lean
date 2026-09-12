import Mathlib

/-!
# Isolated task: Fekete-point attainment (compactness)

Self-contained definitions (mirror of Submission/Dubinin.lean).  Prove ONLY
the declarations below; leave nothing unproved.

STATEMENT (`exists_fekete_points`): for a nonempty compact `E : Set ℂ` and
`n : ℕ`, there is an `n`-point configuration `x : ℕ → ℂ` (all `x i ∈ E`,
`i < n`) whose Vandermonde product attains the Fekete number:

    vdm x n = feketeNumber E n

where `vdm x n := ∏ i ∈ range n, ∏ j ∈ range i, ‖x j - x i‖` and
`feketeNumber E n := sSup {d | ∃ x, (∀ i < n, x i ∈ E) ∧ d = vdm x n}`.

PROOF SKELETON (compactness + continuity):

1. Reduce to the finite product `Eⁿ`: the domain of configurations is
   `{x : Fin n → ℂ | ∀ i, x i ∈ E}` ≅ `Eⁿ` (embed via
   `x ↦ (x 0, …, x (n−1))`), a compact space (`isCompact_iff` on finite
   products; use `isCompact_pi` or induction on `n` with
   `IsCompact.prod`; or use `Set.pi` and `isCompact_pi`).
   In Lean it is simplest to phrase the proof with `Fin n` as the domain:
   restate the goal with `x : Fin n → ℂ`, prove it there, then convert
   (a helper lemma `feketeNumber_eq_sSup_fin` may help: the set of
   `vdm`-values over `ℕ`-configurations equals the set over `Fin n`
   configurations, both are the same values).
2. `vdm` is continuous on the configuration space: each factor
   `‖x j - x i‖` is continuous (norm of a linear map in the real and
   imaginary parts; `Continuous.norm` / `continuous_norm`, sub of two
   coordinates), finite products of continuous functions are continuous
   (`Finset.continuous_prod` or `Continuous.prod` iterated), and the map
   `x ↦ vdm x n` is a finite product of such factors.
3. `feketeSet E n` is the image of the compact configuration space under
   this continuous `vdm` map, hence is compact (continuous image of
   compact), so its `sSup` (= `feketeNumber E n`) is attained: the set is
   nonempty (constant configuration `x i := e₀` for `e₀ ∈ E`) and bounded
   above (compactness, or the explicit bound from boundedness of `E`), and
   `IsCompact` sets in `ℝ` are closed and bounded, so `sSup` is a member
   (`csSup_mem`-style: `IsCompact.exists_isMaxOn` or use
   `sSup_mem_of_isCompact` if available; else: compactness gives
   `∃ d ∈ feketeSet, ∀ e ∈ feketeSet, e ≤ d` via
   `IsCompact.exists_isGreatest`/`exists_isMaxOn` on the continuous
   identity, then `sSup = d` by `csSup_eq`).
4. Assemble: the maximizing `d = vdm x n` gives the desired configuration.

Suggested Mathlib lemmas to look for: `IsCompact.image`,
`IsCompact.exists_isMaxOn`, `isCompact_iff_isClosed_bounded`,
`Metric.isCompact_iff_closed_bounded`, `Continuous.prod`,
`Finset.continuous_prod` (or prove by induction),
`Continuous.norm`, `continuous_pow`/`continuous_id`,
`csSup_eq` / `IsGreatest.sSup_eq` / `sSup_mem`.
Do NOT change the statement below; add helper lemmas freely (e.g. a
`Fin n`-based version of `feketeNumber`, a `vdm`-continuity lemma, and an
`IsCompact` version of the configuration space).  Note `n = 0` and `n = 1`
are trivial (empty/one-term products).
-/

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.FeketeAt

/-- The Vandermonde product of `n` points (pairs `j < i < n`). -/
def vdm (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖

/-- The set of Vandermonde products over `n`-point configurations in `E`. -/
def feketeSet (E : Set ℂ) (n : ℕ) : Set ℝ :=
  {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ E) ∧ d = vdm x n}

/-- **Fekete number.** -/
def feketeNumber (E : Set ℂ) (n : ℕ) : ℝ := sSup (feketeSet E n)

/-- The zero-extension of a `Fin n`-configuration to a sequence `ℕ → ℂ`. -/
def zeroExt (n : ℕ) (y : Fin n → ℂ) : ℕ → ℂ := fun i => if h : i < n then y ⟨i, h⟩ else 0

/-- `vdm` only depends on the first `n` coordinates of a configuration. -/
lemma vdm_congr {n : ℕ} {x x' : ℕ → ℂ} (h : ∀ j : ℕ, j < n → x j = x' j) :
    vdm x n = vdm x' n := by
  unfold vdm
  apply Finset.prod_congr rfl
  intro i hi
  have hi_lt : i < n := Finset.mem_range.mp hi
  apply Finset.prod_congr rfl
  intro j hj
  have hj_lt : j < i := Finset.mem_range.mp hj
  have hx_j : x j = x' j := h j (lt_trans hj_lt hi_lt)
  have hx_i : x i = x' i := h i hi_lt
  rw [hx_j, hx_i]

/-- `vdm (·, n)` is continuous on the product of the coordinate spaces. -/
lemma continuous_vdm (n : ℕ) : Continuous (fun x : ℕ → ℂ => vdm x n) := by
  unfold vdm
  fun_prop

/-- Zero-extension is continuous (coordinate-wise a projection or a constant). -/
lemma continuous_zeroExt (n : ℕ) : Continuous (zeroExt n) := by
  apply continuous_pi
  intro i
  by_cases h : i < n
  · have hc : Continuous (fun y : Fin n → ℂ => y (⟨i, h⟩ : Fin n)) := continuous_apply (⟨i, h⟩ : Fin n)
    simpa [zeroExt, h] using hc
  · have hc : Continuous (fun y : Fin n → ℂ => (0 : ℂ)) := continuous_const
    simpa [zeroExt, h] using hc

/-- **Fekete-point attainment.**  On a nonempty compact `E`, an
`n`-configuration attaining the Fekete number exists. -/
lemma exists_fekete_points {E : Set ℂ} (hE : IsCompact E) (hne : E.Nonempty)
    (n : ℕ) :
    ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ E) ∧ vdm x n = feketeNumber E n := by
  -- Configurations over `Fin n` with coordinates in `E` (compact by Tychonoff).
  let A : Set (Fin n → ℂ) := {y | ∀ i : Fin n, y i ∈ E}
  -- Vandermonde of the zero-extension.
  let F : (Fin n → ℂ) → ℝ := fun y => vdm (zeroExt n y) n
  have hAcomp : IsCompact A := by
    dsimp [A]
    exact isCompact_pi_infinite (s := fun _ : Fin n => E) (fun _ => hE)
  have hAne : A.Nonempty := by
    rcases hne with ⟨e, he⟩
    refine ⟨fun _ : Fin n => e, ?_⟩
    intro i
    exact he
  have hFcont : ContinuousOn F A := by
    have hF : Continuous F := by
      dsimp [F]
      exact (continuous_vdm n).comp (continuous_zeroExt n)
    exact hF.continuousOn
  -- The value set of `F` on `A` is exactly `feketeSet E n`.
  have hset : F '' A = feketeSet E n := by
    ext d
    constructor
    · rintro ⟨y, hyA, rfl⟩
      refine ⟨zeroExt n y, ?_, rfl⟩
      intro i hi
      simpa [zeroExt, hi] using (hyA ⟨i, hi⟩ : y (⟨i, hi⟩ : Fin n) ∈ E)
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun i : Fin n => x i.val, ?_, ?_⟩
      · intro i
        exact hx i.val i.isLt
      · apply vdm_congr
        intro j hj
        dsimp [zeroExt]
        simp [hj]
  -- `F '' A` is compact and nonempty, so its supremum is attained at some `y₀`.
  obtain ⟨y₀, hy₀A, hs⟩ := hAcomp.exists_sSup_image_eq hAne hFcont
  -- hs : sSup (F '' A) = F y₀
  let x₀ : ℕ → ℂ := zeroExt n y₀
  refine ⟨x₀, ?_, ?_⟩
  · intro i hi
    show zeroExt n y₀ i ∈ E
    simpa [zeroExt, hi] using (hy₀A ⟨i, hi⟩ : y₀ (⟨i, hi⟩ : Fin n) ∈ E)
  · show vdm (zeroExt n y₀) n = feketeNumber E n
    have hnum : feketeNumber E n = F y₀ := by
      dsimp [feketeNumber]
      rw [← hset]
      exact hs
    dsimp [F] at hnum
    exact hnum.symm

end Submission.FeketeAt

end
