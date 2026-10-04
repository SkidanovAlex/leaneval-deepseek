/-
# The flat torus Cauchy problem: assembly (design Layer D, flat case)

This file assembles the flat analytic core `Work.Diff.STE.Flat.TorusShortTimeExistence n` from the
pieces proved in the sibling modules of this directory:

* `flat/uniform_ellipticity_of_posDef` — the uniform ellipticity constant `lam` of the initial
  datum (used to fix the constants);
* `flat/posDef_of_uniform_close` — positivity is open (used to make the truncated initial data
  positive definite as well);
* `flat/fourier_projBox_uniform_tendsto` — the partial Fourier sums converge uniformly to a smooth
  periodic function (used for the initial data of the Galerkin solutions);
* `flat/ENormSq_projBox_fourierCoeff_le` — the truncated datum has no larger energy than the datum;

and the four analytic pieces:

* `flat/energy_apriori` (`energy_apriori`) and `flat/ellipticity_persist`
  (`ellipticity_persist`) — the two a priori estimates, which are the hypotheses `hCauchy`/`hEll`
  of `flat/galerkin_bootstrap`;
* `flat/level_step` (`level_step`) glued with `flat/energy_differentiable`
  (`energy_differentiable`) into `level_step_diff`, which is the hypothesis `hstep` of
  `flat/all_levels`;
* `flat/galerkin_bootstrap` (`galerkin_bootstrap`) — existence of the Galerkin solution on the
  *fixed* interval `[0, τ)` with the uniform bounds, by the bootstrap (this is where the local
  Picard–Lindelöf existence `flat/galerkin_ode_existence` is used);
* `flat/limit_solves` (`limit_solves`) — the limit of the Galerkin solutions solves the equation.

The planar situation (`n = 0`) is degenerate and handled separately: the torus is a point and
`MatC 0` is a subsingleton, so the constant datum solves the equation.

The final step is the *reality* of the solution: the initial datum is real, the nonlinearity is
conjugation-equivariant (`solvesOn_conj`), and the conjugate of a solution is a solution with the
same initial datum, so the two agree by `flat/torus_uniqueness`.

Symmetry of the solution (needed in the geometric layer) is *not* part of
`TorusShortTimeExistence`: for a general DeTurck-shaped `Φ` it is false.  In the geometric
application it is obtained outside this file from `flat/SolvesOn_symm_of_jet` together with the
jet-level symmetry `Work.Diff.STE.DeTurck.pPhi_symm` of the DeTurck operator.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.galerkin_ode_existence
import Submission.Work.Diff.STE.flat.galerkin_bootstrap
import Submission.Work.Diff.STE.flat.galerkin_symm_of_initial
import Submission.Work.Diff.STE.flat.all_levels
import Submission.Work.Diff.STE.flat.energy_apriori
import Submission.Work.Diff.STE.fill.energy_apriori
import Submission.Work.Diff.STE.flat.energy_differentiable
import Submission.Work.Diff.STE.flat.ellipticity_persist
import Submission.Work.Diff.STE.flat.level_step
import Submission.Work.Diff.STE.flat.limit_solves
import Submission.Work.Diff.STE.flat.torus_uniqueness
import Submission.Work.Diff.STE.flat.uniform_ellipticity_of_posDef
import Submission.Work.Diff.STE.flat.fourier_projBox_uniform_tendsto
import Submission.Work.Diff.STE.flat.ENormSq_projBox_fourierCoeff_le
import Submission.Work.Diff.STE.flat.posDef_of_uniform_close
import Submission.Work.Diff.STE.flat.solvesOn_conj
import Submission.Work.Diff.STE.flat.SolvesOn_quadForm_persist
import Submission.Work.Diff.STE.flat.SolvesOn_symm_of_jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Topology

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

/-- **The level step, glued with the differentiability of the energy.**  This is exactly the
hypothesis `hstep` of `all_levels`: `level_step` supplies the differential inequality and
`energy_differentiable` the differentiability of the energy function. -/
theorem level_step_diff {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (s : ℕ) (hs : Fintype.card (Fin n) + 5 ≤ s)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ)
        (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ Bs ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc,
          DifferentiableAt ℝ
            (fun σ => Work.Diff.STE.Flat.ENormSqFull (s + 1)
              (Work.Diff.STE.Flat.seriesFunM (c σ))) t ∧
          deriv (fun σ => Work.Diff.STE.Flat.ENormSqFull (s + 1)
              (Work.Diff.STE.Flat.seriesFunM (c σ))) t
            ≤ C * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
                (Work.Diff.STE.Flat.seriesFunM (c t))) := by
  obtain ⟨C, hC, hstep⟩ := level_step hn Φ hshape s hs lam hlam Bs hBs
  refine ⟨C, hC, fun Tc hc N c hode hsupp hell hlev t ht => ⟨?_, hstep Tc hc N c hode hsupp hell hlev t ht⟩⟩
  exact energy_differentiable hn Φ hshape (s + 1) lam hlam Tc N c hode hsupp hell t ht

/-! ## The torus Cauchy problem, in the form used by the geometric layer -/

/-- **The torus theorem, with the jet symmetry hypothesis and the symmetry conclusion.**

The extra hypothesis `hsym` says that the nonlinearity maps *symmetric* jets (a symmetric value
`A`, a first jet `L` symmetric in the metric indices, a second jet `B` symmetric in the metric
indices and symmetric in its two derivative slots) to symmetric values.  This holds for the chart
expression `pPhi` of the DeTurck operator (`Work.Diff.STE.DeTurck.pPhi_symm`), which is the only
instance the geometric layer uses; it does *not* hold for a general DeTurck-shaped nonlinearity
(`secOpFlat A B + ε` with a constant antisymmetric `ε`), which is why the conclusion of the general
`TorusShortTimeExistence` cannot contain symmetry. -/
def TorusShortTimeExistenceSymm (n : ℕ) : Prop :=
  ∀ (Φ : (Fin n → ℝ) × Jet n → MatC n), IsDeTurckNonlin Φ → ConjEquivNonlin Φ →
    (∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n) (B : Fin n → Fin n → MatC n),
      (∀ i j, A i j = A j i) → (∀ c i j, L c i j = L c j i) →
      (∀ c d i j, B c d i j = B c d j i) → (∀ c d, B c d = B d c) →
      ∀ i j, Φ (x, (A, L, B)) i j = Φ (x, (A, L, B)) j i) →
    ∀ u₀ : Torus n, ContDiff ℝ (⊤ : ℕ∞) u₀ → Periodic1 u₀ →
      (∀ x i j, (u₀ x i j).im = 0) → (∀ x, PosDefM (u₀ x)) →
      ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → Torus n, SolvesOn Φ T u ∧ u 0 = u₀ ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (u t x)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x i j, (u t x i j).im = 0) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x i j, u t x i j = u t x j i)

theorem torus_cauchy_symm (n : ℕ) : TorusShortTimeExistenceSymm n := by
  intro Φ hshape hconj hsymΦ u₀ hu₀ hper₀ him hpd
  by_cases hn0 : n = 0
  · -- ## the degenerate case: `Fin 0` is a point and `MatC 0` is a subsingleton
    subst hn0
    haveI : Subsingleton (MatC 0) := ⟨fun a b => by funext i; exact i.elim0⟩
    haveI : Subsingleton (Fin 0 → ℝ) := ⟨fun _ _ => funext (fun i => i.elim0)⟩
    refine ⟨1, one_pos, fun _ => u₀, ⟨?_, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
    · -- joint smoothness: the datum is constant, the torus being a point
      have hconst : (fun p : ℝ × (Fin 0 → ℝ) => u₀ p.2) = fun _ => u₀ (fun i => i.elim0) := by
        funext p
        exact congrArg u₀ (Subsingleton.elim _ _)
      rw [hconst]
      exact contDiffOn_const
    · intro t ht
      exact fun i => i.elim0
    · intro t ht x
      have h0 : Φ (x, jetM ((fun _ : ℝ => u₀) t) x) = 0 := Subsingleton.elim _ _
      rw [h0]
      exact hasDerivWithinAt_const (c := u₀ x) (s := Set.Ico (0 : ℝ) 1) (x := t)
    · intro t ht x; exact hpd x
    · intro t ht x i j; exact him x i j
    · intro t ht x i j; exact i.elim0
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    -- ## the constants
    obtain ⟨lam, hlam, hell₀⟩ := uniform_ellipticity_of_posDef u₀ hu₀.continuous hper₀ hpd
    obtain ⟨ε, hε, hclose⟩ := posDef_of_uniform_close u₀ lam hlam hell₀
    obtain ⟨N₀, hN₀⟩ := fourier_projBox_uniform_tendsto u₀ hu₀ hper₀ ε hε
    set k : ℕ := n + 5 with hkdef
    have hk : Fintype.card (Fin n) + 4 < 2 * k := by
      rw [Fintype.card_fin, hkdef]; omega
    have hsk : Fintype.card (Fin n) + 5 ≤ k := by rw [Fintype.card_fin, hkdef]
    -- ## the energy scale of the initial datum
    set E₀ : ℝ := |ENormSqFull k u₀| + 1 with hE₀def
    have hE₀1 : 1 ≤ E₀ := by
      rw [hE₀def]; have := abs_nonneg (ENormSqFull k u₀); linarith
    have hE₀abs : ENormSqFull k u₀ ≤ E₀ := by
      rw [hE₀def]
      exact le_add_of_le_of_nonneg (le_abs_self _) zero_le_one
    set B : ℝ := Real.sqrt (4 * E₀) with hBdef
    have hBpos : 0 < B := Real.sqrt_pos.mpr (by rw [hBdef] at *; linarith)
    have hBsq : B ^ 2 = 4 * E₀ := Real.sq_sqrt (by linarith)
    -- ## symmetry of the initial datum (it is positive definite and real)
    have hsym0 : ∀ (x : Fin n → ℝ) (i j : Fin n), u₀ x i j = u₀ x j i := by
      intro x i j
      haveI : Fact ((reMat (u₀ x)).IsHermitian) := ⟨(hpd x).1⟩
      have hre : (u₀ x i j).re = (u₀ x j i).re := by
        have h := Matrix.IsHermitian.apply (hpd x).1 j i
        simpa [reMat, Matrix.conjTranspose_apply, star_trivial] using h
      exact Complex.ext hre (by rw [him x i j, him x j i])
    have hcoeff_symm : ∀ (k' : Fin n → ℤ) (i j : Fin n),
        fourierCoeffM u₀ k' i j = fourierCoeffM u₀ k' j i := by
      intro k' i j
      simp only [fourierCoeffM_apply]
      congr 1
      funext x
      exact hsym0 x i j
    -- ## the two a priori constants
    -- (the a priori estimate is taken from `fill/energy_apriori`, the sorry-free version obtained
    -- from the sharp static pairing bound `fill/pairingBoundSharp`; the twin in
    -- `flat/energy_apriori` still carries its `sorry`)
    obtain ⟨C, hC, hCauchy⟩ :=
      Work.Diff.STE.fill.energy_apriori hn1 Φ hshape k hk (lam / 2 / 2) (by linarith) B hBpos.le
    obtain ⟨M, hM, hEll⟩ := ellipticity_persist hn1 Φ hshape k hk (lam / 2) (by linarith) B hBpos.le
    -- ## the time
    set r : ℝ := (4 * E₀ + 1) / (2 * E₀ + 1) with hrdef
    have hrpos : 0 < r := by rw [hrdef]; positivity
    have hr1 : 1 < r := by
      rw [hrdef, one_lt_div (by linarith)]; linarith
    have hlogr : 0 < Real.log r := Real.log_pos hr1
    set τ : ℝ := min (min (Real.log r / (2 * (C + 1))) (lam / (8 * (M + 1)))) 1 with hτdef
    have hτpos : 0 < τ := by
      rw [hτdef]
      exact lt_min (lt_min (div_pos hlogr (by linarith)) (div_pos hlam (by linarith))) one_pos
    have hτC : (B ^ 2 / 2 + 1) * Real.exp (C * τ) - 1 < B ^ 2 := by
      have hτ1 : τ ≤ Real.log r / (2 * (C + 1)) := le_trans (min_le_left _ _) (min_le_left _ _)
      have h2 : C * (Real.log r / (2 * (C + 1))) ≤ Real.log r / 2 := by
        rw [show C * (Real.log r / (2 * (C + 1))) = C * Real.log r / (2 * (C + 1)) from by ring,
          div_le_iff₀ (show (0:ℝ) < 2 * (C + 1) by linarith)]
        nlinarith [hlogr, hC]
      have hCτ : C * τ < Real.log r := by
        calc C * τ ≤ C * (Real.log r / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hτ1 hC
          _ ≤ Real.log r / 2 := h2
          _ < Real.log r := by linarith
      have hexp : Real.exp (C * τ) < r := by
        rw [← Real.exp_log hrpos]
        exact Real.exp_lt_exp.mpr hCτ
      have hrval : (2 * E₀ + 1) * r = 4 * E₀ + 1 := by
        rw [hrdef]
        field_simp
      have hmul := mul_lt_mul_of_pos_left hexp (show (0:ℝ) < 2 * E₀ + 1 by linarith)
      nlinarith [hmul, hrval, hBsq]
    have hτM : M * τ < lam / 2 / 2 := by
      have hτ1 : τ ≤ lam / (8 * (M + 1)) := le_trans (min_le_left _ _) (min_le_right _ _)
      have h2 : M * (lam / (8 * (M + 1))) ≤ lam / 8 := by
        rw [show M * (lam / (8 * (M + 1))) = M * lam / (8 * (M + 1)) from by ring,
          div_le_iff₀ (show (0:ℝ) < 8 * (M + 1) by linarith)]
        nlinarith [hlam, hM]
      have hmul := mul_le_mul_of_nonneg_left hτ1 hM
      nlinarith [h2, hmul, hlam]
    -- ## the Galerkin solutions on the fixed interval `[0, τ)`
    have hbootN : ∀ N : ℕ, N₀ ≤ N → ∃ c : ℝ → (Fin n → ℤ) → MatC n,
        c 0 = projBox N (fourierCoeffM u₀) ∧
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → c t k' = 0) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k' ∈ box n N, ∀ (i j : Fin n),
          HasDerivAt (fun s => c s k' i j)
            (fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x) i j) k') t) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) τ, ENormSqFull k (seriesFunM (c t)) ≤ B ^ 2) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          (lam / 2 / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            reMat (seriesFunM (c t) x) i j * v i * v j) := by
      intro N hN
      refine galerkin_bootstrap hn1 Φ hshape.1 k hk (lam / 2) (by linarith) B hBpos C M hC hM
        hCauchy hEll τ hτpos hτC hτM N (projBox N (fourierCoeffM u₀)) ?_ ?_ ?_
      · intro k' hk'
        exact projBox_apply_of_not_mem N _ hk'
      · intro x v
        exact hclose _ (hN₀ N hN) x v
      · have h1 : ENormSqFull k
            (seriesFunM (projBox N (fourierCoeffM u₀))) ≤ ENormSqFull k u₀ :=
          ENormSq_projBox_fourierCoeff_le u₀ hu₀ hper₀ k N
        rw [hBsq]
        linarith
    have hboot : ∀ N : ℕ, ∃ c : ℝ → (Fin n → ℤ) → MatC n,
        (N₀ ≤ N) → c 0 = projBox N (fourierCoeffM u₀) ∧
          (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → c t k' = 0) ∧
          (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k' ∈ box n N, ∀ (i j : Fin n),
            HasDerivAt (fun s => c s k' i j)
              (fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x) i j) k') t) ∧
          (∀ t ∈ Set.Ico (0 : ℝ) τ, ENormSqFull k (seriesFunM (c t)) ≤ B ^ 2) ∧
          (∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
            (lam / 2 / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
              reMat (seriesFunM (c t) x) i j * v i * v j) := by
      intro N
      by_cases hN : N₀ ≤ N
      · obtain ⟨c, h1, h2, h3, h4, h5⟩ := hbootN N hN
        exact ⟨c, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
      · exact ⟨fun _ _ => 0, fun h => absurd h hN⟩
    choose cN hcN using hboot
    -- ## the uniform initial data bound
    set E0 : ℕ → ℝ := fun j => |ENormSqFull j u₀| + 1 with hE0def
    have hE0nn : ∀ j, 0 ≤ E0 j := by intro j; rw [hE0def]; positivity
    have hE0init : ∀ (m j : ℕ), ENormSqFull j (seriesFunM (cN (N₀ + m) 0)) ≤ E0 j := by
      intro m j
      have hN : N₀ ≤ N₀ + m := by omega
      rw [(hcN (N₀ + m) hN).1, hE0def]
      have h1 := ENormSq_projBox_fourierCoeff_le u₀ hu₀ hper₀ j (N₀ + m)
      linarith [le_abs_self (ENormSqFull j u₀)]
    -- ## uniform bounds at every level
    obtain ⟨Blim, hBlimnn, hBlim⟩ :=
      all_levels hn1 Φ k hsk (lam / 2 / 2) (by linarith)
        (fun s hs Bs hBs => level_step_diff hn1 Φ hshape s (le_trans hsk hs) (lam / 2 / 2)
          (by linarith) Bs hBs)
        B hBpos.le τ hτpos
    have hbdd : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ j : ℕ,
        ENormSqFull j (seriesFunM (cN (N₀ + m) t)) ≤ Blim E0 j := by
      intro m t ht j
      have hN : N₀ ≤ N₀ + m := by omega
      exact hBlim (N₀ + m) (cN (N₀ + m)) (hcN (N₀ + m) hN).2.2.1 (hcN (N₀ + m) hN).2.1
        (hcN (N₀ + m) hN).2.2.2.2 (hcN (N₀ + m) hN).2.2.2.1 E0 hE0nn (hE0init m) t ht j
    -- ## the limit
    have hNb : Filter.Tendsto (fun m : ℕ => N₀ + m) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
    have hsymc : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ → ∀ (x : Fin n → ℝ) (i j : Fin n),
        reMat (seriesFunM (cN (N₀ + m) t) x) i j
          = reMat (seriesFunM (cN (N₀ + m) t) x) j i := by
      intro m t ht x i j
      have hN : N₀ ≤ N₀ + m := by omega
      have h := galerkin_symm_of_initial hn1 Φ hshape hsymΦ (N₀ + m)
        (projBox (N₀ + m) (fourierCoeffM u₀))
        (fun k' hk' => projBox_apply_of_not_mem (N₀ + m) _ hk')
        (fun k' i j => by
          by_cases hk : k' ∈ box n (N₀ + m)
          · simpa only [projBox_apply_of_mem (N₀ + m) _ hk] using hcoeff_symm k' i j
          · simp [projBox_apply_of_not_mem (N₀ + m) _ hk])
          τ hτpos (lam / 2 / 2) (by linarith) (cN (N₀ + m))
        (hcN (N₀ + m) hN).1 (hcN (N₀ + m) hN).2.2.1 (hcN (N₀ + m) hN).2.1
        ?_ t ht x i j
      · exact congrArg Complex.re h
      · -- the ellipticity at the level `lam/2` needed by the symmetry lemma
        intro t' ht' x' v
        have h := (hcN (N₀ + m) hN).2.2.2.2 t' ht' x' v
        linarith
    have hinit : ∀ x : Fin n → ℝ,
        Filter.Tendsto (fun m => seriesFunM (cN (N₀ + m) 0) x) Filter.atTop (nhds (u₀ x)) := by
      intro x
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨M', hM'⟩ := fourier_projBox_uniform_tendsto u₀ hu₀ hper₀ (δ / 2) (by linarith)
      refine ⟨M', fun m hm => ?_⟩
      have hN : N₀ ≤ N₀ + m := by omega
      rw [(hcN (N₀ + m) hN).1, dist_eq_norm]
      linarith [hM' (N₀ + m) (by omega) x]
    obtain ⟨u, huSolves, hu0, hupos⟩ :=
      limit_solves hn1 Φ hshape k hk τ hτpos (lam / 2 / 2) (by linarith) (Blim E0)
        (hBlimnn E0 hE0nn) u₀ hu₀ hper₀
        (fun m => N₀ + m) hNb (fun m => cN (N₀ + m))
        (fun m t ht k' hk' i j => (hcN (N₀ + m) (by omega)).2.2.1 t ht k' hk' i j)
        (fun m t ht x v => (hcN (N₀ + m) (by omega)).2.2.2.2 t ht x v)
        hsymc (fun m t k' hk' => (hcN (N₀ + m) (by omega)).2.1 t k' hk')
        hbdd hinit
    have hu0eq : u 0 = u₀ := funext hu0
    -- ## a uniform ellipticity bound on a small interval, from continuity
    have hell0u : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        (lam / 2 / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          reMat (u 0 x) i j * v i * v j := by
      intro x v
      rw [hu0eq]
      have h := hell₀ x v
      have hnn : (0:ℝ) ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hstep : (lam / 2 / 2) * (∑ i, (v i) ^ 2) ≤ lam * (∑ i, (v i) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hnn
      linarith
    obtain ⟨τ', hτ'pos, hτ'le, hell'⟩ :=
      SolvesOn_quadForm_persist hn1 Φ hshape τ hτpos (lam / 2 / 2) (by linarith) u huSolves hell0u
    -- ## restricting everything to `[0, τ')`
    have hIco : ∀ t ∈ Set.Ico (0 : ℝ) τ',
        t ∈ Set.Ico (0 : ℝ) τ ∧ t ∈ Set.Ico (0 : ℝ) τ := by
      intro t ht
      exact ⟨⟨ht.1, lt_of_lt_of_le ht.2 hτ'le⟩, ⟨ht.1, lt_of_lt_of_le ht.2 hτ'le⟩⟩
    have huSolves' : SolvesOn Φ τ' u := by
      refine ⟨huSolves.1.mono (fun p hp => ?_), ?_, ?_⟩
      · exact ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 hτ'le⟩, hp.2⟩
      · intro t ht
        exact huSolves.2.1 t ⟨ht.1, lt_of_lt_of_le ht.2 hτ'le⟩
      · intro t ht x
        exact (huSolves.2.2 t ⟨ht.1, lt_of_lt_of_le ht.2 hτ'le⟩ x).mono
          (fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2 hτ'le⟩)
    -- ## symmetry of the solution, from the jet-level symmetry of the nonlinearity
    have hsymm : ∀ t ∈ Set.Ico (0 : ℝ) τ', ∀ (x : Fin n → ℝ) (i j : Fin n),
        u t x i j = u t x j i :=
      SolvesOn_symm_of_jet hn1 Φ hshape hsymΦ τ' hτ'pos (lam / 2 / 2 / 2) (by linarith) u huSolves'
        (fun x i j => by rw [hu0eq]; exact hsym0 x i j) hell'
    -- ## reality of the solution, by uniqueness applied to the conjugate solution
    have hconj_sol : SolvesOn Φ τ' (fun t => conjMat ∘ u t) := solvesOn_conj Φ hconj τ' u huSolves'
    have hconj_pos : ∀ t ∈ Set.Ico (0 : ℝ) τ', ∀ x, PosDefM ((fun t => conjMat ∘ u t) t x) := by
      intro t ht x
      have h := hupos t ⟨ht.1, lt_of_lt_of_le ht.2 hτ'le⟩ x
      simp only [Function.comp_apply, PosDefM, reMat_conjMat]
      exact h
    have hconj0 : (fun t => conjMat ∘ u t) 0 = u 0 := by
      funext x i j
      show conjMat (u 0 x) i j = u 0 x i j
      rw [hu0 x, conjMat_apply, Complex.star_def, Complex.conj_eq_iff_im]
      exact him x i j
    have huniq := torus_uniqueness hn1 Φ hshape τ' u (fun t => conjMat ∘ u t) huSolves'
      hconj_sol (fun t ht x => hupos t ⟨ht.1, lt_of_lt_of_le ht.2 hτ'le⟩ x) hconj_pos hconj0.symm
    have hreal : ∀ t ∈ Set.Ico (0 : ℝ) τ', ∀ (x : Fin n → ℝ) (i j : Fin n),
        (u t x i j).im = 0 := by
      intro t ht x i j
      have h1 : u t x = conjMat (u t x) := by
        have := congrFun (huniq t ht) x
        simpa only [Function.comp_apply] using this
      have h3 := congrFun (congrFun h1 i) j
      simp only [conjMat_apply] at h3
      exact Complex.conj_eq_iff_im.mp (by simpa only [Complex.star_def] using h3.symm)
    exact ⟨τ', hτ'pos, u, huSolves', hu0eq,
      (fun t ht x => hupos t ⟨ht.1, lt_of_lt_of_le ht.2 hτ'le⟩ x), hreal, hsymm⟩

end

end Work.Diff.STE.flat
