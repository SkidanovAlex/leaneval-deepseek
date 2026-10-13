import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Engine

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology
open scoped BigOperators

set_option maxHeartbeats 2000000

namespace Work.WilkG4c

/-! ## Self-contained analytic helpers

The statement below is `Work.WilkG4c.pt_jet_le_multi` with the near-maximality hypothesis `hmax`
*and* the curve bound `hcurve` required only off a finite "bad" set `B` of `x`-coordinates.
At a bad point `x ∈ B` the pointwise bound is recovered by continuity: on the dense set of
good coordinates `x' ∈ I \ B` both hypotheses apply, and the `x`-slice of the jet is continuous
at `x`.  The few analytic facts this uses are proved here so that the theorem does not depend
on modules that are still under construction elsewhere in the tree. -/

/-- If `f : X → ℝ` is continuous at `x₀` and satisfies `|f x| ≤ C` on a set `s` that
accumulates at `x₀` (`x₀ ∈ closure s`), then `|f x₀| ≤ C`. -/
private lemma abs_le_of_contAt_closure_v2 {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {C : ℝ} {x₀ : X} {s : Set X}
    (hs : x₀ ∈ closure s) (hf : ContinuousAt f x₀) (hb : ∀ x ∈ s, |f x| ≤ C) :
    |f x₀| ≤ C := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hmem : f ⁻¹' Metric.ball (f x₀) ε ∈ nhds x₀ :=
    hf.preimage_mem_nhds (Metric.ball_mem_nhds (f x₀) hε)
  obtain ⟨y, hyU, hys⟩ := (mem_closure_iff_nhds.mp hs) _ hmem
  have hy1 : |f y - f x₀| < ε := by
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hyU
    exact hyU
  have hy2 : |f y| ≤ C := hb y hys
  have h1 : |f x₀| ≤ |f x₀ - f y| + |f y| := by
    simpa using abs_add_le (f x₀ - f y) (f y)
  have h2 : |f x₀ - f y| = |f y - f x₀| := abs_sub_comm _ _
  linarith

/-- The `x`-slice of the `m`-jet of a function that is `C^m` at `pt x y`, evaluated on a fixed
tuple of coordinate directions, varies continuously in `x`. -/
private lemma continuousAt_pt_jet' {n m : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ}
    {v : Fin m → Fin (n + 1)} {y : Fin n → ℝ} {x : ℝ}
    (hG : ContDiffAt ℝ m G (Work.WilkG4c.pt x y)) :
    ContinuousAt (fun x' : ℝ =>
      iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y) (fun k => Pi.single (v k) 1)) x := by
  have hpt : ContinuousAt (fun x' : ℝ => Work.WilkG4c.pt x' y) x := by
    apply Continuous.continuousAt
    rw [continuous_pi_iff]
    intro i
    induction i using Fin.cases with
    | zero => exact continuous_id
    | succ j => exact continuous_const
  have hderiv : ContinuousAt (iteratedFDeriv ℝ m G) (Work.WilkG4c.pt x y) :=
    hG.continuousAt_iteratedFDeriv le_rfl
  have hcomp : ContinuousAt (fun x' : ℝ => iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y)) x :=
    ContinuousAt.comp (f := fun x' : ℝ => Work.WilkG4c.pt x' y) (x := x)
      (g := iteratedFDeriv ℝ m G) hderiv hpt
  have hc : ContinuousAt (fun _ : ℝ =>
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Fin (n + 1) → ℝ) ℝ
        (fun k => Pi.single (v k) 1)) x := continuousAt_const
  have h2 := hc.clm_apply hcomp
  simpa only [ContinuousMultilinearMap.apply_apply] using h2

/-- The "good" `x`-coordinates — inside `I`, outside the finite bad set `B`, and with `pt x y`
in a given open set `U` — accumulate at every point `x ∈ I` whose own `pt x y` lies in `U`. -/
private lemma mem_closure_good_pts' {n : ℕ} (B : Finset ℝ) {y : Fin n → ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) {x : ℝ}
    (hxU : Work.WilkG4c.pt x y ∈ U) (hxI : x ∈ Work.WilkG4c.I) :
    x ∈ closure {x' : ℝ | x' ∈ Work.WilkG4c.I ∧ x' ∉ (B : Set ℝ) ∧
      Work.WilkG4c.pt x' y ∈ U} := by
  -- The slice `x' ↦ pt x' y` is continuous.
  have hg : Continuous (fun x' : ℝ => Work.WilkG4c.pt x' y) := by
    rw [continuous_pi_iff]
    intro i
    induction i using Fin.cases with
    | zero => exact continuous_id
    | succ j => exact continuous_const
  -- `A := I ∩ {x' | pt x' y ∈ U}` is a neighbourhood of `x`.
  have hAmem : (Work.WilkG4c.I ∩ (fun x' : ℝ => Work.WilkG4c.pt x' y) ⁻¹' U) ∈ 𝓝 x :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds hxI) ((hU.preimage hg).mem_nhds hxU)
  -- The complement of a finite set is dense.
  have hBdense : Dense (((B : Set ℝ))ᶜ) := by
    rw [Set.compl_eq_univ_sdiff]
    exact dense_univ.sdiff_finset B
  rw [mem_closure_iff_nhds]
  intro W hW
  have hWTV : W ∩ (Work.WilkG4c.I ∩ (fun x' : ℝ => Work.WilkG4c.pt x' y) ⁻¹' U) ∈ 𝓝 x :=
    Filter.inter_mem hW hAmem
  rcases hBdense.inter_nhds_nonempty hWTV with ⟨u, huBc, huW⟩
  exact ⟨u, huW.1, huW.2.1, huBc, huW.2.2⟩

/-! ### Coordinate expansion of a multilinear form -/

/-- Coordinate expansion in the standard basis of `Fin N → ℝ`: `x j • e_j` is the `j`-th
coordinate vector `Pi.single j (x j)`. -/
private lemma smul_pi_single' (N : ℕ) (x : Fin N → ℝ) (j : Fin N) :
    (x j) • Pi.single j (1 : ℝ) = Pi.single j (x j) := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_apply, h]

/-- Reassembly of a vector in `Fin N → ℝ` from its coordinate functions. -/
private lemma sum_pi_single_eq_self' (N : ℕ) (x : Fin N → ℝ) :
    (∑ j : Fin N, Pi.single j (x j)) = x := by
  ext i
  rw [Finset.sum_apply]
  simpa using Finset.sum_pi_single i x Finset.univ

/-- The expansion of a vector in `Fin N → ℝ` in the standard basis. -/
private lemma sum_smul_single' (N : ℕ) (x : Fin N → ℝ) :
    (∑ j : Fin N, (x j) • Pi.single j (1 : ℝ)) = x := by
  simpa only [smul_pi_single'] using sum_pi_single_eq_self' N x

/-- **Multilinear expansion bound.**  If the `m`-linear form `A = D^m G(z)` is bounded by `C` on
all tuples of coordinate directions, then it is bounded by `C * N^m` on all tuples of vectors,
after multiplying by `∏ i, ‖x i‖`. -/
private lemma norm_expansion_bound' {N m : ℕ} (G : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ) (C : ℝ)
    (h : ∀ v : Fin m → Fin N, |iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1)| ≤ C)
    (x : Fin m → (Fin N → ℝ)) :
    ‖iteratedFDeriv ℝ m G z x‖ ≤ (C * (N : ℝ) ^ m) * ∏ i, ‖x i‖ := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin m => Fin N → ℝ) ℝ := iteratedFDeriv ℝ m G z
  have hAeval : ∀ v : Fin m → Fin N, |A (fun k => Pi.single (v k) 1)| ≤ C := h
  have hA : A x = ∑ r : Fin m → Fin N,
      A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ)) := by
    have hmap := ContinuousMultilinearMap.map_sum A
      (fun (i : Fin m) (j : Fin N) => (x i j) • Pi.single j (1 : ℝ))
    rw [← hmap]
    exact congr_arg A (funext (fun i => (sum_smul_single' N (x i)).symm))
  have hterm : ∀ r : Fin m → Fin N,
      ‖A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ))‖
        = (∏ i, |x i (r i)|) * |A (fun i => Pi.single (r i) (1 : ℝ))| := by
    intro r
    rw [ContinuousMultilinearMap.map_smul_univ, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, Finset.abs_prod]
  calc ‖A x‖
      = ‖∑ r : Fin m → Fin N, A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ))‖ := by
        rw [hA]
    _ ≤ ∑ r : Fin m → Fin N, ‖A (fun i => (x i (r i)) • Pi.single (r i) (1 : ℝ))‖ :=
        norm_sum_le Finset.univ _
    _ = ∑ r : Fin m → Fin N,
          (∏ i, |x i (r i)|) * |A (fun i => Pi.single (r i) (1 : ℝ))| :=
        Finset.sum_congr rfl (fun r _ => hterm r)
    _ ≤ ∑ r : Fin m → Fin N, (∏ i, ‖x i‖) * C := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        have hprod : (∏ i, |x i (r i)|) ≤ ∏ i, ‖x i‖ :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (x i) (r i))
        exact mul_le_mul hprod (hAeval r) (abs_nonneg _)
          (Finset.prod_nonneg (fun i _ => norm_nonneg _))
    _ = (Fintype.card (Fin m → Fin N) : ℝ) * ((∏ i, ‖x i‖) * C) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (C * (N : ℝ) ^ m) * ∏ i, ‖x i‖ := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
        ring

/-- The operator norm of the `m`-th iterated derivative of `G` at `z` is bounded by `N^m` times
any uniform bound on its values at the coordinate direction tuples `(Pi.single i 1)`. -/
private theorem norm_iteratedFDeriv_le_of_dirs' {N m : ℕ} (G : (Fin N → ℝ) → ℝ) (z : Fin N → ℝ)
    (C : ℝ) (h : ∀ v : Fin m → Fin N, |iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1)| ≤ C) :
    ‖iteratedFDeriv ℝ m G z‖ ≤ C * (N : ℝ) ^ m := by
  have hM : 0 ≤ C * (N : ℝ) ^ m := by
    by_cases hv : Nonempty (Fin m → Fin N)
    · obtain ⟨v0⟩ := hv
      exact mul_nonneg (le_trans (abs_nonneg _) (h v0)) (by positivity)
    · have hN0 : N = 0 := by
        by_contra hN
        exact hv ⟨fun _ : Fin m => (⟨0, Nat.pos_of_ne_zero hN⟩ : Fin N)⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hv ⟨fun i : Fin 0 => Fin.elim0 i⟩
      have hNpow : (N : ℝ) ^ m = 0 := by
        have h1 : (N : ℝ) = 0 := by exact_mod_cast hN0
        rw [h1, zero_pow hm0]
      simp [hNpow]
  exact ContinuousMultilinearMap.opNorm_le_bound (M := C * (N : ℝ) ^ m) hM
    (fun x => norm_expansion_bound' G z C h x)

/-! ## The theorem -/

theorem pt_jet_le_multi_bad_offBC {n r : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ)
    (γ : (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ) (B : Finset ℝ)
    (hmax : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x) (fun k => Pi.single (v k) 1)|)
    (hcurve : ∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r →
      x ∈ Work.WilkG4c.I → x ∉ (B : Set ℝ) → y ∈ WilkiesDesign.openCube n →
      ContDiffAt ℝ m G (Work.WilkG4c.pt x y) →
      |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)
    {m : ℕ} (hm : m ≤ r) {x : ℝ} {y : Fin n → ℝ} (hx : x ∈ Work.WilkG4c.I)
    (hy : y ∈ WilkiesDesign.openCube n) (hG : ContDiffAt ℝ m G (Work.WilkG4c.pt x y)) :
    ‖iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y)‖ ≤
      2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by
  -- Bound the jet at `pt x y` on every tuple of coordinate directions.
  have hC : ∀ v : Fin m → Fin (n + 1),
      |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) := by
    intro v
    -- `G` is `C^m` on a neighbourhood of `pt x y`; take its interior as the open `U`.
    obtain ⟨U, hUnhds, hUcd⟩ := hG.contDiffOn le_rfl (fun h => absurd h (by simp))
    -- The set of good `x`-coordinates (inside `I`, outside `B`, with `pt · y` in `U`).
    refine abs_le_of_contAt_closure_v2
      (f := fun x' : ℝ => iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y) (fun k => Pi.single (v k) 1))
      (x₀ := x) (C := 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m))
      (s := {x' : ℝ | x' ∈ Work.WilkG4c.I ∧ x' ∉ (B : Set ℝ) ∧
        Work.WilkG4c.pt x' y ∈ interior U})
      ?_ (continuousAt_pt_jet' hG) ?_
    · -- the good coordinates accumulate at `x`
      exact mem_closure_good_pts' (B := B) (y := y) (U := interior U) isOpen_interior
        (mem_interior_iff_mem_nhds.mpr hUnhds) hx
    · -- and the bound holds at every good coordinate
      intro x' hx'
      obtain ⟨hx'I, hx'B, hx'U⟩ := hx'
      have hcd : ContDiffAt ℝ m G (Work.WilkG4c.pt x' y) :=
        hUcd.contDiffAt (Filter.mem_of_superset (isOpen_interior.mem_nhds hx'U) interior_subset)
      calc |iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y) (fun k => Pi.single (v k) 1)|
          ≤ 2 * |iteratedFDeriv ℝ m G (Work.WilkG4c.curveFun (γ m v) x')
                (fun k => Pi.single (v k) 1)| := hmax m v x' y hm hx'I hx'B hy hcd
        _ ≤ 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) :=
            mul_le_mul_of_nonneg_left (hcurve m v x' y hm hx'I hx'B hy hcd) (by norm_num)
  -- Multilinear expansion: `(n+1)^m` coordinate tuples.
  have hbound := norm_iteratedFDeriv_le_of_dirs' G (Work.WilkG4c.pt x y)
    (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) hC
  calc ‖iteratedFDeriv ℝ m G (Work.WilkG4c.pt x y)‖
      ≤ (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m)) * ((n + 1 : ℕ) : ℝ) ^ m := hbound
    _ = 2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m := by
        rw [Nat.cast_add, Nat.cast_one]

end Work.WilkG4c
