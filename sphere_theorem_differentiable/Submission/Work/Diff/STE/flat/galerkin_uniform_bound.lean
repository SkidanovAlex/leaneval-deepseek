/-
# `Work.Diff.STE.flat.galerkin_uniform_bound`

Uniform (in the Galerkin order and in the trajectory) bounds for a family of Galerkin solutions
`c m` of the flat DeTurck system, on the time interval `[0, τ)`.

Given

* a nonlinearity `Φ` of DeTurck shape (`IsDeTurckNonlin Φ`),
* box support `hsupp` of every `c m t` in `box n (Nb m)`,
* the Galerkin ODE `hsol` (`∂_t c m · k = fourierCoeff (Φ ∘ jet) k` on the box),
* uniform ellipticity `hell` (`lam > 0`) and symmetry `hsym` of the metric matrix
  `reMat (seriesFunM (c m t) ·)`,
* the level-`j` energy bounds `hbdd` (`ENormSqFull j (seriesFunM (c m t)) ≤ Blim j` for all `j`),

the theorem produces a single `K ≥ 0` with, for all `m`, all `t, t' ∈ [0,τ)`, all `k, i, j`:

`‖c m t k i j‖ ≤ K`, `‖c m t k i j − c m t' k i j‖ ≤ K |t − t'|` and
`‖fourierCoeff (Φ (·, jet (c m t) ·) i j) k‖ ≤ K`.

## Proof

* **Coefficient bound.**  Parseval for a box-supported family (`ENormSqM_seriesFunM_eq`, level `0`)
  gives `‖c m t k i j‖² ≤ ENormSqM 0 (seriesFunM (c m t)) ≤ ENormSqFull 0 … ≤ Blim 0`.  So
  `K` may be taken `≥ √(Blim 0)`.
* **Sup bounds for the jet.**  The Sobolev bound `norm_seriesFun_le` at level `sob n = n/2 + 1`,
  combined with the level-`j` energy bound, bounds the value, the first and the second coordinate
  derivatives of `seriesFunM (c m t)` *uniformly* in the family, the box size and the point `x`
  (`jet_sup_le_uniform_box`, an in-file copy of `Work.Diff.STE.flat.jet_sup_le_uniform` so that
  this module only depends on the stable Layer A library).
* **Sup bound for `Φ`.**  On the elliptic ball the DeTurck nonlinearity is bounded by a constant
  depending only on `n`, `lam` and the jet size (`phi_bound`, imported).
* **Fourier coefficients.**  A Fourier coefficient is a mean of the modulus
  (`norm_fourierCoeff_sub_le`), so the sup bound of `Φ ∘ jet` on the unit cube bounds every
  coefficient, uniformly in the frequency.
* **Lipschitz in time.**  The ODE `hsol` writes the derivative of `t ↦ c m t k i j` as exactly the
  Fourier coefficient just bounded, so the mean value inequality gives the Lipschitz bound.

The `0 < τ` hypothesis is not needed: it only ensures that `[0, τ)` is nonempty, whereas the bounds
above are proved for arbitrary `t, t'` in that interval.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.phi_bound
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.norm_fourierCoeff_sub_le
import Submission.Work.Diff.STE.flat.seriesFunM_eq_sum
import Submission.Work.Diff.STE.CSq_le_ENormSq_seriesFun
import Submission.Work.Diff.STE.flat.energy_differentiable
import Submission.Work.Diff.STE.flat.GalerkinJet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open Work.Diff.STE.Flat.Galerkin
open MeasureTheory BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Coefficient bounds from the energy

For a box-supported coefficient family the `L²`-energy of the corresponding trigonometric
polynomial controls every one of its coefficients: this is Parseval's identity restricted to the
(finitely many) frequencies in the box (`ENormSqM_seriesFunM_eq`). -/

/-- Every coefficient of a box-supported family is dominated (in modulus squared) by the `L²`
energy of the associated Fourier series. -/
lemma norm_coeff_sq_le_energy {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) {k : Fin n → ℤ} (hk : k ∈ box n N)
    (i j : Fin n) :
    ‖c k i j‖ ^ 2 ≤ ENormSqM 0 (seriesFunM c) := by
  rw [ENormSqM_seriesFunM_eq N 0 c hc]
  have hnil : (List.ofFn (Fin.elim0 : Fin 0 → Fin n) : List (Fin n)) = [] :=
    List.eq_nil_of_length_eq_zero (by simp)
  have hterm : ‖c k i j‖ ^ 2
      ≤ ∑ k' ∈ box n N,
          ‖dmulV (List.ofFn (Fin.elim0 : Fin 0 → Fin n)) (fun k => c k i j) k'‖ ^ 2 := by
    rw [hnil, dmulV_nil]
    exact Finset.single_le_sum (f := fun k' => ‖c k' i j‖ ^ 2) (fun k' _ => by positivity) hk
  have h1 : (∑ k' ∈ box n N,
        ‖dmulV (List.ofFn (Fin.elim0 : Fin 0 → Fin n)) (fun k => c k i j) k'‖ ^ 2)
      ≤ ∑ l : Fin 0 → Fin n,
          ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k i j) k'‖ ^ 2 :=
    Finset.single_le_sum (f := fun l : Fin 0 → Fin n =>
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k i j) k'‖ ^ 2)
      (fun l _ => Finset.sum_nonneg fun k' _ => by positivity) (Finset.mem_univ _)
  have h2 : (∑ l : Fin 0 → Fin n,
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k i j) k'‖ ^ 2)
      ≤ ∑ b : Fin n, ∑ l : Fin 0 → Fin n,
          ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k i b) k'‖ ^ 2 :=
    Finset.single_le_sum (f := fun b : Fin n => ∑ l : Fin 0 → Fin n,
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k i b) k'‖ ^ 2)
      (fun b _ => Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun k' _ => by positivity) (Finset.mem_univ j)
  have h3 : (∑ b : Fin n, ∑ l : Fin 0 → Fin n,
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k i b) k'‖ ^ 2)
      ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin 0 → Fin n,
          ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k a b) k'‖ ^ 2 :=
    Finset.single_le_sum (f := fun a : Fin n => ∑ b : Fin n, ∑ l : Fin 0 → Fin n,
        ∑ k' ∈ box n N, ‖dmulV (List.ofFn l) (fun k => c k a b) k'‖ ^ 2)
      (fun a _ => Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun k' _ => by positivity) (Finset.mem_univ i)
  exact hterm.trans (h1.trans (h2.trans h3))

/-- Every coefficient of a box-supported family is dominated by the square root of the `L²` energy
of the associated Fourier series. -/
lemma norm_coeff_le_sqrt_energy {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (k : Fin n → ℤ) (i j : Fin n) :
    ‖c k i j‖ ≤ Real.sqrt (ENormSqFull 0 (seriesFunM c)) := by
  rw [Real.le_sqrt (norm_nonneg _) (ENormSqFull_nonneg 0 _)]
  by_cases hk : k ∈ box n N
  · exact (norm_coeff_sq_le_energy c hc hk i j).trans (ENormSqM_le_ENormSqFull 0 (seriesFunM c))
  · have hzero : ‖c k i j‖ ^ 2 = 0 := by
      rw [hc k hk]
      simp
    rw [hzero]
    exact ENormSqFull_nonneg 0 _

/-! ## Sup bounds for the jet of a box-supported Fourier series

This is `Work.Diff.STE.flat.jet_sup_le_uniform` (`ellipticity_persist`), reproduced here so that
this module only depends on the (stable) Layer A library. -/

/-- **Uniform sup bounds for the derivatives of `seriesFunM c`** in terms of the level-`k`
energy. -/
lemma jet_sup_le_uniform_box {n k m : ℕ} (hm : m + sob n ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k', k' ∉ box n N → c k' = 0) → ∀ (l : Fin m → Fin n) (i j : Fin n) (x : Fin n → ℝ),
      ‖pdVec m l (fun y => seriesFunM c y i j) x‖
        ≤ C * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))) := by
  obtain ⟨C0, hC0, h0⟩ := norm_seriesFun_le (ι := Fin n) (sob n) (by simpa using n_lt_two_sob n)
  obtain ⟨C2, hC2, h2⟩ := CSq_le_ENormSq_seriesFun (ι := Fin n) k
  refine ⟨C0 * (2 * Real.pi) ^ m * Real.sqrt C2, by positivity, ?_⟩
  intro N c hc l i j x
  have hmom : ∀ M : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ M * ‖c k i j‖) :=
    fun M => summable_moment_box c hc i j M
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j)
      = seriesFun (fun k : Fin n → ℤ => c k i j) := by
    funext y; rw [seriesFunM_apply]
  have hpd : pdVec m l (fun y => seriesFunM c y i j) x
      = seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x := by
    rw [hfun]
    exact pdList_seriesFun (List.ofFn l) (fun k => c k i j) hmom x
  rw [hpd]
  have hstep := h0 (dmulV (List.ofFn l) (fun k => c k i j))
    (summable_wt_pow_mul_norm_sq _ (fun M => summable_dmulV _ _ hmom M) (sob n)) x
  have hCSq : CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))
      ≤ ((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j) := by
    have h := CSq_dmulV_le (sob n) (List.ofFn l) (fun k => c k i j) hmom
    simpa [List.length_ofFn] using h
  have hlev : sob n + m ≤ k := by omega
  have hmono : CSq (sob n + m) (fun k : Fin n → ℤ => c k i j)
      ≤ CSq k (fun k => c k i j) := by
    rw [CSq, CSq]
    refine Summable.tsum_le_tsum (fun k => ?_)
      (summable_wt_pow_mul_norm_sq _ hmom (sob n + m))
      (summable_wt_pow_mul_norm_sq _ hmom k)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (wt_one_le k) hlev) (sq_nonneg _)
  have h4 : CSq k (fun k : Fin n → ℤ => c k i j) ≤ C2 * ENormSqFull k (seriesFunM c) := by
    have h := h2 (fun k => c k i j) hmom
    have hEs : ENormSq k (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM k (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := k) (seriesFunM c) i j
      rwa [hfun] at hh
    have hE0 : ENormSq 0 (seriesFun (fun k : Fin n → ℤ => c k i j))
        ≤ ENormSqM 0 (seriesFunM c) := by
      have hh := ENormSq_le_ENormSqM (j := 0) (seriesFunM c) i j
      rwa [hfun] at hh
    refine h.trans ?_
    rw [ENormSqFull]
    exact mul_le_mul_of_nonneg_left (add_le_add hEs hE0) hC2
  calc ‖seriesFun (dmulV (List.ofFn l) (fun k => c k i j)) x‖
      ≤ C0 * Real.sqrt (CSq (sob n) (dmulV (List.ofFn l) (fun k => c k i j))) := hstep
    _ ≤ C0 * Real.sqrt (((2 * Real.pi) ^ 2) ^ m * CSq (sob n + m) (fun k => c k i j)) := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCSq) hC0
    _ = C0 * ((2 * Real.pi) ^ m * Real.sqrt (CSq (sob n + m) (fun k => c k i j))) := by
        have hsq : ((2 * Real.pi) ^ 2) ^ m = ((2 * Real.pi) ^ m) ^ 2 := by
          rw [← pow_mul]; ring_nf
        rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ C0 * ((2 * Real.pi) ^ m * Real.sqrt (C2 * ENormSqFull k (seriesFunM c))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
        exact hmono.trans h4
    _ = C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2 * Real.sqrt (ENormSqFull k (seriesFunM c)))) := by
        rw [Real.sqrt_mul hC2]
    _ ≤ C0 * ((2 * Real.pi) ^ m * (Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg C2)
    _ = C0 * (2 * Real.pi) ^ m * Real.sqrt C2
          * (1 + Real.sqrt (ENormSqFull k (seriesFunM c))) := by ring

/-- Uniform (in the box size and in the family) sup bounds for the value, the first and the second
coordinate derivatives of `seriesFunM c`, in terms of the level `sob n + 2` energy: this is
`jet_sup_le_uniform_box` rewritten in the three components of `jetM`. -/
lemma jet_entry_bounds {n : ℕ} :
    ∃ C0 C1 C2 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 ≤ C2 ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n), (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
        ∀ (x : Fin n → ℝ) (i j : Fin n),
          ‖(jetM (seriesFunM c) x).1 i j‖
              ≤ C0 * (1 + Real.sqrt (ENormSqFull (sob n + 2) (seriesFunM c))) ∧
          (∀ c' : Fin n, ‖(jetM (seriesFunM c) x).2.1 c' i j‖
              ≤ C1 * (1 + Real.sqrt (ENormSqFull (sob n + 2) (seriesFunM c)))) ∧
          (∀ c' d' : Fin n, ‖(jetM (seriesFunM c) x).2.2 c' d' i j‖
              ≤ C2 * (1 + Real.sqrt (ENormSqFull (sob n + 2) (seriesFunM c)))) := by
  obtain ⟨C0, hC0, h0⟩ := jet_sup_le_uniform_box (n := n) (k := sob n + 2) (m := 0) (by omega)
  obtain ⟨C1, hC1, h1⟩ := jet_sup_le_uniform_box (n := n) (k := sob n + 2) (m := 1) (by omega)
  obtain ⟨C2, hC2, h2⟩ := jet_sup_le_uniform_box (n := n) (k := sob n + 2) (m := 2) (by omega)
  refine ⟨C0, C1, C2, hC0, hC1, hC2, ?_⟩
  intro N c hc x i j
  refine ⟨?_, ?_, ?_⟩
  · have h := h0 N c hc (Fin.elim0 : Fin 0 → Fin n) i j x
    simpa [jetM, pdVec, pdList] using h
  · intro c'
    have h := h1 N c hc (fun _ : Fin 1 => c') i j x
    simpa [jetM, pdM, pdVec, pdList] using h
  · intro c' d'
    have h := h2 N c hc (fun l : Fin 2 => if l = 0 then c' else d') i j x
    simpa [jetM, pdM, pdVec, pdList] using h

/-! ## Continuity and a sup bound for the nonlinearity on a box-supported series -/

/-- Each entry of `x ↦ Φ (x, jet of (seriesFunM c) at x)` is continuous, provided the series is
uniformly elliptic (so that its jet lands in the nondegenerate locus on which `Φ` is smooth). -/
lemma continuous_phi_entry_seriesFunM {n : ℕ}
    (Φ : (Fin n → ℝ) × Jet n → MatC n) (hshape : IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) {N : ℕ} (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i : Fin n, (v i) ^ 2
        ≤ ∑ i : Fin n, ∑ j : Fin n, reMat (seriesFunM c x) i j * v i * v j)
    (hsym : ∀ (x : Fin n → ℝ) (i j : Fin n),
      reMat (seriesFunM c x) i j = reMat (seriesFunM c x) j i)
    (i j : Fin n) :
    Continuous (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM c) x) i j) := by
  obtain ⟨hΦcont, -⟩ := hshape
  let a : Coeff n N := ofCoeff c hc
  have hto : toCoeff a = c := toCoeff_ofCoeff c hc
  have hJ : Continuous (fun x : Fin n → ℝ => (x, jetExp a x)) :=
    continuous_id.prodMk (contDiff_jetExp_fixed a).continuous
  have hmem : ∀ x : Fin n → ℝ,
      (x, jetExp a x) ∈ Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0} := by
    intro x
    refine ⟨Set.mem_univ x, ?_⟩
    have h1 : (jetExp a x).1 = seriesFunM c x := by
      rw [← hto]
      exact valExp_eq_seriesFunM a x
    show (reMat ((x, jetExp a x).2.1)).det ≠ 0
    rw [show (x, jetExp a x).2.1 = (jetExp a x).1 from rfl, h1]
    exact reMat_det_ne_zero_of_elliptic (seriesFunM c x) hlam (hsym x) (hell x)
  have hcomp : Continuous (fun x : Fin n → ℝ => Φ (x, jetExp a x)) :=
    hΦcont.continuousOn.comp_continuous hJ hmem
  have hcomp' : Continuous (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM c) x)) :=
    hcomp.congr (fun x => by
      show Φ (x, jetExp a x) = Φ (x, jetM (seriesFunM c) x)
      rw [← jetM_seriesFunM_toCoeff a x, hto])
  exact (continuous_apply j).comp ((continuous_apply i).comp hcomp')

/-- **Sup bound for the nonlinearity on the elliptic locus.**  For a nonlinearity of DeTurck shape,
a box-supported series whose jet is uniformly elliptic and whose level `(sob n + 2)` energy is
bounded by `B`, every entry of `Φ (·, jet)` is bounded on the unit cube by a constant depending only
on the dimension, on `lam` and on `B`. -/
lemma exists_phi_bound_seriesFunM {n : ℕ}
    (Φ : (Fin n → ℝ) × Jet n → MatC n) (hshape : IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
        (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
        ENormSqFull (sob n + 2) (seriesFunM c) ≤ B →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i : Fin n, (v i) ^ 2
            ≤ ∑ i : Fin n, ∑ j : Fin n, reMat (seriesFunM c x) i j * v i * v j) →
        (∀ (x : Fin n → ℝ) (i j : Fin n),
          reMat (seriesFunM c x) i j = reMat (seriesFunM c x) j i) →
        ∀ (x : Fin n → ℝ), x ∈ Work.Diff.STE.unitCube (ι := Fin n) → ∀ (i j : Fin n),
          ‖Φ (x, jetM (seriesFunM c) x) i j‖ ≤ C := by
  obtain ⟨C0, C1, C2, hC0, hC1, hC2, hjet⟩ := jet_entry_bounds (n := n)
  obtain ⟨C, hC, hCbound⟩ := phi_bound n Φ hshape lam hlam
    (C0 * (1 + Real.sqrt B)) (C1 * (1 + Real.sqrt B)) (C2 * (1 + Real.sqrt B))
  have hS : (0 : ℝ) ≤ 1 + Real.sqrt B := by positivity
  have hBL : (0 : ℝ) ≤ C1 * (1 + Real.sqrt B) := mul_nonneg hC1 hS
  have hBB : (0 : ℝ) ≤ C2 * (1 + Real.sqrt B) := mul_nonneg hC2 hS
  refine ⟨C, hC, ?_⟩
  intro N c hc hbdd hell hsym x hx i j
  have hle : Real.sqrt (ENormSqFull (sob n + 2) (seriesFunM c)) ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt hbdd
  have hSle : (1 : ℝ) + Real.sqrt (ENormSqFull (sob n + 2) (seriesFunM c))
      ≤ 1 + Real.sqrt B := by linarith
  have hx' : x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun k => ⟨le_of_lt (hx k).1, (hx k).2⟩
  have hA : ∀ i' j' : Fin n, ‖(jetM (seriesFunM c) x).1 i' j'‖ ≤ C0 * (1 + Real.sqrt B) := by
    intro i' j'
    exact ((hjet N c hc x i' j').1).trans (mul_le_mul_of_nonneg_left hSle hC0)
  have hL : ∀ i' : Fin n, ‖(jetM (seriesFunM c) x).2.1 i'‖ ≤ C1 * (1 + Real.sqrt B) := by
    intro i'
    refine (pi_norm_le_iff_of_nonneg hBL).mpr (fun j' => ?_)
    refine (pi_norm_le_iff_of_nonneg hBL).mpr (fun j'' => ?_)
    exact ((hjet N c hc x j' j'').2.1 i').trans (mul_le_mul_of_nonneg_left hSle hC1)
  have hBs : ∀ i' j' : Fin n, ‖(jetM (seriesFunM c) x).2.2 i' j'‖ ≤ C2 * (1 + Real.sqrt B) := by
    intro i' j'
    refine (pi_norm_le_iff_of_nonneg hBB).mpr (fun a => ?_)
    refine (pi_norm_le_iff_of_nonneg hBB).mpr (fun b => ?_)
    exact (((hjet N c hc x a b).2.2 i' j')).trans (mul_le_mul_of_nonneg_left hSle hC2)
  have hmain : ‖Φ (x, jetM (seriesFunM c) x)‖ ≤ C :=
    hCbound x hx' (jetM (seriesFunM c) x).1 (jetM (seriesFunM c) x).2.1
      (jetM (seriesFunM c) x).2.2 (fun i' j' => hsym x i' j') (fun v => hell x v) hA hL hBs
  have h1 : ‖Φ (x, jetM (seriesFunM c) x) i j‖ ≤ ‖Φ (x, jetM (seriesFunM c) x) i‖ :=
    norm_le_pi_norm _ j
  have h2 : ‖Φ (x, jetM (seriesFunM c) x) i‖ ≤ ‖Φ (x, jetM (seriesFunM c) x)‖ :=
    norm_le_pi_norm _ i
  exact h1.trans (h2.trans hmain)

end

theorem galerkin_uniform_bound {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (τ : ℝ) (hτ : 0 < τ) (lam : ℝ) (hlam : 0 < lam)
    (Blim : ℕ → ℝ) (hBlim : ∀ j : ℕ, 0 ≤ Blim j)
    (Nb : ℕ → ℕ) (c : ℕ → ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hsol : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k' ∈ Work.Diff.STE.Flat.box n (Nb m),
      ∀ (i j : Fin n),
      HasDerivAt (fun s => c m s k' i j)
        (Work.Diff.STE.fourierCoeff (fun x =>
          Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c m t)) x) i j) k') t)
    (hell : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * Finset.sum Finset.univ (fun i : Fin n => (v i) ^ 2) ≤
        Finset.sum Finset.univ (fun i : Fin n => Finset.sum Finset.univ (fun j : Fin n =>
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) i j * v i * v j)))
    (hsym : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (i j : Fin n),
      Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) i j
        = Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c m t) x) j i)
    (hsupp : ∀ (m : ℕ) (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n (Nb m) →
      c m t k' = 0)
    (hbdd : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ j : ℕ,
      Work.Diff.STE.Flat.ENormSqFull j (Work.Diff.STE.Flat.seriesFunM (c m t)) ≤ Blim j) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ t' ∈ Set.Ico (0 : ℝ) τ,
      ∀ (k : Fin n → ℤ) (i j : Fin n),
      ‖c m t k i j‖ ≤ K ∧
      ‖c m t k i j - c m t' k i j‖ ≤ K * |t - t'| ∧
      ‖Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ =>
        Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c m t)) x) i j) k‖ ≤ K := by
  classical
  obtain ⟨C, hC, hCbound⟩ :=
    exists_phi_bound_seriesFunM Φ hshape lam hlam (Blim (sob n + 2)) (hBlim (sob n + 2))
  set K : ℝ := max C (Real.sqrt (Blim 0)) with hKdef
  have hCK : C ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hK1K : Real.sqrt (Blim 0) ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK0 : 0 ≤ K := hC.trans hCK
  refine ⟨K, hK0, ?_⟩
  intro m t ht t' ht' k i j
  have hfourier : ∀ s ∈ Set.Ico (0 : ℝ) τ,
      ‖Work.Diff.STE.fourierCoeff (fun x : Fin n → ℝ =>
        Φ (x, jetM (seriesFunM (c m s)) x) i j) k‖ ≤ C := by
    intro s hs
    have hcont : Continuous (fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM (c m s)) x) i j) :=
      continuous_phi_entry_seriesFunM Φ hshape lam hlam (c m s) (hsupp m s)
        (hell m s hs) (hsym m s hs) i j
    have hpt : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
        ‖Φ (x, jetM (seriesFunM (c m s)) x) i j - 0‖ ≤ C := by
      intro x hx
      rw [sub_zero]
      exact hCbound (Nb m) (c m s) (hsupp m s) (hbdd m s hs (sob n + 2))
        (hell m s hs) (hsym m s hs) x hx i j
    have h := norm_fourierCoeff_sub_le
      (f := fun x : Fin n → ℝ => Φ (x, jetM (seriesFunM (c m s)) x) i j)
      (g := fun _ : Fin n → ℝ => (0 : ℂ))
      hcont.continuousOn continuous_const.continuousOn hC hpt k
    simpa [Work.Diff.STE.fourierCoeff] using h
  refine ⟨?_, ?_, ?_⟩
  · refine (norm_coeff_le_sqrt_energy (c m t) (hsupp m t) k i j).trans ?_
    exact (Real.sqrt_le_sqrt (hbdd m t ht 0)).trans hK1K
  · by_cases hk : k ∈ box n (Nb m)
    · have hsub : Set.Icc (min t t') (max t t') ⊆ Set.Ico (0 : ℝ) τ := by
        intro s hs
        exact ⟨le_trans (le_min ht.1 ht'.1) hs.1, lt_of_le_of_lt hs.2 (max_lt ht.2 ht'.2)⟩
      have hdiff : ∀ s ∈ Set.Icc (min t t') (max t t'),
          DifferentiableAt ℝ (fun σ => c m σ k i j) s :=
        fun s hs => (hsol m s (hsub hs) k hk i j).differentiableAt
      have hbd : ∀ s ∈ Set.Icc (min t t') (max t t'),
          ‖deriv (fun σ => c m σ k i j) s‖ ≤ C := by
        intro s hs
        rw [(hsol m s (hsub hs) k hk i j).deriv]
        exact hfourier s (hsub hs)
      have hconv : Convex ℝ (Set.Icc (min t t') (max t t')) := convex_Icc _ _
      have htmem : t ∈ Set.Icc (min t t') (max t t') := ⟨min_le_left _ _, le_max_left _ _⟩
      have ht'mem : t' ∈ Set.Icc (min t t') (max t t') := ⟨min_le_right _ _, le_max_right _ _⟩
      have hmain := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd hconv htmem ht'mem
      calc ‖c m t k i j - c m t' k i j‖
          = ‖c m t' k i j - c m t k i j‖ := norm_sub_rev _ _
        _ ≤ C * ‖t' - t‖ := hmain
        _ = C * |t - t'| := by rw [Real.norm_eq_abs, abs_sub_comm]
        _ ≤ K * |t - t'| := mul_le_mul_of_nonneg_right hCK (abs_nonneg _)
    · have h1 : (c m t) k i j = 0 := by
        rw [hsupp m t k hk]
        simp
      have h2 : (c m t') k i j = 0 := by
        rw [hsupp m t' k hk]
        simp
      rw [h1, h2, sub_zero, norm_zero]
      exact mul_nonneg hK0 (abs_nonneg _)
  · exact (hfourier t ht).trans hCK

end Work.Diff.STE.flat
