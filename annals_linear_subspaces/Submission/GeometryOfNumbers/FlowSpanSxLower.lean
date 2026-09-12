import Submission.Work.ModelStar.ModelStar
import Submission.GeometryOfNumbers.FlowLatticeMinimaLower
import Submission.GeometryOfNumbers.ImageLatticeCovolume
import ChallengeDeps

/-!
# (s1′) first sheared bound: the norm floor of the sheared flow lattice

The coordinate §3 chain (`sessions 52–68`) established exact short/long rates for the
lattice `a_t ℤᵈ`.  For a general plane `x = P s_x` the relevant lattice is the *sheared*
flow lattice `Λ_t^x = (a_t ∘ s_x)(ℤᵈ)` (`Submission.ImageLattice.flowSpan_sx`).  This file
starts (s1′): the first genuinely per-`x` bound that is true for **arbitrary** `s_x`.

**Caveat (recorded)**: a naive composition of the coordinate decay rates with the session-70
covariance lemma is *false* for arbitrary `s_x` — e.g. `s_x` sending `x₀` into `x₀ᗮ` turns
the `a_t`-contraction into expansion, so `λ_i(Λ_t^x) ≤ C_x·e^{−t/ℓ}` cannot hold uniformly
(the paper's §3 polygon/HN machinery produces the correct, `s_x`-dependent rates).  What
*is* elementary and true is the **norm floor**: every image point `a_t(s_x n)` satisfies

    `‖a_t(s_x n)‖ ≥ ‖n‖/(B·e^{t/ℓ})`    (`t ≥ 0`, `‖s_x⁻¹ y‖ ≤ B·‖y‖`),

proved here as `FlowSpanSxLower.norm_ge_exp_of_shearedFlow`.  The argument: `n =
s_x⁻¹(s_x n)` (so `‖n‖ ≤ B·‖s_x n‖`), `s_x n = a_t⁻¹(a_t(s_x n))` with the inverse flow
shrinking by at most `e^{t/ℓ}` (`ModelStar.invFlow_exp_norm_le`), hence
`‖n‖ ≤ B·e^{t/ℓ}·‖a_t(s_x n)‖`, and division by `B·e^{t/ℓ} > 0`.

For an integer point `n ∈ ℤᵈ \ {0}` the norm floor combines with the **integer floor**
`norm_ge_one_of_mem_intPoints` (`1 ≤ ‖n‖` for every nonzero `n ∈ ℤᵈ`, via
`flowLattice_one_one_eq_intPoints`: the unit-scale flow lattice is `ℤᵈ`, and
`FlowLatticeMinimaLower.norm_ge_of_mem_flowLattice` gives `1 ≤ ‖n‖`).  The per-member
version `norm_ge_exp_of_mem_flowSpan_sx` (every nonzero `v ∈ Λ_t^x` has
`e^{−t/ℓ}/M ≤ ‖v‖`; `v = a_t(s_x n)` via `imageSpan_eq_map`, then integer + norm floor)
and the **assembly** `successiveMinimum_ge_exp_of_flowSpan_sx`
(`λ₁(Λ_t^x) ≥ e^{−t/ℓ}/M`, via `SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge`
with nonemptyness witnessed by the first image-basis vector,
`linearIndependent_imageBasis` + `Subsingleton`) complete (s1′-ii).

Mathlib + Submission geometry modules only.
-/

noncomputable section
open Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice
open Submission.ImageLattice

namespace Submission.FlowSpanSxLower

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Sheared-flow norm floor**: with `a_t` the exponential two-scale flow (`t ≥ 0`), for
every `n`, `‖a_t (s_x n)‖ ≥ ‖n‖/(B·e^{t/ℓ})` whenever the inverse shear shrinks by no
more than `B` (`‖s_x⁻¹ y‖ ≤ B·‖y‖`, `0 ≤ B`).  Proof: `n = s_x⁻¹(s_x n)`,
`s_x n = a_t⁻¹(a_t(s_x n))`, so `‖n‖ ≤ B·‖s_x n‖ ≤ B·e^{t/ℓ}·‖a_t(s_x n)‖`
(`hsx` + the inverse-flow norm bound `ModelStar.invFlow_exp_norm_le`), then divide by
`B·e^{t/ℓ} > 0`. -/
lemma norm_ge_exp_of_shearedFlow {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ} (ht : 0 ≤ t)
    (sx : RD d ≃ₗ[ℝ] RD d) {B : ℝ} (hB : 0 ≤ B)
    (hsx : ∀ y : RD d, ‖((sx.symm : RD d →ₗ[ℝ] RD d) y)‖ ≤ B * ‖y‖)
    (n : RD d) :
    ‖n‖ / (B * Real.exp (t / (ℓ : ℝ))) ≤
      ‖(scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (sx n)‖ := by
  classical
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : a ≠ 0 := ne_of_gt (by dsimp [a]; exact Real.exp_pos _)
  have hb0 : b ≠ 0 := ne_of_gt (by dsimp [b]; exact Real.exp_pos _)
  have hE : 0 < Real.exp (t / (ℓ : ℝ)) := Real.exp_pos _
  by_cases hB0 : B = 0
  · simp [hB0]
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    have h1 : ‖n‖ ≤ B * ‖sx n‖ := by
      calc
        ‖n‖ = ‖((sx.symm : RD d →ₗ[ℝ] RD d)) (sx n)‖ := by
              congr 1
              exact (sx.symm_apply_apply n).symm
        _ ≤ B * ‖sx n‖ := hsx (sx n)
    have hiv := Submission.ModelStar.invFlow_exp_norm_le (d := d) hℓ0 hℓd ht
      ((scaleMap (twoScale a b ℓ)) (sx n))
    have hli := Submission.ModelStar.invFlow_left_inv (d := d) a b ℓ ha0 hb0 (sx n)
    have h2 : ‖sx n‖ ≤ Real.exp (t / (ℓ : ℝ)) * ‖(scaleMap (twoScale a b ℓ)) (sx n)‖ := by
      calc
        ‖sx n‖ = ‖Submission.ModelStar.invFlow (d := d) a b ℓ ((scaleMap (twoScale a b ℓ)) (sx n))‖ := by
              rw [hli]
        _ ≤ Real.exp (t / (ℓ : ℝ)) * ‖(scaleMap (twoScale a b ℓ)) (sx n)‖ := hiv
    have hle : ‖n‖ ≤ (B * Real.exp (t / (ℓ : ℝ))) * ‖(scaleMap (twoScale a b ℓ)) (sx n)‖ := by
      calc
        ‖n‖ ≤ B * ‖sx n‖ := h1
        _ ≤ B * (Real.exp (t / (ℓ : ℝ)) * ‖(scaleMap (twoScale a b ℓ)) (sx n)‖) :=
              mul_le_mul_of_nonneg_left h2 (le_of_lt hBp)
        _ = (B * Real.exp (t / (ℓ : ℝ))) * ‖(scaleMap (twoScale a b ℓ)) (sx n)‖ := by ring
    have hpos : 0 < B * Real.exp (t / (ℓ : ℝ)) := mul_pos hBp hE
    have hmain : ‖n‖ / (B * Real.exp (t / (ℓ : ℝ))) ≤ ‖(scaleMap (twoScale a b ℓ)) (sx n)‖ :=
      (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using hle)
    simpa [a, b] using hmain

/-- With both flow scales equal to `1`, the flow lattice is the integer lattice. -/
lemma flowLattice_one_one_eq_intPoints :
    flowLattice (d := d) 1 1 0 = intPoints (d := d) := by
  classical
  have hint : intPoints (d := d) =
      Submodule.span ℤ (Set.range (fun i : Fin d => ((B d) i : RD d))) := by
    dsimp [intPoints]
  have hidx : ∀ x : RD d, scaleMap (twoScale (1 : ℝ) (1 : ℝ) 0) x = x := by
    intro x
    apply rd_ext
    intro j
    by_cases hj : j.val < (0 : ℕ)
    · simp [hj, scaleMap_apply]
    · simp [hj, scaleMap_apply]
  rw [hint]
  unfold flowLattice
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    exact (hidx ((B d) i)).symm
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    exact hidx ((B d) i)

/-- **Integer floor**: every nonzero integer point has norm at least `1`. -/
lemma norm_ge_one_of_mem_intPoints {v : RD d} (hv : v ∈ intPoints (d := d)) (hv0 : v ≠ 0) :
    (1 : ℝ) ≤ ‖v‖ := by
  have hv' : v ∈ flowLattice (d := d) 1 1 0 := by
    rwa [flowLattice_one_one_eq_intPoints]
  exact Submission.FlowLatticeMinimaLower.norm_ge_of_mem_flowLattice (d := d) (a := 1)
    (b := 1) (ℓ := 0) hv' hv0 (by norm_num) (by norm_num)

/-- **Per-member sheared norm floor**: every nonzero member `v` of the sheared flow
lattice `(a_t ∘ s_x)(ℤᵈ)` (exponential flow, `t ≥ 0`, inverse-shear bound `B`) satisfies
`e^{−t/ℓ}/B ≤ ‖v‖`.  Proof: `v = a_t(s_x n)` for an integer `n ≠ 0` (`imageSpan_eq_map`),
then `1 ≤ ‖n‖` (integer floor) and `‖a_t(s_x n)‖ ≥ ‖n‖/(B·e^{t/ℓ})` (norm floor). -/
lemma norm_ge_exp_of_mem_flowSpan_sx {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    (ht : 0 ≤ t) (sx : RD d ≃ₗ[ℝ] RD d) {B : ℝ} (hB : 0 ≤ B)
    (hsx : ∀ y : RD d, ‖((sx.symm : RD d →ₗ[ℝ] RD d) y)‖ ≤ B * ‖y‖)
    {v : RD d} (hv : v ∈ flowSpan_sx (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (ne_of_gt (Real.exp_pos _))
      (ne_of_gt (Real.exp_pos _)) sx) (hv0 : v ≠ 0) :
    Real.exp (-t / (ℓ : ℝ)) / B ≤ ‖v‖ := by
  classical
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : a ≠ 0 := ne_of_gt (by dsimp [a]; exact Real.exp_pos _)
  have hb0 : b ≠ 0 := ne_of_gt (by dsimp [b]; exact Real.exp_pos _)
  have hE : 0 < Real.exp (t / (ℓ : ℝ)) := Real.exp_pos _
  have hEneg : Real.exp (-t / (ℓ : ℝ)) = (Real.exp (t / (ℓ : ℝ)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  by_cases hB0 : B = 0
  · simp [hB0]
  · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    -- v ∈ imageSpan T with T := sx.trans (scaleMapEquiv a b ℓ ha0 hb0)
    let T : RD d ≃ₗ[ℝ] RD d := sx.trans (Submission.FlowLattice.scaleMapEquiv (d := d) a b ℓ ha0 hb0)
    have hvT : v ∈ imageSpan (d := d) T := by
      simpa [flowSpan_sx, T] using hv
    rw [imageSpan_eq_map (d := d) T] at hvT
    rcases (Submodule.mem_map).mp hvT with ⟨n, hn_int, hnv⟩
    have hnvR : (T : RD d →ₗ[ℝ] RD d) n = v := by simpa using hnv
    have hnz : n ≠ 0 := by
      intro hn0
      apply hv0
      calc
        v = (T : RD d →ₗ[ℝ] RD d) n := hnvR.symm
        _ = 0 := by rw [hn0]; simp
    have hn1 : (1 : ℝ) ≤ ‖n‖ := Submission.FlowSpanSxLower.norm_ge_one_of_mem_intPoints (d := d) hn_int hnz
    -- v = a_t(sx n)
    have hvAt : v = (scaleMap (twoScale a b ℓ)) (sx n) := by
      calc
        v = (T : RD d →ₗ[ℝ] RD d) n := hnvR.symm
        _ = (scaleMap (twoScale a b ℓ)) (sx n) := by
              dsimp [T]
              rfl
    have hfloor := norm_ge_exp_of_shearedFlow (d := d) hℓ0 hℓd ht sx hB hsx n
    -- hfloor : ‖n‖/(B·e^{t/ℓ}) ≤ ‖a_t(sx n)‖
    have hle1 : 1 / (B * Real.exp (t / (ℓ : ℝ))) ≤ ‖n‖ / (B * Real.exp (t / (ℓ : ℝ))) := by
      exact div_le_div_of_nonneg_right hn1 (le_of_lt (mul_pos hBp hE))
    have hfloor' : ‖n‖ / (B * Real.exp (t / (ℓ : ℝ))) ≤ ‖v‖ := by
      calc
        ‖n‖ / (B * Real.exp (t / (ℓ : ℝ))) ≤ ‖(scaleMap (twoScale a b ℓ)) (sx n)‖ := hfloor
        _ = ‖v‖ := by rw [← hvAt]
    have hm : Real.exp (-t / (ℓ : ℝ)) / B = 1 / (B * Real.exp (t / (ℓ : ℝ))) := by
      calc
        Real.exp (-t / (ℓ : ℝ)) / B = (Real.exp (t / (ℓ : ℝ)))⁻¹ / B := by rw [hEneg]
        _ = 1 / (B * Real.exp (t / (ℓ : ℝ))) := by
              field_simp [hB0, ne_of_gt hE]
    rw [hm]
    exact le_trans hle1 hfloor'

/-- **Assembly**: the first successive minimum of the sheared flow lattice satisfies
`λ₁(Λ_t^x) ≥ e^{−t/ℓ}/M` (exponential flow, `t ≥ 0`, inverse-shear bound `M`). -/
theorem successiveMinimum_ge_exp_of_flowSpan_sx {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d)
    {t : ℝ} (ht : 0 ≤ t) (sx : RD d ≃ₗ[ℝ] RD d) {M : ℝ} (hM : 0 ≤ M)
    (hsx : ∀ y : RD d, ‖((sx.symm : RD d →ₗ[ℝ] RD d) y)‖ ≤ M * ‖y‖) :
    Real.exp (-t / (ℓ : ℝ)) / M ≤
      Submission.SuccessiveMinima.successiveMinimum
        (flowSpan_sx (d := d) (Real.exp (-t / (ℓ : ℝ)))
          (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (ne_of_gt (Real.exp_pos _))
          (ne_of_gt (Real.exp_pos _)) sx) 1 := by
  classical
  let EA : ℝ := Real.exp (-t / (ℓ : ℝ))
  let EB : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have hd0 : 0 < d := lt_trans hℓ0 hℓd
  let L : Submodule ℤ (RD d) := flowSpan_sx (d := d) EA EB ℓ (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (Real.exp_pos _)) sx
  let T : RD d ≃ₗ[ℝ] RD d := sx.trans (Submission.FlowLattice.scaleMapEquiv (d := d) EA EB ℓ
    (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)))
  have hLdef : L = imageSpan (d := d) T := by
    rfl
  let idx0 : Fin d := ⟨0, hd0⟩
  have hLI := Submission.ImageLattice.linearIndependent_imageBasis (d := d) T
  have hmem : (imageBasis (d := d) T idx0 : RD d) ∈ L := by
    rw [hLdef]
    exact imageBasis_mem_imageSpan (d := d) T idx0
  let w0 : L := ⟨(imageBasis (d := d) T idx0 : RD d), hmem⟩
  have hlin : LinearIndependent ℤ (fun _ : Fin 1 => (w0 : RD d)) := by
    have hc := LinearIndependent.comp hLI (fun _ : Fin 1 => idx0) (by
      intro a b h
      exact Subsingleton.elim a b)
    have hfam : (fun i : Fin d => ((imageBasis (d := d) T i) : RD d)) ∘
          (fun _ : Fin 1 => idx0) =
        (fun _ : Fin 1 => ((imageBasis (d := d) T idx0) : RD d)) := by
      funext j
      rfl
    rwa [hfam] at hc
  have hS : (Submission.SuccessiveMinima.successiveMinimumSet L 1).Nonempty := by
    exact Submission.SuccessiveMinima.successiveMinimumSet_nonempty_of_exists_linearIndependent
      L 1 (f := fun _ : Fin 1 => w0) hlin ‖(w0 : RD d)‖ (fun j => le_rfl) (norm_nonneg _)
  have hge : ∀ v : L, v ≠ 0 → Real.exp (-t / (ℓ : ℝ)) / M ≤ ‖(v : RD d)‖ := by
    intro v hv0
    have hnez : (v : RD d) ≠ 0 := by
      intro hz
      apply hv0
      exact Subtype.ext hz
    exact norm_ge_exp_of_mem_flowSpan_sx (d := d) hℓ0 hℓd ht sx hM hsx v.2 hnez
  have hm : Real.exp (-t / (ℓ : ℝ)) / M ≤
      Submission.SuccessiveMinima.successiveMinimum L 1 := by
    exact Submission.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge
      L (Real.exp (-t / (ℓ : ℝ)) / M) (by norm_num : (1 : ℕ) ≤ 1) hS hge
  simpa [L, EA, EB] using hm


end Submission.FlowSpanSxLower
