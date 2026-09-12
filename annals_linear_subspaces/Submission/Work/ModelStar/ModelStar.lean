import Submission.GeometryOfNumbers.Prop5Model
import Submission.GeometryOfNumbers.ModelCone
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.GeometryOfNumbers.BlockCovering
import Submission.GeometryOfNumbers.BlockMinima
import Submission.Commons.Analysis.Real.exp_neg_div_mul_exp
import Submission.Work.ModelStar.ModelStarHeight
import Submission.GeometryOfNumbers.RationalSpan

/-!
# Model Theorem-9 assembly, first link: the ★-pair distance half at `x₀`

This module starts the model-level assembly of de Saxcé Theorem 9 (§3) in the coordinate
model — ROADMAP NEXT item (a).  The theorem's proof needs, from the §3 machinery, a
rational `k`-plane `v̲` with the correlated pair

    `d(v̲, x₀) ≤ η`   and   `H(v̲) ≤ C·η^(-k(d-ℓ)/d)`      (★)

for the same `v̲`, for `η` in the small range of the realizable contract
(`DirichletBoundSmall.conjunct1_of_dirichlet_bound_small`).  In the paper this pair comes
from the common flow-time parameterisation: at time `t`, Prop 5 produces annulus vectors
`v₁..v_k ∈ a_tℤᵈ` with `π₀`-control, and the correspondence (paper Prop 1 second point)
turns the integer preimage tensor into the rational plane with
`d ≲ e^{-t(1/ℓ+1/(d-ℓ))}` and `H ≲ e^{t·k/ℓ}`.

This module proves the **distance half** of the model pair at the coordinate plane
`x₀ = modelX ℓ` — the full Prop-5 → cone-condition → distance chain — as
`ModelStar.modelStar_distance`.  Along the way it records the reusable glue:

* `invFlow` / `invFlow_left_inv` / `preimage_mem_intPoints` /
  `exists_preimage_family` — every flow-lattice vector has an **integer preimage** under
  the inverse two-scale flow (`flowLattice a b ℓ = map f ℤᵈ`, `flowLattice_eq_map`), and
  a flow-lattice family lifts to an integer family `m` with `f(m i) = v i`;
* `contractDir` / `contractDir_mem_blockSpan` / `contractDir_orthonormal` — the explicit
  Lemma-5 directions (first `k` standard vectors) in the contracting block `blockSpan ℓ`,
  feeding `BlockCovering.exists_blockFamily_annulus_exp`;
* the π₀-control of the annulus wedge
  (`wedgeContract_blockAnnulus_lower` + wedge ≤ product), wedge positivity ⟹
  `LinearIndependent` of the ambient family (converse of
  `iMulti_ne_zero_of_linearIndependent`, via `AlternatingMap.map_linearDependent`), and the
  transfer of independence to the preimages (`LinearIndependent.of_comp` through the
  injective flow);
* the **cone condition**: the Prop-5 π₀-control IS the block-0 dominance hypothesis of
  `ModelCone.model_prop1_part2` after unwinding the flow through
  `exteriorPower.map_apply_ιMulti` (`map k f (ιMulti m) = ιMulti (f∘m)`) and
  `WedgeContract.pi0_apply` (`π₀ w = blockElem w 0`);
* the exponent rewrite to the paper denominator `1/(d−ℓ)` via
  `Commons.Analysis.Real.exp_neg_div_mul_exp`.

Output: `modelStar_distance` — for `0 < k ≤ ℓ < d`, `k ≤ 4` (the short-tensor range of the
model Prop 5) and **every** real `t`, there is a `k`-plane `V` (the span of the integer
preimages `m`) with `finrank = k` and

    `distSubspaces V (modelX ℓ) ≤ (1/(1−k/5)) · e^{−t·(1/ℓ + 1/(d−ℓ))}`

(the bound tends to `0` as `t → ∞`, at the paper's rate; no `t > 0` hypothesis is needed —
`a = e^{-t/ℓ} > 0` and the block-annulus machinery work for every real `t`).

The height half is developed in `ModelStarHeight` (`height_le_norm_iMulti_of_mem_imageLattice`,
`height_le_span_intPoints`) and this file now carries its norm input (a1-iii, first
lemmas): the diagonal-map norm bound `scaleMap_norm_le`, the inverse-flow coefficient and
norm bounds for the exponential flow at `t ≥ 0` (`invFlow_coeff_bound_exp`,
`invFlow_exp_norm_le`), and the **annulus preimage estimate**
`preimage_norm_le_of_annulus_exp`: the integer preimages `m i = a_t^{-1}(v i)` of an
annulus family (`‖v i‖ ≤ 12·ℓ·e^{−t/ℓ}`) satisfy `‖m i‖ ≤ 12·(ℓ:ℝ)` — the input to the
★-pair height bound `height V ≤ (12·ℓ)^k ≤ (12·ℓ)^k·e^{t·k/ℓ}`.  Still open: assembling
the ★-pair theorem from `modelStar_distance` + the height bound, and the general-`x`
(s_x) conjugation.

All problem-side code is under `Submission/`; Mathlib + Submission geometry modules only.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real LinearSubspaces
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice
open Submission.BlockCovering
open Submission.WedgeBlocks
open Submission.WedgeContract
open Submission.BlockMinima

namespace Submission.ModelStar

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The inverse two-scale flow (reciprocal coefficients). -/
noncomputable def invFlow (a b : ℝ) (ℓ : ℕ) : ℝᵈ →ₗ[ℝ] ℝᵈ :=
  scaleMap (fun i : Fin d => (twoScale a b ℓ i)⁻¹)

/-- `invFlow` left-inverts the flow. -/
lemma invFlow_left_inv (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝᵈ) :
    invFlow a b ℓ ((scaleMap (twoScale a b ℓ)) x) = x := by
  have hcomp := scaleMap_twoScale_left_inv (d := d) a b ℓ ha hb
  have hc := congrArg (fun (φ : ℝᵈ →ₗ[ℝ] ℝᵈ) => φ x) hcomp
  simpa [invFlow] using hc

/-- The preimage of a flow-lattice vector under the flow is an integer point. -/
lemma preimage_mem_intPoints (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    {y : ℝᵈ} (hy : y ∈ flowLattice (d := d) a b ℓ) :
    invFlow a b ℓ y ∈ intPoints (d := d) := by
  classical
  rw [flowLattice_eq_map (d := d) a b ℓ] at hy
  rcases (Submodule.mem_map).mp hy with ⟨x, hx, hxy⟩
  have hxy' : (scaleMap (twoScale a b ℓ)) x = y := by
    simpa using hxy
  have hpre : invFlow a b ℓ y = x := by
    rw [← hxy']
    exact invFlow_left_inv a b ℓ ha hb x
  rwa [hpre]

/-- An integer-preimage family of a flow-lattice family. -/
lemma exists_preimage_family (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) {k : ℕ}
    (v : Fin k → flowLattice (d := d) a b ℓ) :
    ∃ m : Fin k → ℝᵈ, (∀ i : Fin k, m i ∈ intPoints (d := d)) ∧
      ∀ i : Fin k, (scaleMap (twoScale a b ℓ)) (m i) = (v i : ℝᵈ) := by
  classical
  refine ⟨fun i => invFlow a b ℓ (v i : ℝᵈ), ?_, ?_⟩
  · intro i
    exact preimage_mem_intPoints a b ℓ ha hb (v i).2
  · intro i
    have hcomp := scaleMap_twoScale_right_inv (d := d) a b ℓ ha hb
    have hc := congrArg (fun (φ : ℝᵈ →ₗ[ℝ] ℝᵈ) => φ ((v i : ℝᵈ))) hcomp
    simpa [invFlow] using hc

/-- The first `k ≤ ℓ` contracting-block directions `e₀,…,eₖ₋₁`. -/
noncomputable def contractDir {k ℓ : ℕ} (hℓd : ℓ ≤ d) (hkl : k ≤ ℓ) (i : Fin k) : ℝᵈ :=
  (B d) (Fin.castLE (le_trans hkl hℓd) i)

/-- The contracting directions lie in the block's real span `blockSpan ℓ`. -/
lemma contractDir_mem_blockSpan {k ℓ : ℕ} (hℓd : ℓ ≤ d) (hkl : k ≤ ℓ) (i : Fin k) :
    contractDir (d := d) hℓd hkl i ∈ blockSpan (d := d) ℓ := by
  classical
  have hval : (Fin.castLE (le_trans hkl hℓd) i).val = i.val := rfl
  have hlt : i.val < ℓ := lt_of_lt_of_le i.isLt hkl
  let j : {j : Fin d // j.val < ℓ} := ⟨Fin.castLE (le_trans hkl hℓd) i, by simpa [hval] using hlt⟩
  have heq : contractDir (d := d) hℓd hkl i = blockAmb (d := d) (ℓ := ℓ) j := by
    dsimp [contractDir, blockAmb, j]
  rw [heq]
  exact Submodule.subset_span ⟨j, rfl⟩

/-- The contracting directions form an orthonormal family. -/
lemma contractDir_orthonormal {k ℓ : ℕ} (hℓd : ℓ ≤ d) (hkl : k ≤ ℓ) :
    Orthonormal ℝ (contractDir (d := d) hℓd hkl) := by
  unfold contractDir
  exact Orthonormal.comp (B d).orthonormal (Fin.castLE (le_trans hkl hℓd))
    (Fin.castLE_injective (le_trans hkl hℓd))

/-- **Model Theorem 9, distance half**: with `0 < k ≤ ℓ < d` and `k ≤ 4` (the short-tensor
range of the model Prop 5), the Prop-5 annulus construction in the exponential flow at
time `t` yields a `k`-plane whose distance to the coordinate `ℓ`-plane `x₀ = modelX ℓ` is
at most `(1/(1−k/5))·e^{−t(1/ℓ+1/(d−ℓ))}` (valid for every real `t`; the bound tends to
`0` as `t → ∞`). -/
theorem modelStar_distance {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hkl : k ≤ ℓ) {t : ℝ} :
    ∃ V : Submodule ℝ ℝᵈ, Module.finrank ℝ V = k ∧
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤
        (1 / (1 - (k : ℝ) / 5)) *
          Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
  classical
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : 0 < a := by dsimp [a]; exact Real.exp_pos _
  have hb0 : 0 < b := by dsimp [b]; exact Real.exp_pos _
  have ha0' : a ≠ 0 := ne_of_gt ha0
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have hℓd' : ℓ ≤ d := le_of_lt hℓd
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  let c : ℝ := 1 - (k : ℝ) / 5
  have hc0 : 0 < c := by
    dsimp [c]
    have hk4R : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
    nlinarith
  -- (0) explicit Lemma-5 directions: the first k standard vectors
  let u : Fin k → ℝᵈ := contractDir (d := d) hℓd' hkl
  have hu_mem : ∀ i, u i ∈ blockSpan (d := d) ℓ := fun i =>
    contractDir_mem_blockSpan (d := d) hℓd' hkl i
  have huON : Orthonormal ℝ u := by
    dsimp [u]
    exact contractDir_orthonormal (d := d) hℓd' hkl
  have hu1 : ∀ i, ‖u i‖ = 1 := fun i => (huON.1 i)
  -- (1) annulus family w : Fin k → smallFlow in the contracting sublattice
  obtain ⟨w, hwann⟩ := exists_blockFamily_annulus_exp (d := d) ℓ hℓd (u := u) hu_mem hu1
  -- (2) π₀ control and positivity on the annulus wedge
  have hv0 : ∀ i : Fin k, 0 < ‖(w i : ℝᵈ)‖ := by
    intro i
    have hlo : (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(w i : ℝᵈ)‖ := by
      simpa [a] using (hwann i).2.1
    have h10 : 0 < (10 : ℝ) * (ℓ : ℝ) * a := by positivity
    exact lt_of_lt_of_le h10 hlo
  have hprod0 : 0 < (∏ i : Fin k, ‖(w i : ℝᵈ)‖) := Finset.prod_pos (fun i hi => hv0 i)
  have hlower := wedgeContract_blockAnnulus_lower (d := d) (k := k) ℓ hℓd' (a := a) (b := b)
    ha0 hℓ0 u hu_mem huON hk0 w hwann
  have hpi0pos : 0 < ‖pi0 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 hc0) hlower
  have hupw := norm_pi0_le (d := d) (k := k) ℓ
    (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))
  have hwpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ :=
    lt_of_lt_of_le hpi0pos hupw
  -- (3) lift to the full flow lattice
  let v : Fin k → flowLattice (d := d) a b ℓ := fun i =>
    ⟨(w i : ℝᵈ), (smallFlow_le_flowLattice (d := d) a b ℓ hℓd') (w i).2⟩
  have hlow : c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
      ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
    have hle : ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
        (∏ i : Fin k, ‖(v i : ℝᵈ)‖) :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
        (fun i : Fin k => (v i : ℝᵈ))
    have h1m : 0 ≤ c := le_of_lt hc0
    calc
      c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖
          ≤ c * (∏ i : Fin k, ‖(v i : ℝᵈ)‖) := mul_le_mul_of_nonneg_left hle h1m
      _ = (∏ i : Fin k, ‖(v i : ℝᵈ)‖) * (1 - (k : ℝ) / 5) := by dsimp [c]; rw [mul_comm]
      _ ≤ ‖pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
            simpa [v] using hlower
  have hvpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ := by
    have hpi0pos_v : 0 < ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
      simpa [v] using hpi0pos
    have hupv := norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))
    exact lt_of_lt_of_le hpi0pos_v hupv
  have hvine : exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) ≠ 0 :=
    norm_pos_iff.mp hvpos
  have hLIv : LinearIndependent ℝ (fun i : Fin k => (v i : ℝᵈ)) := by
    by_contra h
    exact hvine (AlternatingMap.map_linearDependent (f := exteriorPower.ιMulti ℝ k)
      (fun i : Fin k => (v i : ℝᵈ)) h)
  -- (4) integer preimage family m : f(m i) = (v i)
  obtain ⟨m, _hm_int, hm_eq⟩ := exists_preimage_family (d := d) a b ℓ ha0' hb0' v
  have hLIv' : LinearIndependent ℝ (fun i : Fin k => scaleMap (twoScale a b ℓ) (m i)) := by
    convert hLIv using 1
    funext i
    exact hm_eq i
  have hLIm : LinearIndependent ℝ m :=
    LinearIndependent.of_comp (scaleMap (twoScale a b ℓ)) hLIv'
  -- (5) the cone condition (π₀ control = block-0 dominance after unwinding the flow)
  have hfk : exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m) =
      exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) := by
    rw [exteriorPower.map_apply_ιMulti (f := scaleMap (twoScale a b ℓ)) (m := m)]
    congr 1
    funext i
    exact hm_eq i
  have hcone : c * ‖exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m)‖ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ))
          (exteriorPower.ιMulti ℝ k m)) 0‖ := by
    rw [hfk]
    rw [← pi0_apply (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))]
    exact hlow
  -- (6) the model Prop-1-part-2 distance bound (arbitrary two-scale parameters)
  have hmain := Submission.ModelCone.model_prop1_part2 (d := d) (k := k) ℓ hk0 hkl hℓ0 hℓd' m
    hLIm a b c ha0 hb0 hc0 hcone
  -- (7) exponent rewrite to the paper's `1/(d−ℓ)` denominator
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  have hm : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hb_eq : b = Real.exp (t / ((d - ℓ : ℕ) : ℝ)) := by
    dsimp [b]
    congr 1
    rw [Nat.cast_sub (le_of_lt hℓd)]
  have hA : a / (c * b) = (1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) +
      (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
    rw [hb_eq]
    dsimp [a]
    exact Commons.Analysis.Real.exp_neg_div_mul_exp (t := t) (ℓ := (ℓ : ℝ))
      (m := ((d - ℓ : ℕ) : ℝ)) (c := c) hℓR hm (ne_of_gt hc0)
  refine ⟨Submodule.span ℝ (Set.range m), ?_, ?_⟩
  · exact PlaneFinrank.finrank_span_range (d := d) m hLIm
  · calc
      LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) (modelX (d := d) ℓ)
          ≤ a / (c * b) := hmain
      _ = (1 / (1 - (k : ℝ) / 5)) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) +
            (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
            simpa [c] using hA


/-- diagonal map norm bound: `‖scaleMap s x‖ ≤ M·‖x‖` when `|s i| ≤ M`, `0 ≤ M`. -/
lemma scaleMap_norm_le (s : Fin d → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ i : Fin d, |s i| ≤ M) (x : ℝᵈ) : ‖scaleMap s x‖ ≤ M * ‖x‖ := by
  have h1 : ‖scaleMap s x‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
    calc
      ‖scaleMap s x‖ ^ 2 = ∑ i : Fin d, ((scaleMap s x) i) ^ 2 := by
            exact EuclideanSpace.real_norm_sq_eq (scaleMap s x)
      _ = ∑ i : Fin d, (s i * x i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [scaleMap_apply]
      _ ≤ ∑ i : Fin d, M ^ 2 * (x i) ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hs' : (s i) ^ 2 ≤ M ^ 2 := by
              have h := (sq_le_sq₀ (abs_nonneg (s i)) hM).mpr (hs i)
              rwa [sq_abs] at h
            calc
              (s i * x i) ^ 2 = (s i) ^ 2 * (x i) ^ 2 := by rw [mul_pow]
              _ ≤ M ^ 2 * (x i) ^ 2 := mul_le_mul_of_nonneg_right hs' (sq_nonneg (x i))
      _ = M ^ 2 * (∑ i : Fin d, (x i) ^ 2) := by
            rw [Finset.mul_sum]
      _ = M ^ 2 * ‖x‖ ^ 2 := by
            rw [EuclideanSpace.real_norm_sq_eq x]
  have h1' : ‖scaleMap s x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rwa [mul_pow]
  exact (sq_le_sq₀ (norm_nonneg (scaleMap s x)) (mul_nonneg hM (norm_nonneg x))).mp h1'

/-- exp-flow notation: `a = exp(-t/ℓ)` on the block, `b = exp(t/(d−ℓ))` outside. -/
lemma exp_twoScale_apply_lt (ℓ : ℕ) (t : ℝ) (i : Fin d) (hi : i.val < ℓ) :
    twoScale (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ i =
      Real.exp (-t / (ℓ : ℝ)) := by
  rw [twoScale_apply]
  simp [hi]

lemma exp_twoScale_apply_ge (ℓ : ℕ) (t : ℝ) (i : Fin d) (hi : ¬ i.val < ℓ) :
    twoScale (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ i =
      Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  rw [twoScale_apply]
  simp [hi]

/-- coefficient bound of the inverse exp flow: every `|(twoScale … i)⁻¹| ≤ exp(t/ℓ)`
(for `t ≥ 0`; the contracting directions recover `e^{t/ℓ}`, the expanding ones give
`e^{−t/(d−ℓ)} ≤ 1 ≤ e^{t/ℓ}`). -/
lemma invFlow_coeff_bound_exp {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ} (ht : 0 ≤ t) :
    ∀ i : Fin d,
      |((twoScale (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ i)⁻¹)| ≤
        Real.exp (t / (ℓ : ℝ)) := by
  intro i
  by_cases hi : i.val < ℓ
  · rw [exp_twoScale_apply_lt ℓ t i hi]
    have hc : (Real.exp (-t / (ℓ : ℝ)))⁻¹ = Real.exp (t / (ℓ : ℝ)) := by
      calc
        (Real.exp (-t / (ℓ : ℝ)))⁻¹ = (Real.exp (-(t / (ℓ : ℝ))))⁻¹ := by congr 1; ring_nf
        _ = Real.exp (t / (ℓ : ℝ)) := by
              rw [Real.exp_neg]
              simp
    rw [hc, abs_of_pos (Real.exp_pos _)]
  · rw [exp_twoScale_apply_ge ℓ t i hi]
    have hc : (Real.exp (t / ((d : ℝ) - (ℓ : ℝ))))⁻¹ =
        Real.exp (-t / ((d : ℝ) - (ℓ : ℝ))) := by
      rw [← Real.exp_neg (t / ((d : ℝ) - (ℓ : ℝ)))]
      congr 1
      ring_nf
    rw [hc]
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by
      have hdR : 0 < (d : ℝ) - (ℓ : ℝ) := by
        rw [← Nat.cast_sub (le_of_lt hℓd)]
        exact_mod_cast (Nat.sub_pos_of_lt hℓd)
      have hℓR : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ0
      have htd : 0 ≤ t * (d : ℝ) := mul_nonneg ht (Nat.cast_nonneg d)
      rw [div_le_iff₀ hdR]
      rw [div_mul_eq_mul_div]
      rw [le_div_iff₀ hℓR]
      nlinarith)

/-- norm bound for the inverse exp flow: `‖invFlow a b ℓ x‖ ≤ exp(t/ℓ)·‖x‖` (`t ≥ 0`). -/
lemma invFlow_exp_norm_le {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ} (ht : 0 ≤ t) (x : ℝᵈ) :
    ‖invFlow (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ x‖ ≤
      Real.exp (t / (ℓ : ℝ)) * ‖x‖ := by
  dsimp [invFlow]
  exact scaleMap_norm_le (fun i : Fin d => (twoScale (Real.exp (-t / (ℓ : ℝ)))
    (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ i)⁻¹) (le_of_lt (Real.exp_pos _))
    (invFlow_coeff_bound_exp (d := d) hℓ0 hℓd ht) x


/-- **Annulus preimage estimate**: the integer preimages `m` of an annulus family
`v ∈ flowLattice` (exp flow, `t ≥ 0`, `‖v i‖ ≤ 12·ℓ·e^{−t/ℓ}`) have bounded norm:
`‖m i‖ ≤ 12·(ℓ:ℝ)`.  Proof: `m i = invFlow (v i)` (the flow left-inverse), the inverse
flow shrinks by at most `e^{t/ℓ}` (`invFlow_exp_norm_le`), and
`e^{t/ℓ}·12·ℓ·e^{−t/ℓ} = 12·ℓ`. -/
lemma preimage_norm_le_of_annulus_exp {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ}
    (v : Fin k → flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (m : Fin k → ℝᵈ)
    (hm_eq : ∀ i, (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (m i) = (v i : ℝᵈ))
    (hvann : ∀ i, ‖(v i : ℝᵈ)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :
    ∀ i, ‖m i‖ ≤ (12 : ℝ) * (ℓ : ℝ) := by
  intro i
  have hli := invFlow_left_inv (d := d) (Real.exp (-t / (ℓ : ℝ)))
    (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (Real.exp_pos _)) (m i)
  have hm : m i = invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (v i : ℝᵈ) := by
    calc
      m i = invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
            (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ
            ((scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
              (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (m i)) := hli.symm
      _ = invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
            (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (v i : ℝᵈ) := by rw [hm_eq i]
  have hn := invFlow_exp_norm_le (d := d) hℓ0 hℓd ht (v i : ℝᵈ)
  have he : Real.exp (t / (ℓ : ℝ)) * Real.exp (-t / (ℓ : ℝ)) = 1 := by
    rw [← Real.exp_add]
    have harg : t / (ℓ : ℝ) + -t / (ℓ : ℝ) = 0 := by ring
    rw [harg, Real.exp_zero]
  calc
    ‖m i‖ = ‖invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
          (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (v i : ℝᵈ)‖ := by rw [hm]
    _ ≤ Real.exp (t / (ℓ : ℝ)) * ‖(v i : ℝᵈ)‖ := hn
    _ ≤ Real.exp (t / (ℓ : ℝ)) * ((12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :=
          mul_le_mul_of_nonneg_left (hvann i) (le_of_lt (Real.exp_pos _))
    _ = (12 : ℝ) * (ℓ : ℝ) := by
          calc
            Real.exp (t / (ℓ : ℝ)) * ((12 : ℝ) * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)))
                = (12 : ℝ) * (ℓ : ℝ) *
                    (Real.exp (t / (ℓ : ℝ)) * Real.exp (-t / (ℓ : ℝ))) := by ring
            _ = (12 : ℝ) * (ℓ : ℝ) := by rw [he]; ring

/-- **Model Theorem 9, ★-pair**: for `0 < k ≤ ℓ < d`, `k ≤ 4`, `t ≥ 0`, the Prop-5
annulus construction yields a rational `k`-plane `V` with the correlated pair
`distSubspaces V (modelX ℓ) ≤ (1/(1−k/5))·e^{−t(1/ℓ+1/(d−ℓ))}` and
`height V ≤ (12·ℓ)^k·e^{t·k/ℓ}` (the model ★-pair: both bounds on the same plane). -/
theorem modelStar_pair {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hkl : k ≤ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ V : Submodule ℝ ℝᵈ, ∃ hV : IsRational V,
      Module.finrank ℝ V = k ∧
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤
        (1 / (1 - (k : ℝ) / 5)) *
          Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) ∧
      LinearSubspaces.height V hV ≤
        ((12 : ℝ) * (ℓ : ℝ)) ^ k * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
  classical
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : 0 < a := by dsimp [a]; exact Real.exp_pos _
  have hb0 : 0 < b := by dsimp [b]; exact Real.exp_pos _
  have ha0' : a ≠ 0 := ne_of_gt ha0
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have hℓd' : ℓ ≤ d := le_of_lt hℓd
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  let c : ℝ := 1 - (k : ℝ) / 5
  have hc0 : 0 < c := by
    dsimp [c]
    have hk4R : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
    nlinarith
  -- (0) explicit Lemma-5 directions
  let u : Fin k → ℝᵈ := contractDir (d := d) hℓd' hkl
  have hu_mem : ∀ i, u i ∈ blockSpan (d := d) ℓ := fun i =>
    contractDir_mem_blockSpan (d := d) hℓd' hkl i
  have huON : Orthonormal ℝ u := by
    dsimp [u]
    exact contractDir_orthonormal (d := d) hℓd' hkl
  have hu1 : ∀ i, ‖u i‖ = 1 := fun i => (huON.1 i)
  -- (1) annulus family w : Fin k → smallFlow
  obtain ⟨w, hwann⟩ := exists_blockFamily_annulus_exp (d := d) ℓ hℓd (u := u) hu_mem hu1
  -- (2) π₀ control and positivity on the annulus wedge
  have hv0 : ∀ i : Fin k, 0 < ‖(w i : ℝᵈ)‖ := by
    intro i
    have hlo : (10 : ℝ) * (ℓ : ℝ) * a ≤ ‖(w i : ℝᵈ)‖ := by
      simpa [a] using (hwann i).2.1
    have h10 : 0 < (10 : ℝ) * (ℓ : ℝ) * a := by positivity
    exact lt_of_lt_of_le h10 hlo
  have hprod0 : 0 < (∏ i : Fin k, ‖(w i : ℝᵈ)‖) := Finset.prod_pos (fun i hi => hv0 i)
  have hlower := wedgeContract_blockAnnulus_lower (d := d) (k := k) ℓ hℓd' (a := a) (b := b)
    ha0 hℓ0 u hu_mem huON hk0 w hwann
  have hpi0pos : 0 < ‖pi0 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 hc0) hlower
  have hupw := norm_pi0_le (d := d) (k := k) ℓ
    (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))
  have hwpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ :=
    lt_of_lt_of_le hpi0pos hupw
  -- (3) lift to the full flow lattice
  let v : Fin k → flowLattice (d := d) a b ℓ := fun i =>
    ⟨(w i : ℝᵈ), (smallFlow_le_flowLattice (d := d) a b ℓ hℓd') (w i).2⟩
  have hlow : c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
      ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
    have hle : ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
        (∏ i : Fin k, ‖(v i : ℝᵈ)‖) :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
        (fun i : Fin k => (v i : ℝᵈ))
    have h1m : 0 ≤ c := le_of_lt hc0
    calc
      c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖
          ≤ c * (∏ i : Fin k, ‖(v i : ℝᵈ)‖) := mul_le_mul_of_nonneg_left hle h1m
      _ = (∏ i : Fin k, ‖(v i : ℝᵈ)‖) * (1 - (k : ℝ) / 5) := by dsimp [c]; rw [mul_comm]
      _ ≤ ‖pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
            simpa [v] using hlower
  have hvpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ := by
    have hpi0pos_v : 0 < ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
      simpa [v] using hpi0pos
    have hupv := norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))
    exact lt_of_lt_of_le hpi0pos_v hupv
  have hvine : exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) ≠ 0 :=
    norm_pos_iff.mp hvpos
  have hLIv : LinearIndependent ℝ (fun i : Fin k => (v i : ℝᵈ)) := by
    by_contra h
    exact hvine (AlternatingMap.map_linearDependent (f := exteriorPower.ιMulti ℝ k)
      (fun i : Fin k => (v i : ℝᵈ)) h)
  -- (4) integer preimage family m : f(m i) = (v i)
  obtain ⟨m, hm_int, hm_eq⟩ := exists_preimage_family (d := d) a b ℓ ha0' hb0' v
  have hLIv' : LinearIndependent ℝ (fun i : Fin k => scaleMap (twoScale a b ℓ) (m i)) := by
    convert hLIv using 1
    funext i
    exact hm_eq i
  have hLIm : LinearIndependent ℝ m :=
    LinearIndependent.of_comp (scaleMap (twoScale a b ℓ)) hLIv'
  -- (5) the cone condition
  have hfk : exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m) =
      exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) := by
    rw [exteriorPower.map_apply_ιMulti (f := scaleMap (twoScale a b ℓ)) (m := m)]
    congr 1
    funext i
    exact hm_eq i
  have hcone : c * ‖exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m)‖ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ))
          (exteriorPower.ιMulti ℝ k m)) 0‖ := by
    rw [hfk]
    rw [← pi0_apply (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))]
    exact hlow
  -- (6) distance bound (arbitrary two-scale parameters)
  have hmain := Submission.ModelCone.model_prop1_part2 (d := d) (k := k) ℓ hk0 hkl hℓ0 hℓd' m
    hLIm a b c ha0 hb0 hc0 hcone
  -- (7) exponent rewrite
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  have hm : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hb_eq : b = Real.exp (t / ((d - ℓ : ℕ) : ℝ)) := by
    dsimp [b]
    congr 1
    rw [Nat.cast_sub (le_of_lt hℓd)]
  have hA : a / (c * b) = (1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) +
      (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
    rw [hb_eq]
    dsimp [a]
    exact Commons.Analysis.Real.exp_neg_div_mul_exp (t := t) (ℓ := (ℓ : ℝ))
      (m := ((d - ℓ : ℕ) : ℝ)) (c := c) hℓR hm (ne_of_gt hc0)
  -- (8) annulus preimage estimate ‖m i‖ ≤ 12·(ℓ:ℝ)
  have hvann : ∀ i, ‖(v i : ℝᵈ)‖ ≤ (12 : ℝ) * (ℓ : ℝ) * a := by
    intro i
    simpa [v, a] using (hwann i).2.2
  have hm_pre : ∀ i, ‖m i‖ ≤ (12 : ℝ) * (ℓ : ℝ) :=
    preimage_norm_le_of_annulus_exp (d := d) hℓ0 hℓd ht v m hm_eq hvann
  -- (9) height bound: height V ≤ (12·ℓ)^k ≤ (12·ℓ)^k·e^{t·k/ℓ}
  let V : Submodule ℝ ℝᵈ := Submodule.span ℝ (Set.range m)
  have hV : IsRational V := by
    dsimp [V]
    exact Submission.RationalSpan.isRational_span_of_mem_intPoints (d := d) m hm_int
  have hfinV : Module.finrank ℝ V = k := by
    dsimp [V]
    exact PlaneFinrank.finrank_span_range (d := d) m hLIm
  let uu : Fin (Module.finrank ℝ V) → ℝᵈ := fun i => m (Fin.cast hfinV i)
  have hu_mem_uu : ∀ j, uu j ∈ Submission.Heights.imageLattice (d := d) V := by
    intro j
    apply Submission.ModelStarHeight.mem_imageLattice_of_mem V
    · dsimp [uu, V]
      exact Submodule.subset_span ⟨Fin.cast hfinV j, rfl⟩
    · dsimp [uu]
      exact hm_int (Fin.cast hfinV j)
  have hu_li_uu : LinearIndependent ℝ uu := by
    dsimp [uu]
    exact LinearIndependent.comp hLIm (Fin.cast hfinV) (Fin.cast_injective hfinV)
  have hH := Submission.ModelStarHeight.height_le_norm_iMulti_of_mem_imageLattice (d := d) V hV
    uu hu_mem_uu hu_li_uu
  have hprod_le : (∏ i : Fin (Module.finrank ℝ V), ‖uu i‖) ≤
      ((12 : ℝ) * (ℓ : ℝ)) ^ Module.finrank ℝ V := by
    calc
      (∏ i : Fin (Module.finrank ℝ V), ‖uu i‖)
          ≤ ∏ _i : Fin (Module.finrank ℝ V), (12 : ℝ) * (ℓ : ℝ) := by
            exact Finset.prod_le_prod (s := Finset.univ)
              (f := fun i : Fin (Module.finrank ℝ V) => ‖uu i‖)
              (g := fun _ : Fin (Module.finrank ℝ V) => (12 : ℝ) * (ℓ : ℝ))
              (by intro i hi; exact norm_nonneg _)
              (by intro i hi; calc
                  ‖uu i‖ = ‖m (Fin.cast hfinV i)‖ := by dsimp [uu]
                  _ ≤ (12 : ℝ) * (ℓ : ℝ) := hm_pre (Fin.cast hfinV i))
      _ = ((12 : ℝ) * (ℓ : ℝ)) ^ Module.finrank ℝ V := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hHfin : LinearSubspaces.height V hV ≤ ((12 : ℝ) * (ℓ : ℝ)) ^ k := by
    calc
      LinearSubspaces.height V hV
          ≤ ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) uu‖ := hH
      _ ≤ (∏ i : Fin (Module.finrank ℝ V), ‖uu i‖) :=
            Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod uu
      _ ≤ ((12 : ℝ) * (ℓ : ℝ)) ^ Module.finrank ℝ V := hprod_le
      _ = ((12 : ℝ) * (ℓ : ℝ)) ^ k := by rw [hfinV]
  have hC0 : 0 ≤ ((12 : ℝ) * (ℓ : ℝ)) ^ k := pow_nonneg (by positivity) k
  have hCkpos : 0 < ((12 : ℝ) * (ℓ : ℝ)) ^ k := pow_pos (by positivity) k
  have he1 : 1 ≤ Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
    apply Real.one_le_exp
    have hℓR' : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ0
    exact mul_nonneg ht (div_nonneg (Nat.cast_nonneg k) (le_of_lt hℓR'))
  have hHexp : LinearSubspaces.height V hV ≤
      ((12 : ℝ) * (ℓ : ℝ)) ^ k * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
    calc
      LinearSubspaces.height V hV ≤ ((12 : ℝ) * (ℓ : ℝ)) ^ k := hHfin
      _ ≤ ((12 : ℝ) * (ℓ : ℝ)) ^ k * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
            simpa [mul_comm] using (mul_le_mul_of_nonneg_right he1 hC0)
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · exact hfinV
  · dsimp [V]
    calc
      LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) (modelX (d := d) ℓ)
          ≤ a / (c * b) := hmain
      _ = (1 / (1 - (k : ℝ) / 5)) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) +
            (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
            simpa [c] using hA
  · dsimp [V]
    exact hHexp

/-- ★-form identity: `(12·ℓ)^k·e^{t·k/ℓ} = (12·ℓ)^k·c^{−α}·η^{−α}` for
`η := (1/c)·e^{−t·S}`, `S := 1/ℓ + 1/(d−ℓ)`, `α := k·(d−ℓ)/d` (used by the ★-pair
corollary `modelStar_pair_star`). -/
lemma star_form_height_identity {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ}
    (c : ℝ) (hc : 0 < c) (t : ℝ) :
    ((12 : ℝ) * (ℓ : ℝ)) ^ k * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) =
      ((12 : ℝ) * (ℓ : ℝ)) ^ k * c ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
        ((1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
          (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
  classical
  let α : ℝ := ((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ)
  let S : ℝ := (1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)
  let A : ℝ := ((12 : ℝ) * (ℓ : ℝ)) ^ k
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le hℓ0 (le_of_lt hℓd)))
  have hdℓ : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hcast : (d : ℝ) - (ℓ : ℝ) = ((d - ℓ : ℕ) : ℝ) := by
    rw [← Nat.cast_sub (le_of_lt hℓd)]
  have hE : 0 < Real.exp (-t * S) := Real.exp_pos _
  have hc1 : 0 < 1 / c := one_div_pos.mpr hc
  have hSα : S * α = (k : ℝ) / (ℓ : ℝ) := by
    dsimp [S, α]
    rw [hcast]
    have hsub : ((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ) = (d : ℝ) := by
      rw [← Nat.cast_add]
      congr 1
      exact Nat.sub_add_cancel (le_of_lt hℓd)
    field_simp [hdR, hℓR, hdℓ]
    nlinarith
  have hEpow : (Real.exp (-t * S)) ^ (-α) = Real.exp (t * (S * α)) := by
    rw [Real.rpow_def_of_pos hE (-α)]
    rw [Real.log_exp]
    congr 1
    ring_nf
  have hηpow : ((1 / c) * Real.exp (-t * S)) ^ (-α) =
      (1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α) := by
    exact Real.mul_rpow (z := -α) (le_of_lt hc1) (le_of_lt hE)
  have hcomb : c ^ (-α) * (1 / c) ^ (-α) = 1 := by
    have hm := Real.mul_rpow (z := -α) (le_of_lt hc) (le_of_lt hc1)
    rw [← hm]
    have h1 : c * (1 / c) = 1 := by field_simp [ne_of_gt hc]
    rw [h1, Real.one_rpow]
  calc
    A * Real.exp (t * ((k : ℝ) / (ℓ : ℝ)))
        = A * Real.exp (t * (S * α)) := by rw [hSα]
    _ = A * (Real.exp (-t * S)) ^ (-α) := by rw [← hEpow]
    _ = A * c ^ (-α) * (1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α) := by
          have h := congrArg (fun r : ℝ => A * r * (Real.exp (-t * S)) ^ (-α)) hcomb.symm
          -- hcomb.symm : 1 = c^{-α}·(1/c)^{-α} ; h : A·1·E = A·(c^{-α}(1/c)^{-α})·E
          calc
            A * (Real.exp (-t * S)) ^ (-α)
                = A * 1 * (Real.exp (-t * S)) ^ (-α) := by ring
            _ = A * (c ^ (-α) * (1 / c) ^ (-α)) * (Real.exp (-t * S)) ^ (-α) := h
            _ = A * c ^ (-α) * (1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α) := by ring
    _ = A * c ^ (-α) * ((1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α)) := by ring
    _ = A * c ^ (-α) * ((1 / c) * Real.exp (-t * S)) ^ (-α) := by
          rw [← hηpow]
    _ = ((12 : ℝ) * (ℓ : ℝ)) ^ k * c ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
          dsimp [A, α, S]



/-- **Model Theorem 9, ★-shape**: the `modelStar_pair` bound in the exact correlated form
used by the small-`η` Dirichlet contract: with `η := (1/(1−k/5))·e^{−t·(1/ℓ+1/(d−ℓ))}`
and `C := (12·ℓ)^k·(1−k/5)^{−α}`, `α := k·(d−ℓ)/d`:

    `distSubspaces V (modelX ℓ) ≤ η`  and  `height V hV ≤ C·η^{−α}`. -/
theorem modelStar_pair_star {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hk4 : k ≤ 4) (hkl : k ≤ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ V : Submodule ℝ ℝᵈ, ∃ hV : IsRational V,
      Module.finrank ℝ V = k ∧
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤
        (1 / (1 - (k : ℝ) / 5)) *
          Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) ∧
      LinearSubspaces.height V hV ≤
        ((12 : ℝ) * (ℓ : ℝ)) ^ k * (1 - (k : ℝ) / 5) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / (1 - (k : ℝ) / 5)) *
            Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
  classical
  rcases modelStar_pair (d := d) hℓ0 hℓd hk1 hk4 hkl ht with ⟨V, hV, hfin, hdist, hheight⟩
  refine ⟨V, hV, hfin, hdist, ?_⟩
  let c : ℝ := 1 - (k : ℝ) / 5
  have hc : 0 < c := by
    dsimp [c]
    have hk4R : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
    nlinarith
  have hid := star_form_height_identity (d := d) (ℓ := ℓ) (k := k) hℓ0 hℓd c hc t
  -- hid : (12ℓ)^k·e^{tk/ℓ} = (12ℓ)^k·c^{-α}·η^{-α}  (η := (1/c)·e^{-t·(1/ℓ + 1/(d-ℓ))})
  calc
    LinearSubspaces.height V hV
        ≤ ((12 : ℝ) * (ℓ : ℝ)) ^ k * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := hheight
    _ = ((12 : ℝ) * (ℓ : ℝ)) ^ k * c ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := hid
    _ = ((12 : ℝ) * (ℓ : ℝ)) ^ k * (1 - (k : ℝ) / 5) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / (1 - (k : ℝ) / 5)) *
            Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
          dsimp [c]

/-- **Small-η Dirichlet contract at `x₀`** (the hT9'-shape restricted to the coordinate
plane): with `η₀ := 1/(1−k/5)`, every target `0 < η ≤ η₀` admits the rational `k`-plane of
`modelStar_pair_star` at the time `t := log((1/c)/η)/S` (so that the achieved distance
bound `η(t) = (1/c)·e^{−t·S}` equals `η` exactly), with
`height V ≤ (12·ℓ)^k·c^{−α}·η^{−α}`.  This is the template the general-`x` machinery will
instantiate for every `ℓ`-plane. -/
theorem modelStar_smallEta_dirichlet {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ}
    (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hkl : k ≤ ℓ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ V : Submodule ℝ ℝᵈ, ∃ hV : IsRational V,
          Module.finrank ℝ V = k ∧
          LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤ η ∧
          LinearSubspaces.height V hV ≤
            ((12 : ℝ) * (ℓ : ℝ)) ^ k * (1 - (k : ℝ) / 5) ^
                (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
              η ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
  classical
  let c : ℝ := 1 - (k : ℝ) / 5
  have hc : 0 < c := by
    dsimp [c]
    have hk4R : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
    nlinarith
  let α : ℝ := ((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ)
  let S : ℝ := (1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)
  have hSpos : 0 < S := by
    dsimp [S]
    have h1 : 0 < (1 : ℝ) / (ℓ : ℝ) := one_div_pos.mpr (by exact_mod_cast hℓ0)
    have h2 : 0 < (1 : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
      apply one_div_pos.mpr
      exact_mod_cast (Nat.sub_pos_of_lt hℓd)
    nlinarith
  refine ⟨1 / c, one_div_pos.mpr hc, ?_⟩
  intro η hηpos hηle
  have hηle' : η ≤ 1 / c := by simpa [c] using hηle
  have hxpos : 0 < (1 / c) / η := div_pos (one_div_pos.mpr hc) hηpos
  have hxge : 1 ≤ (1 / c) / η := by
    rw [le_div_iff₀ hηpos]
    simpa using hηle'
  have ht0 : 0 ≤ Real.log ((1 / c) / η) := Real.log_nonneg hxge
  let t : ℝ := Real.log ((1 / c) / η) / S
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg ht0 (le_of_lt hSpos)
  have htS : t * S = Real.log ((1 / c) / η) := by
    dsimp [t]
    field_simp [ne_of_gt hSpos]
  have hηt : (1 / c) * Real.exp (-t * S) = η := by
    calc
      (1 / c) * Real.exp (-t * S) = (1 / c) * Real.exp (-(t * S)) := by congr 1; ring_nf
      _ = (1 / c) * (Real.exp (t * S))⁻¹ := by rw [Real.exp_neg]
      _ = (1 / c) * (Real.exp (Real.log ((1 / c) / η)))⁻¹ := by rw [← htS]
      _ = (1 / c) * (((1 / c) / η)⁻¹) := by rw [Real.exp_log hxpos]
      _ = η := by field_simp [ne_of_gt hηpos]
  rcases modelStar_pair_star (d := d) hℓ0 hℓd hk1 hk4 hkl ht with ⟨V, hV, hfin, hdist, hheight⟩
  have hdistη : LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤ η := by
    calc
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤ (1 / c) * Real.exp (-t * S) := by
            simpa [S, c] using hdist
      _ = η := hηt
  have hheightη : LinearSubspaces.height V hV ≤
      ((12 : ℝ) * (ℓ : ℝ)) ^ k * c ^ (-α) * η ^ (-α) := by
    calc
      LinearSubspaces.height V hV
          ≤ ((12 : ℝ) * (ℓ : ℝ)) ^ k * c ^ (-α) *
              ((1 / c) * Real.exp (-t * S)) ^ (-α) := by
                simpa [S, c, α] using hheight
      _ = ((12 : ℝ) * (ℓ : ℝ)) ^ k * c ^ (-α) * η ^ (-α) := by rw [hηt]
  refine ⟨V, hV, hfin, hdistη, ?_⟩
  simpa [c, α] using hheightη


/-! ### General-`k` Model Theorem-9 (★-pair machinery, no `k ≤ 4`)

The `k ≤ 4` restriction of `modelStar_distance`/`modelStar_pair`/`modelStar_pair_star`/
`modelStar_smallEta_dirichlet` comes only from the slack `c = 1 − k/5` needing `k ≤ 4`.
With the general-`k` contracting annulus (`BlockCovering.exists_blockFamily_annulus_k_exp`,
`(11k)`-anchor, per-direction error `2/(11k−1)`) and the `(11k)`-two-sided `π₀`-sandwich
(`WedgeContract.wedgeContract_blockAnnulus_twoSided_k`, wedge loss `2k/(11k−1)`), the slack
is `c_k := 1 − 2k/(11k−1) ≥ 4/5 > 0` for EVERY `k ≥ 1`, the annulus norms lie in
`[((11k−1)·(ℓ:ℝ))·e^{−t/ℓ}, ((11k+1)·(ℓ:ℝ))·e^{−t/ℓ}]`, and the height base becomes
`A_k := ((11k+1)·(ℓ:ℝ))^k`.  This section re-proves the whole ★-chain for every
`1 ≤ k ≤ ℓ` (suffix `_k`):

* `preimage_norm_le_of_annulus_exp_mul` — the generic-`M` annulus preimage estimate
  (`‖v i‖ ≤ M·(ℓ:ℝ)·e^{−t/ℓ}` ⟹ `‖m i‖ ≤ M·(ℓ:ℝ)`), generalising the `M = 12` version;
* `star_form_height_identity_A` — the ★-form identity with a free height base `A`;
* `modelStar_distance_k`, `modelStar_pair_k`, `modelStar_pair_star_k`,
  `modelStar_smallEta_dirichlet_k` — the general-`k` ★-chain at `x₀`.
-/

/-- **Annulus preimage estimate, generic `M`**: the integer preimages `m` of an annulus
family `v ∈ flowLattice` (exp flow, `t ≥ 0`, `‖v i‖ ≤ M·(ℓ:ℝ)·e^{−t/ℓ}`) have bounded
norm: `‖m i‖ ≤ M·(ℓ:ℝ)`. -/
lemma preimage_norm_le_of_annulus_exp_mul {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {t : ℝ}
    (ht : 0 ≤ t) (M : ℝ) {k : ℕ}
    (v : Fin k → flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)
    (m : Fin k → ℝᵈ)
    (hm_eq : ∀ i, (scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (m i) = (v i : ℝᵈ))
    (hvann : ∀ i, ‖(v i : ℝᵈ)‖ ≤ M * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :
    ∀ i, ‖m i‖ ≤ M * (ℓ : ℝ) := by
  intro i
  have hli := invFlow_left_inv (d := d) (Real.exp (-t / (ℓ : ℝ)))
    (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (Real.exp_pos _)) (m i)
  have hm : m i = invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (v i : ℝᵈ) := by
    calc
      m i = invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
            (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ
            ((scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
              (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ)) (m i)) := hli.symm
      _ = invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
            (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (v i : ℝᵈ) := by rw [hm_eq i]
  have hn := invFlow_exp_norm_le (d := d) hℓ0 hℓd ht (v i : ℝᵈ)
  have he : Real.exp (t / (ℓ : ℝ)) * Real.exp (-t / (ℓ : ℝ)) = 1 := by
    rw [← Real.exp_add]
    have harg : t / (ℓ : ℝ) + -t / (ℓ : ℝ) = 0 := by ring
    rw [harg, Real.exp_zero]
  calc
    ‖m i‖ = ‖invFlow (d := d) (Real.exp (-t / (ℓ : ℝ)))
          (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (v i : ℝᵈ)‖ := by rw [hm]
    _ ≤ Real.exp (t / (ℓ : ℝ)) * ‖(v i : ℝᵈ)‖ := hn
    _ ≤ Real.exp (t / (ℓ : ℝ)) * (M * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ))) :=
          mul_le_mul_of_nonneg_left (hvann i) (le_of_lt (Real.exp_pos _))
    _ = M * (ℓ : ℝ) := by
          calc
            Real.exp (t / (ℓ : ℝ)) * (M * (ℓ : ℝ) * Real.exp (-t / (ℓ : ℝ)))
                = M * (ℓ : ℝ) *
                    (Real.exp (t / (ℓ : ℝ)) * Real.exp (-t / (ℓ : ℝ))) := by ring
            _ = M * (ℓ : ℝ) := by rw [he]; ring

/-- **Model Theorem 9, distance half, general `k`**: with `1 ≤ k ≤ ℓ < d` (no `k ≤ 4`),
the Prop-5 annulus construction in the exponential flow at time `t` yields a `k`-plane
whose distance to `x₀ = modelX ℓ` is at most
`(1/c)·e^{−t·(1/ℓ+1/(d−ℓ))}` with the universal slack `c := 1 − 2k/(11k−1) ≥ 4/5`. -/
theorem modelStar_distance_k {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hkl : k ≤ ℓ) {t : ℝ} :
    ∃ V : Submodule ℝ ℝᵈ, Module.finrank ℝ V = k ∧
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤
        (1 / (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) *
          Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
  classical
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : 0 < a := by dsimp [a]; exact Real.exp_pos _
  have hb0 : 0 < b := by dsimp [b]; exact Real.exp_pos _
  have ha0' : a ≠ 0 := ne_of_gt ha0
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have hℓd' : ℓ ≤ d := le_of_lt hℓd
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  let c : ℝ := 1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)
  have hc0 : 0 < c := by
    dsimp [c]
    have hloss := Submission.WedgeContract.wedgeLoss_k_le_one_fifth k hk1
    have hlosslt1 : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) < 1 := by
      exact lt_of_le_of_lt hloss (by norm_num)
    linarith
  -- (0) explicit Lemma-5 directions: the first k standard vectors
  let u : Fin k → ℝᵈ := contractDir (d := d) hℓd' hkl
  have hu_mem : ∀ i, u i ∈ blockSpan (d := d) ℓ := fun i =>
    contractDir_mem_blockSpan (d := d) hℓd' hkl i
  have huON : Orthonormal ℝ u := by
    dsimp [u]
    exact contractDir_orthonormal (d := d) hℓd' hkl
  have hu1 : ∀ i, ‖u i‖ = 1 := fun i => (huON.1 i)
  -- (1) annulus family w : Fin k → smallFlow (general-k, (11k)-anchor)
  obtain ⟨w, hwann⟩ := exists_blockFamily_annulus_k_exp (d := d) ℓ hℓd (t := t)
    (m := k) (u := u) hk1 hu_mem hu1
  -- (2) π₀ control and positivity on the annulus wedge
  have hv0 : ∀ i : Fin k, 0 < ‖(w i : ℝᵈ)‖ := by
    intro i
    have hlo : (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a ≤ ‖(w i : ℝᵈ)‖ := by
      simpa [a] using (hwann i).2.1
    have hpos : 0 < (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a := by
      have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
      have hC : 0 < (ℓ : ℝ) * a := mul_pos (by exact_mod_cast hℓ0) ha0
      nlinarith
    exact lt_of_lt_of_le hpos hlo
  have hprod0 : 0 < (∏ i : Fin k, ‖(w i : ℝᵈ)‖) := Finset.prod_pos (fun i hi => hv0 i)
  have htwo := wedgeContract_blockAnnulus_twoSided_k (d := d) (k := k) ℓ hℓd' (a := a)
    (b := b) ha0 hℓ0 u hu_mem huON hk0 w hwann
  have hpi0pos : 0 < ‖pi0 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 hc0) htwo.1
  have hupw := norm_pi0_le (d := d) (k := k) ℓ
    (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))
  have hwpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ :=
    lt_of_lt_of_le hpi0pos hupw
  -- (3) lift to the full flow lattice
  let v : Fin k → flowLattice (d := d) a b ℓ := fun i =>
    ⟨(w i : ℝᵈ), (smallFlow_le_flowLattice (d := d) a b ℓ hℓd') (w i).2⟩
  have hlow : c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
      ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
    have hle : ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
        (∏ i : Fin k, ‖(v i : ℝᵈ)‖) :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
        (fun i : Fin k => (v i : ℝᵈ))
    have h1m : 0 ≤ c := le_of_lt hc0
    calc
      c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖
          ≤ c * (∏ i : Fin k, ‖(v i : ℝᵈ)‖) := mul_le_mul_of_nonneg_left hle h1m
      _ = (∏ i : Fin k, ‖(v i : ℝᵈ)‖) *
            (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) := by dsimp [c]; rw [mul_comm]
      _ ≤ ‖pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
            simpa [v] using htwo.1
  have hvpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ := by
    have hpi0pos_v : 0 < ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
      simpa [v] using hpi0pos
    have hupv := norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))
    exact lt_of_lt_of_le hpi0pos_v hupv
  have hvine : exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) ≠ 0 :=
    norm_pos_iff.mp hvpos
  have hLIv : LinearIndependent ℝ (fun i : Fin k => (v i : ℝᵈ)) := by
    by_contra h
    exact hvine (AlternatingMap.map_linearDependent (f := exteriorPower.ιMulti ℝ k)
      (fun i : Fin k => (v i : ℝᵈ)) h)
  -- (4) integer preimage family m : f(m i) = (v i)
  obtain ⟨m, _hm_int, hm_eq⟩ := exists_preimage_family (d := d) a b ℓ ha0' hb0' v
  have hLIv' : LinearIndependent ℝ (fun i : Fin k => scaleMap (twoScale a b ℓ) (m i)) := by
    convert hLIv using 1
    funext i
    exact hm_eq i
  have hLIm : LinearIndependent ℝ m :=
    LinearIndependent.of_comp (scaleMap (twoScale a b ℓ)) hLIv'
  -- (5) the cone condition (π₀ control = block-0 dominance after unwinding the flow)
  have hfk : exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m) =
      exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) := by
    rw [exteriorPower.map_apply_ιMulti (f := scaleMap (twoScale a b ℓ)) (m := m)]
    congr 1
    funext i
    exact hm_eq i
  have hcone : c * ‖exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m)‖ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ))
          (exteriorPower.ιMulti ℝ k m)) 0‖ := by
    rw [hfk]
    rw [← pi0_apply (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))]
    exact hlow
  -- (6) the model Prop-1-part-2 distance bound (arbitrary two-scale parameters)
  have hmain := Submission.ModelCone.model_prop1_part2 (d := d) (k := k) ℓ hk0 hkl hℓ0 hℓd' m
    hLIm a b c ha0 hb0 hc0 hcone
  -- (7) exponent rewrite to the paper's `1/(d−ℓ)` denominator
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  have hm : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hb_eq : b = Real.exp (t / ((d - ℓ : ℕ) : ℝ)) := by
    dsimp [b]
    congr 1
    rw [Nat.cast_sub (le_of_lt hℓd)]
  have hA : a / (c * b) = (1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) +
      (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
    rw [hb_eq]
    dsimp [a]
    exact Commons.Analysis.Real.exp_neg_div_mul_exp (t := t) (ℓ := (ℓ : ℝ))
      (m := ((d - ℓ : ℕ) : ℝ)) (c := c) hℓR hm (ne_of_gt hc0)
  refine ⟨Submodule.span ℝ (Set.range m), ?_, ?_⟩
  · exact PlaneFinrank.finrank_span_range (d := d) m hLIm
  · calc
      LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) (modelX (d := d) ℓ)
          ≤ a / (c * b) := hmain
      _ = (1 / (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) *
            Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
            simpa [c] using hA


/-- ★-form identity with a free height base `A`:
`A·e^{t·k/ℓ} = A·c^{−α}·η^{−α}` for `η := (1/c)·e^{−t·S}`, `S := 1/ℓ + 1/(d−ℓ)`,
`α := k·(d−ℓ)/d` (the general-`k` version of `star_form_height_identity`, used with
`A = A_k := (((11k+1)·(ℓ:ℝ))^k`). -/
lemma star_form_height_identity_A {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ}
    (A c : ℝ) (hc : 0 < c) (t : ℝ) :
    A * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) =
      A * c ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
        ((1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
          (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
  classical
  let α : ℝ := ((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ)
  let S : ℝ := (1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le hℓ0 (le_of_lt hℓd)))
  have hdℓ : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hcast : (d : ℝ) - (ℓ : ℝ) = ((d - ℓ : ℕ) : ℝ) := by
    rw [← Nat.cast_sub (le_of_lt hℓd)]
  have hE : 0 < Real.exp (-t * S) := Real.exp_pos _
  have hc1 : 0 < 1 / c := one_div_pos.mpr hc
  have hSα : S * α = (k : ℝ) / (ℓ : ℝ) := by
    dsimp [S, α]
    rw [hcast]
    have hsub : ((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ) = (d : ℝ) := by
      rw [← Nat.cast_add]
      congr 1
      exact Nat.sub_add_cancel (le_of_lt hℓd)
    field_simp [hdR, hℓR, hdℓ]
    nlinarith
  have hEpow : (Real.exp (-t * S)) ^ (-α) = Real.exp (t * (S * α)) := by
    rw [Real.rpow_def_of_pos hE (-α)]
    rw [Real.log_exp]
    congr 1
    ring_nf
  have hηpow : ((1 / c) * Real.exp (-t * S)) ^ (-α) =
      (1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α) := by
    exact Real.mul_rpow (z := -α) (le_of_lt hc1) (le_of_lt hE)
  have hcomb : c ^ (-α) * (1 / c) ^ (-α) = 1 := by
    have hm := Real.mul_rpow (z := -α) (le_of_lt hc) (le_of_lt hc1)
    rw [← hm]
    have h1 : c * (1 / c) = 1 := by field_simp [ne_of_gt hc]
    rw [h1, Real.one_rpow]
  calc
    A * Real.exp (t * ((k : ℝ) / (ℓ : ℝ)))
        = A * Real.exp (t * (S * α)) := by rw [hSα]
    _ = A * (Real.exp (-t * S)) ^ (-α) := by rw [← hEpow]
    _ = A * c ^ (-α) * (1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α) := by
          have h := congrArg (fun r : ℝ => A * r * (Real.exp (-t * S)) ^ (-α)) hcomb.symm
          calc
            A * (Real.exp (-t * S)) ^ (-α)
                = A * 1 * (Real.exp (-t * S)) ^ (-α) := by ring
            _ = A * (c ^ (-α) * (1 / c) ^ (-α)) * (Real.exp (-t * S)) ^ (-α) := h
            _ = A * c ^ (-α) * (1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α) := by ring
    _ = A * c ^ (-α) * ((1 / c) ^ (-α) * (Real.exp (-t * S)) ^ (-α)) := by ring
    _ = A * c ^ (-α) * ((1 / c) * Real.exp (-t * S)) ^ (-α) := by
          rw [← hηpow]
    _ = A * c ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
          dsimp [α, S]

/-- **Model Theorem 9, ★-pair, general `k`**: for `1 ≤ k ≤ ℓ < d`, `t ≥ 0`, the Prop-5
annulus construction yields a rational `k`-plane `V` with
`distSubspaces V (modelX ℓ) ≤ (1/c)·e^{−t(1/ℓ+1/(d−ℓ))}` and
`height V ≤ A_k·e^{t·k/ℓ}` where `c := 1 − 2k/(11k−1)` and
`A_k := (((11:ℝ)·(k:ℝ)+1)·(ℓ:ℝ))^k` — no `k ≤ 4` restriction. -/
theorem modelStar_pair_k {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hkl : k ≤ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ V : Submodule ℝ ℝᵈ, ∃ hV : IsRational V,
      Module.finrank ℝ V = k ∧
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤
        (1 / (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) *
          Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) ∧
      LinearSubspaces.height V hV ≤
        (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
  classical
  let a : ℝ := Real.exp (-t / (ℓ : ℝ))
  let b : ℝ := Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))
  have ha0 : 0 < a := by dsimp [a]; exact Real.exp_pos _
  have hb0 : 0 < b := by dsimp [b]; exact Real.exp_pos _
  have ha0' : a ≠ 0 := ne_of_gt ha0
  have hb0' : b ≠ 0 := ne_of_gt hb0
  have hℓd' : ℓ ≤ d := le_of_lt hℓd
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk1
  let c : ℝ := 1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)
  have hc0 : 0 < c := by
    dsimp [c]
    have hloss := Submission.WedgeContract.wedgeLoss_k_le_one_fifth k hk1
    have hlosslt1 : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) < 1 := by
      exact lt_of_le_of_lt hloss (by norm_num)
    linarith
  -- (0) explicit Lemma-5 directions
  let u : Fin k → ℝᵈ := contractDir (d := d) hℓd' hkl
  have hu_mem : ∀ i, u i ∈ blockSpan (d := d) ℓ := fun i =>
    contractDir_mem_blockSpan (d := d) hℓd' hkl i
  have huON : Orthonormal ℝ u := by
    dsimp [u]
    exact contractDir_orthonormal (d := d) hℓd' hkl
  have hu1 : ∀ i, ‖u i‖ = 1 := fun i => (huON.1 i)
  -- (1) annulus family w : Fin k → smallFlow (general-k, (11k)-anchor)
  obtain ⟨w, hwann⟩ := exists_blockFamily_annulus_k_exp (d := d) ℓ hℓd (t := t)
    (m := k) (u := u) hk1 hu_mem hu1
  -- (2) π₀ control and positivity on the annulus wedge
  have hv0 : ∀ i : Fin k, 0 < ‖(w i : ℝᵈ)‖ := by
    intro i
    have hlo : (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a ≤ ‖(w i : ℝᵈ)‖ := by
      simpa [a] using (hwann i).2.1
    have hpos : 0 < (((11 : ℝ) * (k : ℝ) - 1) * (ℓ : ℝ)) * a := by
      have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
      have hC : 0 < (ℓ : ℝ) * a := mul_pos (by exact_mod_cast hℓ0) ha0
      nlinarith
    exact lt_of_lt_of_le hpos hlo
  have hprod0 : 0 < (∏ i : Fin k, ‖(w i : ℝᵈ)‖) := Finset.prod_pos (fun i hi => hv0 i)
  have htwo := wedgeContract_blockAnnulus_twoSided_k (d := d) (k := k) ℓ hℓd' (a := a)
    (b := b) ha0 hℓ0 u hu_mem huON hk0 w hwann
  have hpi0pos : 0 < ‖pi0 (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))‖ :=
    lt_of_lt_of_le (mul_pos hprod0 hc0) htwo.1
  have hupw := norm_pi0_le (d := d) (k := k) ℓ
    (exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ)))
  have hwpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (w i : ℝᵈ))‖ :=
    lt_of_lt_of_le hpi0pos hupw
  -- (3) lift to the full flow lattice
  let v : Fin k → flowLattice (d := d) a b ℓ := fun i =>
    ⟨(w i : ℝᵈ), (smallFlow_le_flowLattice (d := d) a b ℓ hℓd') (w i).2⟩
  have hlow : c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
      ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
    have hle : ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ ≤
        (∏ i : Fin k, ‖(v i : ℝᵈ)‖) :=
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
        (fun i : Fin k => (v i : ℝᵈ))
    have h1m : 0 ≤ c := le_of_lt hc0
    calc
      c * ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖
          ≤ c * (∏ i : Fin k, ‖(v i : ℝᵈ)‖) := mul_le_mul_of_nonneg_left hle h1m
      _ = (∏ i : Fin k, ‖(v i : ℝᵈ)‖) *
            (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)) := by dsimp [c]; rw [mul_comm]
      _ ≤ ‖pi0 (d := d) (k := k) ℓ
            (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
            simpa [v] using htwo.1
  have hvpos : 0 < ‖exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ))‖ := by
    have hpi0pos_v : 0 < ‖pi0 (d := d) (k := k) ℓ
        (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))‖ := by
      simpa [v] using hpi0pos
    have hupv := norm_pi0_le (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))
    exact lt_of_lt_of_le hpi0pos_v hupv
  have hvine : exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) ≠ 0 :=
    norm_pos_iff.mp hvpos
  have hLIv : LinearIndependent ℝ (fun i : Fin k => (v i : ℝᵈ)) := by
    by_contra h
    exact hvine (AlternatingMap.map_linearDependent (f := exteriorPower.ιMulti ℝ k)
      (fun i : Fin k => (v i : ℝᵈ)) h)
  -- (4) integer preimage family m : f(m i) = (v i)
  obtain ⟨m, hm_int, hm_eq⟩ := exists_preimage_family (d := d) a b ℓ ha0' hb0' v
  have hLIv' : LinearIndependent ℝ (fun i : Fin k => scaleMap (twoScale a b ℓ) (m i)) := by
    convert hLIv using 1
    funext i
    exact hm_eq i
  have hLIm : LinearIndependent ℝ m :=
    LinearIndependent.of_comp (scaleMap (twoScale a b ℓ)) hLIv'
  -- (5) the cone condition
  have hfk : exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m) =
      exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)) := by
    rw [exteriorPower.map_apply_ιMulti (f := scaleMap (twoScale a b ℓ)) (m := m)]
    congr 1
    funext i
    exact hm_eq i
  have hcone : c * ‖exteriorPower.map k (scaleMap (twoScale a b ℓ))
        (exteriorPower.ιMulti ℝ k m)‖ ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ))
          (exteriorPower.ιMulti ℝ k m)) 0‖ := by
    rw [hfk]
    rw [← pi0_apply (d := d) (k := k) ℓ
      (exteriorPower.ιMulti ℝ k (fun i : Fin k => (v i : ℝᵈ)))]
    exact hlow
  -- (6) the model Prop-1-part-2 distance bound (arbitrary two-scale parameters)
  have hmain := Submission.ModelCone.model_prop1_part2 (d := d) (k := k) ℓ hk0 hkl hℓ0 hℓd' m
    hLIm a b c ha0 hb0 hc0 hcone
  -- (7) exponent rewrite to the paper's `1/(d−ℓ)` denominator
  have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ0)
  have hm : ((d - ℓ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.sub_pos_of_lt hℓd))
  have hb_eq : b = Real.exp (t / ((d - ℓ : ℕ) : ℝ)) := by
    dsimp [b]
    congr 1
    rw [Nat.cast_sub (le_of_lt hℓd)]
  have hA : a / (c * b) = (1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) +
      (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
    rw [hb_eq]
    dsimp [a]
    exact Commons.Analysis.Real.exp_neg_div_mul_exp (t := t) (ℓ := (ℓ : ℝ))
      (m := ((d - ℓ : ℕ) : ℝ)) (c := c) hℓR hm (ne_of_gt hc0)
  -- (8) annulus preimage estimate ‖m i‖ ≤ ((11k+1)·(ℓ:ℝ))
  have hvann : ∀ i, ‖(v i : ℝᵈ)‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) * a := by
    intro i
    simpa [v, a] using (hwann i).2.2
  have hm_pre : ∀ i, ‖m i‖ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) :=
    preimage_norm_le_of_annulus_exp_mul (d := d) hℓ0 hℓd ht
      (((11 : ℝ) * (k : ℝ) + 1)) v m hm_eq (by intro i; simpa [a] using hvann i)
  -- (9) height bound: height V ≤ A_k ≤ A_k·e^{t·k/ℓ}
  let V : Submodule ℝ ℝᵈ := Submodule.span ℝ (Set.range m)
  have hV : IsRational V := by
    dsimp [V]
    exact Submission.RationalSpan.isRational_span_of_mem_intPoints (d := d) m hm_int
  have hfinV : Module.finrank ℝ V = k := by
    dsimp [V]
    exact PlaneFinrank.finrank_span_range (d := d) m hLIm
  let uu : Fin (Module.finrank ℝ V) → ℝᵈ := fun i => m (Fin.cast hfinV i)
  have hu_mem_uu : ∀ j, uu j ∈ Submission.Heights.imageLattice (d := d) V := by
    intro j
    apply Submission.ModelStarHeight.mem_imageLattice_of_mem V
    · dsimp [uu, V]
      exact Submodule.subset_span ⟨Fin.cast hfinV j, rfl⟩
    · dsimp [uu]
      exact hm_int (Fin.cast hfinV j)
  have hu_li_uu : LinearIndependent ℝ uu := by
    dsimp [uu]
    exact LinearIndependent.comp hLIm (Fin.cast hfinV) (Fin.cast_injective hfinV)
  have hH := Submission.ModelStarHeight.height_le_norm_iMulti_of_mem_imageLattice (d := d) V hV
    uu hu_mem_uu hu_li_uu
  have hprod_le : (∏ i : Fin (Module.finrank ℝ V), ‖uu i‖) ≤
      (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ Module.finrank ℝ V := by
    calc
      (∏ i : Fin (Module.finrank ℝ V), ‖uu i‖)
          ≤ ∏ _i : Fin (Module.finrank ℝ V), (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) := by
            exact Finset.prod_le_prod (s := Finset.univ)
              (f := fun i : Fin (Module.finrank ℝ V) => ‖uu i‖)
              (g := fun _ : Fin (Module.finrank ℝ V) => (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)))
              (by intro i hi; exact norm_nonneg _)
              (by intro i hi; calc
                  ‖uu i‖ = ‖m (Fin.cast hfinV i)‖ := by dsimp [uu]
                  _ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) := hm_pre (Fin.cast hfinV i))
      _ = (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ Module.finrank ℝ V := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hHfin : LinearSubspaces.height V hV ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k := by
    calc
      LinearSubspaces.height V hV
          ≤ ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) uu‖ := hH
      _ ≤ (∏ i : Fin (Module.finrank ℝ V), ‖uu i‖) :=
            Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod uu
      _ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ Module.finrank ℝ V := hprod_le
      _ = (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k := by rw [hfinV]
  have hC0 : 0 ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k := pow_nonneg (by positivity) k
  have he1 : 1 ≤ Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
    apply Real.one_le_exp
    have hℓR' : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ0
    exact mul_nonneg ht (div_nonneg (Nat.cast_nonneg k) (le_of_lt hℓR'))
  have hHexp : LinearSubspaces.height V hV ≤
      (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k *
        Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
    calc
      LinearSubspaces.height V hV ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k := hHfin
      _ ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k *
            Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by
            simpa [mul_comm] using (mul_le_mul_of_nonneg_right he1 hC0)
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · exact hfinV
  · dsimp [V]
    calc
      LinearSubspaces.distSubspaces (Submodule.span ℝ (Set.range m)) (modelX (d := d) ℓ)
          ≤ a / (c * b) := hmain
      _ = (1 / (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) *
            Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
            simpa [c] using hA
  · dsimp [V]
    exact hHexp


/-- **Model Theorem 9, ★-shape, general `k`**: the `modelStar_pair_k` bound in the exact
correlated form used by the small-`η` Dirichlet contract: with
`η := (1/c)·e^{−t·(1/ℓ+1/(d−ℓ))}` and `A_k := ((11k+1)·(ℓ:ℝ))^k`,
`c := 1 − 2k/(11k−1)`, `α := k·(d−ℓ)/d`:

    `distSubspaces V (modelX ℓ) ≤ η`  and  `height V hV ≤ A_k·c^{−α}·η^{−α}`. -/
theorem modelStar_pair_star_k {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ} (hk1 : 1 ≤ k)
    (hkl : k ≤ ℓ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ V : Submodule ℝ ℝᵈ, ∃ hV : IsRational V,
      Module.finrank ℝ V = k ∧
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤
        (1 / (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) *
          Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ))) ∧
      LinearSubspaces.height V hV ≤
        (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k * (1 - (2 * (k : ℝ)) /
            ((11 : ℝ) * (k : ℝ) - 1)) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) *
            Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
  classical
  rcases modelStar_pair_k (d := d) hℓ0 hℓd hk1 hkl ht with ⟨V, hV, hfin, hdist, hheight⟩
  refine ⟨V, hV, hfin, hdist, ?_⟩
  let c : ℝ := 1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)
  have hc : 0 < c := by
    dsimp [c]
    have hloss := Submission.WedgeContract.wedgeLoss_k_le_one_fifth k hk1
    have hlosslt1 : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) < 1 := by
      exact lt_of_le_of_lt hloss (by norm_num)
    linarith
  let A : ℝ := (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k
  have hid := star_form_height_identity_A (d := d) (ℓ := ℓ) (k := k) hℓ0 hℓd A c hc t
  calc
    LinearSubspaces.height V hV
        ≤ A * Real.exp (t * ((k : ℝ) / (ℓ : ℝ))) := by simpa [A] using hheight
    _ = A * c ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / c) * Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := hid
    _ = (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k * (1 - (2 * (k : ℝ)) /
            ((11 : ℝ) * (k : ℝ) - 1)) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
          ((1 / (1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1))) *
            Real.exp (-t * ((1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)))) ^
            (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
          dsimp [A, c]

/-- **Small-η Dirichlet contract at `x₀`, general `k`** (the hT9'-shape restricted to the
coordinate plane): with `η₀ := 1/c` (`c := 1 − 2k/(11k−1)`), every target `0 < η ≤ η₀`
admits the rational `k`-plane of `modelStar_pair_star_k` at the time
`t := log((1/c)/η)/S` (so that the achieved distance bound `η(t) = (1/c)·e^{−t·S}` equals
`η` exactly), with `height V ≤ A_k·c^{−α}·η^{−α}` — the general-`x` machinery will
instantiate this for every `ℓ`-plane. -/
theorem modelStar_smallEta_dirichlet_k {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {k : ℕ}
    (hk1 : 1 ≤ k) (hkl : k ≤ ℓ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∃ V : Submodule ℝ ℝᵈ, ∃ hV : IsRational V,
          Module.finrank ℝ V = k ∧
          LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤ η ∧
          LinearSubspaces.height V hV ≤
            (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k * (1 - (2 * (k : ℝ)) /
                ((11 : ℝ) * (k : ℝ) - 1)) ^
                (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) *
              η ^ (-(((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ))) := by
  classical
  let c : ℝ := 1 - (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1)
  have hc : 0 < c := by
    dsimp [c]
    have hloss := Submission.WedgeContract.wedgeLoss_k_le_one_fifth k hk1
    have hlosslt1 : (2 * (k : ℝ)) / ((11 : ℝ) * (k : ℝ) - 1) < 1 := by
      exact lt_of_le_of_lt hloss (by norm_num)
    linarith
  let α : ℝ := ((k : ℝ) * ((d : ℝ) - (ℓ : ℝ))) / (d : ℝ)
  let S : ℝ := (1 : ℝ) / (ℓ : ℝ) + (1 : ℝ) / ((d - ℓ : ℕ) : ℝ)
  have hSpos : 0 < S := by
    dsimp [S]
    have h1 : 0 < (1 : ℝ) / (ℓ : ℝ) := one_div_pos.mpr (by exact_mod_cast hℓ0)
    have h2 : 0 < (1 : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
      apply one_div_pos.mpr
      exact_mod_cast (Nat.sub_pos_of_lt hℓd)
    nlinarith
  refine ⟨1 / c, one_div_pos.mpr hc, ?_⟩
  intro η hηpos hηle
  have hηle' : η ≤ 1 / c := by simpa [c] using hηle
  have hxpos : 0 < (1 / c) / η := div_pos (one_div_pos.mpr hc) hηpos
  have hxge : 1 ≤ (1 / c) / η := by
    rw [le_div_iff₀ hηpos]
    simpa using hηle'
  have ht0 : 0 ≤ Real.log ((1 / c) / η) := Real.log_nonneg hxge
  let t : ℝ := Real.log ((1 / c) / η) / S
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg ht0 (le_of_lt hSpos)
  have htS : t * S = Real.log ((1 / c) / η) := by
    dsimp [t]
    field_simp [ne_of_gt hSpos]
  have hηt : (1 / c) * Real.exp (-t * S) = η := by
    calc
      (1 / c) * Real.exp (-t * S) = (1 / c) * Real.exp (-(t * S)) := by congr 1; ring_nf
      _ = (1 / c) * (Real.exp (t * S))⁻¹ := by rw [Real.exp_neg]
      _ = (1 / c) * (Real.exp (Real.log ((1 / c) / η)))⁻¹ := by rw [← htS]
      _ = (1 / c) * (((1 / c) / η)⁻¹) := by rw [Real.exp_log hxpos]
      _ = η := by field_simp [ne_of_gt hηpos]
  rcases modelStar_pair_star_k (d := d) hℓ0 hℓd hk1 hkl ht with ⟨V, hV, hfin, hdist, hheight⟩
  have hdistη : LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤ η := by
    calc
      LinearSubspaces.distSubspaces V (modelX (d := d) ℓ) ≤ (1 / c) * Real.exp (-t * S) := by
            simpa [S, c] using hdist
      _ = η := hηt
  have hheightη : LinearSubspaces.height V hV ≤
      (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k * c ^ (-α) * η ^ (-α) := by
    calc
      LinearSubspaces.height V hV
          ≤ (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k * c ^ (-α) *
              ((1 / c) * Real.exp (-t * S)) ^ (-α) := by
                simpa [S, c, α] using hheight
      _ = (((11 : ℝ) * (k : ℝ) + 1) * (ℓ : ℝ)) ^ k * c ^ (-α) * η ^ (-α) := by rw [hηt]
  refine ⟨V, hV, hfin, hdistη, ?_⟩
  simpa [c, α] using hheightη

end Submission.ModelStar
