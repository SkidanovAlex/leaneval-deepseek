import Mathlib
import Submission.Work.Serre.E2bDefs
import Submission.Work.Cohomology.HomologyPairSequence

/-!
# The prism pieces: the geometric core of the relative cone construction

This file contains the *geometric* input to `Work.Serre.simpHomVanishing`: the decomposition of
the cylinder `Δⁿ × I` into its `n + 1` prism pieces, together with the face identities between
them.  These identities are exactly what turns the family `SimpHom.G` of homotopies of singular
simplices into a chain contraction of the relative chain complex `C_*(X,A)`.

## The pieces

For `k : Fin (n+1)`, the `k`-th piece

`Work.Serre.pp n k : C(Δⁿ⁺¹, Δⁿ × I)`

is the affine map sending the `j`-th vertex of `Δⁿ⁺¹` (`j : Fin (n+2)`) to the `j`-th vertex of
the ordered list `(e₀,0) ≤ … ≤ (e_k,0) ≤ (e_k,1) ≤ … ≤ (e_n,1)`; equivalently, in barycentric
coordinates, the first component is `∑_{ψ_k l = j} t l` and the second is `∑_{k < l} t l`, with
`ψ_k` the collapse `j ↦ j` (`j ≤ k`), `j ↦ j-1` (`j > k`).

## The face identities

Writing `δ_f` for `coface n f` (faces of `Δⁿ⁺¹`) and `φ_k = pp n k`:

* `pp_coface_zero_zero` : `φ_0 ∘ δ_0` is the *top* inclusion `z ↦ (z,1)`;
* `pp_coface_last_last` : `φ_n ∘ δ_{n+1}` is the *bottom* inclusion `z ↦ (z,0)`;
* `pp_coface_diag` : `φ_k ∘ δ_{k+1} = φ_{k+1} ∘ δ_{k+1}` (the `(k+1)`-st face is shared by the
  `k`-th and `(k+1)`-st piece);
* `pp_coface_lt` : for `f < k`, `φ_k ∘ δ_f = (δ_f × id) ∘ φ_{k-1}` (the `f`-th face of the
  `k`-th piece is the `(k-1)`-st piece of the prism over the `f`-th face);
* `pp_coface_gt` : for `f > k+1`, `φ_k ∘ δ_f = (δ_{f-1} × id) ∘ φ_k`.
-/

open scoped Topology unitInterval
open CategoryTheory Limits

open Work.RatHurewicz.Bridge (coface coface_apply)

namespace stdSimplex

/-- Two maps with the same fibre over zero induce the same zero-th coordinate. -/
lemma map_apply_zero_eq_of {X : Type*} [Fintype X] {Y Z : Type*} [Fintype Y] [Fintype Z]
    [DecidableEq Y] [DecidableEq Z] [Zero Y] [Zero Z]
    (χ : X → Y) (χ' : X → Z) (h : ∀ i, (χ i = 0 ↔ χ' i = 0)) (z : stdSimplex ℝ X) :
    (stdSimplex.map χ z : Y → ℝ) 0 = (stdSimplex.map χ' z : Z → ℝ) 0 := by
  rw [stdSimplex.map_coe, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    FunOnFinite.linearMap_apply_apply]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h i

/-- A map avoiding zero has vanishing zero-th coordinate. -/
lemma map_apply_zero_of_ne {X : Type*} [Fintype X] {Y : Type*} [Fintype Y] [DecidableEq Y]
    [Zero Y] (χ : X → Y) (h : ∀ i, χ i ≠ 0) (z : stdSimplex ℝ X) :
    (stdSimplex.map χ z : Y → ℝ) 0 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  refine Finset.sum_eq_zero (fun i hi => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact absurd hi (h i)

/-- A map vanishing everywhere has zero-th coordinate the total sum. -/
lemma map_apply_zero_of_eq {X : Type*} [Fintype X] {Y : Type*} [Fintype Y] [DecidableEq Y]
    [Zero Y] (χ : X → Y) (h : ∀ i, χ i = 0) (z : stdSimplex ℝ X) :
    (stdSimplex.map χ z : Y → ℝ) 0 = ∑ i, (z : X → ℝ) i := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Finset.filter_true_of_mem (fun i _ => h i)]

end stdSimplex

namespace Work.Serre

noncomputable section

/-! ## The two vertex maps of a prism piece -/

/-- The collapse vertex map `ψ_k : Fin (n+2) → Fin (n+1)`: `j ↦ j` for `j ≤ k` and `j ↦ j - 1`
for `j > k`; it describes the first component of the `k`-th prism piece. -/
def psi (n : ℕ) (k : Fin (n + 1)) (j : Fin (n + 2)) : Fin (n + 1) :=
  ⟨if (j : ℕ) ≤ (k : ℕ) then (j : ℕ) else (j : ℕ) - 1, by split_ifs <;> omega⟩

@[simp]
theorem psi_apply (n : ℕ) (k : Fin (n + 1)) (j : Fin (n + 2)) :
    ((psi n k j : Fin (n + 1)) : ℕ) =
      if (j : ℕ) ≤ (k : ℕ) then (j : ℕ) else (j : ℕ) - 1 := rfl

/-- The weight map `θ_k : Fin (n+2) → Fin (n+2)`: `i ↦ 0` for `i ≤ k` and `i ↦ i - k` for
`i > k`; the `0`-th coordinate of `stdSimplex.map (θ_k)` is `∑_{i ≤ k} t i`, so that
`1 - ` that coordinate is the second (interval) component of the `k`-th prism piece. -/
def theta (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2)) : Fin (n + 2) :=
  ⟨if (i : ℕ) ≤ (k : ℕ) then 0 else (i : ℕ) - (k : ℕ), by split_ifs <;> omega⟩

@[simp]
theorem theta_apply (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2)) :
    ((theta n k i : Fin (n + 2)) : ℕ) =
      if (i : ℕ) ≤ (k : ℕ) then 0 else (i : ℕ) - (k : ℕ) := rfl

/-- The interval coordinate of the `k`-th prism piece: `∑_{k < l} t l`. -/
def prismSnd (n : ℕ) (k : Fin (n + 1)) (t : ↥(stdSimplex ℝ (Fin (n + 2)))) : ℝ :=
  1 - (stdSimplex.map (theta n k) t : Fin (n + 2) → ℝ) 0

theorem prismSnd_nonneg (n : ℕ) (k : Fin (n + 1)) (t : ↥(stdSimplex ℝ (Fin (n + 2)))) :
    0 ≤ prismSnd n k t := by
  have h : (stdSimplex.map (theta n k) t : Fin (n + 2) → ℝ) 0 ≤ 1 := by
    have h1 := Finset.single_le_sum (f := fun j : Fin (n + 2) =>
        (stdSimplex.map (theta n k) t : Fin (n + 2) → ℝ) j)
      (fun i _ => (stdSimplex.map (theta n k) t).2.1 i) (Finset.mem_univ 0)
    have h2 : ∑ j : Fin (n + 2), (stdSimplex.map (theta n k) t : Fin (n + 2) → ℝ) j = 1 :=
      (stdSimplex.map (theta n k) t).2.2
    linarith
  simp only [prismSnd]
  linarith

theorem prismSnd_le_one (n : ℕ) (k : Fin (n + 1)) (t : ↥(stdSimplex ℝ (Fin (n + 2)))) :
    prismSnd n k t ≤ 1 := by
  have h : 0 ≤ (stdSimplex.map (theta n k) t : Fin (n + 2) → ℝ) 0 :=
    (stdSimplex.map (theta n k) t).2.1 0
  simp only [prismSnd]
  linarith

/-- **The `k`-th prism piece of `Δⁿ × I`.** -/
def pp (n : ℕ) (k : Fin (n + 1)) :
    C(↥(stdSimplex ℝ (Fin (n + 2))), ↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) where
  toFun t := (stdSimplex.map (psi n k) t,
    ⟨prismSnd n k t, ⟨prismSnd_nonneg n k t, prismSnd_le_one n k t⟩⟩)
  continuous_toFun := by
    refine Continuous.prodMk (stdSimplex.continuous_map _) (Continuous.subtype_mk ?_ _)
    have h1 : Continuous fun t : ↥(stdSimplex ℝ (Fin (n + 2))) =>
        ((stdSimplex.map (theta n k) t : ↥(stdSimplex ℝ (Fin (n + 2)))) : Fin (n + 2) → ℝ) :=
      continuous_subtype_val.comp (stdSimplex.continuous_map (theta n k))
    have h2 : Continuous fun t : ↥(stdSimplex ℝ (Fin (n + 2))) =>
        (stdSimplex.map (theta n k) t : Fin (n + 2) → ℝ) 0 :=
      (continuous_apply 0).comp h1
    exact continuous_const.sub h2

@[simp]
theorem pp_fst (n : ℕ) (k : Fin (n + 1)) (t : ↥(stdSimplex ℝ (Fin (n + 2)))) :
    (pp n k t).1 = stdSimplex.map (psi n k) t := rfl

@[simp]
theorem pp_snd (n : ℕ) (k : Fin (n + 1)) (t : ↥(stdSimplex ℝ (Fin (n + 2)))) :
    ((pp n k t).2 : ℝ) = prismSnd n k t := rfl

/-! ## The pointwise identities for the vertex maps -/

theorem psi_succAbove_zero (n : ℕ) :
    (psi n 0) ∘ (Fin.succAbove (0 : Fin (n + 2))) = id := by
  funext i
  ext
  simp only [Function.comp_apply, psi, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ, Fin.val_zero, id_eq]
  all_goals (split_ifs <;> omega)

theorem psi_succAbove_last (n : ℕ) :
    (psi n (Fin.last n)) ∘ (Fin.succAbove (Fin.last (n + 1))) = id := by
  funext i
  ext
  simp only [Function.comp_apply, psi, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ, Fin.val_last, id_eq]
  all_goals (split_ifs <;> omega)

theorem psi_succAbove_diag {m : ℕ} (k : Fin (m + 1)) :
    (psi (m + 1) k.castSucc) ∘ (Fin.succAbove k.castSucc.succ)
      = (psi (m + 1) k.succ) ∘ (Fin.succAbove k.castSucc.succ) := by
  funext i
  ext
  simp only [Function.comp_apply, psi, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ]
  all_goals (split_ifs <;> omega)

theorem psi_succAbove_lt {m : ℕ} (k : Fin (m + 2)) (f : Fin (m + 3))
    (hfk : (f : ℕ) < (k : ℕ)) :
    (psi (m + 1) k) ∘ (Fin.succAbove f)
      = (Fin.succAbove (⟨(f : ℕ), by omega⟩ : Fin (m + 2)))
          ∘ (psi m ⟨(k : ℕ) - 1, by omega⟩) := by
  funext i
  ext
  simp only [Function.comp_apply, psi, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ]
  all_goals (split_ifs <;> omega)

theorem psi_succAbove_gt {m : ℕ} (k : Fin (m + 2)) (f : Fin (m + 3))
    (hfk : (k : ℕ) + 1 < (f : ℕ)) :
    (psi (m + 1) k) ∘ (Fin.succAbove f)
      = (Fin.succAbove (⟨(f : ℕ) - 1, by omega⟩ : Fin (m + 2)))
          ∘ (psi m ⟨(k : ℕ), by omega⟩) := by
  funext i
  ext
  simp only [Function.comp_apply, psi, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ]
  all_goals (split_ifs <;> omega)

/-! ## The pointwise identities for the weight map -/

theorem theta_zero_ne_succ_zero (n : ℕ) (i : Fin (n + 1)) :
    theta n 0 (Fin.succAbove (0 : Fin (n + 2)) i) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : Fin (n + 2) => (x : ℕ)) h
  simp only [theta_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val,
    Fin.val_succ, Fin.val_zero] at h'
  all_goals (split_ifs at h' <;> omega)

theorem theta_last_eq_zero (n : ℕ) (i : Fin (n + 1)) :
    theta n (Fin.last n) (Fin.succAbove (Fin.last (n + 1)) i) = 0 := by
  ext
  simp only [theta_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val,
    Fin.val_succ, Fin.val_last, Fin.val_zero]
  all_goals (split_ifs <;> omega)

theorem theta_castSucc_zero_iff_succ_zero {m : ℕ} (k : Fin (m + 1)) (i : Fin (m + 2)) :
    (theta (m + 1) k.castSucc (Fin.succAbove k.castSucc.succ i) = 0 ↔
      theta (m + 1) k.succ (Fin.succAbove k.castSucc.succ i) = 0) := by
  simp only [Fin.ext_iff, Fin.val_zero, theta_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ]
  all_goals (split_ifs <;> omega)

theorem theta_lt_zero_iff {m : ℕ} (k : Fin (m + 2)) (f : Fin (m + 3))
    (hfk : (f : ℕ) < (k : ℕ)) (i : Fin (m + 2)) :
    (theta (m + 1) k (Fin.succAbove f i) = 0 ↔
      theta m ⟨(k : ℕ) - 1, by omega⟩ i = 0) := by
  simp only [Fin.ext_iff, Fin.val_zero, theta_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ]
  all_goals (split_ifs <;> omega)

theorem theta_gt_zero_iff {m : ℕ} (k : Fin (m + 2)) (f : Fin (m + 3))
    (hfk : (k : ℕ) + 1 < (f : ℕ)) (i : Fin (m + 2)) :
    (theta (m + 1) k (Fin.succAbove f i) = 0 ↔
      theta m ⟨(k : ℕ), by omega⟩ i = 0) := by
  simp only [Fin.ext_iff, Fin.val_zero, theta_apply, Fin.succAbove, Fin.lt_def, Fin.val_castSucc,
    apply_ite Fin.val, Fin.val_succ]
  all_goals (split_ifs <;> omega)


/-! ## The map-level face identities -/

theorem prodMap_apply_pair {α₁ α₂ β₁ β₂ : Type*} [TopologicalSpace α₁] [TopologicalSpace α₂]
    [TopologicalSpace β₁] [TopologicalSpace β₂] (f : C(α₁, α₂)) (g : C(β₁, β₂))
    (a : α₁) (b : β₁) : f.prodMap g (a, b) = (f a, g b) := rfl

theorem prod_map_apply_eta {α₁ α₂ β₁ β₂ : Type*} (f : α₁ → α₂) (g : β₁ → β₂) (p : α₁ × β₁) :
    Prod.map f g p = (f p.1, g p.2) := rfl

/-- The top inclusion `z ↦ (z,1)`. -/
def topIncl (n : ℕ) :
    C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) where
  toFun z := (z, 1)
  continuous_toFun := continuous_id.prodMk continuous_const

/-- The bottom inclusion `z ↦ (z,0)`. -/
def botIncl (n : ℕ) :
    C(↥(stdSimplex ℝ (Fin (n + 1))), ↥(stdSimplex ℝ (Fin (n + 1))) × unitInterval) where
  toFun z := (z, 0)
  continuous_toFun := continuous_id.prodMk continuous_const

@[simp]
theorem topIncl_apply (n : ℕ) (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    topIncl n z = (z, 1) := rfl

@[simp]
theorem botIncl_apply (n : ℕ) (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    botIncl n z = (z, 0) := rfl

theorem pp_coface_zero_zero (n : ℕ) :
    (pp n 0).comp (coface n (0 : Fin (n + 2))) = topIncl n := by
  apply ContinuousMap.ext
  intro z
  refine Prod.ext ?_ ?_
  · simp only [ContinuousMap.comp_apply, pp_fst, coface_apply, topIncl_apply]
    rw [stdSimplex.map_comp_apply, psi_succAbove_zero, stdSimplex.map_id_apply]
  · apply Subtype.ext
    show (prismSnd n 0 (stdSimplex.map (Fin.succAbove 0) z) : ℝ) = 1
    rw [prismSnd, stdSimplex.map_comp_apply]
    rw [stdSimplex.map_apply_zero_of_ne (theta n 0 ∘ Fin.succAbove 0)
      (fun i => theta_zero_ne_succ_zero n i) z]
    norm_num

theorem pp_coface_last_last (n : ℕ) :
    (pp n (Fin.last n)).comp (coface n (Fin.last (n + 1))) = botIncl n := by
  apply ContinuousMap.ext
  intro z
  refine Prod.ext ?_ ?_
  · simp only [ContinuousMap.comp_apply, pp_fst, coface_apply, botIncl_apply]
    rw [stdSimplex.map_comp_apply, psi_succAbove_last, stdSimplex.map_id_apply]
  · apply Subtype.ext
    show (prismSnd n (Fin.last n) (stdSimplex.map (Fin.succAbove (Fin.last (n + 1))) z) : ℝ) = 0
    rw [prismSnd, stdSimplex.map_comp_apply]
    rw [stdSimplex.map_apply_zero_of_eq (theta n (Fin.last n) ∘ Fin.succAbove (Fin.last (n + 1)))
      (fun i => theta_last_eq_zero n i) z]
    have h1 : ∑ i, (z : Fin (n + 1) → ℝ) i = 1 := z.2.2
    rw [h1]
    norm_num

theorem pp_coface_diag {m : ℕ} (k : Fin (m + 1)) :
    (pp (m + 1) k.castSucc).comp (coface (m + 1) k.castSucc.succ)
      = (pp (m + 1) k.succ).comp (coface (m + 1) k.castSucc.succ) := by
  apply ContinuousMap.ext
  intro z
  refine Prod.ext ?_ ?_
  · simp only [ContinuousMap.comp_apply, pp_fst, coface_apply, Prod.map_fst]
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, psi_succAbove_diag k]
  · apply Subtype.ext
    show (prismSnd (m + 1) k.castSucc (stdSimplex.map (Fin.succAbove k.castSucc.succ) z) : ℝ)
      = prismSnd (m + 1) k.succ (stdSimplex.map (Fin.succAbove k.castSucc.succ) z)
    rw [prismSnd, prismSnd]
    congr 1
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
    exact stdSimplex.map_apply_zero_eq_of _ _ (fun i => theta_castSucc_zero_iff_succ_zero k i) z

theorem pp_coface_lt {m : ℕ} (k : Fin (m + 2)) (f : Fin (m + 3))
    (hfk : (f : ℕ) < (k : ℕ)) :
    (pp (m + 1) k).comp (coface (m + 1) f)
      = ((coface m ⟨(f : ℕ), by omega⟩).prodMap (ContinuousMap.id unitInterval)).comp
          (pp m ⟨(k : ℕ) - 1, by omega⟩) := by
  apply ContinuousMap.ext
  intro z
  refine Prod.ext ?_ ?_
  · simp only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.id_apply,
      pp_fst, coface_apply, Prod.map_fst]
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, psi_succAbove_lt k f hfk]
  · apply Subtype.ext
    show (prismSnd (m + 1) k (stdSimplex.map (Fin.succAbove f) z) : ℝ)
      = prismSnd m ⟨(k : ℕ) - 1, by omega⟩ z
    rw [prismSnd, prismSnd]
    congr 1
    rw [stdSimplex.map_comp_apply]
    exact stdSimplex.map_apply_zero_eq_of _ _ (fun i => theta_lt_zero_iff k f hfk i) z

theorem pp_coface_gt {m : ℕ} (k : Fin (m + 2)) (f : Fin (m + 3))
    (hfk : (k : ℕ) + 1 < (f : ℕ)) :
    (pp (m + 1) k).comp (coface (m + 1) f)
      = ((coface m ⟨(f : ℕ) - 1, by omega⟩).prodMap (ContinuousMap.id unitInterval)).comp
          (pp m ⟨(k : ℕ), by omega⟩) := by
  apply ContinuousMap.ext
  intro z
  refine Prod.ext ?_ ?_
  · simp only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply, ContinuousMap.id_apply,
      pp_fst, coface_apply, Prod.map_fst]
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply, psi_succAbove_gt k f hfk]
  · apply Subtype.ext
    show (prismSnd (m + 1) k (stdSimplex.map (Fin.succAbove f) z) : ℝ)
      = prismSnd m ⟨(k : ℕ), by omega⟩ z
    rw [prismSnd, prismSnd]
    congr 1
    rw [stdSimplex.map_comp_apply]
    exact stdSimplex.map_apply_zero_eq_of _ _ (fun i => theta_gt_zero_iff k f hfk i) z


/-! ## The face identities at the level of simplices of `X`

For a family `SimpHom.G` of homotopies, the `k`-th prism piece of an `n`-simplex `σ` is the
`(n+1)`-simplex `prismSimplex H n k σ = (G n σ) ∘ pp n k`.  Composing the geometric identities of
the previous section with `G n σ`, and using the compatibility `SimpHom.hside` of the family `G`,
gives the face identities needed for the chain contraction.
-/

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- The `k`-th prism piece of the homotopy of an `n`-simplex: an `(n+1)`-simplex of `X`. -/
def prismSimplex (H : SimpHom X A N) (n : ℕ) (k : Fin (n + 1))
    (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X)) : C(↥(stdSimplex ℝ (Fin (n + 2))), X) :=
  (H.G n s).comp (pp n k)

/-- The "top" simplex of the homotopy: `z ↦ G n s (z,1)`. -/
def topSimplex (H : SimpHom X A N) (n : ℕ)
    (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X)) : C(↥(stdSimplex ℝ (Fin (n + 1))), X) :=
  ⟨fun z => H.G n s (z, 1), (H.G n s).continuous.comp (continuous_id.prodMk continuous_const)⟩

@[simp]
theorem topSimplex_apply (H : SimpHom X A N) (n : ℕ)
    (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X)) (z : ↥(stdSimplex ℝ (Fin (n + 1)))) :
    topSimplex H n s z = H.G n s (z, 1) := rfl

/-- The `0`-th face of the `0`-th prism piece is the top simplex. -/
theorem prismSimplex_coface_zero (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N)
    (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X)) :
    (prismSimplex H n 0 s).comp (coface n (0 : Fin (n + 2))) = topSimplex H n s := by
  unfold prismSimplex topSimplex
  rw [ContinuousMap.comp_assoc, pp_coface_zero_zero n]
  refine ContinuousMap.ext (fun z => ?_)
  exact congrArg (fun w => H.G n s w) rfl

/-- The last face of the last prism piece is the simplex itself. -/
theorem prismSimplex_coface_last (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N)
    (s : C(↥(stdSimplex ℝ (Fin (n + 1))), X)) :
    (prismSimplex H n (Fin.last n) s).comp (coface n (Fin.last (n + 1))) = s := by
  unfold prismSimplex
  rw [ContinuousMap.comp_assoc, pp_coface_last_last n]
  refine ContinuousMap.ext (fun z => ?_)
  exact H.ht0 n hn s z

/-- The `(k+1)`-st face is shared by the `k`-th and `(k+1)`-st prism piece. -/
theorem prismSimplex_coface_diag (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (k : Fin (m + 1)) (s : C(↥(stdSimplex ℝ (Fin (m + 2))), X)) :
    (prismSimplex H (m + 1) k.castSucc s).comp (coface (m + 1) k.castSucc.succ)
      = (prismSimplex H (m + 1) k.succ s).comp (coface (m + 1) k.castSucc.succ) := by
  unfold prismSimplex
  rw [ContinuousMap.comp_assoc, ContinuousMap.comp_assoc, pp_coface_diag k]

/-- For `f < k`, the `f`-th face of the `k`-th prism piece is the prism piece of the `f`-th face. -/
theorem prismSimplex_coface_lt (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (k : Fin (m + 2)) (f : Fin (m + 3)) (hfk : (f : ℕ) < (k : ℕ))
    (s : C(↥(stdSimplex ℝ (Fin (m + 2))), X)) :
    (prismSimplex H (m + 1) k s).comp (coface (m + 1) f)
      = prismSimplex H m ⟨(k : ℕ) - 1, by omega⟩ (s.comp (coface m ⟨(f : ℕ), by omega⟩)) := by
  unfold prismSimplex
  rw [ContinuousMap.comp_assoc, pp_coface_lt k f hfk, ← ContinuousMap.comp_assoc]
  congr 1
  refine ContinuousMap.ext (fun p => ?_)
  obtain ⟨z, t⟩ := p
  exact H.hside m (by omega) s ⟨(f : ℕ), by omega⟩ z t

/-- For `f > k+1`, the `f`-th face of the `k`-th prism piece is the prism piece of the
`(f-1)`-st face. -/
theorem prismSimplex_coface_gt (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (k : Fin (m + 2)) (f : Fin (m + 3)) (hfk : (k : ℕ) + 1 < (f : ℕ))
    (s : C(↥(stdSimplex ℝ (Fin (m + 2))), X)) :
    (prismSimplex H (m + 1) k s).comp (coface (m + 1) f)
      = prismSimplex H m ⟨(k : ℕ), by omega⟩ (s.comp (coface m ⟨(f : ℕ) - 1, by omega⟩)) := by
  unfold prismSimplex
  rw [ContinuousMap.comp_assoc, pp_coface_gt k f hfk, ← ContinuousMap.comp_assoc]
  congr 1
  refine ContinuousMap.ext (fun p => ?_)
  obtain ⟨z, t⟩ := p
  exact H.hside m (by omega) s ⟨(f : ℕ) - 1, by omega⟩ z t

end

end Work.Serre
