import Mathlib
import Submission.SieveMargKey
import Submission.TensorThin

open scoped BigOperators Topology
open Filter Finset MeasureTheory

set_option maxHeartbeats 2000000

/-!
# §5.3: the criterion's `hkey` from the thin tensor data and the variational certificate

`Submission/SieveMargKey.lean` proves `hkey_of_split_tensorData`, whose inputs are

* the thin tensor data of §5.3 (components with marginal support radius `β`, thin of width `6η`,
  uniformly bounded by `B`, marginal sum bounded by `Bmarg`),
* the split `J₁`-sets `splitBox Mr cc i` with `Mr = max (12η) β`,
* the variational certificate `IFuncOrth k F + ef + Mg < Σ_i JFunc k i cc F`,
* the two budgets (`J̃ ≈ JFunc` and the `J₂`-loss slab).

This module performs the concrete instantiation: with `aa = cc - 18η(k-1)`, `ef = δ`,
`Bm = 6η·B·Bmarg`, the `J₂`-marginal sup bound of `hkey_of_split_tensorData` follows from the
thin structure via `abs_tenP_le_thin`, and `hβlow` follows from `Mr j l ≤ β j l + 12η`.

The single remaining *quantitative* input of the whole §5.3 chapter is therefore the
certificate inequality `IFuncOrth k F + δ + Mg < Σ_i JFunc k i cc F` together with the
resulting budget `k·(6η·B·Bmarg)²·vol(slab) < Mg/2` (discharged once the localisation exports an
explicit marginal bound — see
`Commons.Analysis.TensorApprox.exists_tensor_localization_orthant_thin_marg_explicit`).
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The sum over the subtype `{l // l ≠ i}` equals the sum over `univ.erase i` (stated in the
form used for rewriting). -/
theorem sum_subtype_ne_eq_sum_erase {k : ℕ} (i : Fin k) (g : Fin k → ℝ) :
    (∑ l : {l : Fin k // l ≠ i}, g l.1) = ∑ l ∈ (Finset.univ.erase i), g l :=
  (Finset.sum_subtype (Finset.univ.erase i) (fun x => by simp [Finset.mem_erase]) g).symm

/-- **`hkey` from the thin tensor data and the variational certificate.**

`Mr := fun j i => max (12η) (β j i)` and `Sf i := splitBox Mr cc i` are the `J₁`-sets of the
paper; the `J₂`-loss bound uses `abs_tenP_le_thin` with the explicit marginal constant
`Bm := 6η·B·Bmarg`. -/
theorem hkey_of_thin_tensorData {J k : ℕ} {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0)
    (c : Fin J → ℝ) (β : Fin J → Fin k → ℝ)
    {F : (Fin k → ℝ) → ℝ} {η cc aa ef eJ B Bmarg Mg : ℝ}
    (hη : 0 ≤ η) (hk : 1 ≤ k) (hk2 : 2 ≤ k)
    (hβ0 : ∀ j i, 0 ≤ β j i)
    (hthin : ∀ j l u, 0 ≤ u → G j l u ≠ 0 → β j l - 6 * η < u ∧ u < β j l)
    (hB0 : 0 ≤ B) (hBbd : ∀ j l u, |G j l u| ≤ B)
    (hBmarg0 : 0 ≤ Bmarg)
    (hBmarg : ∀ (i : Fin k) (t : {l : Fin k // l ≠ i} → ℝ),
      ∑ j, |c j| * ∏ l : {l : Fin k // l ≠ i}, |G j (l : Fin k) (t l)| ≤ Bmarg)
    (haa : 0 ≤ aa) (hac : aa ≤ cc) (haacc : aa + 18 * η * (k - 1) ≤ cc)
    (hJapprox : ∀ i, |(∫ t : ({l : Fin k // l ≠ i} → ℝ),
        (tenP G c i Finset.univ t) ^ 2 * margInd k i cc t) - JFunc k i cc F| ≤ eJ)
    (hcert : IFuncOrth k F + ef + Mg < ∑ i : Fin k, JFunc k i cc F)
    (hbudJ : (k : ℝ) * eJ ≤ Mg / 2)
    (hbudL : (k : ℝ) * ((6 * η * B * Bmarg) ^ 2 * ((cc ^ (k - 1) - aa ^ (k - 1)) /
        (Nat.factorial (k - 1) : ℝ))) < Mg / 2)
    (hα : tpAlpha c (fun j i => anti ψ (G j) i) < IFuncOrth k F + ef) :
    tpAlpha c (fun j i => anti ψ (G j) i)
      < ∑ i : Fin k, tpBetaSplit (splitBox (fun j i => max (12 * η) (β j i)) cc i) c
          (fun j i => anti ψ (G j) i) i := by
  classical
  have hGi : ∀ j i, Integrable (G j i) :=
    fun j i => (hGc j i).integrable_of_hasCompactSupport (hGcs j i)
  have hBm : ∀ i : Fin k, ∀ t : ({l : Fin k // l ≠ i} → ℝ), (∀ l, 0 ≤ t l) →
      |tenP G c i (Finset.univ \ splitBox (fun j i => max (12 * η) (β j i)) cc i) t|
        ≤ 6 * η * B * Bmarg := by
    intro i t ht
    exact abs_tenP_le_thin G c i
      (Finset.univ \ splitBox (fun j i => max (12 * η) (β j i)) cc i) β hη hthin hBbd
      (hBmarg i) hB0 hBmarg0 t ht
  refine hkey_of_split_tensorData hψ0 hψ1 G hGc hGcs hGi hGv c
    (fun j i => max (12 * η) (β j i)) β _ hη hk hk2 hthin
    (fun j l => le_max_right _ _) ?_ ?_ hBm haa hac hJapprox hcert hbudJ ?_ hbudL hα
  · -- `hSf`: the `J₁`-set consists of the components with small marginal radius
    intro i j hj
    have h := mem_splitBox.mp hj
    rwa [show (∑ l : {l : Fin k // l ≠ i}, max (12 * η) (β j (l : Fin k)))
        = ∑ l ∈ (Finset.univ.erase i), max (12 * η) (β j l) from
      (Finset.sum_subtype (Finset.univ.erase i) (fun x => by simp [Finset.mem_erase])
        (fun l => max (12 * η) (β j l))).symm]
  · -- `hβlow`: on the complement, `max (12η) β ≤ β + 12η` forces `aa + 6η(k-1) ≤ Σβ`
    intro i j hj
    have hnot : ¬ (∑ l ∈ Finset.univ.erase i, max (12 * η) (β j l) < cc) :=
      fun h => hj (mem_splitBox.mpr h)
    have hcc : cc ≤ ∑ l ∈ Finset.univ.erase i, max (12 * η) (β j l) := not_lt.mp hnot
    have hle : ∑ l ∈ Finset.univ.erase i, max (12 * η) (β j l)
        ≤ ∑ l ∈ Finset.univ.erase i, (β j l + 12 * η) :=
      Finset.sum_le_sum fun l _ => max_le (by have := hβ0 j l; linarith) (by linarith)
    have hcard : ((Finset.univ : Finset (Fin k)).erase i).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hsum2 : ∑ l ∈ Finset.univ.erase i, (β j l + 12 * η)
        = (∑ l ∈ Finset.univ.erase i, β j l) + ((k - 1 : ℕ) : ℝ) * (12 * η) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
    have hcast : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; norm_num
    have hmain : aa + 6 * η * ((k : ℝ) - 1) ≤ ∑ l ∈ Finset.univ.erase i, β j l := by
      have h1 : aa + 18 * η * ((k : ℝ) - 1) ≤ cc := haacc
      nlinarith [hcc, hle, hsum2, hη, hBmarg0]
    rwa [show (∑ l : {l : Fin k // l ≠ i}, β j (l : Fin k))
        = ∑ l ∈ (Finset.univ.erase i), β j l from
      (Finset.sum_subtype (Finset.univ.erase i) (fun x => by simp [Finset.mem_erase])
        (fun l => β j l)).symm]
  · -- positivity of the marginal constant
    positivity

end Commons.NumberTheory.MaynardSieve
