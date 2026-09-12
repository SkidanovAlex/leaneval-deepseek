import Mathlib
import Submission.GeometryOfNumbers.WedgeBlocks
import Submission.GeometryOfNumbers.WedgeGeneralE1
import Submission.Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero

/-!
# Higher blocks of a graph wedge: paper Lemma 2 (coordinate graph model)

Setup (as in `WedgeBlocks`): `e : Fin k → ℝᵈ` with `e j ∈ x₀ = modelX ℓ`, `c : Fin k → ℝᵈ`
with `c j ∈ x₀ᗮ`, and the graph wedge `w = ιMulti (e + c)`.  Expanding `w` by
multilinearity as a sum over subsets `T ⊆ Fin k` (slots taking the `c`-factor, commons
`iMulti_sum_swap_expansion`), the `r`-th block of `w` is the sub-sum over the subsets of
cardinality `r` (`blockElem_r_of_graph`).

**Lemma 2 (graph form, Plücker/multilinear control of higher blocks)**: for `1 ≤ r ≤ k`,
`‖block_r w‖ ≤ Σ_{|T|=r} Π_{i∈T} ‖c i‖` (`blockElem_r_of_graph_norm_le`), hence — when `e`
is orthonormal so that `‖block₁ w‖² = Σᵢ‖c i‖²` — `‖block_r w‖ ≤ 2^k · ‖block₁ w‖^r`
(`graph_blockElem_r_le_block1`).  For a general pure tensor `w = ιMulti u` with
`span(range u) ⊓ x₀ᗮ = ⊥`, passing through the orthonormal graph representation
(`WedgeGeneralE1.exists_graph_rep`) and scalar proportionality
(commons `iMulti_proportional_of_span_eq`) gives the paper's inequality
`‖w₀‖^{r−1}‖w_r‖ ≤ C · ‖w₁‖^r` (`pureTensor_blockElem_r_le`).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.WedgeGeneralE1

namespace Submission.WedgeBlocks

variable {d k : ℕ}

/-- The cardinality of the high (`≥ ℓ`) columns of the subset `I`, counted through the
enumeration `σ = ofFinEmbEquiv.symm I`, equals the block degree of `I`. -/
lemma enum_high_card_eq_block {d k ℓ : ℕ} (r : ℕ) (I : IDX d k) :
    (((Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
        ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))).card = r) ↔
      I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) r := by
  classical
  have hb := card_filter_enum_ge (d := d) (k := k) (I := I) (ℓ := ℓ)
  constructor
  · intro h
    simp only [blockFinset, Finset.mem_univ, Finset.mem_filter, true_and]
    exact hb.symm.trans h
  · intro hI
    have hc : (((I : Finset (Fin d)).filter (fun i : Fin d => ℓ ≤ i.val)).card) = r := by
      simpa [blockFinset] using hI
    exact hb.trans hc

/-- **Block decomposition of a graph wedge, general degree `r`**: the `r`-th block of
`w = ιMulti (e + c)` (factors `e j ∈ x₀`, `c j ∈ x₀ᗮ`) is the sum over the subsets
`T ⊆ Fin k` of cardinality `r` of the wedges taking the `c`-factor exactly on `T`. -/
lemma blockElem_r_of_graph (ℓ : ℕ) (r : ℕ) (e c : Fin k → RD d)
    (he_mem : ∀ r, e r ∈ modelX ℓ) (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) r =
      ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
        (fun T : Finset (Fin k) => exteriorPower.ιMulti ℝ k
          (fun a : Fin k => if a ∈ T then c a else e a)) := by
  classical
  apply wk_ext (d := d) (k := k)
  intro I
  let A : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k =>
    ℓ ≤ ((Set.powersetCard.ofFinEmbEquiv.symm I j : Fin d).val))
  have hAr_iff : (A.card = r) ↔ I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) r := by
    simpa [A] using (enum_high_card_eq_block (d := d) (k := k) (ℓ := ℓ) r I)
  rw [wcoord_blockElem (d := d) (k := k) (ℓ := ℓ)
    (w := exteriorPower.ιMulti ℝ k (fun a : Fin k => e a + c a)) (s := I) (j := r)]
  by_cases hI : I ∈ blockFinset (d := d) (k := k) (ℓ := ℓ) r
  · rw [if_pos hI]
    have hAr : A.card = r := hAr_iff.mpr hI
    rw [Commons.Analysis.InnerProductSpace.iMulti_sum_swap_expansion (k := k) (E := RD d) e c]
    have hwsum : wcoord (d := d) (k := k)
        ((Finset.univ : Finset (Finset (Fin k))).sum (fun T : Finset (Fin k) =>
          exteriorPower.ιMulti ℝ k (fun a : Fin k => if a ∈ T then c a else e a))) I =
        (Finset.univ : Finset (Finset (Fin k))).sum (fun T : Finset (Fin k) =>
          wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
            (fun a : Fin k => if a ∈ T then c a else e a)) I) := by
        simp [wcoord]
    rw [hwsum]
    rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Finset (Fin k))))
      (p := fun T : Finset (Fin k) => T.card = r)
      (f := fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
        (fun a : Fin k => if a ∈ T then c a else e a)) I)]
    have hz : ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card ≠ r)).sum
        (fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
          (fun a : Fin k => if a ∈ T then c a else e a)) I) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      have hTne : T.card ≠ r := (Finset.mem_filter.mp hT).2
      have hne : T.card ≠ A.card := by
        rw [hAr]
        exact hTne
      exact wcoord_wedge_zero_of_block_mismatch (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth T I
        (by simpa [A] using hne)
    rw [hz]
    have hwsum2 : wcoord (d := d) (k := k)
        (((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
          (fun T : Finset (Fin k) => exteriorPower.ιMulti ℝ k
            (fun a : Fin k => if a ∈ T then c a else e a))) I =
        ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
          (fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
            (fun a : Fin k => if a ∈ T then c a else e a)) I) := by
        simp [wcoord]
    simpa using hwsum2.symm
  · rw [if_neg hI]
    have hAnr : A.card ≠ r := by
      intro h
      exact hI (hAr_iff.mp h)
    have hz : ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
        (fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
          (fun a : Fin k => if a ∈ T then c a else e a)) I) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      have hTr : T.card = r := (Finset.mem_filter.mp hT).2
      have hne : T.card ≠ A.card := by
        rw [hTr]
        exact hAnr.symm
      exact wcoord_wedge_zero_of_block_mismatch (d := d) (k := k) (ℓ := ℓ) e c he_mem hc_orth T I
        (by simpa [A] using hne)
    have hwsum2 : wcoord (d := d) (k := k)
        (((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
          (fun T : Finset (Fin k) => exteriorPower.ιMulti ℝ k
            (fun a : Fin k => if a ∈ T then c a else e a))) I = 0 := by
      have hwsum' : wcoord (d := d) (k := k)
          (((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
            (fun T : Finset (Fin k) => exteriorPower.ιMulti ℝ k
              (fun a : Fin k => if a ∈ T then c a else e a))) I =
          ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
            (fun T : Finset (Fin k) => wcoord (d := d) (k := k) (exteriorPower.ιMulti ℝ k
              (fun a : Fin k => if a ∈ T then c a else e a)) I) := by
          simp [wcoord]
      rw [hwsum', hz]
    exact hwsum2.symm


/-- **Norm of the `r`-th block of a graph wedge**: bounded by the sum over the `r`-subsets
`T` of the products of the norms of the `c`-factors in `T` (times the unit norms of the
`e`-factors outside). -/
lemma blockElem_r_of_graph_norm_le (ℓ : ℕ) (r : ℕ) (e c : Fin k → RD d)
    (he_mem : ∀ r, e r ∈ modelX ℓ) (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) r‖ ≤
      ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).sum
        (fun T : Finset (Fin k) => ∏ i : Fin k, if i ∈ T then ‖c i‖ else ‖e i‖) := by
  classical
  let S : Finset (Finset (Fin k)) := (Finset.univ : Finset (Finset (Fin k))).filter
    (fun T : Finset (Fin k) => T.card = r)
  calc
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) r‖
        = ‖S.sum (fun T : Finset (Fin k) => exteriorPower.ιMulti ℝ k
            (fun a : Fin k => if a ∈ T then c a else e a))‖ := by
            rw [blockElem_r_of_graph (d := d) (k := k) ℓ r e c he_mem hc_orth]
    _ ≤ S.sum (fun T : Finset (Fin k) => ‖exteriorPower.ιMulti ℝ k
          (fun a : Fin k => if a ∈ T then c a else e a)‖) := by
          exact norm_sum_le _ _
    _ ≤ S.sum (fun T : Finset (Fin k) => ∏ i : Fin k, if i ∈ T then ‖c i‖ else ‖e i‖) := by
          apply Finset.sum_le_sum
          intro T hT
          have hw := Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
            (fun a : Fin k => if a ∈ T then c a else e a)
          calc
            ‖exteriorPower.ιMulti ℝ k (fun a : Fin k => if a ∈ T then c a else e a)‖
                ≤ ∏ i : Fin k, ‖(fun a : Fin k => if a ∈ T then c a else e a) i‖ := hw
            _ = ∏ i : Fin k, (if i ∈ T then ‖c i‖ else ‖e i‖) := by
                apply Finset.prod_congr rfl
                intro i hi
                by_cases hit : i ∈ T <;> simp [hit]

/-- Number of `r`-subsets of `Fin k` is at most `2^k`. -/
lemma card_filter_card_le_two_pow_nat {k : ℕ} (r : ℕ) :
    ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).card ≤
      2 ^ k := by
  classical
  calc
    ((Finset.univ : Finset (Finset (Fin k))).filter (fun T : Finset (Fin k) => T.card = r)).card ≤
        (Finset.univ : Finset (Finset (Fin k))).card := Finset.card_filter_le _ _
    _ = Fintype.card (Finset (Fin k)) := by simp
    _ = 2 ^ k := by simp [Fintype.card_finset]

/-- **Lemma 2 (graph form)**: for an orthonormal `e ⊆ x₀` and `c ⊆ x₀ᗮ`, the `r`-th block
of the graph wedge `w = ιMulti (e + c)` satisfies `‖w_r‖ ≤ 2^k · ‖w₁‖^r` for `r ≥ 1`. -/
lemma graph_blockElem_r_le_block1 {d k : ℕ} (ℓ : ℕ) (r : ℕ) (hr : 1 ≤ r)
    (e c : Fin k → RD d) (he : Orthonormal ℝ e) (he_mem : ∀ r, e r ∈ modelX ℓ)
    (hc_orth : ∀ r, c r ∈ (modelX ℓ)ᗮ) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
      (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) r‖ ≤
      (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖ ^ r := by
  classical
  let b1 : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ)
    (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖
  have hb1nonneg : 0 ≤ b1 := by dsimp [b1]; exact norm_nonneg _
  have hsq : b1 ^ 2 = (Finset.univ : Finset (Fin k)).sum (fun j => ‖c j‖ ^ 2) := by
    dsimp [b1]
    exact blockElem_one_of_graph_normSq (d := d) (k := k) ℓ e c he he_mem hc_orth
  have hc_le : ∀ i : Fin k, ‖c i‖ ≤ b1 := by
    intro i
    have h1 : ‖c i‖ ^ 2 ≤ b1 ^ 2 := by
      rw [hsq]
      exact Finset.single_le_sum (fun j hj => sq_nonneg (‖c j‖)) (Finset.mem_univ i)
    exact (sq_le_sq₀ (norm_nonneg (c i)) hb1nonneg).mp h1
  have he1 : ∀ i : Fin k, ‖e i‖ = 1 := by
    intro i
    exact he.1 i
  have hle := blockElem_r_of_graph_norm_le (d := d) (k := k) ℓ r e c he_mem hc_orth
  let S : Finset (Finset (Fin k)) := (Finset.univ : Finset (Finset (Fin k))).filter
    (fun T : Finset (Fin k) => T.card = r)
  have hterm : ∀ T ∈ S, (∏ i : Fin k, if i ∈ T then ‖c i‖ else ‖e i‖) ≤ b1 ^ T.card := by
    intro T hT
    calc
      (∏ i : Fin k, if i ∈ T then ‖c i‖ else ‖e i‖)
          = (∏ i : Fin k, if i ∈ T then ‖c i‖ else 1) := by
              apply Finset.prod_congr rfl
              intro i hi
              by_cases hit : i ∈ T <;> simp [hit, he1]
      _ = (∏ i : Fin k, if i ∈ T then ‖c i‖ else 1) := rfl
      _ = (∏ i ∈ T, ‖c i‖) := by simp
      _ ≤ (∏ i ∈ T, b1) := by
              apply Finset.prod_le_prod (s := T) (f := fun i : Fin k => ‖c i‖) (g := fun _ : Fin k => b1)
              · intro i hi
                exact norm_nonneg (c i)
              · intro i hi
                exact hc_le i
      _ = b1 ^ T.card := by
              simp [Finset.prod_const]
  calc
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) r‖
        ≤ S.sum (fun T : Finset (Fin k) => ∏ i : Fin k, if i ∈ T then ‖c i‖ else ‖e i‖) := by
            simpa [S] using hle
    _ ≤ S.sum (fun T : Finset (Fin k) => b1 ^ T.card) := by
            exact Finset.sum_le_sum (fun T hT => hterm T hT)
    _ = S.sum (fun T : Finset (Fin k) => b1 ^ r) := by
            apply Finset.sum_congr rfl
            intro T hT
            have hTr : T.card = r := (Finset.mem_filter.mp hT).2
            rw [hTr]
    _ ≤ (2 : ℝ) ^ k * b1 ^ r := by
            have hcard : S.card ≤ 2 ^ k := by
              simpa [S] using (card_filter_card_le_two_pow_nat (k := k) r)
            have hsmul : S.sum (fun _ : Finset (Fin k) => b1 ^ r) = (S.card : ℝ) * (b1 ^ r) := by simp
            rw [hsmul]
            have hbpow : 0 ≤ b1 ^ r := pow_nonneg hb1nonneg r
            have hcardR : (S.card : ℝ) ≤ (2 : ℝ) ^ k := by
              have hconv : (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k := by
                rw [Nat.cast_pow]
                norm_num
              rw [← hconv]
              exact_mod_cast hcard
            exact (mul_le_mul_of_nonneg_right hcardR hbpow)
    _ = (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.ιMulti ℝ k (fun r : Fin k => e r + c r)) 1‖ ^ r := by
            simp [b1]

/-- **Lemma 2 (general pure tensor)**: for an independent `u : Fin k → ℝᵈ` spanning a plane
`V` transverse to `x₀ᗮ` (`V ⊓ x₀ᗮ = ⊥`), the pure tensor `w = ιMulti u` satisfies the
Plücker-type control `‖w₀‖^{r−1}‖w_r‖ ≤ 2^k · ‖w₁‖^r` for `r ≥ 1`.  (Reduces to the graph
form through the orthonormal graph representation `u = λ(e + coff)` of `exists_graph_rep`;
block norms are multiplied by the common scalar `|λ|`.) -/
lemma pureTensor_blockElem_r_le {d k : ℕ} (ℓ : ℕ) (r : ℕ) (hk : 0 < k) (hr : 1 ≤ r)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ ^ (r - 1) *
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) r‖ ≤
      (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ^ r := by
  classical
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  rcases exists_graph_rep (d := d) (k := k) ℓ hk u hu hbot with ⟨e, coff, he_ON, he_x0, coff_orth, hspan⟩
  let g : Fin k → RD d := fun j => e j + coff j
  let w' : WK d k := exteriorPower.ιMulti ℝ k g
  have hw'0 : blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 = exteriorPower.ιMulti ℝ k e := by
    dsimp [w', g]
    exact blockElem_zero_of_graph (d := d) (k := k) ℓ e coff he_x0 coff_orth
  have hw'ne : w' ≠ 0 := by
    intro hz
    have h0 : blockElem (d := d) (k := k) (ℓ := ℓ) w' 0 = 0 := by rw [hz]; simp
    rw [hw'0] at h0
    have hn : ‖exteriorPower.ιMulti ℝ k e‖ ≠ 0 := by
      rw [Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he_ON hk]
      norm_num
    exact hn (by simp [h0])
  have hgLI : LinearIndependent ℝ g :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero g hw'ne
  have hspan' : Submodule.span ℝ (Set.range u) = Submodule.span ℝ (Set.range g) := by
    simpa [g] using hspan.symm
  rcases Commons.LinearAlgebra.Alternating.iMulti_proportional_of_span_eq
      (𝕜 := ℝ) (M := RD d) u g hu hgLI hspan' with ⟨lam, hlam0, hprop⟩
  have hprop_j : ∀ j : ℕ, blockElem (d := d) (k := k) (ℓ := ℓ) w j =
      lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' j := by
    intro j
    have hc := congrArg (fun z : WK d k => blockElem (d := d) (k := k) (ℓ := ℓ) z j) hprop
    simpa [w, w', blockElem_smul] using hc
  have hb0' : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ = 1 := by
    rw [hw'0]
    exact Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal e he_ON hk
  have hn0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ = |lam| := by
    calc
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖
          = ‖lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ := by rw [hprop_j 0]
      _ = |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 0‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = |lam| := by rw [hb0', mul_one]
  have hn1 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ = |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ := by
    calc
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖
          = ‖lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ := by rw [hprop_j 1]
      _ = |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ := by
            rw [norm_smul, Real.norm_eq_abs]
  have hgr := graph_blockElem_r_le_block1 (d := d) (k := k) ℓ r hr e coff he_ON he_x0 coff_orth
  have hgr' : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' r‖ ≤
      (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r := by
    simpa [w', g] using hgr
  have hnr : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ ≤
      |lam| * (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r := by
    calc
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖
          = |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' r‖ := by
              calc
                ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖
                    = ‖lam • blockElem (d := d) (k := k) (ℓ := ℓ) w' r‖ := by rw [hprop_j r]
                _ = |lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' r‖ := by
                      rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |lam| * ((2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r) := by
            exact mul_le_mul_of_nonneg_left hgr' (abs_nonneg lam)
      _ = |lam| * (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r := by ring
  have hpow : |lam| ^ (r - 1) * |lam| = |lam| ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ^ (r - 1) *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖
        = |lam| ^ (r - 1) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w r‖ := by
            rw [hn0]
    _ ≤ |lam| ^ (r - 1) *
          (|lam| * (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r) := by
          exact mul_le_mul_of_nonneg_left hnr (pow_nonneg (abs_nonneg lam) (r - 1))
    _ = (2 : ℝ) ^ k * (|lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖) ^ r := by
          have hmain :
              |lam| ^ (r - 1) *
                (|lam| * (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r) =
              (2 : ℝ) ^ k * (|lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖) ^ r := by
            calc
              |lam| ^ (r - 1) * (|lam| * (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r)
                  = (|lam| ^ (r - 1) * |lam|) * (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r := by ring
              _ = |lam| ^ r * (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖ ^ r := by rw [hpow]
              _ = (2 : ℝ) ^ k * (|lam| * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w' 1‖) ^ r := by
                    rw [mul_pow]
                    ring
          exact hmain
    _ = (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖ ^ r := by
          rw [← hn1]
    _ = (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ)
          (exteriorPower.ιMulti ℝ k u) 1‖ ^ r := by
          simp [w]


/-- **Lemma 2 (general pure tensor, ratio form)**: with nonzero block-0 norm `X`, the higher
blocks of a transverse pure tensor `w = ιMulti u` are controlled by the ratio
`ρ = ‖w₁‖/‖w₀‖`: `‖w_r‖ ≤ 2^k · X · ρ^r`. -/
lemma pureTensor_blockElem_r_le_div {d k : ℕ} (ℓ : ℕ) (r : ℕ) (hk : 0 < k) (hr : 1 ≤ r)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥)
    (hX : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) r‖ ≤
      (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ *
        (‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ /
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖) ^ r := by
  classical
  let X : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖
  let Y : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖
  have hXpos : 0 < X := by simpa [X] using hX
  have hXne : X ≠ 0 := ne_of_gt hXpos
  have hmain0 := pureTensor_blockElem_r_le (d := d) (k := k) ℓ r hk hr u hu hbot
  have hXpow : 0 < X ^ (r - 1) := pow_pos hXpos (r - 1)
  have hdiv : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) r‖ ≤
      (2 : ℝ) ^ k * Y ^ r / X ^ (r - 1) := by
    have hle : ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) r‖ * X ^ (r - 1) ≤
        (2 : ℝ) ^ k * Y ^ r := by
      calc
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) r‖ * X ^ (r - 1)
            = X ^ (r - 1) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) r‖ := by rw [mul_comm]
        _ ≤ (2 : ℝ) ^ k * Y ^ r := by
              simpa [X, Y] using hmain0
    exact (le_div_iff₀ hXpow).mpr hle
  have hXpowX : X ^ (r - 1) * X = X ^ r := by
    rw [← pow_succ]
    congr 1
    omega
  have hXY : X * (Y / X) ^ r = Y ^ r / X ^ (r - 1) := by
    rw [div_pow]
    field_simp [hXne]
    rw [← hXpowX]
    ring
  calc
    ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) r‖ ≤
        (2 : ℝ) ^ k * Y ^ r / X ^ (r - 1) := hdiv
    _ = (2 : ℝ) ^ k * X * (Y / X) ^ r := by
          calc
            (2 : ℝ) ^ k * Y ^ r / X ^ (r - 1) = (2 : ℝ) ^ k * (Y ^ r / X ^ (r - 1)) := by ring
            _ = (2 : ℝ) ^ k * (X * (Y / X) ^ r) := by rw [← hXY]
            _ = (2 : ℝ) ^ k * X * (Y / X) ^ r := by ring

/-- **Flow norm bound (Prop 1 part 1, analytic input)**: for the two-scale flow
`f = scaleMap (twoScale a b ℓ)` (`a` on `x₀`, `b` on `x₀ᗮ`), a pure tensor `w = ιMulti u`
of a plane transverse to `x₀ᗮ`, with block norms `X = ‖w₀‖`, `Y = ‖w₁‖`, the cone
hypothesis `b·Y ≤ a·X` keeps every flowed block within `2^k·a^k·X`, hence
`‖fₖ w‖ ≤ (k+1)·2^k·a^k·X`. -/
theorem pureTensor_flow_le {d k : ℕ} (ℓ : ℕ) (hk : 0 < k) (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥)
    (hX : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖)
    (hcone : b * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
      a * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖) :
    ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ k u)‖ ≤
      ((k : ℝ) + 1) * (2 : ℝ) ^ k * a ^ k *
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
  classical
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let X : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖
  let Y : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖
  let f : RD d →ₗ[ℝ] RD d := scaleMap (twoScale a b ℓ)
  let aw : WK d k := exteriorPower.map k f w
  have hXpos : 0 < X := by simpa [X, w] using hX
  have hXnonneg : 0 ≤ X := le_of_lt hXpos
  have hYnonneg : 0 ≤ Y := by dsimp [Y, w]; exact norm_nonneg _
  have hη : b * Y ≤ a * X := by simpa [X, Y, w] using hcone
  have hXne : X ≠ 0 := ne_of_gt hXpos
  have hdec : (Finset.range (k + 1)).sum (fun j : ℕ =>
      blockElem (d := d) (k := k) (ℓ := ℓ) aw j) = aw :=
    sum_blockElem (d := d) (k := k) (ℓ := ℓ) aw
  have htri : ‖aw‖ ≤ (Finset.range (k + 1)).sum (fun j : ℕ =>
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw j‖) := by
    calc
      ‖aw‖ = ‖(Finset.range (k + 1)).sum (fun j : ℕ =>
          blockElem (d := d) (k := k) (ℓ := ℓ) aw j)‖ := by rw [hdec]
      _ ≤ (Finset.range (k + 1)).sum (fun j : ℕ =>
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw j‖) := norm_sum_le _ _
  have hterm : ∀ j ∈ Finset.range (k + 1),
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw j‖ ≤ (2 : ℝ) ^ k * a ^ k * X := by
    intro j hj
    have hjk : j ≤ k := by exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have hbj : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw j‖ =
        (a ^ (k - j) * b ^ j) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ := by
      dsimp [aw, f, w]
      exact norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b)
        (exteriorPower.ιMulti ℝ k u) hjk (le_of_lt ha) hb
    rw [hbj]
    by_cases hj0 : j = 0
    · subst hj0
      have hXa : 0 ≤ a ^ k * X := mul_nonneg (pow_nonneg (le_of_lt ha) k) hXnonneg
      have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
        have : (1 : ℕ) ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) k)
        exact_mod_cast this
      have hle : a ^ k * X ≤ (2 : ℝ) ^ k * (a ^ k * X) := le_mul_of_one_le_left hXa h2k
      calc
        (a ^ (k - 0) * b ^ 0) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖
            = a ^ k * X := by
                dsimp [X]
                simp [w]
        _ ≤ (2 : ℝ) ^ k * (a ^ k * X) := hle
        _ = (2 : ℝ) ^ k * a ^ k * X := by ring
    · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
      have hL2 := pureTensor_blockElem_r_le_div (d := d) (k := k) ℓ j hk hj1 u hu hbot hX
      have hwj : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ≤
          (2 : ℝ) ^ k * X * (Y / X) ^ j := by
        simpa [X, Y, w] using hL2
      have hXj : 0 < X ^ j := pow_pos hXpos j
      have hbYnonneg : 0 ≤ b * Y := mul_nonneg hb hYnonneg
      have hbYj : (b * Y) ^ j ≤ (a * X) ^ j := pow_le_pow_left₀ hbYnonneg hη j
      have hakj : 0 ≤ a ^ (k - j) := pow_nonneg (le_of_lt ha) (k - j)
      have hmul : a ^ (k - j) * (b * Y) ^ j ≤ a ^ k * X ^ j := by
        have hstep : a ^ (k - j) * (b * Y) ^ j ≤ a ^ (k - j) * (a * X) ^ j :=
          mul_le_mul_of_nonneg_left hbYj hakj
        calc
          a ^ (k - j) * (b * Y) ^ j ≤ a ^ (k - j) * (a * X) ^ j := hstep
          _ = a ^ k * X ^ j := by
                rw [mul_pow]
                have haj : a ^ (k - j) * a ^ j = a ^ k := by
                  rw [← pow_add]
                  congr 1
                  omega
                calc
                  a ^ (k - j) * (a ^ j * X ^ j) = (a ^ (k - j) * a ^ j) * X ^ j := by ring
                  _ = a ^ k * X ^ j := by rw [haj]
      have hle_ratio : a ^ (k - j) * (b * Y / X) ^ j ≤ a ^ k := by
        rw [div_pow]
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hXj).mpr hmul
      have hprod : (a ^ (k - j) * b ^ j) * (X * (Y / X) ^ j) =
          X * (a ^ (k - j) * (b * Y / X) ^ j) := by
        calc
          (a ^ (k - j) * b ^ j) * (X * (Y / X) ^ j)
              = X * (a ^ (k - j) * (b ^ j * (Y / X) ^ j)) := by ring
          _ = X * (a ^ (k - j) * ((b * (Y / X)) ^ j)) := by rw [← mul_pow]
          _ = X * (a ^ (k - j) * ((b * Y / X) ^ j)) := by
                congr 3
                field_simp [hXne]
      calc
        (a ^ (k - j) * b ^ j) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖
            ≤ (a ^ (k - j) * b ^ j) * ((2 : ℝ) ^ k * X * (Y / X) ^ j) := by
                exact mul_le_mul_of_nonneg_left hwj (by positivity)
        _ = (2 : ℝ) ^ k * X * (a ^ (k - j) * (b * Y / X) ^ j) := by
                calc
                  (a ^ (k - j) * b ^ j) * ((2 : ℝ) ^ k * X * (Y / X) ^ j)
                      = (2 : ℝ) ^ k * ((a ^ (k - j) * b ^ j) * (X * (Y / X) ^ j)) := by ring
                  _ = (2 : ℝ) ^ k * (X * (a ^ (k - j) * (b * Y / X) ^ j)) := by rw [hprod]
                  _ = (2 : ℝ) ^ k * X * (a ^ (k - j) * (b * Y / X) ^ j) := by ring
        _ ≤ (2 : ℝ) ^ k * X * a ^ k := by
                exact mul_le_mul_of_nonneg_left hle_ratio (by positivity)
        _ = (2 : ℝ) ^ k * a ^ k * X := by ring
  calc
    ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ k u)‖
        = ‖aw‖ := by simp [aw, f, w]
    _ ≤ (Finset.range (k + 1)).sum (fun j : ℕ =>
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw j‖) := htri
    _ ≤ (Finset.range (k + 1)).sum (fun _ : ℕ => (2 : ℝ) ^ k * a ^ k * X) := by
          exact Finset.sum_le_sum (fun j hj => hterm j hj)
    _ = (Finset.range (k + 1)).card • ((2 : ℝ) ^ k * a ^ k * X) := by simp
    _ = (((k + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ k * a ^ k * X) := by
          simp
    _ = ((k : ℝ) + 1) * (2 : ℝ) ^ k * a ^ k *
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖ := by
          have hk1 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
          rw [hk1]
          ring_nf
          simp [X, w]


/-- **Block-0 dominance under the flow (Prop 1 part 1, cone stays in `C₊`)**: under the
hypotheses of `pureTensor_flow_le`, the block-0 part of the flowed vector dominates the whole
flowed vector: `‖block₀(fₖ w)‖ ≥ ‖fₖ w‖ / ((k+1)·2^k)`. -/
theorem pureTensor_flow_block0_dominance {d k : ℕ} (ℓ : ℕ) (hk : 0 < k) (a b : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥)
    (hX : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖)
    (hcone : b * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
      a * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖) :
    ‖blockElem (d := d) (k := k) (ℓ := ℓ)
        (exteriorPower.map k (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ k u)) 0‖ ≥
      ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ k u)‖ /
        (((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
  classical
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let X : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖
  let f : RD d →ₗ[ℝ] RD d := scaleMap (twoScale a b ℓ)
  let aw : WK d k := exteriorPower.map k f w
  have hC : 0 < ((k : ℝ) + 1) * (2 : ℝ) ^ k := by positivity
  have hflow := pureTensor_flow_le (d := d) (k := k) ℓ hk a b ha hb u hu hbot hX hcone
  have hB : a ^ k * X = ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ := by
    have hb0 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ =
        (a ^ (k - 0) * b ^ 0) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
      dsimp [aw, f, w]
      exact norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b)
        (exteriorPower.ιMulti ℝ k u) (by omega : 0 ≤ k) (le_of_lt ha) hb
    rw [hb0]
    dsimp [X, w]
    simp
  have hle : ‖aw‖ ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ *
      (((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
    calc
      ‖aw‖ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * a ^ k * X := by simpa [aw, f, w] using hflow
      _ = ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ * (((k : ℝ) + 1) * (2 : ℝ) ^ k) := by
            rw [← hB]
            ring
  have hdiv : ‖aw‖ / (((k : ℝ) + 1) * (2 : ℝ) ^ k) ≤
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ := by
    exact (div_le_iff₀ hC).mpr hle
  simpa [aw, f, w] using hdiv



/-- **Height/flow comparison (model form of Prop 1 part 1, second estimate)**: for the
two-scale flow with `0 < a ≤ b` and the cone hypothesis `b·‖w₁‖ ≤ a·‖w₀‖`, the total norm of
the pure tensor is controlled by the flowed norm: `a^k·‖w‖ ≤ (k+1)·2^k·‖a_t w‖`.  (With
`a = exp(-t/ℓ)`, `b = exp(t/(d-ℓ))` this is `H(v) ≲ e^{tk/ℓ}‖a_t v‖` once the height of a
rational plane is identified with `‖w‖`.) -/
theorem pureTensor_norm_le_flow {d k : ℕ} (ℓ : ℕ) (hk : 0 < k) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hab : a ≤ b) (u : Fin k → RD d) (hu : LinearIndependent ℝ u)
    (hbot : (Submodule.span ℝ (Set.range u)) ⊓ (modelX ℓ)ᗮ = ⊥)
    (hX : 0 < ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖)
    (hcone : b * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 1‖ ≤
      a * ‖blockElem (d := d) (k := k) (ℓ := ℓ) (exteriorPower.ιMulti ℝ k u) 0‖) :
    a ^ k * ‖exteriorPower.ιMulti ℝ k u‖ ≤
      ((k : ℝ) + 1) * (2 : ℝ) ^ k *
        ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ k u)‖ := by
  classical
  let w : WK d k := exteriorPower.ιMulti ℝ k u
  let X : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖
  let Y : ℝ := ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 1‖
  let f : RD d →ₗ[ℝ] RD d := scaleMap (twoScale a b ℓ)
  let aw : WK d k := exteriorPower.map k f w
  have hXpos : 0 < X := by simpa [X, w] using hX
  have hYnonneg : 0 ≤ Y := by dsimp [Y, w]; exact norm_nonneg _
  have hb0 : 0 ≤ b := le_of_lt hb
  -- block-0 of the flowed vector is a^k·w₀, so ‖aw‖ ≥ a^k·X
  have hb0flow : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ = a ^ k * X := by
    have hb0' : ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ =
        (a ^ (k - 0) * b ^ 0) * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
      dsimp [aw, f, w]
      exact norm_blockElem_map_twoScale (d := d) (k := k) (ℓ := ℓ) (a := a) (b := b)
        (exteriorPower.ιMulti ℝ k u) (by omega : 0 ≤ k) (le_of_lt ha) hb0
    rw [hb0']
    dsimp [X, w]
    simp
  have hak : 0 ≤ a ^ k := pow_nonneg (le_of_lt ha) k
  have hle0 : a ^ k * X ≤ ‖aw‖ := by
    calc
      a ^ k * X = ‖blockElem (d := d) (k := k) (ℓ := ℓ) aw 0‖ := by rw [hb0flow]
      _ ≤ ‖aw‖ := by
            exact norm_blockElem_le_norm (d := d) (k := k) (ℓ := ℓ) aw (by omega : 0 ≤ k)
  -- cone hypothesis gives ρ := Y/X ≤ 1
  have hρ : Y / X ≤ 1 := by
    have hstep : Y / X ≤ a / b := by
      exact (div_le_div_iff₀ hXpos hb).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcone)
    exact hstep.trans ((div_le_one hb).mpr hab)
  have hρ0 : 0 ≤ Y / X := div_nonneg hYnonneg (le_of_lt hXpos)
  -- each block ‖w_j‖ ≤ 2^k·X (j = 0 is even ≤ X ≤ 2^k·X)
  have hwj : ∀ j ∈ Finset.range (k + 1),
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ≤ (2 : ℝ) ^ k * X := by
    intro j hj
    have hjk : j ≤ k := by exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    by_cases hj0 : j = 0
    · subst hj0
      have hX0 : 0 ≤ ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := norm_nonneg _
      have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
        have : (1 : ℕ) ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) k)
        exact_mod_cast this
      have hX2 : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ≤ (2 : ℝ) ^ k * X := by
        dsimp [X]
        have hle : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ ≤
            (2 : ℝ) ^ k * ‖blockElem (d := d) (k := k) (ℓ := ℓ) w 0‖ := by
          exact le_mul_of_one_le_left hX0 h2k
        simpa using hle
      simpa [w] using hX2
    · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
      have hL2 := pureTensor_blockElem_r_le_div (d := d) (k := k) ℓ j hk hj1 u hu hbot hX
      have hL2' : ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ≤
          (2 : ℝ) ^ k * X * (Y / X) ^ j := by
        simpa [X, Y, w] using hL2
      have hpow1 : (Y / X) ^ j ≤ 1 := pow_le_one₀ hρ0 hρ
      calc
        ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖ ≤ (2 : ℝ) ^ k * X * (Y / X) ^ j := hL2'
        _ ≤ (2 : ℝ) ^ k * X * 1 := by
              exact mul_le_mul_of_nonneg_left hpow1 (by positivity)
        _ = (2 : ℝ) ^ k * X := by ring_nf
  have htri : ‖w‖ ≤ (Finset.range (k + 1)).sum (fun j : ℕ =>
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖) := by
    calc
      ‖w‖ = ‖(Finset.range (k + 1)).sum (fun j : ℕ =>
          blockElem (d := d) (k := k) (ℓ := ℓ) w j)‖ := by rw [sum_blockElem (d := d) (k := k) (ℓ := ℓ) w]
      _ ≤ (Finset.range (k + 1)).sum (fun j : ℕ =>
          ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖) := norm_sum_le _ _
  have hsum : (Finset.range (k + 1)).sum (fun j : ℕ =>
      ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖) ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * X := by
    calc
      (Finset.range (k + 1)).sum (fun j : ℕ => ‖blockElem (d := d) (k := k) (ℓ := ℓ) w j‖)
          ≤ (Finset.range (k + 1)).sum (fun _ : ℕ => (2 : ℝ) ^ k * X) := by
              exact Finset.sum_le_sum (fun j hj => hwj j hj)
      _ = (Finset.range (k + 1)).card • ((2 : ℝ) ^ k * X) := by simp
      _ = (((k + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ k * X) := by simp
      _ = ((k : ℝ) + 1) * (2 : ℝ) ^ k * X := by
            have hk1 : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
            rw [hk1]
            ring_nf
  calc
    a ^ k * ‖exteriorPower.ιMulti ℝ k u‖
        = a ^ k * ‖w‖ := by simp [w]
    _ ≤ a ^ k * (((k : ℝ) + 1) * (2 : ℝ) ^ k * X) := by
          exact mul_le_mul_of_nonneg_left (htri.trans hsum) hak
    _ = ((k : ℝ) + 1) * (2 : ℝ) ^ k * (a ^ k * X) := by ring_nf
    _ ≤ ((k : ℝ) + 1) * (2 : ℝ) ^ k * ‖aw‖ := by
          exact mul_le_mul_of_nonneg_left hle0 (by positivity)
    _ = ((k : ℝ) + 1) * (2 : ℝ) ^ k *
          ‖exteriorPower.map k (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ k u)‖ := by
          simp [aw, f, w]

end Submission.WedgeBlocks
