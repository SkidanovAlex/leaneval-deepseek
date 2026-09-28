import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.dmin_le_exists_prim
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Q44Child.latZero_bound
import Submission.Work.HP.Q44Child.witness_class_count
import Submission.Work.HP.Q44Child.witness_outside
import Submission.Work.HP.MDEstimates.q44_wclass_determines
import Submission.Work.HP.MDEstimates.q44_perlat_56
import Submission.Work.HP.MDEstimates.q44_layer_sum

/-!
# `ℓ^{(56)}(Z; Δ, J) ≪ Z⁴ Δ²⁴ J¹⁵` (BLBS §3.4, Lemma `l56`)

`Work.HP.MDEstimates.ell44_56_bound` is the second half of the paper's quartic-threefold
estimate: the number of `ℤ`-linearly independent pairs `(x,y)` of vectors of `ℤ⁵` of norm
at most `Z` with `𝔡₃({x,y}) ≤ Δ` and `λ₅₆(Γ_{x,y}) ≤ J` is `O(Z⁴ Δ²⁴ J¹⁵)`.

The proof is assembled from three pieces:

* `ell44_le_sum` (this file): the pair count is at most the sum, over the finite set `T` of
  *witness lattices* (primitive rank-`3` sublattices of `ℤ⁵` of covolume `≤ Δ+1` containing
  the pair, with `λ₁, λ₂ ≤ Z`), of the number of counted pairs lying in `L`;
* `q44_perlat_56`: in such an `L` that number is `O(Z⁴ J¹⁵ λ₁¹⁸ λ₂¹⁸ λ₃²⁰)`;
* `q44_layer_sum`: `Σ_{L ∈ T} λ₁¹⁸ λ₂¹⁸ λ₃²⁰ = O(Δ²⁴)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

/-- `ℓ^{(56)}(Z;Δ,J)` is at most the sum over the family of witness lattices of the pair
counts inside them. -/
theorem ell44_le_sum (Z Δ J : ℝ) (hZ : 1 ≤ Z) :
    ∃ T : Finset (Submodule ℤ (Fin 5 → ℤ)),
      (∀ L ∈ T, IsPrimLat L ∧ rk L = 3 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ Z ∧ lam L 2 ≤ Z) ∧
      ((ell44 56 Z Δ J : ℝ) ≤ ∑ L ∈ T,
        (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
            LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
          Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ)) := by
  classical
  have hLIne : ∀ p : (Fin 5 → ℤ) × (Fin 5 → ℤ),
      LinearIndependent ℤ ![p.1, p.2] → p.1 ≠ 0 := by
    intro p hp h
    rw [h] at hp
    rw [LinearIndependent.pair_iff] at hp
    have := (hp 1 0 (by simp)).1
    exact one_ne_zero this
  set S : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) := Q44PairLam 56 Z Δ J with hSdef
  have hSfin : S.Finite := by
    rw [hSdef]
    refine Set.Finite.subset ((MDBasic.finite_eNorm_le (ι := Fin 5) Z).prod
      (MDBasic.finite_eNorm_le (ι := Fin 5) Z)) ?_
    intro p hp
    exact ⟨hp.2.1, hp.2.2.1⟩
  let g : ((Fin 5 → ℤ) × (Fin 5 → ℤ)) → Submodule ℤ (Fin 5 → ℤ) := fun p =>
    if hp : p ∈ S then
      Classical.choose (dmin_le_exists_prim (Fin 5) 3 p.1 p.2 Δ hp.1 (by norm_num) (by simp)
        hp.2.2.2.1)
    else ⊥
  have hg : ∀ p ∈ S, IsPrimLat (g p) ∧ rk (g p) = 3 ∧ p.1 ∈ g p ∧ p.2 ∈ g p ∧
      detL (g p) ≤ Δ + 1 := by
    intro p hp
    rw [show g p = Classical.choose (dmin_le_exists_prim (Fin 5) 3 p.1 p.2 Δ hp.1
        (by norm_num) (by simp) hp.2.2.2.1) from dif_pos hp]
    exact Classical.choose_spec
      (dmin_le_exists_prim (Fin 5) 3 p.1 p.2 Δ hp.1 (by norm_num) (by simp) hp.2.2.2.1)
  refine ⟨(hSfin.toFinset).image g, ?_, ?_⟩
  · intro L hL
    rw [Finset.mem_image] at hL
    obtain ⟨p, hp, rfl⟩ := hL
    have hpS : p ∈ S := by rwa [Set.Finite.mem_toFinset] at hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hg p hpS
    refine ⟨h1, h2, h5, ?_, ?_⟩
    · exact le_trans ((lam_basic (Fin 5) (g p)).2.2.2.1 p.1 h3 (hLIne p hpS.1)) hpS.2.1
    · refine le_trans ((lam_basic (Fin 5) (g p)).2.2.2.2 p.1 p.2 h3 h4 hpS.1) ?_
      exact max_le hpS.2.1 hpS.2.2.1
  · have hcard : (S.ncard : ℝ) = ∑ L ∈ (hSfin.toFinset).image g,
        (((hSfin.toFinset).filter (fun p => g p = L)).card : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hSfin]
      rw [Finset.card_eq_sum_card_fiberwise (f := g) (s := hSfin.toFinset)
        (t := (hSfin.toFinset).image g) (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
      push_cast
      rfl
    rw [ell44_eq, ← hSdef, hcard]
    refine Finset.sum_le_sum (fun L hL => ?_)
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hL
    have hp₀S : p₀ ∈ S := by rwa [Set.Finite.mem_toFinset] at hp₀
    have hPfin : ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
        p.1 ∈ g p₀ ∧ p.2 ∈ g p₀ ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
        LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
      Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).Finite :=
      ((MDBasic.finite_eNorm_le (ι := Fin 5) Z).prod
        (MDBasic.finite_eNorm_le (ι := Fin 5) Z)).subset
        (fun p hp => ⟨hp.2.2.1, hp.2.2.2.1⟩)
    have hsub : ((hSfin.toFinset).filter (fun p => g p = g p₀)) ⊆ hPfin.toFinset := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpT, hpg⟩ := hp
      have hpS : p ∈ S := by rwa [Set.Finite.mem_toFinset] at hpT
      obtain ⟨-, -, h1, h2, -⟩ := hg p hpS
      rw [Set.Finite.mem_toFinset]
      exact ⟨by rw [← hpg]; exact h1, by rw [← hpg]; exact h2,
        hpS.2.1, hpS.2.2.1, hpS.1, hpS.2.2.2.2⟩
    have h2 : hPfin.toFinset.card = ({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
        p.1 ∈ g p₀ ∧ p.2 ∈ g p₀ ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
        LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
      Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard :=
      (Set.ncard_eq_toFinset_card _ hPfin).symm
    calc (((hSfin.toFinset).filter (fun p => g p = g p₀)).card : ℝ)
        ≤ (hPfin.toFinset.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p.1 ∈ g p₀ ∧ p.2 ∈ g p₀ ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
            LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
          Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ) := by rw [h2]

theorem ell44_56_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ Z Δ J : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ J →
      (ell44 56 Z Δ J : ℝ) ≤ K * Z ^ 4 * Δ ^ 24 * J ^ 15 := by
  obtain ⟨K1, hK1, hB⟩ := q44_perlat_56
  obtain ⟨K2, hK2, hC⟩ := q44_layer_sum
  refine ⟨K1 * K2, by positivity, ?_⟩
  intro Z Δ J hZ hΔ hJ
  obtain ⟨T, hT, hsum⟩ := ell44_le_sum Z Δ J hZ
  have hstep : (∑ L ∈ T,
        (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
            p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
            LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
          Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ))
      ≤ K1 * Z ^ 4 * J ^ 15 * ∑ L ∈ T,
          (lam L 1 ^ 18 * lam L 2 ^ 18 * lam L 3 ^ 20) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun L hL => ?_)
    obtain ⟨-, hrk, -, hl1, hl2⟩ := hT L hL
    have hb := hB L hrk Z J hZ hJ hl1 hl2
    calc (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
              p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
              LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
            Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ)
        ≤ K1 * Z ^ 4 * J ^ 15 * lam L 1 ^ 18 * lam L 2 ^ 18 * lam L 3 ^ 20 := hb
      _ = (K1 * Z ^ 4 * J ^ 15) * (lam L 1 ^ 18 * lam L 2 ^ 18 * lam L 3 ^ 20) := by
          ring
  calc (ell44 56 Z Δ J : ℝ)
      ≤ ∑ L ∈ T,
          (({p : (Fin 5 → ℤ) × (Fin 5 → ℤ) |
              p.1 ∈ L ∧ p.2 ∈ L ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
              LinearIndependent ℤ ![p.1, p.2] ∧ lam (Gam 4 4 p.1 p.2) 56 ≤ J} :
            Set ((Fin 5 → ℤ) × (Fin 5 → ℤ))).ncard : ℝ) := hsum
    _ ≤ K1 * Z ^ 4 * J ^ 15 * ∑ L ∈ T,
          (lam L 1 ^ 18 * lam L 2 ^ 18 * lam L 3 ^ 20) := hstep
    _ ≤ K1 * Z ^ 4 * J ^ 15 * (K2 * Δ ^ 24) := by
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact hC T Δ hΔ
            (fun L hL => ⟨(hT L hL).1, (hT L hL).2.1, (hT L hL).2.2.1⟩)
        · positivity
    _ = (K1 * K2) * Z ^ 4 * Δ ^ 24 * J ^ 15 := by ring

end Work.HP.MDEstimates
