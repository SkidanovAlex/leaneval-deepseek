import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.card_diff_le_Jincom
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The pair sum of Ford's tent factors

The extraction of Ford's Lemma 5.1 (`Work.BMF.vkford_lemma51`) expands the `2s`-th moment of
the inner `b`-sum `Xsum` into a sum over pairs `p : Pair s M₂` of `s`-tuples, each carrying the
product `∏_{j<k} tent (1/(2 r M₁^{j+1})) (γ_{j+1} dvec (j+1) p)` of the Fourier (tent) kernels
evaluated at the pair differences `dvec`.  The point of this file is the estimate

  `∑_p ∏_{j<k} tent_j(dvec_j p) ≤ J_{s,g,h}[1,M₂] · ∏_{h ≤ j ≤ g} #D_j`,

i.e. the whole pair sum is controlled by the *incomplete*-system count `Jincom` and by the
cardinalities of the resonant difference sets `D_j` of the middle range `h ≤ j ≤ g`.

The two ingredients are

* `prod_tent_le_prod_dset_indicator`: each tent factor is bounded by the indicator of the
  resonant set `D_j` at the same index (the tent is `≤ 1`, and it vanishes unless
  `nint (γ_j dvec_j p) < 1/(2 r M₁^j)`; the companion bound `|dvec_j p| ≤ s M₂^j - 1` is
  automatic for pairs of `s`-tuples with entries in `[1, M₂]`), so the full product over
  `1 ≤ j ≤ k` is at most the sub-product over the middle range `h ≤ j ≤ g`;
* `sum_prod_indicator_le`: the number of pairs whose difference vector lies in prescribed
  sets is at most `Jincom` times the number of choices, by partitioning over the difference
  vector and applying `card_diff_le_Jincom` to each fibre.
-/

namespace Work.BMF

open Finset
open scoped BigOperators

namespace PairAux

/-- A product of indicators is the indicator of the conjunction: the product of
`if p i then 1 else 0` over `i ∈ s` is `1` exactly when all the `p i` hold. -/
lemma prod_ite_indicator {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∏ i ∈ s, (if p i then (1 : ℝ) else 0)) = if (∀ i ∈ s, p i) then 1 else 0 := by
  by_cases h : ∀ i ∈ s, p i
  · rw [if_pos h]
    exact Finset.prod_eq_one fun i hi => if_pos (h i hi)
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi, hpi⟩ := h
    exact Finset.prod_eq_zero hi (if_neg hpi)

/-- `{1, 2, …, k}` is the image of `{0, 1, …, k-1}` under `i ↦ i + 1`. -/
lemma image_range_add_one (k : ℕ) :
    (Finset.range k).image (fun i : ℕ => i + 1) = Finset.Icc 1 k := by
  ext m
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨m - 1, by omega, by omega⟩

/-- `Jincom` is the cast of a cardinal, hence non-negative. -/
lemma jincom_nonneg (s k h : ℕ) (B : Finset ℕ) : 0 ≤ Jincom s k h B := by
  rw [Jincom]; positivity

/-- **The difference vector is bounded by `s M₂^j - 1`.**  For a pair of `s`-tuples with entries
in `[1, M₂]`, each power sum lies between `s` and `s M₂^j`, so the difference `dvec j p` lies in
the symmetric range `±(s M₂^j - 1)` of `Dset`. -/
lemma dvec_mem_Icc {s M₂ : ℕ} (hs : 1 ≤ s) (hM₂ : 1 ≤ M₂) (j : ℕ) (p : Pair s M₂) :
    dvec j p ∈ Finset.Icc (-(((s * M₂ ^ j - 1 : ℕ)) : ℤ)) (((s * M₂ ^ j - 1 : ℕ) : ℤ)) := by
  rw [Finset.mem_Icc]
  have hle1 : ∀ i : Fin s, ((p.1 i).1 : ℤ) ≤ (M₂ : ℤ) := fun i =>
    Int.ofNat_le.mpr (Finset.mem_Icc.mp (p.1 i).2).2
  have hle2 : ∀ i : Fin s, ((p.2 i).1 : ℤ) ≤ (M₂ : ℤ) := fun i =>
    Int.ofNat_le.mpr (Finset.mem_Icc.mp (p.2 i).2).2
  have hge1 : ∀ i : Fin s, (1 : ℤ) ≤ ((p.1 i).1 : ℤ) := fun i =>
    Int.ofNat_le.mpr (Finset.mem_Icc.mp (p.1 i).2).1
  have hge2 : ∀ i : Fin s, (1 : ℤ) ≤ ((p.2 i).1 : ℤ) := fun i =>
    Int.ofNat_le.mpr (Finset.mem_Icc.mp (p.2 i).2).1
  have hsum : (∑ _i : Fin s, ((M₂ : ℤ) ^ j)) = (s:ℤ) * (M₂:ℤ)^j := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
  have hsum1 : (∑ _i : Fin s, (1:ℤ)) = (s:ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
  have hA' : (∑ i : Fin s, (((p.1 i).1 : ℤ) ^ j)) ≤ (s:ℤ) * (M₂:ℤ)^j := by
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (by linarith [hge1 i]) (hle1 i) j
  have hA2 : (s:ℤ) ≤ ∑ i : Fin s, (((p.1 i).1 : ℤ) ^ j) := by
    rw [← hsum1]
    exact Finset.sum_le_sum fun i _ => by
      calc (1:ℤ) = (1:ℤ)^j := (one_pow j).symm
        _ ≤ ((p.1 i).1 : ℤ) ^ j := pow_le_pow_left₀ (by norm_num) (hge1 i) j
  have hB' : (s:ℤ) ≤ ∑ i : Fin s, (((p.2 i).1 : ℤ) ^ j) := by
    rw [← hsum1]
    exact Finset.sum_le_sum fun i _ => by
      calc (1:ℤ) = (1:ℤ)^j := (one_pow j).symm
        _ ≤ ((p.2 i).1 : ℤ) ^ j := pow_le_pow_left₀ (by norm_num) (hge2 i) j
  have hB2 : (∑ i : Fin s, (((p.2 i).1 : ℤ) ^ j)) ≤ (s:ℤ) * (M₂:ℤ)^j := by
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (by linarith [hge2 i]) (hle2 i) j
  have hcast : (((s * M₂ ^ j - 1 : ℕ)) : ℤ) = (s:ℤ) * (M₂:ℤ)^j - 1 := by
    have h1 : 1 ≤ M₂ ^ j := one_le_pow₀ hM₂
    have h2 : 1 ≤ s * M₂ ^ j := by
      calc (1:ℕ) = 1*1 := by ring
        _ ≤ s * M₂^j := Nat.mul_le_mul hs h1
    rw [Nat.cast_sub h2, Nat.cast_one, Nat.cast_mul, Nat.cast_pow]
  constructor <;> rw [dvec, hcast] <;> linarith

/-- The width `1/(2 r M₁^j)` of the `j`-th tent is positive. -/
lemma tent_width_pos (r M₁ : ℕ) (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) (j : ℕ) :
    (0:ℝ) < 1 / (2 * ((r * M₁ ^ j : ℕ) : ℝ)) := by
  have h2 : (0:ℕ) < r * M₁ ^ j :=
    Nat.mul_pos (by omega) (pow_pos (by omega) j)
  have h3 : (0:ℝ) < ((r * M₁ ^ j : ℕ) : ℝ) := by exact_mod_cast h2
  positivity

/-- **A single tent factor is bounded by the indicator of the resonant set.**  If the tent is
non-zero then `nint (γ_j dvec_j p) < 1/(2 r M₁^j)`; together with the automatic bound
`|dvec_j p| ≤ s M₂^j - 1` this says `dvec_j p ∈ Dset r s M₁ M₂ j γ`. -/
lemma tent_factor_le_indicator (r s M₁ M₂ : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁)
    (hM₂ : 1 ≤ M₂) (t z : ℝ) (j : ℕ) (p : Pair s M₂) :
    tent (1 / (2 * ((r * M₁ ^ j : ℕ) : ℝ))) (gam j t z * ((dvec j p : ℤ) : ℝ))
      ≤ (if dvec j p ∈ Dset r s M₁ M₂ j (gam j t z) then (1 : ℝ) else 0) := by
  have hB := tent_width_pos r M₁ hr hM₁ j
  by_cases hmem : dvec j p ∈ Dset r s M₁ M₂ j (gam j t z)
  · rw [if_pos hmem]; exact tent_le_one hB
  · rw [if_neg hmem]
    have hIcc := dvec_mem_Icc hs hM₂ j p
    have hP : ¬ (nint (((dvec j p : ℤ) : ℝ) * gam j t z) < 1 / (2 * (r:ℝ) * (M₁:ℝ)^j)) := by
      intro hcon
      exact hmem (Finset.mem_filter.mpr ⟨hIcc, hcon⟩)
    have hthr : 1 / (2 * (r:ℝ) * (M₁:ℝ)^j) ≤ nint (((dvec j p : ℤ) : ℝ) * gam j t z) :=
      not_lt.mp hP
    have hle : 1 / (2 * ((r * M₁ ^ j : ℕ) : ℝ))
        ≤ nint (gam j t z * ((dvec j p : ℤ) : ℝ)) := by
      calc 1 / (2 * ((r * M₁ ^ j : ℕ) : ℝ))
          = 1 / (2 * (r:ℝ) * (M₁:ℝ)^j) := by push_cast; ring
        _ ≤ nint (((dvec j p : ℤ) : ℝ) * gam j t z) := hthr
        _ = nint (gam j t z * ((dvec j p : ℤ) : ℝ)) := by congr 1; ring
    rw [tent_eq_zero_of_le hB hle]

/-- **The product of the tent factors is bounded by the sub-product of the resonant
indicators over the middle range `h ≤ j ≤ g`.**  Reindexing `j : Fin k` as the exponents
`1 ≤ m ≤ k`, each tent factor at `m` is at most the indicator of `D_m`; factors outside
`[h, g]` are at most `1` (they are non-negative too), so they may be discarded. -/
theorem prod_tent_le_prod_dset_indicator (r s M₁ M₂ k h g : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂) (hh : 1 ≤ h) (hhg : h ≤ g) (hgk : g ≤ k)
    (t z : ℝ) (p : Pair s M₂) :
    (∏ j : Fin k,
        tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
          (gam ((j : ℕ) + 1) t z * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))
      ≤ ∏ j ∈ Finset.Icc h g,
          (if dvec j p ∈ Dset r s M₁ M₂ j (gam j t z) then (1 : ℝ) else 0) := by
  let TF : ℕ → ℝ := fun j => tent (1 / (2 * ((r * M₁ ^ j : ℕ) : ℝ)))
                            (gam j t z * ((dvec j p : ℤ) : ℝ))
  let GI : ℕ → ℝ := fun j => if dvec j p ∈ Dset r s M₁ M₂ j (gam j t z) then (1:ℝ) else 0
  have hTF0 : ∀ j, 0 ≤ TF j := fun j => tent_nonneg _ _
  have hTF1 : ∀ j, TF j ≤ 1 := fun j => tent_le_one (tent_width_pos r M₁ hr hM₁ j)
  have hTFle : ∀ j, TF j ≤ GI j := fun j =>
    tent_factor_le_indicator r s M₁ M₂ hr hs hM₁ hM₂ t z j p
  have hstep1 : (∏ j : Fin k, TF ((j:ℕ)+1)) = ∏ m ∈ Finset.Icc 1 k, TF m := by
    have h : (∏ j : Fin k, TF ((j:ℕ)+1)) = ∏ i ∈ Finset.range k, TF (i+1) :=
      Fin.prod_univ_eq_prod_range (fun i => TF (i + 1)) k
    rw [h, ← image_range_add_one k]
    exact (Finset.prod_image (f := TF) (g := fun i : ℕ => i + 1) (s := Finset.range k)
      (fun a _ b _ hab => Nat.succ.inj hab)).symm
  have hstep2 : (∏ m ∈ Finset.Icc 1 k, TF m) ≤ ∏ m ∈ Finset.Icc h g, TF m := by
    apply Finset.prod_le_prod_of_subset_of_le_one₀
    · intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨le_trans hh hm1, le_trans hm2 hgk⟩
    · intro m _; exact hTF0 m
    · intro m _ _; exact hTF1 m
  have hstep3 : (∏ m ∈ Finset.Icc h g, TF m) ≤ ∏ m ∈ Finset.Icc h g, GI m := by
    apply Finset.prod_le_prod₀
    · intro m _; exact hTF0 m
    · intro m _; exact hTFle m
  have hmain : (∏ j : Fin k, TF ((j:ℕ)+1)) ≤ ∏ m ∈ Finset.Icc h g, GI m := by
    calc (∏ j : Fin k, TF ((j:ℕ)+1)) = ∏ m ∈ Finset.Icc 1 k, TF m := hstep1
      _ ≤ ∏ m ∈ Finset.Icc h g, TF m := hstep2
      _ ≤ ∏ m ∈ Finset.Icc h g, GI m := hstep3
  exact hmain

/-- **Counting pairs with prescribed difference vector.**  Summing the indicator product over all
pairs counts those whose difference vector lies in the prescribed sets; partitioning by the
difference vector and bounding each fibre with `card_diff_le_Jincom` gives the bound
`Jincom · ∏ #(B j)`. -/
theorem sum_prod_indicator_le (s M₂ h g : ℕ) (B : ℕ → Finset ℤ) :
    (∑ p : Pair s M₂, ∏ j ∈ Finset.Icc h g, (if dvec j p ∈ B j then (1 : ℝ) else 0))
      ≤ Jincom s g h (Finset.Icc 1 M₂) * ∏ j ∈ Finset.Icc h g, ((B j).card : ℝ) := by
  classical
  let S : Finset (Pair s M₂) := Finset.univ.filter (fun p => ∀ j ∈ Finset.Icc h g, dvec j p ∈ B j)
  let φ : Pair s M₂ → (↥(Finset.Icc h g) → ℤ) := fun p j => dvec (j : ℕ) p
  let K : Finset (↥(Finset.Icc h g) → ℤ) :=
    Fintype.piFinset (fun j : ↥(Finset.Icc h g) => B (j : ℕ))
  have hLHS : (∑ p : Pair s M₂, ∏ j ∈ Finset.Icc h g,
        (if dvec j p ∈ B j then (1 : ℝ) else 0)) = (S.card : ℝ) := by
    have h1 : (∑ p : Pair s M₂, ∏ j ∈ Finset.Icc h g,
          (if dvec j p ∈ B j then (1 : ℝ) else 0))
        = ∑ p : Pair s M₂, (if (∀ j ∈ Finset.Icc h g, dvec j p ∈ B j) then (1:ℝ) else 0) :=
      Finset.sum_congr rfl fun p _ => prod_ite_indicator _ _
    rw [h1, Finset.sum_boole]
  have hmap : ∀ p ∈ S, φ p ∈ K := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [K, Fintype.mem_piFinset]
    intro j
    exact hp (j:ℕ) j.2
  have hfib : S.card = ∑ δ ∈ K, (S.filter (fun p => φ p = δ)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hfibJ : ∀ δ ∈ K,
      ((S.filter (fun p => φ p = δ)).card : ℝ) ≤ Jincom s g h (Finset.Icc 1 M₂) := by
    intro δ _
    let δ' : ℕ → ℤ := fun j => if hh : h ≤ j ∧ j ≤ g then δ ⟨j, Finset.mem_Icc.mpr hh⟩ else 0
    have hsub : S.filter (fun p => φ p = δ) ⊆
        (Finset.univ : Finset (Pair s M₂)).filter
          (fun p => ∀ j : ℕ, h ≤ j → j ≤ g → dvec j p = δ' j) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨_, hpφ⟩ := hp
      intro j hj1 hj2
      have hmem : j ∈ Finset.Icc h g := Finset.mem_Icc.mpr ⟨hj1, hj2⟩
      have h2 : δ' j = δ ⟨j, hmem⟩ := by
        dsimp only [δ']
        rw [dif_pos (show h ≤ j ∧ j ≤ g from ⟨hj1, hj2⟩)]
      have h1 : δ ⟨j, hmem⟩ = φ p ⟨j, hmem⟩ := by rw [hpφ]
      rw [h2, h1]
    refine le_trans ?_ (card_diff_le_Jincom s g h M₂ δ')
    exact Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hKcard : ((K.card : ℕ) : ℝ) = ∏ j ∈ Finset.Icc h g, ((B j).card : ℝ) := by
    dsimp only [K]
    rw [Fintype.card_piFinset]
    push_cast
    exact Finset.prod_coe_sort (s := Finset.Icc h g) (f := fun i : ℕ => ((B i).card : ℝ))
  calc (∑ p : Pair s M₂, ∏ j ∈ Finset.Icc h g, (if dvec j p ∈ B j then (1 : ℝ) else 0))
      = (S.card : ℝ) := hLHS
    _ = ∑ δ ∈ K, ((S.filter (fun p => φ p = δ)).card : ℝ) := by rw [hfib, Nat.cast_sum]
    _ ≤ ∑ δ ∈ K, Jincom s g h (Finset.Icc 1 M₂) := Finset.sum_le_sum hfibJ
    _ = (K.card : ℝ) * Jincom s g h (Finset.Icc 1 M₂) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = Jincom s g h (Finset.Icc 1 M₂) * (K.card : ℝ) := by ring
    _ ≤ Jincom s g h (Finset.Icc 1 M₂) * ∏ j ∈ Finset.Icc h g, ((B j).card : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_eq hKcard) (jincom_nonneg s g h _)

end PairAux

open PairAux

theorem pair_tent_sum_le (r s M₁ M₂ k h g : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (N t z : ℝ) (ht : 0 < t) (hz : N < z) (hz2 : z ≤ 2 * N) (hh : 1 ≤ h) (hhg : h ≤ g) (hgk : g ≤ k) :
    (∑ p : Pair s M₂, ∏ j : Fin k,
        tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
          (gam ((j : ℕ) + 1) t z * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))
      ≤ (Jincom s g h (Finset.Icc 1 M₂))
          * ∏ j ∈ Finset.Icc h g, ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ) := by
  calc (∑ p : Pair s M₂, ∏ j : Fin k,
        tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
          (gam ((j : ℕ) + 1) t z * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))
      ≤ ∑ p : Pair s M₂, ∏ j ∈ Finset.Icc h g,
          (if dvec j p ∈ Dset r s M₁ M₂ j (gam j t z) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun p _ =>
          prod_tent_le_prod_dset_indicator r s M₁ M₂ k h g hr hs hM₁ hM₂ hh hhg hgk t z p
    _ ≤ Jincom s g h (Finset.Icc 1 M₂)
          * ∏ j ∈ Finset.Icc h g, ((Dset r s M₁ M₂ j (gam j t z)).card : ℝ) :=
        sum_prod_indicator_le s M₂ h g (fun j => Dset r s M₁ M₂ j (gam j t z))

end Work.BMF
