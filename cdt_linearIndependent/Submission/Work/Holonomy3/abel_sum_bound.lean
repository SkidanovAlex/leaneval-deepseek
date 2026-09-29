import Mathlib
import Submission.Work.Holonomy3.seeding_defs
import Submission.Work.Holonomy3.block_sum_bound
import Submission.Work.Holonomy3.card_blockIdx_close
import Submission.Work.Holonomy3.abel_fin_identity

/-!
# The Abel summation bound of the seeding estimate (`§Seeding`)

Let `γ : Fin (l+2) → ℝ` be the (strictly increasing) division points with `γ 0 = 0` and
`γ_{l+1} = m`, and let `blockIdx m γ j` be the block index of the rank `j` (the block
`[γ_k/m, γ_{k+1}/m)` containing `j/d`).  Writing `n_j` for the (sorted) seed coordinates and
`L_k` for the logarithm of the analytic growth rate attached to the `k`-th block, this file proves

`(m d D/2)·(L_l − m⁻² ∑_{k<l} γ_{k+1}² (L_{k+1} − L_k)) ≤ ∑_j n_j L_{k(j)} + (m d D)·B·(ε + 16(l+1)/d)`,

the elementary seeding estimate of the paper's §"Seeding": the main term obtained by Abel
summation from the block sums is bounded by the actual weighted sum of the `n_j` plus the two
error terms (the `ε`-error of the seeding hypothesis and the `5`-error of the discrete block sum).

The proof is a finite, elementary estimate:

* **Fibre decomposition.**  `∑_j n_j L_{k(j)} = ∑_k L_k N_k` with `N_k = ∑_{j : k(j)=k} n_j`.
* **Seeding error.**  `|N_k − (mD/d)·S_k| ≤ mDε·|{k(j)=k}|` where `S_k = ∑_{j:k(j)=k} j`, since
  `|n_j − mD(j/d)| ≤ mDε` pointwise; summing the fibre cardinalities gives exactly `d`.
* **Discrete block sum** (`block_sum_bound`):  `|S_k/d − (d/2)(b_k²−a_k²)| ≤ 5` for the block
  `[a_k,b_k) = [γ_k/m, γ_{k+1}/m)`, i.e. `|(mD/d)S_k − (dD/2m)(γ_{k+1}²−γ_k²)| ≤ 5mD`.
* **Abel summation** (`abel_fin_identity`):  `∑_k (γ_{k+1}²−γ_k²)L_k = m²L_l − ∑_{k<l}γ_{k+1}²(L_{k+1}−L_k)`
  turns the sum of the block main terms back into the closed expression on the left-hand side.
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- Transfer a two-sided bound on a difference to the difference of the two products with a factor
`L` bounded by `B`. -/
lemma abs_mul_sub_le {x y L B e : ℝ} (hL : |L| ≤ B) (h : |x - y| ≤ e) :
    |x * L - y * L| ≤ B * e := by
  have h2 : x * L - y * L = (x - y) * L := by ring
  rw [h2, abs_mul]
  calc |x - y| * |L| ≤ e * B := mul_le_mul h hL (abs_nonneg _) (le_trans (abs_nonneg _) h)
    _ = B * e := by ring

/-- **The discrete block sum, in `j`-scale.**  The sum of the ranks `j` belonging to the `k`-th
block equals `d²(γ_{k+1}² − γ_k²)/(2m²)` up to an absolute error of `5d`.  This is
`block_sum_bound` (which bounds the sum of `j/d`) multiplied by `d`, after rewriting the block
`{j : blockIdx m γ j = k}` as the lattice filter `{j : γ_k/m ≤ j/d < γ_{k+1}/m}`. -/
lemma fiber_j_sum_bound {l d : ℕ} (m : ℕ) (hm : 0 < m) (hd : 0 < d)
    (γ : Fin (l + 2) → ℝ) (hγ0 : γ 0 = 0) (hγlast : γ (Fin.last (l + 1)) = m)
    (hmono : StrictMono γ) (k : Fin (l + 1)) :
    |(∑ j ∈ Finset.univ.filter (fun j : Fin d => blockIdx m γ j = k), (j : ℝ))
      - (d : ℝ) ^ 2 / (2 * (m : ℝ) ^ 2) * ((γ k.succ) ^ 2 - (γ k.castSucc) ^ 2)| ≤ 5 * (d : ℝ) := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
  set a : ℝ := γ k.castSucc / (m:ℝ) with ha
  set b : ℝ := γ k.succ / (m:ℝ) with hb
  have ha0 : 0 ≤ a := by
    rw [ha]
    refine div_nonneg ?_ hmR.le
    have h := hmono.monotone (Fin.zero_le k.castSucc)
    rw [hγ0] at h; exact h
  have hab : a ≤ b := by
    rw [ha, hb]
    refine div_le_div_of_nonneg_right ?_ hmR.le
    apply hmono.monotone
    rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]; omega
  have hb1 : b ≤ 1 := by
    rw [hb]
    have hle : γ k.succ ≤ (m:ℝ) := by
      rw [← hγlast]
      apply hmono.monotone
      rw [Fin.le_iff_val_le_val]; simp only [Fin.val_succ, Fin.val_last]; omega
    calc γ k.succ / (m:ℝ) ≤ (m:ℝ) / (m:ℝ) := div_le_div_of_nonneg_right hle hmR.le
      _ = 1 := div_self hmne
  have hset : Finset.univ.filter (fun j : Fin d => blockIdx m γ j = k)
      = Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b) := by
    apply Finset.filter_congr
    intro j _
    rw [ha, hb]
    exact CBC.blockIdx_iff m hm hd γ hγ0 hγlast hmono j k
  have hT : (∑ j ∈ Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b), (j:ℝ))
      = (d:ℝ) * (∑ j ∈ Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b),
          (j:ℝ)/(d:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hbs := block_sum_bound hd (a := a) (b := b) ha0 hab hb1
  rw [hset, hT]
  have hnum : (d:ℝ)^2/(2*(m:ℝ)^2)*((γ k.succ)^2 - (γ k.castSucc)^2)
      = (d:ℝ)*((d:ℝ)/2*(b^2-a^2)) := by
    rw [ha, hb]; field_simp
  rw [hnum]
  calc |(d:ℝ) * (∑ j ∈ Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b),
          (j:ℝ)/(d:ℝ)) - (d:ℝ)*((d:ℝ)/2*(b^2-a^2))|
      = (d:ℝ) * |(∑ j ∈ Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b),
          (j:ℝ)/(d:ℝ)) - (d:ℝ)/2*(b^2-a^2)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (le_of_lt hdR)]
    _ ≤ (d:ℝ) * 5 := mul_le_mul_of_nonneg_left hbs (le_of_lt hdR)
    _ = 5*(d:ℝ) := by ring

theorem abel_sum_bound {l d : ℕ} (m D : ℕ) (hm : 0 < m) (hd : 0 < d)
    (γ : Fin (l + 2) → ℝ) (hγ0 : γ 0 = 0) (hγlast : γ (Fin.last (l + 1)) = m)
    (hmono : StrictMono γ) (L : Fin (l + 1) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hLB : ∀ k, |L k| ≤ B)
    (n : Fin d → ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ j : Fin d, |(n j : ℝ) - (m : ℝ) * D * ((j : ℝ) / d)| ≤ (m : ℝ) * D * ε) :
    ((m : ℝ) * d * D / 2) * (L (Fin.last l) -
        (1 / (m : ℝ) ^ 2) * ∑ k : Fin l,
          (γ k.succ.castSucc) ^ 2 * (L k.succ - L k.castSucc))
      ≤ ∑ j : Fin d, (n j : ℝ) * L (blockIdx m γ j)
        + ((m : ℝ) * d * D) * B * (ε + 16 * ((l : ℝ) + 1) / d) := by
  classical
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hmne : (m:ℝ) ≠ 0 := ne_of_gt hmR
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdR
  let FIB : Fin (l+1) → Finset (Fin d) := fun k => Finset.univ.filter (fun j : Fin d => blockIdx m γ j = k)
  have hT : ∑ j : Fin d, (n j : ℝ) * L (blockIdx m γ j)
      = ∑ k : Fin (l+1), (∑ j ∈ FIB k, (n j : ℝ)) * L k := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin d)))
          (t := (Finset.univ : Finset (Fin (l+1))))
          (g := fun j => blockIdx m γ j) (fun i _ => Finset.mem_univ _)
          (fun i => (n i : ℝ) * L (blockIdx m γ i))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [(Finset.mem_filter.mp hj).2]
  have hN : ∀ k : Fin (l+1), |(∑ j ∈ FIB k, (n j : ℝ)) - ((m:ℝ)*D/(d:ℝ)) * (∑ j ∈ FIB k, (j:ℝ))|
      ≤ (m:ℝ)*D*ε*((FIB k).card : ℝ) := by
    intro k
    have h1 : ((m:ℝ)*D/(d:ℝ)) * (∑ j ∈ FIB k, (j:ℝ)) = ∑ j ∈ FIB k, (m:ℝ)*D*((j:ℝ)/d) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [h1, ← Finset.sum_sub_distrib]
    calc |∑ j ∈ FIB k, ((n j : ℝ) - (m:ℝ)*D*((j:ℝ)/d))|
        ≤ ∑ j ∈ FIB k, |(n j : ℝ) - (m:ℝ)*D*((j:ℝ)/d)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ FIB k, ((m:ℝ)*D*ε) := Finset.sum_le_sum (fun j _ => hb j)
      _ = (m:ℝ)*D*ε*((FIB k).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hS : ∀ k : Fin (l+1), |(∑ j ∈ FIB k, (j:ℝ)) - (d:ℝ)^2/(2*(m:ℝ)^2)*((γ k.succ)^2 - (γ k.castSucc)^2)| ≤ 5*(d:ℝ) := by
    intro k
    change |(∑ j ∈ Finset.univ.filter (fun j : Fin d => blockIdx m γ j = k), (j:ℝ))
        - (d:ℝ)^2/(2*(m:ℝ)^2)*((γ k.succ)^2 - (γ k.castSucc)^2)| ≤ 5*(d:ℝ)
    exact fiber_j_sum_bound m hm hd γ hγ0 hγlast hmono k
  have hcomb : ∀ k : Fin (l+1),
      |(∑ j ∈ FIB k, (n j : ℝ)) * L k - (((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)) * L k|
      ≤ B * ((m:ℝ)*D*ε*((FIB k).card : ℝ) + 5*(m:ℝ)*D) := by
    intro k
    have hBC : |((m:ℝ)*D/(d:ℝ))*(∑ j ∈ FIB k, (j:ℝ)) - ((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)| ≤ 5*(m:ℝ)*D := by
      have h2 : ((m:ℝ)*D/(d:ℝ))*(∑ j ∈ FIB k, (j:ℝ)) - ((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)
          = ((m:ℝ)*D/(d:ℝ)) * ((∑ j ∈ FIB k, (j:ℝ)) - (d:ℝ)^2/(2*(m:ℝ)^2)*((γ k.succ)^2 - (γ k.castSucc)^2)) := by
        field_simp
      rw [h2, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)*D/(d:ℝ))]
      calc ((m:ℝ)*D/(d:ℝ)) * |(∑ j ∈ FIB k, (j:ℝ)) - (d:ℝ)^2/(2*(m:ℝ)^2)*((γ k.succ)^2 - (γ k.castSucc)^2)|
          ≤ ((m:ℝ)*D/(d:ℝ)) * (5*(d:ℝ)) := mul_le_mul_of_nonneg_left (hS k) (by positivity)
        _ = 5*(m:ℝ)*D := by field_simp
    have hkey : |(∑ j ∈ FIB k, (n j : ℝ)) - ((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)|
        ≤ (m:ℝ)*D*ε*((FIB k).card : ℝ) + 5*(m:ℝ)*D := by
      have h3 : (∑ j ∈ FIB k, (n j : ℝ)) - ((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)
          = ((∑ j ∈ FIB k, (n j : ℝ)) - ((m:ℝ)*D/(d:ℝ))*(∑ j ∈ FIB k, (j:ℝ)))
            + (((m:ℝ)*D/(d:ℝ))*(∑ j ∈ FIB k, (j:ℝ)) - ((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)) := by
        ring
      rw [h3]
      exact le_trans (abs_add_le _ _) (add_le_add (hN k) hBC)
    calc |(∑ j ∈ FIB k, (n j : ℝ)) * L k - (((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)) * L k|
        ≤ B * |(∑ j ∈ FIB k, (n j : ℝ)) - ((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)| :=
          abs_mul_sub_le (hLB k) (le_refl _)
      _ ≤ B * ((m:ℝ)*D*ε*((FIB k).card : ℝ) + 5*(m:ℝ)*D) := mul_le_mul_of_nonneg_left hkey hB
  have hfact : (∑ k : Fin (l+1), (((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)) * L k)
      = ((d:ℝ)*D/(2*(m:ℝ))) * (∑ k : Fin (l+1), ((γ k.succ)^2 - (γ k.castSucc)^2) * L k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => by ring)
  have hcard : (∑ k : Fin (l+1), ((FIB k).card : ℝ)) = (d:ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin d)))
      (t := (Finset.univ : Finset (Fin (l+1)))) (f := fun j : Fin d => blockIdx m γ j)
      (fun i _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h3 : (d:ℝ) = ∑ k : Fin (l+1), ((FIB k).card : ℝ) := by exact_mod_cast h
    exact h3.symm
  have hsum : |(∑ k : Fin (l+1), (∑ j ∈ FIB k, (n j:ℝ)) * L k)
      - ((d:ℝ)*D/(2*(m:ℝ))) * (∑ k : Fin (l+1), ((γ k.succ)^2 - (γ k.castSucc)^2) * L k)|
      ≤ B * ((m:ℝ)*D*ε*(d:ℝ) + 5*(m:ℝ)*D*((l:ℝ)+1)) := by
    have hstep : (∑ k : Fin (l+1), (∑ j ∈ FIB k, (n j:ℝ)) * L k)
        - ((d:ℝ)*D/(2*(m:ℝ))) * (∑ k : Fin (l+1), ((γ k.succ)^2 - (γ k.castSucc)^2) * L k)
        = ∑ k : Fin (l+1), ((∑ j ∈ FIB k, (n j:ℝ)) * L k - (((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)) * L k) := by
      rw [Finset.sum_sub_distrib, hfact]
    rw [hstep]
    calc |∑ k : Fin (l+1), ((∑ j ∈ FIB k, (n j:ℝ)) * L k - (((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)) * L k)|
        ≤ ∑ k : Fin (l+1), |(∑ j ∈ FIB k, (n j:ℝ)) * L k - (((d:ℝ)*D/(2*(m:ℝ))) * ((γ k.succ)^2 - (γ k.castSucc)^2)) * L k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (l+1), B * ((m:ℝ)*D*ε*((FIB k).card : ℝ) + 5*(m:ℝ)*D) := Finset.sum_le_sum (fun k _ => hcomb k)
      _ = B * ((m:ℝ)*D*ε*(d:ℝ) + 5*(m:ℝ)*D*((l:ℝ)+1)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcard]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hT' : |(∑ j : Fin d, (n j : ℝ) * L (blockIdx m γ j))
      - ((d:ℝ)*D/(2*(m:ℝ))) * (∑ k : Fin (l+1), ((γ k.succ)^2 - (γ k.castSucc)^2) * L k)|
      ≤ B * ((m:ℝ)*D*ε*(d:ℝ) + 5*(m:ℝ)*D*((l:ℝ)+1)) := by
    rw [hT]; exact hsum
  have hAb' : (∑ k : Fin (l+1), ((γ k.succ)^2 - (γ k.castSucc)^2) * L k)
      = (m:ℝ)^2 * L (Fin.last l) - ∑ k : Fin l, (γ k.succ.castSucc)^2 * (L k.succ - L k.castSucc) := by
    rw [abel_fin_identity γ hγ0 L, hγlast]
  have hLHS : ((m:ℝ)*d*D/2) * (L (Fin.last l) - (1/(m:ℝ)^2) * (∑ k : Fin l, (γ k.succ.castSucc)^2 * (L k.succ - L k.castSucc)))
      = ((d:ℝ)*D/(2*(m:ℝ))) * (∑ k : Fin (l+1), ((γ k.succ)^2 - (γ k.castSucc)^2) * L k) := by
    rw [hAb']
    field_simp
  have h4 : B * ((m:ℝ)*D*ε*(d:ℝ) + 5*(m:ℝ)*D*((l:ℝ)+1)) ≤ ((m:ℝ)*d*D)*B*(ε + 16*((l:ℝ)+1)/d) := by
    have hexp : ((m:ℝ)*d*D)*B*(ε + 16*((l:ℝ)+1)/d) = ((m:ℝ)*d*D)*B*ε + 16*((m:ℝ)*D)*B*((l:ℝ)+1) := by
      rw [mul_add]
      congr 1
      field_simp
    rw [hexp]
    have hX : (0:ℝ) ≤ ((m:ℝ)*D*B)*((l:ℝ)+1) :=
      mul_nonneg (mul_nonneg (by positivity) hB) (by positivity)
    nlinarith [hX]
  rw [hLHS]
  have h1 := (abs_le.mp hT').1
  linarith

end Work.Holonomy3
