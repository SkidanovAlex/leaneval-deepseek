import Mathlib.Computability.Reduce
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseRowsL.LatticeCoulomb.telBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.telAxisLe`

The **axis fibre** of the telescoping sum: the sum of the absolute telescoping coefficients
`telG T j` over those points of `telW T j` whose transverse coordinates vanish.

## The mathematical content

`telG T j m = 1_{m∈T}/‖m‖² - ½·1_{m-e_j∈T}/‖m-e_j‖² - ½·1_{m+e_j∈T}/‖m+e_j‖²` is a second
difference of the function `f(m) = 1_{m∈T}/‖m‖²` along the `j`-th coordinate direction.  On the
axis fibre (`x.2 = 0` in the product coordinates of `telEq j`, i.e. `m = k • e_j`) the norm is
`‖k • e_j‖ = |k|`, so the summand is `|f_k - ½ f_{k-1} - ½ f_{k+1}|` with `f_k = 1_{k•e_j∈T}/k²`.

This is the `ρ → 0` case of `telFiberInterior`'s fibre estimate — but here the parameter `R` is
**large**, so the fibre is long and the `1/(k²+ρ²)` second-difference bound (`O(ρ⁻³)`) is not
available at all: one needs the *absolute* summability instead.  The proof here uses only the
elementary estimate

    ∑_{k∈ℤ} |f_k - ½ f_{k-1} - ½ f_{k+1}| ≤ ∑_{k∈ℤ} (f_k + ½ f_{k-1} + ½ f_{k+1}) = 2 ∑_{k∈ℤ} f_k

together with the sharp value `∑_{n≥1} 1/n² = π²/6`, giving the bound `2π²/3 = 6.579… ≤ 7`.
Numerically the true supremum of the left-hand side is `4` (attained for `1 ≤ R < 2`, i.e. for
`T = {±e₁, ±e₂, ±e₃}`, where the sum is `1 + 2·1 + 2·½`), so the constant `7` is valid but not
tight — the loss comes from the triangle inequality, which pays `f_k + ½f_{k-1} + ½f_{k+1}`
instead of the second-difference gain `≈ 3/k⁴`.

## The route (all in this file)

1. `telAxisLe`'s left-hand side is reindexed along the equivalence `telEq j`:
   `telG T j` on the image of `telW T j` becomes `telG T j m` over the filtered fibre
   `{m ∈ telW T j | (telEq j m).2 = 0}`;
2. on that fibre `m = m_j • e_j` (`telAxisFiberEq`), and the map `m ↦ m j` is injective there, so
   the sum is reindexed to a finset `K' ⊆ ℤ` with summand `telG T j (k • e_j)`;
3. `telG_axis` identifies the summand with the second difference of `telAxis T j`;
4. `telAxis_nonneg` / `telAxis_le` bound it pointwise by `1/(k²) + ½/(k-1)² + ½/(k+1)²`;
5. `telSumInvSqLe` bounds the sum of `1/k²` over **any** finset of integers by `π²/3`
   (split by sign, reindex to `ℕ` by `Int.toNat` / `k ↦ (-k).toNat`, and use Mathlib's
   `hasSum_zeta_two`), and the shifts `k ↦ k ± 1` are handled by reindexing;
6. the arithmetic `2π²/3 < 7` follows from Mathlib's `Real.pi_lt_d2` (`π < 3.15`).

Note that the hypotheses `h1`, `h2`, `h4` of `telAxisLe` (which state that `T` is exactly the set
of nonzero lattice points of norm `≤ R`) are **not** used: the estimate is a purely telescoping
bound, valid for every `T`; they are part of the requested interface (`T` is the ball in the
applications).  This is why no hypothesis is mentioned in the lemmas below.
-/

noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL.LatticeCoulomb

set_option autoImplicit false

/-! ### The axis value of the telescoping coefficient -/

/-- `telAxis T j k` is the telescoping coefficient `telG T j` evaluated at the lattice point
`k • e_j` on the `j`-th coordinate axis. -/
def telAxis (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (k : ℤ) : ℝ :=
  if k • telE j ∈ T then 1 / ‖nvec (k • telE j)‖ ^ 2 else 0

lemma telAxis_nonneg (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (k : ℤ) : 0 ≤ telAxis T j k := by
  rw [telAxis]; split_ifs <;> positivity

/-- `‖k • e_j‖ = |k|`. -/
lemma norm_nvec_zsmul_telE (j : Fin 3) (k : ℤ) : ‖nvec (k • telE j)‖ = |(k : ℝ)| := by
  rw [nvec_zsmul, norm_smul, norm_nvec_telE, mul_one, Real.norm_eq_abs]

lemma telAxis_le (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (k : ℤ) :
    telAxis T j k ≤ 1 / ((k : ℝ) ^ 2) := by
  rw [telAxis]
  split_ifs with h
  · rw [norm_nvec_zsmul_telE, sq_abs]
  · positivity

/-- **`telG` on the axis is the second difference of `telAxis`.** -/
lemma telG_axis (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (k : ℤ) :
    telG T j (k • telE j)
      = telAxis T j k - (1/2) * telAxis T j (k - 1) - (1/2) * telAxis T j (k + 1) := by
  have h1 : k • telE j - telE j = (k - 1) • telE j := by rw [sub_smul, one_smul]
  have h2 : k • telE j + telE j = (k + 1) • telE j := by rw [add_smul, one_smul]
  rw [telG, telAxis, telAxis, telAxis, h1, h2]

/-! ### The `ℤ`-lattice bound `∑ 1/k² ≤ π²/3` -/

/-- For **any** finite set of integers, `∑_{k∈K} 1/k² ≤ π²/3` (the sum over all of `ℤ`, split
by sign and reindexed to `ℕ`, against Mathlib's `∑_{n≥1} 1/n² = π²/6`). -/
lemma telSumInvSqLe (K : Finset ℤ) :
    ∑ k ∈ K, (1:ℝ) / ((k : ℝ) ^ 2) ≤ Real.pi ^ 2 / 3 := by
  have hsummable : Summable (fun n : ℕ => (1:ℝ) / ((n : ℝ) ^ 2)) := hasSum_zeta_two.summable
  have htsum : (∑' (n : ℕ), (1:ℝ) / ((n : ℝ) ^ 2)) = Real.pi ^ 2 / 6 :=
    hasSum_zeta_two.tsum_eq
  have key : ∀ (S : Finset ℕ), ∑ n ∈ S, (1:ℝ)/((n:ℝ)^2) ≤ Real.pi^2/6 := by
    intro S
    have h := Summable.sum_le_tsum S (fun n _ => by positivity) hsummable
    rwa [htsum] at h
  have hpos : (∑ k ∈ K.filter (fun k => 0 < k), (1:ℝ)/((k:ℝ)^2)) ≤ Real.pi^2/6 := by
    have hinj : Set.InjOn (fun k : ℤ => k.toNat) ↑(K.filter (fun k => 0 < k)) := by
      intro a ha b hb h
      have ha0 : (0:ℤ) ≤ a := le_of_lt (Finset.mem_filter.mp ha).2
      have hb0 : (0:ℤ) ≤ b := le_of_lt (Finset.mem_filter.mp hb).2
      have h' : a.toNat = b.toNat := h
      have h1 : (((a.toNat) : ℤ)) = a := Int.toNat_of_nonneg ha0
      have h2 : (((b.toNat) : ℤ)) = b := Int.toNat_of_nonneg hb0
      calc a = (((a.toNat) : ℤ)) := h1.symm
        _ = (((b.toNat) : ℤ)) := by exact_mod_cast h'
        _ = b := h2
    have htoNat : ∀ k ∈ K.filter (fun k => 0 < k),
        (1:ℝ)/((k:ℝ)^2) = 1/(((k.toNat : ℕ):ℝ)^2) := by
      intro k hk
      have hk0 : (0:ℤ) ≤ k := le_of_lt (Finset.mem_filter.mp hk).2
      have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hk0)
      rw [hcast]
    calc (∑ k ∈ K.filter (fun k => 0 < k), (1:ℝ)/((k:ℝ)^2))
        = ∑ k ∈ K.filter (fun k => 0 < k), (1:ℝ)/(((k.toNat : ℕ):ℝ)^2) :=
          Finset.sum_congr rfl htoNat
      _ = ∑ n ∈ (K.filter (fun k => 0 < k)).image (fun k : ℤ => k.toNat), (1:ℝ)/((n:ℝ)^2) :=
          (Finset.sum_image (f := fun n : ℕ => (1:ℝ)/((n:ℝ)^2))
            (g := fun k : ℤ => k.toNat) (s := K.filter (fun k => 0 < k)) hinj).symm
      _ ≤ Real.pi^2/6 := key _
  have hneg : (∑ k ∈ K.filter (fun k => k < 0), (1:ℝ)/((k:ℝ)^2)) ≤ Real.pi^2/6 := by
    have hinj : Set.InjOn (fun k : ℤ => (-k).toNat) ↑(K.filter (fun k => k < 0)) := by
      intro a ha b hb h
      have ha0 : (0:ℤ) ≤ -a := by have := (Finset.mem_filter.mp ha).2; omega
      have hb0 : (0:ℤ) ≤ -b := by have := (Finset.mem_filter.mp hb).2; omega
      have h' : (-a).toNat = (-b).toNat := h
      have h1 : ((((-a).toNat) : ℤ)) = -a := Int.toNat_of_nonneg ha0
      have h2 : ((((-b).toNat) : ℤ)) = -b := Int.toNat_of_nonneg hb0
      have h4 : (-a : ℤ) = -b := by
        calc (-a : ℤ) = ((((-a).toNat) : ℤ)) := h1.symm
          _ = ((((-b).toNat) : ℤ)) := by exact_mod_cast h'
          _ = -b := h2
      omega
    have htoNat : ∀ k ∈ K.filter (fun k => k < 0),
        (1:ℝ)/((k:ℝ)^2) = 1/((((-k).toNat : ℕ):ℝ)^2) := by
      intro k hk
      have hk0 : (0:ℤ) ≤ -k := by have := (Finset.mem_filter.mp hk).2; omega
      have hcast : ((((-k).toNat : ℕ)) : ℝ) = -((k:ℝ)) := by
        have h2 : ((((-k).toNat : ℕ)) : ℤ) = -k := Int.toNat_of_nonneg hk0
        have h3 : ((((-k).toNat : ℕ)) : ℝ) = ((-k : ℤ) : ℝ) := by exact_mod_cast h2
        rw [h3]; push_cast; ring
      rw [hcast, neg_sq]
    calc (∑ k ∈ K.filter (fun k => k < 0), (1:ℝ)/((k:ℝ)^2))
        = ∑ k ∈ K.filter (fun k => k < 0), (1:ℝ)/((((-k).toNat : ℕ):ℝ)^2) :=
          Finset.sum_congr rfl htoNat
      _ = ∑ n ∈ (K.filter (fun k => k < 0)).image (fun k : ℤ => (-k).toNat), (1:ℝ)/((n:ℝ)^2) :=
          (Finset.sum_image (f := fun n : ℕ => (1:ℝ)/((n:ℝ)^2))
            (g := fun k : ℤ => (-k).toNat) (s := K.filter (fun k => k < 0)) hinj).symm
      _ ≤ Real.pi^2/6 := key _
  have hU : K.filter (fun k => ¬ 0 < k)
      = (K.filter (fun k => k < 0)) ∪ (K.filter (fun k => k = 0)) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hk, hk1⟩
      rcases lt_trichotomy k 0 with h | h | h
      · exact Or.inl ⟨hk, h⟩
      · exact Or.inr ⟨hk, h⟩
      · omega
    · rintro (⟨hk, hk1⟩ | ⟨hk, hk1⟩)
      · exact ⟨hk, by omega⟩
      · exact ⟨hk, by omega⟩
  have hdisj : Disjoint (K.filter (fun k => k < 0)) (K.filter (fun k => k = 0)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    have h1 := (Finset.mem_filter.mp hk).2
    have h2 := (Finset.mem_filter.mp hk').2
    omega
  have hzero : (∑ k ∈ K.filter (fun k => k = 0), (1:ℝ)/((k:ℝ)^2)) = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk0 : k = 0 := (Finset.mem_filter.mp hk).2
    rw [hk0]; simp
  calc ∑ k ∈ K, (1:ℝ)/((k:ℝ)^2)
      = (∑ k ∈ K.filter (fun k => 0 < k), (1:ℝ)/((k:ℝ)^2))
        + (∑ k ∈ K.filter (fun k => ¬ 0 < k), (1:ℝ)/((k:ℝ)^2)) :=
        (Finset.sum_filter_add_sum_filter_not K (fun k => 0 < k) _).symm
    _ = (∑ k ∈ K.filter (fun k => 0 < k), (1:ℝ)/((k:ℝ)^2))
        + ((∑ k ∈ K.filter (fun k => k < 0), (1:ℝ)/((k:ℝ)^2))
           + (∑ k ∈ K.filter (fun k => k = 0), (1:ℝ)/((k:ℝ)^2))) := by
        rw [hU, Finset.sum_union hdisj]
    _ = (∑ k ∈ K.filter (fun k => 0 < k), (1:ℝ)/((k:ℝ)^2))
        + (∑ k ∈ K.filter (fun k => k < 0), (1:ℝ)/((k:ℝ)^2)) := by
        rw [hzero, add_zero]
    _ ≤ Real.pi^2/6 + Real.pi^2/6 := add_le_add hpos hneg
    _ = Real.pi^2/3 := by ring

/-! ### The axis fibre in product coordinates -/

/-- On the axis fibre (all transverse coordinates zero) the point is `m j • e_j`. -/
lemma telAxisFiberEq (j : Fin 3) (m : Fin 3 → ℤ) :
    (telEq j m).2 = 0 ↔ m = m j • telE j := by
  constructor
  · intro h
    funext i
    by_cases hi : i = j
    · subst hi; simp [telE]
    · have hm : m i = 0 := by
        have hc := congr_fun h ⟨i, hi⟩
        rwa [telEq_snd] at hc
      simp [hm, telE, hi]
  · intro h
    funext i
    have hm : m i = 0 := by
      have hc := congr_fun h i.1
      rw [Pi.smul_apply, zsmul_eq_mul, telE_ne i.2, mul_zero] at hc
      exact hc
    rw [telEq_snd, hm]; simp

/-! ### The target -/

theorem telAxisLe (R : ℝ) (hR : 1 ≤ R) (T : Finset (Fin 3 → ℤ)) (j : Fin 3)
    (h1 : ∀ n ∈ T, n ≠ 0) (h2 : ∀ n ∈ T, ‖nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖nvec n‖ ≤ R → n ∈ T) :
    (∑ x ∈ ((telW T j).map (telEq j).toEmbedding).filter (fun x => x.2 = 0),
        |telG T j ((telEq j).symm x)|) ≤ 7 := by
  classical
  -- Step 1: reindex along `telEq j`, so the sum runs over the axis fibre of `telW T j`.
  have hstep1 : (∑ x ∈ ((telW T j).map (telEq j).toEmbedding).filter (fun x => x.2 = 0),
        |telG T j ((telEq j).symm x)|)
      = ∑ m ∈ (telW T j).filter (fun m => (telEq j m).2 = 0), |telG T j m| := by
    rw [Finset.sum_filter, Finset.sum_map, ← Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    simp
  -- Step 2: the axis fibre is indexed by `k = m j ∈ ℤ`.
  set K' : Finset ℤ := ((telW T j).filter (fun m => (telEq j m).2 = 0)).image (fun m => m j)
    with hK'
  have hinj : Set.InjOn (fun m : Fin 3 → ℤ => m j)
      ↑((telW T j).filter (fun m => (telEq j m).2 = 0)) := by
    intro a ha b hb h
    have h' : a j = b j := h
    have ha' := (telAxisFiberEq j a).mp (Finset.mem_filter.mp ha).2
    have hb' := (telAxisFiberEq j b).mp (Finset.mem_filter.mp hb).2
    rw [ha', hb', h']
  have hcongr : (∑ m ∈ (telW T j).filter (fun m => (telEq j m).2 = 0), |telG T j m|)
      = ∑ m ∈ (telW T j).filter (fun m => (telEq j m).2 = 0), |telG T j (m j • telE j)| := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [show |telG T j m| = |telG T j (m j • telE j)| from
      congrArg (fun z => |telG T j z|) ((telAxisFiberEq j m).mp (Finset.mem_filter.mp hm).2)]
  have hisum := Finset.sum_image (s := (telW T j).filter (fun m => (telEq j m).2 = 0))
    (g := fun m : Fin 3 → ℤ => m j) (f := fun k : ℤ => |telG T j (k • telE j)|) hinj
  have hstep2 : (∑ m ∈ (telW T j).filter (fun m => (telEq j m).2 = 0), |telG T j m|)
      = ∑ k ∈ K', |telG T j (k • telE j)| := hcongr.trans hisum.symm
  -- Step 3: the pointwise bound, via the triangle inequality and `telAxis`.
  have hpt : ∀ k : ℤ, |telG T j (k • telE j)| ≤
      1/((k:ℝ)^2) + (1/2) * (1/(((k - 1 : ℤ) : ℝ)^2)) + (1/2) * (1/(((k + 1 : ℤ) : ℝ)^2)) := by
    intro k
    have hB0 := telAxis_nonneg T j (k - 1)
    have hC0 := telAxis_nonneg T j (k + 1)
    have hA1 := telAxis_le T j k
    have hB1 := telAxis_le T j (k - 1)
    have hC1 := telAxis_le T j (k + 1)
    have hAb : |telAxis T j k| = telAxis T j k := abs_of_nonneg (telAxis_nonneg T j k)
    have hBb : |(1/2) * telAxis T j (k - 1)| = (1/2) * telAxis T j (k - 1) :=
      abs_of_nonneg (by linarith)
    have hCb : |(1/2) * telAxis T j (k + 1)| = (1/2) * telAxis T j (k + 1) :=
      abs_of_nonneg (by linarith)
    have htri : |telAxis T j k - (1/2) * telAxis T j (k - 1) - (1/2) * telAxis T j (k + 1)|
        ≤ telAxis T j k + (1/2) * telAxis T j (k - 1) + (1/2) * telAxis T j (k + 1) := by
      have h1 : |telAxis T j k - (1/2) * telAxis T j (k - 1) - (1/2) * telAxis T j (k + 1)|
          ≤ |telAxis T j k - (1/2) * telAxis T j (k - 1)| + |(1/2) * telAxis T j (k + 1)| := by
        simpa using abs_sub_le (telAxis T j k - (1/2) * telAxis T j (k - 1)) 0
          ((1/2) * telAxis T j (k + 1))
      have h2 : |telAxis T j k - (1/2) * telAxis T j (k - 1)|
          ≤ |telAxis T j k| + |(1/2) * telAxis T j (k - 1)| := by
        simpa using abs_sub_le (telAxis T j k) 0 ((1/2) * telAxis T j (k - 1))
      rw [hCb] at h1
      rw [hAb, hBb] at h2
      linarith
    calc |telG T j (k • telE j)|
        = |telAxis T j k - (1/2) * telAxis T j (k - 1) - (1/2) * telAxis T j (k + 1)| := by
          rw [telG_axis]
      _ ≤ telAxis T j k + (1/2) * telAxis T j (k - 1) + (1/2) * telAxis T j (k + 1) := htri
      _ ≤ 1/((k:ℝ)^2) + (1/2) * (1/(((k - 1 : ℤ) : ℝ)^2)) + (1/2) * (1/(((k + 1 : ℤ) : ℝ)^2)) := by
          linarith
  -- Step 4: sum the bound; each of the three lattice sums is `≤ π²/3`.
  have hsum : (∑ k ∈ K', |telG T j (k • telE j)|) ≤ 2 * Real.pi^2 / 3 := by
    calc (∑ k ∈ K', |telG T j (k • telE j)|)
        ≤ ∑ k ∈ K', (1/((k:ℝ)^2) + (1/2) * (1/(((k - 1 : ℤ) : ℝ)^2))
            + (1/2) * (1/(((k + 1 : ℤ) : ℝ)^2))) := Finset.sum_le_sum (fun k _ => hpt k)
      _ = (∑ k ∈ K', 1/((k:ℝ)^2)) + (1/2) * (∑ k ∈ K', 1/(((k - 1 : ℤ) : ℝ)^2))
          + (1/2) * (∑ k ∈ K', 1/(((k + 1 : ℤ) : ℝ)^2)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 2 * Real.pi^2 / 3 := by
          have hA := telSumInvSqLe K'
          have hB : (∑ k ∈ K', 1/(((k - 1 : ℤ) : ℝ)^2)) ≤ Real.pi^2/3 := by
            have hi : Set.InjOn (fun k : ℤ => k - 1) ↑K' := by
              intro a _ b _ h
              have h' : a - 1 = b - 1 := h
              omega
            rw [← Finset.sum_image (f := fun m : ℤ => (1:ℝ)/((m:ℝ)^2))
              (g := fun k : ℤ => k - 1) (s := K') hi]
            exact telSumInvSqLe _
          have hC : (∑ k ∈ K', 1/(((k + 1 : ℤ) : ℝ)^2)) ≤ Real.pi^2/3 := by
            have hi : Set.InjOn (fun k : ℤ => k + 1) ↑K' := by
              intro a _ b _ h
              have h' : a + 1 = b + 1 := h
              omega
            rw [← Finset.sum_image (f := fun m : ℤ => (1:ℝ)/((m:ℝ)^2))
              (g := fun k : ℤ => k + 1) (s := K') hi]
            exact telSumInvSqLe _
          linarith
  -- Step 5: `2π²/3 < 7`.
  have hpi : 2 * Real.pi^2 / 3 < 7 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  linarith [hstep1, hstep2, hsum, hpi]

end Work.BoseRowsL.LatticeCoulomb
