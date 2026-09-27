import Mathlib

namespace Work.Drive

noncomputable section

/-- The open half-space `{(x, t) | 0 < t}`, on which the square-root substitution is smooth. -/
private abbrev substSet (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Set (X × ℝ) :=
  Set.univ ×ˢ Set.Ioi (0 : ℝ)

/-- The substitution `(x, t) ↦ (x, √t)`. -/
private abbrev substMap (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : X × ℝ → X × ℝ :=
  fun y => (y.1, Real.sqrt y.2)

private lemma isOpen_substSet (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    IsOpen (substSet X) := isOpen_univ.prod isOpen_Ioi

private lemma contDiffAt_substMap (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    {y : X × ℝ} (hy : 0 < y.2) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (substMap X) y := by
  apply ContDiffAt.prodMk contDiffAt_fst
  apply ContDiffAt.sqrt contDiffAt_snd
  exact ne_of_gt hy

private lemma contDiffOn_substMap (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (substMap X) (substSet X) := by
  apply ContDiffOn.prodMk contDiffOn_fst
  apply ContDiffOn.sqrt contDiffOn_snd
  intro y hy
  simp only [substSet, Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hy
  exact ne_of_gt hy

private lemma mapsTo_substMap (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    Set.MapsTo (substMap X) (substSet X) (substSet X) := by
  intro y hy
  simp only [substSet, substMap, Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and] at hy ⊢
  exact Real.sqrt_pos.2 hy

/-- The sizes of the parts of an ordered finpartition of `Fin k` add up to `k`. -/
private lemma sum_partSize {k : ℕ} (c : OrderedFinpartition k) :
    ∑ i : Fin c.length, c.partSize i = k := by
  have h := Fintype.card_congr c.equivSigma
  rw [Fintype.card_fin, Fintype.card_sigma] at h
  simpa using h

private lemma sum_partSize_sub_one {k : ℕ} (c : OrderedFinpartition k) :
    ∑ i : Fin c.length, (c.partSize i - 1) = k - c.length := by
  have h1 : ∀ i : Fin c.length, c.partSize i - 1 + 1 = c.partSize i :=
    fun i => Nat.sub_add_cancel (c.partSize_pos i)
  have h3 : (∑ i : Fin c.length, (c.partSize i - 1 + 1)) = k := by
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    exact sum_partSize c
  have h2 : (∑ i : Fin c.length, (c.partSize i - 1)) + c.length = k := by
    rw [Finset.sum_add_distrib] at h3
    simpa using h3
  omega

private lemma sum_two_partSize_sub_one {k : ℕ} (c : OrderedFinpartition k) :
    ∑ i : Fin c.length, (2 * c.partSize i - 1) = 2 * k - c.length := by
  have hle : c.length ≤ k := c.length_le
  have h4 : ∀ i : Fin c.length, 2 * c.partSize i - 1 = 2 * (c.partSize i - 1) + 1 :=
    fun i => by have := c.partSize_pos i; omega
  have h5 : (∑ i : Fin c.length, (2 * c.partSize i - 1)) = 2 * (k - c.length) + c.length := by
    rw [Finset.sum_congr rfl (fun i _ => h4 i)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_partSize_sub_one c]
    simp
  omega

/-- Weighted Faà di Bruno estimate for the square-root substitution.  If the derivatives of the
substitution `σ y = (y.1, √y.2)` at `z` (of order `≥ 1`) are bounded by `b` times the
appropriate negative power of `√z.2`, then the `k`-th derivative of `Φ ∘ σ` at `z` is bounded by
the size of the finite set of ordered partitions of `Fin k` times the weighted sum of the
derivatives of `Φ` at `σ z`. -/
private theorem subst_taylor_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : ℕ → ℝ) (hb0 : ∀ m, 0 ≤ b m)
    (hb : ∀ (m : ℕ) (z : X × ℝ), 0 < z.2 → z.2 ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun y : X × ℝ => fderiv ℝ (substMap X) y) z‖ ≤
        b m / (Real.sqrt z.2) ^ (1 + 2 * m))
    (k : ℕ) (z : X × ℝ) (hz0 : 0 < z.2) (hz1 : z.2 ≤ 1)
    (Φ : X × ℝ → F) (hΦ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (substMap X z)) :
    ‖iteratedFDeriv ℝ k (fun y : X × ℝ => Φ (substMap X y)) z‖ ≤
      (∑ c : OrderedFinpartition k, ∏ i : Fin c.length, b (c.partSize i - 1)) *
        ∑ j ∈ Finset.range (k + 1),
          ‖iteratedFDeriv ℝ j Φ (substMap X z)‖ * (Real.sqrt z.2)⁻¹ ^ (2 * k - j) := by
  have hQnn : 0 ≤ (Real.sqrt z.2)⁻¹ := by positivity
  have hFB : iteratedFDeriv ℝ k (fun y : X × ℝ => Φ (substMap X y)) z =
      (ftaylorSeries ℝ Φ (substMap X z)).taylorComp (ftaylorSeries ℝ (substMap X) z) k := by
    have h := iteratedFDeriv_comp (𝕜 := ℝ) (E := X × ℝ) (F := X × ℝ) (G := F)
      (f := substMap X) (g := Φ) (x := z) hΦ (contDiffAt_substMap X hz0) (i := k)
      (by exact_mod_cast le_top)
    simpa [Function.comp_def] using h
  rw [hFB]
  calc ‖∑ c : OrderedFinpartition k, (ftaylorSeries ℝ Φ (substMap X z)).compAlongOrderedFinpartition
          (ftaylorSeries ℝ (substMap X) z) c‖
      ≤ ∑ c : OrderedFinpartition k, ‖(ftaylorSeries ℝ Φ (substMap X z)).compAlongOrderedFinpartition
          (ftaylorSeries ℝ (substMap X) z) c‖ := norm_sum_le _ _
    _ ≤ ∑ c : OrderedFinpartition k,
          ‖ftaylorSeries ℝ Φ (substMap X z) c.length‖ *
            ∏ i : Fin c.length, ‖ftaylorSeries ℝ (substMap X) z (c.partSize i)‖ := by
        refine Finset.sum_le_sum fun c _ => ?_
        exact OrderedFinpartition.norm_compAlongOrderedFinpartition_le c _ _
    _ ≤ ∑ c : OrderedFinpartition k,
          (∏ i : Fin c.length, b (c.partSize i - 1)) *
            (∑ j ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ j Φ (substMap X z)‖ * (Real.sqrt z.2)⁻¹ ^ (2 * k - j)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hprod : ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) (substMap X) z‖ ≤
            (∏ i : Fin c.length, b (c.partSize i - 1)) *
              (Real.sqrt z.2)⁻¹ ^ (2 * k - c.length) := by
          have h1 : ∀ i : Fin c.length,
              ‖iteratedFDeriv ℝ (c.partSize i) (substMap X) z‖ ≤
                b (c.partSize i - 1) * (Real.sqrt z.2)⁻¹ ^ (2 * c.partSize i - 1) := by
            intro i
            have hpos : 0 < c.partSize i := c.partSize_pos i
            have hnorm : ‖iteratedFDeriv ℝ (c.partSize i - 1)
                  (fun y : X × ℝ => fderiv ℝ (substMap X) y) z‖ =
                ‖iteratedFDeriv ℝ (c.partSize i) (substMap X) z‖ := by
              rw [norm_iteratedFDeriv_fderiv, Nat.sub_add_cancel hpos]
            rw [← hnorm]
            refine (hb (c.partSize i - 1) z hz0 hz1).trans ?_
            rw [div_eq_mul_inv, ← inv_pow,
              show 1 + 2 * (c.partSize i - 1) = 2 * c.partSize i - 1 from by omega]
          calc ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) (substMap X) z‖
              ≤ ∏ i : Fin c.length,
                  (b (c.partSize i - 1) * (Real.sqrt z.2)⁻¹ ^ (2 * c.partSize i - 1)) :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h1 i)
            _ = (∏ i : Fin c.length, b (c.partSize i - 1)) *
                  ∏ i : Fin c.length, (Real.sqrt z.2)⁻¹ ^ (2 * c.partSize i - 1) :=
                Finset.prod_mul_distrib
            _ = (∏ i : Fin c.length, b (c.partSize i - 1)) *
                  (Real.sqrt z.2)⁻¹ ^ (∑ i : Fin c.length, (2 * c.partSize i - 1)) := by
                rw [Finset.prod_pow_eq_pow_sum]
            _ = (∏ i : Fin c.length, b (c.partSize i - 1)) *
                  (Real.sqrt z.2)⁻¹ ^ (2 * k - c.length) := by
                rw [sum_two_partSize_sub_one c]
        have hterm : ‖iteratedFDeriv ℝ c.length Φ (substMap X z)‖ *
              (Real.sqrt z.2)⁻¹ ^ (2 * k - c.length) ≤
            ∑ j ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ j Φ (substMap X z)‖ * (Real.sqrt z.2)⁻¹ ^ (2 * k - j) :=
          Finset.single_le_sum (s := Finset.range (k + 1))
            (f := fun j => ‖iteratedFDeriv ℝ j Φ (substMap X z)‖ * (Real.sqrt z.2)⁻¹ ^ (2 * k - j))
            (a := c.length) (fun j _ => mul_nonneg (norm_nonneg _) (pow_nonneg hQnn _))
            (Finset.mem_range.mpr (Nat.lt_succ_of_le (OrderedFinpartition.length_le c)))
        have hPnn : 0 ≤ ∏ i : Fin c.length, b (c.partSize i - 1) :=
          Finset.prod_nonneg fun i _ => hb0 _
        calc ‖ftaylorSeries ℝ Φ (substMap X z) c.length‖ *
              ∏ i : Fin c.length, ‖ftaylorSeries ℝ (substMap X) z (c.partSize i)‖
            = ‖iteratedFDeriv ℝ c.length Φ (substMap X z)‖ *
              ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) (substMap X) z‖ := rfl
          _ ≤ ‖iteratedFDeriv ℝ c.length Φ (substMap X z)‖ *
              ((∏ i : Fin c.length, b (c.partSize i - 1)) *
                (Real.sqrt z.2)⁻¹ ^ (2 * k - c.length)) :=
              mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
          _ = (∏ i : Fin c.length, b (c.partSize i - 1)) *
              (‖iteratedFDeriv ℝ c.length Φ (substMap X z)‖ *
                (Real.sqrt z.2)⁻¹ ^ (2 * k - c.length)) := by ring
          _ ≤ (∏ i : Fin c.length, b (c.partSize i - 1)) *
              (∑ j ∈ Finset.range (k + 1),
                ‖iteratedFDeriv ℝ j Φ (substMap X z)‖ * (Real.sqrt z.2)⁻¹ ^ (2 * k - j)) :=
              mul_le_mul_of_nonneg_left hterm hPnn
    _ = (∑ c : OrderedFinpartition k, ∏ i : Fin c.length, b (c.partSize i - 1)) *
          ∑ j ∈ Finset.range (k + 1),
            ‖iteratedFDeriv ℝ j Φ (substMap X z)‖ * (Real.sqrt z.2)⁻¹ ^ (2 * k - j) :=
        (Finset.sum_mul ..).symm

theorem subst_iteratedFDeriv_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (b : ℕ → ℝ) (hb0 : ∀ m, 0 ≤ b m)
    (hb : ∀ (m : ℕ) (z : X × ℝ), 0 < z.2 → z.2 ≤ 1 →
      ‖iteratedFDeriv ℝ m
          (fun y : X × ℝ => fderiv ℝ (fun p : X × ℝ => ((p.1 : X), Real.sqrt p.2)) y) z‖
        ≤ b m / (Real.sqrt z.2) ^ (1 + 2 * m)) :
    ∃ c : ℕ → ℝ, (∀ m, 0 ≤ c m) ∧
      ∀ (k : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (Φ : X × ℝ → F),
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (Set.univ ×ˢ Set.Ioi (0 : ℝ)) →
        ∀ z : X × ℝ, 0 < z.2 → z.2 ≤ 1 →
          ‖iteratedFDeriv ℝ k (fun y : X × ℝ => Φ (y.1, Real.sqrt y.2)) z‖ ≤
            c k * ∑ j ∈ Finset.range (k + 1),
              ‖iteratedFDeriv ℝ j Φ (z.1, Real.sqrt z.2)‖ / (Real.sqrt z.2) ^ (2 * k - j) := by
  refine ⟨fun k => ∑ c : OrderedFinpartition k, ∏ i : Fin c.length, b (c.partSize i - 1),
    fun k => Finset.sum_nonneg fun c _ => Finset.prod_nonneg fun i _ => hb0 _, ?_⟩
  intro k F _ _ Φ hΦ z hz0 hz1
  have hso : IsOpen (substSet X) := isOpen_substSet X
  have hσz : substMap X z ∈ substSet X := by
    simp only [substSet, substMap, Set.mem_prod, Set.mem_univ, Set.mem_Ioi, true_and]
    exact Real.sqrt_pos.2 hz0
  have hΦc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ (substMap X z) :=
    hΦ.contDiffAt (hso.mem_nhds hσz)
  have hmain := subst_taylor_bound b hb0 hb k z hz0 hz1 Φ hΦc
  have hsum : (∑ j ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ j Φ (substMap X z)‖ * (Real.sqrt z.2)⁻¹ ^ (2 * k - j)) =
      ∑ j ∈ Finset.range (k + 1),
        ‖iteratedFDeriv ℝ j Φ (z.1, Real.sqrt z.2)‖ / (Real.sqrt z.2) ^ (2 * k - j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [div_eq_mul_inv, ← inv_pow]
  rw [hsum] at hmain
  exact hmain

end

end Work.Drive
