import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.minkowski_basis
import Submission.Work.BW.exists_det_submatrix_ne_zero
import Submission.Work.BW.cramer_dominated

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Block C1: a Minkowski-reduced primitive basis from maximal minors

`Work.BW.prim_basis_from_minors`. Let `L` be the saturated rank-`ρ` lattice in `ℤ^r` spanned by the
rows of `M`, and let `J` maximise `|Δ_J| ∏_{i∈J} aᵢ` over the `ρ`-element sets of columns. The
proof projects `L` to the coordinates in `J` (an isomorphism onto a sublattice of `ℤ^ρ` of
covolume `|Δ_J|`), applies `Work.BW.minkowski_basis` to that projection with the weights
`a|_{J}`, and lifts the resulting basis `U` back to `M' = Uᵀ M`. Cramer's rule on the `J`-columns of
`M` shows that every lattice vector `x` satisfies `aᵢ|xᵢ| ≤ ∑_{j∈J} aⱼ|xⱼ|` for `i ∉ J`
(this is `Work.BW.cramer_dominated`, whose bound on the Cramer coefficients is exactly the
maximality of `J` through `Work.BW.det_cols_eq_sign_minorJ`), whence
`∑ᵢ aᵢ|xᵢ| ≤ r ∑_{j∈J} aⱼ|xⱼ|` and the two bounds multiply to the stated constant.

Nonvanishing of `Δ_J` is not a hypothesis: `Work.BW.exists_det_submatrix_ne_zero` supplies a
nonzero minor, and maximality then forces `Δ_J ≠ 0`.
-/

open Matrix

namespace Work.BW

/-- Block C1. For a saturated rank-`ρ` lattice with basis rows `M` and weights `a > 0`, let `J`
maximise `|Δ_J| ∏_{i∈J} aᵢ`. Then the lattice has a basis `M'` with
`∏_j ∑ᵢ aᵢ|M'_{ji}| ≤ 2^{1-ρ} (ρ!)² r^ρ |Δ_J| ∏_{i∈J} aᵢ`. Route: Cramer gives
`aᵢ|xᵢ| ≤ ∑_{j∈J} aⱼ|xⱼ|` on the lattice span, so `∑ aᵢ|xᵢ| ≤ r ∑_{j∈J} aⱼ|xⱼ|`; apply
`minkowski_basis` to the projection on the `J` coordinates (covolume `|Δ_J|`) and lift. -/
theorem prim_basis_from_minors {r ρ : ℕ} (hρ : 1 ≤ ρ) (hρr : ρ ≤ r) (M : Fin ρ → Fin r → ℤ)
    (hM : PrimSys M) (a : Fin r → ℝ) (ha : ∀ i, 0 < a i) (J : Finset (Fin r)) (hJ : J.card = ρ)
    (hmax : ∀ (J' : Finset (Fin r)) (hJ' : J'.card = ρ),
      |(minorJ M J' hJ' : ℝ)| * ∏ i ∈ J', a i ≤ |(minorJ M J hJ : ℝ)| * ∏ i ∈ J, a i) :
    ∃ M' : Fin ρ → Fin r → ℤ, PrimSys M' ∧
      Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
      ∏ j, ∑ i, a i * |(M' j i : ℝ)| ≤
        (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ *
          |(minorJ M J hJ : ℝ)| * ∏ i ∈ J, a i := by
  -- Step 1: the maximising minor does not vanish
  have hΔ : minorJ M J hJ ≠ 0 := by
    obtain ⟨J', hJ', hdet⟩ := exists_det_submatrix_ne_zero (K := ℚ)
      (A := fun j i => (M j i : ℚ)) hM.1
    have hbridge : ∀ (f : Fin ρ → Fin r),
        ((Matrix.det (fun a b : Fin ρ => M a (f b)) : ℤ) : ℚ)
          = (Matrix.submatrix (fun j i => (M j i : ℚ)) id f).det := by
      intro f
      have h' : ((Matrix.det (fun a b : Fin ρ => M a (f b)) : ℤ) : ℚ)
          = (Matrix.map (fun a b : Fin ρ => M a (f b)) (fun z : ℤ => (z : ℚ))).det :=
        Int.cast_det (fun a b : Fin ρ => M a (f b))
      have hmat : Matrix.map (fun a b : Fin ρ => M a (f b)) (fun z : ℤ => (z : ℚ))
          = Matrix.submatrix (fun j i => (M j i : ℚ)) id f := rfl
      rw [h', hmat]
    have hdet1 : ((minorJ M J' hJ' : ℤ) : ℚ) ≠ 0 := by
      show ((Matrix.det (fun a b : Fin ρ => M a (J'.orderEmbOfFin hJ' b)) : ℤ) : ℚ) ≠ 0
      rw [hbridge (J'.orderEmbOfFin hJ')]
      exact hdet
    have hmin_ne : minorJ M J' hJ' ≠ 0 := fun h0 => hdet1 (by simp [h0])
    have hpos : 0 < |(minorJ M J' hJ' : ℝ)| * ∏ i ∈ J', a i := by
      refine mul_pos ?_ (Finset.prod_pos (fun i _ => ha i))
      rw [abs_pos]
      exact_mod_cast hmin_ne
    have hpos2 : 0 < |(minorJ M J hJ : ℝ)| * ∏ i ∈ J, a i := lt_of_lt_of_le hpos (hmax J' hJ')
    have h3 : (0 : ℝ) < ∏ i ∈ J, a i := Finset.prod_pos (fun i _ => ha i)
    have hpos3 : 0 < |(minorJ M J hJ : ℝ)| := by nlinarith [hpos2, h3]
    exact fun h0 => by simp [h0] at hpos3
  -- Step 2: Minkowski on the projection to the coordinates of J
  let N : Matrix (Fin ρ) (Fin ρ) ℤ := (fun a b : Fin ρ => M a (J.orderEmbOfFin hJ b))ᵀ
  have hNd : N.det = minorJ M J hJ :=
    Matrix.det_transpose (fun a b : Fin ρ => M a (J.orderEmbOfFin hJ b))
  have hNne : N.det ≠ 0 := by rw [hNd]; exact hΔ
  let c : Fin ρ → ℝ := fun i => a (J.orderEmbOfFin hJ i)
  have hcpos : ∀ i, 0 < c i := fun i => ha _
  have hρpos : 0 < ρ := lt_of_lt_of_le Nat.zero_lt_one hρ
  obtain ⟨U, hUunit, hmink⟩ := minkowski_basis hρpos N hNne c hcpos
  have hcprod : ∏ i, c i = ∏ i ∈ J, a i := by
    have h := Finset.prod_image (s := Finset.univ)
      (g := (J.orderEmbOfFin hJ : Fin ρ → Fin r)) (f := fun i => a i)
      (by intro x _ y _ hxy; exact (J.orderEmbOfFin hJ).injective hxy)
    rw [Finset.image_orderEmbOfFin_univ J hJ] at h
    simp only [c]
    exact h.symm
  -- Step 3: the lifted basis
  let M' : Fin ρ → Fin r → ℤ := fun j i => ∑ k, U k j * M k i
  have hAU : ∀ (i j : Fin ρ), (N * U) i j = M' j (J.orderEmbOfFin hJ i) := by
    intro i j
    simp only [N, M', Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  -- Step 4: pointwise domination, then the product bound
  have hMi : ∀ (j : Fin ρ) (i : Fin r),
      (M' j i : ℝ) = ∑ k, (U k j : ℝ) * (M k i : ℝ) := by
    intro j i
    simp only [M']
    push_cast
    rfl
  have hpt : ∀ j : Fin ρ, ∑ i, a i * |(M' j i : ℝ)| ≤
      (r : ℝ) * (∑ i, c i * |(((N * U) i j : ℤ) : ℝ)|) := by
    intro j
    have h1 : ∀ i : Fin r, a i * |(M' j i : ℝ)| ≤ ∑ i' ∈ J, a i' * |(M' j i' : ℝ)| := by
      intro i
      have hcd := cramer_dominated M a ha J hJ hmax hΔ (fun k => (U k j : ℝ)) i
      simp only [hMi] at hcd ⊢
      exact hcd
    calc ∑ i, a i * |(M' j i : ℝ)| ≤ ∑ i, ∑ i' ∈ J, a i' * |(M' j i' : ℝ)| :=
          Finset.sum_le_sum (fun i _ => h1 i)
      _ = (r : ℝ) * ∑ i' ∈ J, a i' * |(M' j i' : ℝ)| := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (r : ℝ) * ∑ i, c i * |(((N * U) i j : ℤ) : ℝ)| := by
          congr 1
          have h := Finset.sum_image (s := Finset.univ)
            (g := (J.orderEmbOfFin hJ : Fin ρ → Fin r))
            (f := fun i' => a i' * |(M' j i' : ℝ)|)
            (by intro x _ y _ hxy; exact (J.orderEmbOfFin hJ).injective hxy)
          rw [Finset.image_orderEmbOfFin_univ J hJ] at h
          rw [h]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          simp only [c, hAU x j]
  have hfin : ∏ j, ∑ i, a i * |(M' j i : ℝ)| ≤
      (r : ℝ) ^ ρ * ∏ j, (∑ i, c i * |(((N * U) i j : ℤ) : ℝ)|) := by
    calc ∏ j, ∑ i, a i * |(M' j i : ℝ)|
        ≤ ∏ j, ((r : ℝ) * ∑ i, c i * |(((N * U) i j : ℤ) : ℝ)|) :=
          Finset.prod_le_prod₀
            (fun j _ => Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (ha i)) (abs_nonneg _)))
            (fun j _ => hpt j)
      _ = (r : ℝ) ^ ρ * ∏ j, (∑ i, c i * |(((N * U) i j : ℤ) : ℝ)|) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmink' : ∏ j, (∑ i, c i * |(((N * U) i j : ℤ) : ℝ)|) ≤
      ((ρ.factorial : ℝ) ^ 2 / 2 ^ (ρ - 1)) * |(minorJ M J hJ : ℝ)| * ∏ i ∈ J, a i := by
    rw [← hcprod, ← hNd]
    exact hmink
  have hbound : ∏ j, ∑ i, a i * |(M' j i : ℝ)| ≤
      (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (r : ℝ) ^ ρ *
        |(minorJ M J hJ : ℝ)| * ∏ i ∈ J, a i := by
    refine le_trans hfin (le_trans (mul_le_mul_of_nonneg_left hmink' (by positivity)) ?_)
    have h2 : (2 : ℝ) ^ (1 - (ρ : ℤ)) = ((2 : ℝ) ^ (ρ - 1))⁻¹ := by
      have h1 : (1 : ℤ) - (ρ : ℤ) = -(((ρ - 1 : ℕ)) : ℤ) := by omega
      calc (2 : ℝ) ^ (1 - (ρ : ℤ)) = (2 : ℝ) ^ (-(((ρ - 1 : ℕ)) : ℤ)) := by rw [h1]
        _ = ((2 : ℝ) ^ (((ρ - 1 : ℕ)) : ℤ))⁻¹ := _root_.zpow_neg (2 : ℝ) ((ρ - 1 : ℕ) : ℤ)
        _ = ((2 : ℝ) ^ (ρ - 1))⁻¹ := by rw [zpow_natCast]
    refine le_of_eq ?_
    rw [h2, div_eq_mul_inv]
    ring
  -- Step 5: invertibility of U over ℤ
  obtain ⟨V, hUV, hVU⟩ : ∃ V : Matrix (Fin ρ) (Fin ρ) ℤ, U * V = 1 ∧ V * U = 1 := by
    have hUi : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr hUunit
    obtain ⟨u, hu⟩ : ∃ u : (Matrix (Fin ρ) (Fin ρ) ℤ)ˣ, (u : Matrix (Fin ρ) (Fin ρ) ℤ) = U :=
      ⟨hUi.unit, IsUnit.unit_spec hUi⟩
    exact ⟨↑(u⁻¹), by rw [← hu]; exact Units.mul_inv u, by rw [← hu]; exact Units.inv_mul u⟩
  have hspan : Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨j, rfl⟩
      have hx : (M' j : Fin r → ℤ) = ∑ k, (U k j) • (M k) := by
        ext i
        simp [M', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hx]
      exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
    · rw [Submodule.span_le]
      rintro x ⟨j, rfl⟩
      have hkey : ∀ l : Fin ρ, ∑ k, V k j * U l k = if j = l then 1 else 0 := by
        intro l
        have h1 : (Vᵀ * Uᵀ : Matrix (Fin ρ) (Fin ρ) ℤ) = 1 := by
          rw [← Matrix.transpose_mul, hUV, Matrix.transpose_one]
        have h2 := congr_fun (congr_fun h1 j) l
        simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h2
      have hsumi : ∀ i, ∑ k, V k j * (∑ l, U l k * M l i) = M j i := by
        intro i
        calc ∑ k, V k j * (∑ l, U l k * M l i)
            = ∑ k, ∑ l, V k j * U l k * M l i := by
              refine Finset.sum_congr rfl (fun k _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun l _ => by ring)
          _ = ∑ l, ∑ k, V k j * U l k * M l i := Finset.sum_comm
          _ = ∑ l, (∑ k, V k j * U l k) * M l i := by
              exact Finset.sum_congr rfl (fun l _ => (Finset.sum_mul _ _ _).symm)
          _ = M j i := by
              rw [Finset.sum_eq_single j]
              · simp [hkey j]
              · intro l _ hl; rw [hkey l, if_neg (fun h => hl h.symm), zero_mul]
              · intro hj; exact absurd (Finset.mem_univ j) hj
      have hx : (M j : Fin r → ℤ) = ∑ k, (V k j) • (M' k) := by
        ext i
        simp only [M', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact (hsumi i).symm
      rw [hx]
      exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hliM : ∀ (g' : Fin ρ → ℚ), (∑ k, g' k • (fun i => (M k i : ℚ))) = 0 → ∀ k, g' k = 0 := by
    have h := hM.1
    rwa [Fintype.linearIndependent_iff] at h
  refine ⟨M', ⟨?_, ?_⟩, hspan, hbound⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hg' : ∀ i, ∑ j, g j * (M' j i : ℚ) = 0 := by
      intro i
      have h := congr_fun hg i
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
    have hsum : ∑ k, (∑ j, (U k j : ℚ) * g j) • (fun i => (M k i : ℚ)) = 0 := by
      funext i
      have hstep : ∑ k, (∑ j, (U k j : ℚ) * g j) * ((M k i : ℤ) : ℚ)
          = ∑ j, g j * ((M' j i : ℤ) : ℚ) := by
        simp only [M']
        push_cast
        calc ∑ k, (∑ j, ↑(U k j) * g j) * ↑(M k i)
            = ∑ k, ∑ j, (↑(U k j) * g j) * ↑(M k i) := by
              refine Finset.sum_congr rfl (fun k _ => ?_); rw [Finset.sum_mul]
          _ = ∑ j, ∑ k, (↑(U k j) * g j) * ↑(M k i) := Finset.sum_comm
          _ = ∑ j, g j * ∑ k, ↑(U k j) * ↑(M k i) := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun k _ => by ring)
      calc (∑ k, (∑ j, (U k j : ℚ) * g j) • (fun i => (M k i : ℚ))) i
          = ∑ k, (∑ j, (U k j : ℚ) * g j) * ((M k i : ℤ) : ℚ) := by
            simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        _ = ∑ j, g j * ((M' j i : ℤ) : ℚ) := hstep
        _ = 0 := hg' i
    have hgg' : ∀ k, (∑ j, (U k j : ℚ) * g j) = 0 := fun k => hliM _ hsum k
    have hgid : g j = ∑ k, (V j k : ℚ) * (∑ l, (U k l : ℚ) * g l) := by
      have hkey : ∀ l : Fin ρ, ∑ k, (V j k : ℚ) * (U k l : ℚ) = if j = l then 1 else 0 := by
        intro l
        have h2 := congr_fun (congr_fun hVU j) l
        simp only [Matrix.mul_apply, Matrix.one_apply] at h2
        have h3 := congrArg (fun z : ℤ => (z : ℚ)) h2
        push_cast at h3
        simpa using h3
      rw [eq_comm]
      calc ∑ k, (V j k : ℚ) * (∑ l, (U k l : ℚ) * g l)
          = ∑ k, ∑ l, (V j k : ℚ) * ((U k l : ℚ) * g l) := by
            refine Finset.sum_congr rfl (fun k _ => ?_); rw [Finset.mul_sum]
        _ = ∑ l, ∑ k, (V j k : ℚ) * ((U k l : ℚ) * g l) := Finset.sum_comm
        _ = ∑ l, (∑ k, (V j k : ℚ) * (U k l : ℚ)) * g l := by
            refine Finset.sum_congr rfl (fun l _ => ?_)
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl (fun k _ => by ring)
        _ = g j := by
            rw [Finset.sum_eq_single j]
            · simp [hkey j]
            · intro l _ hl; rw [hkey l, if_neg (fun h => hl h.symm), zero_mul]
            · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hgid]
    exact Finset.sum_eq_zero (fun k _ => by rw [hgg' k, mul_zero])
  · intro x m hm hx
    rw [hspan] at hx ⊢
    exact hM.2 x m hm hx


end Work.BW
