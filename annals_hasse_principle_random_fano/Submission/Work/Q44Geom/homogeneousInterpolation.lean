import Mathlib

/-!
# Homogeneous interpolation at pairwise non-proportional points of `ℚ³`

Given `N` points `x 0, …, x (N-1)` of `ℚ³` which are nonzero and no two of which are
proportional, and given numbers `c i`, we construct a homogeneous polynomial `h` of degree `n`
in `3` variables with `h (x i) = c i`, provided `N - 1 ≤ n`.

The construction is the classical Lagrange-type one.  For every ordered pair `i ≠ j` the two
points `x i`, `x j` are linearly independent, so there is a linear form `ℓ i j` vanishing at
`x j` but not at `x i` (`Work.Q44Geom.interpExists_orthogonal_ne`).  Then

`g i = (∏_{j ≠ i} ℓ i j) * (m i) ^ (n - (N - 1))`

is homogeneous of degree `n` (the product has `N - 1` factors and the extra factor makes up the
degree), vanishes at every `x m` with `m ≠ i`, and is nonzero at `x i`.  Hence the matrix
`(g i (x j))` is diagonal with nonzero diagonal entries, and

`h = ∑ i (c i / g i (x i)) * g i`

interpolates.
-/

namespace Work.Q44Geom

open MvPolynomial

/-- The standard bilinear pairing `ℚ³ × ℚ³ → ℚ`. -/
def interpDot (a b : Fin 3 → ℚ) : ℚ := ∑ k, a k * b k

/-- The linear form `∑ₖ aₖXₖ` on `ℚ³`. -/
noncomputable def interpLinForm (a : Fin 3 → ℚ) : MvPolynomial (Fin 3) ℚ := ∑ k, C (a k) * X k

lemma interpLinForm_isHomogeneous (a : Fin 3 → ℚ) : (interpLinForm a).IsHomogeneous 1 := by
  rw [interpLinForm]
  refine IsHomogeneous.sum Finset.univ (fun k => C (a k) * X k) 1 ?_
  intro k _
  exact (isHomogeneous_C (Fin 3) (a k)).mul (isHomogeneous_X ℚ k)

lemma interpEval_linForm (x a : Fin 3 → ℚ) :
    MvPolynomial.eval x (interpLinForm a) = interpDot a x := by
  rw [interpLinForm, interpDot]
  simp [map_sum]

lemma interpProd_isHomogeneous {ι : Type*} (s : Finset ι) (f : ι → (Fin 3 → ℚ)) :
    (∏ j ∈ s, interpLinForm (f j)).IsHomogeneous s.card := by
  have h := IsHomogeneous.prod s (fun j => interpLinForm (f j)) (fun _ => 1)
    (fun j _ => interpLinForm_isHomogeneous (f j))
  convert h using 2
  simp [Finset.sum_const]

lemma interpEval_prod {ι : Type*} (x : Fin 3 → ℚ) (s : Finset ι) (f : ι → (Fin 3 → ℚ)) :
    MvPolynomial.eval x (∏ j ∈ s, interpLinForm (f j)) = ∏ j ∈ s, interpDot (f j) x := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [interpEval_linForm]

/-- A nonzero vector is not annihilated by every linear form. -/
lemma interpExists_ne_zero_dot {v : Fin 3 → ℚ} (hv : v ≠ 0) :
    ∃ a : Fin 3 → ℚ, interpDot a v ≠ 0 := by
  have hk : ∃ k, v k ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  obtain ⟨k, hk⟩ := hk
  refine ⟨Pi.single k 1, ?_⟩
  rw [interpDot, Finset.sum_eq_single k
      (fun b _ hbk => by rw [Pi.single_eq_of_ne hbk, zero_mul])
      (fun hk' => absurd (Finset.mem_univ k) hk')]
  rw [Pi.single_eq_same, one_mul]
  exact hk

/-! ### The separating linear form -/

lemma interpDot_linmap_add (v a b : Fin 3 → ℚ) :
    interpDot (a + b) v = interpDot a v + interpDot b v := by
  simp only [interpDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma interpDot_linmap_smul (v : Fin 3 → ℚ) (c : ℚ) (a : Fin 3 → ℚ) :
    interpDot (c • a) v = c • interpDot a v := by
  simp only [interpDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- The pairing with a fixed vector, as a linear form. -/
def interpDotLin (w : Fin 3 → ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] ℚ :=
  { toFun := fun a => interpDot a w
    map_add' := fun a b => interpDot_linmap_add w a b
    map_smul' := fun c a => interpDot_linmap_smul w c a }

@[simp] lemma interpDotLin_apply (w a : Fin 3 → ℚ) : interpDotLin w a = interpDot a w := rfl

lemma interpDot_single (k : Fin 3) (w : Fin 3 → ℚ) : interpDot (Pi.single k 1) w = w k := by
  rw [interpDot, Finset.sum_eq_single k
      (fun b _ hbk => by rw [Pi.single_eq_of_ne hbk, zero_mul])
      (fun hk' => absurd (Finset.mem_univ k) hk')]
  rw [Pi.single_eq_same, one_mul]

/-- If `u ≠ 0` and `v` is not a multiple of `u`, then some linear form kills `v` but not `u`.
Equivalently, the functional `· ⬝ u` is not a multiple of the functional `· ⬝ v` unless `u`
and `v` are proportional: nested kernels of linear forms force one form to be a multiple of the
other (`mem_span_of_iInf_ker_le_ker`). -/
theorem interpExists_orthogonal_ne {u v : Fin 3 → ℚ} (hu : u ≠ 0)
    (hdep : ∀ c : ℚ, v ≠ c • u) :
    ∃ a : Fin 3 → ℚ, interpDot a v = 0 ∧ interpDot a u ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hker : LinearMap.ker (interpDotLin v) ≤ LinearMap.ker (interpDotLin u) := by
    intro a ha
    simp only [LinearMap.mem_ker, interpDotLin_apply] at ha ⊢
    exact h a ha
  have hmem : interpDotLin u ∈ Submodule.span ℚ (Set.range (fun _ : Unit => interpDotLin v)) := by
    refine mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => interpDotLin v)
      (K := interpDotLin u) ?_
    simpa using hker
  rw [Set.range_const, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hu_eq : u = c • v := by
    funext k
    have h1 := LinearMap.congr_fun hc (Pi.single k 1)
    rw [LinearMap.smul_apply] at h1
    simp only [interpDotLin_apply, interpDot_single, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    exact h1.symm
  rcases eq_or_ne c 0 with hc0 | hc0
  · rw [hc0, zero_smul] at hu_eq
    exact hu hu_eq
  · have hv : v = c⁻¹ • u := by
      rw [hu_eq, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    exact hdep c⁻¹ hv

/-! ### The main interpolation theorem -/

open MvPolynomial in
theorem homogeneousInterpolation {N n : ℕ} (x : Fin N → (Fin 3 → ℚ))
    (hxne : ∀ i, x i ≠ 0) (hxind : ∀ i j, i ≠ j → ∀ c : ℚ, x j ≠ c • x i)
    (hn : N - 1 ≤ n) (c : Fin N → ℚ) :
    ∃ h : MvPolynomial (Fin 3) ℚ, h.IsHomogeneous n ∧ ∀ i, MvPolynomial.eval (x i) h = c i := by
  obtain ⟨k, hk⟩ : ∃ k, N - 1 + k = n := ⟨n - (N - 1), Nat.add_sub_cancel' hn⟩
  -- for every pair `i ≠ j`, a linear form vanishing at `x j` but not at `x i`
  have hℓ : ∀ i j, i ≠ j → ∃ a : Fin 3 → ℚ, interpDot a (x j) = 0 ∧ interpDot a (x i) ≠ 0 :=
    fun i j hij => interpExists_orthogonal_ne (hxne i) (hxind i j hij)
  have hP : ∀ i j, ∃ a : Fin 3 → ℚ,
      (i ≠ j → interpDot a (x j) = 0) ∧ (i ≠ j → interpDot a (x i) ≠ 0) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => absurd hij h, fun h => absurd hij h⟩
    · obtain ⟨a, ha1, ha2⟩ := hℓ i j hij
      exact ⟨a, fun _ => ha1, fun _ => ha2⟩
  let ℓ : Fin N → Fin N → (Fin 3 → ℚ) := fun i j => Classical.choose (hP i j)
  have hℓ0 : ∀ i j (hij : i ≠ j), interpDot (ℓ i j) (x j) = 0 :=
    fun i j hij => (Classical.choose_spec (hP i j)).1 hij
  have hℓn : ∀ i j (hij : i ≠ j), interpDot (ℓ i j) (x i) ≠ 0 :=
    fun i j hij => (Classical.choose_spec (hP i j)).2 hij
  -- a linear form not vanishing at each `x i`
  have hM : ∀ i, ∃ a : Fin 3 → ℚ, interpDot a (x i) ≠ 0 :=
    fun i => interpExists_ne_zero_dot (hxne i)
  let M : Fin N → (Fin 3 → ℚ) := fun i => Classical.choose (hM i)
  have hMn : ∀ i, interpDot (M i) (x i) ≠ 0 := fun i => Classical.choose_spec (hM i)
  -- the Lagrange-type functions
  let g : Fin N → MvPolynomial (Fin 3) ℚ := fun i =>
    (∏ j ∈ Finset.univ.erase i, interpLinForm (ℓ i j)) * (interpLinForm (M i)) ^ k
  have hg : ∀ i, (g i).IsHomogeneous n := by
    intro i
    have h1 : (∏ j ∈ Finset.univ.erase i, interpLinForm (ℓ i j)).IsHomogeneous
        (Finset.univ.erase i).card :=
      interpProd_isHomogeneous (Finset.univ.erase i) (fun j => ℓ i j)
    have h2 : ((interpLinForm (M i)) ^ k).IsHomogeneous k := by
      simpa using (interpLinForm_isHomogeneous (M i)).pow k
    have hmul := h1.mul h2
    show ((∏ j ∈ Finset.univ.erase i, interpLinForm (ℓ i j)) *
      (interpLinForm (M i)) ^ k).IsHomogeneous n
    convert hmul using 1
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    exact hk.symm
  have hgself : ∀ i, MvPolynomial.eval (x i) (g i) ≠ 0 := by
    intro i
    have hev : MvPolynomial.eval (x i) (g i) =
        (∏ j ∈ Finset.univ.erase i, interpDot (ℓ i j) (x i)) *
          (interpDot (M i) (x i)) ^ k := by
      show MvPolynomial.eval (x i)
        ((∏ j ∈ Finset.univ.erase i, interpLinForm (ℓ i j)) *
          (interpLinForm (M i)) ^ k) = _
      rw [map_mul, map_pow, interpEval_prod, interpEval_linForm]
    rw [hev]
    refine mul_ne_zero ?_ (pow_ne_zero k (hMn i))
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact hℓn i j (Finset.mem_erase.mp hj).1.symm
  have hgother : ∀ i m, m ≠ i → MvPolynomial.eval (x m) (g i) = 0 := by
    intro i m hmi
    have hev : MvPolynomial.eval (x m) (g i) =
        (∏ j ∈ Finset.univ.erase i, interpDot (ℓ i j) (x m)) *
          (interpDot (M i) (x m)) ^ k := by
      show MvPolynomial.eval (x m)
        ((∏ j ∈ Finset.univ.erase i, interpLinForm (ℓ i j)) *
          (interpLinForm (M i)) ^ k) = _
      rw [map_mul, map_pow, interpEval_prod, interpEval_linForm]
    rw [hev]
    have hz : (∏ j ∈ Finset.univ.erase i, interpDot (ℓ i j) (x m)) = 0 := by
      apply Finset.prod_eq_zero (i := m)
      · exact Finset.mem_erase.mpr ⟨hmi, Finset.mem_univ m⟩
      · exact hℓ0 i m (Ne.symm hmi)
    rw [hz, zero_mul]
  refine ⟨∑ i, C (c i / MvPolynomial.eval (x i) (g i)) * g i, ?_, ?_⟩
  · refine IsHomogeneous.sum Finset.univ
      (fun i => C (c i / MvPolynomial.eval (x i) (g i)) * g i) n ?_
    intro i _
    exact (hg i).C_mul _
  · intro m
    rw [map_sum]
    simp only [map_mul, eval_C]
    rw [Finset.sum_eq_single m]
    · rw [div_mul_cancel₀ _ (hgself m)]
    · intro b _ hbm
      rw [hgother b m (Ne.symm hbm), mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm

end Work.Q44Geom
