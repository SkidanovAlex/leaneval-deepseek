import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_same_sign
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# The stabiliser of the Weyl vector `ρ` in the Weyl group of `E₈` is trivial

The `E₈` Cartan matrix `A = CartanMatrix.E₈` is invertible over `ℤ`, with integral inverse
`A⁻¹ = E8NormTwo.E8inv`.  Weights are written in the fundamental-weight basis, so a weight is a
function `v : Fin 8 → ℤ` and its coordinates in the simple-root basis are `coords v = A⁻¹ v`.  The
simple reflection at the node `i` acts by `sref i v = fun j => v j - v i * A i j`, and the
Weyl-group action attached to a word `L` is `wact L v = L.foldl (fun w i => sref i w) v`.

The Weyl vector is `ρ = ω₀ + ⋯ + ω₇`, i.e. the constant vector `rhoZ = fun _ => 1`.  This file
proves:

* `E8_weyl_stab_rho_trivial`: if a word `L` of simple reflections fixes `ρ`, then the induced linear
  self-map of `ℤ^8` is the identity.

The proof is the standard "regular vector" argument.  The bilinear form `bil v w = v ⬝ A⁻¹ w` is
invariant under `wact L` (each `sref i` is an isometry).  Fixing `ρ` therefore preserves the height
`e8htZ v = ∑ (coords v)ᵢ = ⟪ρ, v⟫`.  For every node `i` the image `b = wact L (αᵢ)` is a vector of
squared length `2` and height `1`; by `E8_coords_same_sign` its `α`-coordinates all have the same
sign, and since their sum is `1` they form a standard basis vector.  Hence `wact L` permutes the
simple roots: `wact L (αᵢ) = α_{σ i}` with `σ` injective.  Writing `ρ = ∑ᵢ cᵢ αᵢ` (`c = coords ρ`)
and applying `wact L` gives `ρ = ∑ᵢ cᵢ α_{σ i}`, i.e. `c_{σ j} = c_j` for all `j`.  The eight
entries of `c` are all distinct (`![46, 68, 91, 135, 110, 84, 57, 29]`), so `σ = id`, and since the
simple roots span, `wact L` is the identity.
-/

abbrev E8m : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈
abbrev E8i : Matrix (Fin 8) (Fin 8) ℤ := E8NormTwo.E8inv

/-- The coordinates of `v` in the simple-root basis, i.e. `A⁻¹ v`. -/
def coords (v : Fin 8 → ℤ) : Fin 8 → ℤ := E8i.mulVec v

/-- The Weyl vector `ρ = ω₀ + ⋯ + ω₇`. -/
def rhoZ : Fin 8 → ℤ := fun _ => 1

/-- The simple reflection `sᵢ v = v - vᵢ αᵢ` at the node `i`. -/
def sref (i : Fin 8) (v : Fin 8 → ℤ) : Fin 8 → ℤ := fun j => v j - v i * E8m i j

/-- The Weyl-group action attached to a word `L` of simple reflections. -/
def wact (L : List (Fin 8)) (v : Fin 8 → ℤ) : Fin 8 → ℤ :=
  L.foldl (fun w (i : Fin 8) => sref i w) v

/-- The `W`-invariant bilinear form `⟪v, w⟫ = v ⬝ A⁻¹ w`. -/
def bil (v w : Fin 8 → ℤ) : ℤ := v ⬝ᵥ coords w

/-- The height `⟪ρ, v⟫ = ∑ᵢ (coords v)ᵢ`. -/
def e8htZ (v : Fin 8 → ℤ) : ℤ := ∑ i, coords v i

/-- The `i`-th simple root `αᵢ`, in the fundamental-weight basis. -/
def alpha (i : Fin 8) : Fin 8 → ℤ := E8m.mulVec (Pi.single i 1)

/-! ## Elementary structure -/

@[simp] lemma sref_apply (i : Fin 8) (v : Fin 8 → ℤ) (j : Fin 8) :
    sref i v j = v j - v i * E8m i j := rfl

@[simp] lemma wact_nil (v : Fin 8 → ℤ) : wact [] v = v := rfl

lemma wact_cons (i : Fin 8) (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    wact (i :: L) v = wact L (sref i v) := rfl

lemma wact_singleton (i : Fin 8) (v : Fin 8 → ℤ) : wact [i] v = sref i v := rfl

lemma wact_append (L₁ L₂ : List (Fin 8)) (v : Fin 8 → ℤ) :
    wact (L₁ ++ L₂) v = wact L₂ (wact L₁ v) := by
  simp only [wact, List.foldl_append]

lemma E8m_symm (i j : Fin 8) : E8m i j = E8m j i := E8_diag_offdiag_symm.1 i j

lemma E8m_diag (i : Fin 8) : E8m i i = 2 := E8_diag_offdiag_symm.2.1 i

lemma E8i_mul : E8i * E8m = 1 := E8NormTwo.E8inv_mul_E8

lemma mul_E8i : E8m * E8i = 1 := by rw [mul_eq_one_comm]; exact E8i_mul

lemma coords_mulVec (v : Fin 8 → ℤ) : coords (E8m.mulVec v) = v := by
  simp only [coords, Matrix.mulVec_mulVec, E8i_mul, Matrix.one_mulVec]

lemma mulVec_coords (v : Fin 8 → ℤ) : E8m.mulVec (coords v) = v := by
  simp only [coords, Matrix.mulVec_mulVec, mul_E8i, Matrix.one_mulVec]

lemma coords_apply (v : Fin 8 → ℤ) (i : Fin 8) : coords v i = ∑ j, E8i i j * v j := by
  rw [coords, Matrix.mulVec_apply_eq_sum]

lemma e8htZ_def (v : Fin 8 → ℤ) : e8htZ v = ∑ i, coords v i := rfl

lemma alpha_apply (i j : Fin 8) : alpha i j = E8m i j := by
  rw [alpha, Matrix.mulVec_apply_eq_sum]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk])
      (fun h => absurd (Finset.mem_univ i) h)]
  rw [Pi.single_eq_same, mul_one, E8m_symm j i]

lemma coords_alpha (i : Fin 8) : coords (alpha i) = Pi.single i 1 := by
  rw [alpha, coords_mulVec]

lemma E8i_alpha (i : Fin 8) : E8i.mulVec (alpha i) = Pi.single i 1 := coords_alpha i

lemma mulVec_eq_sum (w : Fin 8 → ℤ) : E8m.mulVec w = ∑ i, w i • alpha i := by
  funext j
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, alpha_apply, E8m_symm j i]
  ring

/-! ## Linearity -/

lemma sref_zero (i : Fin 8) : sref i (0 : Fin 8 → ℤ) = 0 := by
  funext j; simp [sref]

lemma sref_add (i : Fin 8) (a b : Fin 8 → ℤ) : sref i (a + b) = sref i a + sref i b := by
  funext j; simp only [sref_apply, Pi.add_apply]; ring

lemma sref_smul (i : Fin 8) (c : ℤ) (a : Fin 8 → ℤ) : sref i (c • a) = c • sref i a := by
  funext j; simp only [sref_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma wact_zero (L : List (Fin 8)) : wact L (0 : Fin 8 → ℤ) = 0 := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [wact_cons, sref_zero]; exact ih

lemma wact_add (L : List (Fin 8)) (a b : Fin 8 → ℤ) :
    wact L (a + b) = wact L a + wact L b := by
  induction L generalizing a b with
  | nil => rfl
  | cons i L ih => rw [wact_cons, wact_cons, wact_cons, sref_add, ih]

lemma wact_smul (L : List (Fin 8)) (c : ℤ) (a : Fin 8 → ℤ) :
    wact L (c • a) = c • wact L a := by
  induction L generalizing a with
  | nil => rfl
  | cons i L ih => rw [wact_cons, wact_cons, sref_smul, ih]

lemma coords_add (a b : Fin 8 → ℤ) : coords (a + b) = coords a + coords b := by
  simp only [coords, Matrix.mulVec_add]

lemma coords_smul (c : ℤ) (a : Fin 8 → ℤ) : coords (c • a) = c • coords a := by
  simp only [coords, Matrix.mulVec_smul]

lemma wact_finset_sum (L : List (Fin 8)) (s : Finset (Fin 8)) (g : Fin 8 → Fin 8 → ℤ) :
    wact L (∑ i ∈ s, g i) = ∑ i ∈ s, wact L (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wact_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wact_add, ih]

noncomputable def wactLM (L : List (Fin 8)) : (Fin 8 → ℤ) →ₗ[ℤ] (Fin 8 → ℤ) where
  toFun := wact L
  map_add' := wact_add L
  map_smul' := wact_smul L

/-- `wact L` commutes with finite linear combinations. -/
lemma wact_sum_smul (L : List (Fin 8)) (c : Fin 8 → ℤ) (x : Fin 8 → Fin 8 → ℤ) :
    wact L (∑ i, c i • x i) = ∑ i, c i • wact L (x i) := by
  change (wactLM L) (∑ i, c i • x i) = ∑ i, c i • (wactLM L) (x i)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_smul (wactLM L) (c i) (x i))

/-- `coords` commutes with finite linear combinations. -/
lemma coords_sum_smul (c : Fin 8 → ℤ) (x : Fin 8 → Fin 8 → ℤ) :
    coords (∑ i, c i • x i) = ∑ i, c i • coords (x i) := by
  simp only [coords, Matrix.mulVec_sum, Matrix.mulVec_smul]

/-! ## The invariant bilinear form -/

lemma sref_eq (i : Fin 8) (v : Fin 8 → ℤ) : sref i v = v - v i • alpha i := by
  funext j
  rw [sref_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, alpha_apply]

lemma sref_invol (i : Fin 8) (v : Fin 8 → ℤ) : sref i (sref i v) = v := by
  funext j
  simp only [sref_apply, E8m_diag]
  ring

lemma coords_sref (i : Fin 8) (v : Fin 8 → ℤ) :
    coords (sref i v) = coords v - v i • Pi.single i 1 := by
  rw [sref_eq]
  simp only [coords, Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [E8i_alpha]

lemma bil_alpha_left (i : Fin 8) (v : Fin 8 → ℤ) : bil (alpha i) v = v i := by
  have h : bil (alpha i) v = E8m.mulVec (coords v) i := by
    simp only [bil, dotProduct, Matrix.mulVec_apply_eq_sum, alpha_apply]
  rw [h, mulVec_coords]

lemma bil_alpha_right (i : Fin 8) (v : Fin 8 → ℤ) : bil v (alpha i) = v i := by
  simp only [bil, coords_alpha, dotProduct, Pi.single_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk])
      (fun h => absurd (Finset.mem_univ i) h)]
  simp

lemma bil_apply (i j : Fin 8) : bil (alpha i) (alpha j) = E8m i j := by
  rw [bil_alpha_left i (alpha j), alpha_apply, E8m_symm j i]

lemma bil_sub_left (a b w : Fin 8 → ℤ) : bil (a - b) w = bil a w - bil b w := by
  simp only [bil, sub_dotProduct]

lemma bil_smul_left (c : ℤ) (a w : Fin 8 → ℤ) : bil (c • a) w = c * bil a w := by
  simp only [bil, smul_dotProduct, smul_eq_mul]

lemma bil_sub_right (a b w : Fin 8 → ℤ) : bil a (b - w) = bil a b - bil a w := by
  simp only [bil, coords, Matrix.mulVec_sub, dotProduct_sub]

lemma bil_smul_right (c : ℤ) (a w : Fin 8 → ℤ) : bil a (c • w) = c * bil a w := by
  simp only [bil, coords, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma bil_sref_left (i : Fin 8) (x w : Fin 8 → ℤ) :
    bil (sref i x) w = bil x (sref i w) := by
  have e1 : bil (sref i x) w = bil x w - x i * w i := by
    rw [sref_eq i x, bil_sub_left, bil_smul_left, bil_alpha_left]
  have e2 : bil x (sref i w) = bil x w - x i * w i := by
    rw [sref_eq i w, bil_sub_right, bil_smul_right, bil_alpha_right]
    ring
  rw [e1, e2]

lemma bil_sref (i : Fin 8) (x y : Fin 8 → ℤ) :
    bil (sref i x) (sref i y) = bil x y := by
  rw [bil_sref_left, sref_invol]

lemma bil_wact (L : List (Fin 8)) (x y : Fin 8 → ℤ) :
    bil (wact L x) (wact L y) = bil x y := by
  induction L generalizing x y with
  | nil => rfl
  | cons i L ih => rw [wact_cons, wact_cons, ih, bil_sref]

lemma qZ_eq_bil (v : Fin 8 → ℤ) : E8NormTwo.qZ v = bil v v := by
  simp only [E8NormTwo.qZ, bil, coords, dotProduct, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma e8ht_eq_bil (v : Fin 8 → ℤ) : e8htZ v = bil rhoZ v := by
  simp only [e8htZ, bil, rhoZ, dotProduct, one_mul]

lemma wact_reverse (L : List (Fin 8)) (v : Fin 8 → ℤ) : wact L.reverse (wact L v) = v := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
      rw [List.reverse_cons, wact_append, wact_singleton, wact_cons, ih, sref_invol]

/-! ## A finite arithmetic lemma -/

/-- If the entries of `f : Fin 8 → ℤ` are non-negative integers summing to `1`, then `f` is a
standard basis vector. -/
lemma eq_single_of_sum_eq_one (f : Fin 8 → ℤ) (hnn : ∀ i, 0 ≤ f i)
    (hsum : ∑ i, f i = 1) : ∃ k, f = Pi.single k 1 := by
  have hne : ∑ i, f i ≠ 0 := by rw [hsum]; norm_num
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hkpos : 1 ≤ f k := by have := hnn k; omega
  have hother : ∀ i, i ≠ k → f i = 0 := by
    intro i hi
    by_contra hne0
    have hipos : 1 ≤ f i := by have := hnn i; omega
    have hsub : ({k, i} : Finset (Fin 8)) ⊆ Finset.univ := Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnn j)
    rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact fun h => hi h.symm),
        Finset.sum_singleton] at hle
    omega
  have hkval : f k = 1 := by
    have h1 : ∑ i, f i = f k :=
      Finset.sum_eq_single k (fun i _ hi => hother i hi) (fun h => absurd (Finset.mem_univ k) h)
    omega
  refine ⟨k, ?_⟩
  funext j
  by_cases hj : j = k
  · rw [hj, hkval, Pi.single_eq_same]
  · rw [hother j hj, Pi.single_eq_of_ne hj]

/-! ## The main theorem -/

theorem wact_stab_rho_trivial (L : List (Fin 8))
    (h : wact L rhoZ = rhoZ) :
    ∀ v : Fin 8 → ℤ, wact L v = v := by
  classical
  -- Step 1: `wact L` sends every simple root to a simple root.
  have key : ∀ i : Fin 8, ∃ k : Fin 8, wact L (alpha i) = alpha k := by
    intro i
    set b : Fin 8 → ℤ := wact L (alpha i) with hb
    have hqq : E8NormTwo.qZ b = 2 := by
      rw [qZ_eq_bil, hb, bil_wact, bil_apply, E8m_diag]
    have hbne : b ≠ 0 := by
      intro h0
      rw [h0] at hqq
      simp [E8NormTwo.qZ] at hqq
    have hth : e8htZ b = 1 := by
      rw [e8ht_eq_bil]
      calc bil rhoZ b = bil (wact L rhoZ) (wact L (alpha i)) := by rw [h, hb]
        _ = bil rhoZ (alpha i) := bil_wact L rhoZ (alpha i)
        _ = 1 := by simp [bil_alpha_right, rhoZ]
    have hsign := E8_coords_same_sign b hbne hqq
    have hnn : ∀ j, 0 ≤ coords b j := by
      rcases hsign with hpos | hneg
      · intro j; rw [coords_apply]; exact hpos j
      · exfalso
        have h1 : ∑ j, coords b j = 1 := by rw [← e8htZ_def]; exact hth
        have h2 : ∑ j, coords b j ≤ 0 :=
          Finset.sum_nonpos (fun j _ => by rw [coords_apply]; exact hneg j)
        omega
    have hsum : ∑ j, coords b j = 1 := by rw [← e8htZ_def]; exact hth
    obtain ⟨k, hk⟩ := eq_single_of_sum_eq_one (coords b) hnn hsum
    refine ⟨k, ?_⟩
    rw [← mulVec_coords b, hk]
    rfl
  choose σ hσ using key
  -- Step 2: `σ` is injective.
  have hσinj : Function.Injective σ := by
    intro i j hij
    have h1 : wact L (alpha i) = wact L (alpha j) := by rw [hσ i, hσ j, hij]
    have h2 : alpha i = alpha j := by
      have h2' := congrArg (wact L.reverse) h1
      rw [wact_reverse, wact_reverse] at h2'
      exact h2'
    have h3 : (Pi.single i (1 : ℤ) : Fin 8 → ℤ) = Pi.single j 1 := by
      rw [← coords_alpha i, ← coords_alpha j, h2]
    have h4 := congrFun h3 i
    rw [Pi.single_eq_same] at h4
    by_cases hij' : i = j
    · exact hij'
    · rw [Pi.single_eq_of_ne hij'] at h4
      exact absurd h4 (by norm_num)
  -- Step 3: the entries of `coords ρ` are all distinct.
  have hcoords_rhoZ : coords rhoZ = ![46, 68, 91, 135, 110, 84, 57, 29] := by
    funext i
    fin_cases i <;>
      (rw [coords, Matrix.mulVec_apply_eq_sum]
       simp only [rhoZ, E8i, E8NormTwo.E8inv, Fin.sum_univ_eight]
       norm_num
       try decide)
  have hInj : Function.Injective (coords rhoZ) := by
    rw [hcoords_rhoZ]
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  -- Step 4: `ρ = ∑ᵢ cᵢ αᵢ` with `c = coords ρ`, so applying `wact L` gives `c_{σ j} = c_j`.
  have hrho : rhoZ = ∑ i, coords rhoZ i • alpha i := by
    conv_lhs => rw [← mulVec_coords rhoZ]
    rw [mulVec_eq_sum]
  have h1 : rhoZ = ∑ i, coords rhoZ i • alpha (σ i) := by
    calc rhoZ = wact L rhoZ := h.symm
      _ = wact L (∑ i, coords rhoZ i • alpha i) := congrArg (wact L) hrho
      _ = ∑ i, coords rhoZ i • wact L (alpha i) := wact_sum_smul L (coords rhoZ) (fun i => alpha i)
      _ = ∑ i, coords rhoZ i • alpha (σ i) :=
            Finset.sum_congr rfl (fun i _ => by rw [hσ i])
  have h2 : coords rhoZ = ∑ i, coords rhoZ i • Pi.single (σ i) 1 := by
    calc coords rhoZ = coords (∑ i, coords rhoZ i • alpha (σ i)) := congrArg coords h1
      _ = ∑ i, coords rhoZ i • coords (alpha (σ i)) :=
            coords_sum_smul (coords rhoZ) (fun i => alpha (σ i))
      _ = ∑ i, coords rhoZ i • Pi.single (σ i) 1 :=
            Finset.sum_congr rfl (fun i _ => by rw [coords_alpha])
  have hFreq : ∀ j, coords rhoZ (σ j) = coords rhoZ j := by
    intro j
    have hj := congrFun h2 (σ j)
    rw [Finset.sum_apply] at hj
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at hj
    have hsumj : ∑ i, coords rhoZ i * (if σ j = σ i then (1 : ℤ) else 0) = coords rhoZ j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        have hne : σ j ≠ σ i := fun hh => hij (hσinj hh.symm)
        rw [if_neg hne, mul_zero]
      · intro hh; exact absurd (Finset.mem_univ j) hh
    rw [hsumj] at hj
    exact hj
  have hσid : ∀ j, σ j = j := fun j => hInj (hFreq j)
  -- Step 5: conclude.
  have hσ' : ∀ i, wact L (alpha i) = alpha i := by
    intro i; rw [hσ i, hσid i]
  intro v
  have hstep : (∑ i, coords v i • wact L (alpha i)) = ∑ i, coords v i • alpha i :=
    Finset.sum_congr rfl (fun i _ => by rw [hσ' i])
  rw [← mulVec_coords v, mulVec_eq_sum, wact_sum_smul, hstep, ← mulVec_eq_sum, mulVec_coords]

/-- **The stabiliser of the Weyl vector `ρ = ω₀ + ⋯ + ω₇` of `E₈` is trivial.**

If a word `L` of simple reflections, acting on weights written in the fundamental-weight basis by
`(sᵢ v)ⱼ = vⱼ - vᵢ A_{ij}`, fixes `ρ = (1, …, 1)`, then the induced linear map on `ℤ⁸` is the
identity.  (Equivalently, the Weyl group acts freely on the interior of the fundamental chamber.) -/
theorem E8_weyl_stab_rho_trivial (L : List (Fin 8))
    (h : L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) (fun _ => (1 : ℤ))
      = fun _ => 1) :
    ∀ v : Fin 8 → ℤ,
      L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) v = v := by
  have hw : wact L rhoZ = rhoZ := h
  intro v
  exact wact_stab_rho_trivial L hw v

end Commons.LinearAlgebra.Matrix.Cartan
