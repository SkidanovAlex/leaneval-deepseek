import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_same_sign

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

namespace E8posRoots

/-!
# The Weyl-group element preserving every positive root fixes the Weyl vector

A weight `v : Fin 8 → ℤ` is written in the `ω`-basis (`v i = ⟨v, αᵢ∨⟩`), so the simple reflection
at node `i` acts by `(sᵢ v) j = v j - v i * A i j` (`sref`).  The `α∨`-coordinates of `v` are
`coords v = A⁻¹ v`, and `E8NormTwo.qZ v = v ⬝ A⁻¹ v` is the squared length.

A product `w` of simple reflections which maps every positive root into the positive cone permutes
the finite set of positive roots (a positive root of squared length `2` maps again to one), hence
fixes their sum.  That sum is `2ρ = 2 • (fun _ => 1)`, so `w` fixes the all-ones vector.
-/

lemma E8_symm (i j : Fin 8) : CartanMatrix.E₈ i j = CartanMatrix.E₈ j i :=
  E8_diag_offdiag_symm.1 i j
lemma E8_diag (i : Fin 8) : CartanMatrix.E₈ i i = 2 := E8_diag_offdiag_symm.2.1 i

lemma E8_offdiag_nonpos (i j : Fin 8) (h : i ≠ j) : CartanMatrix.E₈ i j ≤ 0 := by
  rcases E8_diag_offdiag_symm.2.2 i j h with h0 | h1
  · simp [h0]
  · simp [h1]

/-- The coordinates of `v` in the simple root basis: `coords v = A⁻¹ v`. -/
def coords (v : Fin 8 → ℤ) : Fin 8 → ℤ := E8NormTwo.E8inv.mulVec v

/-- The simple reflection at the node `i` acting on weights. -/
def sref (i : Fin 8) (v : Fin 8 → ℤ) : Fin 8 → ℤ :=
  fun j => v j - v i * CartanMatrix.E₈ i j

/-- The Weyl-group action of a list of simple reflections. -/
def wact (L : List (Fin 8)) (v : Fin 8 → ℤ) : Fin 8 → ℤ := L.foldl (fun w i => sref i w) v

/-- The simple root `αᵢ` in `ω`-coordinates: `αᵢ j = ⟨αᵢ, αⱼ∨⟩ = A i j`. -/
def alpha (i : Fin 8) : Fin 8 → ℤ := fun j => CartanMatrix.E₈ i j

/-- The Weyl vector `ρ` in `ω`-coordinates. -/
def rhoZ : Fin 8 → ℤ := fun _ => 1

lemma qz_eq_sum (v : Fin 8 → ℤ) :
    E8NormTwo.qZ v = ∑ i, ∑ j, v i * E8NormTwo.E8inv i j * v j := rfl

@[simp] lemma coords_apply (v : Fin 8 → ℤ) (i : Fin 8) :
    coords v i = ∑ j, E8NormTwo.E8inv i j * v j := by
  rw [coords, Matrix.mulVec_apply_eq_sum]

lemma coords_add (a b : Fin 8 → ℤ) : coords (a + b) = coords a + coords b := by
  change E8NormTwo.E8inv.mulVec (a + b) = E8NormTwo.E8inv.mulVec a + E8NormTwo.E8inv.mulVec b
  rw [Matrix.mulVec_add]

lemma coords_neg (a : Fin 8 → ℤ) : coords (-a) = -coords a := by
  change E8NormTwo.E8inv.mulVec (-a) = -E8NormTwo.E8inv.mulVec a
  rw [Matrix.mulVec_neg]

lemma E8i_mul : E8NormTwo.E8inv * CartanMatrix.E₈ = 1 := E8NormTwo.E8inv_mul_E8
lemma mul_E8i : CartanMatrix.E₈ * E8NormTwo.E8inv = 1 := by
  rw [mul_eq_one_comm]; exact E8NormTwo.E8inv_mul_E8

lemma mulVec_coords (v : Fin 8 → ℤ) : CartanMatrix.E₈.mulVec (coords v) = v := by
  change CartanMatrix.E₈.mulVec (E8NormTwo.E8inv.mulVec v) = v
  rw [Matrix.mulVec_mulVec, mul_E8i, Matrix.one_mulVec]

lemma mulVec_alpha (i : Fin 8) :
    E8NormTwo.E8inv.mulVec (fun j => CartanMatrix.E₈ i j) = Pi.single i 1 := by
  have hα : (fun j => CartanMatrix.E₈ i j) = CartanMatrix.E₈.mulVec (Pi.single i 1) := by
    rw [Matrix.mulVec_single_one]
    funext j
    simp only [Matrix.col_apply]
    exact E8_symm i j
  rw [hα, Matrix.mulVec_mulVec, E8i_mul, Matrix.one_mulVec]

lemma coords_alpha (i : Fin 8) : coords (alpha i) = Pi.single i 1 := mulVec_alpha i

lemma coords_sref (i : Fin 8) (v : Fin 8 → ℤ) :
    coords (sref i v) = coords v - (v i) • (Pi.single i 1 : Fin 8 → ℤ) := by
  have hv : sref i v = v - (v i) • (fun j => CartanMatrix.E₈ i j) := by
    funext j; simp [sref, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hv, coords, Matrix.mulVec_sub, Matrix.mulVec_smul, mulVec_alpha]
  rfl

lemma qz_eq_dot (v : Fin 8 → ℤ) : E8NormTwo.qZ v = ∑ p, coords v p * v p := by
  simp only [qz_eq_sum, coords_apply]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro q _
  ring

lemma qz_sref (i : Fin 8) (v : Fin 8 → ℤ) : E8NormTwo.qZ (sref i v) = E8NormTwo.qZ v :=
  E8NormTwo.qZ_refl v i

lemma sref_zero (i : Fin 8) : sref i 0 = 0 := by
  funext j; simp [sref]

lemma sref_add (i : Fin 8) (a b : Fin 8 → ℤ) : sref i (a + b) = sref i a + sref i b := by
  funext j; simp only [sref, Pi.add_apply]; ring

lemma sref_smul (i : Fin 8) (c : ℤ) (a : Fin 8 → ℤ) : sref i (c • a) = c • sref i a := by
  funext j; simp only [sref, Pi.smul_apply, smul_eq_mul]; ring

lemma sref_invol (i : Fin 8) : Function.Involutive (sref i) := by
  intro v
  funext j
  simp only [sref, E8_diag]
  ring

lemma sref_alpha (i : Fin 8) : sref i (alpha i) = - alpha i := by
  funext j
  simp only [sref, alpha, Pi.neg_apply, E8_diag]
  ring

lemma sref_sum (i : Fin 8) (T : Finset (Fin 8 → ℤ)) :
    sref i (∑ v ∈ T, v) = ∑ v ∈ T, sref i v := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [sref_zero]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sref_add, ih]

lemma wact_zero (L : List (Fin 8)) : wact L 0 = 0 := by
  induction L with
  | nil => rfl
  | cons i L ih => rw [show wact (i :: L) 0 = wact L (sref i 0) from rfl, sref_zero, ih]

lemma wact_add (L : List (Fin 8)) (a b : Fin 8 → ℤ) :
    wact L (a + b) = wact L a + wact L b := by
  induction L generalizing a b with
  | nil => rfl
  | cons i L ih =>
      rw [show wact (i :: L) (a + b) = wact L (sref i (a + b)) from rfl, sref_add,
        ih (sref i a) (sref i b),
        show wact (i :: L) a = wact L (sref i a) from rfl,
        show wact (i :: L) b = wact L (sref i b) from rfl]

lemma wact_smul (L : List (Fin 8)) (c : ℤ) (a : Fin 8 → ℤ) :
    wact L (c • a) = c • wact L a := by
  induction L generalizing a with
  | nil => rfl
  | cons i L ih =>
      rw [show wact (i :: L) (c • a) = wact L (sref i (c • a)) from rfl, sref_smul, ih (sref i a),
        show wact (i :: L) a = wact L (sref i a) from rfl]

/-- `wact` agrees with the raw `foldl` of the statement. -/
lemma wact_eq_foldl (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    wact L v
      = L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) v := rfl

lemma wact_sum (L : List (Fin 8)) (T : Finset (Fin 8 → ℤ)) :
    wact L (∑ v ∈ T, v) = ∑ v ∈ T, wact L v := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [wact_zero]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wact_add, ih]

lemma wact_append (L₁ L₂ : List (Fin 8)) (v : Fin 8 → ℤ) :
    wact (L₁ ++ L₂) v = wact L₂ (wact L₁ v) := by
  simp only [wact, List.foldl_append]

lemma wact_reverse (L : List (Fin 8)) (v : Fin 8 → ℤ) : wact L.reverse (wact L v) = v := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
      rw [List.reverse_cons, wact_append, show wact (i :: L) v = wact L (sref i v) from rfl]
      show sref i (wact L.reverse (wact L (sref i v))) = v
      rw [ih (sref i v), sref_invol]

lemma wact_injective (L : List (Fin 8)) : Function.Injective (wact L) := by
  intro a b h
  have h1 := congrArg (wact L.reverse) h
  simpa only [wact_reverse] using h1

lemma qz_wact (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    E8NormTwo.qZ (wact L v) = E8NormTwo.qZ v := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
      rw [show wact (i :: L) v = wact L (sref i v) from rfl, ih, qz_sref]

/-! ## Cauchy–Schwarz and the reflection lemma -/

lemma int_sq_bounds (x : ℤ) (h : x ^ 2 ≤ 4) : -2 ≤ x ∧ x ≤ 2 := by
  constructor <;> nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 2)]

lemma qz_eq_zero (v : Fin 8 → ℤ) (h : E8NormTwo.qZ v = 0) : v = 0 := by
  have hx : E8NormTwo.xc v = 0 := by
    by_contra hne
    have hpos : 0 < E8NormTwo.form2 (E8NormTwo.xc v) (E8NormTwo.xc v) := E8_posDef _ hne
    rw [E8NormTwo.form2_xc_self] at hpos
    rw [h] at hpos
    norm_num at hpos
  have h2 : (fun j => (v j : ℚ)) = 0 := by
    have h0 := E8NormTwo.E8q_mul_xc v
    rw [hx, Matrix.mulVec_zero] at h0
    exact h0.symm
  funext j
  have := congr_fun h2 j
  simp only [Pi.zero_apply] at this
  exact_mod_cast this

lemma qz_sub_alpha (i : Fin 8) (a : Fin 8 → ℤ) :
    E8NormTwo.qZ (a - alpha i) = E8NormTwo.qZ a - 2 * a i + 2 := by
  fin_cases i <;>
    (simp [E8NormTwo.qZ, alpha, E8NormTwo.E8inv, CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_eight] <;> ring)

/-- A positive root: a nonzero weight of squared length `2` with nonnegative simple-root
coordinates. -/
def IsPosRoot (v : Fin 8 → ℤ) : Prop :=
  E8NormTwo.qZ v = 2 ∧ v ≠ 0 ∧ ∀ i, 0 ≤ coords v i

lemma alpha_isPosRoot (i : Fin 8) : IsPosRoot (alpha i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [qz_eq_dot]
    have hca : coords (alpha i) = Pi.single i 1 := coords_alpha i
    rw [hca, Finset.sum_eq_single i]
    · simp [alpha, E8_diag]
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro h
    have := congr_fun h i
    simp [alpha, E8_diag] at this
  · intro j
    have hca : coords (alpha i) = Pi.single i 1 := coords_alpha i
    rw [hca]
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]

lemma beta_i_le_one (i : Fin 8) (β : Fin 8 → ℤ) (hβ : IsPosRoot β) (hne : β ≠ alpha i) :
    β i ≤ 1 := by
  have h4 : (β i) ^ 2 ≤ 4 := E8NormTwo.sq_le_four β hβ.1 i
  by_contra hc
  push Not at hc
  have hle2 : β i ≤ 2 := (int_sq_bounds (β i) h4).2
  have h2 : β i = 2 := by omega
  have hzero : E8NormTwo.qZ (β - alpha i) = 0 := by
    rw [qz_sub_alpha i β, hβ.1, h2]
    ring
  have := qz_eq_zero (β - alpha i) hzero
  exact hne (sub_eq_zero.mp this)

lemma beta_i_eq_one_coords (i : Fin 8) (β : Fin 8 → ℤ) (hβ : IsPosRoot β) (hb : β i = 1) :
    1 ≤ coords β i := by
  have hβc : β = CartanMatrix.E₈.mulVec (coords β) := (mulVec_coords β).symm
  have h1 : β i = ∑ k, CartanMatrix.E₈ i k * coords β k := by
    conv_lhs => rw [hβc]
    rw [Matrix.mulVec_apply_eq_sum]
  have hsplit : β i = 2 * coords β i + ∑ k ∈ Finset.univ.erase i, CartanMatrix.E₈ i k * coords β k := by
    rw [h1, ← Finset.add_sum_erase Finset.univ
      (fun k => CartanMatrix.E₈ i k * coords β k) (Finset.mem_univ i), E8_diag]
  have hle : ∑ k ∈ Finset.univ.erase i, CartanMatrix.E₈ i k * coords β k ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    rw [Finset.mem_erase] at hk
    exact mul_nonpos_of_nonpos_of_nonneg (E8_offdiag_nonpos i k (Ne.symm hk.1)) (hβ.2.2 k)
  omega

lemma sref_mem_posRoot (i : Fin 8) (β : Fin 8 → ℤ) (hβ : IsPosRoot β) (hne : β ≠ alpha i) :
    IsPosRoot (sref i β) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [qz_sref]; exact hβ.1
  · intro h0
    have h1 : sref i (sref i β) = sref i 0 := by rw [h0]
    rw [sref_invol, sref_zero] at h1
    exact hβ.2.1 h1
  · intro j
    rw [coords_sref]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases hj : j = i
    · rw [hj, if_pos rfl, mul_one]
      have hle1 : β i ≤ 1 := beta_i_le_one i β hβ hne
      by_cases hb : β i ≤ 0
      · have hge : 0 ≤ coords β i := hβ.2.2 i
        omega
      · push Not at hb
        have hb1 : β i = 1 := by omega
        have hc1 : 1 ≤ coords β i := beta_i_eq_one_coords i β hβ hb1
        omega
    · rw [if_neg hj, mul_zero, sub_zero]
      exact hβ.2.2 j

/-! ## The finite set of positive roots and the sum identity -/

theorem posRoot_finite : (Set.Finite {v : Fin 8 → ℤ | IsPosRoot v}) := by
  refine (Set.Finite.pi (fun _ : Fin 8 => Set.finite_Icc (-2 : ℤ) 2)).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq, IsPosRoot, Set.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  obtain ⟨hq, -, -⟩ := hv
  intro i
  exact int_sq_bounds (v i) (E8NormTwo.sq_le_four v hq i)

noncomputable def P : Finset (Fin 8 → ℤ) := posRoot_finite.toFinset

lemma memP (v : Fin 8 → ℤ) : v ∈ P ↔ IsPosRoot v := by
  simp only [P, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

lemma neg_alpha_not_memP (i : Fin 8) : - alpha i ∉ P := by
  intro h
  have hge : 0 ≤ coords (- alpha i) i := ((memP (- alpha i)).mp h).2.2 i
  have hca : coords (alpha i) = Pi.single i 1 := coords_alpha i
  have hc : coords (- alpha i) i = -1 := by
    rw [coords_neg, hca]; simp
  rw [hc] at hge
  norm_num at hge

lemma sum_P_apply (i : Fin 8) : (∑ v ∈ P, v) i = 2 := by
  have haP : alpha i ∈ P := (memP (alpha i)).mpr (alpha_isPosRoot i)
  set T : Finset (Fin 8 → ℤ) := P.erase (alpha i) with hT
  have hTmem : ∀ v, v ∈ T ↔ v ∈ P ∧ v ≠ alpha i := by
    intro v; rw [hT, Finset.mem_erase]; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hmap : ∀ v ∈ T, sref i v ∈ T := by
    intro v hv
    rw [hTmem] at hv ⊢
    obtain ⟨hvP, hvne⟩ := hv
    refine ⟨(memP (sref i v)).mpr (sref_mem_posRoot i v ((memP v).mp hvP) hvne), ?_⟩
    intro hcon
    have hv_eq : v = sref i (alpha i) := by
      have h1 := congrArg (sref i) hcon
      rwa [sref_invol] at h1
    rw [sref_alpha] at hv_eq
    exact neg_alpha_not_memP i (hv_eq ▸ hvP)
  have hinj : ∀ a1 ∈ T, ∀ a2 ∈ T, sref i a1 = sref i a2 → a1 = a2 :=
    fun a1 _ a2 _ h => (sref_invol i).injective h
  have hsurj : ∀ b ∈ T, ∃ a, ∃ _ : a ∈ T, sref i a = b :=
    fun b hb => ⟨sref i b, hmap b hb, sref_invol i b⟩
  have hbij : (∑ v ∈ T, sref i v) = ∑ v ∈ T, v :=
    Finset.sum_bij (fun v _ => sref i v) hmap hinj hsurj (fun a _ => rfl)
  have hfix : sref i (∑ v ∈ T, v) = ∑ v ∈ T, v := by rw [sref_sum, hbij]
  have hSsplit : (∑ v ∈ P, v) = alpha i + ∑ v ∈ T, v := by
    rw [hT]; exact (Finset.add_sum_erase P (fun v => v) haP).symm
  have hsub : (∑ v ∈ P, v) - alpha i = ∑ v ∈ T, v := by rw [hSsplit]; abel
  have hX : sref i ((∑ v ∈ P, v) - alpha i) = (∑ v ∈ P, v) - alpha i := by
    rw [hsub]; exact hfix
  have heval : ((∑ v ∈ P, v) - alpha i) i = 0 := by
    have h2 := congr_fun hX i
    simp only [sref, E8_diag] at h2
    omega
  have hmain : (∑ v ∈ P, v) i = 2 := by
    have h := heval
    simp only [Pi.sub_apply, alpha, E8_diag] at h
    omega
  exact hmain

lemma sum_P_eq : (∑ v ∈ P, v) = fun _ => (2 : ℤ) := funext sum_P_apply

/-! ## A product preserving every positive root is the identity -/

lemma wact_memP (L : List (Fin 8))
    (h : ∀ v : Fin 8 → ℤ, E8NormTwo.qZ v = 2 → v ≠ 0 → (∀ i, 0 ≤ coords v i) →
        (∀ i, 0 ≤ coords (wact L v) i))
    (v : Fin 8 → ℤ) (hv : v ∈ P) : wact L v ∈ P := by
  obtain ⟨hq, hv0, hc⟩ := (memP v).mp hv
  refine (memP (wact L v)).mpr ⟨?_, ?_, ?_⟩
  · rw [qz_wact]; exact hq
  · intro h0
    exact hv0 (wact_injective L (by rw [h0, wact_zero]))
  · exact h v hq hv0 hc

lemma image_wact_P (L : List (Fin 8))
    (h : ∀ v : Fin 8 → ℤ, E8NormTwo.qZ v = 2 → v ≠ 0 → (∀ i, 0 ≤ coords v i) →
        (∀ i, 0 ≤ coords (wact L v) i)) :
    P.image (wact L) = P := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact wact_memP L h u hu
  · exact le_of_eq (Finset.card_image_of_injective P (wact_injective L)).symm

lemma wact_sum_P (L : List (Fin 8))
    (h : ∀ v : Fin 8 → ℤ, E8NormTwo.qZ v = 2 → v ≠ 0 → (∀ i, 0 ≤ coords v i) →
        (∀ i, 0 ≤ coords (wact L v) i)) :
    (∑ v ∈ P, wact L v) = ∑ v ∈ P, v := by
  have himg := image_wact_P L h
  refine Finset.sum_bij (fun v _ => wact L v) ?_ ?_ ?_ ?_
  · intro v hv; rw [← himg]; exact Finset.mem_image_of_mem (wact L) hv
  · intro a _ b _ hab; exact wact_injective L hab
  · intro b hb
    rw [← himg] at hb
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hb
    exact ⟨a, ha, hae⟩
  · intro v _; rfl

end E8posRoots

open E8posRoots

theorem E8_weyl_posRoots_fixes_rho (L : List (Fin 8))
    (h : ∀ v : Fin 8 → ℤ,
      (∑ i, ∑ j, v i * Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j * v j = 2) → v ≠ 0 →
      (∀ i, 0 ≤ ∑ j, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j * v j) →
      (∀ i, 0 ≤ ∑ j, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j *
        (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) v) j)) :
    L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) (fun _ => (1 : ℤ))
      = fun _ => 1 := by
  have h' : ∀ v : Fin 8 → ℤ, E8NormTwo.qZ v = 2 → v ≠ 0 → (∀ i, 0 ≤ coords v i) →
      (∀ i, 0 ≤ coords (wact L v) i) := by
    intro v hq hv0 hc i
    have hq' : (∑ i, ∑ j, v i * E8NormTwo.E8inv i j * v j) = 2 := by
      rw [← qz_eq_sum]; exact hq
    have hc' : ∀ k, 0 ≤ ∑ j, E8NormTwo.E8inv k j * v j := fun k => by
      rw [← coords_apply]; exact hc k
    have hh := h v hq' hv0 hc' i
    rw [coords_apply, wact_eq_foldl L v]
    exact hh
  have hS : (∑ v ∈ P, v) = fun _ => (2 : ℤ) := sum_P_eq
  have hWS : wact L (∑ v ∈ P, v) = ∑ v ∈ P, v := by
    rw [wact_sum L P, wact_sum_P L h']
  rw [hS] at hWS
  have h2rho : ((2 : ℤ) • rhoZ : Fin 8 → ℤ) = fun _ => (2 : ℤ) := by
    funext j; simp [rhoZ]
  have hthis : wact L ((2 : ℤ) • rhoZ) = (2 : ℤ) • rhoZ := by
    rw [h2rho]; exact hWS
  have hsm : wact L ((2 : ℤ) • rhoZ) = (2 : ℤ) • wact L rhoZ := wact_smul L 2 rhoZ
  have hfin : (2 : ℤ) • wact L rhoZ = (2 : ℤ) • rhoZ := by rw [← hsm]; exact hthis
  have hr : wact L rhoZ = rhoZ := by
    funext j
    have hh := congr_fun hfin j
    have h1 : 2 * (wact L rhoZ) j = 2 * rhoZ j := by
      simpa [Pi.smul_apply, smul_eq_mul] using hh
    have h2 : rhoZ j = 1 := rfl
    rw [h2] at h1 ⊢
    omega
  rw [← wact_eq_foldl L (fun _ => 1)]
  change wact L (fun _ => 1) = (fun _ => 1) at hr
  exact hr

end Commons.LinearAlgebra.Matrix.Cartan
