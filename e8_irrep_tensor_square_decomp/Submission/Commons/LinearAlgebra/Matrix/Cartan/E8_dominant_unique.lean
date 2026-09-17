import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_diag_offdiag_symm
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_same_sign
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_posRoots_fixes_rho
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_height_bound

/-!
# The dominant chamber is a fundamental domain for the Weyl group of `E₈`

`Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique`: if `v` and `v'` are dominant weights
(all `ω`-coordinates nonnegative) and `v'` is obtained from `v` by a sequence of simple
reflections `(sᵢ w)ⱼ = wⱼ - wᵢ A_{ij}`, then `v = v'`.

The proof is the classical "fundamental domain" argument.  Writing `w` for the element of the Weyl
group attached to the list, the key point is:

* if every `w αᵢ` lies in the positive cone (span of the simple roots), then `w ρ = ρ`
  (`E8_weyl_posRoots_fixes_rho`), and then `w = 1` (`wact_stab_rho_trivial`);
* hence for `w ρ ≠ ρ` some `w αᵢ` has a nonpositive coordinate, and the height measure
  `620 - ⟪wρ,ρ⟫` strictly decreases along the modified word `i :: L`;
* induction on that measure gives `μ - w μ ∈` positive cone for every dominant `μ`, and applying it
  to `v` and to `v'` (with the reversed word) gives `v = v'`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

noncomputable section

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-! ## The descent -/

lemma alpha_ne_zero (i : Fin 8) : alpha i ≠ 0 := by
  intro h
  have h2 := congr_fun h i
  simp only [alpha, Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk])
    (fun hh => absurd (Finset.mem_univ i) hh)] at h2
  simp [E8m_diag] at h2

lemma e8htZ_eq_e8ht (v : Fin 8 → ℤ) : e8htZ v = E8NormTwo.e8ht v := rfl

/-- **Descent.**  If `w ρ ≠ ρ` then some `w αᵢ` has all coordinates nonpositive. -/
theorem weyl_descent_self (L : List (Fin 8)) (hne : wact L rhoZ ≠ rhoZ) :
    ∃ i : Fin 8, ∀ j, coords (wact L (alpha i)) j ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have hq : ∀ i : Fin 8, E8NormTwo.qZ (wact L (alpha i)) = 2 := by
    intro i
    rw [qZ_eq_bil, bil_wact, bil_apply, E8m_diag]
  have hsign : ∀ i : Fin 8, ∀ j, 0 ≤ coords (wact L (alpha i)) j := by
    intro i
    have hne0 : wact L (alpha i) ≠ 0 := by
      intro h0
      have h1 := wact_reverse L (alpha i)
      rw [h0, wact_zero] at h1
      exact alpha_ne_zero i h1.symm
    rcases E8_coords_same_sign (wact L (alpha i)) hne0 (hq i) with h | h
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ := hcon i
      exact absurd (h j) (not_le.mpr hj)
  have hcone : ∀ v : Fin 8 → ℤ, E8NormTwo.qZ v = 2 → v ≠ 0 → (∀ i, 0 ≤ coords v i) →
      (∀ i, 0 ≤ coords (wact L v) i) := by
    intro v _ _ hvc j
    have hvsum : v = ∑ i, (coords v i) • alpha i := by
      conv_lhs => rw [← mulVec_coords v]
      rw [mulVec_eq_sum]
    have hwv : wact L v = ∑ i, (coords v i) • wact L (alpha i) := by
      conv_lhs => rw [hvsum]
      rw [wact_sum_smul]
    rw [hwv, coords_sum_smul]
    simp only [Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hvc i) (hsign i j))
  have hfix := E8_weyl_posRoots_fixes_rho L (fun v hv hv0 hvc => by
    have hvc' : ∀ i, 0 ≤ coords v i := fun i => by
      rw [coords_apply]; exact hvc i
    intro i
    have h2 := hcone v hv hv0 hvc' i
    rwa [coords_apply] at h2)
  exact hne hfix

/-! ## The main induction -/

lemma coords_sub' (x y : Fin 8 → ℤ) : coords (x - y) = coords x - coords y := by
  rw [sub_eq_add_neg, ← neg_one_smul ℤ y, coords_add, coords_smul]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, neg_one_smul, Pi.neg_apply]
  ring

lemma wact_sub' (L : List (Fin 8)) (a b : Fin 8 → ℤ) : wact L (a - b) = wact L a - wact L b := by
  rw [sub_eq_add_neg, ← neg_one_smul ℤ b, wact_add, wact_smul]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, neg_one_smul, Pi.neg_apply]
  ring

lemma e8htZ_sub (x y : Fin 8 → ℤ) : e8htZ (x - y) = e8htZ x - e8htZ y := by
  simp only [e8htZ, coords_sub', Pi.sub_apply, Finset.sum_sub_distrib]

lemma e8htZ_rhoZ : e8htZ rhoZ = 620 := by
  simp only [e8htZ, rhoZ, coords, Matrix.mulVec, dotProduct, one_mul, E8i,
    E8NormTwo.E8inv, Fin.sum_univ_eight, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val]
  norm_num

lemma sref_alpha_self (i : Fin 8) : sref i (alpha i) = - alpha i := by
  rw [sref_eq]
  have h : (alpha i) i = 2 := by rw [alpha_apply, E8m_diag]
  rw [h]; module

lemma wact_cons_smul (i : Fin 8) (L : List (Fin 8)) (μ : Fin 8 → ℤ) :
    wact (i :: L) μ = wact L μ - μ i • wact L (alpha i) := by
  rw [wact_cons, sref_eq, wact_sub', wact_smul]

lemma wact_cons_alpha (i : Fin 8) (L : List (Fin 8)) :
    wact (i :: L) (alpha i) = - wact L (alpha i) := by
  rw [wact_cons, sref_alpha_self]
  have : (- alpha i) = (-1 : ℤ) • alpha i := by rw [neg_one_smul]
  rw [this, wact_smul]; simp

/-- `e8htZ` is the height `⟪ρ, v⟫`. -/
lemma e8htZ_def' (v : Fin 8 → ℤ) : e8htZ v = ∑ i, coords v i := rfl

/-- **The image of a dominant weight is dominated by it in the cone order.** -/
theorem weyl_acts_cone_aux (hb : ∀ L : List (Fin 8), e8htZ (wact L rhoZ) ≤ 620)
    (heq : ∀ L : List (Fin 8), e8htZ (wact L rhoZ) = 620 → wact L rhoZ = rhoZ) :
    ∀ (L : List (Fin 8)) (μ : Fin 8 → ℤ), (∀ i, 0 ≤ μ i) →
      ∀ j, 0 ≤ coords (μ - wact L μ) j := by
  suffices H : ∀ n : ℕ, ∀ (L : List (Fin 8)), (620 - e8htZ (wact L rhoZ)).toNat = n →
      ∀ (μ : Fin 8 → ℤ), (∀ i, 0 ≤ μ i) → ∀ j, 0 ≤ coords (μ - wact L μ) j by
    intro L μ hμ j; exact H _ L rfl μ hμ j
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L hn μ hμ j
    by_cases h0 : (620 - e8htZ (wact L rhoZ)).toNat = 0
    · have h620 : e8htZ (wact L rhoZ) = 620 := by have := hb L; omega
      have hid := wact_stab_rho_trivial L (heq L h620)
      rw [hid μ]
      simp [coords, sub_self]
    · have hne : wact L rhoZ ≠ rhoZ := by
        intro hh
        rw [hh, e8htZ_rhoZ] at h0
        simp at h0
      obtain ⟨i, hi⟩ := weyl_descent_self L hne
      have hne0 : wact L (alpha i) ≠ 0 := by
        intro h0'
        have h1 := wact_reverse L (alpha i)
        rw [h0', wact_zero] at h1
        exact alpha_ne_zero i h1.symm
      have hneg : e8htZ (wact L (alpha i)) ≤ -1 := by
        have h1 : e8htZ (wact L (alpha i)) ≤ 0 := by
          rw [e8htZ_def']
          exact Finset.sum_nonpos (fun k _ => hi k)
        have h2 : e8htZ (wact L (alpha i)) ≠ 0 := by
          intro h2'
          have hsum : ∑ k, coords (wact L (alpha i)) k = 0 := by
            rw [← e8htZ_def']; exact h2'
          have hall : coords (wact L (alpha i)) = 0 := by
            funext k
            simp only [Pi.zero_apply]
            have hle := hi k
            have hrest : ∑ j ∈ Finset.univ.erase k, coords (wact L (alpha i)) j ≤ 0 :=
              Finset.sum_nonpos (fun j _ => hi j)
            have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin 8))
              (fun j => coords (wact L (alpha i)) j) (Finset.mem_univ k)
            omega
          exact hne0 (by
            have : E8m.mulVec (coords (wact L (alpha i))) = 0 := by
              rw [hall]; exact Matrix.mulVec_zero E8m
            rw [← mulVec_coords (wact L (alpha i))]; exact this)
        omega
      have hlt : (620 - e8htZ (wact (i :: L) rhoZ)).toNat < n := by
        have h1 : e8htZ (wact (i :: L) rhoZ)
            = e8htZ (wact L rhoZ) - e8htZ (wact L (alpha i)) := by
          rw [wact_cons_smul, e8htZ_sub, rhoZ]
          simp
        have h2 : e8htZ (wact (i :: L) rhoZ) ≥ e8htZ (wact L rhoZ) + 1 := by
          rw [h1]; omega
        have h3 : (620 : ℤ) - e8htZ (wact (i :: L) rhoZ)
            ≤ 620 - e8htZ (wact L rhoZ) - 1 := by omega
        have h4 : (0 : ℤ) ≤ 620 - e8htZ (wact L rhoZ) := by have := hb L; omega
        have h9 : (620 : ℤ) - e8htZ (wact L rhoZ) = (n : ℤ) := by
          rw [← hn, Int.toNat_of_nonneg h4]
        have h10 : ((620 : ℤ) - e8htZ (wact (i :: L) rhoZ)).toNat ≤ n - 1 := by
          calc ((620 : ℤ) - e8htZ (wact (i :: L) rhoZ)).toNat
              ≤ ((620 : ℤ) - e8htZ (wact L rhoZ) - 1).toNat := Int.toNat_le_toNat h3
            _ = n - 1 := by rw [h9]; simp
        omega
      have hrec := ih (620 - e8htZ (wact (i :: L) rhoZ)).toNat hlt (i :: L) rfl μ hμ
      have hmain : μ - wact L μ = (μ - wact (i :: L) μ) + μ i • wact (i :: L) (alpha i) := by
        rw [wact_cons_smul, wact_cons_alpha]
        module
      rw [hmain, coords_add, coords_smul]
      simp only [Pi.add_apply, Pi.smul_apply]
      refine add_nonneg (hrec j) (mul_nonneg (hμ i) ?_)
      rw [wact_cons_alpha, coords, Matrix.mulVec_neg, Pi.neg_apply]
      exact neg_nonneg.mpr (hi j)

/-! ## Positive definiteness and the height equality -/

lemma bil_comm' (v w : Fin 8 → ℤ) : bil v w = bil w v := by
  simp only [bil, coords, dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have hs : E8i i j = E8i j i := by fin_cases i <;> fin_cases j <;> norm_num [E8i, E8NormTwo.E8inv]
  rw [hs]; ring

lemma qZ_eq_quad (v : Fin 8 → ℤ) :
    E8NormTwo.qZ v = ∑ i, ∑ j, coords v i * E8m i j * coords v j := by
  have h1 : E8NormTwo.qZ v = (E8m.mulVec (coords v)) ⬝ᵥ coords v := by
    rw [qZ_eq_bil]
    simp only [bil]
    exact congrArg (fun x => x ⬝ᵥ coords v) (mulVec_coords v).symm
  rw [h1]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _
  ring

lemma qZ_pos' (v : Fin 8 → ℤ) (hv : v ≠ 0) : 0 < E8NormTwo.qZ v := by
  have hc : coords v ≠ 0 := by
    intro h
    exact hv (by rw [← mulVec_coords v, h, Matrix.mulVec_zero])
  have h1 : 2 * E8sign_T8 (coords v)
      = ∑ i, ∑ j, coords v i * E8m i j * coords v j :=
    E8sign_two_mul_T8 (coords v)
  have h3 : 1 ≤ E8sign_T8 (coords v) := E8sign_T8_pos (coords v) hc
  rw [qZ_eq_quad, ← h1]; omega

lemma qZ_eq_zero_iff (v : Fin 8 → ℤ) (h : E8NormTwo.qZ v = 0) : v = 0 := by
  by_contra hv
  have := qZ_pos' v hv
  omega

/-- If the height of `w ρ` is maximal then `w ρ = ρ`. -/
theorem height_eq_aux (L : List (Fin 8)) (h : e8htZ (wact L rhoZ) = 620) :
    wact L rhoZ = rhoZ := by
  have h620 : bil rhoZ rhoZ = 620 := by
    rw [← e8ht_eq_bil, e8htZ_rhoZ]
  have hbil : bil rhoZ (wact L rhoZ) = 620 := by
    rw [← e8ht_eq_bil, h]
  have hww : bil (wact L rhoZ) (wact L rhoZ) = 620 := by
    rw [bil_wact, h620]
  have hx : bil (wact L rhoZ - rhoZ) (wact L rhoZ - rhoZ) = 0 := by
    rw [bil_sub_left, bil_sub_right, bil_sub_right, hww, hbil, bil_comm', hbil, h620]
    ring
  have hz : wact L rhoZ - rhoZ = 0 := by
    apply qZ_eq_zero_iff
    rw [qZ_eq_bil]
    exact hx
  exact sub_eq_zero.mp hz

/-- **Uniqueness of the dominant element of a Weyl-group orbit of `E₈`.**

If `v` and `v'` are dominant weights (all `ω`-coordinates nonnegative) and `v'` is obtained from
`v` by a sequence `L` of simple reflections `(sᵢ w)ⱼ = wⱼ - wᵢ A_{ij}`, then `v = v'`.  Equivalently
the closed dominant chamber is a fundamental domain for the Weyl group. -/
theorem E8_dominant_unique {v v' : Fin 8 → ℤ} (hv : ∀ i, 0 ≤ v i) (hv' : ∀ i, 0 ≤ v' i)
    (h : ∃ L : List (Fin 8),
      L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j) v = v') :
    v = v' := by
  obtain ⟨L, hL⟩ := h
  have hL' : wact L v = v' := hL
  have hb : ∀ L : List (Fin 8), e8htZ (wact L rhoZ) ≤ 620 := fun L => by
    have := E8_weyl_height_bound L
    rwa [show (∑ i, ∑ j, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv i j *
        (L.foldl (fun w (i : Fin 8) => fun j => w j - w i * CartanMatrix.E₈ i j)
          (fun _ => (1 : ℤ))) j) = e8htZ (wact L rhoZ) from rfl] at this
  have heq : ∀ L : List (Fin 8), e8htZ (wact L rhoZ) = 620 → wact L rhoZ = rhoZ :=
    height_eq_aux
  have key := weyl_acts_cone_aux hb heq
  have h1 : ∀ j, 0 ≤ coords (v - v') j := by
    intro j
    have := key L v hv j
    rw [hL'] at this
    exact this
  have h2 : ∀ j, 0 ≤ coords (v' - v) j := by
    intro j
    have hrev : wact L.reverse v' = v := by
      have := wact_reverse L v
      rw [hL'] at this
      exact this
    have := key L.reverse v' hv' j
    rw [hrev] at this
    exact this
  have h3 : coords (v - v') = 0 := by
    funext j
    simp only [Pi.zero_apply]
    set A : ℤ := coords (v - v') j with hA
    set B : ℤ := coords (v' - v) j with hB
    have hp : 0 ≤ A := h1 j
    have hn : 0 ≤ B := h2 j
    have hs : A = -B := by
      rw [hA, hB, coords_sub', coords_sub']
      simp only [Pi.sub_apply]; ring
    omega
  have h4 : v - v' = 0 := by
    rw [← mulVec_coords (v - v'), h3, Matrix.mulVec_zero]
  exact sub_eq_zero.mp h4

end Commons.LinearAlgebra.Matrix.Cartan
