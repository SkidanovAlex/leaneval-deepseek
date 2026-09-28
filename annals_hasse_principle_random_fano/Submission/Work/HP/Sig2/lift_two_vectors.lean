import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.MulDefs
import Submission.Work.HP.Vero.mulVec_formEval
import Submission.Work.HP.Vero.mulVec_assoc
import Submission.Work.HP.Vero.mulVec_symm
import Submission.Work.HP.MDBasic.mem_Gam_iff

/-!
# The `Ψ`-lift for the two-vector key lemma (`Work.HP.Sig2.lift_two_vectors`)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.Sig2.LiftTwo

open Work.HP Vero

variable {n : ℕ}

/-! ## Multiplicativity of `formEvalR` for `mulVec` (real coefficients) -/

/-- `formEvalR` is multiplicative with respect to `mulVec` (real coefficient vectors).  This is the
real-coefficient analogue of `Vero.mulVec_formEval`, proved by the same exchange argument. -/
theorem mulVec_formEvalR' {a b n : ℕ} (A : Mon a n → ℝ) (B : Mon b n → ℝ)
    (z : Fin (n + 1) → ℝ) :
    formEvalR (a + b) n (mulVec a b (a + b) A B) z
      = formEvalR a n A z * formEvalR b n B z := by
  rw [formEvalR, formEvalR, formEvalR, Finset.sum_mul_sum]
  simp only [mulVec]
  simp only [← addMon_eq_iff]
  rw [sum_ite_prod_mul (fun p (q : Mon b n) => addMon p q) (fun p q => A p * B q)
      (fun M => veronese (a + b) n z M)]
  simp only [veronese_addMon]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-! ## The space `VR k x y` of degree-`k` forms vanishing at `x` and `y` -/

/-- The evaluation functional `F ↦ ∑_m F m · x^m` for degree-`k` coefficient vectors. -/
def ev (k : ℕ) (z : Fin (n + 1) → ℤ) : (Mon k n → ℝ) →ₗ[ℝ] ℝ :=
  Fintype.linearCombination ℝ fun m : Mon k n => ((veronese k n z m : ℤ) : ℝ)

lemma ev_apply (k : ℕ) (z : Fin (n + 1) → ℤ) (F : Mon k n → ℝ) :
    ev k z F = ∑ m, F m * ((veronese k n z m : ℤ) : ℝ) := by
  simp [ev, Fintype.linearCombination]

/-- The real vector space of degree-`k` forms vanishing at `x` and at `y`. -/
def VR (k : ℕ) (x y : Fin (n + 1) → ℤ) : Submodule ℝ (Mon k n → ℝ) :=
  (ev k x).ker ⊓ (ev k y).ker

lemma mem_VR {k : ℕ} {x y : Fin (n + 1) → ℤ} {F : Mon k n → ℝ} :
    F ∈ VR k x y ↔ ev k x F = 0 ∧ ev k y F = 0 := by
  simp [VR]

/-- `ev` at an integral vector, evaluated at a real vector. -/
lemma ev_eq_formEvalR (k : ℕ) (z : Fin (n + 1) → ℤ) (F : Mon k n → ℝ) :
    ev k z F = formEvalR k n F (fun i => (z i : ℝ)) := by
  rw [ev_apply, formEvalR]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  simp only [veronese]
  push_cast
  rfl

/-! ## The shift `X_i ·` on coefficient vectors and its adjoint "extraction" -/

/-- The coefficient vector of `X_i` times the form with coefficient vector `u`. -/
def shift {k : ℕ} (i : Fin (n + 1)) (u : Mon k n → ℝ) : Mon (k + 1) n → ℝ :=
  mulVec k 1 (k + 1) u (unitMon (R := ℝ) (eMon n i))

/-- The `i`-th extraction: `(extr i T) m = T (m + e_i)`. -/
def extr {k : ℕ} (i : Fin (n + 1)) (T : Mon (k + 1) n → ℝ) : Mon k n → ℝ :=
  fun m => T (addMon m (eMon n i))

@[simp] lemma extr_apply {k : ℕ} (i : Fin (n + 1)) (T : Mon (k + 1) n → ℝ)
    (m : Mon k n) : extr i T m = T (addMon m (eMon n i)) := rfl

/-- The standard (coordinate) pairing of coefficient vectors. -/
def ip {k : ℕ} (F G : Mon k n → ℝ) : ℝ := ∑ m, F m * G m

/-- **The shift lands in `VR (k+1)`.** -/
lemma shift_mem_VR (k : ℕ) (x y : Fin (n + 1) → ℤ) (i : Fin (n + 1))
    {u : Mon k n → ℝ} (hu : u ∈ VR k x y) : shift i u ∈ VR (k + 1) x y := by
  obtain ⟨hx, hy⟩ := (mem_VR.mp hu)
  rw [mem_VR]
  have hx' : formEvalR k n u (fun i => (x i : ℝ)) = 0 := by
    rw [← ev_eq_formEvalR]; exact hx
  have hy' : formEvalR k n u (fun i => (y i : ℝ)) = 0 := by
    rw [← ev_eq_formEvalR]; exact hy
  constructor
  · rw [ev_eq_formEvalR]
    simp only [shift]
    rw [mulVec_formEvalR', hx', zero_mul]
  · rw [ev_eq_formEvalR]
    simp only [shift]
    rw [mulVec_formEvalR', hy', zero_mul]

/-- `mulVec` with a unit second argument: the entries of `u` shifted by the monomial `P`. -/
lemma mulVec_unitMon_apply {a b : ℕ} (u : Mon a n → ℝ) (P : Mon b n) (M : Mon (a + b) n) :
    mulVec a b (a + b) u (unitMon (R := ℝ) P) M
      = ∑ p : Mon a n, if addMon p P = M then u p else 0 := by
  rw [mulVec]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single P]
  · rw [unitMon_same, mul_one]
    by_cases h : addMon p P = M
    · have h' : (∀ i, (p.1 i : ℕ) + (P.1 i : ℕ) = (M.1 i : ℕ)) := fun i => by
        rw [← h]; exact addMon_val p P i
      rw [if_pos h, if_pos h']
    · have h' : ¬ (∀ i, (p.1 i : ℕ) + (P.1 i : ℕ) = (M.1 i : ℕ)) := fun hh =>
        h (by
          apply Subtype.ext
          funext i
          exact Fin.ext (hh i))
      rw [if_neg h, if_neg h']
  · intro q _ hq
    rw [unitMon_of_ne hq, mul_zero, ite_self]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The adjointness of `shift` and `extr`**: `⟪T, X_i·u⟫ = ⟪extrᵢ T, u⟫`. -/
lemma ip_shift {k : ℕ} (i : Fin (n + 1)) (T : Mon (k + 1) n → ℝ) (u : Mon k n → ℝ) :
    ip T (shift i u) = ip (extr i T) u := by
  rw [ip, ip]
  simp only [shift, mulVec_unitMon_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (addMon p (eMon n i))]
  · rw [if_pos rfl, extr_apply, mul_comm]
  · intro M _ hM
    rw [if_neg (fun h => hM h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h


/-! ## Linear independence of the two Veronese vectors over `ℝ` -/

/-- The Veronese value at a unit monomial. -/
lemma veronese_eMon (z : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    veronese 1 n z (eMon n i) = z i := by
  rw [veronese, Finset.prod_eq_single i]
  · rw [eMon_val, if_pos rfl, pow_one]
  · intro j _ hj
    rw [eMon_val, if_neg hj, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- For integer vectors, `ℤ`-linear independence implies `ℝ`-linear independence (base change). -/
lemma real_li_of_int_li (x y : Fin (n + 1) → ℤ) (h : LinearIndependent ℤ ![x, y]) :
    LinearIndependent ℝ ![(fun j => (x j : ℝ)), (fun j => (y j : ℝ))] := by
  have h' := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := ![x, y])).mpr h
  rw [show (![(fun j => (x j : ℝ)), (fun j => (y j : ℝ))] : Fin 2 → Fin (n + 1) → ℝ)
      = (fun i => algebraMap ℤ ℝ ∘ ![x, y] i) from ?_]
  · exact h'
  · funext i j
    fin_cases i <;> rfl

/-- **Probe nondegeneracy.**  For `m ≥ 1` and `ℤ`-linearly independent `x, y`, a linear relation
between the two Veronese vectors `ν_m(x)`, `ν_m(y)` is trivial.  Inductively, the probes
`ν_{m+1}(z)_{ν+e_i} = z_i · ν_m(z)_ν` reduce the claim to the case `m = 1`. -/
lemma probes_injective (x y : Fin (n + 1) → ℤ) (hxy : LinearIndependent ℤ ![x, y]) :
    ∀ m : ℕ, 1 ≤ m → ∀ C D : ℝ,
      (∀ μ : Mon m n, C * ((veronese m n x μ : ℤ) : ℝ) + D * ((veronese m n y μ : ℤ) : ℝ) = 0) →
      C = 0 ∧ D = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      intro C D hCD
      have hR := real_li_of_int_li (n := n) x y hxy
      have hzero :
          C • (fun j => (x j : ℝ)) + D • (fun j => (y j : ℝ)) = 0 := by
        funext j
        have hj := hCD (eMon n j)
        rw [veronese_eMon, veronese_eMon] at hj
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hj
      exact (LinearIndependent.pair_iff.mp hR) C D hzero
  | succ m hm ih =>
      intro C D hCD
      have hx0 : x ≠ 0 := hxy.ne_zero 0
      have hy0 : y ≠ 0 := hxy.ne_zero 1
      have hsplit : ∀ i : Fin (n + 1),
          (∀ ν : Mon m n, (C * (x i : ℝ)) * ((veronese m n x ν : ℤ) : ℝ)
            + (D * (y i : ℝ)) * ((veronese m n y ν : ℤ) : ℝ) = 0) := by
        intro i ν
        have hi := hCD (addMon ν (eMon n i))
        simp only [veronese_addMon, veronese_eMon] at hi
        push_cast at hi
        linarith [hi]
      have hCi : ∀ i : Fin (n + 1), C * (x i : ℝ) = 0 := fun i => (ih _ _ (hsplit i)).1
      have hDi : ∀ i : Fin (n + 1), D * (y i : ℝ) = 0 := fun i => (ih _ _ (hsplit i)).2
      constructor
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
        have hxi : (x i : ℝ) ≠ 0 := by exact_mod_cast hi
        exact (mul_eq_zero.mp (hCi i)).resolve_right hxi
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
        have hyi : (y i : ℝ) ≠ 0 := by exact_mod_cast hi
        exact (mul_eq_zero.mp (hDi i)).resolve_right hyi

/-- **Subtracting a unit monomial.**  A monomial of degree `k+1` with positive `i`-th coordinate is
`ν + e_i` with `ν` of degree `k`. -/
lemma exists_sub_eMon {k : ℕ} (m : Mon (k + 1) n) {i : Fin (n + 1)} (hi : 1 ≤ (m.1 i : ℕ)) :
    ∃ μ : Mon k n, addMon μ (eMon n i) = m := by
  classical
  set δ : Fin (n + 1) → ℕ := fun j => if j = i then 1 else 0 with hδ
  have hδi : δ i = 1 := by simp [hδ]
  have hδle : ∀ j, δ j ≤ (m.1 j : ℕ) := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa [hδ] using hi
    · simp [hδ, hj]
  have hsumδ : (∑ j, δ j) = 1 := by
    rw [hδ, Finset.sum_ite_eq']
    simp
  have hsum : (∑ j, ((m.1 j : ℕ) - δ j)) = k := by
    have h1 : (∑ j, (((m.1 j : ℕ) - δ j) + δ j)) = ∑ j, (m.1 j : ℕ) :=
      Finset.sum_congr rfl fun j _ => Nat.sub_add_cancel (hδle j)
    rw [Finset.sum_add_distrib, hsumδ, m.2] at h1
    omega
  have hle : ∀ j, ((m.1 j : ℕ) - δ j) < k + 1 := by
    intro j
    have hmj : (m.1 j : ℕ) ≤ k + 1 := Nat.lt_succ_iff.mp (m.1 j).isLt
    by_cases hj : j = i
    · rw [hj, hδi]
      omega
    · have hpair : (m.1 j : ℕ) + (m.1 i : ℕ) ≤ ∑ l, (m.1 l : ℕ) := by
        have hsub : ({j, i} : Finset (Fin (n + 1))) ⊆ Finset.univ := Finset.subset_univ _
        have h2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => (m.1 l : ℕ)) hsub
          (fun l _ _ => Nat.zero_le _)
        rwa [Finset.sum_insert (by simp [hj]), Finset.sum_singleton] at h2
      have hδj : δ j = 0 := by simp [hδ, hj]
      rw [hδj]
      omega
  refine ⟨⟨fun j => ⟨((m.1 j : ℕ) - δ j), hle j⟩, hsum⟩, ?_⟩
  apply Subtype.ext
  funext j
  apply Fin.ext
  rw [addMon_val, eMon_val]
  by_cases hj : j = i
  · rw [hj]
    show ((m.1 i : ℕ) - δ i) + (if i = i then 1 else 0) = (m.1 i : ℕ)
    rw [hδi, if_pos rfl, Nat.sub_add_cancel hi]
  · have hδj : δ j = 0 := by simp [hδ, hj]
    show ((m.1 j : ℕ) - δ j) + (if j = i then 1 else 0) = (m.1 j : ℕ)
    rw [hδj, if_neg hj]
    simp

end Work.HP.Sig2.LiftTwo
