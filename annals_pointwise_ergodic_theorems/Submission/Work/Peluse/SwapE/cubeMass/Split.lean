import Submission.Work.Peluse.SwapE.cubeMass.Defs

/-!
# Splitting the cube term in the first direction

The cube term `aN (d+1) f (Fin.cons δ n)` of the direction tuple `(δ, n₁, …, n_d)` factorises as

`aN (d+1) f (Fin.cons δ n) x = aN d f n x * conj (aN d f n (x + δ))`,

because the `2^{d+1}` corners of the cube split into the two `2^d`-cubes at the corners `x` and
`x + δ`.  This is the algebraic identity behind the Cauchy–Schwarz/Fejér conversion: it identifies
`Wf (d+1) f (Fin.cons δ n)` with the *autocorrelation at `δ`* of the function `aN d f n`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse

lemma weight_cons {d : ℕ} (ε : Bool) (ω : Fin d → Bool) :
    Work.Peluse.weight (Fin.cons ε ω : Fin (d + 1) → Bool)
      = Work.Peluse.weight ω + (if ε then 1 else 0) := by
  rw [Work.Peluse.BoxNorm.weight_eq_sum, Work.Peluse.BoxNorm.weight_eq_sum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases h : ε <;> simp [h] <;> omega

lemma cornerShift_cons {d : ℕ} (δ : ℤ) (n : Fin d → ℤ) (ε : Bool) (ω : Fin d → Bool) :
    Work.Peluse.cornerShift (Fin.cons δ n : Fin (d + 1) → ℤ) (0 : Fin (d + 1) → ℤ)
        (Fin.cons ε ω : Fin (d + 1) → Bool)
      = (if ε then δ else 0) + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω := by
  rw [Work.Peluse.cornerShift, Work.Peluse.cornerShift, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases h : ε <;> simp [h]

/-- Membership in `symIcc N` in terms of the absolute value. -/
lemma mem_symIcc_of_natAbs_le {N : ℕ} {z : ℤ} (h : z.natAbs ≤ N) : z ∈ symIcc N := by
  rw [symIcc, Finset.mem_Icc]
  have h2 : (((z.natAbs : ℕ)) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h2
  exact ⟨neg_le_of_abs_le h2, le_of_abs_le h2⟩

lemma natAbs_le_of_mem_symIcc {N : ℕ} {z : ℤ} (h : z ∈ symIcc N) : z.natAbs ≤ N := by
  rw [symIcc, Finset.mem_Icc] at h
  have h2 : |z| ≤ (N : ℤ) := abs_le.mpr ⟨h.1, h.2⟩
  have h3 : (((z.natAbs : ℕ)) : ℤ) = |z| := Int.natCast_natAbs z
  have h4 : (((z.natAbs : ℕ)) : ℤ) ≤ (N : ℤ) := by rw [h3]; exact h2
  exact_mod_cast h4

lemma natAbs_lt_of_notMem_symIcc {N : ℕ} {z : ℤ} (h : z ∉ symIcc N) : N < z.natAbs := by
  by_contra hc
  exact h (mem_symIcc_of_natAbs_le (by omega))

/-- The pointwise split of the cube term in the first direction. -/
theorem aN_cons {d : ℕ} (f : ℤ → ℂ) (n : Fin d → ℤ) (δ : ℤ) (x : ℤ) :
    aN (d + 1) f (Fin.cons δ n) x = aN d f n x * star (aN d f n (x + δ)) := by
  classical
  unfold aN
  set G : Bool → (Fin d → Bool) → ℂ := fun ε ω =>
    (star^[Work.Peluse.weight (Fin.cons ε ω : Fin (d + 1) → Bool)])
      (f (x + Work.Peluse.cornerShift (Fin.cons δ n : Fin (d + 1) → ℤ)
        (0 : Fin (d + 1) → ℤ) (Fin.cons ε ω : Fin (d + 1) → Bool))) with hG
  have hfalse : ∀ ω : Fin d → Bool, G false ω
      = (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω)) := by
    intro ω
    simp only [hG, weight_cons, cornerShift_cons]
    simp
  have htrue : ∀ ω : Fin d → Bool, G true ω
      = star ((star^[Work.Peluse.weight ω])
          (f ((x + δ) + Work.Peluse.cornerShift n (0 : Fin d → ℤ) ω))) := by
    intro ω
    simp only [hG, weight_cons, cornerShift_cons]
    simp only [if_true]
    rw [Function.iterate_succ_apply']
    simp only [add_assoc]
  have step1 : (∏ ω : Fin (d + 1) → Bool,
      (star^[Work.Peluse.weight ω])
        (f (x + Work.Peluse.cornerShift (Fin.cons δ n : Fin (d + 1) → ℤ)
          (0 : Fin (d + 1) → ℤ) ω)))
      = ∏ p : Bool × (Fin d → Bool), G p.1 p.2 := by
    refine Fintype.prod_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).symm _ _ ?_
    intro ω
    simp only [hG]
    rw [Fin.consEquiv_symm_apply]
    exact congrArg (fun v : Fin (d + 1) → Bool =>
        (star^[Work.Peluse.weight v])
          (f (x + Work.Peluse.cornerShift (Fin.cons δ n : Fin (d + 1) → ℤ)
            (0 : Fin (d + 1) → ℤ) v)))
      (Fin.cons_self_tail ω).symm
  rw [step1]
  rw [Fintype.prod_prod_type]
  rw [Fintype.prod_bool]
  rw [Finset.prod_congr rfl (fun ω _ => hfalse ω),
    Finset.prod_congr rfl (fun ω _ => htrue ω)]
  rw [← star_prod, mul_comm]

/-- The tsum form of the split: `Wf (d+1) f (Fin.cons δ n)` is the autocorrelation of
`aN d f n` at `δ`. -/
theorem Wf_cons {d : ℕ} (f : ℤ → ℂ) (n : Fin d → ℤ) (δ : ℤ) :
    Work.Peluse.Concat.Wf (d + 1) (fun _ : Fin (d + 1) → Bool => f) (Fin.cons δ n)
      = ∑' x : ℤ, aN d f n x * star (aN d f n (x + δ)) :=
  tsum_congr (fun x => aN_cons f n δ x)

/-- The cube term of a given direction tuple is finitely supported in the corner. -/
lemma aN_eq_zero_of_notMem_symIcc {t : ℕ} {f : ℤ → ℂ} {N : ℕ} (hf : SupportIn f N)
    (u : Fin t → ℤ) {z : ℤ} (hz : z ∉ symIcc N) : aN t f u z = 0 := by
  classical
  unfold aN
  refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin t → Bool)) ?_
  have hcs : Work.Peluse.cornerShift u (0 : Fin t → ℤ) (0 : Fin t → Bool) = 0 := by
    rw [Work.Peluse.cornerShift]
    simp
  have hw : Work.Peluse.weight (0 : Fin t → Bool) = 0 := by
    rw [Work.Peluse.BoxNorm.weight_eq_sum]
    simp
  rw [hw, hcs, add_zero, Function.iterate_zero_apply]
  exact hf z (natAbs_lt_of_notMem_symIcc hz)

end

end Work.Peluse.SwapE
