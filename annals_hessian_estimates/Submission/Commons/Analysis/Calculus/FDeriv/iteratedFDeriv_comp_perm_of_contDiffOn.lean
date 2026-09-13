import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Order.CompletePartialOrder

open scoped Topology
open Equiv Filter

namespace Commons.Analysis.Calculus.FDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For `z : Fin (k+2) → E`, the tuple obtained by keeping the first entry and dropping it is
`Fin.tail z`, which in terms of `Fin.cons` is `cons (z 1) (fun j ↦ z j.succ.succ)`. -/
lemma fin_cons_one_tail {k : ℕ} {E : Type*} (z : Fin (k+2) → E) :
    Fin.cons (z 1) (fun j : Fin k => z j.succ.succ) = Fin.tail z := by
  rw [← Fin.cons_self_tail (Fin.tail z)]
  congr 1

/-- Decomposition of a tuple `Fin (k+2) → E` into its first two entries and the rest. -/
lemma fin_eq_cons_cons {k : ℕ} {E : Type*} (z : Fin (k+2) → E) :
    z = Fin.cons (z 0) (Fin.cons (z 1) (fun j : Fin k => z j.succ.succ)) := by
  rw [fin_cons_one_tail z, Fin.cons_self_tail]

/-- Evaluation of the `k`-th iterated derivative at a fixed tuple is `C²` if `f` is `C^{k+2}`. -/
lemma contDiffAt_iteratedFDeriv_apply {k : ℕ} (f : E → F) (x : E)
    (hf : ContDiffAt ℝ (k+2) f x) (w : Fin k → E) :
    ContDiffAt ℝ 2 (fun z => (iteratedFDeriv ℝ k f z) w) x := by
  have hk : ContDiffAt ℝ 2 (iteratedFDeriv ℝ k f) x :=
    hf.iteratedFDeriv_right (m := 2) (i := k) (by norm_cast; omega)
  have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) F w).contDiff.comp_contDiffAt x hk
  exact this

/-- For a `C^{k+2}` function, the `(k+2)`-nd iterated derivative on a tuple whose first two
entries are `a`, `b` is the second derivative of `z ↦ (D^k f z) w` at `a`, `b`. -/
lemma iteratedFDeriv_cons_cons_eq {k : ℕ} (f : E → F) (x : E)
    (hf : ContDiffAt ℝ (k+2) f x) (a b : E) (w : Fin k → E) :
    iteratedFDeriv ℝ (k+2) f x (Fin.cons a (Fin.cons b w))
      = fderiv ℝ (fderiv ℝ (fun z => (iteratedFDeriv ℝ k f z) w)) x a b := by
  have hdiff1 : DifferentiableAt ℝ (iteratedFDeriv ℝ (k+1) f) x :=
    (hf.iteratedFDeriv_right (m := 1) (i := k+1) (by norm_cast; omega)).differentiableAt
      one_ne_zero
  have hEq : ((fderiv ℝ (iteratedFDeriv ℝ (k+1) f) x) a) (Fin.cons b w)
      = ((fderiv ℝ (fun y => (iteratedFDeriv ℝ (k+1) f y) (Fin.cons b w)) x) a) := by
    rw [fderiv_continuousMultilinear_apply_const_apply hdiff1]
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]
  rw [hEq]
  have hsub : (fun y => (iteratedFDeriv ℝ (k+1) f y) (Fin.cons b w))
      =ᶠ[𝓝 x] (fun y => (fderiv ℝ (fun z => (iteratedFDeriv ℝ k f z) w) y) b) := by
    filter_upwards [hf.eventually (by
      intro h; exact ENat.natCast_ne_top (k+2) (WithTop.coe_inj.mp h))] with y hy
    have hdiffk : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) y :=
      (hy.iteratedFDeriv_right (m := 1) (i := k) (by norm_cast; omega)).differentiableAt
        one_ne_zero
    rw [iteratedFDeriv_succ_apply_left]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rw [fderiv_continuousMultilinear_apply_const_apply hdiffk]
  rw [hsub.fderiv_eq]
  have hg : ContDiffAt ℝ 2 (fun z => (iteratedFDeriv ℝ k f z) w) x :=
    contDiffAt_iteratedFDeriv_apply f x hf w
  have hclm : DifferentiableAt ℝ (fderiv ℝ (fun z => (iteratedFDeriv ℝ k f z) w)) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hclm (differentiableAt_const b)]
  simp [ContinuousLinearMap.flip_apply]

/-- The `(k+2)`-nd iterated derivative of a `C^{k+2}` function is symmetric in its first two
arguments. -/
lemma iteratedFDeriv_cons_swap {k : ℕ} (f : E → F) (x : E) (hf : ContDiffAt ℝ (k+2) f x)
    (a b : E) (w : Fin k → E) :
    iteratedFDeriv ℝ (k+2) f x (Fin.cons a (Fin.cons b w))
      = iteratedFDeriv ℝ (k+2) f x (Fin.cons b (Fin.cons a w)) := by
  rw [iteratedFDeriv_cons_cons_eq f x hf a b w, iteratedFDeriv_cons_cons_eq f x hf b a w]
  exact (ContDiffAt.isSymmSndFDerivAt (contDiffAt_iteratedFDeriv_apply f x hf w)
    (by norm_num)).eq a b

/-- Symmetry of the iterated derivative of a function which is `C^n` at a point: for the
real field, the `n`-th Fréchet derivative is invariant under permuting its arguments. -/
theorem iteratedFDeriv_comp_perm_of_contDiffAt (f : E → F) :
    ∀ (n : ℕ) (x : E) (m : Fin n → E) (σ : Perm (Fin n)),
      ContDiffAt ℝ n f x →
      iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | k
    · intro x m σ _
      simp [iteratedFDeriv_zero_apply]
    · intro x m σ _
      have hms : m ∘ σ = m := by
        funext i
        rw [Function.comp_apply]
        congr 1
        exact Fin.ext (by have := (σ i).isLt; have := i.isLt; omega)
      rw [hms]
    · intro x m σ hf
      have hd0 : DifferentiableAt ℝ (iteratedFDeriv ℝ (k+1) f) x :=
        (hf.iteratedFDeriv_right (m := 1) (i := k+1) (by norm_cast; omega)).differentiableAt
          one_ne_zero
      -- permutations of the last `k+1` entries
      have htail : ∀ (a : E) (w : Fin (k+1) → E) (ρ : Perm (Fin (k+1))),
          iteratedFDeriv ℝ (k+2) f x (Fin.cons a (w ∘ ρ))
            = iteratedFDeriv ℝ (k+2) f x (Fin.cons a w) := by
        intro a w ρ
        rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hd0,
            DifferentiableAt.iteratedFDeriv_succ_apply_left' hd0]
        simp only [Fin.tail_cons, Fin.cons_zero]
        have hev : (fun y => iteratedFDeriv ℝ (k+1) f y (w ∘ ρ))
            =ᶠ[𝓝 x] (fun y => iteratedFDeriv ℝ (k+1) f y w) := by
          filter_upwards [hf.eventually (by
            intro h; exact ENat.natCast_ne_top (k+2) (WithTop.coe_inj.mp h))] with y hy
          exact ih (k+1) (by omega) y w ρ (hy.of_le (by norm_cast; omega))
        rw [Filter.EventuallyEq.fderiv_eq hev]
      have hswap01 : ∀ (a b : E) (w : Fin k → E),
          iteratedFDeriv ℝ (k+2) f x (Fin.cons a (Fin.cons b w))
            = iteratedFDeriv ℝ (k+2) f x (Fin.cons b (Fin.cons a w)) :=
        fun a b w => iteratedFDeriv_cons_swap f x hf a b w
      let S : Submonoid (Perm (Fin (k+2))) :=
        { carrier := {τ | ∀ z : Fin (k+2) → E,
              iteratedFDeriv ℝ (k+2) f x (z ∘ τ) = iteratedFDeriv ℝ (k+2) f x z},
          one_mem' := by intro z; simp
          mul_mem' := by
            intro a b ha hb z
            have hzab : z ∘ (a * b) = (z ∘ a) ∘ b := by
              ext i; rfl
            rw [hzab, hb (z ∘ a), ha z] }
      have hmem01 : Equiv.swap (0 : Fin (k+2)) 1 ∈ S := by
        intro z
        have h1 : z ∘ Equiv.swap (0 : Fin (k+2)) 1
            = Fin.cons (z 1) (Fin.cons (z 0) (fun j : Fin k => z j.succ.succ)) := by
          rw [fin_eq_cons_cons z]
          exact Matrix.cons_cons_comp_swap_zero_one (z 0) (z 1)
            (fun j : Fin k => z j.succ.succ)
        rw [h1, (hswap01 (z 0) (z 1) (fun j : Fin k => z j.succ.succ)).symm,
          ← fin_eq_cons_cons z]
      have hmem_nz : ∀ (x' y' : Fin (k+2)), x' ≠ 0 → y' ≠ 0 → Equiv.swap x' y' ∈ S := by
        intro x' y' hx hy z
        have key : z ∘ Equiv.swap x' y'
            = Fin.cons (z 0) (Fin.tail z ∘ Equiv.swap (x'.pred hx) (y'.pred hy)) := by
          conv_lhs => rw [← Fin.cons_self_tail z]
          have hcs := Matrix.cons_swap (z 0) (Fin.tail z) (x'.pred hx) (y'.pred hy)
          simp only [Matrix.vecCons] at hcs
          rw [hcs, Fin.succ_pred x' hx, Fin.succ_pred y' hy]
        rw [key, htail (z 0) (Fin.tail z) (Equiv.swap (x'.pred hx) (y'.pred hy))]
        exact congrArg (fun u => iteratedFDeriv ℝ (k+2) f x u) (Fin.cons_self_tail z)
      have hswap_mem : ∀ (x' y' : Fin (k+2)), x' ≠ y' → Equiv.swap x' y' ∈ S := by
        intro x' y' hxy
        by_cases hx0 : x' = 0
        · subst hx0
          by_cases hy0 : y' = 0
          · exact absurd hy0.symm hxy
          by_cases hy1 : y' = 1
          · subst hy1; exact hmem01
          · have h01 : (0 : Fin (k+2)) ≠ 1 := Fin.zero_ne_one
            have h0y : (0 : Fin (k+2)) ≠ y' := fun h => hy0 h.symm
            have hconj : Equiv.swap (0 : Fin (k+2)) y'
                = Equiv.swap 1 y' * Equiv.swap 0 1 * Equiv.swap 1 y' := by
              rw [Equiv.swap_comm (0 : Fin (k+2)) y',
                ← swap_mul_swap_mul_swap (x := (0 : Fin (k+2))) (y := (1 : Fin (k+2)))
                    (z := y') h01 h0y]
            rw [hconj]
            exact S.mul_mem (S.mul_mem (hmem_nz 1 y' (Fin.zero_ne_one.symm) hy0) hmem01)
              (hmem_nz 1 y' (Fin.zero_ne_one.symm) hy0)
        · by_cases hy0 : y' = 0
          · subst hy0
            rw [Equiv.swap_comm x' 0]
            by_cases hx1 : x' = 1
            · subst hx1; exact hmem01
            · have h01 : (0 : Fin (k+2)) ≠ 1 := Fin.zero_ne_one
              have h0y : (0 : Fin (k+2)) ≠ x' := fun h => hx0 h.symm
              have hconj : Equiv.swap (0 : Fin (k+2)) x'
                  = Equiv.swap 1 x' * Equiv.swap 0 1 * Equiv.swap 1 x' := by
                rw [Equiv.swap_comm (0 : Fin (k+2)) x',
                  ← swap_mul_swap_mul_swap (x := (0 : Fin (k+2))) (y := (1 : Fin (k+2)))
                      (z := x') h01 h0y]
              rw [hconj]
              exact S.mul_mem (S.mul_mem (hmem_nz 1 x' (Fin.zero_ne_one.symm) hx0) hmem01)
                (hmem_nz 1 x' (Fin.zero_ne_one.symm) hx0)
          · exact hmem_nz x' y' hx0 hy0
      have htop : S = ⊤ := by
        rw [eq_top_iff, ← Equiv.Perm.mclosure_isSwap (α := Fin (k+2))]
        refine Submonoid.closure_le.mpr (fun σ hσ => ?_)
        rcases hσ with ⟨x', y', hxy, rfl⟩
        exact hswap_mem x' y' hxy
      exact (htop.symm ▸ Submonoid.mem_top σ) m

theorem iteratedFDeriv_comp_perm_of_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set E} {f : E → F} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) {n : ℕ} (hf : ContDiffOn ℝ n f s) (m : Fin n → E)
    (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m :=
  iteratedFDeriv_comp_perm_of_contDiffAt f n x m σ (hf.contDiffAt (hs.mem_nhds hx))

end Commons.Analysis.Calculus.FDeriv