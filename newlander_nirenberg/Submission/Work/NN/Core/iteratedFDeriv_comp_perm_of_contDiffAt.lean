import Mathlib

namespace Work.NN.Core

open scoped ContDiff
open scoped Topology

/-! ## Index identities for the recursion with adjacent transpositions -/

/-- Index identity for the right-recursion case (swapping the two first slots). -/
theorem swap_zero_one_castSucc (N : ℕ) [NeZero N] (hN : 2 ≤ N) (k : Fin N) :
    (Equiv.swap (0 : Fin (N + 1)) (1 : Fin (N + 1))) k.castSucc =
      ((Equiv.swap (0 : Fin N) (1 : Fin N)) k).castSucc := by
  have h1N : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
  have h1N1 : 1 % (N + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  apply Fin.ext
  rw [Fin.val_castSucc, Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 <;>
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_zero, Fin.val_one', h1N, h1N1] at * <;>
    omega

/-- Index identity for the left-recursion case (swapping two adjacent slots, not the first). -/
theorem swap_succ_castSucc_succ (M : ℕ) (j : Fin M) (k : Fin (M + 1)) :
    (Equiv.swap j.succ.castSucc j.succ.succ) k.succ =
      ((Equiv.swap j.castSucc j.succ) k).succ := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

/-- The first slot is fixed by an adjacent transposition away from the first two slots. -/
theorem swap_succ_castSucc_succ_zero (M : ℕ) (j : Fin M) :
    (Equiv.swap j.succ.castSucc j.succ.succ) (0 : Fin (M + 2)) = 0 := by
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro h; have := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_castSucc, Fin.val_succ] at this; omega
  · intro h; have := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_succ] at this; omega

/-! ## Permutation invariance from invariance under adjacent transpositions -/

/-- If the `(N+1)`-th iterated derivative is invariant under all adjacent transpositions
`swap i.castSucc i.succ` of `Fin (N+1)`, then it is invariant under all permutations. -/
theorem perm_invariance_of_swap_castSucc {N : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E)
    (hgen : ∀ (i : Fin N) (v : Fin (N + 1) → E),
      iteratedFDeriv ℝ (N + 1) f x (v ∘ Equiv.swap i.castSucc i.succ) =
        iteratedFDeriv ℝ (N + 1) f x v) :
    ∀ (v : Fin (N + 1) → E) (σ : Equiv.Perm (Fin (N + 1))),
      iteratedFDeriv ℝ (N + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (N + 1) f x v := by
  intro v σ
  let M := iteratedFDeriv ℝ (N + 1) f x
  have hS : ∀ σ : Equiv.Perm (Fin (N + 1)), (∀ v, M (v ∘ σ) = M v) := by
    intro σ
    let S : Submonoid (Equiv.Perm (Fin (N + 1))) :=
      { carrier := {τ | ∀ v, M (v ∘ τ) = M v}
        one_mem' := by intro v; simp
        mul_mem' := by
          intro a b ha hb v
          have h1 : v ∘ (a * b) = (v ∘ a) ∘ b := by
            funext k; simp
          rw [h1, hb (v ∘ a), ha v] }
    have hle : Submonoid.closure (Set.range fun i : Fin N => Equiv.swap i.castSucc i.succ) ≤ S :=
      Submonoid.closure_le.mpr (by rintro _ ⟨i, rfl⟩; exact hgen i)
    rw [Equiv.Perm.mclosure_swap_castSucc_succ N] at hle
    exact hle (Submonoid.mem_top σ)
  exact hS σ v

/-! ## Second-order recursion identity -/

/-- The `(n+2)`-th iterated derivative is the second derivative of the `n`-th derivative as a
function of the base point. -/
theorem iteratedFDeriv_add_two_apply (n : ℕ) {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (m : Fin (n + 2) → E) (hf : ContDiffAt ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f x) :
    (iteratedFDeriv ℝ (n + 2) f x) m
      = (fderiv ℝ (fderiv ℝ (fun y => (iteratedFDeriv ℝ n f y) (Fin.tail (Fin.tail m))))
            x (m 0)) (m 1) := by
  have hdiffG : DifferentiableAt ℝ (iteratedFDeriv ℝ (n + 1) f) x :=
    (ContDiffAt.iteratedFDeriv_right hf (m := 1) (i := n + 1) (by
      exact_mod_cast (by omega : 1 + (n + 1) ≤ n + 2))).differentiableAt one_ne_zero
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y := by
    filter_upwards [ContDiffAt.eventually hf
      (by exact fun h => ENat.natCast_ne_top (n + 2) (WithTop.coe_eq_coe.mp h))] with y hy
    exact (ContDiffAt.iteratedFDeriv_right hy (m := 1) (i := n) (by
      exact_mod_cast (by omega : 1 + n ≤ n + 2))).differentiableAt one_ne_zero
  have hpt : (fun y => (iteratedFDeriv ℝ (n + 1) f y) (Fin.tail m)) =ᶠ[𝓝 x]
      fun y => fderiv ℝ (fun z => (iteratedFDeriv ℝ n f z) (Fin.tail (Fin.tail m))) y (m 1) := by
    filter_upwards [hev] with y hy
    have h1 : (Fin.tail m) 0 = m 1 := by simp [Fin.tail, Fin.succ_zero_eq_one]
    rw [← h1]
    exact DifferentiableAt.iteratedFDeriv_succ_apply_left' (f := f) (x := y) (n := n)
      (m := Fin.tail m) hy
  have hG2 : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun z => iteratedFDeriv ℝ n f z) x :=
    ContDiffAt.iteratedFDeriv_right hf (m := 2) (i := n) (by
      exact_mod_cast (by omega : 2 + n ≤ n + 2))
  have hΨ2 : ContDiffAt ℝ (2 : WithTop ℕ∞)
      (fun z => (iteratedFDeriv ℝ n f z) (Fin.tail (Fin.tail m))) x :=
    ContDiffAt.clm_apply (f := fun _ : E =>
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) F (Fin.tail (Fin.tail m))))
      contDiffAt_const hG2
  calc (iteratedFDeriv ℝ (n + 2) f x) m
      = fderiv ℝ (fun y => (iteratedFDeriv ℝ (n + 1) f y) (Fin.tail m)) x (m 0) :=
        DifferentiableAt.iteratedFDeriv_succ_apply_left' (f := f) (x := x) (n := n + 1)
          (m := m) hdiffG
    _ = fderiv ℝ (fun y => fderiv ℝ (fun z => (iteratedFDeriv ℝ n f z)
            (Fin.tail (Fin.tail m))) y (m 1)) x (m 0) := by
        rw [hpt.fderiv_eq]
    _ = (fderiv ℝ (fderiv ℝ (fun z => (iteratedFDeriv ℝ n f z) (Fin.tail (Fin.tail m))))
            x (m 0)) (m 1) := by
        have hd : DifferentiableAt ℝ
            (fderiv ℝ (fun z => (iteratedFDeriv ℝ n f z) (Fin.tail (Fin.tail m)))) x :=
          (hΨ2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
        rw [fderiv_clm_apply hd (differentiableAt_const (c := m 1))]
        simp [ContinuousLinearMap.flip_apply]

/-! ## The main induction -/

theorem iteratedFDeriv_perm_aux :
    ∀ (n : ℕ) {E F : Type*} [NormedAddCommGroup E]
      [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E),
      ContDiffAt ℝ (n : WithTop ℕ∞) f x →
        ∀ (v : Fin n → E) (σ : Equiv.Perm (Fin n)),
        iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  intro n
  induction n with
  | zero => intro E F _ _ _ _ f x hf v σ; simp
  | succ N ih =>
    rcases N with _ | _ | K
    · -- n = 1
      intro E F _ _ _ _ f x hf v σ
      exact perm_invariance_of_swap_castSucc f x (by intro i; exact i.elim0) v σ
    · -- n = 2
      intro E F _ _ _ _ f x hf v σ
      have hsymm : IsSymmSndFDerivAt ℝ f x :=
        ContDiffAt.isSymmSndFDerivAt (𝕜 := ℝ) hf (by simp)
      refine perm_invariance_of_swap_castSucc f x ?_ v σ
      intro i w
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi, Fin.castSucc_zero, Fin.succ_zero_eq_one]
      have hc0 : (w ∘ Equiv.swap (0 : Fin 2) (1 : Fin 2)) 0 = w 1 := by
        show w ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) 0) = w 1
        rw [Equiv.swap_apply_left]
      have hc1 : (w ∘ Equiv.swap (0 : Fin 2) (1 : Fin 2)) 1 = w 0 := by
        show w ((Equiv.swap (0 : Fin 2) (1 : Fin 2)) 1) = w 0
        rw [Equiv.swap_apply_right]
      rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hc0, hc1]
      exact (hsymm (w 0) (w 1)).symm
    · -- n = K + 3, ih : P (K + 2)
      intro E F _ _ _ _ f x hf v σ
      refine perm_invariance_of_swap_castSucc f x ?_ v σ
      intro i w
      by_cases hi : i.val = 0
      · -- slots 0 and 1: second-order recursion identity + symmetry of the second derivative
        have hi0 : i = 0 := Fin.ext hi
        rw [hi0, Fin.castSucc_zero, Fin.succ_zero_eq_one]
        have hG : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun y => iteratedFDeriv ℝ (K + 1) f y) x :=
          ContDiffAt.iteratedFDeriv_right hf (m := 2) (i := K + 1) (by
            exact_mod_cast (by omega : 2 + (K + 1) ≤ K + 3))
        have hΦcd : ContDiffAt ℝ (2 : WithTop ℕ∞)
            (fun y => (iteratedFDeriv ℝ (K + 1) f y) (Fin.tail (Fin.tail w))) x :=
          ContDiffAt.clm_apply (f := fun _ : E =>
            (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (K + 1) => E) F
              (Fin.tail (Fin.tail w)))) contDiffAt_const hG
        have hsymm := ContDiffAt.isSymmSndFDerivAt (𝕜 := ℝ)
          (f := fun y => (iteratedFDeriv ℝ (K + 1) f y) (Fin.tail (Fin.tail w))) hΦcd (by simp)
        have hc0 : (w ∘ Equiv.swap (0 : Fin (K + 3)) (1 : Fin (K + 3))) 0 = w 1 := by
          show w ((Equiv.swap (0 : Fin (K + 3)) (1 : Fin (K + 3))) 0) = w 1
          rw [Equiv.swap_apply_left]
        have hc1 : (w ∘ Equiv.swap (0 : Fin (K + 3)) (1 : Fin (K + 3))) 1 = w 0 := by
          show w ((Equiv.swap (0 : Fin (K + 3)) (1 : Fin (K + 3))) 1) = w 0
          rw [Equiv.swap_apply_right]
        have htail2 :
            Fin.tail (Fin.tail (w ∘ Equiv.swap (0 : Fin (K + 3)) (1 : Fin (K + 3)))) =
              Fin.tail (Fin.tail w) := by
          funext k
          simp only [Fin.tail, Function.comp_apply]
          rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero (k.succ)) (Fin.succ_succ_ne_one k)]
        rw [iteratedFDeriv_add_two_apply (n := K + 1) (f := f) (x := x)
              (m := w ∘ Equiv.swap (0 : Fin (K + 3)) (1 : Fin (K + 3))) hf,
            hc0, hc1, htail2,
            iteratedFDeriv_add_two_apply (n := K + 1) (f := f) (x := x) (m := w) hf]
        exact (hsymm (w 0) (w 1)).symm
      · -- left recursion
        have hne : i ≠ 0 := by intro h; exact hi (by rw [h]; rfl)
        obtain ⟨j, hj⟩ := (Fin.exists_succ_eq (n := K + 1)).mpr hne
        rw [← hj]
        have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (K + 2) f) x := by
          have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞) (iteratedFDeriv ℝ (K + 2) f) x :=
            ContDiffAt.iteratedFDeriv_right hf (m := 1) (i := K + 2) (by
              exact_mod_cast (by omega : 1 + (K + 2) ≤ K + 3))
          exact h1.differentiableAt one_ne_zero
        have h0 : (w ∘ Equiv.swap j.succ.castSucc j.succ.succ) 0 = w 0 := by
          show w ((Equiv.swap j.succ.castSucc j.succ.succ) 0) = w 0
          rw [swap_succ_castSucc_succ_zero (K + 1) j]
        have htail : Fin.tail (w ∘ Equiv.swap j.succ.castSucc j.succ.succ) =
            (Fin.tail w) ∘ (Equiv.swap j.castSucc j.succ) := by
          funext k
          simp only [Fin.tail, Function.comp_apply]
          exact congrArg w (swap_succ_castSucc_succ (K + 1) j k)
        have hev : (fun y => (iteratedFDeriv ℝ (K + 2) f y)
              ((Fin.tail w) ∘ (Equiv.swap j.castSucc j.succ))) =ᶠ[𝓝 x]
            (fun y => (iteratedFDeriv ℝ (K + 2) f y) (Fin.tail w)) := by
          filter_upwards [ContDiffAt.eventually hf
            (by exact fun h => ENat.natCast_ne_top (K + 3) (WithTop.coe_eq_coe.mp h))]
            with y hy
          exact ih f y (hy.of_le (by exact_mod_cast (by omega : K + 2 ≤ K + 3)))
            (Fin.tail w) (Equiv.swap j.castSucc j.succ)
        calc iteratedFDeriv ℝ (K + 3) f x (w ∘ Equiv.swap j.succ.castSucc j.succ.succ)
            = (fderiv ℝ (fun y => (iteratedFDeriv ℝ (K + 2) f y)
                (Fin.tail (w ∘ Equiv.swap j.succ.castSucc j.succ.succ))) x)
                ((w ∘ Equiv.swap j.succ.castSucc j.succ.succ) 0) :=
              DifferentiableAt.iteratedFDeriv_succ_apply_left' hdiff
          _ = (fderiv ℝ (fun y => (iteratedFDeriv ℝ (K + 2) f y)
                ((Fin.tail w) ∘ (Equiv.swap j.castSucc j.succ))) x) (w 0) := by
              rw [h0, htail]
          _ = (fderiv ℝ (fun y => (iteratedFDeriv ℝ (K + 2) f y) (Fin.tail w)) x) (w 0) := by
              rw [hev.fderiv_eq]
          _ = iteratedFDeriv ℝ (K + 3) f x w :=
              (DifferentiableAt.iteratedFDeriv_succ_apply_left' (f := f) (x := x)
                (n := K + 2) (m := w) hdiff).symm

/-- The iterated derivative of a `C^n` function is symmetric in its arguments. -/
theorem iteratedFDeriv_comp_perm_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ (n : WithTop ℕ∞) f x) {j : ℕ} (hj : j ≤ n) (v : Fin j → E)
    (σ : Equiv.Perm (Fin j)) :
    iteratedFDeriv ℝ j f x (v ∘ σ) = iteratedFDeriv ℝ j f x v :=
  iteratedFDeriv_perm_aux j f x (hf.of_le (by exact_mod_cast hj)) v σ

end Work.NN.Core
