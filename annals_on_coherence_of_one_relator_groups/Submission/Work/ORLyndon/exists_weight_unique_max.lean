import Mathlib

/-!
# A generic separating weight, and the existence of a unique maximising one-relator weight

This file proves `Work.ORLyndon.exists_weight_unique_max`.  Given a finite family of integer
"weight functions" `f : ι → X → ℤ` and an integer vector `e : X → ℤ` such that no two of the `f i`
differ by a *rational* multiple of `e` (`hsep`), it produces an integer vector `c : X → ℤ` with
`∑ x, c x * e x = 0` and a distinguished index `i` that is the *strict* maximiser of `x ↦ ∑ c x * f i x`.

The mathematical content is the following.  Consider the `ℚ`-vector space `M = X → ℚ` and the
hyperplane `p = ker (w ↦ ∑ x, w x * e x)`.  The hypothesis says precisely that the images of the
vectors `f i` in `M / ℚ·e` are pairwise distinct, i.e. that for every pair `i ≠ j` the functional
`w ↦ ∑ x, w x * (f i x - f j x)` is *not* identically zero on `p`.  A finite union of proper
subspaces over the infinite field `ℚ` is proper (`Module.Dual.exists_forall_mem_ne_zero_of_forall_exists`),
so there is `w ∈ p` on which all these finitely many functionals are nonzero; equivalently the
values `∑ x, w x * (f i x)` are pairwise distinct, and the maximiser `i` is then strict.  Finally
`w` is scaled by the product of the denominators of its coordinates to obtain `c : X → ℤ`.
-/

namespace Work.ORLyndon

open scoped BigOperators

section Helpers

variable {X : Type*} [Fintype X]

/-- The linear functional `w ↦ ∑ x, v x * w x` on the space `X → ℚ`, as an element of the dual. -/
noncomputable def wmaxDot (v : X → ℚ) : Module.Dual ℚ (X → ℚ) :=
  ∑ x : X, v x • (LinearMap.proj (φ := fun _ : X => ℚ) x)

lemma wmaxDot_apply (v w : X → ℚ) : wmaxDot v w = ∑ x, v x * w x := by
  simp [wmaxDot]

/-- If `d ∉ ℚ·e` then some `w` with `∑ x, e x * w x = 0` has `∑ x, d x * w x ≠ 0`. -/
lemma wmax_exists_vec (e d : X → ℚ) (hd : ¬ ∃ lam : ℚ, ∀ x, d x = lam * e x) :
    ∃ w : X → ℚ, (∑ x, e x * w x = 0) ∧ (∑ x, d x * w x ≠ 0) := by
  classical
  by_contra hcon
  push Not at hcon
  have hker : (wmaxDot e).ker ≤ (wmaxDot d).ker := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [wmaxDot_apply] at hw ⊢
    exact hcon w hw
  have hmem : wmaxDot d ∈ Submodule.span ℚ (Set.range (fun _ : Unit => wmaxDot e)) :=
    mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => wmaxDot e) (K := wmaxDot d)
      (by simpa using hker)
  have hrange : Set.range (fun _ : Unit => wmaxDot e) = {wmaxDot e} := by simp
  rw [hrange] at hmem
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  -- Evaluating `c • wmaxDot e = wmaxDot d` at the standard basis vector indexed by `x`
  -- gives `d x = c * e x`.
  refine hd ⟨c, fun x => ?_⟩
  have hs : ∀ u : X → ℚ, wmaxDot u (Pi.single x (1 : ℚ)) = u x := by
    intro u
    rw [wmaxDot_apply]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb]; simp
    · intro hx; exact absurd (Finset.mem_univ x) hx
  have h1 := congrArg (fun (g : Module.Dual ℚ (X → ℚ)) => g (Pi.single x (1 : ℚ))) hc
  rw [LinearMap.smul_apply, smul_eq_mul, hs e, hs d] at h1
  exact h1.symm

end Helpers

/-- The `ℚ`-valued version of the main result: separation of the `f i` modulo `ℚ·e` yields a
rational weight with a unique strict maximiser. -/
lemma wmax_exists_rat_weight {X ι : Type*} [Fintype X] [Fintype ι] [Nonempty ι]
    (f : ι → X → ℚ) (e : X → ℚ)
    (hsep : ∀ i j : ι, i ≠ j → ¬ ∃ lam : ℚ, ∀ x, f i x = f j x + lam * e x) :
    ∃ w : X → ℚ, (∑ x, e x * w x = 0) ∧
      ∃ i : ι, ∀ j : ι, j ≠ i → 0 < ∑ x, (f i x - f j x) * w x := by
  classical
  have hsep' : ∀ t : {t : ι × ι // t.1 ≠ t.2},
      ¬ ∃ lam : ℚ, ∀ x, f t.1.1 x - f t.1.2 x = lam * e x := by
    intro t
    rintro ⟨lam, hlam⟩
    refine hsep t.1.1 t.1.2 t.2 ⟨lam, fun x => ?_⟩
    have := hlam x
    linarith
  have hex : ∀ t : {t : ι × ι // t.1 ≠ t.2}, ∃ w : X → ℚ,
      (∑ x, e x * w x = 0) ∧ (∑ x, (f t.1.1 x - f t.1.2 x) * w x ≠ 0) :=
    fun t => wmax_exists_vec e (fun x => f t.1.1 x - f t.1.2 x) (hsep' t)
  have h : ∀ t : {t : ι × ι // t.1 ≠ t.2},
      ∃ w ∈ (wmaxDot e).ker, (wmaxDot (fun x => f t.1.1 x - f t.1.2 x)) w ≠ 0 := by
    intro t
    obtain ⟨w, h1, h2⟩ := hex t
    exact ⟨w, by rw [LinearMap.mem_ker, wmaxDot_apply]; exact h1, by rwa [wmaxDot_apply]⟩
  obtain ⟨w, hwmem, hwne⟩ :=
    Module.Dual.exists_forall_mem_ne_zero_of_forall_exists (wmaxDot e).ker
      (fun t : {t : ι × ι // t.1 ≠ t.2} => wmaxDot (fun x => f t.1.1 x - f t.1.2 x)) h
  have hwe : ∑ x, e x * w x = 0 := by
    have := hwmem; rw [LinearMap.mem_ker, wmaxDot_apply] at this; exact this
  set g : ι → ℚ := fun i => ∑ x, f i x * w x with hg_def
  have hdiff : ∀ i j, g i - g j = ∑ x, (f i x - f j x) * w x := by
    intro i j
    simp only [hg_def]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have hg_inj : ∀ i j, i ≠ j → g i ≠ g j := by
    intro i j hij h_eq
    have hne := hwne ⟨(i, j), hij⟩
    rw [wmaxDot_apply] at hne
    exact hne (by rw [← hdiff i j, h_eq]; ring)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  refine ⟨w, hwe, i, fun j hj => ?_⟩
  have hle : g j ≤ g i := hi j (Finset.mem_univ j)
  have hne : g j ≠ g i := hg_inj j i hj
  have hlt : g j < g i := lt_of_le_of_ne hle hne
  rw [← hdiff i j]
  linarith

theorem exists_weight_unique_max {X ι : Type*} [Fintype X] [Fintype ι] [Nonempty ι]
    (f : ι → X → ℤ) (e : X → ℤ)
    (hsep : ∀ i j : ι, i ≠ j → ¬ ∃ (lam : ℚ), ∀ x : X, (f i x : ℚ) = (f j x : ℚ) + lam * (e x : ℚ)) :
    ∃ c : X → ℤ, (∑ x, (c x : ℚ) * (e x : ℚ) = 0) ∧
      ∃ i : ι, ∀ j : ι, j ≠ i →
        0 < ∑ x, (c x : ℚ) * ((f i x : ℚ) - (f j x : ℚ)) := by
  classical
  obtain ⟨w, hwe, i, hwi⟩ :=
    wmax_exists_rat_weight (fun i x => (f i x : ℚ)) (fun x => (e x : ℚ)) hsep
  -- Clear denominators: `N` is a common denominator of all the coordinates of `w`.
  set N : ℕ := ∏ x : X, (w x).den with hN
  have key : ∀ x, (((w x).num * ((N / (w x).den : ℕ) : ℤ) : ℤ) : ℚ) = (N : ℚ) * w x := by
    intro x
    have hdvd : (w x).den ∣ N := by rw [hN]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ x)
    have hden : (((w x).den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz (w x)
    have hcast : (((N / (w x).den : ℕ)) : ℚ) = (N : ℚ) / ((w x).den : ℚ) :=
      Nat.cast_div hdvd hden
    rw [Int.cast_mul, Int.cast_natCast, hcast]
    conv_rhs => rw [← Rat.num_div_den (w x)]
    ring
  refine ⟨fun x => (w x).num * ((N / (w x).den : ℕ) : ℤ), ?_, i, fun j hj => ?_⟩
  · calc ∑ x, (((w x).num * ((N / (w x).den : ℕ) : ℤ) : ℤ) : ℚ) * (e x : ℚ)
        = ∑ x, (N : ℚ) * ((e x : ℚ) * w x) := by
          apply Finset.sum_congr rfl; intro x _
          rw [key x]; ring
      _ = (N : ℚ) * ∑ x, (e x : ℚ) * w x := by rw [Finset.mul_sum]
      _ = 0 := by rw [hwe]; ring
  · have hNpos : (0 : ℚ) < (N : ℚ) := by
      have : 0 < N := by rw [hN]; exact Finset.prod_pos (fun x _ => Rat.den_pos (w x))
      exact_mod_cast this
    calc (0 : ℚ) < (N : ℚ) * ∑ x, ((f i x : ℚ) - (f j x : ℚ)) * w x :=
          mul_pos hNpos (hwi j hj)
      _ = ∑ x, (((w x).num * ((N / (w x).den : ℕ) : ℤ) : ℤ) : ℚ) *
            ((f i x : ℚ) - (f j x : ℚ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [key x]; ring

end Work.ORLyndon
