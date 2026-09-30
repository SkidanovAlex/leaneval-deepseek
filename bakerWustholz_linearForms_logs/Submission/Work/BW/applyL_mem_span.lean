import Mathlib
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.derH_derivation
import Submission.Work.BW.applyL_compose

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The `ℂ`-span of the `applyH w t x` with `∑ k, t k ≤ n`. -/
private noncomputable abbrev spanH {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (x : MR N) (n : ℕ) : Submodule ℂ (MR N) :=
  Submodule.span ℂ {y : MR N | ∃ t : Fin q → ℕ, (∑ k, t k ≤ n) ∧ y = applyH w t x}

/-- Additivity of `derH w` in the polynomial argument. -/
private lemma bw_derH_add {N : ℕ} (w : Fin (N + 1) → ℂ) (F G : MR N) :
    derH w (F + G) = derH w F + derH w G :=
  (derH_derivation (N := N) (q := 1) (fun _ : Fin 1 => w)).2.1 0 F G

/-- `ℂ`-homogeneity of `derH w` in the polynomial argument. -/
private lemma bw_derH_smul {N : ℕ} (w : Fin (N + 1) → ℂ) (a : ℂ) (F : MR N) :
    derH w (a • F) = a • derH w F :=
  (derH_derivation (N := N) (q := 1) (fun _ : Fin 1 => w)).2.2.1 0 a F

/-- `derH w 0 = 0`. -/
private lemma bw_derH_zero {N : ℕ} (w : Fin (N + 1) → ℂ) : derH w 0 = 0 := by
  simp [derH]

/-- `derH w` commutes with finite sums. -/
private lemma bw_derH_sum {N : ℕ} (w : Fin (N + 1) → ℂ) {ι : Type*} (s : Finset ι)
    (f : ι → MR N) : derH w (∑ i ∈ s, f i) = ∑ i ∈ s, derH w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact bw_derH_zero w
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, bw_derH_add, ih]

/-- Additivity of the constant-coefficient operator `opOf w c i`. -/
private lemma bw_opOf_add {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin q → ℂ)
    (i : Fin ℓ) (F G : MR N) : opOf w c i (F + G) = opOf w c i F + opOf w c i G := by
  unfold opOf
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [bw_derH_add, smul_add]

/-- `ℂ`-homogeneity of the constant-coefficient operator `opOf w c i`. -/
private lemma bw_opOf_smul {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin q → ℂ)
    (i : Fin ℓ) (a : ℂ) (F : MR N) : opOf w c i (a • F) = a • opOf w c i F := by
  unfold opOf
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [bw_derH_smul, smul_comm]

/-- `opOf w c i 0 = 0`. -/
private lemma bw_opOf_zero {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin q → ℂ)
    (i : Fin ℓ) : opOf w c i 0 = 0 := by
  unfold opOf
  simp [bw_derH_zero]

/-- `opOf` applied to `applyH w t F`, for the re-indexed family `a ↦ w (K a)`:
Leibniz along the individual derivations `derH (w (K a))`. -/
private lemma bw_opOf_applyH {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin ℓ → ℂ)
    (K : Fin ℓ → Fin q) (i : Fin ℓ) (t : Fin q → ℕ) (F : MR N) :
    opOf (fun a : Fin ℓ => w (K a)) c i (applyH w t F)
      = ∑ a : Fin ℓ, c i a • applyH w (t + Pi.single (K a) 1) F := by
  unfold opOf
  exact Finset.sum_congr rfl fun a _ => by
    rw [(derH_derivation (N := N) (q := q) w).2.2.2.2.2 t (K a) F]

/-- Two constant-coefficient operators `opOf` (built from the same re-indexed family of
derivations) commute. -/
private lemma bw_opOf_comm {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (K : Fin ℓ → Fin q)
    (c : Fin ℓ → Fin ℓ → ℂ) (i j : Fin ℓ) (y : MR N) :
    opOf (fun a : Fin ℓ => w (K a)) c i (opOf (fun a : Fin ℓ => w (K a)) c j y)
      = opOf (fun a : Fin ℓ => w (K a)) c j (opOf (fun a : Fin ℓ => w (K a)) c i y) := by
  simp only [opOf, bw_derH_sum, bw_derH_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [(derH_derivation (N := N) (q := q) w).2.2.2.2.1 (K a) (K b) y]
  module

/-- The total weight of `t + e_k` is `∑ t + 1`. -/
private lemma bw_sum_add_single {q : ℕ} (t : Fin q → ℕ) (k : Fin q) :
    ∑ i, (t + (Pi.single k (1 : ℕ) : Fin q → ℕ)) i = ∑ i, t i + 1 := by
  have hsingle : (∑ i, (Pi.single k (1 : ℕ) : Fin q → ℕ) i) = 1 := by
    have hstep : ∀ b : Fin q, b ≠ k → (Pi.single k (1 : ℕ) : Fin q → ℕ) b = 0 :=
      fun b hb => Pi.single_eq_of_ne (M := fun _ : Fin q => ℕ) hb (1 : ℕ)
    calc (∑ i, (Pi.single k (1 : ℕ) : Fin q → ℕ) i)
        = (Pi.single k (1 : ℕ) : Fin q → ℕ) k := Fintype.sum_eq_single k hstep
      _ = 1 := Pi.single_eq_same (M := fun _ : Fin q => ℕ) k 1
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, hsingle]

/-- The operator `Λ i = opOf (fun a => w (K a)) c i` maps the span of the `applyH w t x`,
`∑ t ≤ n`, into the span of the `applyH w t x`, `∑ t ≤ n + 1`. -/
private lemma bw_opOf_mem_spanH {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ)
    (c : Fin ℓ → Fin ℓ → ℂ) (K : Fin ℓ → Fin q) (i : Fin ℓ) (x : MR N) (n : ℕ) {y : MR N}
    (hy : y ∈ spanH w x n) :
    opOf (fun a : Fin ℓ => w (K a)) c i y ∈ spanH w x (n + 1) := by
  refine Submodule.span_induction
    (p := fun z _ => opOf (fun a : Fin ℓ => w (K a)) c i z ∈ spanH w x (n + 1))
    ?_ ?_ ?_ ?_ hy
  · rintro z ⟨t, ht, rfl⟩
    rw [bw_opOf_applyH]
    refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨t + Pi.single (K a) 1, ?_, rfl⟩
    rw [bw_sum_add_single]
    omega
  · rw [bw_opOf_zero]; exact Submodule.zero_mem _
  · intro u v hu hv hpu hpv
    rw [bw_opOf_add]; exact Submodule.add_mem _ hpu hpv
  · intro a u hu hpu
    rw [bw_opOf_smul]; exact Submodule.smul_mem _ _ hpu

/-- A composition `applyL Λ α` of the constant-coefficient derivations
`Λ i = ∑ a, c i a • derH (w (K a))` maps `x` into the `ℂ`-span of the `applyH w t x` with
`∑ t ≤ ∑ α`.  Proof: induction on `∑ α`; if `α ≠ 0` pick `i` with `α i ≠ 0`, write
`α = α' + Pi.single i 1` with `α' := Function.update α i (α i - 1)` (so `∑ α' = ∑ α - 1`), use
`(applyL_compose _ hcomm).2.2.1` to peel `Λ i`, the induction hypothesis for `α'`, and the fact
that `Λ i = opOf (fun a => w (K a)) c i` maps `applyH w t y` (with `∑ t ≤ n-1`) to
`∑ a, c i a • applyH w (t + Pi.single (K a) 1) y` (Leibniz along `derH`), each summand having
`∑ (t + e) = ∑ t + 1 ≤ n`. -/
theorem applyL_mem_span {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin ℓ → ℂ)
    (K : Fin ℓ → Fin q) (x : MR N) (α : Fin ℓ → ℕ) :
    applyL (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i) α x ∈
      Submodule.span ℂ
        {y : MR N | ∃ t : Fin q → ℕ, (∑ k, t k ≤ ∑ i, α i) ∧ y = applyH w t x} := by
  have hcomm : ∀ (i j : Fin ℓ) (y : MR N),
      opOf (fun a : Fin ℓ => w (K a)) c i (opOf (fun a : Fin ℓ => w (K a)) c j y)
        = opOf (fun a : Fin ℓ => w (K a)) c j (opOf (fun a : Fin ℓ => w (K a)) c i y) :=
    fun i j y => bw_opOf_comm w K c i j y
  suffices hmain : ∀ n : ℕ, ∀ α : Fin ℓ → ℕ, (∑ i, α i) = n → ∀ x : MR N,
      applyL (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i) α x ∈ spanH w x n by
    exact hmain _ α rfl x
  intro n
  induction n with
  | zero =>
    intro α hα x
    have hα0 : α = 0 := by
      funext j
      simp only [Pi.zero_apply]
      have h1 : α j ≤ ∑ i, α i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) (Finset.mem_univ j)
      omega
    rw [hα0]
    refine Submodule.subset_span ⟨0, ?_, ?_⟩
    · simp
    · simp [applyL, applyH]
  | succ n ih =>
    intro α hα x
    have hpos : 0 < ∑ j, α j := by omega
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    have hi1 : 1 ≤ α i := Nat.one_le_iff_ne_zero.mpr hi
    have hpt : ∀ j, Function.update α i (α i - 1) j + (Pi.single i (1 : ℕ) : Fin ℓ → ℕ) j = α j := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Pi.single_eq_same (M := fun _ : Fin ℓ => ℕ)]
        omega
      · rw [Function.update_of_ne hj,
          Pi.single_eq_of_ne (M := fun _ : Fin ℓ => ℕ) hj (1 : ℕ), add_zero]
    obtain ⟨α', hα'add, hα'sum⟩ :
        ∃ α' : Fin ℓ → ℕ, α' + Pi.single i 1 = α ∧ (∑ j, α' j) = n := by
      refine ⟨Function.update α i (α i - 1), ?_, ?_⟩
      · funext j; simpa only [Pi.add_apply] using hpt j
      · have hsingle : (∑ j, (Pi.single i (1 : ℕ) : Fin ℓ → ℕ) j) = 1 := by
          have hstep : ∀ b : Fin ℓ, b ≠ i → (Pi.single i (1 : ℕ) : Fin ℓ → ℕ) b = 0 :=
            fun b hb => Pi.single_eq_of_ne (M := fun _ : Fin ℓ => ℕ) hb (1 : ℕ)
          calc (∑ j, (Pi.single i (1 : ℕ) : Fin ℓ → ℕ) j)
              = (Pi.single i (1 : ℕ) : Fin ℓ → ℕ) i := Fintype.sum_eq_single i hstep
            _ = 1 := Pi.single_eq_same (M := fun _ : Fin ℓ => ℕ) i 1
        have h2 : (∑ j, Function.update α i (α i - 1) j) +
            (∑ j, (Pi.single i (1 : ℕ) : Fin ℓ → ℕ) j) = ∑ j, α j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => hpt j
        have h1 : (∑ j, Function.update α i (α i - 1) j) + 1 = ∑ j, α j := by
          rwa [hsingle] at h2
        omega
    rw [← hα'add,
      (applyL_compose (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i) hcomm).2.2.1
        α' i x]
    have hmem' : applyL (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i) α' x ∈
        spanH w x n := ih α' hα'sum x
    exact bw_opOf_mem_spanH w c K i x n hmem'

end Work.BW
