import Mathlib
import Submission.Work.BW.wuestholzDefs
import Submission.Work.BW.derH_derivation
import Submission.Work.BW.applyL_compose
import Submission.Work.BW.applyL_pow_le
import Submission.Work.BW.applyL_mem_span
import Submission.Work.BW.extract_coeff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Additivity of the constant-coefficient operator `opOf w c i`. -/
private lemma opOf_add {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin q → ℂ)
    (i : Fin ℓ) (F G : MR N) : opOf w c i (F + G) = opOf w c i F + opOf w c i G := by
  unfold opOf
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by
    rw [(derH_derivation w).2.1 k F G, smul_add]

/-- Leibniz rule for the constant-coefficient operator `opOf w c i`. -/
private lemma opOf_mul {N q ℓ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (c : Fin ℓ → Fin q → ℂ)
    (i : Fin ℓ) (F G : MR N) : opOf w c i (F * G) = opOf w c i F * G + F * opOf w c i G := by
  unfold opOf
  trans ∑ k, (c i k • derH (w k) F * G + F * (c i k • derH (w k) G))
  · exact Finset.sum_congr rfl fun k _ => by
      rw [(derH_derivation w).1 k F G, smul_add, smul_mul_assoc, mul_smul_comm]
  · rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

/-- An additive map commutes with iterates. -/
private lemma iterate_add_of_additive {α : Type*} [AddCommMonoid α] (f : α → α)
    (hf : ∀ x y, f (x + y) = f x + f y) (n : ℕ) (x y : α) :
    f^[n] (x + y) = f^[n] x + f^[n] y := by
  induction n generalizing x y with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, hf x y, ih (f x) (f y)]

/-- Additivity of `applyL` in its argument, for a family of additive operators. -/
private lemma applyL_map_add {R : Type*} [AddCommMonoid R] {ℓ : ℕ} (Λ : Fin ℓ → R → R)
    (hadd : ∀ i x y, Λ i (x + y) = Λ i x + Λ i y) (α : Fin ℓ → ℕ) (x y : R) :
    applyL Λ α (x + y) = applyL Λ α x + applyL Λ α y := by
  unfold applyL
  induction (List.finRange ℓ) with
  | nil => simp
  | cons i L ih =>
    simp only [List.foldr_cons]
    rw [ih, iterate_add_of_additive (Λ i) (hadd i) (α i)]

/-- A finite product of elements outside a prime ideal is outside it. -/
private lemma prod_notMem_of_forall_notMem {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I.IsPrime) {ι : Type*} {s : Finset ι} {f : ι → R} (h : ∀ i ∈ s, f i ∉ I) :
    ∏ i ∈ s, f i ∉ I := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    intro h1
    exact hI.ne_top (Submodule.eq_top_iff'.mpr fun x => by
      simpa using Ideal.mul_mem_left I x h1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    intro hmem
    rcases hI.mem_or_mem hmem with h1 | h1
    · exact h a (Finset.mem_insert_self a s) h1
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) h1

/-- A power of an element outside a prime ideal is outside it. -/
private lemma pow_notMem_of_notMem {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsPrime)
    {x : R} (hx : x ∉ I) : ∀ n, x ^ n ∉ I := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero]
    intro h1
    exact hI.ne_top (Submodule.eq_top_iff'.mpr fun y => by
      simpa using Ideal.mul_mem_left I y h1)
  | succ n ih => rw [pow_succ]; exact fun h => (hI.mem_or_mem h).elim ih hx

/-- The independence of the weighted monomials modulo `J + 𝔓^{τ+1}` (Philippon 4.6–4.7),
given the dual congruences.  For the operators `Λ i = ∑ a, c i a • derH (w (K a))` with
`Λ i (u j) ≡ D j · δᵢⱼ` modulo `𝔓`, `u j ∈ 𝔓`, `D j ∉ 𝔓`, and `applyH w t (J) ⊆ 𝔓` for
`∑ t ≤ T`: if `∑_{|β|=τ} C β · u^β ∈ J + 𝔓^{τ+1}` (with `τ ≤ T`, coefficients in `MR N`), then
every `C α ∈ 𝔓`.  Proof: clear denominators (multiply by `m ∈ 𝔓.primeCompl`), apply the
extraction lemma `extract_coeff` to the order-`τ` operator `Λ^α` — whose value on an element of
`J` lies in `𝔓` (via `applyL_mem_span` and `hT`) and on an element of `𝔓^{τ+1}` lies in `𝔓` (via
`applyL_pow_le`) — and cancel the non-vanishing factors `(∏ αᵢ!)`, `∏ Dᵢ^{αᵢ}`, `m`. -/
theorem indep_of_cong {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (𝔓 : Ideal (MR N))
    (hprime : 𝔓.IsPrime) (J : Ideal (MR N)) (T : ℕ)
    (hT : ∀ F ∈ J, ∀ t : Fin q → ℕ, ∑ k, t k ≤ T → applyH w t F ∈ 𝔓)
    {ℓ : ℕ} (u D : Fin ℓ → MR N) (c : Fin ℓ → Fin ℓ → ℂ) (K : Fin ℓ → Fin q)
    (hu : ∀ j, u j ∈ 𝔓) (hD : ∀ j, D j ∉ 𝔓)
    (hcong : ∀ i j, opOf (fun a : Fin ℓ => w (K a)) c i (u j)
        - D j * (if i = j then (1 : MR N) else 0) ∈ 𝔓) :
    ∀ (τ : ℕ), τ ≤ T → ∀ C : (Fin ℓ → ℕ) → MR N,
      algebraMap (MR N) (Localization.AtPrime 𝔓)
          (∑ β ∈ weightFinset ℓ τ, C β * monoPow u β)
        ∈ Ideal.map (algebraMap (MR N) (Localization.AtPrime 𝔓)) (J + 𝔓 ^ (τ + 1)) →
      ∀ α ∈ weightFinset ℓ τ, C α ∈ 𝔓 := by
  classical
  haveI := hprime
  intro τ hτ C hmem α hα
  have hαsum : ∑ i, α i = τ := (Finset.mem_filter.mp hα).2
  obtain ⟨m, hm, hmem'⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (𝔓.primeCompl)
      (Localization.AtPrime 𝔓) (J + 𝔓 ^ (τ + 1))
      (∑ β ∈ weightFinset ℓ τ, C β * monoPow u β)).mp hmem
  have hm' : m ∉ 𝔓 := hm
  have hX : applyL (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i) α
      (weightedSum u τ (fun β => m * C β)) ∈ 𝔓 := by
    have heq : weightedSum u τ (fun β => m * C β)
        = m * (∑ β ∈ weightFinset ℓ τ, C β * monoPow u β) := by
      rw [weightedSum_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [heq]
    obtain ⟨j, hjJ, hjPow, hjP, hsum⟩ := Submodule.mem_sup.mp hmem'
    rw [← hsum]
    rw [applyL_map_add (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i)
      (fun i => opOf_add (fun a : Fin ℓ => w (K a)) c i) α j hjPow]
    refine Submodule.add_mem _ ?_ ?_
    · have hsub : Submodule.span ℂ
          {y : MR N | ∃ t : Fin q → ℕ, (∑ k, t k ≤ ∑ i, α i) ∧ y = applyH w t j}
          ≤ Submodule.restrictScalars ℂ 𝔓 := by
        rw [Submodule.span_le]
        rintro y ⟨t, ht, rfl⟩
        exact hT j hjJ t (le_trans (le_trans ht (le_of_eq hαsum)) hτ)
      exact hsub (applyL_mem_span w c K j α)
    · have hm1 : τ + 1 - ∑ i, α i = 1 := by rw [hαsum]; omega
      have h2 : applyL (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i) α hjPow ∈ 𝔓 := by
        have h := applyL_pow_le (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i)
          (fun i => opOf_add (fun a : Fin ℓ => w (K a)) c i)
          (fun i => opOf_mul (fun a : Fin ℓ => w (K a)) c i) 𝔓 (m := τ + 1) α
          (by rw [hαsum]; exact Nat.le_succ τ) hjPow hjP
        rwa [hm1, pow_one] at h
      exact h2
  have hbig := extract_coeff 𝔓 (fun i : Fin ℓ => opOf (fun a : Fin ℓ => w (K a)) c i)
    u D (fun i => opOf_add (fun a : Fin ℓ => w (K a)) c i) (fun i => opOf_mul (fun a : Fin ℓ => w (K a)) c i) hu hcong α hαsum
    (fun β => m * C β) hX
  have hfac : IsUnit (((∏ i, (α i).factorial : ℕ) : MR N)) := by
    rw [show ((∏ i, (α i).factorial : ℕ) : MR N)
        = algebraMap ℂ (MR N) ((∏ i, (α i).factorial : ℕ) : ℂ) from
      (map_natCast (algebraMap ℂ (MR N)) (∏ i, (α i).factorial)).symm]
    refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
    simp only [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _
  have hAnot : ((∏ i, (α i).factorial : ℕ) : MR N) ∉ 𝔓 :=
    fun h => hprime.ne_top (Ideal.eq_top_of_isUnit_mem 𝔓 h hfac)
  have hBnot : (∏ i, D i ^ (α i)) ∉ 𝔓 :=
    prod_notMem_of_forall_notMem hprime fun i _ => pow_notMem_of_notMem hprime (hD i) (α i)
  have hAB : ((∏ i, (α i).factorial : ℕ) : MR N) * (∏ i, D i ^ (α i)) ∉ 𝔓 :=
    fun h => (hprime.mem_or_mem h).elim hAnot hBnot
  rcases hprime.mem_or_mem hbig with h1 | h1
  · exact absurd h1 hAB
  · rcases hprime.mem_or_mem h1 with h2 | h2
    · exact absurd h2 hm'
    · exact h2

end Work.BW
