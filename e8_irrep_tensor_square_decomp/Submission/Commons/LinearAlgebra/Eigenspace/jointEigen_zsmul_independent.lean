import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Eigenspace

/-- **ℤ-linear independence of joint eigenvectors.**  If `x m ≠ 0` are common
eigenvectors of a family `T i : M →+ M` of *additive* endomorphisms of a `ℂ`-module `M`,
with pairwise distinct integer eigenvalue functions `w m : κ → ℤ`, then the family `x` is
`ℤ`-linearly independent.

The proof isolates one vector at a time, exactly as for the `K`-linear case
(`Commons.LinearAlgebra.Eigenspace.linearIndependent_of_jointEigen`), but the operator
`T j - c • 1` and the resulting coefficient arithmetic live in `ℤ` (a domain), and the
base case uses that a `ℂ`-module has no `ℤ`-torsion. -/
theorem linearIndependent_zsmul_of_jointEigen {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ι κ : Type*} [DecidableEq ι] (T : κ → M →+ M) (x : ι → M) (w : ι → κ → ℤ)
    (hx : ∀ m i, T i (x m) = w m i • x m) (hne : ∀ m, x m ≠ 0)
    (hinj : Function.Injective w) : LinearIndependent ℤ x := by
  classical
  have isolate : ∀ (t : ι) (U : Finset ι), t ∉ U →
      (∀ u ∈ U, ∃ i, w t i ≠ w u i) → ∀ a : ι → ℤ,
        (∑ u ∈ insert t U, a u • x u) = 0 → a t = 0 := by
    intro t U
    refine Finset.induction_on U ?base ?step
    · intro ht _ a hrel
      have hrel' : a t • x t = 0 := by simpa using hrel
      by_contra ha
      have hxt : x t = 0 := by
        have h2 : (a t : ℂ) • x t = 0 := by rw [Int.cast_smul_eq_zsmul]; exact hrel'
        rcases smul_eq_zero.mp h2 with h3 | h3
        · exact absurd (Int.cast_eq_zero.mp h3) ha
        · exact h3
      exact hne t hxt
    · intro m₀ U' hm₀notin ih ht hpair a hrel
      have hm₀sep : ∃ i, w t i ≠ w m₀ i := hpair m₀ (Finset.mem_insert_self m₀ U')
      let j := Classical.choose hm₀sep
      have hj : w t j ≠ w m₀ j := Classical.choose_spec hm₀sep
      let c : ℤ := w m₀ j
      let ψ : M →+ M := T j - c • AddMonoidHom.id M
      have hψ : ∀ u, ψ (x u) = (w u j - c) • x u := by
        intro u
        show T j (x u) - c • x u = (w u j - c) • x u
        rw [hx u j, sub_smul]
      have htU' : t ∉ U' := by
        intro htU'
        exact ht (Finset.mem_insert_of_mem htU')
      have htm₀notin : m₀ ∉ insert t U' := by
        intro h
        rcases Finset.mem_insert.mp h with hmt | hm₀U'
        · subst hmt
          exact ht (Finset.mem_insert_self m₀ U')
        · exact hm₀notin hm₀U'
      have hψrel : ψ (∑ u ∈ insert t (insert m₀ U'), a u • x u) = 0 := by
        rw [hrel, map_zero]
      have hψrel' : (∑ u ∈ insert t (insert m₀ U'), (a u * (w u j - c)) • x u) = 0 := by
        rw [map_sum] at hψrel
        simpa [map_zsmul, hψ, smul_smul] using hψrel
      have hrelm₀ : (∑ u ∈ insert m₀ (insert t U'), (a u * (w u j - c)) • x u) = 0 := by
        simpa [Finset.insert_comm] using hψrel'
      have hnew : (∑ u ∈ insert t U', (a u * (w u j - c)) • x u) = 0 := by
        have hsum := hrelm₀
        rw [Finset.sum_insert htm₀notin] at hsum
        have hz : (a m₀ * (w m₀ j - c)) • x m₀ = 0 := by
          have : w m₀ j - c = 0 := by simp [c]
          rw [this, mul_zero, zero_smul]
        rw [hz, zero_add] at hsum
        exact hsum
      have hpairU' : ∀ u ∈ U', ∃ i, w t i ≠ w u i := by
        intro u hu
        exact hpair u (Finset.mem_insert_of_mem hu)
      have hbt : a t * (w t j - c) = 0 :=
        ih htU' hpairU' (fun u => a u * (w u j - c)) hnew
      have hd : w t j - c ≠ 0 := by
        simp only [c]
        exact sub_ne_zero.mpr hj
      exact (mul_eq_zero.mp hbt).resolve_right hd
  rw [linearIndependent_iff']
  intro s g hrel m hm
  have hpair : ∀ u ∈ s.erase m, ∃ i, w m i ≠ w u i := by
    intro u hu
    have hum : u ≠ m := (Finset.mem_erase.mp hu).1
    have hwm : w m ≠ w u := by
      intro hwmu
      exact hum (hinj hwmu).symm
    by_contra hno
    apply hwm
    funext i
    by_contra hnei
    exact hno ⟨i, hnei⟩
  have hmnotin : m ∉ s.erase m := by simp
  have hrel' : (∑ u ∈ insert m (s.erase m), g u • x u) = 0 := by
    simpa [Finset.insert_erase hm] using hrel
  exact isolate m (s.erase m) hmnotin hpair g hrel'

/-- Independence of joint eigenvectors of a family of *additive* endomorphisms with pairwise
distinct integer joint eigenvalue tuples: in a relation `∑ j, c j i • y j = 0` with integer
coefficients (one relation for each operator index `i`), each summand vanishes individually.
This is the `ℤ`-linear analogue of `Commons.LinearAlgebra.Eigenvector.eq_zero_of_sum_smul_eq_zero`
(the `ℂ`-linear operators there need not be `ℂ`-linear here, only additive). -/
theorem jointEigen_zsmul_independent {M : Type*} [AddCommGroup M] [Module ℂ M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Fin 8 → M →+ M) (y : ι → M)
    (eig : ι → Fin 8 → ℤ) (c : ι → Fin 8 → ℤ)
    (heig : ∀ j i, T i (y j) = (eig j i) • y j)
    (hsep : Function.Injective eig)
    (hsum : ∀ i, (∑ j, c j i • y j) = 0) :
    ∀ j i, c j i • y j = 0 := by
  classical
  -- For each operator index `i`, the single relation `∑ j, c j i • y j = 0`
  -- forces each of its summands to vanish.
  have key : ∀ i, ∀ j, c j i • y j = 0 := by
    intro i
    have hLI : LinearIndependent ℤ (fun m : {j : ι // y j ≠ 0} => y m.1) :=
      linearIndependent_zsmul_of_jointEigen T (fun m : {j : ι // y j ≠ 0} => y m.1)
        (fun m : {j : ι // y j ≠ 0} => eig m.1)
        (fun m k => heig m.1 k)
        (fun m => m.2)
        (fun m m' h => Subtype.ext (hsep h))
    rw [linearIndependent_iff'] at hLI
    intro j
    by_cases hyj : y j = 0
    · rw [hyj, smul_zero]
    · have hsum' : (∑ m : {j : ι // y j ≠ 0}, c m.1 i • y m.1) = 0 := by
        have h1 : (∑ m : {j : ι // y j ≠ 0}, c m.1 i • y m.1)
            = ∑ j ∈ Finset.univ.filter (fun j => y j ≠ 0), c j i • y j :=
          (Finset.sum_subtype (p := fun j => y j ≠ 0)
            (Finset.univ.filter (fun j => y j ≠ 0)) (fun j => by simp)
            (fun j => c j i • y j)).symm
        have h2 : (∑ j ∈ Finset.univ.filter (fun j => y j ≠ 0), c j i • y j)
            = ∑ j, c j i • y j :=
          Finset.sum_filter_of_ne (fun j _ hj hx => hj (by rw [hx, smul_zero]))
        rw [h1, h2, hsum i]
      have hzero := hLI Finset.univ (fun m : {j : ι // y j ≠ 0} => c m.1 i) hsum'
        ⟨j, hyj⟩ (Finset.mem_univ _)
      show c j i • y j = 0
      rw [hzero, zero_smul]
  exact fun j i => key i j

end Commons.LinearAlgebra.Eigenspace