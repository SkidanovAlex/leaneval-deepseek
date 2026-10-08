import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.pow_mem_frattiniIn

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

open scoped Pointwise commutatorElement

namespace Work.NormalComplement.AppVII

/-- **Peterfalvi Appendix VII, Part 1 step 1 (the shape of `K`).**  If a finite abelian group `K`
with `Φ(K) = 1` is `A`-irreducible (no proper nontrivial `A`-invariant subgroup), then `K` is an
elementary abelian `r`-group for a prime `r`. -/
theorem ElementaryOfIrreducible {A : Type} [Group A] {K : Type} [Group K] [Finite K]
    [MulDistribMulAction A K] (hKcomm : IsMulCommutative K) (hPhi : frattini K = ⊥)
    (hnt : Nontrivial K)
    (hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤) :
    ∃ r : ℕ, r.Prime ∧ ∀ x : K, x ^ r = 1 := by
  classical
  haveI hF : Fintype K := Fintype.ofFinite K
  have hcard_ne_one : Nat.card K ≠ 1 := by
    intro h
    have hsub : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h).1
    exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub
  obtain ⟨r, hr, hrK⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  haveI : Fact r.Prime := ⟨hr⟩
  refine ⟨r, hr, ?_⟩
  let f : ℕ → K →* K := fun n => MonoidHom.mk' (fun x : K => x ^ (r ^ n))
    (fun x y => by rw [Commute.mul_pow (hKcomm.is_comm.comm x y)])
  let S : Subgroup K := ⨆ n : ℕ, (f n).ker
  have hfker : ∀ (n : ℕ) (x : K), x ∈ (f n).ker ↔ x ^ (r ^ n) = 1 := by
    intro n x; rw [MonoidHom.mem_ker]; rfl
  have hdir : Directed (· ≤ ·) (fun n : ℕ => (f n).ker) := by
    intro m n
    refine ⟨max m n, ?_, ?_⟩
    · intro x hx
      rw [hfker] at hx ⊢
      obtain ⟨c, hc⟩ := Nat.pow_dvd_pow r (le_max_left m n)
      rw [hc, pow_mul, hx, one_pow]
    · intro x hx
      rw [hfker] at hx ⊢
      obtain ⟨c, hc⟩ := Nat.pow_dvd_pow r (le_max_right m n)
      rw [hc, pow_mul, hx, one_pow]
  have hSinv : ∀ a : A, ∀ x ∈ S, a • x ∈ S := by
    intro a x hx
    rw [Subgroup.mem_iSup_of_directed hdir] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, by rw [hfker] at hn ⊢; rw [← smul_pow', hn, smul_one]⟩
  have hSne : S ≠ ⊥ := by
    have hdvd : r ∣ Fintype.card K := by rw [Fintype.card_eq_nat_card]; exact hrK
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card r hdvd
    have hxS : x ∈ S := Subgroup.mem_iSup_of_mem 1 (by
      rw [hfker, pow_one]
      rw [← hx]; exact pow_orderOf_eq_one x)
    have hx1 : x ≠ 1 := by
      intro h
      have h1 : orderOf x = 1 := by rw [h]; exact orderOf_one
      rw [hx] at h1
      exact hr.ne_one h1
    intro hbot
    have : x ∈ (⊥ : Subgroup K) := hbot ▸ hxS
    rw [Subgroup.mem_bot] at this
    exact hx1 this
  have hStop : S = ⊤ := hirr S hSinv hSne
  have hpgroup : IsPGroup r K := by
    intro x
    have hxS : x ∈ S := by rw [hStop]; exact Subgroup.mem_top x
    rw [Subgroup.mem_iSup_of_directed hdir] at hxS
    obtain ⟨n, hn⟩ := hxS
    exact ⟨n, by rwa [hfker] at hn⟩
  intro x
  have hxr := Work.PGroup.pow_mem_frattini hr hpgroup x
  rw [hPhi] at hxr
  simpa using hxr

end Work.NormalComplement.AppVII
