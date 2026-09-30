import Mathlib
import Submission.Work.BMF.mr_direct.dupExtra_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cardinality of a fibre of `nnD` on `pSetD`

`dupExtra_fiber_card` bounds the number of triples `x' ∈ pSetD K P Q X` with `nnD x' = nnD x`
by `2 + 2 · #{p' ∈ primeImgD : p' ≠ x.1.2, p' ∣ x.2}`.

Writing `x = ⟨⟨j, p⟩, m⟩` (so `nnD x = p · m`), an element `x' = ⟨⟨j', p'⟩, m'⟩` of the fibre
satisfies `p' · m' = p · m` with `p'` prime, hence either `p' = p` or `p' ∣ m`. So the primes
`p'` occurring in the fibre lie in `{p} ∪ {p' ∈ primeImgD : p' ≠ p ∧ p' ∣ m}`. For each such
`p'`, the remaining freedom is the window index `j'` (the cofactor `m' = nnD x / p'` is forced
because `p' ≠ 0`), and a prime belongs to at most two prime windows, so each prime contributes
at most `2` elements. Multiplying gives the claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF
namespace mr_direct

open scoped BigOperators

/-- The second component of an element of `pSetD` is a prime. -/
lemma prime_of_mem_pSetD {K P Q X : ℝ} {x : Σ _ : Σ _ : ℕ, ℕ, ℕ}
    (hx : x ∈ Work.BMF.mrDirect.pSetD K P Q X) : x.1.2.Prime := by
  rw [Work.BMF.mr_direct.pSetD_eq_sigma, Finset.mem_sigma] at hx
  obtain ⟨hx1, -⟩ := hx
  rw [Work.BMF.mr_direct.pairSetD_eq, Finset.mem_sigma] at hx1
  exact (Work.BMF.mrDirect.mem_winPrimes.mp (Finset.mem_filter.mp hx1.2).1).1

/-- For a prime `b` occurring among the primes of `pSetD`, the elements `a` of `pSetD` with
`nnD a = nnD x` and `a.1.2 = b` number at most two: the cofactor is forced and only the
window index `a.1.1` is free, while a prime lies in at most two prime windows. -/
lemma dupExtra_fiber_le_two (K P Q X : ℝ) (hK : 1 ≤ K) (x : Σ _ : Σ _ : ℕ, ℕ, ℕ)
    {b : ℕ}
    (hb : b ∈ (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).image
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2))) :
    (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).filter
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2 = b)).card ≤ 2 := by
  rw [Finset.mem_image] at hb
  obtain ⟨a0, ha0, hbeq⟩ := hb
  subst hbeq
  have hbprime : a0.1.2.Prime :=
    prime_of_mem_pSetD (Finset.mem_filter.mp ha0).1
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  set S : Finset (Σ _ : Σ _ : ℕ, ℕ, ℕ) :=
    ((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).filter
          (fun a => a.1.2 = a0.1.2) with hS
  set T : Finset ℕ := (Finset.range (Work.BMF.mrDirect.jdex K a0.1.2 + 1)).filter
      (fun j => a0.1.2 ∈ Work.BMF.mrDirect.winPrimes K j) with hT
  have hinj : Set.InjOn (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.1) ↑S := by
    intro a ha a' ha' hg
    rw [Finset.mem_coe, hS, Finset.mem_filter] at ha ha'
    obtain ⟨haF, ha1⟩ := ha
    obtain ⟨ha'F, ha'1⟩ := ha'
    rw [Finset.mem_filter] at haF ha'F
    obtain ⟨-, haN⟩ := haF
    obtain ⟨-, ha'N⟩ := ha'F
    rcases a with ⟨⟨j, p⟩, m⟩
    rcases a' with ⟨⟨j', p'⟩, m'⟩
    have hgj : j = j' := hg
    have hp : p = a0.1.2 := ha1
    have hp' : p' = a0.1.2 := ha'1
    have hNm : p * m = x.1.2 * x.2 := haN
    have hNm' : p' * m' = x.1.2 * x.2 := ha'N
    have hm : m = m' := by
      have h : p * m = p' * m' := by rw [hNm, hNm']
      rw [hp, hp'] at h
      exact Nat.mul_left_cancel hbprime.pos h
    subst hgj
    subst hp
    subst hp'
    subst hm
    rfl
  have hsub : S.image (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.1) ⊆ T := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨a, ha, rfl⟩ := hj
    rw [hS, Finset.mem_filter] at ha
    obtain ⟨haF, ha1⟩ := ha
    obtain ⟨haPD, -⟩ := Finset.mem_filter.mp haF
    rw [Work.BMF.mr_direct.pSetD_eq_sigma, Finset.mem_sigma] at haPD
    obtain ⟨haP1, -⟩ := haPD
    rw [Work.BMF.mr_direct.pairSetD_eq, Finset.mem_sigma] at haP1
    have hwin : a0.1.2 ∈ Work.BMF.mrDirect.winPrimes K a.1.1 := by
      rw [← ha1]
      exact (Finset.mem_filter.mp haP1.2).1
    have hbnd := Work.BMF.mrDirect.win_idx_bounds hKpos hwin
    rw [hT, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hwin⟩
    have hle : a.1.1 ≤ Work.BMF.mrDirect.jdex K a0.1.2 := by
      rw [Work.BMF.mrDirect.jdex]
      exact Nat.le_floor hbnd.2
    omega
  calc S.card = (S.image (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.1)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ 2 := Work.BMF.mrDirect.card_winPrimes_le_two hKpos hbprime

/-- The primes occurring in the fibre of `nnD` over `nnD x` inside `pSetD` are either `x.1.2`
itself, or a prime of `primeImgD` distinct from `x.1.2` that divides `x.2`. -/
lemma dupExtra_image_subset (K P Q X : ℝ) (x : Σ _ : Σ _ : ℕ, ℕ, ℕ)
    (hx : x ∈ Work.BMF.mrDirect.pSetD K P Q X) :
    (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).image
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2))
      ⊆ insert x.1.2 ((Work.BMF.mr_direct.primeImgD K P Q X).filter
          (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)) := by
  intro b hb
  rw [Finset.mem_image] at hb
  obtain ⟨a, ha, hba⟩ := hb
  subst hba
  obtain ⟨haPD, haN⟩ := Finset.mem_filter.mp ha
  have hbprime : a.1.2.Prime := prime_of_mem_pSetD haPD
  have hxprime : x.1.2.Prime := prime_of_mem_pSetD hx
  rw [Finset.mem_insert]
  by_cases h : a.1.2 = x.1.2
  · exact Or.inl h
  · refine Or.inr ?_
    rw [Work.BMF.mr_direct.primeImgD, Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨a, haPD, rfl⟩, h, ?_⟩
    have hdvd : a.1.2 ∣ x.1.2 * x.2 := ⟨a.2, (show a.1.2 * a.2 = x.1.2 * x.2 from haN).symm⟩
    rcases (hbprime.dvd_mul).mp hdvd with h1 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hbprime hxprime).mp h1) h
    · exact h2

theorem dupExtra_fiber_card (K P Q X : ℝ) (hX : 1 ≤ X) (hK : 1 ≤ K) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∀ x ∈ Work.BMF.mrDirect.pSetD K P Q X,
      ((Work.BMF.mrDirect.pSetD K P Q X).filter
          (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).card
        ≤ 2 + 2 * ((Work.BMF.mr_direct.primeImgD K P Q X).filter
            (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card := by
  intro x hx
  have hfiber : ∀ b ∈ (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).image
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2)),
      (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).filter
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2 = b)).card ≤ 2 :=
    fun b hb => dupExtra_fiber_le_two K P Q X hK x hb
  have himg := dupExtra_image_subset K P Q X x hx
  have h1 : ((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).card ≤
      2 * (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).image
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2)).card :=
    Finset.card_le_mul_card_image _ 2 hfiber
  have h2 : (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).image
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2)).card ≤
      (insert x.1.2 ((Work.BMF.mr_direct.primeImgD K P Q X).filter
          (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2))).card := Finset.card_le_card himg
  have h3 : (insert x.1.2 ((Work.BMF.mr_direct.primeImgD K P Q X).filter
          (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2))).card ≤
      ((Work.BMF.mr_direct.primeImgD K P Q X).filter
          (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card + 1 :=
    Finset.card_insert_le _ _
  calc ((Work.BMF.mrDirect.pSetD K P Q X).filter
          (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).card
      ≤ 2 * (((Work.BMF.mrDirect.pSetD K P Q X).filter
        (fun x' => Work.BMF.mr_direct.nnD x' = Work.BMF.mr_direct.nnD x)).image
          (fun a : Σ _ : Σ _ : ℕ, ℕ, ℕ => a.1.2)).card := h1
    _ ≤ 2 * (insert x.1.2 ((Work.BMF.mr_direct.primeImgD K P Q X).filter
          (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2))).card := Nat.mul_le_mul_left 2 h2
    _ ≤ 2 * (((Work.BMF.mr_direct.primeImgD K P Q X).filter
          (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card + 1) := Nat.mul_le_mul_left 2 h3
    _ = 2 + 2 * ((Work.BMF.mr_direct.primeImgD K P Q X).filter
          (fun p' => p' ≠ x.1.2 ∧ p' ∣ x.2)).card := by ring

end mr_direct
end Work.BMF
