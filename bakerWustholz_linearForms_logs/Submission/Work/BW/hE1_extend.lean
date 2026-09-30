import Mathlib
import Submission.Work.BW.DefsMP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `liftIdx σ` is injective whenever `σ` is. -/
lemma liftIdx_injective {N r : ℕ} {σ : Fin N → Fin r} (hσ : Function.Injective σ) :
    Function.Injective (liftIdx σ) := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => rfl
    | succ j => exact absurd hab.symm (Fin.succ_ne_zero _)
  | succ i =>
    induction b using Fin.cases with
    | zero => exact absurd hab (Fin.succ_ne_zero _)
    | succ j =>
      simp only [liftIdx, Fin.cases_succ, Fin.succ_inj] at hab
      rw [hσ hab]

theorem hE1_extend {r N : ℕ} (σ : Fin N → Fin r) (hσ : StrictMono σ) (𝒟 : Fin (r + 1) → ℝ)
    (Sq Tq : ℕ → ℕ) (m : ℕ) (hm : m < r)
    (hE1 : ∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, 𝒟 i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (e : Fin (N + 1) → ℕ) (he : ∀ i, e i ≤ 1) (hsum : ∑ i, e i = m + 1) :
    ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, (𝒟 (liftIdx σ i)) ^ e i <
      ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ) := by
  have hlinj : Function.Injective (liftIdx σ) := liftIdx_injective hσ.injective
  -- the support of `e`, and its image under `liftIdx σ`
  set s : Finset (Fin (N + 1)) := Finset.univ.filter (fun i => e i = 1) with hs
  set S : Finset (Fin (r + 1)) := s.image (liftIdx σ) with hS
  -- the pushed-forward exponent vector
  set e' : Fin (r + 1) → ℕ := (fun j => if j ∈ S then 1 else 0) with he'
  have hfilter : Finset.univ.filter (fun j : Fin (r + 1) => j ∈ S) = S := by
    ext j; simp
  have he'1 : ∀ j, e' j ≤ 1 := by
    intro j
    by_cases h : j ∈ S <;> simp [he', h]
  have hsum' : ∑ j, e' j = m + 1 := by
    rw [he']
    rw [← Finset.card_filter (fun j : Fin (r + 1) => j ∈ S) Finset.univ]
    rw [hfilter, hS, Finset.card_image_of_injective s hlinj, hs, Finset.card_filter]
    rw [show (∑ i ∈ Finset.univ, (if e i = 1 then (1:ℕ) else 0)) = ∑ i, e i from
        Finset.sum_congr rfl (fun i _ => by have hi := he i; split <;> omega)]
    exact hsum
  have hprod : ∏ j, 𝒟 j ^ e' j = ∏ i, (𝒟 (liftIdx σ i)) ^ e i := by
    have step1 : ∏ j, 𝒟 j ^ e' j = ∏ j ∈ S, 𝒟 j := by
      rw [he']
      rw [show (∏ j : Fin (r+1), 𝒟 j ^ (if j ∈ S then 1 else 0))
            = ∏ j ∈ Finset.univ, (if j ∈ S then 𝒟 j else 1) from
          Finset.prod_congr rfl (fun j _ => by by_cases h : j ∈ S <;> simp [h])]
      rw [← Finset.prod_filter (fun j : Fin (r+1) => j ∈ S) 𝒟]
      rw [hfilter]
    have step2 : ∏ j ∈ S, 𝒟 j = ∏ i ∈ s, 𝒟 (liftIdx σ i) := by
      rw [hS]
      exact Finset.prod_image (fun a _ b _ h => hlinj h)
    have step3 : ∏ i ∈ s, 𝒟 (liftIdx σ i) = ∏ i, (𝒟 (liftIdx σ i)) ^ e i := by
      rw [show (∏ i ∈ s, 𝒟 (liftIdx σ i)) = ∏ i ∈ s, (𝒟 (liftIdx σ i)) ^ e i from
          Finset.prod_congr rfl (fun i hi => by
            have hi1 : e i = 1 := by
              have hmem := hi
              rw [hs] at hmem
              exact (Finset.mem_filter.mp hmem).2
            rw [hi1, pow_one])]
      exact Finset.prod_subset (Finset.subset_univ s) (fun x _ hx => by
        have hx1 : e x ≠ 1 := by
          intro hx1
          exact hx (by rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx1⟩)
        have hx0 : e x = 0 := by have hi := he x; omega
        rw [hx0, pow_zero])
    rw [step1, step2, step3]
  have key := hE1 m hm e' he'1 hsum'
  rwa [hprod] at key

end Work.BW
