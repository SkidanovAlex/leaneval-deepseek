import Mathlib

namespace Work.BourgainPlan.IonescuWainger

theorem torsion_kernel_classsum {Q : ℕ} (hQ : 1 ≤ Q) (K : ℤ → ℂ)
    (hK0 : ∀ j : ℤ, ¬ (Q : ℤ) ∣ j → K j = 0)
    (a : ℤ → ℂ) (s : Finset ℤ) (r : ℤ) (N : ℤ) :
    (∑ k ∈ s, a k * K ((Q : ℤ) * N + r - k))
      = ∑ M ∈ (s.filter (fun k => (Q : ℤ) ∣ (k - r))).image (fun k => (k - r) / (Q : ℤ)),
          a ((Q : ℤ) * M + r) * K ((Q : ℤ) * (N - M)) := by
  have _hQ := hQ
  -- Restrict the left-hand sum to the indices where `Q ∣ k - r`: off that set the
  -- kernel vanishes because `Q ∤ (Q*N + r - k)`.
  have hstep : (∑ k ∈ s, a k * K ((Q : ℤ) * N + r - k))
      = ∑ k ∈ s.filter (fun k => (Q : ℤ) ∣ (k - r)), a k * K ((Q : ℤ) * N + r - k) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hknot
    have hnp : ¬ (Q : ℤ) ∣ (k - r) := by
      intro hp
      exact hknot (by rw [Finset.mem_filter]; exact ⟨hk, hp⟩)
    have hK0k : K ((Q : ℤ) * N + r - k) = 0 := by
      apply hK0
      intro hd
      apply hnp
      have h1 : (Q : ℤ) ∣ (Q : ℤ) * N := dvd_mul_right _ _
      have h2 : (Q : ℤ) ∣ r - k := by
        have h := Int.dvd_sub hd h1
        convert h using 1
        ring
      have h3 : (Q : ℤ) ∣ k - r := by
        have := (Int.dvd_neg (a := (Q : ℤ)) (b := r - k)).mpr h2
        simpa using this
      exact h3
    rw [hK0k, mul_zero]
  rw [hstep]
  -- On the restricted set the map `k ↦ (k - r)/Q` is injective, so reindex the RHS.
  have hinj : Set.InjOn (fun k : ℤ => (k - r) / (Q : ℤ))
      ↑(s.filter (fun k => (Q : ℤ) ∣ (k - r))) := by
    intro x hx y hy heq
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    have hxx : x - r = (Q : ℤ) * ((x - r) / (Q : ℤ)) := (Int.mul_ediv_cancel' hx.2).symm
    have hyy : y - r = (Q : ℤ) * ((y - r) / (Q : ℤ)) := (Int.mul_ediv_cancel' hy.2).symm
    simp only [] at heq
    have hxy : x - r = y - r := by rw [hxx, hyy, heq]
    omega
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_filter] at hk
  obtain ⟨hks, hkdvd⟩ := hk
  have h1 : (Q : ℤ) * ((k - r) / (Q : ℤ)) + r = k := by
    have := Int.mul_ediv_cancel' hkdvd
    omega
  have harg : (Q : ℤ) * N + r - k = (Q : ℤ) * (N - (k - r) / (Q : ℤ)) := by
    conv_lhs => rw [← h1]
    ring
  rw [h1, harg]

end Work.BourgainPlan.IonescuWainger
