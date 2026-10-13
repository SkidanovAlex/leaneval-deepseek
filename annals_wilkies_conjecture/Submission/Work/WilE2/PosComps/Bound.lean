import Mathlib
import Submission.Work.WilE2.PosComps.Island
import Submission.Work.WilE2.E2_khovanskii_proved

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Topology Filter

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E

/-! ## The island bound: the number of islands is bounded.

Support module for `Work.WilE2.posComps_finite`.  Each island contains a critical point of
`Q + u·x` for a perturbation `u` that is small compared with the maxima of the islands in
question; those critical points are nondegenerate solutions of the square system
`∂ᵢQ + uᵢ = 0`, which `Work.WilE2.E2_khovanskii_proved` counts. -/

/-- A component of the positive set contained in the interior of the cube. -/
def IsIsland {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (C : Set (Fin k → ℝ)) : Prop :=
  (∃ x ∈ posSet c Q, connectedComponentIn (posSet c Q) x = C) ∧
    Disjoint C (frontier (cubeC k))

theorem island_posSet {k r : ℕ} {c : EAChain k r} {Q : EAPoly k r} {C : Set (Fin k → ℝ)}
    (hC : IsIsland c Q C) : C ⊆ posSet c Q := by
  obtain ⟨⟨x, hx, rfl⟩, -⟩ := hC
  exact connectedComponentIn_subset _ _

theorem island_interior {k r : ℕ} {c : EAChain k r} {Q : EAPoly k r} {C : Set (Fin k → ℝ)}
    (hC : IsIsland c Q C) : C ⊆ interior (cubeC k) := by
  obtain ⟨⟨x, hx, hxC⟩, hfr⟩ := hC
  rw [← hxC]
  exact island_subset_interior c Q (hxC.symm ▸ hfr)

theorem eaD_add_C {k r : ℕ} (c : EAChain k r) (i : Fin k) (P : EAPoly k r) (a : ℝ) :
    eaD c i (P + MvPolynomial.C a) = eaD c i P := by
  have h1 : ∀ s : Fin k ⊕ Fin r, MvPolynomial.pderiv s (P + MvPolynomial.C a)
      = MvPolynomial.pderiv s P := by
    intro s
    rw [map_add, MvPolynomial.pderiv_C, add_zero]
  simp only [eaD, h1]

/-- The degree of `P + C a` does not exceed the degree of `P`. -/
theorem atomDeg_add_C_le {k r : ℕ} (P : EAPoly k r) (a : ℝ) :
    atomDeg (P + MvPolynomial.C a) ≤ atomDeg P := by
  have h : (P + MvPolynomial.C a).totalDegree ≤ P.totalDegree := by
    refine (MvPolynomial.totalDegree_add P (MvPolynomial.C a)).trans ?_
    rw [MvPolynomial.totalDegree_C]
    exact max_le le_rfl (Nat.zero_le _)
  exact Nat.add_le_add_right h 1

/-- Monotonicity of polynomial evaluation on the naturals. -/
theorem eval_mono_nat {p : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k)

/-- **The number of islands is bounded.** -/
theorem island_bound {K r : ℕ} (c : EAChain K r) (Q : EAPoly K r) :
    ∃ B : ℕ, ∀ t : Finset (Set (Fin K → ℝ)),
      (∀ C ∈ t, IsIsland c Q C) → t.card ≤ B := by
  classical
  obtain ⟨p, hp⟩ := Work.WilE2.E2_khovanskii_proved (K + r)
  refine ⟨p.eval (∑ i, atomDeg (eaD c i Q)), fun t ht => ?_⟩
  rcases t.eq_empty_or_nonempty with rfl | htnon
  · simp
  -- a point witness for each island
  choose xC hxCs using fun C hC => (ht C hC).1
  -- the maximum of `eaEval c Q` on the closure of each island
  choose yC hyCs using fun C hC => exists_max_of_component c Q (hxCs C hC).1
  -- the minimum of the maxima
  set mvalF : Set (Fin K → ℝ) → ℝ := fun C =>
    if h : C ∈ t then eaEval c Q (yC C h) else 1 with hmvalF
  have hmvalF_pos : ∀ C ∈ t, 0 < mvalF C := by
    intro C hC
    rw [hmvalF]
    simp only [dif_pos hC]
    exact (hyCs C hC).2.2
  have hmvalF_eq : ∀ (C : Set (Fin K → ℝ)) (hC : C ∈ t), mvalF C = eaEval c Q (yC C hC) := by
    intro C hC
    rw [hmvalF]
    simp only [dif_pos hC]
  have hminmem : (t.image mvalF).Nonempty := t.image_nonempty.mpr htnon
  set m₀ : ℝ := (t.image mvalF).min' hminmem with hm₀
  have hm₀pos : 0 < m₀ := by
    rw [hm₀]
    exact (Finset.lt_min'_iff (t.image mvalF) hminmem).mpr fun _ hy => by
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hy
      exact hmvalF_pos C hC
  have hm₀le : ∀ (C : Set (Fin K → ℝ)) (hC : C ∈ t), m₀ ≤ eaEval c Q (yC C hC) := by
    intro C hC
    have h1 : m₀ ≤ mvalF C := by
      rw [hm₀]
      exact (Finset.isLeast_min' (t.image mvalF) hminmem).2
        (Finset.mem_image.mpr ⟨C, hC, rfl⟩)
    rwa [hmvalF_eq C hC] at h1
  -- the perturbation
  set ε : ℝ := m₀ / (2 * (K : ℝ) + 2) with hε
  have hεpos : 0 < ε := div_pos hm₀pos (by positivity)
  obtain ⟨u, hu, hugood⟩ := posComps_good_perturbation c Q ε hεpos
  have hsumK : (∑ i : Fin K, |u i|) ≤ (K : ℝ) * ε := by
    have h2 : (∑ i : Fin K, |u i|) ≤ ∑ _i : Fin K, ε :=
      Finset.sum_le_sum fun i _ => (hu i).le
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h2
  have hDpos : (0 : ℝ) < 2 * (K : ℝ) + 2 := by positivity
  have hεkey : 2 * ((K : ℝ) * ε) = (2 * (K : ℝ) / (2 * (K : ℝ) + 2)) * m₀ := by
    rw [hε]; ring
  have hfac : 2 * (K : ℝ) / (2 * (K : ℝ) + 2) < 1 := by
    rw [div_lt_one hDpos]
    linarith [Nat.cast_nonneg (α := ℝ) K]
  have hm₀K : 2 * ((K : ℝ) * ε) < m₀ := by
    rw [hεkey]; nlinarith [hm₀pos]
  have hsmall' : ∀ (C : Set (Fin K → ℝ)) (hC : C ∈ t), 2 * (∑ i, |u i|) < eaEval c Q (yC C hC) := by
    intro C hC
    have h1 : 2 * (∑ i : Fin K, |u i|) ≤ 2 * ((K : ℝ) * ε) := by linarith
    have h2 : m₀ ≤ eaEval c Q (yC C hC) := hm₀le C hC
    linarith
  -- the critical points
  have hcritex : ∀ (C : Set (Fin K → ℝ)) (hC : C ∈ t),
      ∃ z : Fin K → ℝ, z ∈ C ∧ ∀ i, eaEval c (eaD c i Q) z = - u i := by
    intro C hC
    obtain ⟨z, hz, hzcrit⟩ := exists_crit_of_island c Q (hxCs C hC).1 (hyCs C hC).1
      (hyCs C hC).2.1 (island_interior ((hxCs C hC).2.symm ▸ ht C hC)) u (hsmall' C hC)
    exact ⟨z, (hxCs C hC).2.symm ▸ hz, hzcrit⟩
  choose zC hzCs using hcritex
  have hdisj : ∀ (C : Set (Fin K → ℝ)) (hC : C ∈ t) (C' : Set (Fin K → ℝ)) (hC' : C' ∈ t),
      C ≠ C' → Disjoint C C' := by
    intro C hC C' hC' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    have h1 : z ∈ connectedComponentIn (posSet c Q) (xC C hC) := (hxCs C hC).2.symm ▸ hz
    have h2 : z ∈ connectedComponentIn (posSet c Q) (xC C' hC') := (hxCs C' hC').2.symm ▸ hz'
    have h3 : connectedComponentIn (posSet c Q) (xC C hC) = connectedComponentIn (posSet c Q) z :=
      connectedComponentIn_eq h1
    have h4 : connectedComponentIn (posSet c Q) (xC C' hC') = connectedComponentIn (posSet c Q) z :=
      connectedComponentIn_eq h2
    have h5 : connectedComponentIn (posSet c Q) (xC C hC) = C := (hxCs C hC).2
    have h6 : connectedComponentIn (posSet c Q) (xC C' hC') = C' := (hxCs C' hC').2
    exact hne ((h5.symm.trans (h3.trans h4.symm)).trans h6)
  -- the finite set of witnesses
  let zS : {C : Set (Fin K → ℝ) // C ∈ t} → Fin K → ℝ := fun C => zC C.1 C.2
  have hzS : ∀ C : {C : Set (Fin K → ℝ) // C ∈ t}, zS C ∈ C.1 ∧
      ∀ i, eaEval c (eaD c i Q) (zS C) = - u i := fun C => hzCs C.1 C.2
  have hinj : Set.InjOn zS ↑(t.attach) := by
    intro C _ C' _ heq
    by_contra hne
    have hmem : zS C ∈ C'.1 := heq.symm ▸ (hzS C').1
    have hne' : C.1 ≠ C'.1 := fun h => hne (Subtype.ext h)
    exact (Set.disjoint_left.mp (hdisj C.1 C.2 C'.1 C'.2 hne') (hzS C).1) hmem
  set s : Finset (Fin K → ℝ) := t.attach.image zS with hs
  have hscard : s.card = t.card := by
    rw [hs, Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hsE2 : ∀ x ∈ s, (∀ i, eaEval c (eaD c i Q + MvPolynomial.C (u i)) x = 0) ∧
      (Matrix.of fun i j => eaEval c (eaD c j (eaD c i Q + MvPolynomial.C (u i))) x).det ≠ 0 := by
    intro x hx
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp (hs ▸ hx)
    have hz := hzS C
    refine ⟨fun i => ?_, ?_⟩
    · show MvPolynomial.eval (Sum.elim (zS C) fun j => Real.exp (c.ell j (zS C)))
          (eaD c i Q + MvPolynomial.C (u i)) = 0
      rw [map_add, MvPolynomial.eval_C,
        show MvPolynomial.eval (Sum.elim (zS C) fun j => Real.exp (c.ell j (zS C)))
            (eaD c i Q) = eaEval c (eaD c i Q) (zS C) from rfl, hz.2 i]
      ring
    · have hdet := hugood (zS C) (hz.2)
      have hmat : (Matrix.of fun i j =>
            eaEval c (eaD c j (eaD c i Q + MvPolynomial.C (u i))) (zS C))
          = Matrix.of fun i j => eaEval c (eaD c j (eaD c i Q)) (zS C) := by
        ext i j
        simp only [Matrix.of_apply]
        rw [eaD_add_C]
      rw [hmat]
      exact hdet
  have hbound := hp K r c (fun i => eaD c i Q + MvPolynomial.C (u i)) s le_rfl hsE2
  rw [hscard] at hbound
  exact hbound.trans (eval_mono_nat (Finset.sum_le_sum fun i _ => atomDeg_add_C_le (eaD c i Q) (u i)))

/-- The set of islands is finite. -/
theorem islandSet_finite {K r : ℕ} (c : EAChain K r) (Q : EAPoly K r) :
    {C : Set (Fin K → ℝ) | IsIsland c Q C}.Finite := by
  classical
  obtain ⟨B, hB⟩ := island_bound c Q
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨t, ht, htf, htc⟩ := hinf.exists_subset_ncard_eq (B + 1)
  have hle : t.ncard ≤ B := by
    have h1 : htf.toFinset.card ≤ B := hB htf.toFinset (fun C hC =>
      ht (by rw [← htf.coe_toFinset]; exact hC))
    have h2 : t.ncard = htf.toFinset.card := Set.ncard_eq_toFinset_card t htf
    omega
  omega

end Work.WilE2
