import Mathlib
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

/-- Bender 1981, §4 (1) (p. 224): the single-commutator piece `[⟨s⟩, U ⊓ M] ≤ K` of
`K = [S ∩ E, U ∩ M]`.

Holding `P := U ⊓ M`, an involution `s` normalizing `P` (here `s ∈ S` and `S ≤ N(P)`), and
`K = I_P(s) = {x ∈ P | s x s⁻¹ = x⁻¹}`, every commutator `⁅s, n⁆ = s n s⁻¹ n⁻¹` (`n ∈ P`) lies
in `K`:

* `s n s⁻¹ ∈ P` (as `s ∈ N(P)`) and `n⁻¹ ∈ P`, so `⁅s, n⁆ ∈ P`;
* `s · ⁅s, n⁆ · s⁻¹ = ⁅s, n⁆⁻¹` because `s² = 1`: writing `a = s n s⁻¹`, one has
  `⁅s, n⁆ = a n⁻¹` and `s (a n⁻¹) s⁻¹ = (s a s⁻¹) (s n s⁻¹)⁻¹ = n a⁻¹ = (a n⁻¹)⁻¹`. -/
theorem Case2SingleCommutator {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (h : Work.GW2.Case2Ctx B)
    (hS : (B.S : Subgroup G) ≤ Subgroup.normalizer ((B.U ⊓ h.D.M : Subgroup G) : Set G)) :
    ∀ n ∈ B.U ⊓ h.D.M, h.D.s * n * h.D.s⁻¹ * n⁻¹ ∈ h.D.K := by
  intro n hn
  -- `s ∈ S ≤ N(U ⊓ M)`.
  have hsS : h.D.s ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp h.D.s_mem).1
  have hsN : h.D.s ∈ Subgroup.normalizer ((B.U ⊓ h.D.M : Subgroup G) : Set G) := hS hsS
  -- `s` is an involution.
  have hs2 : h.D.s * h.D.s = 1 := by
    have h1 : h.D.s ^ 2 = 1 := by rw [← h.D.s_order]; exact pow_orderOf_eq_one h.D.s
    simpa [pow_two] using h1
  have hs_inv : h.D.s⁻¹ = h.D.s := inv_eq_of_mul_eq_one_right hs2
  -- Identify `K` with the inversion set `I_{U⊓M}(s)`.
  rw [← SetLike.mem_coe, h.D.K_def]
  simp only [Work.GW2.invSet, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · -- `s n s⁻¹ n⁻¹ ∈ U ⊓ M`: conjugate `s n s⁻¹` times `n⁻¹`.
    have h1 : h.D.s * n * h.D.s⁻¹ ∈ B.U ⊓ h.D.M :=
      (Subgroup.mem_normalizer_iff.mp hsN n).mp hn
    exact mul_mem h1 (inv_mem hn)
  · -- `s · (s n s⁻¹ n⁻¹) · s⁻¹ = (s n s⁻¹ n⁻¹)⁻¹`, using `s² = 1`.
    have h1 : h.D.s * (h.D.s * n * h.D.s⁻¹ * n⁻¹) * h.D.s⁻¹
          = (h.D.s * h.D.s) * n * h.D.s⁻¹ * n⁻¹ * h.D.s⁻¹ := by group
    have h2 : (h.D.s * n * h.D.s⁻¹ * n⁻¹)⁻¹ = n * h.D.s * n⁻¹ * h.D.s⁻¹ := by group
    rw [h1, hs2, one_mul, h2, hs_inv]

end Work.CORE4
