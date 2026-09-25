import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_add_mem
import Submission.Work.BourgainPlan.IonescuWainger.sigmaSubA_add
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

namespace Work.BourgainPlan.IonescuWainger

/-- **The Chinese-remainder / direct-sum decomposition of `Σ_{A ∪ B}`** (the `Σ_·` case of Tao's
(sigma), arXiv:2008.05066, §4).

Let `S` be a finite set of pairwise coprime integers `≥ 2`, and let `A, B ⊆ S` be disjoint.  Then
every point of `Σ_{A ∪ B}` (a point of the circle `𝕋 = ℝ/ℤ` of *exact* denominator `Q_{A ∪ B}`,
`Q_C = ∏_{q ∈ C} q`) has a *unique* decomposition `x = α + β` with `α ∈ Σ_A` and `β ∈ Σ_B`.

This refines the sumset inclusion `Σ_A + Σ_B ⊆ Σ_{A ∪ B}` (already proved as `sigmaA_add_mem`) to an
equality, and it is exactly what is needed to expand `f_{Σ_{A₀ ∪ A_i}} = Σ_{α ∈ Σ_{A_i}}
f_{α + Σ_{A₀}}` in the proof of Tao's Theorem `ortho-apply`(i).  Uniqueness is
`eq_zero_of_mem_sigmaSubA_inter` (`α - α' = β' - β ∈ Σ_{⊆ A} ∩ Σ_{⊆ B} = {0}` since `Q_A`, `Q_B`
are coprime); existence is the Chinese remainder theorem, or equivalently the cardinality count
`|Σ_A| · |Σ_B| = φ(Q_A) φ(Q_B) = φ(Q_{A∪B}) = |Σ_{A∪B}|` (both sides being the numbers of units). -/
theorem sigmaA_exists_unique_add {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (hdisj : Disjoint A B) {x : Circle}
    (hx : x ∈ sigmaA (A ∪ B)) :
    ∃! p : Circle × Circle, p.1 ∈ sigmaA A ∧ p.2 ∈ sigmaA B ∧ p.1 + p.2 = x := by
  classical
  -- `Σ_{⊆ C}` is closed under subtraction: it is (the range of) a group homomorphism.
  have hsub : ∀ {C : Finset ℕ} {y z : Circle}, y ∈ sigmaSubA C → z ∈ sigmaSubA C →
      y - z ∈ sigmaSubA C := by
    intro C y z hy hz
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    refine ⟨a - b, ?_⟩
    rw [arcPt, arcPt, arcPt, ← AddCircle.coe_sub]
    congr 1
    push_cast
    rw [sub_div]
  have hA' : ∀ q ∈ A, 2 ≤ q := fun q hq => h2 q (hA hq)
  have hB' : ∀ q ∈ B, 2 ≤ q := fun q hq => h2 q (hB hq)
  have hQne : QA A ≠ 0 := QA_ne_zero_of_two_le hA'
  have hRne : QA B ≠ 0 := QA_ne_zero_of_two_le hB'
  -- `Q_A` and `Q_B` are coprime
  have hcop : Nat.Coprime (QA A) (QA B) := by
    rw [QA, QA]
    exact Nat.Coprime.prod_left fun q hq => Nat.Coprime.prod_right fun q' hq' =>
      hS q (hA hq) q' (hB hq') (fun he => Finset.disjoint_left.mp hdisj hq (he ▸ hq'))
  have hQU : QA (A ∪ B) = QA A * QA B := QA_union hdisj
  -- `x = c / (Q_A Q_B)` with `gcd(c, Q_A Q_B) = 1`
  obtain ⟨c, hc, hxc⟩ := hx
  rw [hQU] at hc hxc
  -- Bézout: `u Q_A + v Q_B = 1`
  obtain ⟨u, v, huv⟩ := hcop.isCoprime
  have hvQ' : (QA B : ℤ) * v + u * (QA A : ℤ) = 1 := by rw [← huv]; ring
  have huR' : (QA A : ℤ) * u + v * (QA B : ℤ) = 1 := by rw [← huv]; ring
  -- Bézout also shows `v` is coprime to `Q_A` and `u` to `Q_B`
  have hvQ : Nat.Coprime v.natAbs (QA A) := by
    have his : IsCoprime v (QA A : ℤ) := ⟨(QA B : ℤ), u, hvQ'⟩
    have := Int.isCoprime_iff_nat_coprime.mp his
    simpa using this
  have huR : Nat.Coprime u.natAbs (QA B) := by
    have his : IsCoprime u (QA B : ℤ) := ⟨(QA A : ℤ), v, huR'⟩
    have := Int.isCoprime_iff_nat_coprime.mp his
    simpa using this
  -- `c` is coprime to `Q_A` and to `Q_B`
  have hcQ : Nat.Coprime c.natAbs (QA A) := hc.coprime_dvd_right (dvd_mul_right (QA A) (QA B))
  have hcR : Nat.Coprime c.natAbs (QA B) := hc.coprime_dvd_right (dvd_mul_left (QA B) (QA A))
  -- the two summands `α = c v / Q_A ∈ Σ_A`, `β = c u / Q_B ∈ Σ_B`
  have hα : arcPt (QA A) (c * v) ∈ sigmaA A := by
    refine ⟨c * v, ?_, rfl⟩
    rw [Int.natAbs_mul]
    exact Nat.Coprime.mul_left hcQ hvQ
  have hβ : arcPt (QA B) (c * u) ∈ sigmaA B := by
    refine ⟨c * u, ?_, rfl⟩
    rw [Int.natAbs_mul]
    exact Nat.Coprime.mul_left hcR huR
  -- and they sum to `x`: `(c v) Q_B + (c u) Q_A = c (v Q_B + u Q_A) = c`
  have hsum : arcPt (QA A) (c * v) + arcPt (QA B) (c * u) = x := by
    rw [arcPt_add_denom hQne hRne, hxc]
    congr 1
    calc (c * v) * (QA B : ℤ) + (c * u) * (QA A : ℤ)
        = c * (v * (QA B : ℤ) + u * (QA A : ℤ)) := by ring
      _ = c * 1 := by rw [← hvQ', mul_comm (QA B : ℤ) v]
      _ = c := by ring
  refine ⟨(arcPt (QA A) (c * v), arcPt (QA B) (c * u)), ⟨hα, hβ, hsum⟩, ?_⟩
  -- uniqueness: `γ - α = β - δ ∈ Σ_{⊆ A} ∩ Σ_{⊆ B} = {0}`
  rintro ⟨γ, δ⟩ ⟨hγA, hδB, hsum'⟩
  have hkey : γ - arcPt (QA A) (c * v) = arcPt (QA B) (c * u) - δ := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (arcPt (QA B) (c * u)) (arcPt (QA A) (c * v))]
    exact hsum'.trans hsum.symm
  have hmemA : γ - arcPt (QA A) (c * v) ∈ sigmaSubA A :=
    hsub (sigmaA_subset_sigmaSubA A hγA) (sigmaA_subset_sigmaSubA A hα)
  have hmemB : γ - arcPt (QA A) (c * v) ∈ sigmaSubA B := by
    rw [hkey]
    exact hsub (sigmaA_subset_sigmaSubA B hβ) (sigmaA_subset_sigmaSubA B hδB)
  have hzero := eq_zero_of_mem_sigmaSubA_inter h2 hA hB hcop hmemA hmemB
  have hγ : γ = arcPt (QA A) (c * v) := sub_eq_zero.mp hzero
  have hδ : δ = arcPt (QA B) (c * u) := by
    have hh : arcPt (QA B) (c * u) - δ = 0 := by rw [← hkey]; exact hzero
    exact (sub_eq_zero.mp hh).symm
  rw [hγ, hδ]

end Work.BourgainPlan.IonescuWainger
