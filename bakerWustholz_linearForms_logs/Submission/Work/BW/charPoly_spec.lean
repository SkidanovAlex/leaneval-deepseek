import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.charPoly_homPiece
import Submission.Work.BW.charPoly_zpow_prod
import Submission.Work.BW.charPoly_algebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-! # Existence of Philippon's characteristic polynomial class

For every row `j` of an integral matrix `M` we produce an element `F` of the ideal
`subIdeal N ρ ε M` (the multihomogeneous ideal of the closure of `G' = G_a^ε × ker 𝒵`) whose
value at the cone point `conePt N y` of an affine point `y ∈ G` is exactly

`(∏ᵢ yᵢ^{|M_{ji}|}) · ((∏ᵢ yᵢ^{M_{ji}}) − 1)`.

Writing `pᵢ = (M_{ji}).toNat` and `qᵢ = (−M_{ji}).toNat` momentarily, the two monomials

`U = ∏ᵢ X_{(i+1,1)}^{pᵢ} X_{(i+1,0)}^{qᵢ}`,  `V = ∏ᵢ X_{(i+1,1)}^{qᵢ} X_{(i+1,0)}^{pᵢ}`

are multihomogeneous of the same multidegree `∑ᵢ (pᵢ+qᵢ) e_{i+1}`, and

`U − V` vanishes at `conePt N y` for every `y ∈ G'` (there `∏ᵢ yᵢ^{M_{ji}} = 1`, i.e.
`∏ᵢ yᵢ^{pᵢ} = ∏ᵢ yᵢ^{qᵢ}`).  Hence `G := U − V ∈ subIdeal N ρ ε M`, and since `subIdeal` is
an ideal, also `F := (∏ᵢ X_{(i+1,1)}^{pᵢ}) · G ∈ subIdeal N ρ ε M`.  Its value at `conePt N y` is

`(∏ᵢ yᵢ^{pᵢ}) · ((∏ᵢ yᵢ^{pᵢ}) − (∏ᵢ yᵢ^{qᵢ}))`,

which (for `yᵢ ≠ 0`) is the asserted expression, by `charPoly_algebra`. -/

theorem charPoly_spec {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (j : Fin ρ) :
    ∃ F : MR N, F ∈ subIdeal N ρ ε M ∧ ∀ y : Fin (N + 1) → ℂ, InG y →
      MvPolynomial.eval (conePt N y) F =
        (∏ i : Fin N, (y i.succ) ^ ((M j i).natAbs)) *
          ((∏ i : Fin N, (y i.succ) ^ (M j i)) - 1) := by
  -- `U` and `V`: the two monomials whose difference vanishes on `G'`.
  set U : MR N := ∏ i : Fin N,
      (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat)
      * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((-(M j i)).toNat) with hU
  set V : MR N := ∏ i : Fin N,
      (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((-(M j i)).toNat)
      * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat) with hV
  -- `P1 = ∏ᵢ X_{(i+1,1)}^{pᵢ}`, the multiplier that turns `U - V` into the wanted value.
  set P1 : MR N := ∏ i : Fin N,
      (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat) with hP1
  set d : Fin (N+1) →₀ ℕ :=
      ∑ i : Fin N, ((M j i).toNat + (-(M j i)).toNat) • (Finsupp.single i.succ 1 : Fin (N+1) →₀ ℕ)
    with hd
  set G : MR N := U - V with hG
  -- Multihomogeneity of a monomial `∏ᵢ X_{(i+1,1)}^{aᵢ} X_{(i+1,0)}^{bᵢ}`.
  have key : ∀ (a b : Fin N → ℕ),
      (∏ i : Fin N, (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ (a i)
        * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N+1) × Fin 2)) ^ (b i)) ∈
      homPiece N (∑ i : Fin N, (a i + b i) • (Finsupp.single i.succ 1 : Fin (N+1) →₀ ℕ)) := by
    intro a b
    exact (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ
      (fun v : Fin (N+1) × Fin 2 => Finsupp.single v.1 1) _ _).mpr (charPoly_homPiece a b)
  have hUdeg : U ∈ homPiece N d := by
    rw [hU, hd]
    exact key (fun i => (M j i).toNat) (fun i => (-(M j i)).toNat)
  have hVdeg : V ∈ homPiece N d := by
    rw [hV, hd]
    have h := key (fun i => (-(M j i)).toNat) (fun i => (M j i).toNat)
    rw [show (∑ i : Fin N, ((-(M j i)).toNat + (M j i).toNat) •
              (Finsupp.single i.succ 1 : Fin (N+1) →₀ ℕ))
          = (∑ i : Fin N, ((M j i).toNat + (-(M j i)).toNat) •
              (Finsupp.single i.succ 1 : Fin (N+1) →₀ ℕ)) from
          Finset.sum_congr rfl (fun i _ => congrArg
            (fun t : ℕ => t • (Finsupp.single i.succ 1 : Fin (N+1) →₀ ℕ))
            (add_comm ((M j i).toNat) ((-(M j i)).toNat)).symm)] at h
    exact h
  have hGdeg : G ∈ homPiece N d := by
    rw [hG]; exact Submodule.sub_mem _ hUdeg hVdeg
  -- `U - V` vanishes at the cone point of every point of `G'`.
  have hGvan : ∀ y, InSub N ρ ε M y → MvPolynomial.eval (conePt N y) G = 0 := by
    intro y hy
    have hz : ∀ i : Fin N, y i.succ ≠ 0 := hy.2.1
    have h1 : (∏ i : Fin N, y i.succ ^ ((M j i).toNat))
        * (∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat))⁻¹ = 1 := by
      rw [← charPoly_zpow_prod (fun i => y i.succ) (fun i => M j i) hz]
      exact hy.2.2 j
    have hB : (∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hz i))
    have hpq : (∏ i : Fin N, y i.succ ^ ((M j i).toNat))
        = (∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat)) := by
      have h2 : (∏ i : Fin N, y i.succ ^ ((M j i).toNat))
            * (∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat))⁻¹
            * (∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat))
          = 1 * (∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat)) := by
        rw [h1]
      rwa [mul_assoc, inv_mul_cancel₀ hB, mul_one, one_mul] at h2
    rw [hG, hU, hV, map_sub]
    rw [show MvPolynomial.eval (conePt N y) (∏ i : Fin N,
          (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat)
          * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((-(M j i)).toNat))
        = ∏ i : Fin N, y i.succ ^ ((M j i).toNat) from by simp [conePt]]
    rw [show MvPolynomial.eval (conePt N y) (∏ i : Fin N,
          (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((-(M j i)).toNat)
          * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat))
        = ∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat) from by simp [conePt]]
    rw [hpq, sub_self]
  have hGmem : G ∈ subIdeal N ρ ε M :=
    Ideal.subset_span (show G ∈ {F : MR N | (∃ d, F ∈ homPiece N d) ∧
        ∀ y, InSub N ρ ε M y → MvPolynomial.eval (conePt N y) F = 0} from ⟨⟨d, hGdeg⟩, hGvan⟩)
  refine ⟨P1 * G, ?_, ?_⟩
  · exact Ideal.mul_mem_left _ _ hGmem
  · intro y hy
    rw [hP1, hG, hU, hV, map_mul, map_sub]
    rw [show MvPolynomial.eval (conePt N y) (∏ i : Fin N,
          (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat))
        = ∏ i : Fin N, y i.succ ^ ((M j i).toNat) from by simp [conePt]]
    rw [show MvPolynomial.eval (conePt N y) (∏ i : Fin N,
          (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat)
          * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((-(M j i)).toNat))
        = ∏ i : Fin N, y i.succ ^ ((M j i).toNat) from by simp [conePt]]
    rw [show MvPolynomial.eval (conePt N y) (∏ i : Fin N,
          (MvPolynomial.X ((i.succ, (1 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((-(M j i)).toNat)
          * (MvPolynomial.X ((i.succ, (0 : Fin 2)) : Fin (N+1) × Fin 2)) ^ ((M j i).toNat))
        = ∏ i : Fin N, y i.succ ^ ((-(M j i)).toNat) from by simp [conePt]]
    exact charPoly_algebra (fun i => y i.succ) (fun i => M j i) hy

end Work.BW
