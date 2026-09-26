/-
# Polynomial growth of the CKMRV cusp atoms on the tile `E = KEpsilon`

This file proves `Work.Asymptotics.E_atom_poly`: every one of the "atoms" out of which the
CKMRV kernels are assembled — the Eisenstein series `E₂, E₄, E₆, E₈, E₁₀, E₁₄`, the `S`-slash
`E₂|₂S`, the theta powers `U, V, W`, the combinations `ξ₂, ξ₄`, the two normalised logarithms
`𝓛, 𝓛_S`, the basis vectors `φ⃗, φ̃⃗, ψ⃗, ψ̃⃗` and their components — is bounded on the cusp-`0`
tile `E = Work.Asymptotics.KEpsilon` by a fixed power `(scale w) ^ N` of the scale
`scale w = 1 + (im w)⁻¹ + |w|`, with a single constant `C` and a single exponent `N` for all
of them.

The mathematical input is the CKMRV Lemma "HCmoderategrowthPslashed" (Section 4.1): the class
`𝒫 = Work.Kernels.InP` of holomorphic functions of moderate growth is closed under `+`, `*`,
powers and the slash action of `SL(2,ℤ)`, and it contains `E₂` (`Work.Kernels.ClassicalFacts`)
and the four Jacobi theta functions.  Since moderate growth on all of `ℍ` is precisely a bound
`‖F τ‖ ≤ α * (scale τ) ^ N`, restricting to `E ⊆ ℍ` gives the required bound.

The only bookkeeping is that the statement asks for a *single* pair `(C, N)` valid for all
atoms at once.  This is done by `E_atom_common_bound`, which combines the finitely many
witnesses by summing them: an index family `Fin 26` whose members are the 14 scalar atoms and
the 12 components of the four basis vectors, and a `Finset`-sum over the witnesses.

## Main result

* `Work.Asymptotics.E_atom_poly` : `∃ C N, 0 < C ∧ 0 ≤ N` and every atom `F` of the CKMRV
  construction satisfies `‖F w‖ ≤ C * (scale w) ^ N` for `w ∈ E`.
-/
import Mathlib
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.psi_InP
import Submission.Work.Kernels.ClassicalFacts.E2Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E4Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.E6Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta00Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta10Fun_mem_InP

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

/-! ## From moderate growth to a `scale`-power bound -/

/-- Moderate growth on `S` is the same thing as a bound `‖F w‖ ≤ C * (scale w) ^ N` with
`0 < C` and `0 ≤ N`. -/
lemma E_atom_moderate_scale {S : Set ℍ} {F : ℍ → ℂ}
    (hF : Work.Kernels.ModerateGrowthOn S F) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ w ∈ S, ‖F w‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨α, N, hα, hN, hb⟩ := (Work.Kernels.moderateGrowthOn_iff_scale S F).mp hF
  refine ⟨α + 1, N, by linarith, hN, fun w hw => ?_⟩
  have h2 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos w)) N
  exact le_trans (hb w hw) (mul_le_mul_of_nonneg_right (by linarith) h2)

/-- The same, for a function of moderate growth on all of `ℍ`, restricted to the tile `E`. -/
lemma E_atom_KEpsilon_bound {F : ℍ → ℂ}
    (hF : Work.Kernels.ModerateGrowthOn Set.univ F) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ w : ℍ, w ∈ KEpsilon → ‖F w‖ ≤ C * (Work.Kernels.scale w) ^ N :=
  E_atom_moderate_scale (Work.Kernels.ModerateGrowthOn.mono hF (Set.subset_univ _))

/-- The coordinate function `w ↦ w` has moderate growth, with `‖w‖ ≤ scale w`. -/
lemma E_atom_coe_moderate :
    Work.Kernels.ModerateGrowthOn Set.univ (fun w : ℍ => (w : ℂ)) := by
  rw [Work.Kernels.moderateGrowthOn_iff_scale]
  exact ⟨1, 1, by norm_num, by norm_num, fun w _ => by
    rw [Real.rpow_one, one_mul]; exact Work.Kernels.coe_norm_le_scale w⟩

/-- **Merging finitely many `scale`-power bounds.**  If each member `F i` of a finite family of
functions satisfies a bound `‖F i w‖ ≤ C i * (scale w) ^ (N i)` on `S`, then a *single* pair
`(C, N)` works for all of them simultaneously: take `N` to be the sum of the exponents and `C`
the sum of the constants plus one. -/
lemma E_atom_common_bound {ι : Type*} [Fintype ι] {S : Set ℍ} (F : ι → ℍ → ℂ)
    (h : ∀ i, ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ w ∈ S, ‖F i w‖ ≤ C * (Work.Kernels.scale w) ^ N) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ i (w : ℍ), w ∈ S → ‖F i w‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  classical
  choose C N hC hN hb using h
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  refine ⟨(∑ i, C i) + 1, ∑ i, N i, by linarith, Finset.sum_nonneg fun i _ => hN i, ?_⟩
  intro i w hw
  have hCi : C i ≤ (∑ j, C j) + 1 := by
    have := Finset.single_le_sum (f := C) (fun j _ => (hC j).le) (Finset.mem_univ i)
    linarith
  have hNi : N i ≤ ∑ j, N j :=
    Finset.single_le_sum (f := N) (fun j _ => hN j) (Finset.mem_univ i)
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hsN : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (N i) :=
    Real.rpow_nonneg (le_trans zero_le_one hs1) _
  have hpow : (Work.Kernels.scale w) ^ (N i) ≤ (Work.Kernels.scale w) ^ (∑ j, N j) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hNi
  calc ‖F i w‖ ≤ C i * (Work.Kernels.scale w) ^ (N i) := hb i w hw
    _ ≤ ((∑ j, C j) + 1) * (Work.Kernels.scale w) ^ (∑ j, N j) :=
        mul_le_mul hCi hpow hsN (by linarith)

/-! ## The atoms -/

/-- **Polynomial boundedness of all the CKMRV atoms on the cusp-`0` tile `E`.**

There are positive `C`, nonnegative `N` such that the Eisenstein series `E₂, E₄, E₆, E₈, E₁₀,
E₁₄`, the slash `E₂|₂S`, the theta powers `U = θ₀₀⁴, V = θ₁₀⁴, W = θ₀₁⁴`, the combinations
`ξ₂ = U + W`, `ξ₄ = U² + W² - 2V²`, the normalised logarithms `𝓛, 𝓛_S` and all components of
the basis vectors `φ⃗, φ̃⃗, ψ⃗, ψ̃⃗` are bounded by `C * (scale w) ^ N` on `E = KEpsilon`. -/
theorem E_atom_poly (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.E2Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.E4Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.E6Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.E8Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.E10Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.E14Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.E2S w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.UFun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.VFun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.WFun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.xi2Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖Work.Kernels.xi4Fun w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖ℓ.L w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ‖ℓ.L_S w‖ ≤ C * (Work.Kernels.scale w) ^ N) ∧
      (∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ∀ i : Fin 3,
        ‖Work.Kernels.phiVec w i‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.phitVec w i‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.psiVec ℓ w i‖ ≤ C * (Work.Kernels.scale w) ^ N ∧
        ‖Work.Kernels.psitVec ℓ w i‖ ≤ C * (Work.Kernels.scale w) ^ N) := by
  -- moderate growth of the basic atoms on all of `ℍ`
  have hE2m : Work.Kernels.ModerateGrowthOn Set.univ Work.Kernels.E2Fun :=
    Work.Kernels.ClassicalFacts.E2Fun_mem_InP.2
  have hE4m : Work.Kernels.ModerateGrowthOn Set.univ Work.Kernels.E4Fun :=
    Work.Kernels.ClassicalFacts.E4Fun_mem_InP.2
  have hE6m : Work.Kernels.ModerateGrowthOn Set.univ Work.Kernels.E6Fun :=
    Work.Kernels.ClassicalFacts.E6Fun_mem_InP.2
  have hUm : Work.Kernels.ModerateGrowthOn Set.univ Work.Kernels.UFun :=
    (Work.Kernels.ModerateGrowthOn.pow
      Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.2 4)
  have hVm : Work.Kernels.ModerateGrowthOn Set.univ Work.Kernels.VFun :=
    (Work.Kernels.ModerateGrowthOn.pow
      Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.2 4)
  have hWm : Work.Kernels.ModerateGrowthOn Set.univ Work.Kernels.WFun :=
    (Work.Kernels.ModerateGrowthOn.pow
      Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.2 4)
  have hE2Sm : Work.Kernels.ModerateGrowthOn Set.univ Work.Kernels.E2S :=
    (Work.Kernels.InP.slash Work.Kernels.ClassicalFacts.E2Fun_mem_InP 2 ModularGroup.S).2
  have hcoem : Work.Kernels.ModerateGrowthOn Set.univ (fun w : ℍ => (w : ℂ)) :=
    E_atom_coe_moderate
  -- the family of all `26` atoms: the `14` scalars and the `12` components of `φ⃗, φ̃⃗, ψ⃗, ψ̃⃗`
  let Fam : Fin 26 → ℍ → ℂ := fun i w =>
    ![Work.Kernels.E2Fun w, Work.Kernels.E4Fun w, Work.Kernels.E6Fun w, Work.Kernels.E8Fun w,
      Work.Kernels.E10Fun w, Work.Kernels.E14Fun w, Work.Kernels.E2S w, Work.Kernels.UFun w,
      Work.Kernels.VFun w, Work.Kernels.WFun w, Work.Kernels.xi2Fun w, Work.Kernels.xi4Fun w,
      ℓ.L w, ℓ.L_S w,
      Work.Kernels.phiVec w 0, Work.Kernels.phiVec w 1, Work.Kernels.phiVec w 2,
      Work.Kernels.phitVec w 0, Work.Kernels.phitVec w 1, Work.Kernels.phitVec w 2,
      Work.Kernels.psiVec ℓ w 0, Work.Kernels.psiVec ℓ w 1, Work.Kernels.psiVec ℓ w 2,
      Work.Kernels.psitVec ℓ w 0, Work.Kernels.psitVec ℓ w 1, Work.Kernels.psitVec ℓ w 2] i
  have h26 : ∀ i : Fin 26, ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ w ∈ Work.Asymptotics.KEpsilon, ‖Fam i w‖ ≤ C * (Work.Kernels.scale w) ^ N := by
    intro i
    fin_cases i <;> simp only [Fam, Matrix.cons_val_zero, Fin.zero_eta]
    · exact E_atom_KEpsilon_bound hE2m
    · exact E_atom_KEpsilon_bound hE4m
    · exact E_atom_KEpsilon_bound hE6m
    · exact E_atom_KEpsilon_bound (Work.Kernels.ModerateGrowthOn.pow hE4m 2)
    · exact E_atom_KEpsilon_bound (hE4m.mul hE6m)
    · exact E_atom_KEpsilon_bound ((Work.Kernels.ModerateGrowthOn.pow hE4m 2).mul hE6m)
    · exact E_atom_KEpsilon_bound hE2Sm
    · exact E_atom_KEpsilon_bound hUm
    · exact E_atom_KEpsilon_bound hVm
    · exact E_atom_KEpsilon_bound hWm
    · exact E_atom_KEpsilon_bound (hUm.add hWm)
    · exact E_atom_KEpsilon_bound ((hUm.pow 2).add (hWm.pow 2) |>.sub
        (Work.Kernels.ModerateGrowthOn.const_mul (2 : ℂ) (hVm.pow 2)))
    · exact E_atom_KEpsilon_bound ℓ.memP
    · exact E_atom_KEpsilon_bound ℓ.memP_S
    · exact E_atom_KEpsilon_bound hcoem
    · exact E_atom_KEpsilon_bound ((hcoem.mul hE2m).sub
        (Work.Kernels.ModerateGrowthOn.const Set.univ (3 * Complex.I / (Real.pi : ℂ))))
    · exact E_atom_KEpsilon_bound ((hcoem.mul (hE2m.pow 2)).sub
        (Work.Kernels.ModerateGrowthOn.const_mul (6 * Complex.I / (Real.pi : ℂ)) hE2m))
    · exact E_atom_KEpsilon_bound (hcoem.pow 2)
    · exact E_atom_KEpsilon_bound ((hcoem.pow 2).mul hE2Sm)
    · exact E_atom_KEpsilon_bound ((hcoem.pow 2).mul (hE2Sm.pow 2))
    · exact E_atom_KEpsilon_bound (Work.Kernels.ModerateGrowthOn.const Set.univ 1)
    · exact E_atom_KEpsilon_bound (psi_InP ℓ).1.2
    · exact E_atom_KEpsilon_bound (psi_InP ℓ).2.2
    · exact E_atom_KEpsilon_bound ℓ.memP
    · exact E_atom_KEpsilon_bound hWm
    · exact E_atom_KEpsilon_bound ((hUm.pow 2).sub (hVm.pow 2))
  obtain ⟨C, N, hC, hN, hB⟩ := E_atom_common_bound Fam h26
  refine ⟨C, N, hC, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; exact hB 0 w hw
  · intro w hw; exact hB 1 w hw
  · intro w hw; exact hB 2 w hw
  · intro w hw; exact hB 3 w hw
  · intro w hw; exact hB 4 w hw
  · intro w hw; exact hB 5 w hw
  · intro w hw; exact hB 6 w hw
  · intro w hw; exact hB 7 w hw
  · intro w hw; exact hB 8 w hw
  · intro w hw; exact hB 9 w hw
  · intro w hw; exact hB 10 w hw
  · intro w hw; exact hB 11 w hw
  · intro w hw; exact hB 12 w hw
  · intro w hw; exact hB 13 w hw
  · intro w hw i
    fin_cases i
    · exact ⟨hB 14 w hw, hB 17 w hw, hB 20 w hw, hB 23 w hw⟩
    · exact ⟨hB 15 w hw, hB 18 w hw, hB 21 w hw, hB 24 w hw⟩
    · exact ⟨hB 16 w hw, hB 19 w hw, hB 22 w hw, hB 25 w hw⟩

end Work.Asymptotics
