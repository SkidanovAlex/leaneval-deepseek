/-
# Moderate growth of the cleared kernel `K_+^{(d)}` in the first variable

Theorem 4.9(4) of CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022))
states that `Δ(τ)Δ(z)^{e}(j(τ)−j(z))K_+^{(d)}(τ,z)` lies in the class `𝒫` for `d ∈ {8, 24}`.
The *cleared* kernel `Work.Kernels.KPlusClear d τ z` is this product written without any
division by `j(τ)−j(z)`.  Here we prove that for fixed `z` and each `d ∈ {8, 24}` the function
`τ ↦ KPlusClear d τ z` lies in `𝒫 = Work.Kernels.InP` (holomorphic on `ℍ` plus moderate
growth there).

The kernel is the bilinear pairing
`KPlusClear d τ z = ∑ i ∑ j, φ_i(τ) · Υ⁺ᶜˡᵉᵃʳ_{ij}(τ,z) · φ̃_j(z)`.
Since `𝒫` is closed under finite sums, products and multiplication by constants, it suffices
that
* each coordinate `τ ↦ φ_i(τ)` lies in `𝒫` (`Work.Kernels.KernelGrowth.PhiVec_InP`), and
* each entry `τ ↦ Υ⁺ᶜˡᵉᵃʳ_{ij}(τ,z)` lies in `𝒫`
  (`Work.Kernels.KernelGrowth.UpsilonPlusClear_entry_InP`),
while the `z`-dependent factor `φ̃_j(z)` is a constant of `τ` and hence trivially in `𝒫`.

The entry statement is the substantive input: the entries of `Υ⁺ᶜˡᵉᵃʳ` contain `Δ(τ)` and the
`j`-invariant `j(τ)`, and the apparent pole of `j` is cancelled by the explicit power of `Δ`,
via the relation `Δ(τ)j(τ) = E₄(τ)³`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelGrowth.PhiVec_InP
import Submission.Work.Kernels.KernelGrowth.UpsilonPlusClear_entry_InP

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.KernelGrowth

/-- For fixed `z` and `d ∈ {8, 24}`, the cleared kernel `τ ↦ K_+^{(d)}(τ,z)` lies in
`𝒫 = Work.Kernels.InP`. -/
theorem KPlusClear_growth_tau (d : ℕ) (hd : d = 8 ∨ d = 24) (z : UpperHalfPlane) :
    Work.Kernels.InP (fun τ : UpperHalfPlane => Work.Kernels.KPlusClear d τ z) := by
  -- Rewrite the kernel as the finite double sum of the products `φ_i(τ)·Υ_{ij}(τ,z)·φ̃_j(z)`.
  have hfun : (fun τ : UpperHalfPlane => Work.Kernels.KPlusClear d τ z) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        fun τ : UpperHalfPlane => Work.Kernels.phiVec τ i *
          Work.Kernels.UpsilonPlusClear d τ z i j * Work.Kernels.phitVec z j) := by
    funext τ
    simp only [Work.Kernels.KPlusClear, Finset.sum_apply]
  rw [hfun]
  apply Work.Kernels.InP.sum Finset.univ
  intro i _
  apply Work.Kernels.InP.sum Finset.univ
  intro j _
  exact Work.Kernels.InP.mul
    (Work.Kernels.InP.mul (PhiVec_InP i) (UpsilonPlusClear_entry_InP d hd z i j))
    (Work.Kernels.InP.const (Work.Kernels.phitVec z j))

end Work.Kernels.KernelGrowth
