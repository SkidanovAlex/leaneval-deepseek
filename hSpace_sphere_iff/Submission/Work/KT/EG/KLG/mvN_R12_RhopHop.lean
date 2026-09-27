import Mathlib
import Submission.Work.KT.EG.KLG.kappa_bott_defs

/-!
# `Work.KT.EG.KLG.mvN_R12_RhopHop` — the `(R₁,R₂)`-pair is Murray–von Neumann equivalent to
the Hopf pair `(RhopUp, RhopDn)`

The glued matrices `R12Pair X h12` and `RhopPair X hhop` over the fibre product `pullAlg2 X` are
built componentwise out of `2 × 2` matrices over `C(X × Ball ℂ, ℂ)`.  Multiplication in `pullAlg2 X`
is componentwise (it is a subalgebra of a product), so the hypotheses

* `h1 : R₁ * RhopUp = RhopUp`, `h2 : RhopUp * R₁ = R₁`,
* `h3 : R₂ * RhopDn = RhopDn`, `h4 : RhopDn * R₂ = R₂`

transport verbatim to the glued matrices:

* `R12Pair * RhopPair = RhopPair` (from `h1`, `h3`),
* `RhopPair * R12Pair = R12Pair` (from `h2`, `h4`),

which is precisely the Murray–von Neumann datum `(a, b) = (R12Pair, RhopPair)` witnessing
`MvN (R12Pair) (RhopPair)`: `b * a = R12Pair` and `a * b = RhopPair`.

The only formal points are that `bdryRestrict` is a ring homomorphism (so it commutes with matrix
multiplication) and that the compatibility proofs stored in `pairMat` are proof-irrelevant.
-/

namespace Work.KT.EG.KLG

open _root_.Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Multiplication of glued matrices over `pullAlg2 X` is componentwise: the glue of a product is
the product of the glues.  The compatibility hypothesis on `M₀ * N₀` and `M₁ * N₁` is supplied
from those on `M` and `N` via the multiplicativity of `bdryRestrict`. -/
lemma pairMat_mul {ι : Type} [Fintype ι]
    (M₀ M₁ N₀ N₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (hM : M₀.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = M₁.map (fun f => Work.KT.Fund.bdryRestrict X f))
    (hN : N₀.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = N₁.map (fun f => Work.KT.Fund.bdryRestrict X f)) :
    Work.KT.Fund.pairMat X M₀ M₁ hM * Work.KT.Fund.pairMat X N₀ N₁ hN
      = Work.KT.Fund.pairMat X (M₀ * N₀) (M₁ * N₁)
          (by rw [Matrix.map_mul, Matrix.map_mul, hM, hN]) :=
  Work.KT.Fund.mat_ext X
    (by simp only [Matrix.map_mul, Work.KT.Fund.pairMat_map_prF])
    (by simp only [Matrix.map_mul, Work.KT.Fund.pairMat_map_prS])

/-- If the two disc-level matrices of `M` are absorbed by those of `N` on the right
(`M₀ * N₀ = N₀`, `M₁ * N₁ = N₁`), the same happens after gluing. -/
lemma pairMat_mul_of_mul_eq_self {ι : Type} [Fintype ι]
    (M₀ M₁ N₀ N₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (hM : M₀.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = M₁.map (fun f => Work.KT.Fund.bdryRestrict X f))
    (hN : N₀.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = N₁.map (fun f => Work.KT.Fund.bdryRestrict X f))
    (ha : M₀ * N₀ = N₀) (hb : M₁ * N₁ = N₁) :
    Work.KT.Fund.pairMat X M₀ M₁ hM * Work.KT.Fund.pairMat X N₀ N₁ hN
      = Work.KT.Fund.pairMat X N₀ N₁ hN := by
  rw [pairMat_mul X M₀ M₁ N₀ N₁ hM hN]
  apply Work.KT.Fund.mat_ext X
  · simpa only [Work.KT.Fund.pairMat_map_prF] using ha
  · simpa only [Work.KT.Fund.pairMat_map_prS] using hb

/-- If `N` is absorbed by `M` on the right at the disc level, the same holds after gluing. -/
lemma pairMat_mul_of_self_mul_eq {ι : Type} [Fintype ι]
    (M₀ M₁ N₀ N₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (hM : M₀.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = M₁.map (fun f => Work.KT.Fund.bdryRestrict X f))
    (hN : N₀.map (fun f => Work.KT.Fund.bdryRestrict X f)
      = N₁.map (fun f => Work.KT.Fund.bdryRestrict X f))
    (ha : N₀ * M₀ = M₀) (hb : N₁ * M₁ = M₁) :
    Work.KT.Fund.pairMat X N₀ N₁ hN * Work.KT.Fund.pairMat X M₀ M₁ hM
      = Work.KT.Fund.pairMat X M₀ M₁ hM :=
  pairMat_mul_of_mul_eq_self X N₀ N₁ M₀ M₁ hN hM ha hb

theorem mvN_R12_RhopHop (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (h12 : (Work.KT.EG.KLG.R1 X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.EG.KLG.R2 X).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (hhop : (Work.KT.Fund.KL.RhopUp X).map (fun f => Work.KT.Fund.bdryRestrict X f)
      = (Work.KT.Fund.KL.RhopDn X).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (h1 : Work.KT.EG.KLG.R1 X * Work.KT.Fund.KL.RhopUp X = Work.KT.Fund.KL.RhopUp X)
    (h2 : Work.KT.Fund.KL.RhopUp X * Work.KT.EG.KLG.R1 X = Work.KT.EG.KLG.R1 X)
    (h3 : Work.KT.EG.KLG.R2 X * Work.KT.Fund.KL.RhopDn X = Work.KT.Fund.KL.RhopDn X)
    (h4 : Work.KT.Fund.KL.RhopDn X * Work.KT.EG.KLG.R2 X = Work.KT.EG.KLG.R2 X) :
    Work.KT.Mat.MvN (⟨2, Work.KT.EG.KLG.R12Pair X h12⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      (⟨2, Work.KT.EG.KLG.RhopPair X hhop⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
  have hmul1 : R12Pair X h12 * RhopPair X hhop = RhopPair X hhop :=
    pairMat_mul_of_mul_eq_self X (R1 X) (R2 X) (Work.KT.Fund.KL.RhopUp X)
      (Work.KT.Fund.KL.RhopDn X) h12 hhop h1 h3
  have hmul2 : RhopPair X hhop * R12Pair X h12 = R12Pair X h12 :=
    pairMat_mul_of_self_mul_eq X (R1 X) (R2 X) (Work.KT.Fund.KL.RhopUp X)
      (Work.KT.Fund.KL.RhopDn X) h12 hhop h2 h4
  exact ⟨R12Pair X h12, RhopPair X hhop, hmul2, hmul1⟩

end

end Work.KT.EG.KLG
