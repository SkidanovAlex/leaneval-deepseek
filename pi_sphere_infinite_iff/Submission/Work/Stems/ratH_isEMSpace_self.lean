import Mathlib
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Serre.C1Rat
import Submission.Work.Serre.Models

set_option linter.style.haveILetI false

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Stems

noncomputable section

/-- **The Hurewicz map does not depend on the proof of `1 ≤ n` that it carries.**  Since `1 ≤ n` is
a proposition, any two proofs are equal, and the two maps are then equal by congruence.  This is
what lets the additivity `Work.Stems.hurewiczMapN_mul` — which carries the proof
`Nat.succ_le_succ (Nat.zero_le k)` in degree `k + 1` — be used for the Hurewicz map in the
`by omega` form produced by `Work.Stems.hurewicz_first_degree`. -/
theorem hurewiczMapN_congr (n : ℕ) (h1 h2 : 1 ≤ n) {X : Type} [TopologicalSpace X] (x₀ : X) :
    hurewiczMapN n h1 x₀ = hurewiczMapN n h2 x₀ :=
  congrArg (fun hn => hurewiczMapN n hn x₀) (Subsingleton.elim h1 h2)

/-- **A model of `K(ℤ,n)` has `H_n(−;ℚ) ≅ ℚ`** (`n ≥ 2`).

This is the homology form of the "generator in degree `n`" clause of the `C2` layer: for `X` a
model of `K(ℤ,n)`, it supplies `C2evenRange`'s conjunct `Nonempty (ratH X (2j) ≅ ℚ)` (which, since
`2jk < 4j-1` forces `k = 1`, is exactly `H_{2j}(K(ℤ,2j);ℚ) ≅ ℚ`) and the first conjunct of
`Work.Stems.Engine.OddSphereRange` (`Nonempty (ratH X n ≅ ℚ)`).

Proof: `π_n(X,pt) ≅ Multiplicative ℤ` by definition of `IsEMSpace`; the Hurewicz map
`Work.Stems.hurewiczMapN n _ pt : π_n(X,pt) → H_n(X;ℤ)` is bijective —
`Work.Stems.hurewicz_first_degree` (injectivity from
`Work.Stems.Hur2c.hurewiczMapN_injective_firstDegree`, surjectivity from
`Work.Stems.hurewiczMapN_surjective`) — and additive (`Work.Stems.hurewiczHom`, whose underlying
map is `hurewiczMapN` up to the bridge in `Work.Stems.HurewiczNeutralAgree`), so it is an
isomorphism of `ℤ`-modules `ℤ ≅ H_n(X;ℤ)`; then `H_n(X;ℚ) ≅ H_n(X;ℤ) ⊗[ℤ] ℚ ≅ ℚ` by flat base
change (`Work.StemsB.SphRat.homologyMapBaseChange` together with the comparison
`Work.Serre.Phi : (C_*(X;ℤ) ⊗ ℚ) ≅ C_*(X;ℚ)` of `Submission/Work/Serre/C1Rat.lean`; the comparison
is not definitional, so the proof must route through `Phi`).

`IsEMSpace` carries no hypothesis on `n` beyond `0 < n`; `hn : 2 ≤ n` is what makes the Hurewicz
input apply (the case `n = 1` is `C1`'s business, `Work.Serre.serreC1`). -/
theorem ratH_isEMSpace_self {n : ℕ} (hn : 2 ≤ n) {X : Type} [TopologicalSpace X] (pt : X)
    (h : Work.Serre.IsEMSpace ℤ n (by omega) X pt) :
    Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) := by
  -- Work in the successor degree `k + 1 = n`, so that the Hurewicz machinery (stated for `k + 1`)
  -- applies with the canonical `Nonempty (Fin (k+1))` instance.
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨φ⟩ := h.1
  -- `X` is `(n-1)`-connected, so Hurewicz is an isomorphism in degree `n = k + 1`.
  have hconn : ∀ i : ℕ, i < k + 1 → Subsingleton (HomotopyGroup (Fin i) X pt) :=
    fun i _ => h.2 i (by omega)
  have hbij : Function.Bijective (hurewiczMapN (k + 1) (by omega) pt) :=
    hurewicz_first_degree (k + 1) hn pt hconn
  set p0 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k) with hp0
  let H0 : HomotopyGroup (Fin (k + 1)) X pt →
      (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (k + 1) :=
    hurewiczMapN (k + 1) p0 pt
  have hH0 : Function.Bijective H0 := by
    have hEq : H0 = hurewiczMapN (k + 1) (by omega) pt :=
      hurewiczMapN_congr (k + 1) p0 (by omega) pt
    rw [hEq]; exact hbij
  -- `H0` is additive, hence so is `Ψ : ℤ → H_{k+1}(X;ℤ)`, `z ↦ H0 (φ.symm (ofAdd z))`.
  let Ψ : ℤ →+ (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (k + 1) :=
    { toFun := fun z => H0 (φ.symm (Multiplicative.ofAdd z))
      map_zero' := by
        change H0 (φ.symm (Multiplicative.ofAdd (0 : ℤ))) = 0
        rw [show Multiplicative.ofAdd (0 : ℤ) = (1 : Multiplicative ℤ) from rfl, map_one]
        change hurewiczMapN (k + 1) p0 pt (1 : HomotopyGroup (Fin (k + 1)) X pt) = 0
        have hx := hurewiczMapN_mul k pt (1 : HomotopyGroup (Fin (k + 1)) X pt) 1
        rw [mul_one] at hx
        exact (add_right_cancel_iff (a := hurewiczMapN (k + 1) p0 pt
          (1 : HomotopyGroup (Fin (k + 1)) X pt))).mp (by rw [hx.symm, zero_add])
      map_add' := by
        intro z w
        have hof : Multiplicative.ofAdd (z + w) =
            Multiplicative.ofAdd z * Multiplicative.ofAdd w := rfl
        rw [hof, map_mul]
        exact hurewiczMapN_mul k pt _ _ }
  have hΨ : Function.Bijective Ψ := by
    have h1 : Function.Bijective (fun z : ℤ => φ.symm (Multiplicative.ofAdd z)) :=
      φ.symm.bijective.comp Multiplicative.ofAdd.bijective
    exact hH0.comp h1
  let e : ℤ ≃+ (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (k + 1) :=
    AddEquiv.ofBijective Ψ hΨ
  -- The integral Hurewicz isomorphism `ℤ ≅ H_{k+1}(X;ℤ)`.
  have hInt : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (k + 1) ≅
      ModuleCat.of ℤ ℤ :=
    (LinearEquiv.toModuleIso e.toIntLinearEquiv).symm
  -- Flat base change `- ⊗[ℤ] ℚ`.
  let F := ModuleCat.extendScalars (Int.castRingHom ℚ)
  have hf : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI : PreservesFiniteColimits F := inferInstance
  haveI : F.PreservesHomology := inferInstance
  -- `H_{k+1}(X;ℚ) ≅ (C_*(X;ℤ) ⊗ ℚ)_{k+1}` via the comparison `Phi`.
  have hPhi : Work.Serre.ratH (TopCat.of X) (k + 1)
      ≅ ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Work.Cohomology.singularChains ℤ (TopCat.of X))).homology (k + 1) :=
    ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (k + 1)).mapIso
      (Work.Serre.Phi (TopCat.toSSet.obj (TopCat.of X)))).symm
  -- `(C_*(X;ℤ) ⊗ ℚ)_{k+1} ≅ H_{k+1}(X;ℤ) ⊗ ℚ`.
  have hbch : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Work.Cohomology.singularChains ℤ (TopCat.of X))).homology (k + 1)
      ≅ F.obj ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (k + 1)) :=
    (Work.StemsB.SphRat.homologyMapBaseChange F _ (k + 1)).some
  -- `H_{k+1}(X;ℤ) ⊗ ℚ ≅ ℤ ⊗ ℚ ≅ ℚ`.
  have hFmap : F.obj ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology (k + 1))
      ≅ F.obj (ModuleCat.of ℤ ℤ) := F.mapIso hInt
  have hlast : F.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
    Work.StemsB.SphRat.extendScalarsIntRatIso
  exact ⟨hPhi ≪≫ hbch ≪≫ hFmap ≪≫ hlast⟩

end

end Work.Stems
