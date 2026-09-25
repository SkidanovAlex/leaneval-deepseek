import Mathlib
import Submission.Work.WingbergRoute.All
import Submission.Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc

/-!
# `Work.WingbergRoute.natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF`

The `H²`-half of the Shafarevich--Koch count at the **totally real** quadratic base
`gsF = ℚ(√2576450045)`:

`#(H²(G_∅,ℤ) ⧸ 2·H²(G_∅,ℤ)) ≤ #H¹(G_∅,𝔽₂)`,  `G_∅ = Gal(gsF_∅/gsF)`.

The proof is the one of `Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc`,
with the numerical input `#H¹(G_∅,𝔽₂) = 2 ^ rank₂ Cl(Kc)` replaced by the *finiteness* of
`H¹(G_∅,𝔽₂)`, which is available unconditionally: continuous characters `G_∅ → 𝔽₂` are the
continuous homomorphisms `G_∅ → 𝔽₂`, which are the unramified quadratic levels of `gsF`
(`Work.ShafarevichKoch.nonempty_proTwoCharEquiv_option_quadraticLevel`), and there are only
finitely many of those (`Work.ShafarevichKoch.finite_quadraticLevel`, the elementary Kummer
two-descent, valid for **every** number field — no class field theory).

Nothing else is used beyond the general algebra of the chapter:

* `0 → ℤ → ℚ → ℚ/ℤ → 0` with `H¹(G,ℚ) = H²(G,ℚ) = 0` identifies `H²(G,ℤ)` with `H¹(G,ℚ/ℤ)`,
  so `H²(G,ℤ)` is `2`-primary torsion (the pro-`2` group has finite quotients);
* its `2`-torsion is a quotient of `H¹(G,𝔽₂)` via the connecting map of `0 → ℤ →^2 ℤ → 𝔽₂ → 0`;
* for `2`-primary torsion with finite `2`-torsion, `#(A/2A) ≤ #A[2]`
  (`Work.ShafarevichKoch.TorsionCokernel.natCard_quot_two_le_natCard_twoTorsion`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

open scoped Classical

namespace Work.WingbergRoute

open Work.ConCohomology
open Work.ShafarevichKoch
open Work.ShafarevichKoch.H2Half

noncomputable section

/-- **The `H²`-half of the Shafarevich--Koch count, in the `H¹`-normalisation.**

For a number field `F`, a maximal unramified pro-`2` extension `M` of `F` and
`G = G_∅ = Gal(F_∅/F)`: if the `𝔽₂`-vector space `H¹(G,𝔽₂)` is finite, then the `2`-quotient of
`H²(G,ℤ)` is no larger than `H¹(G,𝔽₂)` itself,

`#(H²(G,ℤ) ⧸ 2·H²(G,ℤ)) ≤ #H¹(G,𝔽₂)`.

The finiteness of `H¹(G,𝔽₂)` is the only extra hypothesis: the rest is the general algebra of the
coefficient sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` together with
`Work.ShafarevichKoch.TorsionCokernel.natCard_quot_two_le_natCard_twoTorsion`. -/
theorem natCard_H2Z_quot_two_le_card_H1_zmodTwo_of_finite {F : Type} [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (hfinH1 : Finite (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2))) :
    Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≤
      Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := by
  haveI hfinH1' : Finite (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := hfinH1
  have htrivQ : ∀ (σ : Work.ClassFieldTower.galoisGroup M) (q : ℚ), σ • q = q := fun _ _ => rfl
  have htrivQZ : ∀ (σ : Work.ClassFieldTower.galoisGroup M) (m : QZ), σ • m = m := fun _ _ => rfl
  -- `G_∅` is a pro-`2` group
  have hpro : Work.RelatorRank.IsProPGroup 2 (Work.ClassFieldTower.galoisGroup M) :=
    Work.ShaBound.isProPGroup_of_forall_intermediateField_isPGroup
      (F := F) (K := M.K) M.proP
  -- `H¹(G,ℚ) = H²(G,ℚ) = 0` (compact totally disconnected group, divisible coefficients)
  obtain ⟨h1Q, h2Q⟩ :=
    Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat
      (G := Work.ClassFieldTower.galoisGroup M) htrivQ
  haveI : Subsingleton (H2 (Work.ClassFieldTower.galoisGroup M) ℚ) := h2Q
  haveI : Subsingleton (H1 (Work.ClassFieldTower.galoisGroup M) ℚ) := h1Q
  -- the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0` is surjective and additive
  have hsurjδ : Function.Surjective
      (connecting1 (ratCoeffSES (Work.ClassFieldTower.galoisGroup M))) := by
    intro x
    refine (exact_H2_A (ratCoeffSES (Work.ClassFieldTower.galoisGroup M)) x).mp ?_
    exact Subsingleton.elim _ _
  let δ : H1 (Work.ClassFieldTower.galoisGroup M) QZ →+
      H2 (Work.ClassFieldTower.galoisGroup M) ℤ :=
    AddMonoidHom.mk' (connecting1 (ratCoeffSES (Work.ClassFieldTower.galoisGroup M)))
      (fun x y => connecting1_add _ x y)
  -- hence `H²(G,ℤ)` is `2`-primary torsion
  have htorQZ : ∀ y : H1 (Work.ClassFieldTower.galoisGroup M) QZ,
      ∃ k : ℕ, (2 : ℕ) ^ k • y = 0 := by
    intro y
    obtain ⟨k, hk⟩ :=
      exists_two_pow_nsmul_eq_zero_of_isProPGroup hpro (H1ToContAddHom htrivQZ y)
    refine ⟨k, ?_⟩
    apply (H1EquivContAddHom htrivQZ).injective
    change H1ToContAddHom htrivQZ ((2 : ℕ) ^ k • y) = H1ToContAddHom htrivQZ 0
    rw [map_nsmul, hk, map_zero]
  have htor : ∀ x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ,
      ∃ k : ℕ, (2 : ℕ) ^ k • x = 0 := by
    intro x
    obtain ⟨y, hy⟩ := hsurjδ x
    obtain ⟨k, hk⟩ := htorQZ y
    exact ⟨k, by rw [show x = δ y from hy.symm, ← map_nsmul, hk, map_zero]⟩
  -- its `2`-torsion is the image of `H¹(G,𝔽₂)`
  have hsurj2 : Function.Surjective (fun y : H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2) =>
      (⟨connecting1 (ZSES (Work.ClassFieldTower.galoisGroup M)) y, by
        rw [← H2Map_zModTwoCoeffSES_f]
        exact (exact_H2_A (ZSES (Work.ClassFieldTower.galoisGroup M))
          (connecting1 (ZSES (Work.ClassFieldTower.galoisGroup M)) y)).mpr
            ⟨y, rfl⟩⟩ :
        {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ // (2 : ℕ) • x = 0})) := by
    intro x
    have h0 : H2Map (ZSES (Work.ClassFieldTower.galoisGroup M)).f x.1 = 0 := by
      rw [H2Map_zModTwoCoeffSES_f]
      exact x.2
    obtain ⟨y, hy⟩ := (exact_H2_A (ZSES (Work.ClassFieldTower.galoisGroup M)) x.1).mp h0
    exact ⟨y, Subtype.ext hy⟩
  haveI hfinite_tors : Finite {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ //
      (2 : ℕ) • x = 0} := Finite.of_surjective _ hsurj2
  have htors_le : Nat.card {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ //
      (2 : ℕ) • x = 0} ≤ Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) :=
    Nat.card_le_card_of_surjective _ hsurj2
  -- the pure-algebra count
  calc Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
        twoMulH2 (Work.ClassFieldTower.galoisGroup M))
      ≤ Nat.card {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ // (2 : ℕ) • x = 0} :=
        Work.ShafarevichKoch.TorsionCokernel.natCard_quot_two_le_natCard_twoTorsion htor hfinite_tors
    _ ≤ Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := htors_le

/-- **`#H¹(G_∅,𝔽₂)` is finite for `G_∅ = Gal(gsF_∅/gsF)`**, `gsF = ℚ(√2576450045)`.

The continuous characters `G_∅ → 𝔽₂` are the continuous additive homomorphisms `G_∅ → 𝔽₂`
(`Work.ConCohomology.H1EquivContAddHom`, since `Aut(𝔽₂) = 1`), hence the continuous group
homomorphisms `G_∅ → Multiplicative 𝔽₂`, i.e. the elements of `Work.ShafarevichKoch.ProTwoChar`,
which are the unramified quadratic levels of `gsF` together with the trivial character
(`Work.ShafarevichKoch.nonempty_proTwoCharEquiv_option_quadraticLevel`).  There are only finitely
many unramified quadratic levels (`Work.ShafarevichKoch.finite_quadraticLevel`). -/
theorem finite_H1_zmodTwo_galoisGroup_gsF
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.WingbergRoute.gsF 2) :
    Finite (Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := by
  haveI hfinQL : Finite (Work.ShafarevichKoch.QuadraticLevel gsF M) :=
    Work.ShafarevichKoch.finite_quadraticLevel gsF M
  obtain ⟨eQL⟩ :=
    Work.ShafarevichKoch.nonempty_proTwoCharEquiv_option_quadraticLevel gsF M
  haveI hfinChar : Finite (Work.ShafarevichKoch.ProTwoChar gsF M) :=
    Finite.of_equiv (Option (Work.ShafarevichKoch.QuadraticLevel gsF M)) eQL.symm
  have htriv2 : ∀ (σ : Work.ClassFieldTower.galoisGroup M) (m : ZMod 2), σ • m = m :=
    fun σ m => Work.ShafarevichKoch.smul_zmodTwo_eq σ m
  have eH1 : Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2) ≃
      Work.ShafarevichKoch.ProTwoChar gsF M :=
    (Work.ConCohomology.H1EquivContAddHom (G := Work.ClassFieldTower.galoisGroup M)
      (M := ZMod 2) htriv2).trans
      (Work.ShafarevichKoch.H2Half.contAddHomEquivContinuousHom
        (Work.ClassFieldTower.galoisGroup M) (ZMod 2))
  exact Finite.of_injective (eH1 : _ → _) eH1.injective

theorem natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.WingbergRoute.gsF 2) :
    Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) ≤
      Nat.card (Work.ConCohomology.H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := by
  exact natCard_H2Z_quot_two_le_card_H1_zmodTwo_of_finite M
    (finite_H1_zmodTwo_galoisGroup_gsF M)

end

end Work.WingbergRoute
