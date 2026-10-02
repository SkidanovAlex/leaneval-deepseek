import Mathlib
import Submission.Work.Kunneth.PointDefs
import Submission.Work.Kunneth.GenTautLinePunctVanishing
import Submission.Work.Gen.ChernGenerator

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Kunneth

/-!
# The powers of `c₁(O(-1))` generate the cohomology of `ℂPⁿ`

`Work.Kunneth.GenPowGenerates` is the statement that the `j`-th cup power of the first Chern class
of the tautological line bundle `O(-1) = Work.Gen.tautLine n` on `ℂPⁿ` generates
`H^{2j}(ℂPⁿ;ℤ)` as a `ℤ`-module, for `j ≤ n`:

  `Submodule.span ℤ {pow2 (chernClass 1 1 (tautLine n)) j} = ⊤`.

## The argument

Write `e := chernClass 1 1 (tautLine n) ∈ H²(ℂPⁿ;ℤ)`, the Euler class of the rank-`2` real bundle
`Z = realification (tautLine n)`: `Work.Thom.chernClass_one_top` identifies `e` with `T.eulerClass`
for the canonical Thom class `T = Work.Thom.thomClassRank 1 ⋯ (tautLine n)` (`genT` below).

The Gysin sequence of the sphere bundle of `Z` has, in each degree `k`, exactness at the base term
(`Work.Thom.gysin_exact_at_base`)

  `Set.range (gysinEuler T k) = {x | gysinπ Z (k+2) x = 0}`,

and `gysinEuler T k` **is** cup product with the Euler class
(`Work.Thom.gysinEuler_eq_cupEuler`).  The sphere bundle of `O(-1)` is `ℂ^{n+1}∖{0} ≃ S^{2n+1}`, so
its cohomology vanishes off degrees `0` and `2n+1`
(`Work.Kunneth.GenTautLinePunctVanishing`); in degree `2j+2` — which is even, hence never `2n+1` —
the vanishing makes `gysinπ Z (2j+2)` the zero map, so `∪ e : H^{2j}(ℂPⁿ;ℤ) → H^{2j+2}(ℂPⁿ;ℤ)` is
**surjective**.  Consequently `e^{j+1} = e^j ⌣ e` generates `H^{2j+2}(ℂPⁿ;ℤ)` as soon as `e^j`
generates `H^{2j}(ℂPⁿ;ℤ)` (`Work.Kunneth.span_singleton_image_eq_top`), and the induction starts at
`H⁰(ℂPⁿ;ℤ) = ℤ⟨1⟩` (`Work.Cohomology.exists_smul_oneH`, `ℂPⁿ` being path connected).

The induction is in fact *unconditional* in `j` (the surjectivity of `∪ e` needs no bound on `j`),
so the hypothesis `j ≤ n` of `GenPowGenerates` is not needed; it is kept because it is part of the
requested statement.
-/

noncomputable section

/-- **The canonical Thom class of the realification of the tautological line bundle `O(-1)` on
`ℂPⁿ`.**  Its Euler class is the first Chern class `Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)`
(`genT_euler`). -/
private noncomputable def genT (n : ℕ) : Work.Thom.ThomClass
    (Work.Thom.realification (Work.Gen.tautLine n)) 2 :=
  Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0)) (Work.Gen.tautLine n)

/-- The first Chern class of the tautological line bundle is the Euler class of `genT`. -/
private lemma genT_euler (n : ℕ) :
    Work.Thom.chernClass 1 1 (Work.Gen.tautLine n) = (genT n).eulerClass :=
  Work.Thom.chernClass_one_top (Work.Gen.tautLine n)

/-- The degree cast `Work.Thom.cohTransportLM h` is surjective (it is an isomorphism). -/
private lemma cohTransportLM_surjective {B : Type} [TopologicalSpace B] {m m' : ℕ} (h : m = m') :
    Function.Surjective (Work.Thom.cohTransportLM (B := B) h) :=
  fun y => ⟨Work.Thom.cohTransport (B := B) h.symm y, by
    rw [Work.Thom.cohTransportLM_apply]
    rw [Work.Whitney.cohTransport_trans]
    rw [show h.symm.trans h = (rfl : m' = m') from Subsingleton.elim _ _]
    rw [Work.Thom.cohTransport_rfl]⟩

/-- **The powers of `c₁(O(-1))` generate the cohomology of `ℂPⁿ`, in every degree.**
(The hypothesis `j ≤ n` of `GenPowGenerates` is not needed, see the module docstring.) -/
private theorem genPowAux (n j : ℕ) :
    Submodule.span ℤ {(Work.Kunneth.pow2
      (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) j)} = ⊤ := by
  induction j with
  | zero =>
    -- `H⁰(ℂPⁿ;ℤ) = ℤ⟨1⟩`, and `pow2 e 0 = 1`.
    show Submodule.span ℤ ({Work.Cohomology.oneH ℤ (Work.Whitney.ssB (Work.Projective.CP n))} :
      Set ↥(Work.Thom.Coh ℤ 0 (Work.Projective.CP n))) = ⊤
    rw [Submodule.eq_top_iff']
    intro z
    haveI : PathConnectedSpace (Work.Projective.CP n) := Work.Projective.pathConnectedSpace_CP n
    obtain ⟨m, hm⟩ := Work.Cohomology.exists_smul_oneH (TopCat.of (Work.Projective.CP n)) z
    rw [hm]
    refine Submodule.mem_span_singleton.mpr ⟨m, ?_⟩
    exact int_smul_eq_zsmul (inferInstance : Module ℤ
      ↥(Work.Thom.Coh ℤ 0 (Work.Projective.CP n))) m _
  | succ j ih =>
    have hTe := genT_euler n
    -- `H^{2j+2}` of the sphere bundle of `O(-1)` vanishes: `2j+2` is even, hence not `2n+1`.
    haveI : Subsingleton ↥(Work.Thom.Coh ℤ (2*j+2) ↥(Work.Thom.zeroComplement
        (Work.Thom.realification (Work.Gen.tautLine n)))) :=
      Work.Kunneth.GenTautLinePunctVanishing n (2*j+2) (by omega) (by omega)
    -- hence `∪ e : H^{2j} → H^{2j+2}` is onto
    have hsurj : Function.Surjective (Work.Thom.gysinEuler (genT n) (2*j)) := by
      intro y
      have h := Work.Thom.gysin_exact_at_base (genT n) (2*j)
      have hy : y ∈ Set.range ⇑(Work.Thom.gysinEuler (genT n) (2*j)) := by
        rw [h]
        exact Subsingleton.elim _ _
      exact hy
    have hgen := Work.Kunneth.span_singleton_image_eq_top
      (Work.Thom.gysinEuler (genT n) (2*j)) hsurj ih
    -- `∪ e` is the cup product with `e`
    have hab : (Work.Thom.gysinEuler (genT n) (2*j))
          (Work.Kunneth.pow2 (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) j)
        = (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (Work.Projective.CP n)) (2*j) (2*1))
          (Work.Kunneth.pow2 (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) j)
          (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) := by
      rw [Work.Thom.gysinEuler_eq_cupEuler, ← hTe]
    -- `pow2 e (j+1)` is the degree cast of `e^j ⌣ e`
    have hstep : Work.Kunneth.pow2 (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) (j+1)
        = Work.Thom.cohTransport (Nat.mul_add 2 j 1).symm
          ((Work.Thom.gysinEuler (genT n) (2*j))
            (Work.Kunneth.pow2 (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) j)) := by
      rw [Work.Kunneth.pow2_succ, Work.Whitney.cupChern_def]
      exact congrArg (Work.Thom.cohTransport (Nat.mul_add 2 j 1).symm) hab.symm
    rw [hstep]
    exact Work.Kunneth.span_singleton_image_eq_top
      (Work.Thom.cohTransportLM (Nat.mul_add 2 j 1).symm)
      (cohTransportLM_surjective _) hgen

/-- **`c₁(O(-1))^j` generates `H^{2j}(ℂPⁿ;ℤ)` for `j ≤ n`** — the requested statement. -/
theorem GenPowGenerates (n j : ℕ) (hj : j ≤ n) :
    Submodule.span ℤ {(Work.Kunneth.pow2
      (Work.Thom.chernClass 1 1 (Work.Gen.tautLine n)) j)} = ⊤ :=
  genPowAux n j

end

end Work.Kunneth
