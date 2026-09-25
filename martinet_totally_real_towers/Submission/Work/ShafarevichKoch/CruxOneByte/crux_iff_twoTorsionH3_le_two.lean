import Mathlib
import Submission.Work.ShafarevichKoch.CountZ
import Submission.Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc
import Submission.Work.ShafarevichKoch.Gaschutz.WeakUnitInput
import Submission.Work.ShafarevichKoch.card_quotient_two_eq_card_twoTorsion
import Submission.Work.ShafarevichKoch.GeneratorRankKc
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ShafarevichKoch.WingbergDefs

/-!
# `Work.ShafarevichKoch.CruxOneByte.crux_iff_twoTorsionH3_le_two`

The Shafarevich--Koch relation count for `Kc = ℚ(√-30030)` in its **one-byte** form: for
`G_∅ = Gal(Kc_∅/Kc)`,

`dim_{𝔽₂} H²(G_∅, 𝔽₂) ≤ 6`  **iff**  `#H³(G_∅,ℤ)[2] ≤ 2` .

## The mathematics

The `ℤ`-power coefficient sequence `0 → ℤ --2--> ℤ --mod 2--> ℤ/2 → 0` gives the exact sequence

`0 → H²(G,ℤ)/2H²(G,ℤ) → H²(G,𝔽₂) → H³(G,ℤ)[2] → 0`

(`Work.ShafarevichKoch.natCard_H2_zmodTwo_eq` is its cardinality shadow:
`#H²(G,𝔽₂) = #(H²(G,ℤ)/2H²(G,ℤ)) · #H³(G,ℤ)[2]`).  The whole crux is therefore the statement
that the *first* factor is exactly `2^5 = 32`:

* `#(H²(G,ℤ)/2H²(G,ℤ)) ≤ 2^5` holds with no class field theory
  (`Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc`);
* the reverse inequality is where the "one byte" lives.  For a finite abelian group `A`,
  `A/2A` and `A[2]` have the same cardinality
  (`Work.ShafarevichKoch.card_quotient_two_eq_card_twoTorsion`), and the connecting map
  `δ¹ : H¹(G,𝔽₂) → H²(G,ℤ)[2]` of the coefficient sequence is a homomorphism onto `H²(G,ℤ)[2]`
  (`Work.ConCohomology.exact_H2_A`, `H2Map_zModTwoCoeffSES_f`) whose kernel is the image of
  `H¹(G,ℤ) → H¹(G,𝔽₂)` (`Work.ConCohomology.exact_H1_C`).  Since `G_∅` is a *compact* group and
  `ℤ` is torsion-free, `H¹(G,ℤ) = 0` (`subsingleton_H1_int` below: a locally constant additive
  character `G → ℤ` has open kernel, hence finite index; a positive power of every `σ` lies in that
  kernel, so `n • φ σ = 0` with `n > 0` and hence `φ σ = 0`).  Thus `δ¹` is injective and

`#(H²(G,ℤ)/2H²(G,ℤ)) = #H²(G,ℤ)[2] ≥ #H¹(G,𝔽₂) = 2^5`

(`Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc`), so both factors are `2^5` and
`≤ 2^5`, hence equal: `twoTorsionH2_card_galoisGroup_Kc`.

The two sides of the crux are then `#H²(G,𝔽₂) = 2^5 · #H³(G,ℤ)[2]` being a power of `2`, so
`≤ 2^6` forces `#H³(G,ℤ)[2] ≤ 2`; conversely `#H³(G,𝔽₂)[2] ≤ 2` gives
`#H²(G,𝔽₂) ≤ 2^5 · 2 = 2^6`
(`Work.ShafarevichKoch.contH2DimLe_six_of_twoTorsionH3_le_two`).

No `sorry`, no `axiom`; the only axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch.CruxOneByte

open Work.ConCohomology

/-- **`H¹(G,ℤ) = 0` for a compact group `G` acting trivially on `ℤ`.**

A locally constant additive homomorphism `φ : G → ℤ` has open kernel `K`; by compactness of `G`
the quotient `G ⧸ K` is finite, so some positive power of every `σ : G` lies in `K`, giving
`n • φ σ = φ (σ ^ n) = 0` with `n > 0`.  Since `ℤ` is torsion-free this forces `φ σ = 0` for all
`σ`, i.e. `ContAddHom G ℤ` is trivial, and `H¹(G,ℤ) ≃ ContAddHom G ℤ` for the trivial action
(`Work.ConCohomology.H1EquivContAddHom`). -/
theorem subsingleton_H1_int (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (htriv : ∀ (σ : G) (n : ℤ), σ • n = n) : Subsingleton (H1 G ℤ) := by
  -- every locally constant additive character `G → ℤ` vanishes
  have hzero : ∀ φ : ContAddHom G ℤ, ∀ σ : G, φ σ = 0 := by
    intro φ σ
    have h1 : φ 1 = 0 := by
      have h := φ.map_mul 1 1
      rw [mul_one] at h
      linarith
    -- the kernel of `φ`, as a subgroup of `G`
    let K : Subgroup G :=
      { carrier := {x : G | φ x = 0}
        mul_mem' := by
          intro a b ha hb
          show φ (a * b) = 0
          rw [φ.map_mul, show φ a = 0 from ha, show φ b = 0 from hb, add_zero]
        one_mem' := h1
        inv_mem' := by
          intro a ha
          have h := φ.map_mul a a⁻¹
          rw [mul_inv_cancel, h1, show φ a = 0 from ha, zero_add] at h
          show φ a⁻¹ = 0
          exact h.symm }
    have hKopen : IsOpen (K : Set G) := (ContAddHom.isLocallyConstant φ).isOpen_fiber 0
    haveI : Finite (G ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKopen
    obtain ⟨n, hnpos, -, hnmem⟩ :=
      Subgroup.exists_pow_mem_of_index_ne_zero (H := K)
        (Subgroup.index_ne_zero_of_finite (H := K)) σ
    have hpow : ∀ m : ℕ, φ (σ ^ m) = m • φ σ := by
      intro m
      induction m with
      | zero => rw [pow_zero]; simp [h1]
      | succ k ih => rw [pow_succ, φ.map_mul, ih, succ_nsmul]
    have hz : φ (σ ^ n) = 0 := hnmem
    have hzero' : n • φ σ = 0 := by rw [← hpow n, hz]
    have hn0 : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
    have hnn : (n : ℤ) * φ σ = 0 := by simpa [nsmul_eq_mul] using hzero'
    exact (mul_eq_zero.mp hnn).resolve_left hn0
  haveI : Subsingleton (ContAddHom G ℤ) :=
    ⟨fun φ ψ => ContAddHom.ext fun σ => by rw [hzero φ σ, hzero ψ σ]⟩
  exact ⟨fun a b => (H1EquivContAddHom htriv).injective (Subsingleton.elim _ _)⟩

/-- **`#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) = 2^5 = 32`.**

The connecting map `δ¹ : H¹(G_∅,𝔽₂) → H²(G_∅,ℤ)[2]` of the coefficient sequence
`0 → ℤ →^2 ℤ → ℤ/2 → 0` is a group homomorphism (`H2Half.connecting1_add`) with image exactly
the `2`-torsion of `H²(G_∅,ℤ)` (`exact_H2_A` together with `H2Map_zModTwoCoeffSES_f`) and kernel
the image of `H¹(G_∅,ℤ) → H¹(G_∅,𝔽₂)` (`exact_H1_C`), which is trivial because `G_∅` is compact
(`subsingleton_H1_int`).  Hence `#H²(G_∅,ℤ)[2] = #H¹(G_∅,𝔽₂) = 2^5`
(`H2Half.natCard_H1_zmodTwo_galoisGroup_Kc`), and for a finite abelian group the quotient by the
doubles has the same cardinality as the `2`-torsion
(`Work.ShafarevichKoch.card_quotient_two_eq_card_twoTorsion`). -/
theorem twoTorsionH2_card_galoisGroup_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (hfin2 : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ)) :
    Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) = 2 ^ 5 := by
  let S : CoeffSES (Work.ClassFieldTower.galoisGroup M) ℤ ℤ (ZMod 2) :=
    Work.ShafarevichKoch.ZSES (Work.ClassFieldTower.galoisGroup M)
  have htriv : ∀ (σ : Work.ClassFieldTower.galoisGroup M) (n : ℤ), σ • n = n := fun _ _ => rfl
  haveI : Subsingleton (H1 (Work.ClassFieldTower.galoisGroup M) ℤ) :=
    subsingleton_H1_int _ htriv
  -- the kernel of `δ¹` is trivial: it is the image of `H¹(G,ℤ) = 0`
  have hker : ∀ y : H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2),
      connecting1 S y = 0 → y = 0 := by
    intro y hy
    obtain ⟨z, hz⟩ := (exact_H1_C S y).mp hy
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact hz.symm
  -- `δ¹` is additive, hence so is its action on differences
  have hsub : ∀ x y : H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2),
      connecting1 S (x - y) = connecting1 S x - connecting1 S y := by
    intro x y
    have hadd := Work.ShafarevichKoch.H2Half.connecting1_add S (x - y) y
    rw [sub_add_cancel] at hadd
    exact eq_sub_of_add_eq hadd.symm
  -- `δ¹` as a map onto the `2`-torsion of `H²(G,ℤ)`
  let δ : H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2) →
      {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ // (2 : ℕ) • x = 0} :=
    fun y => ⟨connecting1 S y, by
      have hh := (exact_H2_A S (connecting1 S y)).mpr ⟨y, rfl⟩
      rwa [Work.ShafarevichKoch.H2Map_zModTwoCoeffSES_f] at hh⟩
  have hinj : Function.Injective δ := by
    intro y y' hyy
    have h1 : connecting1 S y = connecting1 S y' := congrArg Subtype.val hyy
    have h2 : connecting1 S (y - y') = 0 := by rw [hsub y y', h1, sub_self]
    have h3 : y - y' = 0 := hker (y - y') h2
    exact sub_eq_zero.mp h3
  haveI : Fintype (H2 (Work.ClassFieldTower.galoisGroup M) ℤ) := Fintype.ofFinite _
  have hEq : Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
      Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) =
      Nat.card {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ // (2 : ℕ) • x = 0} :=
    Work.ShafarevichKoch.card_quotient_two_eq_card_twoTorsion _
  refine le_antisymm (Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc M) ?_
  -- the reverse inequality, from the injectivity of `δ¹`
  rw [hEq]
  calc 2 ^ 5 = Nat.card (H1 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) :=
        (Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M).symm
    _ ≤ Nat.card {x : H2 (Work.ClassFieldTower.galoisGroup M) ℤ // (2 : ℕ) • x = 0} :=
        Nat.card_le_card_of_injective δ hinj

/-- **The crux in one-byte form.**  For `Kc = ℚ(√-30030)` and `G_∅ = Gal(Kc_∅/Kc)`, the
cohomological relation bound `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6` is equivalent to the statement that the
`2`-torsion of `H³(G_∅,ℤ)` has at most two elements.

Indeed, `#H²(G_∅,𝔽₂) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #H³(G_∅,ℤ)[2]` (the `ℤ`-power sequence) and
the first factor is exactly `2^5` (`twoTorsionH2_card_galoisGroup_Kc`); as `#H²(G_∅,𝔽₂) = 2 ^ k`
with `k ≤ 6` (`ContH2DimLe`) the bound `k ≤ 6` is precisely `2^5 · #H³(G_∅,ℤ)[2] ≤ 2^6`, i.e.
`#H³(G_∅,ℤ)[2] ≤ 2`.  Conversely `#H³(G_∅,ℤ)[2] ≤ 2` gives `#H²(G_∅,𝔽₂) ≤ 32 · 2 = 64`
(`Work.ShafarevichKoch.contH2DimLe_six_of_twoTorsionH3_le_two`). -/
theorem crux_iff_twoTorsionH3_le_two
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (hfin2 : Finite (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ))
    (hfin3 : Finite (Work.ShafarevichKoch.H3 (Work.ClassFieldTower.galoisGroup M) ℤ)) :
    (Work.RelatorRank.ContH2DimLe (Work.ClassFieldTower.galoisGroup M) 6) ↔
      (Nat.card (Work.ShafarevichKoch.twoTorsionH3 (Work.ClassFieldTower.galoisGroup M)) ≤ 2) := by
  constructor
  · -- `⇒`: the factor `#(H²(G,ℤ)/2H²(G,ℤ))` is exactly `2^5`
    intro h
    obtain ⟨k, hk, hcard⟩ := h
    have hA : Nat.card (Work.ConCohomology.H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
        Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) = 2 ^ 5 :=
      twoTorsionH2_card_galoisGroup_Kc M hfin2
    have hmul := Work.ShafarevichKoch.natCard_H2_zmodTwo_eq
      (G := Work.ClassFieldTower.galoisGroup M)
    have hle : 2 ^ 5 * Nat.card (Work.ShafarevichKoch.twoTorsionH3
        (Work.ClassFieldTower.galoisGroup M)) ≤ 2 ^ 5 * 2 := by
      calc 2 ^ 5 * Nat.card (Work.ShafarevichKoch.twoTorsionH3
              (Work.ClassFieldTower.galoisGroup M))
          = Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) ℤ ⧸
              Work.ShafarevichKoch.twoMulH2 (Work.ClassFieldTower.galoisGroup M)) *
              Nat.card (Work.ShafarevichKoch.twoTorsionH3
                (Work.ClassFieldTower.galoisGroup M)) := by rw [hA]
        _ = Nat.card (H2 (Work.ClassFieldTower.galoisGroup M) (ZMod 2)) := hmul.symm
        _ = Nat.card (Work.RelatorRank.contH2 (Work.ClassFieldTower.galoisGroup M)) := rfl
        _ = 2 ^ k := hcard
        _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk
        _ = 2 ^ 5 * 2 := by norm_num
    exact Nat.le_of_mul_le_mul_left hle (by norm_num)
  · -- `⇐`: the unconditional `H²`-half plus the one-byte `H³`-torsion bound
    intro hB
    exact Work.ShafarevichKoch.contH2DimLe_six_of_twoTorsionH3_le_two M hfin2 hfin3 hB

end Work.ShafarevichKoch.CruxOneByte
