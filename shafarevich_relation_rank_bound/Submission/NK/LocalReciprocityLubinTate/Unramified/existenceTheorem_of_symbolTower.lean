import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.NK.LocalCFT.Reduction.Defs
import Submission.NK.LocalReciprocityLubinTate.Tower

/-!
# The existence theorem from a general Lubin–Tate symbol tower

`NK.LocalReciprocityLubinTate.LubinTateTowerGen` records the norm groups of the Lubin–Tate levels
`E_{m,n}` of a tower whose *unramified* degree is an arbitrary parameter `a : ℕ → ℕ`:
`N_{E_{m,n}/F} E_{m,n}ˣ = ⟨π^{a m}⟩ · U^{n+1}`.

This file derives from that data the **existence theorem** of local class field theory,
`NK.LocalCFT.ExistenceTheorem F F'`: every finite-index subgroup `M ≤ Fˣ` contains the norm group of
a finite abelian extension `L/F` inside `F^{ab}`.

The argument is the classical one (Serre, *Local Fields*, Ch. XI §2; Neukirch, *Algebraic Number
Theory*, V §4):

* a finite-index subgroup `M` contains a positive power `π ^ k` of the uniformiser
  (`NK.LocalReciprocityLubinTate.exists_pow_mem_of_finiteIndex`), and
* `M` contains `U ^ n` for large `n`, because the higher unit filtration is cofinal among the
  finite-index subgroups of `Fˣ` (`hcof`),

so `M` contains `⟨π^k⟩ · U^{n+1}`.  The two parameters are reconciled by the *growth* hypothesis
`hgrow`: for the exponent `k` of the required power of `π` there is an index `m` with `k ∣ a m`, so
that `π^{a m} = (π^k)^{a m / k} ∈ M`.  Then `⟨π^{a m}⟩ · U^{n+1} ≤ M` and the level `E_{m,n}` has norm
group contained in `M`.

## Main result

* `NK.LocalReciprocityLubinTate.Unramified.existenceTheorem_of_symbolTower`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.Unramified

universe u v

/-- **The existence theorem of local class field theory from a Lubin–Tate tower over an arbitrary
unramified parameter.**

Let `F` be a nonarchimedean local field, `π` a uniformiser, `a : ℕ → ℕ` a divisibility chain in the
sense that every positive `d` divides some `a m` (`hgrow`), and let `T` be the Lubin–Tate tower
whose level `E_{m,n}` has norm group `⟨π^{a m}⟩ · U^{n+1}` with `U = higherUnits F` cofinal among the
finite-index subgroups of `Fˣ` (`hcof`).

Then every finite-index subgroup of `Fˣ` contains the norm group of a finite abelian level of
`F^{ab}`, i.e. the existence theorem holds for `F`. -/
theorem existenceTheorem_of_symbolTower {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {a : ℕ → ℕ}
    (T : NK.LocalReciprocityLubinTate.LubinTateTowerGen F F' π a
      (NK.LocalReciprocityLubinTate.higherUnits F) (NK.LocalReciprocityLubinTate.residueCard F))
    (hgrow : ∀ d : ℕ, d ≠ 0 → ∃ m : ℕ, d ∣ a m)
    (hcof : ∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n : ℕ, higherUnits F n ≤ M) :
    NK.LocalCFT.ExistenceTheorem F F' := by
  intro M hM
  -- (1) `M` contains a positive power of the uniformiser `π`.
  obtain ⟨k, hk, hkπ⟩ :=
    NK.LocalReciprocityLubinTate.exists_pow_mem_of_finiteIndex M hM π
  -- (2) `M` contains a higher unit group `U ^ n`.
  obtain ⟨n, hn⟩ := hcof M hM
  -- (3) the growth hypothesis lets us pick a level whose `π`-power lies in `M`.
  obtain ⟨m, hm⟩ := hgrow k hk.ne'
  refine ⟨T.level m n, T.finiteDimensional m n, T.normal m n, T.commutative m n, ?_⟩
  -- the norm group of `E_{m,n}` is `⟨π^{a m}⟩ · U^{n+1} ≤ M`
  rw [T.normGroup_eq m n]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    obtain ⟨j, hj⟩ := hm
    rw [hj, pow_mul]
    exact M.pow_mem hkπ j
  · exact (NK.LocalReciprocityLubinTate.higherUnits_antitone F (Nat.le_succ n)).trans hn

end NK.LocalReciprocityLubinTate.Unramified
