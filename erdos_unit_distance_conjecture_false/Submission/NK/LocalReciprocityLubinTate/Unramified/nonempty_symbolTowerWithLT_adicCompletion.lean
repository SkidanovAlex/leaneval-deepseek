import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerWithLT
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion

/-!
# A Lubin–Tate symbol tower together with its Lubin–Tate levels, for `𝔭`-adic completions

`NK.LocalReciprocityLubinTate.LubinTateSymbolTowerWithLT` extends the Lubin–Tate symbol tower
`LubinTateSymbolTower` by the *Lubin–Tate levels* `F(Λ_{π^n})`, the canonical Lubin–Tate symbol on
them, and the identification of the tower symbol at level `E_{m,n}` with the product of the
unramified symbol and the Lubin–Tate symbol at level `n + 1`.

This file produces such an extended tower for `F = Q.adicCompletion K`, given any uniformiser `π`,
out of the *already constructed* symbol tower
`NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion`.

The point is that the extra Lubin–Tate data is already present in the symbol tower: the norm groups
of the tower are `N_{E_{m,n}/F} E_{m,n}ˣ = ⟨π^{(m+1)!}⟩ · U^{n+1}`, so the level with `m = 0` is

`E_{0,n} = F^{ur}_1 · F(Λ_{π^{n+1}}) = F(Λ_{π^{n+1}})`,

the pure Lubin–Tate level, whose norm group is exactly Honda's `⟨π⟩ · U^{n+1}`.  Hence we may take

* `ltLevel n`  `= E_{0,n-1}` — the Lubin–Tate level `F(Λ_{π^n})` for `n ≥ 1` (and `E_{0,0}` for `n = 0`);
* `ltSymbol n` `= symbol 0 (n-1)` — the Artin symbol of that level, whose kernel is Honda's
  `⟨π⟩ · U^n = zpowers π ⊔ higherUnits F n` because `(m+1)! = 1` for `m = 0` and `U^{n+1}` with `n = k`
  is `U^{(k+1)}`;

and the two remaining requirements are then immediate from the tower axioms: `E_{0,n} ≤ E_{m,n}` is
`mono` (the unramified degree is `≤`), and `symbol m n x` restricted to `E_{0,n}` is `symbol 0 n x`
by `symbol_compat`.  So no new input from Lubin–Tate theory is needed.

## Main result

* `NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTowerWithLT_adicCompletion`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate.Unramified

theorem nonempty_symbolTowerWithLT_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {π : (Q.adicCompletion K)ˣ}
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)) :
    Nonempty (NK.LocalReciprocityLubinTate.LubinTateSymbolTowerWithLT (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
      (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
      (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K))) := by
  classical
  obtain ⟨T⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion (K := K) Q hπ
  -- The Lubin–Tate level `F(Λ_{π^n})` is the `m = 0` level `E_{0,n-1}` of the tower, and the
  -- Lubin–Tate symbol is the corresponding level symbol `symbol 0 (n-1)`.
  refine ⟨{ T with
    ltLevel := fun n => match n with
      | 0 => T.level 0 0
      | (k + 1) => T.level 0 k
    ltSymbol := fun n => match n with
      | 0 => T.symbol 0 0
      | (k + 1) => T.symbol 0 k
    ltLevel_le := ?_
    ltSymbol_ker := ?_
    symbol_apply_lt := ?_ }⟩
  · -- `ltLevel (n+1) = E_{0,n} ≤ E_{m,n}`
    intro m n
    exact T.mono (Nat.zero_le m) le_rfl
  · -- Honda's reciprocity law, read off from the norm group of `E_{0,n}`
    intro n hn
    cases n with
    | zero => omega
    | succ k =>
      rw [T.symbol_ker 0 k, T.normGroup_eq 0 k]
      simp
  · -- the tower symbol restricts to the Lubin–Tate symbol
    intro m n x y
    exact congrArg (fun z : ↥(T.level m n) => (z : SeparableClosure (Q.adicCompletion K)))
      (T.symbol_compat (m := 0) (n := n) (m' := m) (n' := n) (Nat.zero_le m) le_rfl x y)

end NK.LocalReciprocityLubinTate.Unramified
