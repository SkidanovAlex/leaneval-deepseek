import Mathlib
import Submission.Work.ConCohomology.Defs
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction

/-!
# `Work.ShafarevichKoch.CupInflationRefutation` -- the inflation is **not** injective in degree `2`

For a surjection `G ↠ Q` of (pro-)groups and a coefficient module `M` with trivial action, the
five-term exact sequence of `1 → N → G → Q → 1` reads

```
0 → H¹(Q,M) → H¹(G,M) → H¹(N,M)^Q →^{tg} H²(Q,M) →^{inf} H²(G,M) ,
```

so `ker(inf) = im(tg)`: the inflation in degree `2` is injective **iff** the transgression vanishes.
The claim recorded in `README.md` §8.7 -- that `H¹(Q) ≅ H¹(G)` forces `tg = 0`, hence
`H²(Q) ↪ H²(G)` (and therefore that `r` cannot drop under dense overgroups) -- is therefore
*false*, and this module records a machine-checked **counterexample** of the smallest possible size:

* `G = Multiplicative (ℤ/4 × ℤ/2)`, `Q = Multiplicative (ℤ/2 × ℤ/2)`, and
  `cupInflationReduction : G →* Q` the reduction of the first coordinate modulo `2`
  (`Function.Surjective`, and `d(G) = d(Q) = 2`, so `H¹(Q,𝔽₂) ≅ H¹(G,𝔽₂)`);
* `alpha : Q × Q → 𝔽₂`, `alpha ((a₁,a₂),(b₁,b₂)) = a₁ * b₁`, is the pullback of the non-trivial
  class of `H²(ℤ/2,𝔽₂)` along the first projection: it is a `2`-cocycle
  (`cupInflationAlpha_isCocycle`) and it is **not** a coboundary
  (`cupInflationAlpha_not_coboundary`);
* the pullback `alpha ∘ (ψ × ψ)` **is** a coboundary on `G`: it equals
  `d1Fun cupInflationCarryG`, where `carry = ⌊·/2⌋ : ℤ/4 → 𝔽₂` is the carry function.  This is the
  classical carry identity

  ```
  carry z - carry (x + z) + carry x = (x mod 2) * (z mod 2) ,
  ```

  i.e. the factor system of the non-split extension `𝔽₂ ↪ ℤ/4 ↠ 𝔽₂` pulled back along
  `(ℤ/2)² → ℤ/2` becomes trivial after pulling back further to `ℤ/4 × ℤ/2`.

Hence the pullback (inflation) map `H²(Q,𝔽₂) → H²(G,𝔽₂)` kills a non-zero class.  For `Kc` the same
phenomenon *must* occur with `Q = (ℤ/2)^5`: there `dim_{𝔽₂} H²(Q,𝔽₂) = 5·6/2 = 15`, while the
classical Shafarevich--Koch relation bound gives `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6` (README §25.2), so the
inflation has a kernel of dimension `≥ 9`.

## Main declarations

* `Work.ShafarevichKoch.cupInflationAlpha`, `Work.ShafarevichKoch.cupInflationCarry`,
  `Work.ShafarevichKoch.cupInflationReduction`;
* `Work.ShafarevichKoch.cupInflationAlpha_isCocycle`,
  `Work.ShafarevichKoch.cupInflationAlpha_not_coboundary`,
  `Work.ShafarevichKoch.cupInflation_pullback_coboundary`;
* `Work.ShafarevichKoch.inflation_not_injective_counterexample` (the refutation).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.ShafarevichKoch

open Work.ConCohomology

/-- The quotient group `Q = (ℤ/2)²`, written multiplicatively. -/
abbrev CupInflationQ : Type := Multiplicative (ZMod 2 × ZMod 2)

/-- The group `G = ℤ/4 × ℤ/2`, written multiplicatively. -/
abbrev CupInflationG : Type := Multiplicative (ZMod 4 × ZMod 2)

section Instances

/-- The `𝔽₂`-coefficients carry the trivial action.  (Every action of a group on `ℤ/2` is trivial,
`Work.ShafarevichKoch.smul_zmodTwo_eq`; we simply fix the corresponding instances.) -/
local instance : DistribMulAction CupInflationQ (ZMod 2) :=
  Work.RelatorRank.f2TrivialAction CupInflationQ
local instance : DistribMulAction CupInflationG (ZMod 2) :=
  Work.RelatorRank.f2TrivialAction CupInflationG

/-- `toAdd` is a section of `ofAdd`, as a `simp` lemma. -/
@[simp] lemma cupInflationToAdd_ofAdd {α : Type*} [AddMonoid α] (x : α) :
    Multiplicative.toAdd (Multiplicative.ofAdd x) = x := rfl

/-- `ofAdd` is a section of `toAdd`. -/
@[simp] lemma cupInflationOfAdd_toAdd (y : CupInflationQ) :
    Multiplicative.ofAdd (Multiplicative.toAdd y) = y := rfl

/-- `toAdd` turns the product in `Multiplicative` into a sum. -/
@[simp] lemma cupInflationToAdd_mul {α : Type*} [AddMonoid α] (a b : Multiplicative α) :
    Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b := rfl

/-- The reduction `ℤ/4 × ℤ/2 → ℤ/2 × ℤ/2`, additively. -/
def cupInflationReductionAdd : ZMod 4 × ZMod 2 →+ ZMod 2 × ZMod 2 where
  toFun p := ((ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) p.1, p.2)
  map_zero' := rfl
  map_add' := by
    intro a b
    ext <;> simp

/-- **The reduction `ℤ/4 × ℤ/2 ↠ ℤ/2 × ℤ/2`** (reduce the first coordinate modulo `2`). -/
def cupInflationReduction : CupInflationG →* CupInflationQ where
  toFun g := Multiplicative.ofAdd (cupInflationReductionAdd (Multiplicative.toAdd g))
  map_one' := by
    show Multiplicative.ofAdd (cupInflationReductionAdd (Multiplicative.toAdd 1)) = 1
    simp
  map_mul' := by
    intro a b
    exact congrArg Multiplicative.ofAdd
      (map_add cupInflationReductionAdd (Multiplicative.toAdd a) (Multiplicative.toAdd b))

/-- The additive reduction is surjective. -/
theorem cupInflationReductionAdd_surjective : Function.Surjective cupInflationReductionAdd := by
  intro z
  obtain ⟨a, ha⟩ : ∃ a : ZMod 4, (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2)) a = z.1 :=
    ⟨(z.1.val : ℕ), by simp [ZMod.castHom_apply]⟩
  exact ⟨(a, z.2), by
    apply Prod.ext
    · simpa [cupInflationReductionAdd] using ha
    · simp [cupInflationReductionAdd]⟩

/-- **The reduction `ℤ/4 × ℤ/2 ↠ ℤ/2 × ℤ/2` is surjective.** -/
theorem cupInflationReduction_surjective : Function.Surjective cupInflationReduction := by
  intro y
  obtain ⟨x, hx⟩ := cupInflationReductionAdd_surjective (Multiplicative.toAdd y)
  exact ⟨Multiplicative.ofAdd x, by
    show Multiplicative.ofAdd (cupInflationReductionAdd (Multiplicative.toAdd (Multiplicative.ofAdd x))) = y
    rw [cupInflationToAdd_ofAdd, hx, cupInflationOfAdd_toAdd]⟩

/-- The first generator `x₁` of `Q = (ℤ/2)²`. -/
def cupInflationX : CupInflationQ := Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)

/-- **The `2`-cocycle of `Q = (ℤ/2)²`**: `alpha ((a₁,a₂),(b₁,b₂)) = a₁ * b₁`, the pullback of the
non-trivial class of `H²(ℤ/2,𝔽₂)` along the first projection. -/
def cupInflationAlpha (p : CupInflationQ × CupInflationQ) : ZMod 2 :=
  (Multiplicative.toAdd p.1).1 * (Multiplicative.toAdd p.2).1

/-- **The carry function** `ℤ/4 → 𝔽₂`: `carry x = ⌊x/2⌋`, i.e. `0` on `{0,1}` and `1` on `{2,3}`. -/
def cupInflationCarry (x : ZMod 4) : ZMod 2 := if x = 0 ∨ x = 1 then 0 else 1

/-- The carry function on `G = ℤ/4 × ℤ/2`, read on the first coordinate. -/
def cupInflationCarryG (g : CupInflationG) : ZMod 2 :=
  cupInflationCarry (Multiplicative.toAdd g).1

/-- **The carry identity**: `carry z - carry (x+z) + carry x = (x mod 2) * (z mod 2)`.  This is
the statement that the factor system of the non-split extension `𝔽₂ ↪ ℤ/4 ↠ 𝔽₂`, pulled back to
`ℤ/2 × ℤ/2`, is the coboundary of `carry`. -/
theorem cupInflationCarry_identity (x z : ZMod 4) :
    cupInflationCarry z - cupInflationCarry (x + z) + cupInflationCarry x
      = (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) x)
        * (ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) z) := by
  revert x z
  decide

/-- `alpha` is a `2`-cocycle for the trivial action. -/
theorem cupInflationAlpha_isCocycle : IsCocycle2 cupInflationAlpha := by
  intro σ τ ρ
  simp only [cupInflationAlpha, smul_zmodTwo_eq, cupInflationToAdd_mul, Prod.fst_add, Prod.snd_add]
  ring

/-- **`alpha` is not a coboundary.**  If `d1Fun f = alpha` then evaluating at the four pairs built
from the generators of `Q = (ℤ/2)²` gives `0 = 1` in `𝔽₂`. -/
theorem cupInflationAlpha_not_coboundary (f : CupInflationQ → ZMod 2) :
    d1Fun f ≠ cupInflationAlpha := by
  intro h
  -- the two evaluations of `d¹f = alpha`, at `(1,1)` and at `(x₁,x₁)`
  have e1 : f 1 - f ((1 : CupInflationQ) * 1) + f 1 = cupInflationAlpha ((1 : CupInflationQ), 1) := by
    have h' := congrFun h ((1 : CupInflationQ), 1)
    simpa [d1Fun_apply, smul_zmodTwo_eq] using h'
  have e2 : f cupInflationX - f (cupInflationX * cupInflationX) + f cupInflationX
      = cupInflationAlpha (cupInflationX, cupInflationX) := by
    have h' := congrFun h (cupInflationX, cupInflationX)
    simpa [d1Fun_apply, smul_zmodTwo_eq] using h'
  -- the (closed) values of the right hand sides and of the products
  have c1 : cupInflationAlpha ((1 : CupInflationQ), 1) = (0 : ZMod 2) := by decide
  have c2 : cupInflationAlpha (cupInflationX, cupInflationX) = (1 : ZMod 2) := by decide
  have m1 : (1 : CupInflationQ) * 1 = 1 := by decide
  have m2 : cupInflationX * cupInflationX = 1 := by decide
  rw [c2, m2] at e2
  -- `(1,1)`: `f 1 = 0`;  `(x₁,x₁)`: `f x₁ - f 1 + f x₁ = 1`, i.e. `0 = 1` by the char-2 relation
  have hf1 : f (1 : CupInflationQ) = (0 : ZMod 2) := by
    rw [c1, m1] at e1
    simpa using e1
  have hsum : f cupInflationX + f cupInflationX = (1 : ZMod 2) := by
    rw [hf1] at e2
    simpa using e2
  exact one_ne_zero (hsum.symm.trans (CharTwo.add_self_eq_zero (f cupInflationX)))

/-- **The pullback of `alpha` along the reduction is a coboundary**: it is the coboundary of the
carry function on the first coordinate (the carry identity, read on `G = ℤ/4 × ℤ/2`). -/
theorem cupInflation_pullback_coboundary :
    (fun p : CupInflationG × CupInflationG =>
        cupInflationAlpha (cupInflationReduction p.1, cupInflationReduction p.2))
      = d1Fun cupInflationCarryG := by
  funext p
  obtain ⟨a, b⟩ := p
  simp only [cupInflationAlpha, cupInflationCarryG, d1Fun_apply, smul_zmodTwo_eq,
    cupInflationReduction, cupInflationReductionAdd, cupInflationToAdd_ofAdd,
    cupInflationToAdd_mul, Prod.fst_add, Prod.snd_add]
  exact (cupInflationCarry_identity (Multiplicative.toAdd a).1 (Multiplicative.toAdd b).1).symm

/-- **The inflation in degree `2` is not injective**: for the surjection
`ℤ/4 × ℤ/2 ↠ ℤ/2 × ℤ/2` there is a `2`-cocycle of the quotient which is not a coboundary and whose
pullback to `G` is a coboundary.  (This refutes the argument recorded in `README.md` §8.7 that
`H¹(Q) ≅ H¹(G)` forces `H²(Q) ↪ H²(G)`.) -/
theorem inflation_not_injective_counterexample :
    ∃ alpha : CupInflationQ × CupInflationQ → ZMod 2,
      IsCocycle2 alpha ∧ (∀ f : CupInflationQ → ZMod 2, d1Fun f ≠ alpha) ∧
      ∃ ψ : CupInflationG →* CupInflationQ, Function.Surjective ψ ∧
        ∃ f : CupInflationG → ZMod 2, (fun p => alpha (ψ p.1, ψ p.2)) = d1Fun f :=
  ⟨cupInflationAlpha, cupInflationAlpha_isCocycle, cupInflationAlpha_not_coboundary,
    cupInflationReduction, cupInflationReduction_surjective,
    cupInflationCarryG, cupInflation_pullback_coboundary⟩

end Instances

end Work.ShafarevichKoch
