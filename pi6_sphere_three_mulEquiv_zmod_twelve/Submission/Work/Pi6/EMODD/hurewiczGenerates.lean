import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Stems.HurewiczMapNatural
import Submission.Work.Stems.HurewiczNeutralAgree
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMODD

open CategoryTheory

noncomputable section

/-- **The Hurewicz map on integral powers.**  For a class `g : π₂(X,x)` and `m : ℤ`, the Hurewicz
class of `g ^ m` is `m` times the Hurewicz class of `g`.

Proof: `Work.Stems.hurewiczHom 1 x` (`Stems/HurewiczMapNatural.lean`) packages the Hurewicz map
`π₂(X,x) → H₂(X;ℤ)` as an additive homomorphism out of `Additive (π₂(X,x))`, and
`Work.Stems.hurewiczHom_eq_hurewiczMapN` (`Stems/HurewiczNeutralAgree.lean`) identifies its
underlying function with `Work.Stems.hurewiczMapN`.  Additivity in the exponent is then
`Additive.ofMul_zpow` (`ofMul (g ^ m) = m • ofMul g`) followed by `map_zsmul`. -/
lemma hurewiczMapN_zpow {X : Type} [TopologicalSpace X] (x : X)
    (g : HomotopyGroup (Fin 2) X x) (m : ℤ) :
    Work.Stems.hurewiczMapN 2 (by norm_num) x (g ^ m) =
      m • Work.Stems.hurewiczMapN 2 (by norm_num) x g := by
  calc Work.Stems.hurewiczMapN 2 (by norm_num) x (g ^ m)
      = Work.Stems.hurewiczHom 1 x (Additive.ofMul (g ^ m)) := rfl
    _ = Work.Stems.hurewiczHom 1 x (m • Additive.ofMul g) := by rw [ofMul_zpow]
    _ = m • Work.Stems.hurewiczHom 1 x (Additive.ofMul g) := map_zsmul _ _ _
    _ = m • Work.Stems.hurewiczMapN 2 (by norm_num) x g := rfl

/-- **The Hurewicz image of a free generator of `π₂` freely generates `H₂(-;ℤ)`.** If `g : π₂(X,x)` is a *free* generator (`∀ a, ∃! m : ℤ, a = g^m`) of a `1`-connected space `X` (so that the Hurewicz map `h : π₂(X,x) → H₂(X;ℤ)` is bijective — passed as the hypothesis `hbij`), then `h g` freely generates the `ℤ`-module `H₂(X;ℤ)`: `∀ z, ∃! n : ℤ, z = n • h g`.

(Route: the additive Hurewicz homomorphism `Work.Stems.hurewiczHom 1 x` satisfies `h (a^m) = m • h a` (`ofMul_zpow` + `map_zsmul`, using `hurewiczHom_eq_hurewiczMapN` from `Submission/Work/Stems/HurewiczNeutralAgree.lean`); with `hbij` one gets surjectivity of the map `ℤ → H₂, n ↦ n • h g` and injectivity from `hbij` + the uniqueness of the exponent of `g`.)

Naming note: the file's namespace is `Work.Pi6.EMODD` (module `Submission.Work.Pi6.EMODD.hurewiczGenerates`). Helper lemmas above the statement are welcome. -/
theorem hurewiczGenerates {X : Type} [TopologicalSpace X] (x : X)
    (hbij : Function.Bijective (Work.Stems.hurewiczMapN 2 (by norm_num) x))
    (g : HomotopyGroup (Fin 2) X x)
    (hg : ∀ a : HomotopyGroup (Fin 2) X x, ∃! m : ℤ, a = g ^ m) :
    ∀ z : Work.Pi6.HR ℤ X 2,
      ∃! n : ℤ, z = n • Work.Stems.hurewiczMapN 2 (by norm_num) x g := by
  intro z
  -- Every class is a power of `g`, so every homology class is an integral multiple of `h g`.
  obtain ⟨a, ha⟩ := hbij.2 z
  obtain ⟨m, hm⟩ := hg a
  refine ⟨m, ?_, ?_⟩
  · rw [← ha, hm.1, hurewiczMapN_zpow]
  · -- Uniqueness: two exponents giving the same multiple would give two exponents of the same
    -- element in `π₂`, contradicting the uniqueness in `hg`.
    intro n hn
    have h1 : a = g ^ n := by
      apply hbij.1
      rw [ha, hn, hurewiczMapN_zpow]
    exact hm.2 n h1

end

end Work.Pi6.EMODD
