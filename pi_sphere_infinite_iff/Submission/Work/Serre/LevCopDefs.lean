import Mathlib

/-!
# The "levelwise coproduct" of a family of homological complexes

For a family `K i` of homological complexes of `ℤ`-modules, the coproduct `∐ i, K i` in the
category of homological complexes is computed degreewise: its `n`-th object is the coproduct of
the `n`-th objects and its differential is the coproduct of the differentials.  This file defines
the complex `levCop K` which *is* that levelwise object (so that the identification with the
genuine coproduct `∐ i, K i` becomes a clean statement), together with the degreewise inclusions
`levCopι K i : K i ⟶ levCop K`.
-/

open CategoryTheory Limits

namespace Work.Serre

noncomputable section

/-- The levelwise coproduct of a family of homological complexes: the complex whose `n`-th object
is the coproduct of the `n`-th objects of the `K i`, and whose differential is the coproduct of
the differentials. -/
def levCop {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c) :
    HomologicalComplex (ModuleCat ℤ) c where
  X n := ∐ fun i => (K i).X n
  d n m := Limits.Sigma.map (fun i => (K i).d n m)
  shape n m h := by
    rw [show (fun i => (K i).d n m) = (fun _ => 0) from
      funext (fun i => (K i).shape n m h)]
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_map]
    simp
  d_comp_d' n m l _ _ := by
    rw [Limits.Sigma.map_comp_map]
    rw [show (fun i => (K i).d n m ≫ (K i).d m l) = (fun _ => 0) from
      funext (fun i => (K i).d_comp_d n m l)]
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_map]
    simp

@[simp]
lemma levCop_X {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n : ℕ) : (levCop K).X n = ∐ fun i => (K i).X n := rfl

@[simp]
lemma levCop_d {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n m : ℕ) : (levCop K).d n m = Limits.Sigma.map (fun i => (K i).d n m) := rfl

/-- The degreewise inclusion of `K i` into the levelwise coproduct. -/
def levCopι {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (i : ι) : K i ⟶ levCop K where
  f n := Limits.Sigma.ι (fun j => (K j).X n) i
  comm' n m _ := Limits.Sigma.ι_map (fun j => (K j).d n m) i

@[simp]
lemma levCopι_f {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (i : ι) (n : ℕ) : (levCopι K i).f n = Limits.Sigma.ι (fun j => (K j).X n) i := rfl

/-- The levelwise coproduct of the short complexes `(K i).sc n`: the short complex whose objects
are the coproducts of the corresponding objects and whose maps are the coproducts of the maps. -/
abbrev levShort {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n : ℕ) : ShortComplex (ModuleCat ℤ) where
  X₁ := ∐ fun i => ((K i).sc n).X₁
  X₂ := ∐ fun i => ((K i).sc n).X₂
  X₃ := ∐ fun i => ((K i).sc n).X₃
  f := Limits.Sigma.map (fun i => ((K i).sc n).f)
  g := Limits.Sigma.map (fun i => ((K i).sc n).g)
  zero := by
    rw [Limits.Sigma.map_comp_map]
    rw [show (fun i => ((K i).sc n).f ≫ ((K i).sc n).g) = (fun _ => 0) from
      funext (fun i => ((K i).sc n).zero)]
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_map]
    simp

@[simp]
lemma levShort_X₁ {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n : ℕ) : (levShort K n).X₁ = ∐ fun i => ((K i).sc n).X₁ := rfl

@[simp]
lemma levShort_X₂ {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n : ℕ) : (levShort K n).X₂ = ∐ fun i => ((K i).sc n).X₂ := rfl

@[simp]
lemma levShort_X₃ {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n : ℕ) : (levShort K n).X₃ = ∐ fun i => ((K i).sc n).X₃ := rfl

@[simp]
lemma levShort_f {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n : ℕ) : (levShort K n).f = Limits.Sigma.map (fun i => ((K i).sc n).f) := rfl

@[simp]
lemma levShort_g {ι : Type} {c : ComplexShape ℕ} (K : ι → HomologicalComplex (ModuleCat ℤ) c)
    (n : ℕ) : (levShort K n).g = Limits.Sigma.map (fun i => ((K i).sc n).g) := rfl

end

end Work.Serre
