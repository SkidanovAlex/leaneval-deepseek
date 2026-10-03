import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.Rat.Weak.rho_ofSubgroup_mem
import Submission.Work.ORHughesFree.Rat.Weak.A_add_left
import Submission.Work.ORHughesFree.Rat.WordModel.Defs
import Submission.Work.ORHughesFree.Rat.WordModel.sigma_rho

/-!
# Structural facts about the `A`-families

`Rat.F α = {V ≤ U | α ∈ Rat(V)·U}` is the family whose least element the target theorem
(`Rat.exists_source_subgroup_weak`) has to produce.  This file collects the structural facts
about it and about the *one-sided* family

* `Weak.FA y = {V | y ∈ Rat.A V}` ("`y ∈ Rat(V)`"),

that the eventual proof of the target theorem uses.

The content:

* `mem_FA_iff_SV` : `V ∈ FA y ↔ rho y ∈ SV V` — the word model detects `Rat(V) ⊆ Rat(U)`.
* `mem_FA_iff_words` : `FA y` is determined by the `FA`s of the words in the `rho`-support of
  `y` (this is what reduces the theorem to *words*).
* `FA_add` : `FA (x + y) = FA x ∩ FA y` (additive purity, `A_add_left`, plus closure under `+`).
* `F_eq_iUnion_FA` : `Rat.F α = ⋃ u, FA (α * φ u)`.
* `F_add_subset` : `Rat.F (x + y) ⊆ Rat.F x ∩ Rat.F y`.
* `FA_mul_splitting` : `FA (a*b) ⊇ ⋃ x, (FA (a * φ x) ∩ FA (φ x⁻¹ * b))`, the identity
  `(a φ x)(φ x⁻¹ b) = a b`.
-/

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel

variable {U : Type} [Group U]

/-- The family of subgroups `V` with `y ∈ Rat(V)` (i.e. `y ∈ Rat.A V`). -/
def FA (y : RatU U) : Set (Subgroup U) := {V | y ∈ Rat.A V}

/-- `FA` is monotone in the subgroup. -/
theorem FA_mono {y : RatU U} {V W : Subgroup U} (h : V ≤ W) (hV : V ∈ FA y) : W ∈ FA y :=
  Rat.A_mono h hV

/-- `ofGroup u * ofGroup u⁻¹ = 1`. -/
theorem ofGroup_mul_inv (u : U) : RatU.ofGroup u * RatU.ofGroup u⁻¹ = 1 := by
  rw [← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one]

/-- **The word model detects the `A`-families**: `y ∈ Rat(V)` iff `rho y` lies in the `V`-part of
`ℕ[U ♮ X]`. -/
theorem mem_FA_iff_SV (y : RatU U) (V : Subgroup U) : V ∈ FA y ↔ rho y ∈ SV V := by
  constructor
  · intro hy
    obtain ⟨β, rfl⟩ := hy
    exact rho_ofSubgroup_mem V β
  · intro hy
    have h2 : sigma (rho y) ∈ Rat.A V := sigma_mem_A hy
    rwa [sigma_rho y] at h2

/-- **The `A`-family of `y` is determined by the words in the `rho`-support of `y`.** -/
theorem mem_FA_iff_words (y : RatU U) (V : Subgroup U) :
    V ∈ FA y ↔ ∀ w ∈ (rho y).coeff.support, Mval w ∈ Rat.A V := by
  rw [mem_FA_iff_SV]
  exact Iff.rfl

/-- A sum lies in `Rat(V)` iff both summands do (`Rat.A V` is additively pure, `A_add_left`, and
closed under addition). -/
theorem FA_add (x y : RatU U) : FA (x + y) = FA x ∩ FA y := by
  ext V
  constructor
  · intro h
    refine ⟨A_add_left h, ?_⟩
    exact A_add_left (x := y) (y := x) (by rwa [add_comm] at h)
  · rintro ⟨hx, hy⟩
    exact (ASub V).add_mem hx hy

/-- `Rat.F α` is the union of the `A`-families of the right translates `α · φ u`. -/
theorem F_eq_iUnion_FA (α : RatU U) : Rat.F α = ⋃ u : U, FA (α * RatU.ofGroup u) := by
  ext V
  rw [Set.mem_iUnion, Rat.mem_F_iff]
  constructor
  · rintro ⟨β, u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    have h : α * RatU.ofGroup u⁻¹ = RatU.ofSubgroup V β := by
      calc α * RatU.ofGroup u⁻¹
          = RatU.ofSubgroup V β * RatU.ofGroup u * RatU.ofGroup u⁻¹ := by rw [hu]
        _ = RatU.ofSubgroup V β * (RatU.ofGroup u * RatU.ofGroup u⁻¹) := by rw [mul_assoc]
        _ = RatU.ofSubgroup V β := by rw [ofGroup_mul_inv, mul_one]
    rw [h]; exact ⟨β, rfl⟩
  · rintro ⟨u, β, hβu⟩
    refine ⟨β, u⁻¹, ?_⟩
    rw [hβu]
    calc α * RatU.ofGroup u * RatU.ofGroup u⁻¹
        = α * (RatU.ofGroup u * RatU.ofGroup u⁻¹) := by rw [mul_assoc]
      _ = α := by rw [ofGroup_mul_inv, mul_one]

/-- `Rat.F` is subadditive: `F (x + y) ⊆ F x ∩ F y`. -/
theorem F_add_subset (x y : RatU U) : Rat.F (x + y) ⊆ Rat.F x ∩ Rat.F y := by
  intro V hV
  rw [Rat.mem_F_iff] at hV
  obtain ⟨β, u, hu⟩ := hV
  have hsum : (x + y) * RatU.ofGroup u⁻¹ ∈ Rat.A V := by
    have h : (x + y) * RatU.ofGroup u⁻¹ = RatU.ofSubgroup V β := by
      calc (x + y) * RatU.ofGroup u⁻¹
          = RatU.ofSubgroup V β * RatU.ofGroup u * RatU.ofGroup u⁻¹ := by rw [hu]
        _ = RatU.ofSubgroup V β * (RatU.ofGroup u * RatU.ofGroup u⁻¹) := by rw [mul_assoc]
        _ = RatU.ofSubgroup V β := by rw [ofGroup_mul_inv, mul_one]
    rw [h]; exact ⟨β, rfl⟩
  have hxy : x * RatU.ofGroup u⁻¹ + y * RatU.ofGroup u⁻¹ ∈ Rat.A V := by
    rwa [add_mul] at hsum
  have hx : x * RatU.ofGroup u⁻¹ ∈ Rat.A V := A_add_left hxy
  have hy : y * RatU.ofGroup u⁻¹ ∈ Rat.A V :=
    A_add_left (x := y * RatU.ofGroup u⁻¹) (y := x * RatU.ofGroup u⁻¹)
      (by rwa [add_comm] at hxy)
  constructor
  · obtain ⟨β', hβ'⟩ := hx
    refine ⟨β', u, ?_⟩
    rw [hβ']
    calc x * RatU.ofGroup u⁻¹ * RatU.ofGroup u
        = x * (RatU.ofGroup u⁻¹ * RatU.ofGroup u) := by rw [mul_assoc]
      _ = x := by rw [← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, mul_one]
  · obtain ⟨β', hβ'⟩ := hy
    refine ⟨β', u, ?_⟩
    rw [hβ']
    calc y * RatU.ofGroup u⁻¹ * RatU.ofGroup u
        = y * (RatU.ofGroup u⁻¹ * RatU.ofGroup u) := by rw [mul_assoc]
      _ = y := by rw [← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, mul_one]

/-- **The splitting identity.**  For all `a b : Rat(U)` and all `x : U`,
`(a · φ x) · (φ x⁻¹ · b) = a · b`, so `FA (a*b)` contains the intersection of the `A`-families of
the two factors of any such splitting. -/
theorem FA_mul_splitting (a b : RatU U) :
    (⋃ x : U, (FA (a * RatU.ofGroup x) ∩ FA (RatU.ofGroup x⁻¹ * b))) ⊆ FA (a * b) := by
  intro V hV
  rw [Set.mem_iUnion] at hV
  obtain ⟨x, hax, hxb⟩ := hV
  have h : (a * RatU.ofGroup x) * (RatU.ofGroup x⁻¹ * b) = a * b := by
    calc (a * RatU.ofGroup x) * (RatU.ofGroup x⁻¹ * b)
        = a * (RatU.ofGroup x * (RatU.ofGroup x⁻¹ * b)) := by rw [mul_assoc]
      _ = a * ((RatU.ofGroup x * RatU.ofGroup x⁻¹) * b) := by rw [mul_assoc]
      _ = a * (1 * b) := by rw [ofGroup_mul_inv]
      _ = a * b := by rw [one_mul]
  rw [← h]
  exact (ASub V).mul_mem hax hxb

end Work.ORHughesFree.Rat.Weak
