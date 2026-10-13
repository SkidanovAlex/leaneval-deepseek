/-
  WilC4 / `paramBnd_definable`.

  If `S ⊆ ℝ^{n+1}` is `∅`-definable in `LRc`, then so is the set of parameters `p` for which
  `p 0` is a *boundary point* (`Work.WilC2.IsBnd`) of the fibre
  `Pfib1 S p = {x | Fin.cons x (Fin.tail p) ∈ S}`.

  This is the parametrised form of `Work.WilC2.bnd_definable_alt`: there the definable set `D`
  is fixed and the point `x` is the single free variable, here the definable set `Pfib1 S p`
  varies with the parameter tuple `p` and the point is the first coordinate `p 0` of `p`.  The
  transcription is the same first-order one:

  * `IsBnd D x` is the complement of `x ∈ InteriorSet D ∪ x ∈ InteriorSet Dᶜ`, and
    `Pfib1 Sᶜ p = (Pfib1 S p)ᶜ`, so it suffices to show that the *parametric* interior
    `p ↦ InteriorSet (Pfib1 S p)` is definable.
  * `x ∈ InteriorSet D` is `∃ a b, a < x ∧ x < b ∧ Ioo a b ⊆ D` with `x = p 0`; writing the
    quadruple `(p, a, b, z)` on the index type `PBndQ n = (Fin (n+1) ⊕ Fin 2) ⊕ Fin 1`, the
    relation "`z ∈ (a,b)` and `Fin.cons z (Fin.tail p) ∉ S`" is definable: the membership in `S`
    is pulled back along the index map `pBndIdx n : Fin (n+1) → PBndQ n` which reindexes
    `(z, p₁, …, pₙ)` as the fibre point `Fin.cons z (Fin.tail p)`.  Complementing and applying
    `Set.Definable.forall_of_finite` turns it into `Ioo a b ⊆ Pfib1 S p`, and projecting the two
    endpoints away with `Set.Definable.exists_of_finite` gives the parametric interior.

  All quantifiers are finite (`Fin 1`, `Fin 2`) except the `∀ z`, which is handled by
  `forall_of_finite`; the order is `LRc`-definable through `Work.WilC2.definable_lt`
  (every nonnegative real is a square).
-/
import Mathlib
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC2.bnd_definable_alt

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The index types and the reindexing map -/

/-- The index type of the quadruples `(p, a, b, z)`: the parameter tuple `p` on `Fin (n+1)`, the
two endpoints `a`, `b` of an interval on `Fin 2`, and the point `z` on `Fin 1`. -/
abbrev PBndQ (n : ℕ) : Type := (Fin (n + 1) ⊕ Fin 2) ⊕ Fin 1

/-- The index type of the triples `(p, a, b)`. -/
abbrev PBndT (n : ℕ) : Type := Fin (n + 1) ⊕ Fin 2

/-- The map reindexing the tuple `(z, p₁, …, pₙ)` (the fibre point `z` followed by the parameters
`p`) as a tuple on `PBndQ n`. -/
def pBndIdx (n : ℕ) : Fin (n + 1) → PBndQ n :=
  Fin.cons (Sum.inr (0 : Fin 1)) (fun j : Fin n => Sum.inl (Sum.inl (Fin.succ j)))

/-- The parameter tuple read off a tuple on `PBndQ n`. -/
def pBndOff {n : ℕ} (w : PBndQ n → ℝ) : Fin (n + 1) → ℝ :=
  fun i => w (Sum.inl (Sum.inl i))

/-- Pulling a tuple on `PBndQ n` back along `pBndIdx n` gives the fibre point
`Fin.cons (w (inr 0)) (Fin.tail p)` where `p = pBndOff w`. -/
lemma pBndIdx_comp {n : ℕ} (w : PBndQ n → ℝ) :
    w ∘ pBndIdx n = Fin.cons (w (Sum.inr 0)) (Fin.tail (pBndOff w)) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [pBndIdx, Function.comp_apply]
  | succ j => simp [pBndIdx, pBndOff, Function.comp_apply, Fin.tail_def]

/-- The fibre of the complement family is the complement of the fibre. -/
lemma Pfib1_compl {n : ℕ} (A : Set (Fin (n + 1) → ℝ)) (p : Fin (n + 1) → ℝ) :
    Pfib1 (Aᶜ) p = (Pfib1 A p)ᶜ := by
  ext x
  simp only [Pfib1, Set.mem_ofPred_eq, Set.mem_compl_iff]

/-! ## 2. The parametric interior is definable -/

/-- **The parametric interior is `∅`-definable.**  The set of parameters `p` for which `p 0` lies
in the interior (`Work.WilC2.InteriorSet`) of the fibre `Pfib1 A p`. -/
lemma pbnd_paramInt_definable {n : ℕ} {A : Set (Fin (n + 1) → ℝ)}
    (hA : (∅ : Set ℝ).Definable LRc A) :
    (∅ : Set ℝ).Definable LRc
      {p : Fin (n + 1) → ℝ | p 0 ∈ Work.WilC2.InteriorSet (Pfib1 A p)} := by
  classical
  -- every nonnegative real is a square, so `≤` (and hence `<`) is `LRc`-definable
  have hsq : ∀ x : ℝ, 0 ≤ x → ∃ z : ℝ, x = z * z :=
    fun x hx => ⟨Real.sqrt x, by rw [← pow_two (Real.sqrt x), Real.sq_sqrt hx]⟩
  -- the "point of `S`" read off a quadruple `(p, a, b, z)` is `Fin.cons z (Fin.tail p)`
  have hSin : (∅ : Set ℝ).Definable LRc {w : PBndQ n → ℝ | w ∘ pBndIdx n ∈ A} := by
    have h := hA.preimage_comp (pBndIdx n)
    have heq : {w : PBndQ n → ℝ | w ∘ pBndIdx n ∈ A} =
        (fun g : PBndQ n → ℝ => g ∘ pBndIdx n) ⁻¹' A := rfl
    rw [heq]; exact h
  -- the "bad" condition `Fin.cons z (Fin.tail p) ∉ A`
  have hnot : (∅ : Set ℝ).Definable LRc
      {w : PBndQ n → ℝ | w (Sum.inr 0) ∉ Pfib1 A (pBndOff w)} := by
    have h := hSin.compl
    convert h using 2
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    rw [pBndIdx_comp w]
    simp only [Pfib1, Set.mem_ofPred_eq]
  -- the ordering conditions `z < b` and `a < z`
  have hlt1 : (∅ : Set ℝ).Definable LRc
      {w : PBndQ n → ℝ | w (Sum.inr 0) < w (Sum.inl (Sum.inr (1 : Fin 2)))} :=
    Work.WilC2.definable_lt (M := ℝ) (A := ∅) hsq (Sum.inr (0 : Fin 1))
      (Sum.inl (Sum.inr (1 : Fin 2)))
  have hlt2 : (∅ : Set ℝ).Definable LRc
      {w : PBndQ n → ℝ | w (Sum.inl (Sum.inr (0 : Fin 2))) < w (Sum.inr 0)} :=
    Work.WilC2.definable_lt (M := ℝ) (A := ∅) hsq (Sum.inl (Sum.inr (0 : Fin 2)))
      (Sum.inr (0 : Fin 1))
  have hBad : (∅ : Set ℝ).Definable LRc {w : PBndQ n → ℝ |
      w (Sum.inr 0) < w (Sum.inl (Sum.inr (1 : Fin 2))) ∧
      w (Sum.inl (Sum.inr (0 : Fin 2))) < w (Sum.inr 0) ∧
      w (Sum.inr 0) ∉ Pfib1 A (pBndOff w)} := by
    have h := (hlt1.inter hlt2).inter hnot
    convert h using 2
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  -- the `∀ z` clause: `Ioo a b ⊆ Pfib1 A p`
  have hsub : (∅ : Set ℝ).Definable LRc {v : PBndT n → ℝ |
      Set.Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) ⊆ Pfib1 A (fun i => v (Sum.inl i))} := by
    have h := (hBad.compl).forall_of_finite (α := PBndT n) (β := Fin 1)
    have hset : {v : PBndT n → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ ({w : PBndQ n → ℝ |
        w (Sum.inr 0) < w (Sum.inl (Sum.inr (1 : Fin 2))) ∧
        w (Sum.inl (Sum.inr (0 : Fin 2))) < w (Sum.inr 0) ∧
        w (Sum.inr 0) ∉ Pfib1 A (pBndOff w)})ᶜ} =
        {v : PBndT n → ℝ |
          Set.Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) ⊆ Pfib1 A (fun i => v (Sum.inl i))} := by
      ext v
      constructor
      · intro hv x hx
        by_contra hxD
        exact hv (fun _ => x) ⟨hx.2, hx.1, hxD⟩
      · intro hv u
        rintro ⟨h1, h2, h3⟩
        exact h3 (hv ⟨h2, h1⟩)
    rw [hset] at h
    exact h
  have hlt1' : (∅ : Set ℝ).Definable LRc
      {v : PBndT n → ℝ | v (Sum.inr (0 : Fin 2)) < v (Sum.inl (0 : Fin (n + 1)))} :=
    Work.WilC2.definable_lt (M := ℝ) (A := ∅) hsq (Sum.inr (0 : Fin 2))
      (Sum.inl (0 : Fin (n + 1)))
  have hlt2' : (∅ : Set ℝ).Definable LRc
      {v : PBndT n → ℝ | v (Sum.inl (0 : Fin (n + 1))) < v (Sum.inr (1 : Fin 2))} :=
    Work.WilC2.definable_lt (M := ℝ) (A := ∅) hsq (Sum.inl (0 : Fin (n + 1)))
      (Sum.inr (1 : Fin 2))
  have htriple : (∅ : Set ℝ).Definable LRc {v : PBndT n → ℝ |
      v (Sum.inr 0) < v (Sum.inl 0) ∧ v (Sum.inl 0) < v (Sum.inr 1) ∧
        Set.Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) ⊆ Pfib1 A (fun i => v (Sum.inl i))} := by
    have h := (hlt1'.inter hlt2').inter hsub
    convert h using 2
    ext v
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hproj := htriple.exists_of_finite (α := Fin (n + 1)) (β := Fin 2)
  have hset2 : {v : Fin (n + 1) → ℝ | ∃ u : Fin 2 → ℝ, Sum.elim v u ∈ {v : PBndT n → ℝ |
      v (Sum.inr 0) < v (Sum.inl 0) ∧ v (Sum.inl 0) < v (Sum.inr 1) ∧
        Set.Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) ⊆ Pfib1 A (fun i => v (Sum.inl i))}} =
      {p : Fin (n + 1) → ℝ | p 0 ∈ Work.WilC2.InteriorSet (Pfib1 A p)} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, h1, h2, h3⟩
      exact ⟨u 0, u 1, h1, h2, h3⟩
    · rintro ⟨a, b, h1, h2, h3⟩
      exact ⟨![a, b], h1, h2, h3⟩
  rw [hset2] at hproj
  exact hproj

/-! ## 3. `IsBnd` is the complement of the two interiors -/

/-- `x` is a boundary point of `D` iff `x` lies in neither the interior of `D` nor the interior
of `Dᶜ`. -/
lemma pbnd_isBnd_iff_not_mem_interior {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {D : Set M} {x : M} :
    Work.WilC2.IsBnd D x ↔ x ∉ Work.WilC2.InteriorSet D ∧ x ∉ Work.WilC2.InteriorSet Dᶜ := by
  rw [Work.WilC2.IsBnd]
  exact ⟨fun h => ⟨fun hx => h.1 ((Work.WilC2.exists_Ioo_subset_iff_interior).mpr hx),
      fun hx => h.2 ((Work.WilC2.exists_Ioo_subset_iff_interior).mpr hx)⟩,
    fun h => ⟨fun hx => h.1 ((Work.WilC2.exists_Ioo_subset_iff_interior).mp hx),
      fun hx => h.2 ((Work.WilC2.exists_Ioo_subset_iff_interior).mp hx)⟩⟩

/-! ## 4. The boundary set of the fibre family -/

/-- Prove in namespace `Work.WilC4` (declaration name `Work.WilC4.paramBnd_definable`) in the file
`Submission/Work/WilC4/paramBnd_definable.lean`.  If `S ⊆ ℝ^{n+1}` is `∅`-definable then so is the
parametric boundary set: `p` is kept when `p 0` is a boundary point (`Work.WilC2.IsBnd`) of the
fibre `Pfib1 S p = {x : ℝ | Fin.cons x (Fin.tail p) ∈ S}`.  Mathematical content: build the
*parametrized* version of `Work.WilC2.definable_interior` / `Work.WilC2.bnd_definable_alt` (there
the definable set is fixed, here it varies with `p`); use `Work.WilC2.IsBnd`,
`Work.WilC2.InteriorSet`, `Work.WilC2.definable_le`, `Work.WilC4.empty_definable_coord_eq`. -/
theorem paramBnd_definable {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc S) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | Work.WilC2.IsBnd (Work.WilC4.Pfib1 S p) (p 0)} := by
  have h1 := pbnd_paramInt_definable (A := S) hS
  have hSc : (∅ : Set ℝ).Definable LRc (Sᶜ) := hS.compl
  have h2 := pbnd_paramInt_definable (A := Sᶜ) hSc
  have h2' : (∅ : Set ℝ).Definable LRc
      {p : Fin (n + 1) → ℝ | p 0 ∈ Work.WilC2.InteriorSet ((Pfib1 S p)ᶜ)} := by
    have heq : {p : Fin (n + 1) → ℝ | p 0 ∈ Work.WilC2.InteriorSet (Pfib1 Sᶜ p)} =
        {p : Fin (n + 1) → ℝ | p 0 ∈ Work.WilC2.InteriorSet ((Pfib1 S p)ᶜ)} := by
      ext p
      simp only [Set.mem_ofPred_eq]
      rw [Pfib1_compl]
    rwa [heq] at h2
  have h3 := (h1.union h2').compl
  have hset : ({p : Fin (n + 1) → ℝ | p 0 ∈ Work.WilC2.InteriorSet (Pfib1 S p)} ∪
      {p : Fin (n + 1) → ℝ | p 0 ∈ Work.WilC2.InteriorSet ((Pfib1 S p)ᶜ)})ᶜ =
      {p : Fin (n + 1) → ℝ | Work.WilC2.IsBnd (Pfib1 S p) (p 0)} := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or]
    rw [pbnd_isBnd_iff_not_mem_interior]
  rw [hset] at h3
  exact h3

end Work.WilC4
