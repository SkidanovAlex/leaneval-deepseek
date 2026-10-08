/-
# The first step of Higman's Lemma 11 in the two-step setting

Let `P = TwoStep V W b` satisfy the hypotheses of `Work.Higman.cocycle_normal_form`: `|V| = |W|²`,
the involutions of `P` are exactly `kerFst ∖ {1}` (i.e. `Ω₁(P) = Z(P) = kerFst`) and `ξ ∈ Aut(P)`
permutes them transitively.  Let `Z ≤ X ≤ P` be a `ξ`-invariant subgroup.

* `card_kerFst_sq_le_card`: `|Z|² ≤ |X|` whenever `X ≠ Z`.  Indeed the squaring map `X → Z`,
  `x ↦ x²`, has an image containing a non-zero element, hence (by transitivity of `ξ` on
  `Z ∖ {0}`) equal to `Z`, and every fibre of `x ↦ x²` contains a coset of `Z`.
  Equivalently: for a `ξ`-irreducible `X/Z`, `|X/Z| ≥ q`, i.e. `dim X/Z ≥ n = dim Z`.
* `card_le_card_kerFst_sq_of_comm`: if `X` is abelian then `|X| ≤ |Z|²`, so with the previous
  result `|X| = |Z|²`: a `ξ`-irreducible abelian `X` over `Z` satisfies `|X/Z| = q` (the
  "abelian case" of Higman's Lemma 11 / the type `A(n,1)` case).

Together with the divisibility argument `n ∣ dim(X/Z)` these give that an irreducible `X/Z` has
order `q` unless `X = P`; excluding `X = P` is exactly Higman's Lemma 11, whose linear-algebra
core (`Work.Higman.monomial_form`) is already proved in this workspace.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable [Finite V] [Finite W]
variable {b : V → V → W} [Biadd b]

/-- `x ^ 4 = 1` in a two-step group. -/
theorem pow_four_eq_one (x : TwoStep V W b) : x ^ 4 = 1 := by
  have h := TwoStep.sq_eq x
  calc x ^ 4 = (x ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    _ = (⟨0, b x.fst x.fst⟩ : TwoStep V W b) ^ 2 := by rw [h]
    _ = 1 := by
        rw [TwoStep.sq_eq]
        ext <;> simp [Biadd.zero_left]

/-- `ξ` preserves a subgroup if it maps it into itself. -/
theorem map_mem_of_mem {ξ : MulAut (TwoStep V W b)} {X : Subgroup (TwoStep V W b)}
    (hXinv : ∀ x ∈ X, ξ x ∈ X) : ∀ (k : ℕ) (x : TwoStep V W b), x ∈ X → (ξ ^ k) x ∈ X := by
  intro k
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ', MulAut.mul_apply]
      exact hXinv _ (ih x hx)

/-- **`|Z|² ≤ |X|` for `ξ`-invariant `X ≠ Z`.** -/
theorem card_kerFst_sq_le_card
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = (TwoStep.kerFst (A := V) (Z := W) (b := b)))
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (X : Subgroup (TwoStep V W b)) (hZX : (TwoStep.kerFst (A := V) (Z := W) (b := b)) ≤ X)
    (hXinv : ∀ x ∈ X, ξ x ∈ X) (hXne : X ≠ (TwoStep.kerFst (A := V) (Z := W) (b := b))) :
    Nat.card ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) ^ 2 ≤ Nat.card ↥X := by
  classical
  -- an element of `X` outside `Z`
  obtain ⟨x₀, hx₀X, hx₀Z⟩ : ∃ x : TwoStep V W b, x ∈ X ∧ x ∉ (TwoStep.kerFst (A := V) (Z := W) (b := b)) := by
    by_contra h
    push_neg at h
    exact hXne (le_antisymm h hZX)
  have hx0sq_mem : x₀ ^ 2 ∈ (TwoStep.kerFst (A := V) (Z := W) (b := b)) :=
    (sq_eq_one_iff_mem_kerFst (V := V) (W := W) (b := b) hinvol hcenter (x₀ ^ 2)).mp
      (by rw [← pow_mul]; exact pow_four_eq_one x₀)
  have hx0sq_ne : x₀ ^ 2 ≠ 1 := fun h =>
    hx₀Z ((sq_eq_one_iff_mem_kerFst hinvol hcenter x₀).mp h)
  have hx0sq_ord : orderOf (x₀ ^ 2) = 2 := by
    rw [orderOf_eq_two_iff hinvol hcenter]
    refine ⟨(TwoStep.mem_kerFst).mp hx0sq_mem, fun h => hx0sq_ne ?_⟩
    ext
    · exact (TwoStep.mem_kerFst).mp hx0sq_mem
    · exact h
  -- every element of `Z` is the square of an element of `X`
  have hsurj : ∀ z : ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))),
      ∃ x : TwoStep V W b, x ∈ X ∧ x ^ 2 = (z : TwoStep V W b) := by
    intro z
    rcases eq_or_ne (z : TwoStep V W b) 1 with hz | hz
    · exact ⟨1, X.one_mem, by rw [one_pow, hz]⟩
    · have hz2 : orderOf (z : TwoStep V W b) = 2 := by
        rw [orderOf_eq_two_iff hinvol hcenter]
        refine ⟨(TwoStep.mem_kerFst).mp z.2, fun h => hz ?_⟩
        ext
        · exact (TwoStep.mem_kerFst).mp z.2
        · exact h
      obtain ⟨k, hk⟩ := htrans _ _ hx0sq_ord hz2
      exact ⟨(ξ ^ k) x₀, map_mem_of_mem hXinv k x₀ hx₀X,
        by rw [← map_pow, hk]⟩
  choose χ hχX hχsq using hsurj
  -- the fibre of `x ↦ x²` over `z` contains the coset `χ z * Z`
  have hfib : ∀ (z y : ↥((TwoStep.kerFst (A := V) (Z := W) (b := b)))),
      (χ z * (y : TwoStep V W b)) ^ 2 = (z : TwoStep V W b) := by
    intro z y
    have hyc : (y : TwoStep V W b) ∈ Subgroup.center (TwoStep V W b) := by
      rw [hcenter]; exact y.2
    rw [Subgroup.mem_center_iff] at hyc
    have hcomm : Commute (χ z) (y : TwoStep V W b) := hyc (χ z)
    calc (χ z * (y : TwoStep V W b)) ^ 2
        = (χ z) ^ 2 * (y : TwoStep V W b) ^ 2 := by rw [hcomm.mul_pow]
      _ = (χ z) ^ 2 := by
          rw [show (y : TwoStep V W b) ^ 2 = 1 from
            (sq_eq_one_iff_mem_kerFst hinvol hcenter _).mpr y.2, mul_one]
      _ = (z : TwoStep V W b) := hχsq z
  -- an injective map `Z × Z → X`
  have hinj : Function.Injective
      (fun p : ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) × ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) =>
        (⟨χ p.1 * (p.2 : TwoStep V W b), X.mul_mem (hχX p.1) (hZX p.2.2)⟩ :
          ↥X)) := by
    rintro ⟨z₁, y₁⟩ ⟨z₂, y₂⟩ h
    have h' : χ z₁ * (y₁ : TwoStep V W b) = χ z₂ * (y₂ : TwoStep V W b) :=
      congrArg (fun t : ↥X => (t : TwoStep V W b)) h
    have hz : (z₁ : TwoStep V W b) = (z₂ : TwoStep V W b) := by
      have hsq := congrArg (fun t : TwoStep V W b => t ^ 2) h'
      rw [hfib z₁ y₁, hfib z₂ y₂] at hsq
      exact hsq
    have hy : (y₁ : TwoStep V W b) = (y₂ : TwoStep V W b) := by
      have hzsub : z₁ = z₂ := Subtype.ext hz
      have h2 : χ z₁ * (y₁ : TwoStep V W b) = χ z₁ * (y₂ : TwoStep V W b) := by
        calc χ z₁ * (y₁ : TwoStep V W b) = χ z₂ * (y₂ : TwoStep V W b) := h'
          _ = χ z₁ * (y₂ : TwoStep V W b) := by rw [← hzsub]
      exact mul_left_cancel h2
    exact Prod.ext (Subtype.ext hz) (Subtype.ext hy)
  have h1 := Nat.card_le_card_of_injective
    (fun p : ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) × ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) =>
      (⟨χ p.1 * (p.2 : TwoStep V W b), X.mul_mem (hχX p.1) (hZX p.2.2)⟩ : ↥X)) hinj
  rw [Nat.card_prod] at h1
  calc Nat.card ↥(TwoStep.kerFst (A := V) (Z := W) (b := b)) ^ 2
      = Nat.card ↥(TwoStep.kerFst (A := V) (Z := W) (b := b)) *
        Nat.card ↥(TwoStep.kerFst (A := V) (Z := W) (b := b)) := pow_two _
    _ ≤ Nat.card ↥X := h1

/-- **`|X| ≤ |Z|²` for abelian `ξ`-invariant `X ≥ Z`.** -/
theorem card_le_card_kerFst_sq_of_comm
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = (TwoStep.kerFst (A := V) (Z := W) (b := b)))
    (X : Subgroup (TwoStep V W b)) (hZX : (TwoStep.kerFst (A := V) (Z := W) (b := b)) ≤ X)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card ↥X ≤ Nat.card ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) ^ 2 := by
  classical
  -- the squaring map on `X`, with values in `Z`
  let φ : ↥X →* ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) :=
    { toFun := fun x => ⟨(x : TwoStep V W b) ^ 2,
        (sq_eq_one_iff_mem_kerFst (V := V) (W := W) (b := b) hinvol hcenter _).mp
        (by rw [← pow_mul]; exact pow_four_eq_one (x : TwoStep V W b))⟩
      map_one' := by
        refine Subtype.ext ?_
        show ((1 : ↥X) : TwoStep V W b) ^ 2 = (1 : TwoStep V W b)
        rw [Subgroup.coe_one, one_pow]
      map_mul' := fun x y => by
        refine Subtype.ext ?_
        show ((x * y : ↥X) : TwoStep V W b) ^ 2 =
          (x : TwoStep V W b) ^ 2 * (y : TwoStep V W b) ^ 2
        have hcomm : Commute (x : TwoStep V W b) (y : TwoStep V W b) :=
          hXab (x : TwoStep V W b) x.2 (y : TwoStep V W b) y.2
        rw [Subgroup.coe_mul, hcomm.mul_pow] }
  have hker : φ.ker = (TwoStep.kerFst (A := V) (Z := W) (b := b)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h3 : (φ x : TwoStep V W b) = (1 : TwoStep V W b) := by rw [h]; rfl
      change (x : TwoStep V W b) ^ 2 = 1 at h3
      exact (sq_eq_one_iff_mem_kerFst hinvol hcenter x).mp h3
    · intro h
      refine Subtype.ext ?_
      change ((x : TwoStep V W b)) ^ 2 = (1 : TwoStep V W b)
      exact (sq_eq_one_iff_mem_kerFst hinvol hcenter x).mpr h
  have hcard_ker : Nat.card ↥φ.ker = Nat.card ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) := by
    rw [hker]
    exact Nat.card_congr
      { toFun := fun t : ↥((TwoStep.kerFst (A := V) (Z := W) (b := b)).subgroupOf X) => ⟨(t.1 : TwoStep V W b), t.2⟩
        invFun := fun z : ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) => ⟨⟨z, hZX z.2⟩, z.2⟩
        left_inv := fun t => by ext <;> rfl
        right_inv := fun z => rfl }
  have hrange : Nat.card φ.range ≤ Nat.card ↥((TwoStep.kerFst (A := V) (Z := W) (b := b))) :=
    Nat.card_le_card_of_injective (fun t : ↥φ.range => (t : ↥((TwoStep.kerFst (A := V) (Z := W) (b := b)))))
      Subtype.coe_injective
  have h := φ.ker.card_mul_index
  rw [Subgroup.index_ker] at h
  rw [hcard_ker] at h
  rw [← h]
  simpa [pow_two] using
    Nat.mul_le_mul_left (Nat.card ↥((TwoStep.kerFst (A := V) (Z := W) (b := b)))) hrange

end Work.Higman
