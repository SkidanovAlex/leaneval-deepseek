import Mathlib

set_option linter.unusedSectionVars false

/-!
# Finite σ-algebras and conditional expectation

A finite σ-algebra on a finite type `X` is presented here by the function
`part : X → Finset X` sending `x` to the unique atom of the σ-algebra
containing `x` (so the atoms form a partition of `X`, and the σ-algebra is
recovered as the set of unions of atoms).  The two hypotheses used throughout
are

* `hmem : ∀ x, x ∈ part x`,
* `heq  : ∀ x y, y ∈ part x → part y = part x`.

We develop the elementary theory of the conditional expectation
`𝔼(f | part)`: linearity, positivity, measurability, idempotence, the
self-adjointness identity `∑ x, 𝔼 f x * h x = ∑ x, f x * h x` for `h`
measurable, the `L²`-contraction (Jensen) inequality, and the tower property
for a refinement.  These are the tools needed for the Furstenberg tower /
energy-increment argument in the Green–Tao transference principle (GT §6–7).
-/

open Finset

namespace FinSigma

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The atoms of the finite σ-algebra presented by `part`. -/
def atoms (part : X → Finset X) : Finset (Finset X) := Finset.univ.image part

/-- membership in `atoms` -/
lemma mem_atoms {part : X → Finset X} (A : Finset X) : A ∈ atoms part ↔ ∃ x, part x = A := by
  simp [atoms]

lemma mem_part_iff {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (x y : X) :
    y ∈ part x ↔ part y = part x :=
  ⟨fun h => heq x y h, fun h => h ▸ hmem y⟩

lemma part_nonempty {part : X → Finset X} (hmem : ∀ x, x ∈ part x) (x : X) :
    (part x).Nonempty := ⟨x, hmem x⟩

lemma part_card_ne_zero {part : X → Finset X} (hmem : ∀ x, x ∈ part x) (x : X) :
    (part x).card ≠ 0 := Finset.card_ne_zero.mpr (part_nonempty hmem x)

lemma part_card_pos {part : X → Finset X} (hmem : ∀ x, x ∈ part x) (x : X) :
    0 < (part x).card := Finset.card_pos.mpr (part_nonempty hmem x)

lemma part_card_cast_ne_zero {part : X → Finset X} (hmem : ∀ x, x ∈ part x) (x : X) :
    ((part x).card : ℝ) ≠ 0 := by exact_mod_cast part_card_ne_zero hmem x

lemma pairwiseDisjoint_atoms {part : X → Finset X}
    (heq : ∀ x y : X, y ∈ part x → part y = part x) :
    (atoms part : Set (Finset X)).PairwiseDisjoint (fun A => A) := by
  intro A hA B hB hAB
  rw [Finset.mem_coe, mem_atoms] at hA hB
  obtain ⟨x, rfl⟩ := hA
  obtain ⟨y, rfl⟩ := hB
  change Disjoint (part x) (part y)
  rw [Finset.disjoint_left]
  intro z hzx hzy
  exact hAB ((heq x z hzx).symm.trans (heq y z hzy))

lemma biUnion_atoms {part : X → Finset X} (hmem : ∀ x, x ∈ part x) :
    (atoms part).biUnion (fun A => A) = Finset.univ := by
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨A, hA, hxA⟩; exact Finset.mem_univ x
  · intro _
    exact ⟨part x, (mem_atoms (part x)).mpr ⟨x, rfl⟩, hmem x⟩

/-- Summing over the atoms is the same as summing over `X`. -/
lemma sum_atoms {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (g : X → ℝ) :
    ∑ A ∈ atoms part, ∑ y ∈ A, g y = ∑ y, g y := by
  rw [← biUnion_atoms hmem, Finset.sum_biUnion (pairwiseDisjoint_atoms heq)]

/-! ## Conditional expectation -/

/-- Conditional expectation onto the finite σ-algebra presented by `part`. -/
noncomputable def cE (part : X → Finset X) (f : X → ℝ) : X → ℝ :=
  fun x => ((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, f y

/-- `h` is measurable w.r.t. the σ-algebra presented by `part`. -/
def IsMeas (part : X → Finset X) (h : X → ℝ) : Prop := ∀ x y : X, y ∈ part x → h y = h x

/-- `Q` refines `P` (every `Q`-atom is contained in a `P`-atom). -/
def Refines (Q P : X → Finset X) : Prop := ∀ x, Q x ⊆ P x

lemma cE_apply {part : X → Finset X} (f : X → ℝ) (x : X) :
    cE part f x = ((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, f y := rfl

lemma cE_const {part : X → Finset X} (hmem : ∀ x, x ∈ part x) (c : ℝ) :
    cE part (fun _ => c) = fun _ => c := by
  funext x
  rw [cE_apply, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (part_card_cast_ne_zero hmem x), one_mul]

lemma cE_add {part : X → Finset X} (f g : X → ℝ) :
    cE part (f + g) = cE part f + cE part g := by
  funext x
  simp only [cE_apply, Pi.add_apply, Finset.sum_add_distrib, mul_add]

lemma cE_neg {part : X → Finset X} (f : X → ℝ) : cE part (-f) = -cE part f := by
  funext x
  simp only [cE_apply, Pi.neg_apply, Finset.sum_neg_distrib, mul_neg]

lemma cE_sub {part : X → Finset X} (f g : X → ℝ) :
    cE part (f - g) = cE part f - cE part g := by
  funext x
  simp only [cE_apply, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]

lemma cE_zero {part : X → Finset X} : cE part (fun _ : X => (0 : ℝ)) = fun _ => 0 := by
  funext x
  rw [cE_apply, Finset.sum_const_zero, mul_zero]

lemma cE_sum {part : X → Finset X} {ι : Type*} (s : Finset ι) (f : ι → X → ℝ) :
    cE part (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, cE part (f i) x := by
  funext x
  simp only [cE]
  rw [Finset.sum_comm, Finset.mul_sum]

lemma cE_const_mul {part : X → Finset X} (c : ℝ) (f : X → ℝ) :
    cE part (fun x => c * f x) = fun x => c * cE part f x := by
  funext x
  simp only [cE]
  rw [← Finset.mul_sum]
  ring

lemma cE_mul_const {part : X → Finset X} (c : ℝ) (f : X → ℝ) :
    cE part (fun x => f x * c) = fun x => cE part f x * c := by
  funext x
  simp only [cE]
  rw [← Finset.sum_mul]
  ring

lemma cE_measurable {part : X → Finset X}
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (f : X → ℝ) :
    IsMeas part (cE part f) := by
  intro x y hy
  rw [cE_apply, cE_apply, heq x y hy]

lemma cE_of_measurable {part : X → Finset X} (hmem : ∀ x, x ∈ part x) {h : X → ℝ}
    (hh : IsMeas part h) : cE part h = h := by
  funext x
  have hsum : ∑ y ∈ part x, h y = ∑ y ∈ part x, h x :=
    Finset.sum_congr rfl (fun y hy => hh x y hy)
  rw [cE_apply, hsum, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (part_card_cast_ne_zero hmem x), one_mul]

lemma cE_idem {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (f : X → ℝ) :
    cE part (cE part f) = cE part f :=
  cE_of_measurable hmem (cE_measurable heq f)

/-- On a union of atoms, the conditional expectation has the same sum as `f`. -/
lemma sum_cE_of_union {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (S : Finset X)
    (hS : ∀ x ∈ S, part x ⊆ S) (f : X → ℝ) :
    ∑ x ∈ S, cE part f x = ∑ x ∈ S, f x := by
  have hpair : ((atoms part).filter (fun A => A ⊆ S) : Set (Finset X)).PairwiseDisjoint
      (fun A => A) := by
    intro A hA B hB hAB
    rw [Finset.mem_coe, Finset.mem_filter] at hA hB
    exact pairwiseDisjoint_atoms heq hA.1 hB.1 hAB
  have hbij : ((atoms part).filter (fun A => A ⊆ S)).biUnion (fun A => A) = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨A, ⟨hA, hAS⟩, hxA⟩; exact hAS hxA
    · intro hx
      exact ⟨part x, ⟨(mem_atoms (part x)).mpr ⟨x, rfl⟩, hS x hx⟩, hmem x⟩
  rw [← hbij, Finset.sum_biUnion hpair, Finset.sum_biUnion hpair]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mem_filter] at hA
  obtain ⟨x, rfl⟩ := (mem_atoms A).mp hA.1
  have hconst : ∀ y ∈ part x, cE part f y = cE part f x :=
    fun y hy => cE_measurable heq f x y hy
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, cE_apply,
    ← mul_assoc, mul_inv_cancel₀ (part_card_cast_ne_zero hmem x), one_mul]

lemma sum_cE {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (f : X → ℝ) :
    ∑ x, cE part f x = ∑ x, f x :=
  sum_cE_of_union hmem heq Finset.univ (fun x _ => Finset.subset_univ _) f

lemma cE_nonneg {part : X → Finset X} (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    0 ≤ cE part f x := by
  rw [cE_apply]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun y _ => hf y))

lemma cE_mono {part : X → Finset X} (f g : X → ℝ) (hf : ∀ x, f x ≤ g x) (x : X) :
    cE part f x ≤ cE part g x := by
  rw [cE_apply, cE_apply]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y _ => hf y))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma abs_cE_le {part : X → Finset X} (f : X → ℝ) (x : X) :
    |cE part f x| ≤ cE part (fun y => |f y|) x := by
  rw [cE_apply, cE_apply, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (part x).card))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma cE_le_of_measurable {part : X → Finset X} (hmem : ∀ x, x ∈ part x) {h : X → ℝ}
    (hh : IsMeas part h) (f : X → ℝ) (hf : ∀ x, f x ≤ h x) (x : X) :
    cE part f x ≤ h x := by
  have h1 := cE_mono (part := part) f h hf x
  rwa [cE_of_measurable hmem hh] at h1

lemma cE_le_of_le_measurable {part : X → Finset X} (hmem : ∀ x, x ∈ part x) {h : X → ℝ}
    (hh : IsMeas part h) (f : X → ℝ) (hf : ∀ x, h x ≤ f x) (x : X) :
    h x ≤ cE part f x := by
  have h1 := cE_mono (part := part) h f hf x
  rwa [cE_of_measurable hmem hh] at h1

/-- Self-adjointness of conditional expectation on a union of atoms. -/
lemma sum_cE_mul_measurable_of_union {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (S : Finset X)
    (hS : ∀ x ∈ S, part x ⊆ S) (f h : X → ℝ) (hh : IsMeas part h) :
    ∑ x ∈ S, cE part f x * h x = ∑ x ∈ S, f x * h x := by
  rw [← sum_cE_of_union hmem heq S hS (fun x => f x * h x)]
  apply Finset.sum_congr rfl
  intro x _
  have hsum : ∑ y ∈ part x, f y * h y = (∑ y ∈ part x, f y) * h x := by
    rw [Finset.sum_congr rfl (fun y hy => by rw [hh x y hy]), Finset.sum_mul]
  simp only [cE]
  rw [hsum]
  ring

lemma sum_cE_mul_measurable {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (f h : X → ℝ)
    (hh : IsMeas part h) :
    ∑ x, cE part f x * h x = ∑ x, f x * h x :=
  sum_cE_mul_measurable_of_union hmem heq Finset.univ (fun x _ => Finset.subset_univ _)
    f h hh

lemma sum_cE_mul_self {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (f : X → ℝ) :
    ∑ x, f x * cE part f x = ∑ x, (cE part f x) ^ 2 := by
  have h := sum_cE_mul_measurable hmem heq f (cE part f) (cE_measurable heq f)
  simp only [pow_two]
  exact h.symm

/-- `L²`-contraction (Jensen) for conditional expectation. -/
lemma cE_l2_contraction {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (f : X → ℝ) :
    ∑ x, (cE part f x) ^ 2 ≤ ∑ x, (f x) ^ 2 := by
  have key : ∑ x, (f x - cE part f x) ^ 2 =
      ∑ x, (f x) ^ 2 - ∑ x, (cE part f x) ^ 2 := by
    have expand : ∀ x, (f x - cE part f x) ^ 2 =
        (f x) ^ 2 - 2 * (f x * cE part f x) + (cE part f x) ^ 2 := by
      intro x; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_cE_mul_self hmem heq f]
    ring
  have hnn : 0 ≤ ∑ x, (f x - cE part f x) ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  linarith

/-- The tower property for a refinement. -/
lemma cE_tower {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) {Q : X → Finset X}
    (hQmem : ∀ x, x ∈ Q x) (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x)
    (href : ∀ x, Q x ⊆ part x) (f : X → ℝ) :
    cE part (cE Q f) = cE part f := by
  funext x
  rw [cE_apply, cE_apply]
  have hS : ∀ y ∈ part x, Q y ⊆ part x := by
    intro y hy z hz
    have h1 := href y hz
    rwa [heq x y hy] at h1
  rw [sum_cE_of_union hQmem hQeq (part x) hS f]

/-! ## Join of σ-algebras -/

/-- The join (common refinement) of the σ-algebras presented by `P` and `Q`. -/
def jpart (P Q : X → Finset X) (x : X) : Finset X :=
  (P x).filter (fun y => Q y = Q x)

lemma jpart_eq_inter {P Q : X → Finset X} (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (x : X) :
    jpart P Q x = P x ∩ Q x := by
  ext y
  rw [jpart, Finset.mem_filter, Finset.mem_inter, mem_part_iff hQmem hQeq]

lemma mem_jpart (P Q : X → Finset X) (hmem : ∀ x, x ∈ P x) (x : X) :
    x ∈ jpart P Q x := by
  rw [jpart, Finset.mem_filter]
  exact ⟨hmem x, rfl⟩

lemma jpart_eq {P Q : X → Finset X} (heq : ∀ x y : X, y ∈ P x → P y = P x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) {x y : X} (hy : y ∈ jpart P Q x) :
    jpart P Q y = jpart P Q x := by
  rw [jpart, Finset.mem_filter] at hy
  rw [jpart, jpart, heq x y hy.1, hy.2]

lemma refines_jpart_left (P Q : X → Finset X) : Refines (jpart P Q) P :=
  fun x y hy => (Finset.mem_filter.mp hy).1

lemma refines_jpart_right {P Q : X → Finset X} (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) : Refines (jpart P Q) Q := by
  intro x y hy
  rw [jpart, Finset.mem_filter] at hy
  exact (mem_part_iff hQmem hQeq x y).mpr hy.2

/-- The number of atoms of a join is at most the product of the numbers of atoms. -/
lemma card_atoms_jpart_le {P Q : X → Finset X} (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) :
    (atoms (jpart P Q)).card ≤ (atoms P).card * (atoms Q).card := by
  have hsub : atoms (jpart P Q) ⊆
      ((atoms P).product (atoms Q)).image (fun pq : Finset X × Finset X => pq.1 ∩ pq.2) := by
    intro A hA
    rw [mem_atoms] at hA
    obtain ⟨x, rfl⟩ := hA
    rw [Finset.mem_image]
    refine ⟨(P x, Q x), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨(mem_atoms (P x)).mpr ⟨x, rfl⟩, (mem_atoms (Q x)).mpr ⟨x, rfl⟩⟩
    · rw [jpart_eq_inter hQmem hQeq]
  calc (atoms (jpart P Q)).card
      ≤ (((atoms P).product (atoms Q)).image
          (fun pq : Finset X × Finset X => pq.1 ∩ pq.2)).card := Finset.card_le_card hsub
    _ ≤ ((atoms P).product (atoms Q)).card := Finset.card_image_le
    _ = (atoms P).card * (atoms Q).card := Finset.card_product _ _

lemma abs_cE_sub_le {part : X → Finset X} (hmem : ∀ x, x ∈ part x) (f : X → ℝ) (x : X) :
    |cE part f x - f x| ≤ cE part (fun y => |f y - f x|) x := by
  have h1 : cE part (fun y => f y - f x) x = cE part f x - f x := by
    show cE part (f - fun _ : X => f x) x = cE part f x - f x
    rw [cE_sub (part := part) f (fun _ => f x), Pi.sub_apply,
      congrFun (cE_const hmem (f x)) x]
  rw [← h1]
  exact abs_cE_le (part := part) (fun y => f y - f x) x

lemma cE_abs_sub_le_of_bound {part : X → Finset X} (hmem : ∀ x, x ∈ part x) (f : X → ℝ)
    (x : X) (c : ℝ) (h : ∀ y ∈ part x, |f y - f x| ≤ c) :
    |cE part f x - f x| ≤ c := by
  refine le_trans (abs_cE_sub_le hmem f x) ?_
  rw [cE_apply]
  have hsum : ∑ y ∈ part x, |f y - f x| ≤ ∑ _y ∈ part x, c :=
    Finset.sum_le_sum (fun y hy => h y hy)
  calc ((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, |f y - f x|
      ≤ ((part x).card : ℝ)⁻¹ * ∑ _y ∈ part x, c :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ((part x).card : ℝ)⁻¹ * ((part x).card * c) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = c := by
        rw [← mul_assoc, inv_mul_cancel₀ (part_card_cast_ne_zero hmem x), one_mul]

lemma abs_cE_self_sub_le {part : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (f : X → ℝ) (x : X) :
    |cE part f x - f x| ≤ cE part (fun y => |f y - f x|) x :=
  abs_cE_sub_le hmem f x

/-! ## Energy (Pythagoras) identity and energy increment -/

/-- Pythagoras identity: refining a σ-algebra increases the `L²` energy of the
conditional expectation by the `L²` norm of the difference. -/
lemma sum_cE_sq_eq_add {part Q : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ part x) (f : X → ℝ) :
    ∑ x, (cE Q f x) ^ 2 = ∑ x, (cE part f x) ^ 2
      + ∑ x, (cE Q f x - cE part f x) ^ 2 := by
  have hgm : IsMeas Q (cE part f) := by
    intro x y hy
    exact cE_measurable heq f x y (href x hy)
  have h1 : ∑ x, cE Q f x * cE part f x = ∑ x, f x * cE part f x :=
    sum_cE_mul_measurable hQmem hQeq f (cE part f) hgm
  have h2 : ∑ x, (cE part f x) ^ 2 = ∑ x, f x * cE part f x := by
    simpa [pow_two] using
      sum_cE_mul_measurable hmem heq f (cE part f) (cE_measurable heq f)
  have expand : ∀ x, (cE Q f x - cE part f x) ^ 2 =
      (cE Q f x) ^ 2 - 2 * (cE Q f x * cE part f x) + (cE part f x) ^ 2 := by
    intro x; ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmul : ∑ x, 2 * (cE Q f x * cE part f x) = 2 * ∑ x, cE Q f x * cE part f x := by
    rw [Finset.mul_sum]
  rw [hmul, h1, h2]
  ring

/-- **Energy increment.**  If `h` is measurable for the refined σ-algebra `Q`,
is bounded by `B`, and correlates with `f - 𝔼(f | P)`, then the energy
`𝔼 (𝔼(f|Q))²` exceeds `𝔼 (𝔼(f|P))²` by at least `Δ²/(|X| B²)`. -/
lemma energy_increment {part Q : X → Finset X} (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : X, y ∈ part x → part y = part x) (hQmem : ∀ x, x ∈ Q x)
    (hQeq : ∀ x y : X, y ∈ Q x → Q y = Q x) (href : ∀ x, Q x ⊆ part x)
    (f h : X → ℝ) (hh : ∀ x y : X, y ∈ Q x → h y = h x) {B Δ : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |h x| ≤ B) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ |∑ x, (f x - cE part f x) * h x|) :
    Δ ^ 2 ≤ ((Fintype.card X : ℝ) * B ^ 2)
      * ∑ x, (cE Q f x - cE part f x) ^ 2 := by
  have key : ∑ x, (cE Q f x - cE part f x) * h x = ∑ x, (f x - cE part f x) * h x := by
    have hself := sum_cE_mul_measurable hQmem hQeq (cE Q f) h hh
    have : ∑ x, cE Q f x * h x = ∑ x, f x * h x :=
      sum_cE_mul_measurable hQmem hQeq f h hh
    have expand : ∀ x, (cE Q f x - cE part f x) * h x
        = cE Q f x * h x - cE part f x * h x := by intro x; ring
    have expand2 : ∀ x, (f x - cE part f x) * h x = f x * h x - cE part f x * h x := by
      intro x; ring
    simp_rw [expand, expand2]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, this]
  have hcs : (∑ x, (cE Q f x - cE part f x) * h x) ^ 2
      ≤ (∑ x, (cE Q f x - cE part f x) ^ 2) * ∑ x, (h x) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hh2 : ∑ x, (h x) ^ 2 ≤ (Fintype.card X : ℝ) * B ^ 2 := by
    calc ∑ x, (h x) ^ 2 ≤ ∑ _x : X, B ^ 2 :=
          Finset.sum_le_sum (fun x _ => by
            nlinarith [hB x, hB0, abs_nonneg (h x), sq_abs (h x)])
      _ = (Fintype.card X : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnn : 0 ≤ ∑ x, (cE Q f x - cE part f x) ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hstep : Δ ^ 2 ≤ (∑ x, (cE Q f x - cE part f x) ^ 2) * ∑ x, (h x) ^ 2 := by
    have hA : Δ ≤ |∑ x, (cE Q f x - cE part f x) * h x| := by rw [key]; exact hΔ
    have hsq : Δ ^ 2 ≤ (∑ x, (cE Q f x - cE part f x) * h x) ^ 2 := by
      rw [← sq_abs (∑ x, (cE Q f x - cE part f x) * h x)]
      exact sq_le_sq' (by linarith [abs_nonneg (∑ x, (cE Q f x - cE part f x) * h x)]) hA
    exact le_trans hsq hcs
  calc Δ ^ 2 ≤ (∑ x, (cE Q f x - cE part f x) ^ 2) * ∑ x, (h x) ^ 2 := hstep
    _ ≤ (∑ x, (cE Q f x - cE part f x) ^ 2) * ((Fintype.card X : ℝ) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hh2 hnn
    _ = ((Fintype.card X : ℝ) * B ^ 2) * ∑ x, (cE Q f x - cE part f x) ^ 2 := by ring

end FinSigma
