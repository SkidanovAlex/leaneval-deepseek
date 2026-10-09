import Mathlib
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.coreGraded
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
import Submission.Work.SSGRoute.prop5.witt.Basic
import Submission.Work.SSGRoute.prop5.witt.Vocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus leading term and the graded pieces of the lower central series

This file (namespace `Work.SSGRoute.prop5.lctf`) collects, in one place, the two ingredients needed
to prove the "core" statement of the Magnus embedding theorem:

* the commutator monomial `monGrp c` attached to a free-magma tree `c`, its Magnus leading term
  `mlt N z = (magnus X N z) - 1` in the truncated free associative algebra, and the basic
  congruences for `mlt` (homogeneity, additivity on `γ_k`, behaviour on commutators);
* the graded piece `Lam X q = γ_q/γ_{q+1}` of the lower central series, its class map `cls`, and
  the linear map `treeToLam X k` from the well-indexed trees of size `k` to `Λ_{k-1}`.

The definitions duplicate the ones in `prop5/core/Defs.lean` and `prop5/magnusGroupPart.lean`; they
are repeated here because those modules import `prop5/magnusLieDefs.lean`, which clashes with the
`IsLyndon` of `prop5/witt/Defs.lean` used by the Hall-set development of Witt's theorem.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.lctf

open Work.SSGRoute.prop5

variable {X : Type*}

/-! ## The commutator monomial in the free group -/

/-- The commutator monomial in the free group attached to a binary tree. -/
def monGrp (X : Type*) : Magma X → FreeGroup X
  | .gen x => FreeGroup.of x
  | .mul a b => ⁅monGrp X a, monGrp X b⁆

@[simp] theorem monGrp_gen (X : Type*) (x : X) : monGrp X (.gen x) = FreeGroup.of x := rfl

@[simp] theorem monGrp_mul (X : Type*) (a b : Magma X) :
    monGrp X (.mul a b) = ⁅monGrp X a, monGrp X b⁆ := rfl

/-- The `q`-th term of the lower central series of a free group (Mathlib indexing). -/
abbrev Gam (X : Type*) (q : ℕ) : Subgroup (FreeGroup X) := graded.Gam (G := FreeGroup X) q

/-- The commutator monomial of a tree of size `m` lies in the `(m-1)`-th term of the lower central
series. -/
theorem monGrp_mem_Gam (c : Magma X) : monGrp X c ∈ Gam X (Magma.size c - 1) := by
  induction c with
  | gen x => simp [Magma.size_gen]
  | mul a b iha ihb =>
      rw [monGrp_mul, Magma.size_mul]
      have h := commutator_lowerCentralSeries_le (FreeGroup X) (Magma.size a - 1) (Magma.size b - 1)
        (Subgroup.commutator_mem_commutator iha ihb)
      have hidx : Magma.size a - 1 + (Magma.size b - 1) + 1 = Magma.size a + Magma.size b - 1 := by
        have ha := Magma.size_pos a
        have hb := Magma.size_pos b
        omega
      rwa [hidx] at h

/-! ## The Magnus leading term -/

/-- The Magnus leading term of `z` at truncation `N`: the Magnus image modulo `fil X N`, shifted
by `1`. -/
def mlt (N : ℕ) (z : FreeGroup X) : FreeAssoc X ⧸ fil X N :=
  ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1

@[simp] theorem mlt_one (N : ℕ) : mlt (X := X) N 1 = 0 := by
  simp [mlt]

/-- The leading term of a generator. -/
theorem mlt_of (N : ℕ) (x : X) :
    mlt N (FreeGroup.of x) =
      Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) (1 : ℤ)) := by
  rw [mlt, magnus_of]
  noncomm_ring

/-- The `N`-th filtration piece of the truncated algebra is zero. -/
theorem filq_self_eq_bot (X : Type*) (N : ℕ) : filq X N N = ⊥ := by
  rw [filq, Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  rw [RingHom.mem_ker]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

theorem mem_filq_self_eq_zero {N : ℕ} {x : FreeAssoc X ⧸ fil X N} (h : x ∈ filq X N N) :
    x = 0 := by
  rw [filq_self_eq_bot X N] at h
  exact h

/-- The "easy half" of the Magnus embedding: the leading term of an element of `γ_k` (Mathlib
indexing: `lowerCentralSeries (k-1)`) lies in the degree-`k` filtration piece. -/
theorem mlt_mem_filq (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    mlt N z ∈ filq X N k := by
  have h := magnus_mem_one_add X N (k - 1) (by omega) z hz
  rwa [Nat.sub_add_cancel hk] at h

/-- The leading term vanishes on `γ_{k+1}`. -/
theorem mlt_eq_zero_of_mem_succ (k : ℕ) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k) :
    mlt (k + 1) z = 0 := by
  have h1 : mlt (k + 1) z ∈ filq X (k + 1) (k + 1) :=
    mlt_mem_filq (k + 1) (k + 1) (by omega) le_rfl (by simpa using hz)
  exact mem_filq_self_eq_zero h1

/-- **Additivity of the leading term on `γ_k`** (when `N ≤ 2k`). -/
theorem mlt_mul (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hN2 : N ≤ 2 * k) {g h : FreeGroup X}
    (hg : g ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1))
    (hh : h ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    mlt N (g * h) = mlt N g + mlt N h := by
  have hsq : mlt N g * mlt N h = 0 := by
    refine mem_filq_self_eq_zero ?_
    refine (filq_antitone X N (by omega : N ≤ k + k)) ?_
    exact mul_mem_filq X N k k (mlt_mem_filq N k hk hkN hg) (mlt_mem_filq N k hk hkN hh)
  have key : mlt N (g * h) = mlt N g + mlt N h + mlt N g * mlt N h := by
    unfold mlt
    rw [map_mul, Units.val_mul]
    noncomm_ring
  rw [key, hsq, add_zero]

/-- The leading term of an inverse. -/
theorem mlt_inv (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (hN2 : N ≤ 2 * k) {w : FreeGroup X}
    (hw : w ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    mlt N w⁻¹ = -mlt N w := by
  have h1 : mlt N (w * w⁻¹) = 0 := by rw [mul_inv_cancel]; exact mlt_one N
  have h2 := mlt_mul N k hk hkN hN2 hw (Subgroup.inv_mem _ hw)
  rw [h1] at h2
  have h3 : mlt N w⁻¹ + mlt N w = 0 := by
    rw [add_comm (mlt N w⁻¹) (mlt N w)]; exact h2.symm
  exact eq_neg_of_add_eq_zero_left h3

/-! ## The commutator identity -/

/-- The pure unit-group identity behind the bracket lemma. -/
theorem commutator_sub_one {R : Type*} [Ring R] (A B : Rˣ) :
    ((⁅A, B⁆ : Rˣ) : R) - 1
      = ((((A : R) - 1) * ((B : R) - 1) - ((B : R) - 1) * ((A : R) - 1))
          * (((A⁻¹ : Rˣ) : R) * ((B⁻¹ : Rˣ) : R))) := by
  have key : (A : R) * (B : R) - (B : R) * (A : R)
      = ((A : R) - 1) * ((B : R) - 1) - ((B : R) - 1) * ((A : R) - 1) := by noncomm_ring
  rw [← key, commutatorElement_def, sub_mul]
  simp only [Units.val_mul]
  have h3 : ((B : R) * (A : R)) * (((A⁻¹ : Rˣ) : R) * ((B⁻¹ : Rˣ) : R)) = 1 := by
    have hgrp : (B * A * (A⁻¹ * B⁻¹) : Rˣ) = 1 := by group
    rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hgrp, Units.val_one]
  rw [h3]
  simp only [mul_assoc]

/-- The filtration pieces of the truncated algebra are two-sided. -/
instance instIsTwoSidedFilq (X : Type*) (N k : ℕ) : (filq X N k).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
      (Ideal.Quotient.mk_surjective)).1 ha
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ (Ideal.IsTwoSided.mul_mem_of_left b' ha')

/-- The inverse of a Magnus image is congruent to `1` modulo the first filtration piece. -/
theorem magnus_inv_sub_one_mem (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) {z : FreeGroup X}
    (hz : z ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (k - 1)) :
    (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      filq X N 1 := by
  have hz' : mlt N z ∈ filq X N k := mlt_mem_filq N k hk hkN hz
  have h1 : (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
      * ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h : (((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      = - ((((magnus X N z)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)
          * (((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1)) := by
    rw [mul_sub, mul_one, h1, neg_sub]
  rw [h]
  refine neg_mem ?_
  rw [show ((magnus X N z : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      = mlt N z from rfl]
  exact Ideal.mul_mem_left _ _ ((filq_antitone X N hk) hz')

/-- **The bracket lemma**: for `u ∈ γ_p` and `v ∈ γ_q` the leading term of `⁅u,v⁆` agrees modulo
`filq X N (p+q+1)` with the ring commutator of the leading terms. -/
theorem mlt_commutator (N p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q + 1 ≤ N)
    {u v : FreeGroup X}
    (hu : u ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (p - 1))
    (hv : v ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (q - 1)) :
    mlt N ⁅u,v⁆ - (mlt N u * mlt N v - mlt N v * mlt N u) ∈ filq X N (p + q + 1) := by
  have hpu : p ≤ N := by omega
  have hqv : q ≤ N := by omega
  have hmemu : mlt N u ∈ filq X N p := mlt_mem_filq N p hp hpu hu
  have hmemv : mlt N v ∈ filq X N q := mlt_mem_filq N q hq hqv hv
  have hinvu : (((magnus X N u)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      ∈ filq X N 1 := magnus_inv_sub_one_mem N p hp hpu hu
  have hinvv : (((magnus X N v)⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      ∈ filq X N 1 := magnus_inv_sub_one_mem N q hq hqv hv
  set A : (FreeAssoc X ⧸ fil X N)ˣ := magnus X N u with hA
  set B : (FreeAssoc X ⧸ fil X N)ˣ := magnus X N v with hB
  have hAu : ((A : FreeAssoc X ⧸ fil X N)) - 1 = mlt N u := rfl
  have hBv : ((B : FreeAssoc X ⧸ fil X N)) - 1 = mlt N v := rfl
  have hmap : magnus X N ⁅u,v⁆ = ⁅A, B⁆ := by
    rw [hA, hB, map_commutatorElement]
  have hlt : mlt N ⁅u,v⁆
      = ((((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
          - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1))
        * ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) := by
    rw [mlt, hmap, commutator_sub_one]
  have hY : ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
        * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1
      ∈ filq X N 1 := by
    have h2 : ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
          * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1
        = ((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)) - 1)
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
          + ((((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N)) - 1) := by
      noncomm_ring
    rw [h2]
    exact Submodule.add_mem _
      (Ideal.mul_mem_right _ _ (by rw [hA]; exact hinvu))
      (by rw [hB]; exact hinvv)
  have hX : (((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
      - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1)
      ∈ filq X N (p + q) := by
    rw [hAu, hBv]
    refine Submodule.sub_mem _ (mul_mem_filq X N p q hmemu hmemv) ?_
    exact (Nat.add_comm p q) ▸ mul_mem_filq X N q p hmemv hmemu
  have hkey : mlt N ⁅u,v⁆ - (mlt N u * mlt N v - mlt N v * mlt N u)
      = ((((A : FreeAssoc X ⧸ fil X N)) - 1) * (((B : FreeAssoc X ⧸ fil X N)) - 1)
          - (((B : FreeAssoc X ⧸ fil X N)) - 1) * (((A : FreeAssoc X ⧸ fil X N)) - 1))
        * (((((A⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))
            * (((B⁻¹ : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N))) - 1) := by
    rw [hlt, hAu, hBv]
    noncomm_ring
  rw [hkey]
  exact mul_mem_filq X N (p + q) 1 hX hY

/-! ## The graded pieces and the class maps -/

/-- The `q`-th graded piece `γ_q/γ_{q+1}`, written additively. -/
abbrev Lam (X : Type*) (q : ℕ) : Type _ := Additive (graded.GLam (G := FreeGroup X) q)

/-- The class map `γ_q → γ_q/γ_{q+1}`. -/
def clMul (X : Type*) (q : ℕ) : Gam X q →* graded.GLam (G := FreeGroup X) q where
  toFun x := QuotientGroup.mk x
  map_one' := rfl
  map_mul' := fun a b => rfl

/-- The class map, additively. -/
def cl (X : Type*) (q : ℕ) : Additive (Gam X q) →+ Lam X q := (clMul X q).toAdditive

/-- The class in `Λ_q` of a member of `γ_q`. -/
def cls (X : Type*) (q : ℕ) (x : Gam X q) : Lam X q := cl X q (Additive.ofMul x)

@[simp] theorem cls_apply (X : Type*) (q : ℕ) (x : Gam X q) :
    cls X q x = Additive.ofMul (clMul X q x) := rfl

/-- The class of `1` is zero. -/
@[simp] theorem cls_one (q : ℕ) : cls X q (1 : Gam X q) = 0 := rfl

/-- The class of a product is the sum of the classes. -/
theorem cls_mul (q : ℕ) (x y : Gam X q) : cls X q (x * y) = cls X q x + cls X q y := rfl

/-- The class of an inverse is the negative of the class. -/
theorem cls_inv (q : ℕ) (x : Gam X q) : cls X q x⁻¹ = -cls X q x := by
  have h : cls X q x⁻¹ + cls X q x = 0 := by
    rw [add_comm, ← cls_mul, mul_inv_cancel, show cls X q 1 = 0 from rfl]
  exact eq_neg_of_add_eq_zero_left h

/-- The class is zero exactly on `γ_{q+1}`. -/
theorem cls_eq_zero_iff {q : ℕ} {x : Gam X q} :
    cls X q x = 0 ↔ (x : FreeGroup X) ∈ Gam X (q + 1) := by
  change (clMul X q x : graded.GLam (G := FreeGroup X) q) = 1 ↔ _
  rw [clMul]
  exact QuotientGroup.eq_one_iff x

/-- The trees of size `k`. -/
abbrev TreeIdx (X : Type*) (k : ℕ) := {c : Magma X // Magma.size c = k}

/-- The class in `Λ_{k-1}` of the commutator monomial of a tree of size `k`. -/
def treeClOf (X : Type*) (k : ℕ) (c : TreeIdx X k) : Lam X (k - 1) :=
  cls X (k - 1) ⟨monGrp X c.1, by simpa [c.2] using monGrp_mem_Gam c.1⟩

/-- The linear map sending a tree of size `k` to the class of its commutator monomial. -/
def treeToLam (X : Type*) (k : ℕ) : (TreeIdx X k →₀ ℤ) →ₗ[ℤ] Lam X (k - 1) :=
  Finsupp.linearCombination ℤ (treeClOf X k)

@[simp] theorem treeToLam_single (k : ℕ) (c : TreeIdx X k) :
    treeToLam X k (Finsupp.single c 1) = treeClOf X k c := by
  rw [treeToLam, Finsupp.linearCombination_single, one_smul]

@[simp] theorem treeToLam_gen (x : X) :
    treeClOf X 1 ⟨Magma.gen x, rfl⟩ = cls X 0 ⟨FreeGroup.of x, Subgroup.mem_top _⟩ := rfl

end Work.SSGRoute.prop5.lctf
