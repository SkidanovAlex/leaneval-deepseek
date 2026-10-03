/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Karrass--Magnus--Solitar torsion theorem

This module collects the reusable API of the Karrass--Magnus--Solitar torsion theorem: the
transfer of order and finite order along isomorphisms, conjugations and injective homomorphisms,
the root statement `KMSRoot`, and the two base cases of the induction.  The theorem itself
(`Work.OROneRel.kms_torsion_at`) is proved in `Submission/Work/OROneRel/kms_torsion_at.lean`.

`Work.OROneRel.KMSTorsionAt r`  (`r : FreeGroup α` arbitrary),

i.e. for `r = u ^ l` with `1 ≤ l` and `u` not a proper power, the class of `u` in `⟨α | r⟩` has
order exactly `l` and every element of finite order in `⟨α | r⟩` is conjugate to a power of that
class.

## The shape of the argument

Everything is reduced to the following statement about a *single* root presentation
(`Work.OROneRel.KMSRoot u l`): for `u : FreeGroup α` and `1 ≤ l`, in `⟨α | u ^ l⟩`
the class of `u` has order exactly `l`, and every torsion element is conjugate to a power of it.

* `Work.OROneRel.kmsRoot_of_hnn` is the induction step: an isomorphism of `⟨α | u ^ l⟩` with an
  HNN extension of a shorter root presentation `⟨β | v ^ l⟩` which carries the class of `u` to a
  conjugate of the class of `v` transfers `KMSRoot v l` to `KMSRoot u l`.  The torsion input is
  `Work.ORLocInd.HNN.finiteOrder_conj_mem_of` (torsion elements of an HNN extension are conjugate
  into the base).
* `Work.OROneRel.kmsRoot_of_letterPow` is the base case: `u` a one-letter word, where
  `⟨α | u ^ l⟩ ≅ ℤ/l ∗ F(α \ {a})` (`presentedGroup_of_zpow_iso_coprod_zmod`) and Kurosh's
  torsion theorem for free products (`coprod_isOfFinOrder_conj`) describes the torsion.
* `Work.OROneRel.kmsRoot_of_magnusStep` assembles the two by strong induction on `relatorNorm`,
  using the Magnus step `Work.OROneRel.HasMagnusStep` (the classical Magnus--Moldavanskii
  decomposition of a one-relator presentation, with the root tracked up to conjugacy; proved in
  `Submission/Work/OROneRel/magnus_step_root.lean`).
-/
import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.letterPow
import Submission.Work.OROneRel.presentedGroup_of_zpow_iso_coprod_zmod
import Submission.Work.OROneRel.orderOf_of_terminal_zpow
import Submission.Work.OROneRel.kms_torsion_terminal_conj
import Submission.Work.ORLocInd.HNN.finiteOrder_conj_mem_of

namespace Work.OROneRel

universe u

/-! ## Transfer of order and torsion along isomorphisms and conjugation -/

section Transfer

variable {G H : Type*} [Group G] [Group H]

/-- The order of an element is unchanged by an isomorphism. -/
theorem orderOf_mulEquiv (e : G ≃* H) (x : G) : orderOf (e x) = orderOf x := by
  refine Nat.dvd_antisymm (orderOf_map_dvd e.toMonoidHom x) ?_
  have h := orderOf_map_dvd e.symm.toMonoidHom (e x)
  have h2 : e.symm.toMonoidHom (e x) = x := by
    change e.symm (e x) = x
    exact MulEquiv.symm_apply_apply e x
  rwa [h2] at h

/-- An isomorphism reflects finite order. -/
theorem isOfFinOrder_mulEquiv_iff (e : G ≃* H) (x : G) :
    IsOfFinOrder (e x) ↔ IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, e.injective (by rw [map_pow, h, map_one])⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [← map_pow, h, map_one]⟩

/-- The `n`-th power of a conjugate. -/
theorem pow_conj_eq (c x : G) (n : ℕ) : (c * x * c⁻¹) ^ n = c * x ^ n * c⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

/-- The order of an element is unchanged by conjugation. -/
theorem orderOf_conj (c x : G) : orderOf (c * x * c⁻¹) = orderOf x := by
  refine Nat.dvd_antisymm ?_ ?_
  · refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_conj_eq, pow_orderOf_eq_one]; group
  · have h : x = c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ := by group
    conv_lhs => rw [h]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_conj_eq, pow_orderOf_eq_one]; group

/-- Finite order is unchanged by conjugation. -/
theorem isOfFinOrder_conj_iff (c x : G) : IsOfFinOrder (c * x * c⁻¹) ↔ IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨n, hn, ?_⟩
    have h' : c * x ^ n * c⁻¹ = 1 := by rw [← pow_conj_eq, h]
    have h'' : c⁻¹ * (c * x ^ n * c⁻¹) * c = 1 := by
      rw [h']; group
    have h3 : c⁻¹ * (c * x ^ n * c⁻¹) * c = x ^ n := by group
    rw [h3] at h''
    exact h''
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [pow_conj_eq, h]; group⟩

end Transfer

/-! ## The base group of an HNN extension -/

section HNNOf

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- The embedding of the base group into an HNN extension preserves orders. -/
theorem orderOf_hnn_of (g : G) : orderOf (HNNExtension.of (φ := φ) g) = orderOf g := by
  refine Nat.dvd_antisymm (orderOf_map_dvd HNNExtension.of g) ?_
  refine orderOf_dvd_of_pow_eq_one ?_
  apply HNNExtension.of_injective (φ := φ)
  rw [map_pow, pow_orderOf_eq_one, map_one]

/-- The embedding of the base group into an HNN extension preserves finite order. -/
theorem isOfFinOrder_hnn_of_iff (g : G) :
    IsOfFinOrder (HNNExtension.of (φ := φ) g) ↔ IsOfFinOrder g := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, HNNExtension.of_injective (φ := φ) (by rw [map_pow, h, map_one])⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [← map_pow, h, map_one]⟩

end HNNOf

/-! ## The Karrass--Magnus--Solitar statement for one root presentation -/

/-- **Karrass--Magnus--Solitar at a single root presentation.**  For `u : FreeGroup α` and
`1 ≤ l`, the class of `u` in `⟨α | u ^ l⟩` has order exactly `l`, and every element of finite order
in `⟨α | u ^ l⟩` is conjugate to a power of that class. -/
def KMSRoot {α : Type u} (u : FreeGroup α) (l : ℕ) : Prop :=
  orderOf (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) = l ∧
    ∀ g : PresentedGroup ({u ^ l} : Set (FreeGroup α)), IsOfFinOrder g →
      ∃ k : ℕ, ∃ c : PresentedGroup ({u ^ l} : Set (FreeGroup α)),
        g = c * (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) ^ k * c⁻¹

/-- The Magnus--Moldavanskii step of the induction, with the root tracked up to conjugacy: either
`u` is a one-letter word (up to the trivial element), or `⟨α | u ^ l⟩` is an HNN extension of a
presentation `⟨β | v ^ l⟩` with the *same* exponent `l` and a shorter root `v`, and the class of `u`
becomes conjugate to the class of `v` in the base. -/
def HasMagnusStep : Prop :=
  ∀ {α : Type u} (u : FreeGroup α) (l : ℕ), 1 ≤ l → ¬ IsProperPower u →
    relatorNorm u ≤ 1 ∨
      ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧
        relatorNorm v < relatorNorm u ∧
        ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B),
          ∃ (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
                HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ)
            (c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
            e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
              c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹

/-- **The induction step.**  If `⟨α | u ^ l⟩` is an HNN extension of `⟨β | v ^ l⟩` and the class of
`u` is conjugate to the class of `v` in the base, then `KMSRoot v l` implies `KMSRoot u l`. -/
theorem kmsRoot_of_hnn {α β : Type u} {u : FreeGroup α} {v : FreeGroup β} {l : ℕ}
    {A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))} {φ : A ≃* B}
    {e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
      HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ}
    {c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ}
    (hc : e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
      c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹)
    (hv : KMSRoot v l) : KMSRoot u l := by
  refine ⟨?_, ?_⟩
  · have h1 : orderOf (e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u))
        = orderOf (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) := orderOf_mulEquiv e _
    have h2 : orderOf (HNNExtension.of (φ := φ)
        (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v)) = l := by
      rw [orderOf_hnn_of]; exact hv.1
    rw [← h1, hc, orderOf_conj, h2]
  · intro g hg
    have hge : IsOfFinOrder (e g) := (isOfFinOrder_mulEquiv_iff e g).mpr hg
    obtain ⟨c', k, hk⟩ := Work.ORLocInd.HNN.finiteOrder_conj_mem_of φ (e g) hge
    -- `of k` is conjugate to `e g`, hence `k` has finite order
    have hmem : IsOfFinOrder (HNNExtension.of (φ := φ) k) := by
      rw [← hk]; exact (isOfFinOrder_conj_iff c' (e g)).mpr hge
    obtain ⟨j, d, hd⟩ := hv.2 k ((isOfFinOrder_hnn_of_iff k).mp hmem)
    -- rewrite `e g` in terms of `e (mk u)`
    have hbase : HNNExtension.of (φ := φ) (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v)
        = c⁻¹ * e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) * c := by
      rw [hc]; group
    refine ⟨j, e.symm (c'⁻¹ * HNNExtension.of (φ := φ) d * c⁻¹), ?_⟩
    have hkey : e g = (c'⁻¹ * HNNExtension.of (φ := φ) d * c⁻¹)
        * (e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)) ^ j
        * (c'⁻¹ * HNNExtension.of (φ := φ) d * c⁻¹)⁻¹ := by
      have h1 : e g = c'⁻¹ * HNNExtension.of (φ := φ) k * c' := by rw [← hk]; group
      rw [h1, hd, map_mul, map_mul, map_pow, map_inv, hbase]
      set X := e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) with hX
      have hpow : (c⁻¹ * X * c) ^ j = c⁻¹ * X ^ j * c := by
        simpa using pow_conj_eq c⁻¹ X j
      rw [hpow]
      group
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply]
    exact hkey


/-! ## An order/torsion transfer API for injective homomorphisms -/

section Injective

variable {G H : Type*} [Group G] [Group H]

/-- An injective homomorphism preserves orders. -/
theorem orderOf_of_injective (f : G →* H) (hf : Function.Injective f) (x : G) :
    orderOf (f x) = orderOf x := by
  refine Nat.dvd_antisymm (orderOf_map_dvd f x) ?_
  refine orderOf_dvd_of_pow_eq_one ?_
  exact hf (by rw [map_pow, pow_orderOf_eq_one, map_one])

/-- An injective homomorphism reflects and preserves finite order. -/
theorem isOfFinOrder_of_injective_iff (f : G →* H) (hf : Function.Injective f) (x : G) :
    IsOfFinOrder (f x) ↔ IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, hf (by rw [map_pow, h, map_one])⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [← map_pow, h, map_one]⟩

end Injective

/-! ## The base case: `u` is a generator or the inverse of a generator -/

/-- In a group where `x ^ l = 1` with `1 ≤ l`, every natural power of `x` is a natural power of
`x⁻¹`. -/
theorem exists_pow_inv_of_pow {G : Type*} [Group G] {x : G} {l : ℕ} (hl : 1 ≤ l)
    (hx : x ^ l = 1) (k : ℕ) : ∃ k' : ℕ, (x⁻¹) ^ k' = x ^ k := by
  refine ⟨l - k % l, ?_⟩
  have hj : k % l ≤ l := le_of_lt (Nat.mod_lt k (Nat.lt_of_lt_of_le Nat.zero_lt_one hl))
  have h1 : x ^ (l - k % l) * x ^ (k % l) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj, hx]
  have h2 : x ^ (l - k % l) = (x ^ (k % l))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : (x⁻¹) ^ (l - k % l) = x ^ (k % l) := by rw [inv_pow, h2, inv_inv]
  have h4 : x ^ k = x ^ (k % l) :=
    pow_eq_pow_of_modEq (Nat.mod_modEq k l).symm hx
  rw [h3, h4]

/-- The base case of the induction: `u` is a one-letter word. -/
theorem kmsRoot_of_letterPow {α : Type u} (a : α) (s : Bool) (l : ℕ) (hl : 1 ≤ l) :
    KMSRoot (letterPow a s) l := by
  classical
  have hlz : (l : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hl)
  cases s
  · -- `u = (of a)⁻¹`, so the relator is `of a ^ (-(l : ℤ))`
    have hlzn : -(l : ℤ) ≠ 0 := neg_ne_zero.mpr hlz
    have hset : ({letterPow a false ^ l} : Set (FreeGroup α))
        = {FreeGroup.of a ^ (-(l : ℤ))} := by
      rw [Set.singleton_eq_singleton_iff, letterPow_false, inv_pow, zpow_neg, zpow_natCast]
    have hof : PresentedGroup.of (rels := ({FreeGroup.of a ^ (-(l : ℤ))} : Set (FreeGroup α))) a
        = PresentedGroup.mk ({FreeGroup.of a ^ (-(l : ℤ))} : Set (FreeGroup α))
            (FreeGroup.of a) := rfl
    have hroot : (PresentedGroup.mk ({FreeGroup.of a ^ (-(l : ℤ))} : Set (FreeGroup α))
          (letterPow a false))
        = (PresentedGroup.of (rels := ({FreeGroup.of a ^ (-(l : ℤ))} : Set (FreeGroup α))) a)⁻¹ := by
      rw [letterPow_false, map_inv, ← hof]
    have hord : orderOf (PresentedGroup.of (rels := ({FreeGroup.of a ^ (-(l : ℤ))} : Set (FreeGroup α))) a) = l := by
      simpa using orderOf_of_terminal_zpow (α := α) a (-(l : ℤ)) hlzn
    unfold KMSRoot
    rw [hset]
    refine ⟨?_, ?_⟩
    · rw [hroot, orderOf_inv, hord]
    · intro g hg
      obtain ⟨c, k, hk⟩ := kms_torsion_terminal_conj (α := α) a (-(l : ℤ)) hlzn hg
      have hxl : (PresentedGroup.of (rels := ({FreeGroup.of a ^ (-(l : ℤ))} : Set (FreeGroup α))) a) ^ l = 1 := by
        have h := pow_orderOf_eq_one
          (PresentedGroup.of (rels := ({FreeGroup.of a ^ (-(l : ℤ))} : Set (FreeGroup α))) a)
        rwa [hord] at h
      obtain ⟨k', hk'⟩ := exists_pow_inv_of_pow hl hxl k
      refine ⟨k', c, ?_⟩
      rw [hroot, hk, ← hk']
  · -- `u = of a`, so the relator is `of a ^ (l : ℤ)`
    have hset : ({letterPow a true ^ l} : Set (FreeGroup α))
        = {FreeGroup.of a ^ (l : ℤ)} := by
      rw [Set.singleton_eq_singleton_iff, letterPow_true, zpow_natCast]
    have hroot : (PresentedGroup.mk ({FreeGroup.of a ^ (l : ℤ)} : Set (FreeGroup α))
          (letterPow a true))
        = PresentedGroup.of (rels := ({FreeGroup.of a ^ (l : ℤ)} : Set (FreeGroup α))) a := rfl
    have hord : orderOf (PresentedGroup.of (rels := ({FreeGroup.of a ^ (l : ℤ)} : Set (FreeGroup α))) a) = l := by
      simpa using orderOf_of_terminal_zpow (α := α) a (l : ℤ) hlz
    unfold KMSRoot
    rw [hset]
    refine ⟨?_, ?_⟩
    · rw [hroot, hord]
    · intro g hg
      obtain ⟨c, k, hk⟩ := kms_torsion_terminal_conj (α := α) a (l : ℤ) hlz hg
      refine ⟨k, c, ?_⟩
      rw [hroot, hk]

/-- A word of norm at most one is trivial, or a one-letter word. -/
theorem eq_one_or_exists_letterPow_of_relatorNorm_le_one {α : Type u} {u : FreeGroup α}
    (h : relatorNorm u ≤ 1) : u = 1 ∨ ∃ (a : α) (s : Bool), u = letterPow a s := by
  classical
  have hlen : (FreeGroup.toWord u).length ≤ 1 := by
    simpa [relatorNorm, FreeGroup.norm] using h
  rcases List.eq_nil_or_concat (FreeGroup.toWord u) with hnil | ⟨L, c, hc⟩
  · exact Or.inl (FreeGroup.toWord_eq_nil_iff.mp hnil)
  · have hL : L.length = 0 := by
      rw [hc, List.length_concat] at hlen
      omega
    have hLnil : L = [] := List.length_eq_zero_iff.mp hL
    refine Or.inr ⟨c.1, c.2, ?_⟩
    rw [← FreeGroup.mk_toWord (x := u), hc, hLnil]
    rfl

/-- **The base case**: `relatorNorm u ≤ 1`. -/
theorem kmsRoot_of_relatorNorm_le_one {α : Type u} {u : FreeGroup α} (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ IsProperPower u) (h1 : relatorNorm u ≤ 1) : KMSRoot u l := by
  rcases eq_one_or_exists_letterPow_of_relatorNorm_le_one h1 with rfl | ⟨a, s, rfl⟩
  · exact absurd isProperPower_one hu
  · exact kmsRoot_of_letterPow a s l hl

end Work.OROneRel
