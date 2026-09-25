import Mathlib
import Submission.NK.NUV2.RouteC.cyclic_cocycle
import Submission.NK.NUV2.RouteE.downward
import Submission.NK.NUV2.RouteE.upward
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero

/-!
# The carry cocycle of a finite cyclic group, and the cyclic criterion

Let `G` be a finite group with a chosen isomorphism `e : G ≃* Multiplicative (ZMod n)` (i.e. an
explicit cyclic structure).  The *carry cocycle*

`carryCocycle e p = stdC n (e p.1, e p.2)`

is the pullback of the standard carry `2`-cocycle of `ℤ/n` (whose class generates
`H²(ℤ/n, ℤ) ≅ ℤ/n`).  This file provides it, proves the two properties that the character-formula
route to local class field theory needs, and derives the *cyclic criterion*

`map φ 2 (carry class) = 0 ↔ φ(1) ∈ range A.norm`

for a `ℤ[G]`-module `A` and a morphism `φ : ℤ ⟶ A` of representations.

* `sum_carryCocycle`: the sum of the cocycle over the second coordinate equal to the chosen
  generator is `1`; this is the numerical content of the "downward" direction.
* `carryCocycle_mem_cocycles₂`: the pullback is a `2`-cocycle.
* `mem_range_norm_of_d₁₂_eq_carryCocycle_smul`: **the downward direction**: if the pointwise
  product of the carry cocycle with `a` is a coboundary then `a` lies in the range of the norm.
-/

open scoped BigOperators

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {G : Type} [Group G] [Fintype G]

/-- **The carry cocycle** of the cyclic structure `e : G ≃* Multiplicative (ZMod n)`: the pullback of
the standard cocycle `stdC n` along `e`. -/
noncomputable def carryCocycle {n : ℕ} (e : G ≃* Multiplicative (ZMod n)) (p : G × G) : ℕ :=
  NK.NUV2.RouteC.stdC n (e p.1, e p.2)

/-- The chosen generator of `G` attached to the cyclic structure `e`: the preimage of `ofAdd 1`. -/
noncomputable def carryGenerator {n : ℕ} (e : G ≃* Multiplicative (ZMod n)) : G :=
  e.symm (Multiplicative.ofAdd (1 : ZMod n))

theorem carryCocycle_apply {n : ℕ} (e : G ≃* Multiplicative (ZMod n)) (p : G × G) :
    carryCocycle e p = NK.NUV2.RouteC.stdC n (e p.1, e p.2) := rfl

theorem apply_carryGenerator {n : ℕ} (e : G ≃* Multiplicative (ZMod n)) :
    e (carryGenerator e) = Multiplicative.ofAdd (1 : ZMod n) :=
  e.apply_symm_apply _

/-- The values of the carry cocycle are `0` or `1`, in particular at most `1`. -/
theorem carryCocycle_le_one {n : ℕ} (e : G ≃* Multiplicative (ZMod n)) (p : G × G) :
    carryCocycle e p ≤ 1 := by
  unfold carryCocycle NK.NUV2.RouteC.stdC
  split <;> omega

/-- **The numerical content of the downward direction**: the sum of the carry cocycle over the
second coordinate equal to the chosen generator is `1`. -/
theorem sum_carryCocycle {n : ℕ} [NeZero n] (hn : 1 < n)
    (e : G ≃* Multiplicative (ZMod n)) :
    (∑ i : G, ((carryCocycle e (i, carryGenerator e) : ℕ) : ℤ)) = 1 := by
  classical
  have hterm : ∀ i : G, carryCocycle e (i, carryGenerator e)
      = NK.NUV2.RouteC.stdC n (e i, Multiplicative.ofAdd (1 : ZMod n)) := by
    intro i
    rw [carryCocycle_apply, apply_carryGenerator]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hterm i])]
  refine (Fintype.sum_equiv e.toEquiv
    (fun i : G => ((NK.NUV2.RouteC.stdC n (e i,
      Multiplicative.ofAdd (1 : ZMod n)) : ℕ) : ℤ))
    (fun r : Multiplicative (ZMod n) => ((NK.NUV2.RouteC.stdC n (r,
      Multiplicative.ofAdd (1 : ZMod n)) : ℕ) : ℤ)) (fun i => rfl)).trans ?_
  exact NK.NUV2.RouteE.sum_stdC_ofAdd_mul_one hn

/-! ## The criterion

The two halves of Tate periodicity for the carry class: the "downward" half (the class of the
pointwise product of the cocycle with `a` vanishes only if `a` is a norm) is a telescoping sum
computation; the "upward" half is `NK.NUV2.RouteE.map_eq_zero_of_mem_range_norm`. -/

/-- The `k`-valued sum of the carry cocycle along the chosen generator is `1` (cast of
`sum_carryCocycle`). -/
theorem sum_carryCocycle_cast {k : Type} [CommRing k] {n : ℕ} [NeZero n] (hn : 1 < n)
    (e : G ≃* Multiplicative (ZMod n)) :
    (∑ i : G, ((carryCocycle e (i, carryGenerator e) : ℕ) : k)) = 1 := by
  have h := congrArg (fun z : ℤ => (z : k)) (sum_carryCocycle hn e)
  simpa using h

/-- **The downward direction of the cyclic criterion, in cocycle form.**  If a `1`-cochain `b`
witnesses that the pointwise product of the carry cocycle with `a` is a `2`-coboundary, then `a`
lies in the range of the norm map. -/
theorem mem_range_norm_of_d₁₂_eq_carryCocycle_smul {k : Type} [CommRing k] {n : ℕ} [NeZero n]
    (hn : 1 < n) (e : G ≃* Multiplicative (ZMod n)) (A : Rep k G) (a : A) (b : G → A)
    (hb : ∀ p : G × G, (groupCohomology.d₁₂ A).hom b p = ((carryCocycle e p : ℕ) : k) • a) :
    a ∈ LinearMap.range A.norm.hom.toLinearMap := by
  classical
  set q : G := carryGenerator e with hq
  have hL : (∑ i : G, (groupCohomology.d₁₂ A).hom b (i, q)) = A.norm.hom (b q) := by
    have hterm : ∀ i : G,
        (groupCohomology.d₁₂ A).hom b (i, q) = A.ρ i (b q) - b (i * q) + b i := by
      intro i
      rw [groupCohomology.d₁₂_hom_apply]
    have hre : (∑ i : G, b (i * q)) = ∑ i, b i :=
      Fintype.sum_equiv (Equiv.mulRight q) (fun i => b (i * q)) b (fun i => rfl)
    calc (∑ i : G, (groupCohomology.d₁₂ A).hom b (i, q))
        = ∑ i, (A.ρ i (b q) - b (i * q) + b i) := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, A.ρ i (b q)) - (∑ i, b (i * q)) + (∑ i, b i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ i, A.ρ i (b q)) := by rw [hre, sub_add_cancel]
      _ = A.norm.hom (b q) := (NK.NUV2.RouteC.norm_apply_eq_sum A (b q)).symm
  have hR : (∑ i : G, ((carryCocycle e (i, q) : ℕ) : k) • a) = a := by
    rw [← Finset.sum_smul, sum_carryCocycle_cast (k := k) hn e, one_smul]
  have hkey : A.norm.hom (b q) = a := by
    rw [← hL, ← hR]
    exact Finset.sum_congr rfl (fun i _ => hb (i, q))
  exact ⟨b q, hkey⟩

end NK.NUV2.RouteE

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped BigOperators

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Fintype G]

/-! ## The carry cocycle is a genuine `2`-cocycle

The values of `stdC n` are `0` or `1`; its `n`-fold multiples are the values of the standard
`ℤ`-valued extension cocycle `z (x,y) = x.val + y.val - (x+y).val`, for which the cocycle condition
is the trivial cancellation of `s(x) + s(y) - s(x ⊕ y)` (with `s` the representative map). -/

/-- **The `n`-fold multiple of `stdC` in terms of `ZMod.val`**: the standard `ℤ`-valued cocycle of
the cyclic group. -/
theorem stdC_mul_val (n : ℕ) [NeZero n] (p : Multiplicative (ZMod n) × Multiplicative (ZMod n)) :
    (n : ℤ) * (NK.NUV2.RouteC.stdC n p : ℤ)
      = ((p.1.toAdd).val : ℤ) + ((p.2.toAdd).val : ℤ) - (((p.1.toAdd) + (p.2.toAdd)).val : ℤ) := by
  have hlt1 : (p.1.toAdd).val < n := ZMod.val_lt _
  have hlt2 : (p.2.toAdd).val < n := ZMod.val_lt _
  rcases lt_or_ge ((p.1.toAdd).val + (p.2.toAdd).val) n with hv | hv
  · rw [NK.NUV2.RouteC.stdC, if_pos hv,
      ZMod.val_add_of_lt hv]
    push_cast
    ring
  · rw [NK.NUV2.RouteC.stdC, if_neg (by omega), ZMod.val_add]
    have hmod : ((p.1.toAdd).val + (p.2.toAdd).val) % n
        = (p.1.toAdd).val + (p.2.toAdd).val - n := by
      obtain ⟨t, ht⟩ : ∃ t, (p.1.toAdd).val + (p.2.toAdd).val = n + t :=
        ⟨(p.1.toAdd).val + (p.2.toAdd).val - n, by omega⟩
      have htlt : t < n := by omega
      rw [ht, Nat.add_mod_left, Nat.mod_eq_of_lt htlt]
      omega
    rw [hmod]
    have hle : n ≤ (p.1.toAdd).val + (p.2.toAdd).val := hv
    push_cast [Nat.cast_sub hle]
    ring

/-- **The cocycle condition for the standard carry cocycle** (in the `ℤ`-cochain model). -/
theorem stdC_cocycle_condition (n : ℕ) [NeZero n] (g h j : Multiplicative (ZMod n)) :
    (NK.NUV2.RouteC.stdC n (h, j) : ℤ) - (NK.NUV2.RouteC.stdC n (g * h, j) : ℤ)
      + (NK.NUV2.RouteC.stdC n (g, h * j) : ℤ) - (NK.NUV2.RouteC.stdC n (g, h) : ℤ) = 0 := by
  have hA := stdC_mul_val n (h, j)
  have hB := stdC_mul_val n (g * h, j)
  have hC := stdC_mul_val n (g, h * j)
  have hD := stdC_mul_val n (g, h)
  have hassoc : (Multiplicative.toAdd g + Multiplicative.toAdd h + Multiplicative.toAdd j)
      = (Multiplicative.toAdd g + (Multiplicative.toAdd h + Multiplicative.toAdd j)) :=
    add_assoc _ _ _
  have hkey : (n : ℤ) * ((NK.NUV2.RouteC.stdC n (h, j) : ℤ)
        - (NK.NUV2.RouteC.stdC n (g * h, j) : ℤ)
        + (NK.NUV2.RouteC.stdC n (g, h * j) : ℤ)
        - (NK.NUV2.RouteC.stdC n (g, h) : ℤ)) = 0 := by
    rw [show (n : ℤ) * ((NK.NUV2.RouteC.stdC n (h, j) : ℤ)
          - (NK.NUV2.RouteC.stdC n (g * h, j) : ℤ)
          + (NK.NUV2.RouteC.stdC n (g, h * j) : ℤ)
          - (NK.NUV2.RouteC.stdC n (g, h) : ℤ))
        = (n : ℤ) * (NK.NUV2.RouteC.stdC n (h, j) : ℤ)
          - (n : ℤ) * (NK.NUV2.RouteC.stdC n (g * h, j) : ℤ)
          + (n : ℤ) * (NK.NUV2.RouteC.stdC n (g, h * j) : ℤ)
          - (n : ℤ) * (NK.NUV2.RouteC.stdC n (g, h) : ℤ) from by ring]
    rw [hA, hB, hC, hD]
    simp only [Prod.fst, Prod.snd]
    rw [show Multiplicative.toAdd (g * h) = Multiplicative.toAdd g + Multiplicative.toAdd h
        from rfl,
      show Multiplicative.toAdd (h * j) = Multiplicative.toAdd h + Multiplicative.toAdd j
        from rfl,
      hassoc]
    ring
  have hn0 : (n : ℤ) ≠ 0 := by
    have := NeZero.ne n
    exact_mod_cast this
  exact (mul_eq_zero.mp hkey).resolve_left hn0

/-- **`stdC n` is a `2`-cocycle with values in `ℤ`.** -/
theorem stdC_mem_cocycles₂_int (n : ℕ) [NeZero n] :
    (fun p : Multiplicative (ZMod n) × Multiplicative (ZMod n) =>
        (NK.NUV2.RouteC.stdC n p : ℤ))
      ∈ groupCohomology.cocycles₂ (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) := by
  rw [groupCohomology.mem_cocycles₂_def]
  intro g h j
  rw [Rep.trivial_ρ, LinearMap.id_apply]
  exact stdC_cocycle_condition n g h j

/-- **The carry cocycle of `G` is a `2`-cocycle** (pullback of `stdC` along the cyclic
structure). -/
theorem carryCocycle_mem_cocycles₂_int {n : ℕ} [NeZero n] (e : G ≃* Multiplicative (ZMod n)) :
    (fun p : G × G => ((carryCocycle e p : ℕ) : ℤ))
      ∈ groupCohomology.cocycles₂ (Rep.trivial ℤ G ℤ) := by
  rw [groupCohomology.mem_cocycles₂_def]
  intro g h j
  rw [Rep.trivial_ρ, LinearMap.id_apply]
  have hmodel := stdC_cocycle_condition n (e g) (e h) (e j)
  have h1 : e (g * h) = e g * e h := map_mul e g h
  have h2 : e (h * j) = e h * e j := map_mul e h j
  rw [← h1, ← h2] at hmodel
  exact hmodel

end NK.NUV2.RouteE

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {G : Type} [Group G] [Fintype G]

open scoped BigOperators
open CategoryTheory

/-- **The carry class** of the cyclic structure `e`: the cohomology class of the pullback of the
standard carry cocycle.  It is the class whose cup product with `a ∈ Fˣ` appears in the character
formula of the local Artin map. -/
noncomputable def carryClass {n : ℕ} [NeZero n] (e : G ≃* Multiplicative (ZMod n)) :
    groupCohomology (Rep.trivial ℤ G ℤ) 2 :=
  groupCohomology.H2π (Rep.trivial ℤ G ℤ)
    ⟨fun p : G × G => ((carryCocycle e p : ℕ) : ℤ), carryCocycle_mem_cocycles₂_int e⟩

/-- **The cyclic criterion, downward direction.**  For a finite cyclic group `G` (with cyclic
structure `e`), a `k`-linear representation `A` and a morphism `φ : k ⟶ A` of representations: if
the cup product of `φ(1)` with the carry class is zero, then `φ(1)` is a norm.

This is the half of Tate periodicity that was missing everywhere in the workspace: it is the
statement that "cup product with a generator of `H²(G,ℤ)`" is *injective* on `H⁰`. -/
theorem map_carryClass_eq_zero_imp {k : Type} [CommRing k] {n : ℕ} [NeZero n] (hn : 1 < n)
    (e : G ≃* Multiplicative (ZMod n)) (A : Rep k G) (φ : Rep.trivial k G k ⟶ A)
    (zc : ↥(groupCohomology.cocycles₂ (Rep.trivial k G k)))
    (hzc : (⇑zc : G × G → k) = fun p => ((carryCocycle e p : ℕ) : k))
    (h : (groupCohomology.map (MonoidHom.id G) φ 2)
      (groupCohomology.H2π (Rep.trivial k G k) zc) = 0) :
    φ.hom 1 ∈ LinearMap.range A.norm.hom.toLinearMap := by
  classical
  -- `map φ 2 (H2π zc) = H2π (mapCocycles₂ φ zc)`
  have hcomp : groupCohomology.H2π A
      (groupCohomology.mapCocycles₂ (MonoidHom.id G) φ zc) = 0 := by
    have h2 := congrArg (fun m => (ConcreteCategory.hom m) zc)
      (groupCohomology.H2π_comp_map (A := Rep.trivial k G k) (B := A) (MonoidHom.id G) φ)
    simpa only [ConcreteCategory.comp_apply] using h2.symm.trans h
  -- the cocycle is therefore a coboundary
  have hmem : (⇑(groupCohomology.mapCocycles₂ (MonoidHom.id G) φ zc) : G × G → A)
      ∈ groupCohomology.coboundaries₂ A := (groupCohomology.H2π_eq_zero_iff _).1 hcomp
  obtain ⟨b, hb⟩ := hmem
  -- identify its values with the pointwise product of the carry cocycle with `φ 1`
  have hbval : ∀ p : G × G, (groupCohomology.d₁₂ A).hom b p
      = ((carryCocycle e p : ℕ) : k) • φ.hom 1 := by
    intro p
    have hp : (⇑(groupCohomology.mapCocycles₂ (MonoidHom.id G) φ zc) : G × G → A) p
        = φ.hom (⇑zc p) := by
      rw [groupCohomology.coe_mapCocycles₂]
      rfl
    have hcz : (⇑zc : G × G → k) p = ((carryCocycle e p : ℕ) : k) := congrFun hzc p
    have hsmul : φ.hom (((carryCocycle e p : ℕ) : k))
        = ((carryCocycle e p : ℕ) : k) • φ.hom 1 := by
      have h1 := map_smul φ.hom (((carryCocycle e p : ℕ) : k)) (1 : k)
      simpa [smul_eq_mul] using h1
    calc (groupCohomology.d₁₂ A).hom b p
        = (⇑(groupCohomology.mapCocycles₂ (MonoidHom.id G) φ zc) : G × G → A) p := by
          rw [hb]
      _ = φ.hom (⇑zc p) := hp
      _ = φ.hom (((carryCocycle e p : ℕ) : k)) := by rw [hcz]
      _ = ((carryCocycle e p : ℕ) : k) • φ.hom 1 := hsmul
  exact mem_range_norm_of_d₁₂_eq_carryCocycle_smul hn e A (φ.hom 1) b hbval

/-- **The cyclic criterion, upward direction**: if `φ(1)` is a norm then the cup product with the
carry class vanishes.  (No cyclicity is used: this is
`NK.NUV2.RouteE.map_eq_zero_of_mem_range_norm`.) -/
theorem map_carryClass_eq_zero_of_mem_range (A : Rep ℤ G) (φ : Rep.trivial ℤ G ℤ ⟶ A)
    {n : ℕ} [NeZero n] (e : G ≃* Multiplicative (ZMod n))
    (ha : ∃ x : A, A.norm.hom x = φ.hom 1) :
    (groupCohomology.map (MonoidHom.id G) φ 2) (carryClass e) = 0 :=
  map_eq_zero_of_mem_range_norm A φ (carryClass e) ha

end NK.NUV2.RouteE
