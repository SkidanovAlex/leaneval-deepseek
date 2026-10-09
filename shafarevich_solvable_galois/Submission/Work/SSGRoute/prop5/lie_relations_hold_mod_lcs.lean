import Mathlib
import Submission.Work.SSGRoute.prop5.magnusCore
import Submission.Work.SSGRoute.prop5.bracketBar_axioms
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Lie relations among commutator monomials hold modulo the lower central series

Given binary trees `c i` of the same size `n` and a `ℤ`-linear relation
`∑ k i • monLie X (c i) = 0` in the free Lie algebra on `X`, the corresponding product
`∏ (monGrp X (c i)) ^ (k i)` of commutator monomials of the free group on `X` lies in the `n`-th
term of the lower central series (`(⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n`, Mathlib's
indexing, i.e. the paper's `γ_{n+1}`).

The proof builds the Lie ring `Λbar = ⨁ k, γ_k/γ_{k+1}` of the associated graded of the lower
central series of the free group (whose Lie ring structure is `bracketBar_axioms`) and uses the
universal property of the free Lie algebra: the Lie homomorphism `toLbar` sends the generator `x`
to the class of `x` in `Λ 0`, hence `monLie X c` to the class of `monGrp X c` in `Λ (size c - 1)`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

namespace graded

variable {G : Type*} [Group G]

/-- The graded bracket `bracketBar` on `Λbar = ⨁ k, γ_k/γ_{k+1}` makes it a Lie ring. -/
instance instLieRingLbar : LieRing (Lbar G) where
  bracket := fun x y => bracketBar x y
  add_lie := fun x y z => by
    show bracketBar (x + y) z = bracketBar x z + bracketBar y z
    rw [map_add]; rfl
  lie_add := fun x y z => by
    show bracketBar x (y + z) = bracketBar x y + bracketBar x z
    rw [map_add]
  lie_self := fun x => (bracketBar_axioms G).1 x
  leibniz_lie := fun x y z => (bracketBar_axioms G).2 x y z

end graded

variable {X : Type*}

namespace lcs

/-- The class of a group element `y ∈ γ_k` in the graded piece `Λ k = γ_k/γ_{k+1}`. -/
def stdClass (X : Type*) (k : ℕ) (y : FreeGroup X)
    (hy : y ∈ graded.Gam (G := FreeGroup X) k) : graded.LamAdd (G := FreeGroup X) k :=
  Additive.ofMul (QuotientGroup.mk'
    ((graded.Gam (G := FreeGroup X) (k + 1)).subgroupOf (graded.Gam (G := FreeGroup X) k))
    ⟨y, hy⟩)

/-- The class of a generator in `Λ 0`. -/
def genClass (X : Type*) (x : X) : graded.LamAdd (G := FreeGroup X) 0 :=
  stdClass X 0 (FreeGroup.of x) (by rw [graded.Gam_zero]; exact Subgroup.mem_top _)

theorem stdClass_congr {k : ℕ} {y : FreeGroup X}
    (h1 h2 : y ∈ graded.Gam (G := FreeGroup X) k) :
    stdClass X k y h1 = stdClass X k y h2 := by
  have h : (⟨y, h1⟩ : graded.Gam (G := FreeGroup X) k) = ⟨y, h2⟩ := Subtype.ext rfl
  unfold stdClass
  rw [h]

/-- Transport of `lofL (stdClass …)` along an equality of graded degrees. -/
theorem lofL_stdClass_eq {k k' : ℕ} (h : k = k') {y : FreeGroup X}
    (hy : y ∈ graded.Gam (G := FreeGroup X) k)
    (hy' : y ∈ graded.Gam (G := FreeGroup X) k') :
    graded.lofL k (stdClass X k y hy) = graded.lofL k' (stdClass X k' y hy') := by
  have key : graded.GLamCast (G := FreeGroup X) h (stdClass X k y hy) = stdClass X k' y hy' := by
    unfold stdClass
    rw [graded.GLamCast_mk']
  have h2 := graded.lofL_cast (G := FreeGroup X) h (stdClass X k' y hy')
  have h3 : graded.GLamCast (G := FreeGroup X) h.symm (stdClass X k' y hy') = stdClass X k y hy := by
    rw [← key, graded.GLamCast_symm_apply]
  rw [h3] at h2
  exact h2

/-- The graded bracket of the classes of `y ∈ γ_p` and `z ∈ γ_q` is the class of `⁅y,z⁆`. -/
theorem bracketL_stdClass {p q : ℕ} {y z : FreeGroup X}
    (hy : y ∈ graded.Gam (G := FreeGroup X) p) (hz : z ∈ graded.Gam (G := FreeGroup X) q) :
    graded.bracketL (G := FreeGroup X) p q (stdClass X p y hy) (stdClass X q z hz) =
      stdClass X (p + q + 1) ⁅y, z⁆ (graded.commutator_mem_Gam hy hz) := by
  unfold stdClass
  rw [graded.bracketL_apply_mk]
  rw [graded.commClass_mk']

/-- The class of the commutator monomial of a binary tree `c`, in `Λ (size c - 1)`. -/
def treeClass (X : Type*) (c : Magma X) :
    graded.LamAdd (G := FreeGroup X) (Magma.size c - 1) :=
  stdClass X (Magma.size c - 1) (monGrp X c) (monGrp_mem_lowerCentralSeries c)

/-- The Lie homomorphism from the free Lie algebra on `X` to the associated graded of the lower
central series of the free group on `X`, sending `x` to the class of `x`. -/
def toLbar (X : Type*) : FreeLieAlgebra ℤ X →ₗ⁅ℤ⁆ graded.Lbar (FreeGroup X) :=
  FreeLieAlgebra.lift ℤ fun x : X => graded.lofL 0 (genClass X x)

theorem toLbar_of (X : Type) (x : X) :
    toLbar X (FreeLieAlgebra.of ℤ x) = graded.lofL 0 (genClass X x) :=
  FreeLieAlgebra.lift_of_apply _ x

theorem toLbar_monLie (X : Type) (c : Magma X) :
    toLbar X (monLie X c) = graded.lofL (Magma.size c - 1) (treeClass X c) := by
  induction c with
  | gen x =>
      rw [monLie_gen, toLbar_of]
      show graded.lofL 0 (genClass X x) = graded.lofL 0 (treeClass X (Magma.gen x))
      congr 1
  | mul a b iha ihb =>
      have hsize : (Magma.size a - 1) + (Magma.size b - 1) + 1 =
          Magma.size (Magma.mul a b) - 1 := by
        have ha := Magma.size_pos a
        have hb := Magma.size_pos b
        simp only [Magma.size_mul]
        omega
      calc toLbar X (monLie X (Magma.mul a b))
          = ⁅toLbar X (monLie X a), toLbar X (monLie X b)⁆ := by
              rw [monLie_mul, LieHom.map_lie]
        _ = graded.bracketBar (graded.lofL (Magma.size a - 1) (treeClass X a))
              (graded.lofL (Magma.size b - 1) (treeClass X b)) := by
              rw [iha, ihb]
              rfl
        _ = graded.lofL ((Magma.size a - 1) + (Magma.size b - 1) + 1)
              (graded.bracketL (Magma.size a - 1) (Magma.size b - 1)
                (treeClass X a) (treeClass X b)) := by
              rw [graded.bracketBar_lofL]
        _ = graded.lofL ((Magma.size a - 1) + (Magma.size b - 1) + 1)
              (stdClass X ((Magma.size a - 1) + (Magma.size b - 1) + 1)
                (⁅monGrp X a, monGrp X b⁆)
                (graded.commutator_mem_Gam (monGrp_mem_lowerCentralSeries a)
                  (monGrp_mem_lowerCentralSeries b))) := by
              congr 1
        _ = graded.lofL (Magma.size (Magma.mul a b) - 1)
              (stdClass X (Magma.size (Magma.mul a b) - 1) (⁅monGrp X a, monGrp X b⁆)
                (monGrp_mem_lowerCentralSeries (Magma.mul a b))) :=
              lofL_stdClass_eq hsize
                (graded.commutator_mem_Gam (monGrp_mem_lowerCentralSeries a)
                  (monGrp_mem_lowerCentralSeries b))
                (monGrp_mem_lowerCentralSeries (Magma.mul a b))
        _ = graded.lofL (Magma.size (Magma.mul a b) - 1) (treeClass X (Magma.mul a b)) := rfl

/-- A homogeneous component of `Λbar` vanishes if its `lofL`-image does. -/
theorem lofL_eq_zero {k : ℕ} {a : graded.LamAdd (G := FreeGroup X) k}
    (h : graded.lofL (G := FreeGroup X) k a = 0) : a = 0 := by
  have h2 := congrArg (fun z : graded.Lbar (FreeGroup X) => z k) h
  simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same, DFinsupp.zero_apply] using h2

end lcs

theorem lie_relations_hold_mod_lcs (X : Type) (r n : ℕ) (c : Fin r → Magma X) (k : Fin r → ℤ)
    (hc : ∀ i, Magma.size (c i) = n)
    (h : ∑ i, k i • monLie X (c i) = 0) :
    (List.ofFn fun i : Fin r => monGrp X (c i) ^ (k i)).prod ∈
      (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [List.ofFn_zero, List.prod_nil]
    exact Subgroup.one_mem _
  · have hn : 1 ≤ n := by
      have hpos := Magma.size_pos (c ⟨0, hr⟩)
      rw [hc ⟨0, hr⟩] at hpos
      omega
    have hgs : ∀ i, monGrp X (c i) ∈ graded.Gam (G := FreeGroup X) (n - 1) := by
      intro i
      have h' := monGrp_mem_lowerCentralSeries (c i)
      rw [hc i] at h'
      exact h'
    have key : lcs.toLbar X (∑ i, k i • monLie X (c i))
        = ∑ i, k i • graded.lofL (n - 1) (lcs.stdClass X (n - 1) (monGrp X (c i)) (hgs i)) := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [lcs.toLbar_monLie]
      exact (lcs.lofL_stdClass_eq (X := X) (by rw [hc i]) (hgs i)
        (monGrp_mem_lowerCentralSeries (c i))).symm
    have h1 : lcs.toLbar X (∑ i, k i • monLie X (c i)) = 0 := by rw [h, map_zero]
    have hsumL : ∑ i, k i • graded.lofL (n - 1) (lcs.stdClass X (n - 1) (monGrp X (c i)) (hgs i))
        = 0 := by
      rw [← key]; exact h1
    have hcomp : ∑ i, k i • lcs.stdClass X (n - 1) (monGrp X (c i)) (hgs i) = 0 := by
      have key2 : graded.lofL (n - 1)
            (∑ i, k i • lcs.stdClass X (n - 1) (monGrp X (c i)) (hgs i))
          = ∑ i, k i • graded.lofL (n - 1) (lcs.stdClass X (n - 1) (monGrp X (c i)) (hgs i)) := by
        simp only [map_sum, map_smul]
      exact lcs.lofL_eq_zero (by rw [key2]; exact hsumL)
    set yg : FreeGroup X := (List.ofFn fun i : Fin r => monGrp X (c i) ^ (k i)).prod with hygdef
    have hygmem : yg ∈ graded.Gam (G := FreeGroup X) (n - 1) := by
      rw [hygdef]
      refine Subgroup.list_prod_mem _ (fun x hx => ?_)
      rw [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Subgroup.zpow_mem _ (hgs i) (k i)
    set L : List (graded.Gam (G := FreeGroup X) (n - 1)) :=
      List.ofFn fun i : Fin r =>
        (⟨monGrp X (c i), hgs i⟩ : graded.Gam (G := FreeGroup X) (n - 1)) ^ (k i) with hLdef
    let NN : Subgroup (graded.Gam (G := FreeGroup X) (n - 1)) :=
      (graded.Gam (G := FreeGroup X) (n - 1 + 1)).subgroupOf (graded.Gam (G := FreeGroup X) (n - 1))
    have hcoe : ((L.prod : graded.Gam (G := FreeGroup X) (n - 1)) : FreeGroup X) = yg := by
      rw [show ((L.prod : graded.Gam (G := FreeGroup X) (n - 1)) : FreeGroup X)
          = (List.map (Subgroup.subtype (graded.Gam (G := FreeGroup X) (n - 1))) L).prod from
          map_list_prod (Subgroup.subtype (graded.Gam (G := FreeGroup X) (n - 1))) L]
      have hmap : List.map (Subgroup.subtype (graded.Gam (G := FreeGroup X) (n - 1))) L
          = List.ofFn (fun i : Fin r => monGrp X (c i) ^ (k i)) := by
        rw [hLdef, List.map_ofFn]
        congr 1
      rw [hmap, hygdef]
    have hmul : (∏ i, (QuotientGroup.mk' NN ⟨monGrp X (c i), hgs i⟩ :
        graded.GLam (G := FreeGroup X) (n - 1)) ^ (k i)) = 1 := by
      apply Additive.ofMul.injective
      have hgoal : Additive.ofMul (∏ i, (QuotientGroup.mk' NN ⟨monGrp X (c i), hgs i⟩ :
          graded.GLam (G := FreeGroup X) (n - 1)) ^ (k i)) = 0 := by
        rw [ofMul_prod]
        simp only [ofMul_zpow]
        simpa only [NN, lcs.stdClass] using hcomp
      rw [hgoal, ofMul_one]
    have h1' : (⟨yg, hygmem⟩ : graded.Gam (G := FreeGroup X) (n - 1)) = L.prod := by
      apply Subtype.ext
      exact hcoe.symm
    have hrel : (QuotientGroup.mk' NN ⟨yg, hygmem⟩ : graded.GLam (G := FreeGroup X) (n - 1))
        = ∏ i, (QuotientGroup.mk' NN ⟨monGrp X (c i), hgs i⟩ :
            graded.GLam (G := FreeGroup X) (n - 1)) ^ (k i) := by
      rw [h1']
      rw [show (QuotientGroup.mk' NN L.prod : graded.GLam (G := FreeGroup X) (n - 1))
          = (List.ofFn fun i : Fin r => (QuotientGroup.mk' NN ⟨monGrp X (c i), hgs i⟩ :
              graded.GLam (G := FreeGroup X) (n - 1)) ^ (k i)).prod from by
            rw [hLdef, map_list_prod]
            congr 1
            rw [List.map_ofFn]
            congr 1]
      rw [List.prod_ofFn]
    have hquot : (QuotientGroup.mk' NN ⟨yg, hygmem⟩ : graded.GLam (G := FreeGroup X) (n - 1))
        = 1 := by
      rw [hrel, hmul]
    have hmem : yg ∈ graded.Gam (G := FreeGroup X) n := by
      have h8 : (↑(⟨yg, hygmem⟩ : graded.Gam (G := FreeGroup X) (n - 1)) :
          graded.GLam (G := FreeGroup X) (n - 1)) = 1 := by
        rw [← QuotientGroup.mk'_apply]
        exact hquot
      have h9 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := NN) _).mp h8)
      rwa [Nat.sub_add_cancel hn] at h9
    exact hmem

end Work.SSGRoute.prop5
