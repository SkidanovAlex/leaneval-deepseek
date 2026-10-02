import Mathlib
import Submission.Work.Serre.tpC_homologyMap_cokernel_subsingleton
import Submission.Work.Serre.tensorRat_subsingleton_of_subsingleton
import Submission.Work.Serre.relEZ_homology_iso
import Submission.Work.Kunneth.CrossGen
import Submission.Work.Serre.crossProduct_defs
import Submission.Work.Serre.tpDApplyComp
import Submission.Work.Serre.cyclesTorsionOfHomologyTorsion
import Submission.Work.Serre.homologySubsingletonOfCycleTorsion
import Submission.Work.ThomBordism.PontryaginThom.Torsion

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cross product with a generator of the rational homology of `D`

This file proves `Work.Serre.crossProduct_coker_rat`: if the rational homology of the chain complex
`D` vanishes in degrees `≤ N+1` except in degree `r+1`, where it is generated (up to torsion) by the
class of a cycle `z`, then in the range `m + r + 1 ≤ N + 1` the cross product with `z` induces a map
`T : H_m(C) ⟶ H_{m+r+1}(tpC C D)` whose cokernel is a torsion group.

The proof uses the coefficient complex `ℤ[r+1]` of `Submission/Work/Serre/crossProduct_defs.lean`:
for `D' := ℤ[r+1]` and `φ := dzMap r D z : D' ⟶ D` (a monomorphism as soon as `z` is not a
torsion element), the tensor product `tpC C ℤ[r+1]` has homology `H_m(C)` in degree `m+r+1`, and the
child lemma `Work.Serre.tpC_homologyMap_cokernel_subsingleton` shows that the cokernel of
`homologyMap (tpMap C C D' D 𝟙 φ) (m+r+1)` is rationally trivial, provided the rational homology of
the cokernel of `φ` (the quotient complex `D ⧸ ℤz`) vanishes in degrees `≤ N+1`.  The heavy lifting
is thus

* `Work.Serre.coker_dzMap_homology_rat_subsingleton` — the rational homology of `D ⧸ ℤz`, proved by
  the cycle criterion `Work.Serre.homologySubsingletonOfCycleTorsion` and the description of the
  quotient complex degreewise (its differentials are the induced ones, and its terms away from
  degree `r+1` are those of `D`);
* `Work.Serre.homologyMap_tpMap_image_le` — every class in the image of
  `homologyMap (tpMap C C D' D 𝟙 φ) (m+r+1)` is the class of a cross product `u ⊗ z` with `u` a
  *cycle* of `C` (so that it lies in the image of the map `T`).

In the degenerate case where the class of `z` dies after tensoring with `ℚ`, the rational homology
of `D` itself vanishes in the whole range (`Work.Serre.subsingleton_homology_rat_of_hgen`), and any
`T` works.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

attribute [-instance] AddCommGroup.toIntModule

namespace Work.Serre

noncomputable section

universe u

/-! ## Linear algebra of `M ⊗[ℤ] ℤ`

The contractibility of the second factor, expressed in the formulation in which the scalar
multiplies through `LinearMap.toSpanSingleton` (which avoids the `ℤ`-smul instance friction).
-/

/-- `rid` composed with `toSpanSingleton`. -/
theorem rid_tmul_eq_toSpanSingleton {M : Type*} [AddCommGroup M] [Module ℤ M] (a : M) (k : ℤ) :
    (TensorProduct.rid ℤ M) (a ⊗ₜ[ℤ] k) = (LinearMap.toSpanSingleton ℤ M a) k := by
  rw [TensorProduct.rid_tmul, LinearMap.toSpanSingleton_apply]

/-- The value of `toSpanSingleton` at `-1`. -/
theorem toSpanSingleton_neg_one {N : Type*} [AddCommGroup N] [Module ℤ N] (w : N) :
    (LinearMap.toSpanSingleton ℤ N w) (-1) = -w := by
  rw [show (-1 : ℤ) = -(1 : ℤ) by ring, map_neg, LinearMap.toSpanSingleton_apply_one]

/-- **The value of `toSpanSingleton` at an integer.** -/
theorem toSpanSingleton_apply_zsmul {M : Type*} [AddCommGroup M] [Module ℤ M] (w : M) (k : ℤ) :
    (LinearMap.toSpanSingleton ℤ M w) k = k • w := by
  induction k using Int.induction_on with
  | zero => rw [map_zero, zero_zsmul]
  | succ i ih =>
      rw [map_add, LinearMap.toSpanSingleton_apply_one, add_zsmul, one_zsmul, ih]
  | pred i ih =>
      rw [show (-(↑i : ℤ) - 1) = (-(↑i)) + (-1) by ring, map_add, toSpanSingleton_neg_one,
        add_zsmul, ih]
      simp only [neg_zsmul, one_zsmul]

/-- **The scalar can be moved from one tensor factor to the other.** -/
theorem tmul_toSpanSingleton {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (a : M) (w : N) (k : ℤ) :
    a ⊗ₜ[ℤ] ((LinearMap.toSpanSingleton ℤ N w) k)
      = ((LinearMap.toSpanSingleton ℤ M a) k) ⊗ₜ[ℤ] w := by
  induction k using Int.induction_on with
  | zero => rw [map_zero, map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul]
  | succ i ih =>
      rw [map_add, map_add, LinearMap.toSpanSingleton_apply_one,
        LinearMap.toSpanSingleton_apply_one, TensorProduct.tmul_add, TensorProduct.add_tmul, ih]
  | pred i ih =>
      rw [show (-(↑i : ℤ) - 1) = (-(↑i)) + (-1) by ring, map_add, map_add,
        toSpanSingleton_neg_one, toSpanSingleton_neg_one,
        TensorProduct.tmul_add, TensorProduct.add_tmul, ih, TensorProduct.tmul_neg,
        TensorProduct.neg_tmul]

/-- Contraction naturality for `rid`. -/
theorem rid_map (C : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ) (y : ↥(C.X m) ⊗[ℤ] ℤ) :
    (TensorProduct.rid ℤ ↥(C.X (m - 1)))
        (TensorProduct.map ((C.d m (m - 1)).hom) (LinearMap.id) y)
      = (C.d m (m - 1)).hom ((TensorProduct.rid ℤ ↥(C.X m)) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a k =>
      rw [TensorProduct.map_tmul, TensorProduct.rid_tmul, TensorProduct.rid_tmul,
        LinearMap.map_smul]
      simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-- **The contraction of `M ⊗ ℤ` against `toSpanSingleton`**, in the formulation with the second
factor `ℤ`. -/
theorem map_toSpanSingleton_rid (C : ChainComplex (ModuleCat ℤ) ℕ) (m : ℕ) {N : ModuleCat ℤ}
    (w : ↥N) (β : ↥(C.X m) ⊗[ℤ] ℤ) :
    TensorProduct.map (LinearMap.id) (LinearMap.toSpanSingleton ℤ ↥N w) β
      = (TensorProduct.rid ℤ ↥(C.X m)) β ⊗ₜ[ℤ] w := by
  induction β using TensorProduct.induction_on with
  | zero => simp
  | tmul a k =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, rid_tmul_eq_toSpanSingleton]
      exact tmul_toSpanSingleton a w k
  | add u v hu hv => rw [map_add, map_add, hu, hv, TensorProduct.add_tmul]

/-! ## The image of the cross product map consists of cross products with cycles -/

/-- **The image of `homologyMap (tpMap C C ℤ[r+1] D 𝟙 (dzMap r D z)) (m+r+1)` consists of cross
products of a genuine cycle of `C` with `z`.** -/
theorem exists_cycle_map_dzGen_tmul (C D : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ)
    (z : ↥(D.cycles (r + 1)))
    (α : ↥(C.X m) ⊗[ℤ] ↥((dzComplex r).X (r + 1)))
    (hα : TensorProduct.map ((C.d m (m - 1)).hom) (LinearMap.id) α = 0) :
    ∃ u : ↥(C.cycles m),
      TensorProduct.map (LinearMap.id) (((dzMap r D z).f (r + 1)).hom) α
        = (C.iCycles m) u ⊗ₜ[ℤ] ((D.iCycles (r + 1)) z) := by
  set g : ↥((dzComplex r).X (r + 1)) →ₗ[ℤ] ℤ := ((dzIso r).hom).hom with hg
  set β : ↥(C.X m) ⊗[ℤ] ℤ := TensorProduct.map (LinearMap.id) g α with hβ
  have hcyc : (C.d m (m - 1)).hom ((TensorProduct.rid ℤ ↥(C.X m)) β) = 0 := by
    have hcomm : TensorProduct.map ((C.d m (m - 1)).hom) (LinearMap.id) β
        = TensorProduct.map (LinearMap.id) g
            (TensorProduct.map ((C.d m (m - 1)).hom) (LinearMap.id) α) := by
      rw [hβ, TensorProduct.map_map, TensorProduct.map_map]
      simp only [LinearMap.comp_id, LinearMap.id_comp]
    have h1 : TensorProduct.map ((C.d m (m - 1)).hom) (LinearMap.id) β = 0 := by
      rw [hcomm, hα, map_zero]
    rw [← rid_map C m β, h1, map_zero]
  refine ⟨Work.Kunneth.cycleOf C m ⟨(TensorProduct.rid ℤ ↥(C.X m)) β, hcyc⟩, ?_⟩
  have hf : ((dzMap r D z).f (r + 1)).hom
      = (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z)).comp g := by
    rw [dzMap_f_self, dzGen, ModuleCat.hom_comp, ModuleCat.hom_ofHom, hg]
  have hL : TensorProduct.map (LinearMap.id) (((dzMap r D z).f (r + 1)).hom) α
      = TensorProduct.map (LinearMap.id)
          (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z)) β := by
    rw [hf, hβ, TensorProduct.map_map]
    simp only [LinearMap.comp_id, LinearMap.id_comp]
  rw [hL, map_toSpanSingleton_rid, Work.Kunneth.iCycles_cycleOf]

/-! ## Non-torsion of the class of `z` -/

/-- **The class of `z` is not a torsion element** when it survives rationalisation. -/
theorem zClass_not_torsion (D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (z : ↥(D.cycles (r + 1)))
    (hzt : TensorProduct.tmul ℤ ((D.homologyπ (r + 1)).hom z) (1 : ℚ) ≠ 0) :
    ∀ k : ℤ, k • ((D.homologyπ (r + 1)).hom z) = 0 → k = 0 := by
  generalize hxi : (D.homologyπ (r + 1)).hom z = xi at hzt ⊢
  intro k hk
  by_contra hk0
  apply hzt
  have hkey : @TensorProduct.tmul ℤ _ (↥(D.homology (r + 1))) ℚ _ _
      (AddCommGroup.toIntModule ↥(D.homology (r + 1))) _ xi (1 : ℚ) = 0 := by
    refine (Work.ThomBordism.PontryaginThom.tmul_one_eq_zero_iff xi).mpr
      ⟨(|k|).toNat, ?_, ?_⟩
    · rw [Int.lt_toNat]; exact abs_pos.mpr hk0
    · rw [Int.toNat_of_nonneg (abs_nonneg k)]
      rcases lt_trichotomy k 0 with h | h | h
      · rw [abs_of_neg h, neg_zsmul, hk, neg_zero]
      · exact absurd h hk0
      · rw [abs_of_pos h]; exact hk
  rw [Subsingleton.elim (AddCommGroup.toIntModule ↥(D.homology (r + 1)))
    (D.homology (r + 1)).isModule] at hkey
  exact hkey

/-- **The cycle `z` is not a torsion element** when its class survives rationalisation. -/
theorem z_chain_not_torsion (D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (z : ↥(D.cycles (r + 1)))
    (hzt : TensorProduct.tmul ℤ ((D.homologyπ (r + 1)).hom z) (1 : ℚ) ≠ 0) :
    ∀ k : ℤ, (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) ((D.iCycles (r + 1)) z)) k = 0 → k = 0 := by
  intro k hk
  apply zClass_not_torsion D r z hzt
  set w : ↥(D.X (r + 1)) := (D.iCycles (r + 1)) z with hw
  have hmem : ∀ t : ℤ, (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) t
      ∈ Work.Kunneth.cycKer D (r + 1) := by
    intro t
    show (D.d (r + 1) ((r + 1) - 1)).hom
      ((LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) t) = 0
    have h0 : ((D.d (r + 1) ((r + 1) - 1)).hom).comp
        (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) = 0 := by
      apply LinearMap.ext_ring
      rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply_one, hw]
      exact Work.Kunneth.d_iCycles D (r + 1) z
    rw [← LinearMap.comp_apply, h0, LinearMap.zero_apply]
  let eta : ℤ →ₗ[ℤ] ↥(D.homology (r + 1)) :=
    ((D.homologyπ (r + 1)).hom).comp
      (((Work.Kunneth.cycIso D (r + 1)).inv.hom).comp
        (LinearMap.codRestrict (Work.Kunneth.cycKer D (r + 1))
          (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) hmem))
  have heta0 : eta k = 0 := by
    simp only [eta, LinearMap.comp_apply]
    have hc : (LinearMap.codRestrict (Work.Kunneth.cycKer D (r + 1))
        (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) hmem) k = 0 := by
      apply Subtype.ext
      change (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) k = (0 : ↥(D.X (r + 1)))
      rw [hk]
    rw [hc, map_zero, map_zero]
  have heta1 : eta 1 = (D.homologyπ (r + 1)).hom z := by
    simp only [eta, LinearMap.comp_apply]
    have hc : (LinearMap.codRestrict (Work.Kunneth.cycKer D (r + 1))
        (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) hmem) 1
        = (Work.Kunneth.cycIso D (r + 1)).hom.hom z := by
      apply Subtype.ext
      rw [Work.Kunneth.cycIso_hom_val]
      change (LinearMap.toSpanSingleton ℤ ↥(D.X (r + 1)) w) 1 = (D.iCycles (r + 1)) z
      rw [LinearMap.toSpanSingleton_apply_one, hw]
    rw [hc, Work.Kunneth.homIso_inv_apply]
  have hlin : ∀ t : ℤ, t • (eta 1) = eta t := by
    intro t
    induction t using Int.induction_on with
    | zero => rw [zero_zsmul, map_zero]
    | succ i ih => rw [add_zsmul, one_zsmul, ih, map_add]
    | pred i ih =>
        have ih' : (↑i : ℤ) • (eta 1) = eta (↑i : ℤ) := by
          have h := ih
          rw [neg_zsmul, map_neg] at h
          exact neg_inj.mp h
        rw [show (-(↑i : ℤ) - 1) = -(↑i + 1) by ring, neg_zsmul, map_neg, add_zsmul, one_zsmul,
          ih', map_add]
  rw [← heta1, hlin k, heta0]

/-! ## The degenerate case: the class of `z` dies after rationalisation -/

/-- The kernel of rationalisation is the torsion subgroup: an element killed by tensoring with `ℚ`
has finite order.  (Instance-flexible form of
`Work.ThomBordism.PontryaginThom.torsion_of_tmul_one_eq_zero`.) -/
theorem torsion_of_tmul_one_eq_zero_nat {A : Type*} [AddCommGroup A] {M : Module ℤ A} (h : A)
    (hzero : @TensorProduct.tmul ℤ _ A ℚ _ _ M _ h (1 : ℚ) = 0) :
    ∃ N : ℕ, 0 < N ∧ N • h = 0 := by
  have hM : M = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  rw [hM] at hzero
  obtain ⟨N, hN, hN0⟩ := Work.ThomBordism.PontryaginThom.torsion_of_tmul_one_eq_zero h hzero
  exact ⟨N, hN, by rwa [natCast_zsmul] at hN0⟩

/-- **A multiple of an element killed by rationalisation is also killed.** -/
theorem tmul_zsmul_eq_zero {M : Type*} [AddCommGroup M] [Module ℤ M]
    (y : M) (h : y ⊗ₜ[ℤ] (1 : ℚ) = 0) (m : ℤ) : (m • y) ⊗ₜ[ℤ] (1 : ℚ) = 0 := by
  induction m using Int.induction_on with
  | zero => rw [zero_zsmul, TensorProduct.zero_tmul]
  | succ i ih => rw [add_zsmul, one_zsmul, TensorProduct.add_tmul, ih, h, add_zero]
  | pred i ih =>
      rw [sub_zsmul, one_zsmul, TensorProduct.add_tmul, ih, TensorProduct.neg_tmul, h, neg_zero,
        add_zero]

/-- **The elementwise form of the generating hypothesis `hgen`**: every class in `H_{r+1}(D)` has
a positive multiple which is an integral multiple of the class of `z`. -/
theorem hgen_elem (D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (z : ↥(D.cycles (r + 1)))
    (hgen : ∀ w : ↥(D.homology (r + 1)), ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
      TensorProduct.tmul ℤ (n • w) (1 : ℚ)
        = TensorProduct.tmul ℤ (m • ((D.homologyπ (r + 1)).hom z)) (1 : ℚ)) :
    ∀ a : ↥(D.homology (r + 1)), ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
      n • a = m • ((D.homologyπ (r + 1)).hom z) := by
  intro a
  obtain ⟨n, hn, m, hm⟩ := hgen a
  set d : ↥(D.homology (r + 1)) := (n : ℤ) • a - m • ((D.homologyπ (r + 1)).hom z) with hd
  have hzero : TensorProduct.tmul ℤ d (1 : ℚ) = 0 := by
    rw [hd, TensorProduct.sub_tmul, natCast_zsmul, hm, sub_self]
  obtain ⟨k, hk, hk0⟩ :=
    torsion_of_tmul_one_eq_zero_nat (M := (D.homology (r + 1)).isModule) d hzero
  have hk0' : (k : ℤ) • d = 0 := by rwa [← natCast_zsmul] at hk0
  rw [hd, zsmul_sub, smul_smul, smul_smul, sub_eq_zero] at hk0'
  refine ⟨k * n, Nat.mul_pos hk hn, (k : ℤ) * m, ?_⟩
  rw [← hk0', ← natCast_zsmul, Nat.cast_mul]

/-- **If `[z] ⊗ 1 = 0` then the rational homology of `D` vanishes in the whole range `≤ N+1`.** -/
theorem subsingleton_homology_rat_of_hgen (D : ChainComplex (ModuleCat ℤ) ℕ) (r N : ℕ)
    (z : ↥(D.cycles (r + 1)))
    (hvan : ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      Subsingleton (TensorProduct ℤ ↥(D.homology j) ℚ))
    (hgen : ∀ w : ↥(D.homology (r + 1)), ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
      TensorProduct.tmul ℤ (n • w) (1 : ℚ)
        = TensorProduct.tmul ℤ (m • ((D.homologyπ (r + 1)).hom z)) (1 : ℚ))
    (hzt : TensorProduct.tmul ℤ ((D.homologyπ (r + 1)).hom z) (1 : ℚ) = 0) :
    ∀ j : ℕ, j ≤ N + 1 → Subsingleton (TensorProduct ℤ ↥(D.homology j) ℚ) := by
  intro j hj
  by_cases hjr : j = r + 1
  · subst hjr
    apply Work.Serre.tensorRat_subsingleton_of_torsion_gen
    intro w
    obtain ⟨n, hn, m, hm⟩ := hgen w
    have h2 : TensorProduct.tmul ℤ (n • w) (1 : ℚ) = 0 := by
      rw [hm]
      exact tmul_zsmul_eq_zero ((D.homologyπ (r + 1)).hom z) hzt m
    obtain ⟨k, hk, hk0⟩ := torsion_of_tmul_one_eq_zero_nat (M := (inferInstanceAs (Module ℤ
      ↥(D.homology (r + 1))))) (n • w) h2
    refine ⟨k * n, Nat.mul_pos hk hn, ?_⟩
    rw [mul_smul]
    exact hk0
  · exact hvan j hj hjr

/-! ## The quotient complex `D ⧸ ℤz` -/

/-- The cokernel of `dzMap r D z`, i.e. the quotient complex `D ⧸ ℤz`. -/
abbrev dzCoker (D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (z : ↥(D.cycles (r + 1))) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  CategoryTheory.Limits.cokernel (dzMap r D z)

/-- The quotient morphism `D ⟶ D ⧸ ℤz`. -/
abbrev dzCokerπ (D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) (z : ↥(D.cycles (r + 1))) :
    D ⟶ dzCoker D r z :=
  CategoryTheory.Limits.cokernel.π (dzMap r D z)

/-- **The degreewise description of the cokernel of a chain map**: the range of the `j`-th
component is the kernel of the `j`-th component of the cokernel projection. -/
theorem range_f_eq_ker_cokernelπ_f (A B : ChainComplex (ModuleCat ℤ) ℕ) (φ : A ⟶ B) (j : ℕ) :
    LinearMap.range ((φ.f j).hom)
      = LinearMap.ker (((CategoryTheory.Limits.cokernel.π φ).f j).hom) := by
  have hS : (ShortComplex.cokernelSequence φ).Exact := ShortComplex.cokernelSequence_exact φ
  have h2 := (HomologicalComplex.exact_iff_degreewise_exact
    (ShortComplex.cokernelSequence φ)).mp hS j
  have h3 := ShortComplex.Exact.moduleCat_range_eq_ker h2
  change LinearMap.range ((φ.f j).hom)
    = LinearMap.ker (((CategoryTheory.Limits.cokernel.π φ).f j).hom) at h3
  exact h3

/-- The `j`-th component of the cokernel projection is injective when the `j`-th component of the
chain map vanishes. -/
theorem injective_cokernelπ_f (A B : ChainComplex (ModuleCat ℤ) ℕ) (φ : A ⟶ B) (j : ℕ)
    (h0 : φ.f j = 0) :
    Function.Injective (((CategoryTheory.Limits.cokernel.π φ).f j).hom) := by
  rw [← LinearMap.ker_eq_bot, ← range_f_eq_ker_cokernelπ_f A B φ j, h0]
  simp

/-- An element of the target of the `j`-th component of a chain map is killed by the cokernel
projection exactly when it lies in the range of that component. -/
theorem cokernelπ_f_eq_zero_iff (A B : ChainComplex (ModuleCat ℤ) ℕ) (φ : A ⟶ B) (j : ℕ)
    (v : ↥(B.X j)) :
    (((CategoryTheory.Limits.cokernel.π φ).f j).hom v = 0)
      ↔ ∃ y : ↥(A.X j), (φ.f j).hom y = v := by
  have h := range_f_eq_ker_cokernelπ_f A B φ j
  constructor
  · intro hv
    have hv' : v ∈ LinearMap.ker (((CategoryTheory.Limits.cokernel.π φ).f j).hom) := hv
    rw [← h] at hv'
    exact hv'
  · rintro ⟨y, rfl⟩
    have hy : (φ.f j).hom y ∈ LinearMap.ker (((CategoryTheory.Limits.cokernel.π φ).f j).hom) := by
      rw [← h]
      exact ⟨y, rfl⟩
    exact hy

/-- The class of the cycle `z` is killed by the quotient projection. -/
theorem cokernelπ_f_iCycles_eq_zero (D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) :
    ((dzCokerπ D r z).f (r + 1)).hom ((D.iCycles (r + 1)) z) = 0 := by
  set g : ↥((dzComplex r).X (r + 1)) := (dzIso r).inv.hom (1 : ℤ) with hg
  have h1 : ((dzMap r D z).f (r + 1)).hom g = (D.iCycles (r + 1)) z := by
    rw [dzMap_f_self_apply, hg, Work.Kunneth.homIso_hom_apply,
      LinearMap.toSpanSingleton_apply_one]
  rw [← h1]
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (hom_comp_cokernel_f (dzComplex r) D (dzMap r D z) (r + 1)) g

/-- **A chain whose boundary is a multiple of `z` is a cycle**, in the case where the class of `z`
is not a torsion element. -/
theorem eq_zero_of_d_eq_smul_iCycles (D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1)))
    (hzt : TensorProduct.tmul ℤ ((D.homologyπ (r + 1)).hom z) (1 : ℚ) ≠ 0)
    (k : ℤ) (w : ↥(D.X (r + 2)))
    (h : (D.d (r + 2) (r + 1)).hom w = k • ((D.iCycles (r + 1)) z)) : k = 0 := by
  apply zClass_not_torsion D r z hzt
  have h2 : (D.homologyπ (r + 1)).hom (k • z) = 0 := by
    apply Work.Kunneth.homologyπ_eq_zero_of_d_eq D (r + 1) (k • z) w
    rw [map_zsmul]
    exact h
  rwa [map_zsmul] at h2

/-- **Cycles are killed by boundaries when the rational homology vanishes.** -/
theorem cyclesTorsion_of_subsingleton_tensorRat (D : ChainComplex (ModuleCat ℤ) ℕ) (j : ℕ)
    (h : Subsingleton (TensorProduct ℤ ↥(D.homology j) ℚ)) :
    ∀ x : ↥(D.X j), (D.d j (j - 1)).hom x = 0 →
      ∃ m : ℕ, 0 < m ∧ ∃ y : ↥(D.X (j + 1)), (D.d (j + 1) j).hom y = m • x :=
  Work.Serre.cyclesTorsionOfHomologyTorsion D j
    (fun a => Work.Serre.torsion_of_subsingleton_tensorRat_gen
      (M := (D.homology j).isModule) h a)

/-- **The rational homology of the quotient complex `D ⧸ ℤz` vanishes in degrees `≤ N+1`.**

This is the analytic heart of the file: a cycle of the quotient is lifted to `D`, where the
differential lands in `ℤz`; in degrees different from `r+1` and `r+2` the lift is already a cycle,
in degree `r+1` the generating hypothesis `hgen` shows that a multiple of the lift is a boundary,
and in degree `r+2` the non-torsion of `[z]` forces the lift to be a cycle. -/
theorem coker_dzMap_homology_rat_subsingleton (D : ChainComplex (ModuleCat ℤ) ℕ) (r N : ℕ)
    (z : ↥(D.cycles (r + 1)))
    (hvan : ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      Subsingleton (TensorProduct ℤ ↥(D.homology j) ℚ))
    (hgen : ∀ w : ↥(D.homology (r + 1)), ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
      TensorProduct.tmul ℤ (n • w) (1 : ℚ)
        = TensorProduct.tmul ℤ (m • ((D.homologyπ (r + 1)).hom z)) (1 : ℚ))
    (hzt : TensorProduct.tmul ℤ ((D.homologyπ (r + 1)).hom z) (1 : ℚ) ≠ 0) :
    ∀ j : ℕ, j ≤ N + 1 → Subsingleton (TensorProduct ℤ
      ↥((dzCoker D r z).homology j) ℚ) := by
  intro j hj
  apply Work.Serre.homologySubsingletonOfCycleTorsion
  intro q
  have hq : ((dzCoker D r z).d j (j - 1)).hom (q : ↥((dzCoker D r z).X j)) = 0 := q.2
  obtain ⟨w₀, hw₀⟩ := (ModuleCat.epi_iff_surjective ((dzCokerπ D r z).f j)).mp
    (inferInstance : Epi ((dzCokerπ D r z).f j)) (q : ↥((dzCoker D r z).X j))
  by_cases h1 : j = r + 1
  · -- degree `r+1`: the generating hypothesis
    subst h1
    have hinj : Function.Injective (((dzCokerπ D r z).f (r + 1 - 1)).hom) :=
      injective_cokernelπ_f (dzComplex r) D (dzMap r D z) (r + 1 - 1)
        (dzMap_f_of_ne r D z (r + 1 - 1) (by omega))
    have hcomm := congrArg (fun (u : D.X (r + 1) ⟶ (dzCoker D r z).X (r + 1 - 1)) =>
      ModuleCat.Hom.hom u w₀) (HomologicalComplex.Hom.comm (dzCokerπ D r z) (r + 1) (r + 1 - 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    have hzero : ((dzCokerπ D r z).f (r + 1 - 1)).hom
        ((D.d (r + 1) (r + 1 - 1)).hom w₀) = 0 := by
      rw [← hcomm]
      rw [hw₀, hq]
    have hdw : (D.d (r + 1) ((r + 1) - 1)).hom w₀ = 0 :=
      hinj (hzero.trans (map_zero (((dzCokerπ D r z).f (r + 1 - 1)).hom)).symm)
    set wz : ↥(D.cycles (r + 1)) := Work.Kunneth.cycleOf D (r + 1) ⟨w₀, hdw⟩ with hwzdef
    have hwz : (D.iCycles (r + 1)).hom wz = w₀ := by
      rw [hwzdef]
      exact Work.Kunneth.iCycles_cycleOf D (r + 1) ⟨w₀, hdw⟩
    obtain ⟨n, hn, mm, hm⟩ := hgen_elem D r z hgen ((D.homologyπ (r + 1)).hom wz)
    have hπ : (D.homologyπ (r + 1)).hom (n • wz) = (D.homologyπ (r + 1)).hom (mm • z) := by
      rw [map_nsmul, map_zsmul]
      exact hm
    obtain ⟨y, hy⟩ := Work.Kunneth.exists_d_eq_of_homologyπ_eq D (r + 1) (n • wz) (mm • z) hπ
    refine ⟨n, hn, ((dzCokerπ D r z).f (r + 1 + 1)).hom y, ?_⟩
    have hcomm2 := congrArg (fun (u : D.X (r + 1 + 1) ⟶ (dzCoker D r z).X (r + 1)) =>
      ModuleCat.Hom.hom u y) (HomologicalComplex.Hom.comm (dzCokerπ D r z) (r + 1 + 1) (r + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm2
    have hA : ((dzCokerπ D r z).f (r + 1)).hom ((D.iCycles (r + 1)).hom (n • wz))
        = n • (q : ↥((dzCoker D r z).X (r + 1))) := by
      rw [map_nsmul, hwz, map_nsmul, hw₀]
    have hB : ((dzCokerπ D r z).f (r + 1)).hom ((D.iCycles (r + 1)).hom (mm • z)) = 0 := by
      rw [map_zsmul, map_zsmul, cokernelπ_f_iCycles_eq_zero D r z, zsmul_zero]
    rw [hcomm2, hy, map_sub, hA, hB, sub_zero]
  · by_cases h2 : j = r + 2
    · -- degree `r+2`: the lift is already a cycle
      subst h2
      have hq' : ((dzCoker D r z).d (r + 2) (r + 1)).hom
          (q : ↥((dzCoker D r z).X (r + 2))) = 0 := hq
      have hcomm := congrArg (fun (u : D.X (r + 2) ⟶ (dzCoker D r z).X (r + 1)) =>
        ModuleCat.Hom.hom u w₀) (HomologicalComplex.Hom.comm (dzCokerπ D r z) (r + 2) (r + 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
      have hker : ((dzCokerπ D r z).f (r + 1)).hom
          ((D.d (r + 2) (r + 1)).hom w₀) = 0 := by
        rw [← hcomm, hw₀, hq']
      obtain ⟨y, hy⟩ := (cokernelπ_f_eq_zero_iff (dzComplex r) D (dzMap r D z) (r + 1)
        ((D.d (r + 2) (r + 1)).hom w₀)).mp hker
      set kk : ℤ := ((dzIso r).hom.hom) y with hkk
      have hk : (D.d (r + 2) (r + 1)).hom w₀ = kk • ((D.iCycles (r + 1)) z) := by
        rw [← hy, dzMap_f_self_apply, ← hkk]
        exact toSpanSingleton_apply_zsmul ((D.iCycles (r + 1)) z) kk
      have hk0 : kk = 0 :=
        eq_zero_of_d_eq_smul_iCycles D r z hzt kk w₀ hk
      have hdw : (D.d (r + 2) ((r + 2) - 1)).hom w₀ = 0 := by
        show (D.d (r + 2) (r + 1)).hom w₀ = 0
        rw [hk, hk0, zero_zsmul]
      obtain ⟨mm, hmm, y', hy'⟩ :=
        cyclesTorsion_of_subsingleton_tensorRat D (r + 2) (hvan (r + 2) (by omega) (by omega))
          w₀ hdw
      refine ⟨mm, hmm, ((dzCokerπ D r z).f (r + 2 + 1)).hom y', ?_⟩
      have hcomm2 := congrArg (fun (u : D.X (r + 2 + 1) ⟶ (dzCoker D r z).X (r + 2)) =>
        ModuleCat.Hom.hom u y') (HomologicalComplex.Hom.comm (dzCokerπ D r z) (r + 2 + 1) (r + 2))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm2
      rw [hcomm2, hy', map_nsmul, hw₀]
    · -- all other degrees: the lift is already a cycle in `D`
      have hj1 : j - 1 ≠ r + 1 := by omega
      have hinj : Function.Injective (((dzCokerπ D r z).f (j - 1)).hom) :=
        injective_cokernelπ_f (dzComplex r) D (dzMap r D z) (j - 1)
          (dzMap_f_of_ne r D z (j - 1) hj1)
      have hcomm := congrArg (fun (u : D.X j ⟶ (dzCoker D r z).X (j - 1)) =>
        ModuleCat.Hom.hom u w₀) (HomologicalComplex.Hom.comm (dzCokerπ D r z) j (j - 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
      have hzero : ((dzCokerπ D r z).f (j - 1)).hom ((D.d j (j - 1)).hom w₀) = 0 := by
        rw [← hcomm]
        rw [hw₀, hq]
      have hdw : (D.d j (j - 1)).hom w₀ = 0 :=
        hinj (hzero.trans (map_zero (((dzCokerπ D r z).f (j - 1)).hom)).symm)
      obtain ⟨mm, hmm, y, hy⟩ :=
        cyclesTorsion_of_subsingleton_tensorRat D j (hvan j hj h1) w₀ hdw
      refine ⟨mm, hmm, ((dzCokerπ D r z).f (j + 1)).hom y, ?_⟩
      have hcomm2 := congrArg (fun (u : D.X (j + 1) ⟶ (dzCoker D r z).X j) =>
        ModuleCat.Hom.hom u y) (HomologicalComplex.Hom.comm (dzCokerπ D r z) (j + 1) j)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm2
      rw [hcomm2, hy, map_nsmul, hw₀]

/-! ## The cross product map `T` -/

/-- The "cross product with `z`" on the level of cycles: the cycles of `C` in degree `m` are sent
to the classes of `u ⊗ z`. -/
noncomputable def crossTOnCycles (C D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) (m : ℕ) :
    ↥(ModuleCat.of ℤ ↥(Work.Kunneth.cycKer C m)) →ₗ[ℤ]
      ↥((Work.Kunneth.tpC C D).homology (m + r + 1)) :=
  (((Work.Kunneth.tpC C D).homologyπ (m + r + 1)).hom).comp
    ((Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega)).comp
      (((TensorProduct.comm ℤ ↥(D.cycles (r + 1)) ↥(C.cycles m)).toLinearMap).comp
        (((TensorProduct.mk ℤ ↥(D.cycles (r + 1)) ↥(C.cycles m)) z).comp
          ((Work.Kunneth.cycIso C m).inv.hom))))

/-- The value of `crossTOnCycles` on a cycle of `C`. -/
theorem crossTOnCycles_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) (m : ℕ) (u : ↥(C.cycles m)) :
    crossTOnCycles C D r z m ((Work.Kunneth.cycIso C m).hom.hom u)
      = ((Work.Kunneth.tpC C D).homologyπ (m + r + 1)).hom
          (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega)
            (u ⊗ₜ[ℤ] z)) := by
  have h1 : ((Work.Kunneth.cycIso C m).inv.hom) ((Work.Kunneth.cycIso C m).hom.hom u) = u :=
    Work.Kunneth.homIso_inv_apply _ u
  have h2 : ((TensorProduct.mk ℤ ↥(D.cycles (r + 1)) ↥(C.cycles m)) z) u = z ⊗ₜ[ℤ] u := by
    rw [TensorProduct.mk_apply]
  have h3 : (TensorProduct.comm ℤ ↥(D.cycles (r + 1)) ↥(C.cycles m)).toLinearMap (z ⊗ₜ[ℤ] u)
      = u ⊗ₜ[ℤ] z :=
    TensorProduct.comm_tmul ℤ ↥(D.cycles (r + 1)) ↥(C.cycles m) z u
  show ((Work.Kunneth.tpC C D).homologyπ (m + r + 1)).hom
      (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega)
        ((TensorProduct.comm ℤ ↥(D.cycles (r + 1)) ↥(C.cycles m)).toLinearMap
          (((TensorProduct.mk ℤ ↥(D.cycles (r + 1)) ↥(C.cycles m)) z)
            ((Work.Kunneth.cycIso C m).inv.hom ((Work.Kunneth.cycIso C m).hom.hom u))))) = _
  rw [h1, h2, h3]

/-- `crossTOnCycles` kills the boundaries: a boundary cycle of `C` is sent to zero. -/
theorem crossTOnCycles_homBnd (C D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) (m : ℕ) :
    Work.Kunneth.homBnd C m ≤ LinearMap.ker (crossTOnCycles C D r z m) := by
  intro x hx
  rw [Work.Kunneth.mem_homBnd_iff] at hx
  obtain ⟨w, hw⟩ := hx
  rw [LinearMap.mem_ker]
  set u : ↥(C.cycles m) := Work.Kunneth.cycleOf C m x with hu
  have hiu : (C.iCycles m).hom u = (x : ↥(C.X m)) := by
    rw [hu]
    exact Work.Kunneth.iCycles_cycleOf C m x
  have hxC : ((Work.Kunneth.cycIso C m).hom.hom u) = x := by
    rw [hu]
    exact Work.Kunneth.homIso_hom_apply (Work.Kunneth.cycIso C m) x
  rw [← hxC, crossTOnCycles_apply]
  refine Work.Kunneth.homologyπ_eq_zero_of_d_eq (Work.Kunneth.tpC C D) (m + r + 1)
    (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega) (u ⊗ₜ[ℤ] z))
    (Work.Kunneth.tpLof C D (m + r + 2) ⟨(m + 1, r + 1), by omega⟩
      (w ⊗ₜ[ℤ] ((D.iCycles (r + 1)) z))) ?_
  rw [show ((Work.Kunneth.tpC C D).d (m + r + 2) (m + r + 1)).hom
      = Work.Kunneth.tpD C D (m + r + 1) from by rw [Work.Kunneth.tpC_d]; rfl]
  rw [Work.Kunneth.iCycles_crossCycTens]
  rw [Work.Kunneth.crossCycleMap_tmul]
  show Work.Kunneth.tpD C D (m + r + 1)
      (Work.Kunneth.tpLof C D (m + r + 1 + 1) ⟨(m + 1, r + 1), by omega⟩
        (w ⊗ₜ[ℤ] ((D.iCycles (r + 1)) z)))
    = Work.Kunneth.tpLof C D (m + r + 1) ⟨(m, r + 1), by omega⟩
        (((C.iCycles m) u) ⊗ₜ[ℤ] ((D.iCycles (r + 1)) z))
  rw [Work.Kunneth.tpD_lof_tmul]
  rw [dif_pos (by omega : 1 ≤ m + 1)]
  rw [dif_pos (by omega : 1 ≤ r + 1)]
  rw [Work.Kunneth.d_iCycles, TensorProduct.tmul_zero, map_zero, zsmul_zero, add_zero]
  show Work.Kunneth.tpLof C D (m + r + 1) ⟨(m, r + 1), by omega⟩
      (((C.d (m + 1) m).hom w) ⊗ₜ[ℤ] ((D.iCycles (r + 1)) z))
    = Work.Kunneth.tpLof C D (m + r + 1) ⟨(m, r + 1), by omega⟩
      (((C.iCycles m) u) ⊗ₜ[ℤ] ((D.iCycles (r + 1)) z))
  rw [hiu, hw]

/-- The linear map underlying `crossT`. -/
noncomputable def crossTLinear (C D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) (m : ℕ) :
    ↥(C.homology m) →ₗ[ℤ] ↥((Work.Kunneth.tpC C D).homology (m + r + 1)) :=
  (Submodule.liftQ (Work.Kunneth.homBnd C m) (crossTOnCycles C D r z m)
      (crossTOnCycles_homBnd C D r z m)).comp ((Work.Kunneth.homQuotIso C m).hom.hom)

/-- **The cross product with `z`**, as a map on homology. -/
noncomputable def crossT (C D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) (m : ℕ) :
    C.homology m ⟶ (Work.Kunneth.tpC C D).homology (m + r + 1) :=
  ModuleCat.ofHom (crossTLinear C D r z m)

/-- The defining property of `crossT` on the classes of cycles. -/
theorem crossTLinear_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) (m : ℕ) (u : ↥(C.cycles m)) :
    crossTLinear C D r z m ((C.homologyπ m).hom u)
      = ((Work.Kunneth.tpC C D).homologyπ (m + r + 1)).hom
          (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega)
            (u ⊗ₜ[ℤ] z)) := by
  have h1 : (Work.Kunneth.homQuotIso C m).hom.hom ((C.homologyπ m).hom u)
      = (Work.Kunneth.homBnd C m).mkQ ((Work.Kunneth.cycIso C m).hom.hom u) :=
    Work.Kunneth.homQuotIso_apply C m u
  have key : (Submodule.liftQ (Work.Kunneth.homBnd C m) (crossTOnCycles C D r z m)
      (crossTOnCycles_homBnd C D r z m))
      ((Work.Kunneth.homQuotIso C m).hom.hom ((C.homologyπ m).hom u))
      = ((Work.Kunneth.tpC C D).homologyπ (m + r + 1)).hom
          (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega) (u ⊗ₜ[ℤ] z)) := by
    rw [h1, Submodule.mkQ_apply]
    exact (Submodule.liftQ_apply (p := Work.Kunneth.homBnd C m)
      (f := crossTOnCycles C D r z m) (h := crossTOnCycles_homBnd C D r z m)
      ((Work.Kunneth.cycIso C m).hom.hom u)).trans (crossTOnCycles_apply C D r z m u)
  exact key

/-- The defining property of `crossT` on the classes of cycles. -/
theorem crossT_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ)
    (z : ↥(D.cycles (r + 1))) (m : ℕ) (u : ↥(C.cycles m)) :
    (crossT C D r z m).hom ((C.homologyπ m).hom u)
      = ((Work.Kunneth.tpC C D).homologyπ (m + r + 1)).hom
          (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega)
            (u ⊗ₜ[ℤ] z)) := by
  simp only [crossT, ModuleCat.hom_ofHom]
  exact crossTLinear_apply C D r z m u

/-! ## The image of the cross product with `z` -/

/-- The complex `C ⊗ ℤ[r+1]`. -/
abbrev tpCdz (C : ChainComplex (ModuleCat ℤ) ℕ) (r : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  Work.Kunneth.tpC C (dzComplex r)

/-- The image of `homologyMap (tpMap C C ℤ[r+1] D 𝟙 (dzMap r D z)) (m+r+1)` is contained in the
image of the cross product with `z`.

The proof extracts, from a cycle of `tpC C ℤ[r+1]` representing a homology class, the
`(m, r+1)`-entry `α` (all other entries vanish because `ℤ[r+1]` is concentrated in degree `r+1`),
which is a cycle of `C_m ⊗ ℤ` up to a multiple, and applies
`exists_cycle_map_dzGen_tmul`. -/
theorem homologyMap_tpMap_image_le (C D : ChainComplex (ModuleCat ℤ) ℕ) (r m : ℕ)
    (z : ↥(D.cycles (r + 1)))
    (b : ↥((Work.Kunneth.tpC C (dzComplex r)).homology (m + r + 1))) :
    (HomologicalComplex.homologyMap
      (Work.Kunneth.tpMap C C (dzComplex r) D (𝟙 C) (dzMap r D z)) (m + r + 1)).hom b
      ∈ LinearMap.range (crossT C D r z m).hom := by
  obtain ⟨z₀, hz₀⟩ := Submodule.mkQ_surjective
    (Work.Kunneth.homBnd (tpCdz C r) (m + r + 1))
    ((Work.Kunneth.homQuotIso (tpCdz C r) (m + r + 1)).hom.hom b)
  set x : ↥((tpCdz C r).cycles (m + r + 1)) :=
    Work.Kunneth.cycleOf (tpCdz C r) (m + r + 1) z₀ with hxdef
  have hx : ((tpCdz C r).homologyπ (m + r + 1)).hom x = b := by
    rw [hxdef, Work.Kunneth.homologyπ_cycleOf, hz₀]
    exact Work.Kunneth.homIso_inv_apply (Work.Kunneth.homQuotIso (tpCdz C r) (m + r + 1)) b
  have hxval : ((tpCdz C r).iCycles (m + r + 1)).hom x
      = (z₀ : ↥((tpCdz C r).X (m + r + 1))) := by
    rw [hxdef]
    exact Work.Kunneth.iCycles_cycleOf (tpCdz C r) (m + r + 1) z₀
  have hz₀cyc : ((tpCdz C r).d (m + r + 1) (m + r)).hom
      (z₀ : ↥((tpCdz C r).X (m + r + 1))) = 0 := z₀.2
  set α : Work.Kunneth.tpSummand C (dzComplex r) m (r + 1) :=
    (show Work.Kunneth.tpX C (dzComplex r) (m + r + 1)
      from (z₀ : ↥((tpCdz C r).X (m + r + 1)))) ⟨(m, r + 1), by omega⟩ with hαdef
  have hxdecomp : (z₀ : ↥((tpCdz C r).X (m + r + 1)))
      = Work.Kunneth.tpLof C (dzComplex r) (m + r + 1) ⟨(m, r + 1), by omega⟩ α := by
    show (show Work.Kunneth.tpX C (dzComplex r) (m + r + 1)
        from (z₀ : ↥((tpCdz C r).X (m + r + 1))))
      = (Work.Kunneth.tpLof C (dzComplex r) (m + r + 1) ⟨(m, r + 1), by omega⟩ α
        : Work.Kunneth.tpX C (dzComplex r) (m + r + 1))
    have hsum := Work.Serre.tpX_sum_lof C (dzComplex r) (m + r + 1)
      (show Work.Kunneth.tpX C (dzComplex r) (m + r + 1)
        from (z₀ : ↥((tpCdz C r).X (m + r + 1))))
    rw [← hsum]
    refine (Finset.sum_eq_single (⟨(m, r + 1), by omega⟩ : Work.Kunneth.tpIdx (m + r + 1))
      ?_ ?_).trans ?_
    · intro pq _ hpq
      have hq2 : pq.1.2 ≠ r + 1 := by
        intro hc
        apply hpq
        apply Subtype.ext
        apply Prod.ext
        · show pq.1.1 = m
          omega
        · exact hc
      haveI : Subsingleton ↥((dzComplex r).X pq.1.2) := subsingleton_dzComplex_X r pq.1.2 hq2
      haveI : Subsingleton (Work.Kunneth.tpSummand C (dzComplex r) pq.1.1 pq.1.2) :=
        subsingleton_tensor_of_subsingleton_right
      rw [Subsingleton.elim ((show Work.Kunneth.tpX C (dzComplex r) (m + r + 1)
        from (z₀ : ↥((tpCdz C r).X (m + r + 1)))) pq) 0, map_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
    · rfl
  suffices hαzero : TensorProduct.map ((C.d m (m - 1)).hom) (LinearMap.id) α = 0 by
    obtain ⟨u, hu⟩ := exists_cycle_map_dzGen_tmul C D r m z α hαzero
    refine ⟨(C.homologyπ m).hom u, ?_⟩
    rw [crossT_apply C D r z m u, ← hx, Work.Kunneth.homologyMap_apply_homologyπ]
    have hcyceq : (Work.Kunneth.tpC C D).iCycles (m + r + 1)
          (HomologicalComplex.cyclesMap (Work.Kunneth.tpMap C C (dzComplex r) D (𝟙 C)
            (dzMap r D z)) (m + r + 1) x)
        = (Work.Kunneth.tpC C D).iCycles (m + r + 1)
          (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega) (u ⊗ₜ[ℤ] z)) := by
      rw [Work.Kunneth.iCycles_cyclesMap, hxval, hxdecomp, Work.Kunneth.tpMap_tpLof,
        Work.Kunneth.iCycles_crossCycTens, Work.Kunneth.crossCycleMap_tmul]
      simp only [HomologicalComplex.id_f, ModuleCat.hom_id]
      rw [hu]
    have hπeq := Work.Kunneth.homologyπ_eq_of_sub_eq_d (Work.Kunneth.tpC C D) (m + r + 1)
      (HomologicalComplex.cyclesMap (Work.Kunneth.tpMap C C (dzComplex r) D (𝟙 C)
        (dzMap r D z)) (m + r + 1) x)
      (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega) (u ⊗ₜ[ℤ] z))
      0 (by rw [hcyceq, map_zero, sub_self])
    exact hπeq.symm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    rw [show C.d 0 (0 - 1) = 0 from
      HomologicalComplex.shape C 0 0 (by simp [ComplexShape.down])]
    rw [ModuleCat.hom_zero, TensorProduct.map_zero_left]
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hcomp := Work.Serre.tpDApplyComp C (dzComplex r) ((k + 1) + r)
      (⟨(k, r + 1), by omega⟩ : Work.Kunneth.tpIdx ((k + 1) + r))
      (show Work.Kunneth.tpX C (dzComplex r) ((k + 1) + r + 1)
        from (z₀ : ↥((tpCdz C r).X ((k + 1) + r + 1))))
    have hx0 : Work.Kunneth.tpD C (dzComplex r) ((k + 1) + r)
        (show Work.Kunneth.tpX C (dzComplex r) ((k + 1) + r + 1)
          from (z₀ : ↥((tpCdz C r).X ((k + 1) + r + 1)))) = 0 := by
      have h2 := hz₀cyc
      rw [show ((tpCdz C r).d ((k + 1) + r + 1) ((k + 1) + r))
          = ModuleCat.ofHom (Work.Kunneth.tpD C (dzComplex r) ((k + 1) + r)) from
          Work.Kunneth.tpC_d C (dzComplex r) ((k + 1) + r)] at h2
      exact h2
    rw [hx0, DFinsupp.zero_apply] at hcomp
    have hx12 : (show Work.Kunneth.tpX C (dzComplex r) ((k + 1) + r + 1)
        from (z₀ : ↥((tpCdz C r).X ((k + 1) + r + 1))))
        ⟨(k, r + 2), by omega⟩ = 0 := by
      haveI : Subsingleton ↥((dzComplex r).X (r + 2)) :=
        subsingleton_dzComplex_X r (r + 2) (by omega)
      haveI : Subsingleton (Work.Kunneth.tpSummand C (dzComplex r) k (r + 2)) :=
        subsingleton_tensor_of_subsingleton_right
      exact Subsingleton.elim _ _
    rw [hx12, map_zero, zsmul_zero, zero_add] at hcomp
    exact hcomp.symm

/-! ## Rationalisation of quotients -/

/-- A surjection of `ℤ`-modules remains surjective after tensoring with `ℚ`, so a module whose
rationalisation is trivial has a quotient whose rationalisation is trivial. -/
theorem subsingleton_tensorRat_of_surjective {M N : ModuleCat ℤ} (f : M ⟶ N)
    (hf : Function.Surjective f.hom) (h : Subsingleton (TensorProduct ℤ ↥M ℚ)) :
    Subsingleton (TensorProduct ℤ ↥N ℚ) := by
  haveI : Subsingleton (TensorProduct ℤ ↥M ℚ) := h
  have hsurj : Function.Surjective (TensorProduct.map f.hom (LinearMap.id : ℚ →ₗ[ℤ] ℚ)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul n q =>
        obtain ⟨m, hm⟩ := hf n
        exact ⟨m ⊗ₜ[ℤ] q, by rw [TensorProduct.map_tmul, hm, LinearMap.id_apply]⟩
    | add a b ha hb =>
        obtain ⟨x, hx⟩ := ha
        obtain ⟨y', hy⟩ := hb
        exact ⟨x + y', by rw [map_add, hx, hy]⟩
  rw [subsingleton_iff]
  intro a b
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y', rfl⟩ := hsurj b
  rw [Subsingleton.elim x y']

/-! ## The main theorem -/

theorem crossProduct_coker_rat (C D : ChainComplex (ModuleCat ℤ) ℕ)
    (hC : ∀ i, Module.Free ℤ ↥(C.X i))
    (r N : ℕ) (z : ↥(D.cycles (r + 1))) (hz : z ≠ 0)
    (hvan : ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 → Subsingleton (TensorProduct ℤ ↥(D.homology j) ℚ))
    (h0 : Subsingleton (TensorProduct ℤ ↥(D.homology 0) ℚ))
    (hgen : ∀ w : ↥(D.homology (r + 1)), ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ,
      TensorProduct.tmul ℤ (n • w) (1 : ℚ) = TensorProduct.tmul ℤ (m • ((D.homologyπ (r + 1)).hom z)) (1 : ℚ)) :
    ∀ m : ℕ, m + r + 1 ≤ N + 1 →
      ∃ (T : C.homology m ⟶ (Work.Kunneth.tpC C D).homology (m + r + 1)),
        (∀ u : ↥(C.cycles m), T.hom ((C.homologyπ m).hom u)
            = ((Work.Kunneth.tpC C D).homologyπ (m + r + 1)).hom
                (Work.Kunneth.crossCycTens C D (m + r + 1) m (r + 1) (by omega)
                  (TensorProduct.tmul ℤ u z)))
        ∧ Subsingleton (TensorProduct ℤ ↥(CategoryTheory.Limits.cokernel T) ℚ) := by
  intro m hm
  refine ⟨crossT C D r z m, crossT_apply C D r z m, ?_⟩
  by_cases hzt : TensorProduct.tmul ℤ ((D.homologyπ (r + 1)).hom z) (1 : ℚ) = 0
  · -- the class of `z` dies after rationalisation: the rational homology of `D` vanishes
    have hD := subsingleton_homology_rat_of_hgen D r N z hvan hgen hzt
    have htp := Work.Serre.tensorRat_subsingleton_of_subsingleton C D (N + 1) hC hD
      (m + r + 1) hm
    exact subsingleton_tensorRat_of_surjective (CategoryTheory.Limits.cokernel.π (crossT C D r z m))
      ((ModuleCat.epi_iff_surjective _).mp inferInstance) htp
  · -- the class of `z` survives: use the quotient complex `D ⧸ ℤz`
    have hmono : Mono (dzMap r D z) := mono_dzMap r D z (z_chain_not_torsion D r z hzt)
    have hKrat := coker_dzMap_homology_rat_subsingleton D r N z hvan hgen hzt
    have hquot : ∀ j, j ≤ N + 1 → Subsingleton (TensorProduct ℤ
        ↥((Work.Kunneth.tpC C (dzCoker D r z)).homology j) ℚ) :=
      fun j hj => Work.Serre.tensorRat_subsingleton_of_subsingleton C (dzCoker D r z) (N + 1)
        hC hKrat j hj
    have hA := Work.Serre.tpC_homologyMap_cokernel_subsingleton C D (dzComplex r) (N + 1)
      (dzMap r D z) hmono hC hquot (m + r + 1) hm
    have hfac : HomologicalComplex.homologyMap
          (Work.Kunneth.tpMap C C (dzComplex r) D (𝟙 C) (dzMap r D z)) (m + r + 1)
        ≫ CategoryTheory.Limits.cokernel.π (crossT C D r z m) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro b
      obtain ⟨v, hv⟩ := homologyMap_tpMap_image_le C D r m z b
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply]
      rw [← hv]
      exact cokernel_π_comp_apply _ v
    have hdesc : CategoryTheory.Limits.cokernel.π (HomologicalComplex.homologyMap
          (Work.Kunneth.tpMap C C (dzComplex r) D (𝟙 C) (dzMap r D z)) (m + r + 1))
        ≫ (CategoryTheory.Limits.cokernel.desc (HomologicalComplex.homologyMap
            (Work.Kunneth.tpMap C C (dzComplex r) D (𝟙 C) (dzMap r D z)) (m + r + 1))
          (CategoryTheory.Limits.cokernel.π (crossT C D r z m)) hfac)
        = CategoryTheory.Limits.cokernel.π (crossT C D r z m) :=
      CategoryTheory.Limits.cokernel.π_desc _ _ _
    have hΦ : Epi (CategoryTheory.Limits.cokernel.desc (HomologicalComplex.homologyMap
          (Work.Kunneth.tpMap C C (dzComplex r) D (𝟙 C) (dzMap r D z)) (m + r + 1))
          (CategoryTheory.Limits.cokernel.π (crossT C D r z m)) hfac) :=
      CategoryTheory.epi_of_epi_fac hdesc
    exact subsingleton_tensorRat_of_surjective _ ((ModuleCat.epi_iff_surjective _).mp hΦ) hA

end

end Work.Serre
