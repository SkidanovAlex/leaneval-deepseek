import Mathlib
import Submission.Work.SSGRoute.prop5.lctf.coreDefs
import Submission.Work.SSGRoute.prop5.coreGraded
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The lower central factors of a free group are spanned by commutator monomials

For a binary tree `c : Magma X` of size `m` the commutator monomial `monGrp X c` is an element of
the lower central series term `Gam X (m - 1)` of the free group.  This file proves that the classes
of the trees of size `n+1` span `Λ_n = γ_n/γ_{n+1}`:

`cls X n y ∈ range (treeToLam X (n+1))`  for every `y ∈ γ_n`.

The proof is a direct induction using `Gam X (m+1) = ⁅Gam X m, ⊤⁆`, the graded bilinearity of the
commutator modulo the next term, and the fact that bracketing a weight-`m` monomial with a
generator produces a weight-`(m+1)` monomial.  (Ported from `Submission/Work/lctf/`.)
-/

noncomputable section

open scoped commutatorElement

set_option linter.style.haveILetI false

namespace Work.SSGRoute.prop5.lctf

open Work.SSGRoute.prop5

variable {X : Type*}

/-- The set of commutator monomials of weight `m`. -/
def monGrpSet (X : Type*) (m : ℕ) : Set (FreeGroup X) :=
  {x | ∃ c : Magma X, Magma.size c = m ∧ x = monGrp X c}

theorem mem_monGrpSet {m : ℕ} {x : FreeGroup X} :
    x ∈ monGrpSet X m ↔ ∃ c : Magma X, Magma.size c = m ∧ x = monGrp X c := Iff.rfl

/-- The commutator of a supremum: if `A`, `B`, `C` are normal then
`⁅A ⊔ B, C⁆ ≤ ⁅A,C⁆ ⊔ ⁅B,C⁆`. -/
theorem commutator_sup_le_of_normal {G : Type*} [Group G] (A B C : Subgroup G)
    [A.Normal] [B.Normal] [C.Normal] : ⁅A ⊔ B, C⁆ ≤ ⁅A, C⁆ ⊔ ⁅B, C⁆ := by
  refine Subgroup.commutator_le.mpr ?_
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := A) (t := B)).mp hx
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : a * ⁅b, y⁆ * a⁻¹ ∈ ⁅B, C⁆ :=
    Subgroup.Normal.conj_mem (Subgroup.commutator_normal B C) ⁅b, y⁆
      (Subgroup.commutator_mem_commutator hb hy) a
  have h2 : ⁅a, y⁆ ∈ ⁅A, C⁆ := Subgroup.commutator_mem_commutator ha hy
  have h1' : a * ⁅b, y⁆ * a⁻¹ ∈ ⁅A, C⁆ ⊔ ⁅B, C⁆ := Subgroup.mem_sup_right h1
  have h2' : ⁅a, y⁆ ∈ ⁅A, C⁆ ⊔ ⁅B, C⁆ := Subgroup.mem_sup_left h2
  exact Subgroup.mul_mem _ h1' h2'

/-- If a weight-`m` monomial bracketed with every generator lies in `K`, then it bracketed with
every element of the free group lies in `K` (`K` normal). -/
theorem bracket_monGrp_of_gen {c : Magma X} {K : Subgroup (FreeGroup X)} [K.Normal]
    (hgen : ∀ x : X, ⁅monGrp X c, FreeGroup.of x⁆ ∈ K) :
    ∀ q : FreeGroup X, ⁅monGrp X c, q⁆ ∈ K := by
  intro q
  refine FreeGroup.induction_on q ?_ ?_ ?_ ?_
  · simp
  · intro x; exact hgen x
  · intro x hx
    rw [commutatorElement_inv_right, ← commutatorElement_inv (monGrp X c) (FreeGroup.of x)]
    simpa using Subgroup.Normal.conj_mem (inferInstance : K.Normal)
      (⁅monGrp X c, FreeGroup.of x⁆⁻¹) (K.inv_mem hx) (FreeGroup.of x)⁻¹
  · intro a b ha hb
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hc : a * ⁅monGrp X c, b⁆ * a⁻¹ ∈ K :=
      Subgroup.Normal.conj_mem (inferInstance : K.Normal) ⁅monGrp X c, b⁆ hb a
    rw [show ⁅monGrp X c, a⁆ * a * ⁅monGrp X c, b⁆ * a⁻¹
          = ⁅monGrp X c, a⁆ * (a * ⁅monGrp X c, b⁆ * a⁻¹) from by group]
    exact K.mul_mem ha hc

/-- **The crux.**  Bracketing the normal closure of the weight-`(m+1)` monomials with the whole
free group only produces elements of the normal closure of the weight-`(m+2)` monomials, modulo
`Gam X (m+2)`. -/
theorem crux (X : Type) (m : ℕ) :
    ⁅Subgroup.normalClosure (monGrpSet X (m + 1)), (⊤ : Subgroup (FreeGroup X))⁆ ≤
      Subgroup.normalClosure (monGrpSet X (m + 2)) ⊔ Gam X (m + 2) := by
  set K : Subgroup (FreeGroup X) :=
    Subgroup.normalClosure (monGrpSet X (m + 2)) ⊔ Gam X (m + 2) with hK
  haveI hKnorm : K.Normal := by rw [hK]; infer_instance
  let T : Subgroup (FreeGroup X) :=
    { carrier := {u | ∀ q : FreeGroup X, ⁅u, q⁆ ∈ K}
      one_mem' := by intro q; simp
      mul_mem' := by
        intro u v hu hv q
        change ⁅u * v, q⁆ ∈ K
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hc : u * ⁅v, q⁆ * u⁻¹ ∈ K :=
          Subgroup.Normal.conj_mem hKnorm ⁅v, q⁆ (hv q) u
        exact K.mul_mem hc (hu q)
      inv_mem' := by
        intro u hu q
        change ⁅u⁻¹, q⁆ ∈ K
        rw [commutatorElement_inv_left, ← commutatorElement_inv u q]
        simpa using Subgroup.Normal.conj_mem hKnorm (⁅u, q⁆⁻¹) (K.inv_mem (hu q)) u⁻¹ }
  haveI hTnorm : T.Normal :=
    ⟨fun n hn g => by
      change ∀ q : FreeGroup X, ⁅g * n * g⁻¹, q⁆ ∈ K
      intro q
      have h := Subgroup.Normal.conj_mem hKnorm (⁅n, g⁻¹ * q * g⁆) (hn (g⁻¹ * q * g)) g
      rw [conjugate_commutatorElement n (g⁻¹ * q * g) g] at h
      simpa [show g * (g⁻¹ * q * g) * g⁻¹ = q from by group] using h⟩
  have hUT : Subgroup.normalClosure (monGrpSet X (m + 1)) ≤ T :=
    Subgroup.normalClosure_le_normal (fun s hs => by
      obtain ⟨c, hc, rfl⟩ := hs
      intro q
      refine bracket_monGrp_of_gen (c := c) (fun x => ?_) q
      have hmul : ⁅monGrp X c, FreeGroup.of x⁆ = monGrp X (Magma.mul c (Magma.gen x)) := by
        rw [monGrp_mul, monGrp_gen]
      rw [hmul]
      refine Subgroup.mem_sup_left (Subgroup.subset_normalClosure ?_)
      exact ⟨Magma.mul c (Magma.gen x), by rw [Magma.size_mul, hc, Magma.size_gen], rfl⟩)
  refine Subgroup.commutator_le.mpr ?_
  intro u hu q _
  exact hUT hu q

/-- **The main group-theoretic statement.**  The `m`-th term of the lower central series of a free
group is generated by the commutator monomials of weight `m+1`, modulo the next term. -/
theorem lcs_le_normalClosure_sup (X : Type) : ∀ m : ℕ,
    Gam X m ≤ Subgroup.normalClosure (monGrpSet X (m + 1)) ⊔ Gam X (m + 1) := by
  intro m
  induction m with
  | zero =>
      have h0 : Gam X 0 = ⊤ := graded.Gam_zero
      rw [h0]
      rw [← FreeGroup.closure_range_of X]
      rw [Subgroup.closure_le]
      rintro x ⟨y, rfl⟩
      exact Subgroup.mem_sup_left
        (Subgroup.subset_normalClosure ⟨Magma.gen y, Magma.size_gen y, by simp [monGrp_gen]⟩)
  | succ m ih =>
      have hs : Gam X (m + 1) = ⁅Gam X m, ⊤⁆ := graded.Gam_succ m
      rw [hs]
      refine le_trans (Subgroup.commutator_mono ih le_rfl) ?_
      refine le_trans (commutator_sup_le_of_normal _ _ _) ?_
      exact sup_le (crux X m) le_sup_right

/-- Auxiliary: the class of `v * x * v⁻¹` equals the class of `x` for `x ∈ Gam X n`. -/
theorem cls_conj (X : Type) (n : ℕ) (x : Gam X n) (v : FreeGroup X)
    (hmem : v * (x : FreeGroup X) * v⁻¹ ∈ Gam X n) :
    cls X n ⟨v * (x : FreeGroup X) * v⁻¹, hmem⟩ = cls X n x := by
  have hc : v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹ ∈ Gam X (n + 1) :=
    graded.conj_diff_mem n x.2 v
  have hc' : v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹ ∈ Gam X n :=
    graded.Gam_antitone (Nat.le_succ n) hc
  have hweq : (⟨v * (x : FreeGroup X) * v⁻¹, hmem⟩ : Gam X n) =
      (⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ : Gam X n) * x := by
    ext
    simp only [Subgroup.coe_mul]
    group
  rw [hweq]
  have hadd : cls X n ((⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ : Gam X n) * x)
      = cls X n ⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ + cls X n x := by
    rw [cls_apply, cls_apply, cls_apply, map_mul]
    rfl
  rw [hadd]
  have hz : cls X n (⟨v * (x : FreeGroup X) * v⁻¹ * (x : FreeGroup X)⁻¹, hc'⟩ : Gam X n) = 0 := by
    rw [cls_eq_zero_iff]
    exact hc
  rw [hz, zero_add]

theorem cls_mem_range_treeToLam (X : Type) (n : ℕ) (y : Work.SSGRoute.prop5.lctf.Gam X n) :
    Work.SSGRoute.prop5.lctf.cls X n y ∈
      LinearMap.range (Work.SSGRoute.prop5.lctf.treeToLam X (n + 1)) := by
  set M : Submodule ℤ (Lam X n) := LinearMap.range (treeToLam X (n + 1)) with hM
  let Msub : Subgroup (Gam X n) :=
    { carrier := {x | cls X n x ∈ M}
      one_mem' := by
        show cls X n (1 : Gam X n) ∈ M
        rw [cls_one (X := X) n]
        exact M.zero_mem
      mul_mem' := by
        intro x z hx hz
        show cls X n (x * z) ∈ M
        rw [cls_mul n x z]
        exact M.add_mem hx hz
      inv_mem' := by
        intro x hx
        show cls X n x⁻¹ ∈ M
        rw [cls_inv n x]
        exact M.neg_mem hx }
  let P : Subgroup (FreeGroup X) := Subgroup.map (Gam X n).subtype Msub
  haveI hPnorm : P.Normal :=
    ⟨fun g hg v => by
      change v * g * v⁻¹ ∈ P
      rw [Subgroup.mem_map] at hg ⊢
      obtain ⟨x, hxM, hxg⟩ := hg
      have hwmem : v * (x : FreeGroup X) * v⁻¹ ∈ Gam X n :=
        Subgroup.Normal.conj_mem (inferInstance : (Gam X n).Normal) (x : FreeGroup X) x.2 v
      refine ⟨⟨v * (x : FreeGroup X) * v⁻¹, hwmem⟩, ?_, ?_⟩
      · change cls X n ⟨v * (x : FreeGroup X) * v⁻¹, hwmem⟩ ∈ M
        rw [cls_conj X n x v hwmem]
        exact hxM
      · show v * (x : FreeGroup X) * v⁻¹ = v * g * v⁻¹
        rw [show (x : FreeGroup X) = g from hxg]⟩
  have hUP : Subgroup.normalClosure (monGrpSet X (n + 1)) ≤ P :=
    Subgroup.normalClosure_le_normal (fun s hs => by
      obtain ⟨c, hc, rfl⟩ := hs
      have hg : monGrp X c ∈ Gam X n := by
        have h := monGrp_mem_Gam (X := X) c
        rw [hc] at h
        exact h
      refine Subgroup.mem_map.mpr ⟨⟨monGrp X c, hg⟩, ?_, rfl⟩
      change cls X n ⟨monGrp X c, hg⟩ ∈ M
      have h2 : treeClOf X (n + 1) ⟨c, hc⟩ = cls X n ⟨monGrp X c, hg⟩ := rfl
      rw [← h2]
      exact LinearMap.mem_range.mpr
        ⟨Finsupp.single ⟨c, hc⟩ 1, treeToLam_single (X := X) (n + 1) ⟨c, hc⟩⟩)
  have hyU : (y : FreeGroup X) ∈
      Subgroup.normalClosure (monGrpSet X (n + 1)) ⊔ Gam X (n + 1) :=
    lcs_le_normalClosure_sup X n y.2
  obtain ⟨u, hu, b, hb, hubeq⟩ :=
    (Subgroup.mem_sup_of_normal_left
      (s := Subgroup.normalClosure (monGrpSet X (n + 1))) (t := Gam X (n + 1))).mp hyU
  obtain ⟨xu, hxuM, hxueq⟩ := Subgroup.mem_map.mp (hUP hu)
  have hu' : u ∈ Gam X n := hxueq ▸ xu.2
  have hb' : b ∈ Gam X n := graded.Gam_antitone (Nat.le_succ n) hb
  have hy_eq : y = (⟨u, hu'⟩ : Gam X n) * ⟨b, hb'⟩ := by
    ext
    simpa [Subgroup.coe_mul] using hubeq.symm
  have hcls : cls X n y = cls X n ⟨u, hu'⟩ := by
    rw [hy_eq, cls_mul n]
    have hz : cls X n ⟨b, hb'⟩ = 0 := by
      rw [cls_eq_zero_iff]
      exact hb
    rw [hz, add_zero]
  rw [hcls]
  have hux : cls X n ⟨u, hu'⟩ = cls X n xu := by
    congr 1
    exact Subtype.ext hxueq.symm
  rw [hux]
  exact hxuM


end Work.SSGRoute.prop5.lctf
