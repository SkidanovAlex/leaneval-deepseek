/-
# The identification `H₁(G, M) ≅ Ĥ⁻¹(G, M^♯)` (the `I_G`-twist)

This file builds the classical identification of group homology with Tate cohomology,
`H₁(G, M) ≅ Ĥ⁻²(G, M) ≅ Ĥ⁻¹(G, M ⊗ I_G) ≅ Ĥ⁻¹(G, M^♯)`, for a finite group `G` and a
`G`-module `M`, in the explicit model `M^♯ = Work.Tate.coindUp G M = ker (∑ x⁻¹ • _)`.

The isomorphism is the connecting map of the short exact sequence
`0 → M^♯ → Coind(M) → M → 0`, written out concretely as `θ x = x - single 1 (∑_g x g)`, i.e. as
the map `Θ : Z₁(G,M) → ker(N_{M^♯}) ⊆ M^♯` which is a bijection onto `ker N_{M^♯}` and induces
`Z₁/B₁ ≅ ker N/I_G·M^♯`.
-/
import Mathlib
import Submission.Work.Tate.CoindUp
import Submission.Work.Tate.coind_norm_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Work.Bridge

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {k : Type} [CommRing k]
variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- The `G`-representation on `M` determined by the `DistribMulAction`. -/
noncomputable abbrev repM (k : Type) [CommRing k] (G : Type) [Group G] (M : Type)
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M] : Rep k G :=
  Rep.of (Representation.ofDistribMulAction k G M)

/-- Sum of the coefficients of a finitely supported function. -/
noncomputable def coeffSum (x : G →₀ M) : M := x.sum (fun _ a => a)

@[simp] theorem coeffSum_single (g : G) (m : M) :
    coeffSum (Finsupp.single g m) = m := by
  simp [coeffSum]

theorem coeffSum_add (x y : G →₀ M) : coeffSum (x + y) = coeffSum x + coeffSum y := by
  rw [coeffSum, coeffSum, coeffSum,
    Finsupp.sum_add_index (fun a _ => rfl) (fun a _ b₁ b₂ => rfl)]

theorem coeffSum_eq_sum (x : G →₀ M) : coeffSum x = ∑ g : G, x g := by
  rw [coeffSum, Finsupp.sum_fintype _ _ (fun i => rfl)]

theorem sum_eq_finsupp (x : G →₀ M) (f : G → M → M) (hf : ∀ g, f g 0 = 0) :
    (∑ g : G, f g (x g)) = x.sum f := by
  rw [Finsupp.sum_fintype _ _ hf]

/-- The "delta at `1`" function. -/
noncomputable def d1 (m : M) : G → M := fun g => if g = 1 then m else 0

@[simp] theorem d1_apply (m : M) (g : G) : d1 (G:=G) m g = if g = 1 then m else 0 := rfl

@[simp] theorem d1_zero : d1 (G:=G) (0 : M) = 0 := by
  funext g; simp [d1]

theorem d1_add (a b : M) : d1 (G:=G) (a + b) = d1 (G:=G) a + d1 (G:=G) b := by
  funext g; by_cases h : g = 1 <;> simp [d1, h]

theorem d1_neg (a : M) : d1 (G:=G) (-a) = -d1 (G:=G) a := by
  funext g; by_cases h : g = 1 <;> simp [d1, h]

theorem d1_sub (a b : M) : d1 (G:=G) (a - b) = d1 (G:=G) a - d1 (G:=G) b := by
  funext g; by_cases h : g = 1 <;> simp [d1, h]

@[simp] theorem d1_eq_zero_iff (m : M) : d1 (G:=G) m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have := congrFun h 1
    simpa using this
  · intro h; subst h; simp

/-- The "delta at `g`" function. -/
noncomputable def eg (g : G) (m : M) : G → M := fun y => if y = g then m else 0

@[simp] theorem eg_apply (g : G) (m : M) (y : G) : eg g m y = if y = g then m else 0 := rfl

theorem eg_add (g : G) (a b : M) : eg (G:=G) g (a + b) = eg (G:=G) g a + eg (G:=G) g b := by
  funext y; by_cases h : y = g <;> simp [eg, h]

theorem eg_neg (g : G) (a : M) : eg (G:=G) g (-a) = -eg (G:=G) g a := by
  funext y; by_cases h : y = g <;> simp [eg, h]

theorem eg_sub (g : G) (a b : M) : eg (G:=G) g (a - b) = eg (G:=G) g a - eg (G:=G) g b := by
  funext y; by_cases h : y = g <;> simp [eg, h]

theorem eg_eq_zero_iff (g : G) (m : M) : eg (G:=G) g m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have := congrFun h g
    simpa using this
  · intro h; subst h; funext y; simp [eg]

@[simp] theorem eg_one_eq_d1 (m : M) : eg (G:=G) 1 m = d1 (G:=G) m := by
  funext y; simp [eg, d1]

theorem finsupp_single_eq_eg (g : G) (m : M) :
    ⇑(Finsupp.single g m) = eg (G:=G) g m := by
  funext y
  rw [Finsupp.single_apply]
  by_cases h : g = y
  · subst h; simp [eg]
  · rw [if_neg h, eg, if_neg (Ne.symm h)]

/-- The correction map `x ↦ x - single 1 (∑ x)`, as a function `G → M`. -/
noncomputable def thetaFun (x : G →₀ M) : G → M :=
  fun g => x g - d1 (G:=G) (coeffSum x) g

@[simp] theorem thetaFun_apply (x : G →₀ M) (g : G) :
    thetaFun x g = x g - d1 (G:=G) (coeffSum x) g := rfl

theorem thetaFun_add (x y : G →₀ M) : thetaFun (x + y) = thetaFun x + thetaFun y := by
  funext g
  simp only [thetaFun, Pi.add_apply, coeffSum_add, d1_add, Finsupp.coe_add]
  abel

theorem thetaFun_zero : thetaFun (0 : G →₀ M) = 0 := by
  funext g
  simp [thetaFun_apply, coeffSum]

theorem thetaFun_neg (x : G →₀ M) : thetaFun (-x) = -thetaFun x := by
  funext g
  simp only [Pi.neg_apply]
  rw [thetaFun_apply, thetaFun_apply]
  have h : coeffSum (-x) = -coeffSum x := by
    rw [coeffSum_eq_sum, coeffSum_eq_sum]
    simp
  rw [h, d1_neg]
  simp only [Finsupp.coe_neg, Pi.neg_apply]
  abel

theorem thetaFun_sub (x y : G →₀ M) : thetaFun (x - y) = thetaFun x - thetaFun y := by
  rw [sub_eq_add_neg, thetaFun_add, thetaFun_neg, sub_eq_add_neg]

noncomputable def thetaHom : (G →₀ M) →+ (G → M) where
  toFun := thetaFun
  map_zero' := thetaFun_zero
  map_add' := thetaFun_add

@[simp] theorem thetaFun_single (g : G) (m : M) :
    thetaFun (Finsupp.single g m) = eg (G:=G) g m - d1 (G:=G) m := by
  funext y
  rw [thetaFun_apply, finsupp_single_eq_eg, coeffSum_single]
  rfl

/-! ## The coinduced action on `d1` and `eg` -/

theorem coind_smul_d1 (g : G) (m : M) : g⁻¹ • d1 (G:=G) m = eg (G:=G) g m := by
  funext y
  rw [Work.Tate.coind_smul_eq, d1_apply, eg_apply]
  by_cases hy : y = g
  · rw [if_pos (by rw [hy, mul_inv_cancel]), if_pos hy]
  · rw [if_neg (fun h => hy (mul_inv_eq_one.mp h)), if_neg hy]

theorem coind_smul_eg (g h : G) (m : M) :
    g⁻¹ • eg (G:=G) h m = eg (G:=G) (h * g) m := by
  funext y
  rw [Work.Tate.coind_smul_eq, eg_apply, eg_apply]
  by_cases hy : y = h * g
  · rw [if_pos (by rw [hy, mul_assoc, mul_inv_cancel, mul_one]), if_pos hy]
  · rw [if_neg (fun hh => hy (mul_inv_eq_iff_eq_mul.mp hh)), if_neg hy]

theorem sum_inv_smul_d1 (c : M) : (∑ x : G, x⁻¹ • d1 (G:=G) c x) = c := by
  rw [Finset.sum_eq_single (1:G)]
  · simp [d1]
  · intro b _ hb; simp [d1, hb]
  · intro h; exact absurd (Finset.mem_univ 1) h

theorem sum_inv_smul_eg (g : G) (c : M) : (∑ x : G, x⁻¹ • eg (G:=G) g c x) = g⁻¹ • c := by
  rw [Finset.sum_eq_single g]
  · simp [eg]
  · intro b _ hb; simp [eg, hb]
  · intro h; exact absurd (Finset.mem_univ g) h

/-! ## The short exact sequence generator `φ` -/

/-- The element `φ_{g,a} = single_1(g⁻¹•a) - single_g(a)` of `M^♯`. -/
noncomputable def phiFun (g : G) (a : M) : G → M :=
  d1 (G:=G) (g⁻¹ • a) - eg (G:=G) g a

theorem phiFun_mem (g : G) (a : M) :
    Work.Tate.coindAug G M (phiFun (G:=G) g a) = 0 := by
  have h : ∀ x : G, x⁻¹ • (d1 (G:=G) (g⁻¹ • a) - eg (G:=G) g a) x
      = x⁻¹ • d1 (G:=G) (g⁻¹ • a) x - x⁻¹ • eg (G:=G) g a x := fun x => by
    simp only [Pi.sub_apply, smul_sub]
  rw [phiFun, Work.Tate.coindAug_apply,
    Finset.sum_congr rfl (fun x _ => h x), Finset.sum_sub_distrib,
    sum_inv_smul_d1, sum_inv_smul_eg, sub_self]

/-- The key boundary computation: `θ (d₂₁ (single (g,h) a)) = h⁻¹ • φ_{g,a} - φ_{g,a}`. -/
theorem thetaFun_d21_single (g h : G) (a : M) :
    thetaFun (G:=G) ((groupHomology.d₂₁ (repM k G M)).hom (Finsupp.single (g,h) a))
      = h⁻¹ • phiFun (G:=G) g a - phiFun (G:=G) g a := by
  rw [groupHomology.d₂₁_single]
  have hρ : (repM k G M).ρ g⁻¹ a = g⁻¹ • a := rfl
  rw [hρ, thetaFun_add, thetaFun_sub]
  simp only [thetaFun_single]
  rw [phiFun, Work.Tate.coind_smul_sub, coind_smul_d1 h (g⁻¹ • a), coind_smul_eg h g a]
  abel

/-! ## The coinduced module, the norm and the augmentation -/

/-- The coinduced module `M^♯ ⊆ (G → M)`. -/
noncomputable abbrev A : AddSubgroup (G → M) := Work.Tate.coindUp G M

theorem coe_norm_A (y : A (G:=G) (M:=M)) :
    ((Work.Tate.norm G (A (G:=G) (M:=M)) y : A (G:=G) (M:=M)) : G → M)
      = ∑ g : G, g • (y : G → M) := by
  rw [Work.Tate.norm_apply,
    show ((∑ g : G, g • y : A (G:=G) (M:=M)) : G → M)
      = (A (G:=G) (M:=M)).subtype (∑ g : G, g • y) from rfl,
    Work.Tate.map_sum_univ]
  exact Finset.sum_congr rfl (fun g _ => Work.Tate.coe_smul_coindUp g y)

theorem coe_norm_A_eq_const (y : A (G:=G) (M:=M)) :
    ((Work.Tate.norm G (A (G:=G) (M:=M)) y : A (G:=G) (M:=M)) : G → M)
      = Function.const G (∑ g : G, (y : G → M) g) := by
  rw [coe_norm_A, ← Work.Tate.norm_apply]
  exact Work.Tate.coind_norm_eq_const (G := G) (y : G → M)

theorem sum_d1 (c : M) : (∑ g : G, d1 (G:=G) c g) = c := by
  rw [Finset.sum_eq_single (1:G)]
  · simp [d1]
  · intro b _ hb; simp [d1, hb]
  · intro h; exact absurd (Finset.mem_univ 1) h

theorem thetaFun_sum_eq (x : G →₀ M) : (∑ g : G, thetaFun (G:=G) x g) = 0 := by
  have h : ∀ g : G, thetaFun (G:=G) x g
      = x g - d1 (G:=G) (coeffSum x) g := fun g => thetaFun_apply x g
  rw [Finset.sum_congr rfl (fun g _ => h g), Finset.sum_sub_distrib, coeffSum_eq_sum,
    sum_d1, sub_self]

theorem thetaFun_mem_A {x : G →₀ M}
    (hx : x ∈ groupHomology.cycles₁ (repM k G M)) :
    thetaFun (G:=G) x ∈ A (G:=G) (M:=M) := by
  have h : ∀ g : G, g⁻¹ • thetaFun (G:=G) x g
      = g⁻¹ • x g - g⁻¹ • d1 (G:=G) (coeffSum x) g := fun g => by
    rw [thetaFun_apply]; simp only [Pi.sub_apply, smul_sub]
  rw [Work.Tate.mem_coindUp_iff,
    Finset.sum_congr rfl (fun g _ => h g), Finset.sum_sub_distrib, sum_inv_smul_d1]
  have h2 : (∑ g : G, g⁻¹ • x g) = coeffSum x := by
    rw [sum_eq_finsupp _ _ (by intro g; simp)]
    have := (groupHomology.mem_cycles₁_iff (A := repM k G M) x).mp hx
    have h3 : (fun g a => (repM k G M).ρ g⁻¹ a) = (fun g a => g⁻¹ • a) := by
      funext g a; rfl
    rw [h3] at this
    simpa [coeffSum] using this
  rw [h2, sub_self]

theorem thetaFun_mem_ker_norm {x : G →₀ M}
    (hx : x ∈ groupHomology.cycles₁ (repM k G M)) :
    (⟨thetaFun (G:=G) x, thetaFun_mem_A (k:=k) hx⟩ : A (G:=G) (M:=M))
      ∈ (Work.Tate.norm G (A (G:=G) (M:=M))).ker := by
  rw [AddMonoidHom.mem_ker, Subtype.ext_iff, coe_norm_A_eq_const]
  funext g
  simp only [Function.const_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
  exact thetaFun_sum_eq x

/-! ## The degree shift map `Θ : Z₁(G,M) → ker(N_{M^♯})` -/

/-- The 1-cycles of `M` with coefficients. -/
noncomputable abbrev Z (k : Type) [CommRing k] (G : Type) [Group G] [Fintype G] (M : Type)
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M] :
    Submodule k (G →₀ M) := groupHomology.cycles₁ (repM k G M)

/-- The 1-boundaries of `M` with coefficients. -/
noncomputable abbrev B (k : Type) [CommRing k] (G : Type) [Group G] [Fintype G] (M : Type)
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M] :
    Submodule k (G →₀ M) := groupHomology.boundaries₁ (repM k G M)

/-- The kernel of the norm on `M^♯`. -/
noncomputable abbrev K (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup (A (G:=G) (M:=M)) :=
  (Work.Tate.norm G (A (G:=G) (M:=M))).ker

/-- The augmentation `I_G · M^♯`, inside the kernel of the norm. -/
noncomputable abbrev I (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup (K (G:=G) (M:=M)) :=
  Work.Tate.augInKer G (A (G:=G) (M:=M))

/-- The concrete dimension-shift map `Z₁(G,M) →+ ker(N_{M^♯})`, `x ↦ x - single 1 (∑ x)`. -/
noncomputable def ThetaOn (k : Type) [CommRing k] (G : Type) [Group G] [Fintype G]
    [DecidableEq G] (M : Type) [AddCommGroup M] [Module k M] [DistribMulAction G M]
    [SMulCommClass G k M] : ↥(Z k G M) →+ K (G:=G) (M:=M) where
  toFun x := ⟨⟨thetaFun (G:=G) (x : G →₀ M),
      thetaFun_mem_A (k:=k) (x := (x : G →₀ M)) x.2⟩,
    thetaFun_mem_ker_norm (k:=k) (x := (x : G →₀ M)) x.2⟩
  map_zero' := Subtype.ext (Subtype.ext (thetaFun_zero (G:=G) (M:=M)))
  map_add' x y := Subtype.ext (Subtype.ext (thetaFun_add (x : G →₀ M) (y : G →₀ M)))

@[simp] theorem ThetaOn_coe (x : ↥(Z k G M)) :
    (((ThetaOn k G M x : K (G:=G) (M:=M)) : A (G:=G) (M:=M)) : G → M)
      = thetaFun (G:=G) (x : G →₀ M) := rfl


variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {k : Type} [CommRing k]
variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]

/-- The 1-boundaries, viewed inside the 1-cycles (as the kernel of `H1π`). -/
noncomputable abbrev Bz (k : Type) [CommRing k] (G : Type) [Group G] [Fintype G] (M : Type)
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M] :
    Submodule k ↥(Z k G M) := LinearMap.ker (groupHomology.H1π (repM k G M)).hom

theorem mem_Bz {x : ↥(Z k G M)} : x ∈ Bz k G M ↔ (x : G →₀ M) ∈ B k G M := by
  rw [Bz, LinearMap.mem_ker, groupHomology.H1π_eq_zero_iff]

theorem B_le_Z (x : G →₀ M) (hx : x ∈ B k G M) : x ∈ Z k G M :=
  groupHomology.boundaries₁_le_cycles₁ (repM k G M) hx

/-- The induced map `Z₁/B₁ → ker N / I_G·M^♯`. -/
noncomputable def ThetaQ
    (hbnd : ∀ b : ↥(Z k G M), (b : G →₀ M) ∈ B k G M →
      ((ThetaOn k G M b : K (G:=G) (M:=M)) : A (G:=G) (M:=M))
        ∈ Work.Tate.augmentation G (A (G:=G) (M:=M))) :
    (↥(Z k G M) ⧸ (Bz k G M).toAddSubgroup) →+
      (K (G:=G) (M:=M) ⧸ (I (G:=G) (M:=M))) :=
  QuotientAddGroup.lift (Bz k G M).toAddSubgroup
    ((QuotientAddGroup.mk' (I (G:=G) (M:=M))).comp (ThetaOn k G M))
    (fun b hb => by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, ← AddMonoidHom.mem_ker,
        QuotientAddGroup.ker_mk']
      exact hbnd b ((mem_Bz (k:=k)).mp hb))

theorem ThetaQ_apply (hbnd) (x : ↥(Z k G M)) :
    ThetaQ (k:=k) (G:=G) (M:=M) hbnd (QuotientAddGroup.mk x)
      = QuotientAddGroup.mk (ThetaOn k G M x) := by
  rw [ThetaQ, QuotientAddGroup.lift_mk]
  rfl

theorem ThetaQ_surjective (hbnd) (hsu : Function.Surjective (ThetaOn k G M)) :
    Function.Surjective (ThetaQ (k:=k) (G:=G) (M:=M) hbnd) := by
  intro y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (I (G:=G) (M:=M)) y
  obtain ⟨x, rfl⟩ := hsu w
  exact ⟨QuotientAddGroup.mk x, ThetaQ_apply (k:=k) (G:=G) (M:=M) hbnd x⟩

theorem ThetaQ_injective
    (hbnd : ∀ b : ↥(Z k G M), (b : G →₀ M) ∈ B k G M →
      ((ThetaOn k G M b : K (G:=G) (M:=M)) : A (G:=G) (M:=M))
        ∈ Work.Tate.augmentation G (A (G:=G) (M:=M)))
    (hle : ∀ y : A (G:=G) (M:=M), y ∈ Work.Tate.augmentation G (A (G:=G) (M:=M)) →
      ∃ b : ↥(Z k G M), (b : G →₀ M) ∈ B k G M ∧
        ((ThetaOn k G M b : K (G:=G) (M:=M)) : A (G:=G) (M:=M)) = y)
    (hker : ∀ z : ↥(Z k G M), ThetaOn k G M z = 0 → (z : G →₀ M) ∈ B k G M) :
    Function.Injective (ThetaQ (k:=k) (G:=G) (M:=M) hbnd) := by
  have key : ∀ w : ↥(Z k G M) ⧸ (Bz k G M).toAddSubgroup,
      ThetaQ (k:=k) (G:=G) (M:=M) hbnd w = 0 → w = 0 := by
    intro w
    refine QuotientAddGroup.induction_on w (fun z hw => ?_)
    rw [ThetaQ_apply] at hw
    have hzI : ((ThetaOn k G M z : K (G:=G) (M:=M)) : A (G:=G) (M:=M))
        ∈ Work.Tate.augmentation G (A (G:=G) (M:=M)) :=
      (QuotientAddGroup.eq_zero_iff (ThetaOn k G M z)).mp hw
    obtain ⟨b, hbB, hbEq⟩ := hle _ hzI
    have hbEqK : ThetaOn k G M b = ThetaOn k G M z := Subtype.ext hbEq
    have hsub : ThetaOn k G M (b - z) = 0 := by
      rw [map_sub, hbEqK, sub_self]
    have hB : ((b - z : ↥(Z k G M)) : G →₀ M) ∈ B k G M := hker _ hsub
    have hzB : (z : G →₀ M) ∈ B k G M := by
      have h3 : (z : G →₀ M) = (b : G →₀ M) - ((b - z : ↥(Z k G M)) : G →₀ M) := by
        simp
      rw [h3]
      exact (B k G M).sub_mem hbB hB
    exact (QuotientAddGroup.eq_zero_iff z).mpr ((mem_Bz (k:=k)).mpr hzB)
  intro x y hxy
  have h0 : ThetaQ (k:=k) (G:=G) (M:=M) hbnd (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have := key _ h0
  rwa [sub_eq_zero] at this

/-! ## The assembly: `H₁(G,M) ≅ Ĥ⁻¹(G, M^♯)` -/

theorem H1pi_surjective : Function.Surjective (groupHomology.H1π (repM k G M)).hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The canonical linear isomorphism `Z₁/B₁ ≅ H₁(G,M)`. -/
noncomputable def quotEquivH1 :
    (↥(Z k G M) ⧸ (Bz k G M)) ≃ₗ[k] groupHomology.H1 (repM k G M) :=
  LinearMap.quotKerEquivOfSurjective _ (H1pi_surjective (k:=k) (G:=G) (M:=M))

@[simp] theorem quotEquivH1_mk (x : ↥(Z k G M)) :
    quotEquivH1 (k:=k) (G:=G) (M:=M) (Submodule.Quotient.mk x)
      = (groupHomology.H1π (repM k G M)).hom x := by
  rw [quotEquivH1, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- **The degree shift** `H₁(G,M) ≅ Ĥ⁻¹(G, M^♯)`, as an additive equivalence. -/
noncomputable def h1Hm1Equiv
    (hbnd : ∀ b : ↥(Z k G M), (b : G →₀ M) ∈ B k G M →
      ((ThetaOn k G M b : K (G:=G) (M:=M)) : A (G:=G) (M:=M))
        ∈ Work.Tate.augmentation G (A (G:=G) (M:=M)))
    (hle : ∀ y : A (G:=G) (M:=M), y ∈ Work.Tate.augmentation G (A (G:=G) (M:=M)) →
      ∃ b : ↥(Z k G M), (b : G →₀ M) ∈ B k G M ∧
        ((ThetaOn k G M b : K (G:=G) (M:=M)) : A (G:=G) (M:=M)) = y)
    (hker : ∀ z : ↥(Z k G M), ThetaOn k G M z = 0 → (z : G →₀ M) ∈ B k G M)
    (hsu : Function.Surjective (ThetaOn k G M)) :
    groupHomology.H1 (repM k G M) ≃+ Work.Tate.Hm1 G (A (G:=G) (M:=M)) :=
  ((quotEquivH1 (k:=k) (G:=G) (M:=M)).symm.toAddEquiv).trans
    (AddEquiv.ofBijective (ThetaQ (k:=k) (G:=G) (M:=M) hbnd)
      ⟨ThetaQ_injective (k:=k) (G:=G) (M:=M) hbnd hle hker,
        ThetaQ_surjective (k:=k) (G:=G) (M:=M) hbnd hsu⟩)



variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {k : Type} [CommRing k]
variable {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
variable {N : Type} [AddCommGroup N] [Module k N] [DistribMulAction G N] [SMulCommClass G k N]

/-- The representation morphism induced by an equivariant linear map. -/
noncomputable def repMor (f : M →ₗ[k] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    repM k G M ⟶ repM k G N :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (Representation.ofDistribMulAction k G M) (Representation.ofDistribMulAction k G N) f hf)

theorem repMor_hom (f : M →ₗ[k] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    (repMor (k:=k) (G:=G) f hf).hom.toLinearMap = f :=
  LinearMap.ext (fun m => rfl)

theorem chainsMap₁_id (φ : repM k G M ⟶ repM k G N) :
    groupHomology.chainsMap₁ (MonoidHom.id G) φ
      = ModuleCat.ofHom (Finsupp.mapRange.linearMap (φ.hom.toLinearMap)) := by
  rw [groupHomology.chainsMap₁]
  rw [show (⇑(MonoidHom.id G) : G → G) = id from rfl]
  rw [Finsupp.lmapDomain_id, LinearMap.comp_id]

/-- The induced map on 1-cycles. -/
noncomputable def mapZ (f : M →ₗ[k] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    ↥(Z k G M) →ₗ[k] ↥(Z k G N) :=
  (groupHomology.mapCycles₁ (k := k) (G := G) (H := G) (A := repM k G M) (B := repM k G N)
    (MonoidHom.id G) (repMor (k:=k) (G:=G) f hf)).hom

theorem mapZ_coe (f : M →ₗ[k] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (x : ↥(Z k G M)) :
    ((mapZ (k:=k) (G:=G) f hf x : ↥(Z k G N)) : G →₀ N)
      = Finsupp.mapRange (⇑f) (map_zero f) (x : G →₀ M) := by
  rw [mapZ, groupHomology.coe_mapCycles₁, chainsMap₁_id]
  change (Finsupp.mapRange.linearMap
      (Rep.Hom.hom (repMor (k:=k) (G:=G) f hf)).toLinearMap)
      (x : G →₀ M) = Finsupp.mapRange (⇑f) (map_zero f) (x : G →₀ M)
  rw [Finsupp.mapRange.linearMap_apply]
  rfl


theorem coeffSum_mapRange (f : M →ₗ[k] N) (x : G →₀ M) :
    coeffSum (Finsupp.mapRange (⇑f) (map_zero f) x) = f (coeffSum x) := by
  rw [coeffSum_eq_sum, coeffSum_eq_sum, map_sum]
  exact Finset.sum_congr rfl (fun g _ => Finsupp.mapRange_apply ..)

theorem d1_map (f : M →ₗ[k] N) (c : M) :
    d1 (G:=G) (f c) = fun g => f (d1 (G:=G) c g) := by
  funext g; by_cases h : g = 1 <;> simp [d1, h]

/-- Chain-level naturality of the degree shift. -/
theorem ThetaOn_mapZ (f : M →ₗ[k] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (x : ↥(Z k G M)) :
    ((ThetaOn k G N (mapZ (k:=k) (G:=G) f hf x)
        : K (G:=G) (M:=N)) : A (G:=G) (M:=N))
      = Work.Tate.coindUpMap f.toAddMonoidHom hf
          ((ThetaOn k G M x : K (G:=G) (M:=M)) : A (G:=G) (M:=M)) := by
  apply Subtype.ext
  funext g
  show thetaFun (G:=G) ((mapZ (k:=k) (G:=G) f hf x : ↥(Z k G N)) : G →₀ N) g
      = f ((((ThetaOn k G M x : K (G:=G) (M:=M)) : A (G:=G) (M:=M)) : G → M) g)
  have hz := mapZ_coe (k:=k) (G:=G) f hf x
  rw [thetaFun_apply, hz]
  simp only [Finsupp.mapRange_apply, coeffSum_eq_sum]
  have hsum : (∑ g : G, f (((x : ↥(Z k G M)) : G →₀ M) g))
      = f (coeffSum ((x : ↥(Z k G M)) : G →₀ M)) := by
    rw [coeffSum_eq_sum, ← map_sum]
  rw [hsum]
  rw [ThetaOn_coe, thetaFun_apply, map_sub]
  congr 1
  exact (congrFun (d1_map (k:=k) (G:=G) f (coeffSum ((x : ↥(Z k G M)) : G →₀ M))) g)


theorem h1Hm1Equiv_apply_mk (hbnd) (hle) (hker) (hsu) (z : ↥(Z k G M)) :
    h1Hm1Equiv (k:=k) (G:=G) (M:=M) hbnd hle hker hsu
        ((groupHomology.H1π (repM k G M)).hom z)
      = QuotientAddGroup.mk (ThetaOn k G M z) := by
  have hmem : (Submodule.Quotient.mk z : ↥(Z k G M) ⧸ Bz k G M)
      = (QuotientAddGroup.mk z : ↥(Z k G M) ⧸ (Bz k G M).toAddSubgroup) := rfl
  have hq : (quotEquivH1 (k:=k) (G:=G) (M:=M)).symm
      ((groupHomology.H1π (repM k G M)).hom z) = Submodule.Quotient.mk z := by
    rw [← quotEquivH1_mk (k:=k) (G:=G) (M:=M) z, LinearEquiv.symm_apply_apply]
  change ThetaQ (k:=k) (G:=G) (M:=M) hbnd
      ((quotEquivH1 (k:=k) (G:=G) (M:=M)).symm ((groupHomology.H1π (repM k G M)).hom z))
    = QuotientAddGroup.mk (ThetaOn k G M z)
  rw [hq]
  exact ThetaQ_apply (k:=k) (G:=G) (M:=M) hbnd z


theorem h1Hm1Equiv_apply_mk' (hbnd) (hle) (hker) (hsu) (z : ↥(Z k G M)) :
    h1Hm1Equiv (k:=k) (G:=G) (M:=M) hbnd hle hker hsu
        ((groupHomology.H1π (repM k G M)).hom z)
      = Work.Tate.Hm1π G (A (G:=G) (M:=M)) (ThetaOn k G M z) := by
  rw [h1Hm1Equiv_apply_mk (k:=k) (G:=G) (M:=M) hbnd hle hker hsu z]
  rfl

theorem h1Hm1Equiv_H1pi (hbnd) (hle) (hker) (hsu)
    (hbndN : ∀ b : ↥(Z k G N), (b : G →₀ N) ∈ B k G N →
      ((ThetaOn k G N b : K (G:=G) (M:=N)) : A (G:=G) (M:=N))
        ∈ Work.Tate.augmentation G (A (G:=G) (M:=N)))
    (hleN : ∀ y : A (G:=G) (M:=N), y ∈ Work.Tate.augmentation G (A (G:=G) (M:=N)) →
      ∃ b : ↥(Z k G N), (b : G →₀ N) ∈ B k G N ∧
        ((ThetaOn k G N b : K (G:=G) (M:=N)) : A (G:=G) (M:=N)) = y)
    (hkerN : ∀ z : ↥(Z k G N), ThetaOn k G N z = 0 → (z : G →₀ N) ∈ B k G N)
    (hsuN : Function.Surjective (ThetaOn k G N))
    (f : M →ₗ[k] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (z : ↥(Z k G M)) :
    Work.Tate.Hm1Map G (A (G:=G) (M:=M)) (A (G:=G) (M:=N))
        (Work.Tate.coindUpMap f.toAddMonoidHom hf)
        (Work.Tate.coindUpMap_equiv f.toAddMonoidHom hf)
        (h1Hm1Equiv (k:=k) (G:=G) (M:=M) hbnd hle hker hsu
          ((groupHomology.H1π (repM k G M)).hom z))
      = h1Hm1Equiv (k:=k) (G:=G) (M:=N) hbndN hleN hkerN hsuN
          ((groupHomology.map (MonoidHom.id G) (repMor (k:=k) (G:=G) f hf) 1).hom
            ((groupHomology.H1π (repM k G M)).hom z)) := by
  have hmap : (groupHomology.map (MonoidHom.id G) (repMor (k:=k) (G:=G) f hf) 1).hom
        ((groupHomology.H1π (repM k G M)).hom z)
      = (groupHomology.H1π (repM k G N)).hom (mapZ (k:=k) (G:=G) f hf z) := by
    simpa [mapZ] using
      groupHomology.H1π_comp_map_apply (k := k) (G := G) (H := G)
        (A := repM k G M) (B := repM k G N)
        (MonoidHom.id G) (repMor (k:=k) (G:=G) f hf) z
  rw [h1Hm1Equiv_apply_mk' (k:=k) (G:=G) (M:=M) hbnd hle hker hsu z, hmap,
    h1Hm1Equiv_apply_mk' (k:=k) (G:=G) (M:=N) hbndN hleN hkerN hsuN
      (mapZ (k:=k) (G:=G) f hf z)]
  rw [Work.Tate.Hm1Map_Hm1π]
  congr 1
  apply Subtype.ext
  rw [Work.Tate.mapKer_apply]
  exact (ThetaOn_mapZ (k:=k) (G:=G) f hf z).symm

/-- Naturality of the degree-shift equivalence in the coefficient module. -/
theorem h1Hm1Equiv_natural (hbnd) (hle) (hker) (hsu)
    (hbndN : ∀ b : ↥(Z k G N), (b : G →₀ N) ∈ B k G N →
      ((ThetaOn k G N b : K (G:=G) (M:=N)) : A (G:=G) (M:=N))
        ∈ Work.Tate.augmentation G (A (G:=G) (M:=N)))
    (hleN : ∀ y : A (G:=G) (M:=N), y ∈ Work.Tate.augmentation G (A (G:=G) (M:=N)) →
      ∃ b : ↥(Z k G N), (b : G →₀ N) ∈ B k G N ∧
        ((ThetaOn k G N b : K (G:=G) (M:=N)) : A (G:=G) (M:=N)) = y)
    (hkerN : ∀ z : ↥(Z k G N), ThetaOn k G N z = 0 → (z : G →₀ N) ∈ B k G N)
    (hsuN : Function.Surjective (ThetaOn k G N))
    (f : M →ₗ[k] N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (x : groupHomology.H1 (repM k G M)) :
    Work.Tate.Hm1Map G (A (G:=G) (M:=M)) (A (G:=G) (M:=N))
        (Work.Tate.coindUpMap f.toAddMonoidHom hf)
        (Work.Tate.coindUpMap_equiv f.toAddMonoidHom hf)
        (h1Hm1Equiv (k:=k) (G:=G) (M:=M) hbnd hle hker hsu x)
      = h1Hm1Equiv (k:=k) (G:=G) (M:=N) hbndN hleN hkerN hsuN
          ((groupHomology.map (MonoidHom.id G) (repMor (k:=k) (G:=G) f hf) 1).hom x) :=
  groupHomology.H1_induction_on x (fun z =>
    h1Hm1Equiv_H1pi (k:=k) (G:=G) hbnd hle hker hsu hbndN hleN hkerN hsuN f hf z)


end Work.Bridge
