import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_center
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ZassenhausPSL2.ZData.field_coordinates_of_regular
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The two-point stabiliser `D = H ∩ Hᵗ` is cyclic (L2 of the Zassenhaus–Suzuki design)

In a Zassenhaus split rank-one configuration whose root group `Q` is a Suzuki 2-group
(Higman's sense), the two-point stabiliser `D = twoPoint H t` is cyclic.

The argument is Suzuki 1962, Prop. 3 (`REFS/vision/suzuki1962`), in the Zassenhaus case
`V = C_D(t) = 1`, where `K = J(D,t) = D`:

* `t` inverts every element of `D` (`twoPoint_inverted`), so `D` is abelian — the elementary
  argument: inversion is an anti-automorphism, so `a b = b a`;
* `D` acts on the elementary abelian `2`-group `Z(Q) = Ω₁(Q) = Q₀` (Higman's hypothesis
  `hHig` gives `z ∈ Z(Q) ↔ z ^ 2 = 1`) by conjugation, and it does so *fixed point freely*
  (Zassenhaus: `dStab_fpf_on_Q`);
* `|D| = |Z(Q)| - 1` (the cardinality half of L2, `twoPoint_card_add_one_eq_center_card`,
  via `|D| = #Inv(Q)` of Suzuki Prop. 3);
* an abelian group acting fixed-point-freely on an elementary abelian `2`-group of order
  `|D| + 1` is the multiplicative group of a finite field of characteristic two
  (`regular_coordinates_abstract`, Peterfalvi I App. V (a)), hence **cyclic** (Mathlib:
  `IsCyclic Rˣ` for a finite field `R`).

This is the cyclicity half of `twoPoint_cyclic` of `NOTES_LEAD_probe1630.md`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem twoPoint_cyclic_cyclic {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hHig : Submission.Blueprint.HigmanProp)
    (hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q) :
    IsCyclic ↥(Submission.Blueprint.twoPoint H t) := by
  classical
  let D : Subgroup G := Submission.Blueprint.twoPoint H t
  let Z : Subgroup G := Work.ThmF.centerOf Q
  -- `Q` is non-trivial
  have hQne : Q ≠ ⊥ := Work.ZassenhausPSL2.Feit.Q_ne_bot_of_split h
  -- the two-point stabiliser `D` is abelian, since `t` inverts it
  have hDcomm : ∀ a b : ↥D, a * b = b * a := by
    intro a b
    have hinv : ∀ d ∈ Submission.Blueprint.twoPoint H t, t * d * t⁻¹ = d⁻¹ :=
      twoPoint_inverted h hZ hQne h2
    have ha : t * (a : G) * t⁻¹ = (a : G)⁻¹ := hinv (a : G) a.2
    have hb : t * (b : G) * t⁻¹ = (b : G)⁻¹ := hinv (b : G) b.2
    have hab : t * ((a : G) * (b : G)) * t⁻¹ = ((a : G) * (b : G))⁻¹ :=
      hinv ((a : G) * (b : G)) ((twoPoint H t).mul_mem a.2 b.2)
    have h1 : ((a : G) * (b : G))⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ := by
      rw [← hab]
      rw [show t * ((a : G) * (b : G)) * t⁻¹
            = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) by group, ha, hb]
    have h3 : (a : G)⁻¹ * (b : G)⁻¹ = (b : G)⁻¹ * (a : G)⁻¹ :=
      h1.symm.trans (mul_inv_rev (a : G) (b : G))
    have h4 : (b : G) * (a : G) = (a : G) * (b : G) := by
      have := congrArg Inv.inv h3
      simpa [mul_inv_rev] using this
    exact Subtype.ext h4.symm
  -- `Z = Z(Q)` is an elementary abelian `2`-group
  have hZcomm : ∀ a b : ↥Z, a * b = b * a := by
    intro a b
    exact Subtype.ext ((Work.ThmF.mem_centerOf.mp a.2).2 (b : G) (Work.ThmF.mem_centerOf.mp b.2).1)
  letI : CommGroup ↥Z := { (inferInstance : Group ↥Z) with mul_comm := hZcomm }
  have hZsq : ∀ z : ↥Z, z * z = 1 := by
    intro z
    have hzQ : (z : G) ∈ Q := (Work.ThmF.mem_centerOf.mp z.2).1
    have hmem : (⟨(z : G), hzQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Work.ThmF.mem_centerOf.mp z.2).2 (g : G) g.2).symm
    have h2' : (⟨(z : G), hzQ⟩ : ↥Q) ^ 2 = 1 := ((hHig ↥Q hSuz).1 _).mp hmem
    have h3' : (z : G) * (z : G) = 1 := by
      have := congrArg (fun w : ↥Q => (w : G)) h2'
      simpa [pow_two] using this
    exact Subtype.ext h3'
  have hchar : ∀ x : Additive ↥Z, x + x = 0 := by
    intro x
    rw [← toMul_eq_one, toMul_add]
    exact hZsq x.toMul
  -- `D` acts on `Z` by conjugation
  have hconj_mem : ∀ (d : ↥D), ∀ z : ↥Z, (d : G) * (z : G) * (d : G)⁻¹ ∈ Z := by
    intro d z
    have hdH : (d : G) ∈ H := (Subgroup.mem_inf.mp d.2).1
    have hdN : (d : G) ∈ Subgroup.normalizer (Q : Set G) := h.normal hdH
    have hdN' : (d : G)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hdN
    have hzQ : (z : G) ∈ Q := (Work.ThmF.mem_centerOf.mp z.2).1
    rw [Work.ThmF.mem_centerOf]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hdN (z : G)).mp hzQ, ?_⟩
    intro y hy
    have hw : (d : G)⁻¹ * y * (d : G) ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp hdN' y).mp hy
      simpa using this
    have hzc := (Work.ThmF.mem_centerOf.mp z.2).2 ((d : G)⁻¹ * y * (d : G)) hw
    calc (d : G) * (z : G) * (d : G)⁻¹ * y
        = (d : G) * ((z : G) * ((d : G)⁻¹ * y * (d : G))) * (d : G)⁻¹ := by group
      _ = (d : G) * (((d : G)⁻¹ * y * (d : G)) * (z : G)) * (d : G)⁻¹ := by rw [hzc]
      _ = y * ((d : G) * (z : G) * (d : G)⁻¹) := by group
  letI : SMul ↥D (Additive ↥Z) :=
    ⟨fun d x => Additive.ofMul (⟨(d : G) * ((Additive.toMul x : ↥Z) : G) * (d : G)⁻¹,
      hconj_mem d (Additive.toMul x)⟩ : ↥Z)⟩
  have hsmul_val : ∀ (d : ↥D) (x : Additive ↥Z),
      (((d • x).toMul : ↥Z) : G) = (d : G) * ((x.toMul : ↥Z) : G) * (d : G)⁻¹ := fun _ _ => rfl
  letI : MulAction ↥D (Additive ↥Z) :=
    { one_smul := by
        intro x
        apply Additive.ext
        apply Subtype.ext
        simp only [hsmul_val, Subgroup.coe_one]
        group
      mul_smul := by
        intro a b x
        apply Additive.ext
        apply Subtype.ext
        simp only [hsmul_val, Subgroup.coe_mul]
        group }
  have hsmul_add : ∀ (a : ↥D) (x y : Additive ↥Z), a • (x + y) = a • x + a • y := by
    intro a x y
    apply Additive.ext
    apply Subtype.ext
    simp only [hsmul_val, toMul_add, Subgroup.coe_mul]
    group
  -- `D` acts fixed point freely on `Z` (Zassenhaus)
  have hfpf : ∀ a : ↥D, a ≠ 1 → ∀ x : Additive ↥Z, a • x = x → x = 0 := by
    intro a ha x hx
    have hx' : (a • x).toMul = x.toMul := congrArg Additive.toMul hx
    have hconj : (a : G) * ((x.toMul : ↥Z) : G) * (a : G)⁻¹ = ((x.toMul : ↥Z) : G) := by
      have h := hsmul_val a x
      rw [hx'] at h
      exact h.symm
    have hxQ : ((x.toMul : ↥Z) : G) ∈ Q := (Work.ThmF.mem_centerOf.mp x.toMul.2).1
    have hfix := Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t h hZ (a : G) a.2
      (fun h1 => ha (Subtype.ext h1)) ((x.toMul : ↥Z) : G) hxQ hconj
    rw [← toMul_eq_one]
    exact Subtype.ext (by simpa using hfix)
  -- `|D| = |Z(Q)| - 1`
  have hcard : Nat.card ↥D = Nat.card (Additive ↥Z) - 1 := by
    have hZeq : Z = (Subgroup.center ↥Q).map Q.subtype := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxQ, hxc⟩ := Work.ThmF.mem_centerOf.mp hx
        exact Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩,
          Subgroup.mem_center_iff.mpr (fun g => Subtype.ext ((hxc (g : G) g.2).symm)), rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have hy' : ∀ g : ↥Q, g * y = y * g := Subgroup.mem_center_iff.mp hy
        refine Work.ThmF.mem_centerOf.mpr ⟨hyx ▸ y.2, fun z hz => ?_⟩
        have h1 : (z : G) * (y : G) = (y : G) * (z : G) := by
          simpa using congrArg Subtype.val (hy' ⟨z, hz⟩)
        rw [← hyx]
        exact h1.symm
    have hcardZ : Nat.card ↥Z = Nat.card ↥(Subgroup.center ↥Q) := by
      rw [hZeq, Subgroup.card_map_of_injective Q.subtype_injective]
    have hcenter : Nat.card ↥D + 1 = Nat.card ↥(Subgroup.center ↥Q) :=
      twoPoint_card_add_one_eq_center_card h hZ h2 hSuz
    have hAdd : Nat.card (Additive ↥Z) = Nat.card ↥Z := Nat.card_congr Additive.toMul
    have : Nat.card (Additive ↥Z) = Nat.card ↥D + 1 := by rw [hAdd, hcardZ, ← hcenter]
    omega
  -- an abelian group acting fixed point freely on `Z^#` of size `|D| + 1` is a field's units
  obtain ⟨n, _hn, e, φ, _he, _hphi⟩ :=
    Work.ZassenhausPSL2.ZData.regular_coordinates_abstract (V := Additive ↥Z) (A := ↥D)
      hDcomm hchar hsmul_add hfpf hcard
  haveI : IsCyclic ((GaloisField 2 n)ˣ) := inferInstance
  exact (MulEquiv.isCyclic φ).mpr inferInstance

end Work.ZassenhausSuzuki
