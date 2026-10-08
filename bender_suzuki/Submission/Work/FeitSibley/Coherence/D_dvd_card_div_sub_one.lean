import Mathlib
import Submission.Work.FeitSibley.GroupTheory.D_dvd_card_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|D| ∣ [B : A] - 1` for a pair `A ≤ B ≤ Q₁` of `H`-invariant subgroups

The group `D` acts by conjugation on `Q₁` (`Q₁ ⊴ H`), and this action is fixed point free away
from `1` (`h.D_fpf_Q1`).  Its restriction to the `D`-invariant subgroups `A ≤ B ≤ Q₁` is
fixed point free as well, hence so is the induced action on the coset space `B/A`: if a coset
`xA ∈ B/A` is fixed by `d ≠ 1` then `d x⁻¹ d⁻¹ x ∈ A`, and since `a ↦ d a⁻¹ d⁻¹ a` is an
*injective* self-map of the finite group `A` (injectivity is exactly the fixed-point-freeness),
`x ∈ A`, i.e. `xA = A`.  Thus the action of `D` on `B/A` has `|B/A|` fixed points for `1`,
and exactly one fixed point for every other `d ∈ D`.

Burnside's lemma (`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`) then reads
`|B/A| + (|D| - 1) = (#orbits) · |D|`, which rearranges to `|D| ∣ |B/A| - 1`.  Finally
`|B/A| = |B| / |A|` because `A ≤ B` (Lagrange, `Subgroup.index_eq_card_div`).

## Main results

* `conjQuotAct` — the conjugation action of `D` on the coset space `↥B ⧸ A.subgroupOf B`;
* `dvd_card_sub_one_of_fpf` — the abstract Burnside step (a group acting on a finite set with a
  distinguished fixed point `x₀` and no other fixed points for `d ≠ 1` has `|X| ≡ 1 mod |D|`);
* `mem_of_conj_inv_mul_mem` — the injectivity argument above;
* `D_dvd_card_div_sub_one` — the target: `|D| ∣ |B| / |A| - 1`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-! ## The conjugation action of `D` on the cosets of `A` in `B` -/

/-- Conjugation by `d` as a monoid homomorphism of a `d`-invariant subgroup `B`. -/
def conjSubHom (B : Subgroup G) (d : G)
    (hd : d ∈ Subgroup.normalizer (B : Set G)) : ↥B →* ↥B where
  toFun x := ⟨d * (x : G) * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd (x : G)).mp x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp only [Subgroup.coe_mul]; group

lemma conjSubHom_coe {B : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (B : Set G)) (x : ↥B) :
    ((conjSubHom B d hd x : ↥B) : G) = d * (x : G) * d⁻¹ := rfl

/-- Conjugation by `d` respects the coset relation modulo `A`: the relation on `↥B` defined by
`A.subgroupOf B` is preserved by the map `x ↦ d x d⁻¹`. -/
lemma leftRel_conj (D A B : Subgroup G)
    (hDA : D ≤ Subgroup.normalizer (A : Set G)) (hDB : D ≤ Subgroup.normalizer (B : Set G))
    (d : ↥D) {a b : ↥B} (hab : QuotientGroup.leftRel (A.subgroupOf B) a b) :
    QuotientGroup.leftRel (A.subgroupOf B) (conjSubHom B (d : G) (hDB d.2) a)
      (conjSubHom B (d : G) (hDB d.2) b) := by
  rw [QuotientGroup.leftRel_apply] at hab ⊢
  rw [Subgroup.mem_subgroupOf] at hab ⊢
  have h1 : (conjSubHom B (d : G) (hDB d.2) a)⁻¹ * conjSubHom B (d : G) (hDB d.2) b
      = conjSubHom B (d : G) (hDB d.2) (a⁻¹ * b) := by
    rw [map_mul, map_inv]
  rw [h1, conjSubHom_coe]
  exact (Subgroup.mem_normalizer_iff.mp (hDA d.2) ((a : G)⁻¹ * (b : G))).mp hab

/-- The conjugation action of `D` on the coset space `B/A` (the quotient type of `↥B` by
`A.subgroupOf B`).  The map is well defined because `D` normalises both `A` and `B`. -/
@[instance_reducible]
def conjQuotAct (D A B : Subgroup G)
    (hDA : D ≤ Subgroup.normalizer (A : Set G)) (hDB : D ≤ Subgroup.normalizer (B : Set G)) :
    MulAction ↥D (↥B ⧸ A.subgroupOf B) where
  smul d q := Quotient.map (fun x : ↥B => conjSubHom B (d : G) (hDB d.2) x)
    (fun a b hab => leftRel_conj D A B hDA hDB d hab) q
  one_smul q := by
    induction q using Quotient.inductionOn with
    | h x =>
      apply Quotient.sound
      show QuotientGroup.leftRel (A.subgroupOf B) (conjSubHom B (1 : G) (hDB (1:↥D).2) x) x
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      have h1 : conjSubHom B (1 : G) (hDB (1:↥D).2) x = x := by
        apply Subtype.ext
        show (1:G) * ↑x * (1:G)⁻¹ = ↑x
        group
      rw [h1, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel]
      exact A.one_mem
  mul_smul d e q := by
    induction q using Quotient.inductionOn with
    | h x =>
      apply Quotient.sound
      show QuotientGroup.leftRel (A.subgroupOf B)
        (conjSubHom B ((d * e : ↥D) : G) (hDB (d * e).2) x)
        (conjSubHom B (d : G) (hDB d.2) (conjSubHom B (e : G) (hDB e.2) x))
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      have h1 : conjSubHom B ((d * e : ↥D) : G) (hDB (d * e).2) x
          = conjSubHom B (d : G) (hDB d.2) (conjSubHom B (e : G) (hDB e.2) x) := by
        apply Subtype.ext
        show ((d:↥D):G) * ((e:↥D):G) * ↑x * (((d:↥D):G) * ((e:↥D):G))⁻¹
          = (d:G) * ((e:G) * ↑x * (e:G)⁻¹) * (d:G)⁻¹
        group
      rw [h1, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel]
      exact A.one_mem

/-- The action of `d` on the class of `x` is the class of `d x d⁻¹`. -/
lemma conjQuotAct_smul_mk (D A B : Subgroup G)
    (hDA : D ≤ Subgroup.normalizer (A : Set G)) (hDB : D ≤ Subgroup.normalizer (B : Set G))
    (d : ↥D) (x : ↥B) :
    (conjQuotAct D A B hDA hDB).smul d (QuotientGroup.mk x)
      = QuotientGroup.mk (conjSubHom B (d : G) (hDB d.2) x) := rfl

/-! ## The abstract Burnside step -/

/-- **Burnside's lemma, divisibility form.**  If a finite group `D` acts on a finite set `X`
with a point `x₀` fixed by all of `D` and no other fixed point for any `d ≠ 1`, then
`|D| ∣ |X| - 1`: the complement of `x₀` is a disjoint union of regular orbits. -/
theorem dvd_card_sub_one_of_fpf {D X : Type} [Group D] [Fintype D] [MulAction D X] [Fintype X]
    [∀ d : D, Fintype (MulAction.fixedBy X d)]
    [Fintype (Quotient (MulAction.orbitRel D X))]
    (x₀ : X) (hfix : ∀ d : D, d • x₀ = x₀)
    (huniq : ∀ d : D, d ≠ 1 → ∀ x : X, d • x = x → x = x₀) :
    Nat.card D ∣ Nat.card X - 1 := by
  -- `1` fixes everything.
  have hcard1 : Fintype.card (MulAction.fixedBy X (1 : D)) = Nat.card X := by
    have he : (MulAction.fixedBy X (1 : D)) ≃ X :=
      (Equiv.subtypeEquivRight (fun x => by rw [MulAction.mem_fixedBy]; simp)).trans
        (Equiv.Set.univ X)
    calc Fintype.card (MulAction.fixedBy X (1 : D)) = Fintype.card X := Fintype.card_congr he
      _ = Nat.card X := Nat.card_eq_fintype_card.symm
  -- Every nontrivial `d` fixes only `x₀`.
  have hcardne : ∀ d : D, d ≠ 1 → Fintype.card (MulAction.fixedBy X d) = 1 := by
    intro d hd
    rw [Fintype.card_eq_one_iff]
    have hx₀ : x₀ ∈ MulAction.fixedBy X d := by
      rw [MulAction.mem_fixedBy]; exact hfix d
    refine ⟨⟨x₀, hx₀⟩, fun y => ?_⟩
    exact Subtype.ext (huniq d hd y.1 (MulAction.mem_fixedBy.mp y.2))
  -- The sum of the numbers of fixed points.
  have hsum : (∑ d : D, Fintype.card (MulAction.fixedBy X d))
      = Nat.card X + (Nat.card D - 1) := by
    have h2 : (∑ d ∈ Finset.univ.erase (1 : D), Fintype.card (MulAction.fixedBy X d))
        = Nat.card D - 1 := by
      trans (∑ d ∈ Finset.univ.erase (1 : D), (1 : ℕ))
      · exact Finset.sum_congr rfl (fun d hd => hcardne d (Finset.mem_erase.mp hd).1)
      · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
          ← Nat.card_eq_fintype_card]
        simp
    rw [← Finset.add_sum_erase Finset.univ
      (fun d : D => Fintype.card (MulAction.fixedBy X d)) (Finset.mem_univ 1), hcard1, h2]
  -- Burnside's lemma.
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group D X
  have hmain : Nat.card X + (Nat.card D - 1)
      = Fintype.card (Quotient (MulAction.orbitRel D X)) * Nat.card D := by
    rw [← hsum, hB, Nat.card_eq_fintype_card]
  -- `|X| - 1 = (#orbits - 1) · |D|`.
  have hn : 1 ≤ Nat.card D := Nat.card_pos
  haveI : Nonempty X := ⟨x₀⟩
  have hx : 1 ≤ Nat.card X := Nat.card_pos
  have h1 : Nat.card X - 1
      = Fintype.card (Quotient (MulAction.orbitRel D X)) * Nat.card D - Nat.card D := by
    omega
  have h2 : Fintype.card (Quotient (MulAction.orbitRel D X)) * Nat.card D - Nat.card D
      = (Fintype.card (Quotient (MulAction.orbitRel D X)) - 1) * Nat.card D := by
    rw [Nat.sub_mul, one_mul]
  rw [h1, h2]
  exact dvd_mul_left _ _

/-! ## The key injectivity argument -/

/-- **Injectivity of `x ↦ d x⁻¹ d⁻¹ x`.**  If `D` acts fixed point freely on the invariant
subgroup `B`, then `x ↦ d x⁻¹ d⁻¹ x` (for `d ≠ 1`) is injective on `B`, and on the finite
`D`-invariant subgroup `A ≤ B` it is therefore a bijection; whence `d x⁻¹ d⁻¹ x ∈ A` forces
`x ∈ A`. -/
theorem mem_of_conj_inv_mul_mem {G : Type} [Group G] [Fintype G] (D A B : Subgroup G)
    (hAB : A ≤ B)
    (hDA : D ≤ Subgroup.normalizer (A : Set G)) (_hDB : D ≤ Subgroup.normalizer (B : Set G))
    (hfpf : ∀ d ∈ D, d ≠ 1 → ∀ x ∈ B, d * x * d⁻¹ = x → x = 1)
    {d : G} (hd : d ∈ D) (hd1 : d ≠ 1) {x : G} (hx : x ∈ B)
    (hxA : d * x⁻¹ * d⁻¹ * x ∈ A) : x ∈ A := by
  -- `c y = d * y⁻¹ * d⁻¹ * y` lies in `A` when `y ∈ A`.
  have hcA : ∀ y ∈ A, d * y⁻¹ * d⁻¹ * y ∈ A := by
    intro y hy
    have h1 : d * y⁻¹ * d⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hDA hd) (y⁻¹)).mp (A.inv_mem hy)
    exact A.mul_mem h1 hy
  -- `c` is injective on `B`.
  have hinj : ∀ y ∈ B, ∀ z ∈ B, d * y⁻¹ * d⁻¹ * y = d * z⁻¹ * d⁻¹ * z → y = z := by
    intro y hy z hz heq
    -- `c y = c z =: t` and `y = (d * y * d⁻¹) * t`, `z = (d * z * d⁻¹) * t`.
    have hfix : d * (y * z⁻¹) * d⁻¹ = y * z⁻¹ := by
      have hx : d * y * d⁻¹ = y * (d * y⁻¹ * d⁻¹ * y)⁻¹ := by group
      have hz' : d * z * d⁻¹ = z * (d * z⁻¹ * d⁻¹ * z)⁻¹ := by group
      calc d * (y * z⁻¹) * d⁻¹
          = (d * y * d⁻¹) * (d * z * d⁻¹)⁻¹ := by group
        _ = (y * (d * y⁻¹ * d⁻¹ * y)⁻¹) * (z * (d * z⁻¹ * d⁻¹ * z)⁻¹)⁻¹ := by
              rw [hx, hz']
        _ = y * z⁻¹ := by rw [heq]; group
    have hmem : y * z⁻¹ ∈ B := B.mul_mem hy (B.inv_mem hz)
    have h1 : y * z⁻¹ = 1 := hfpf d hd hd1 (y * z⁻¹) hmem hfix
    calc y = y * z⁻¹ * z := by group
      _ = z := by rw [h1, one_mul]
  -- the restriction of `c` to `A` is injective, hence (as `A` is finite) surjective
  have hkey : Function.Injective
      (fun y : ↥A => (⟨d * (y : G)⁻¹ * d⁻¹ * (y : G), hcA y y.2⟩ : ↥A)) := by
    intro y z hyz
    apply Subtype.ext
    exact hinj y (hAB y.2) z (hAB z.2) (Subtype.ext_iff.mp hyz)
  obtain ⟨a', ha'⟩ :=
    Finite.surjective_of_injective hkey (⟨d * x⁻¹ * d⁻¹ * x, hxA⟩ : ↥A)
  have ha'eq : d * (a' : G)⁻¹ * d⁻¹ * (a' : G) = d * x⁻¹ * d⁻¹ * x := by
    simpa using Subtype.ext_iff.mp ha'
  have hxa : x = (a' : G) := hinj x hx (a' : G) (hAB a'.2) ha'eq.symm
  rw [hxa]
  exact a'.2

/-! ## The main theorem -/

theorem D_dvd_card_div_sub_one {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (A B : Subgroup G) (hAB : A ≤ B) (hB : B ≤ h.Q1)
    (hAn : h.H ≤ Subgroup.normalizer (A : Set G)) (hBn : h.H ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card h.D ∣ Nat.card ↥B / Nat.card ↥A - 1 := by
  classical
  have hDA : h.D ≤ Subgroup.normalizer (A : Set G) := h.D_le_H.trans hAn
  have hDB : h.D ≤ Subgroup.normalizer (B : Set G) := h.D_le_H.trans hBn
  have hfpf : ∀ d ∈ h.D, d ≠ 1 → ∀ x ∈ B, d * x * d⁻¹ = x → x = 1 :=
    fun d hd hd1 x hx => h.D_fpf_Q1 d hd hd1 x (hB hx)
  let K : Subgroup ↥B := A.subgroupOf B
  letI : MulAction ↥h.D (↥B ⧸ K) := conjQuotAct h.D A B hDA hDB
  -- the trivial coset
  let x₀ : ↥B ⧸ K := QuotientGroup.mk (1 : ↥B)
  -- it is fixed by everything
  have hfix₀ : ∀ d : ↥h.D, d • x₀ = x₀ := by
    intro d
    show (conjQuotAct h.D A B hDA hDB).smul d (QuotientGroup.mk (1 : ↥B))
      = QuotientGroup.mk (1 : ↥B)
    rw [conjQuotAct_smul_mk]
    congr 1
    exact map_one _
  -- and it is the only fixed point of a nontrivial `d`
  have huniq : ∀ d : ↥h.D, d ≠ 1 → ∀ q : ↥B ⧸ K, d • q = q → q = x₀ := by
    intro d hd1 q hq
    induction q using Quotient.inductionOn with
    | h x =>
      have hq' : (QuotientGroup.mk (conjSubHom B ((d : ↥h.D) : G) (hDB d.2) x) : ↥B ⧸ K)
          = QuotientGroup.mk x := by
        rw [← conjQuotAct_smul_mk]
        exact hq
      have hrel : (conjSubHom B ((d : ↥h.D) : G) (hDB d.2) x)⁻¹ * x ∈ K :=
        QuotientGroup.eq.mp hq'
      rw [Subgroup.mem_subgroupOf] at hrel
      have hxA : ((d : ↥h.D) : G) * (x : G)⁻¹ * ((d : ↥h.D) : G)⁻¹ * (x : G) ∈ A := by
        have hcoeeq : ((d : ↥h.D) : G) * (x : G)⁻¹ * ((d : ↥h.D) : G)⁻¹ * (x : G)
            = (↑((conjSubHom B ((d : ↥h.D) : G) (hDB d.2) x)⁻¹ * x) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjSubHom_coe]
          group
        rw [hcoeeq]
        exact hrel
      have hxA' : (x : G) ∈ A :=
        mem_of_conj_inv_mul_mem h.D A B hAB hDA hDB hfpf d.2
          (fun h1 => hd1 (Subtype.ext h1)) x.2 hxA
      apply Quotient.sound
      show QuotientGroup.leftRel K x (1 : ↥B)
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      simpa using A.inv_mem_iff.mpr hxA'
  have hdvd := dvd_card_sub_one_of_fpf (D := ↥h.D) (X := ↥B ⧸ K) x₀ hfix₀ huniq
  -- `|B/A| = |B| / |A|`
  have hcard : Nat.card (↥B ⧸ K) = Nat.card ↥B / Nat.card ↥A := by
    have h1 : Nat.card (↥B ⧸ K) = K.index := rfl
    rw [h1, Subgroup.index_eq_card_div]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rwa [hcard] at hdvd

end Work.FeitSibley.Coherence
