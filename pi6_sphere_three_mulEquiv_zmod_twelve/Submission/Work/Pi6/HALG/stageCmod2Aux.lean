import Mathlib
import Submission.Work.Pi6.HALG.defs
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# HALG: cardinality bookkeeping for the mod-2 Bockstein analysis of the killing tower

Helpers used by `Work.Pi6.HALG.stageCmod2` (area HALG, step 5):

* `card_eq_mul_card_of_exact` — an unconditional `Nat.card`-form of "`|B| = |A| · |C|`" for a short
  exact sequence `A → B → C` of abelian groups (Lagrange's theorem; no finiteness hypotheses, since
  `Nat.card` of an infinite type is `0` and the identity still holds);
* `bocksteinCard_of_cards` — the `BocksteinTwo` short exact sequence
  `0 → H_{n+1}(X;ℤ)/2 → H_{n+1}(X;𝔽₂) → H_n(X;ℤ)[2] → 0` turned into a cardinality identity
  `|H_{n+1}(X;𝔽₂)| = |H_{n+1}(X;ℤ)/2| · |H_n(X;ℤ)[2]|`;
* `subsingleton_of_natCard_eq_one` — a one-element type is a subsingleton;
* `exists_hom_apply_ne_zero` — a nonzero morphism of `R`-modules takes a nonzero value;
* `natCard_eq_two_of_linearEquiv_zmodTwo` — transport of `Nat.card = 2` along a linear equivalence;
* `card_two_surjective_of_ne_zero` — a nonzero homomorphism between groups of cardinality `2` is
  surjective.

The remaining lemmas concern the two group-theoretic inputs of the assembly:

* `mulTwo_hom_apply_add_self`, `range_mulTwo_toAddSubgroup_eq_nsmul_range` — `mulTwo M` is
  `x ↦ x + x`, so its range is the subgroup `2M`;
* `card_quot_twoRange_of_card_six`, `card_twoCok_of_card_six` — an abelian group of order `6` has
  `|G/2G| = 2`.

`Work.Pi6.HALG.stageCmod2` imports the sibling modules
`Submission.Work.Pi6.HALG.twoCok_twoKer_card_two` (a group of cardinality `2` has `|M/2M| = 2` and
`|M[2]| = 2`) and `Submission.Work.Pi6.HALG.twoCok_twoKer_card_one` (a trivial group) directly; the
two lemmas of the last group above are kept here because their modules were not ready in time.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.HALG

noncomputable section

/-- **Cardinality of a short exact sequence of abelian groups.**  If `A --f--> B --g--> C` is exact
with `f` injective and `g` surjective, then `Nat.card B = Nat.card A * Nat.card C`.  (Unconditional:
`Nat.card` of an infinite type is `0`, and the identity holds in that degenerate case too, by
Lagrange's theorem.  The same statement is `Work.Pi6.EMZ.natCard_of_exact`; it is repeated here to
keep the HALG dependency surface at Mathlib.) -/
theorem card_eq_mul_card_of_exact {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Nat.card B = Nat.card A * Nat.card C := by
  have hker : f.range = g.ker := (Function.Exact.addMonoidHom_ker_eq hex).symm
  have h1 : Nat.card B = Nat.card (B ⧸ f.range) * Nat.card (f.range : AddSubgroup B) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.range
  have h2 : Nat.card (B ⧸ f.range) = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv
  have h3 : Nat.card (f.range : AddSubgroup B) = Nat.card A :=
    (Nat.card_congr (AddEquiv.ofBijective f.rangeRestrict
      ⟨fun a b h => hf (by simpa using congrArg Subtype.val h),
        f.rangeRestrict_surjective⟩).toEquiv).symm
  rw [h1, h2, h3, mul_comm]

/-- **Cardinality form of the mod-2 Bockstein short exact sequence.**  If `H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ)`
has `a` elements and `H_n(X;ℤ)[2]` has `b` elements, then `H_{n+1}(X;𝔽₂)` has `a · b` elements. -/
theorem bocksteinCard_of_cards (hB2 : BocksteinTwo) {X : Type} [TopologicalSpace X] (n : ℕ)
    {a b : ℕ} (ha : Nat.card ↥(twoCok (HR ℤ X (n + 1))) = a)
    (hb : Nat.card ↥(twoKer (HR ℤ X n)) = b) :
    Nat.card ↥(HR (ZMod 2) X (n + 1)) = a * b := by
  obtain ⟨i, p, h⟩ := hB2
  obtain ⟨hinj, hex, hsurj⟩ := h X n
  have hcard := card_eq_mul_card_of_exact (i X n).toAddMonoidHom (p X n).toAddMonoidHom
    hinj hsurj hex
  rw [hcard, ha, hb]

/-- A type with `Nat.card` equal to `1` is a subsingleton. -/
theorem subsingleton_of_natCard_eq_one {α : Type*} (h : Nat.card α = 1) : Subsingleton α :=
  (Nat.card_eq_one_iff_unique.mp h).1

/-- A nonzero morphism of `R`-modules takes a nonzero value. -/
theorem exists_hom_apply_ne_zero {R : Type} [Ring R] {M N : ModuleCat R} (f : M ⟶ N)
    (hf : f ≠ 0) : ∃ x : ↥M, f.hom x ≠ 0 := by
  by_contra h
  have hzero : f.hom = 0 := LinearMap.ext fun x => by
    by_contra hx
    exact h ⟨x, hx⟩
  refine hf ?_
  rw [ModuleCat.hom_ext_iff, hzero, ModuleCat.hom_zero]

/-- Transport of `Nat.card = 2` along a linear equivalence with `ℤ/2`. -/
theorem natCard_eq_two_of_linearEquiv_zmodTwo {M : ModuleCat ℤ} (e : M ≃ₗ[ℤ] ZMod 2) :
    Nat.card ↥M = 2 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]


/-! ## An abelian group of order `6`: `|G/2G| = 2` -/

/-- Multiplication by `2` on `↥M` is `x ↦ x + x`. -/
theorem mulTwo_hom_apply_add_self (M : ModuleCat ℤ) (x : ↥M) : (mulTwo M).hom x = x + x := by
  show ((2 : ℤ) • 𝟙 M).hom x = x + x
  rw [show (2 : ℤ) • (𝟙 M : M ⟶ M) = 𝟙 M + 𝟙 M from two_zsmul _]
  simp

/-- The range of `mulTwo M` is the subgroup `2M` of twice-elements. -/
theorem range_mulTwo_toAddSubgroup_eq_nsmul_range (M : ModuleCat ℤ) :
    (LinearMap.range (mulTwo M).hom).toAddSubgroup
      = (nsmulAddMonoidHom (α := ↥M) 2).range := by
  ext x
  rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [nsmulAddMonoidHom_apply, two_nsmul, ← mulTwo_hom_apply_add_self]; exact hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [mulTwo_hom_apply_add_self, ← two_nsmul, ← nsmulAddMonoidHom_apply]; exact hy⟩

/-- **An abelian group of order `6` has `|G/2G| = 2`.** -/
theorem card_quot_twoRange_of_card_six {M : ModuleCat ℤ} (hM : Nat.card ↥M = 6) :
    Nat.card (↥M ⧸ (nsmulAddMonoidHom (α := ↥M) 2).range) = 2 := by
  haveI hfin : Finite ↥M := (Nat.card_pos_iff.mp (by rw [hM]; norm_num)).2
  set H : AddSubgroup ↥M := (nsmulAddMonoidHom (α := ↥M) 2).range with hH
  -- Lagrange: `|G| = |G ⧸ H| * |H|`
  have hlag : Nat.card (↥M ⧸ H) * Nat.card ↥H = 6 := by
    rw [← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H, hM]
  have hne0 : Nat.card (↥M ⧸ H) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hlag
    exact absurd hlag (by norm_num)
  haveI hfinQ : Finite (↥M ⧸ H) := (Nat.card_ne_zero.mp hne0).2
  -- every class is killed by `2`
  have h2 : ∀ y : ↥M ⧸ H, 2 • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H y
    rw [← map_nsmul (QuotientAddGroup.mk' H) 2 x, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff]
    exact AddMonoidHom.mem_range.mpr ⟨x, (nsmulAddMonoidHom_apply 2 x).symm⟩
  -- `3 ∤ |G ⧸ H|`
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hndvd3 : ¬ 3 ∣ Nat.card (↥M ⧸ H) := by
    intro h3dvd
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥M ⧸ H) 3 h3dvd
    have hd : addOrderOf y ∣ 2 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (h2 y)
    rw [hy] at hd
    exact absurd hd (by norm_num)
  -- `|G ⧸ H| ≠ 1`: an element of order `2` of `G` is not a double
  have hne1 : Nat.card (↥M ⧸ H) ≠ 1 := by
    intro h1
    haveI : Subsingleton (↥M ⧸ H) := (Nat.card_eq_one_iff_unique.mp h1).1
    obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card' (G := ↥M) 2 (by rw [hM]; norm_num)
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, addOrderOf_zero] at ha
      exact absurd ha (by norm_num)
    have h2a : 2 • a = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [ha])
    have hquota : (a : ↥M ⧸ H) ≠ 0 := by
      intro h0
      obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp ((QuotientAddGroup.eq_zero_iff a).mp h0)
      have hab : a = 2 • b := by rw [← hb, nsmulAddMonoidHom_apply]
      have h4 : 4 • b = 0 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul b 2 2, ← hab, h2a]
      have hdvd4 : addOrderOf b ∣ 4 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h4
      have hdvd6 : addOrderOf b ∣ 6 := by
        have h := addOrderOf_dvd_natCard b
        rwa [hM] at h
      have hdvd2 : addOrderOf b ∣ 2 := by
        have h := Nat.dvd_gcd hdvd4 hdvd6
        rwa [show Nat.gcd 4 6 = 2 from by norm_num] at h
      have hb2 : 2 • b = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd2
      exact ha0 (by rw [hab, hb2])
    exact hquota (Subsingleton.elim _ _)
  -- hence `|G ⧸ H| = 2`
  have hdvd : Nat.card (↥M ⧸ H) ∣ 6 := ⟨Nat.card ↥H, hlag.symm⟩
  have hcop : Nat.Coprime (Nat.card (↥M ⧸ H)) 3 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hndvd3)
  have hdvd23 : Nat.card (↥M ⧸ H) ∣ 2 * 3 := by
    rw [show (2 * 3 : ℕ) = 6 from rfl]
    exact hdvd
  have hdvd2 : Nat.card (↥M ⧸ H) ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd23
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact absurd h hne1
  · exact h

/-- **An abelian group of order `6` has `|M/2M| = 2`.** -/
theorem card_twoCok_of_card_six {M : ModuleCat ℤ} (hM : Nat.card ↥M = 6) :
    Nat.card ↥(twoCok M) = 2 := by
  have h : Nat.card (↥M ⧸ (nsmulAddMonoidHom (α := ↥M) 2).range) = 2 :=
    card_quot_twoRange_of_card_six hM
  rw [← range_mulTwo_toAddSubgroup_eq_nsmul_range M] at h
  exact h

/-- A nonzero homomorphism between (additive) groups of cardinality `2` is surjective.

`Nat.card_eq_two_iff'` exhibits the unique nonzero element `y` of `B`; a nonzero value `f a` of `f`
must be `y`, and every other element of `B` is `0` or `y`. -/
theorem card_two_surjective_of_ne_zero {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (_hA : Nat.card A = 2) (hB : Nat.card B = 2) (hf : ∃ a, f a ≠ 0) :
    Function.Surjective f := by
  obtain ⟨y, _hy, hyu⟩ := (Nat.card_eq_two_iff' (0 : B)).mp hB
  obtain ⟨a, ha⟩ := hf
  have hfa : f a = y := hyu (f a) ha
  intro b
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨0, map_zero f⟩
  · exact ⟨a, by rw [hfa, hyu b hb]⟩

end

end Work.Pi6.HALG
