import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.NUV2.QuadFaithful2_Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

namespace NK.NUV2

open IsDedekindDomain

/-! ## The value set of a binary quadratic form `X² - a Y²`

For a field `F` and `a ∈ F` put `V_a = {u² - a v² : u, v ∈ F}`.  Two elementary structural facts
drive the argument below:

* `V_a ∩ Fˣ` is a **subgroup** of `Fˣ` (Brahmagupta's identity for the product, and the division
  formula `(u²-av²)⁻¹ = (u/Y)² - a (v/Y)²` with `Y = u²-av²`);
* **symmetry**: for `a, b ≠ 0`, `b ∈ V_a ↔ a ∈ V_b` (divide by `v²` when `v ≠ 0`; when `v = 0` one
  has `b = u²` and the explicit witnesses `X = u(1+a/b)/2`, `Y = (a/b-1)/2` work).

For a quadratic level `L = F(√a)` of `F` the norm group `N_{L/F} Lˣ` is exactly `V_a ∩ Fˣ`, since
the norm of `u + v√a` is `u² - a v²`.  The symmetry is therefore the symmetry of the quadratic
Hilbert pairing, and the norm index theorem `[Fˣ : N_{L/F}Lˣ] = [L : F]` — a *proved* theorem of
this workspace at completions — turns it into non-degeneracy:

* if `N(L₁) = N(L₂)` then the two characters `Fˣ → ℤ/2` agree, hence so do their value sets;
* taking `c = a₁a₂` and a square root `√c` inside `F^{ab}` (`NK.NUV2.LC.quadLevel`), the
  bilinearity `[b ∈ V_{a₁a₂}] = [b ∈ V_{a₁}]·[b ∈ V_{a₂}]` forces `V_c ⊇ Fˣ`, contradicting the
  norm index theorem for the quadratic level `F(√c)`.

This is the target `normGroup_quadratic_faithful_two`.
-/

section General

variable {F : Type*} [Field F]

/-- **The value set** of the binary quadratic form `X² - a Y²` over `F`. -/
def twoValueSet (a : F) : Set F := {y | ∃ u v : F, y = u ^ 2 - a * v ^ 2}

theorem twoValueSet.zero_mem (a : F) : (0 : F) ∈ twoValueSet a := ⟨0, 0, by ring⟩

/-- **Brahmagupta's identity**: the value set of `X² - a Y²` is closed under multiplication. -/
theorem twoValueSet.mul_aux {a u v u' v' : F} :
    (u ^ 2 - a * v ^ 2) * (u' ^ 2 - a * v' ^ 2) =
      (u * u' + a * v * v') ^ 2 - a * (u * v' + u' * v) ^ 2 := by
  ring

/-- **The value set, restricted to units, is a subgroup of `Fˣ`.** -/
noncomputable def twoValueSub (a : F) : Subgroup Fˣ where
  carrier := {y | (y : F) ∈ twoValueSet a}
  mul_mem' := by
    rintro y z ⟨u, v, huv⟩ ⟨u', v', huv'⟩
    refine ⟨u * u' + a * v * v', u * v' + u' * v, ?_⟩
    rw [Units.val_mul, huv, huv', twoValueSet.mul_aux]
  one_mem' := ⟨1, 0, by simp⟩
  inv_mem' := by
    rintro y ⟨u, v, huv⟩
    have hy : (y : F) ≠ 0 := Units.ne_zero y
    refine ⟨u / (y : F), v / (y : F), ?_⟩
    rw [Units.val_inv_eq_inv_val]
    field_simp
    rw [← huv]

theorem twoValueSub.mem_iff {a : F} {y : Fˣ} :
    y ∈ twoValueSub a ↔ (y : F) ∈ twoValueSet a := Iff.rfl

theorem twoValueSub.mem_of_units {a : F} {y : Fˣ} (h : y ∈ twoValueSub a) :
    (y : F) ∈ twoValueSet a := h

end General

section Symm

variable {F : Type*} [Field F]

/-- **Symmetry of the value set**, witness form. -/
theorem twoValueSet.comm_aux {a b u v : F} (h2 : (2 : F) ≠ 0) (hb : b ≠ 0)
    (h : b = u ^ 2 - a * v ^ 2) : a ∈ twoValueSet b := by
  by_cases hv : v = 0
  · subst hv
    have hbu : b = u ^ 2 := by simpa using h
    have hu : u ≠ 0 := by rintro rfl; exact hb (by simpa using hbu)
    refine ⟨u * (1 + a / b) / 2, (a / b - 1) / 2, ?_⟩
    rw [hbu]
    field_simp
    ring
  · refine ⟨u / v, 1 / v, ?_⟩
    rw [h]
    field_simp
    ring

/-- **Symmetry of the value set**: for `a, b ≠ 0`, `b ∈ V_a ↔ a ∈ V_b`. -/
theorem twoValueSet.comm {a b : F} (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    b ∈ twoValueSet a ↔ a ∈ twoValueSet b := by
  constructor
  · rintro ⟨u, v, huv⟩
    exact twoValueSet.comm_aux h2 hb huv
  · rintro ⟨u, v, huv⟩
    exact twoValueSet.comm_aux h2 ha huv

end Symm

section IndexTwo

variable {G : Type*} [Group G]

/-- **In a subgroup of index two, a product lies in the subgroup exactly when the two factors lie
on the same side.** -/
theorem mul_mem_iff_iff_of_index_eq_two {H : Subgroup G} [H.Normal] (hH : H.index = 2)
    (x y : G) : x * y ∈ H ↔ (x ∈ H ↔ y ∈ H) := by
  have hcard : Nat.card (G ⧸ H) = 2 := by rw [← Subgroup.index_eq_card]; exact hH
  haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard2 : Nat.card (G ⧸ H) ≤ 2 := le_of_eq hcard
  constructor
  · intro hxy
    refine ⟨fun hx => ?_, fun hy => ?_⟩
    · have h : y = x⁻¹ * (x * y) := by rw [inv_mul_cancel_left]
      rw [h]; exact H.mul_mem (H.inv_mem hx) hxy
    · have h : x = (x * y) * y⁻¹ := by rw [mul_inv_cancel_right]
      rw [h]; exact H.mul_mem hxy (H.inv_mem hy)
  · intro h
    by_cases hx : x ∈ H
    · exact H.mul_mem hx (h.mp hx)
    · have hy : y ∉ H := fun hy => hx (h.mpr hy)
      have hxq : QuotientGroup.mk' H x ≠ 1 := fun h1 =>
        hx ((QuotientGroup.eq_one_iff x).mp (by rwa [QuotientGroup.mk'_apply] at h1))
      have hyq : QuotientGroup.mk' H y ≠ 1 := fun h1 =>
        hy ((QuotientGroup.eq_one_iff y).mp (by rwa [QuotientGroup.mk'_apply] at h1))
      have heq : QuotientGroup.mk' H x = QuotientGroup.mk' H y :=
        NK.NUV2.LC.eq_of_ne_one_of_card_le_two hcard2 hxq hyq
      have h1 : QuotientGroup.mk' H (x * y) = 1 := by
        rw [map_mul, heq]
        exact NK.NUV2.LC.mul_self_eq_one_of_card_le_two hcard2 (QuotientGroup.mk' H y)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

end IndexTwo

section Quad

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **Every element of a quadratic extension `L = F(x)`, with `x² = a ∈ F`, is `u + v x`.** -/
theorem quad_exists_eq_algebraMap_add_mul {L : IntermediateField F E} [FiniteDimensional F ↥L]
    (h : Module.finrank F ↥L = 2) {x : ↥L} {a : F}
    (hx : x ∉ Set.range (algebraMap F ↥L)) (hsq : x ^ 2 = algebraMap F ↥L a) (z : ↥L) :
    ∃ u v : F, z = algebraMap F ↥L u + algebraMap F ↥L v * x := by
  have hli : LinearIndependent F ![1, x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hst' : algebraMap F ↥L s + algebraMap F ↥L t * x = 0 := by
      simpa [Algebra.smul_def] using hst
    by_cases ht : t = 0
    · subst ht
      rw [map_zero, zero_mul, add_zero] at hst'
      exact ⟨(algebraMap F ↥L).injective (by rw [hst', map_zero]), rfl⟩
    · exfalso
      apply hx
      have ht' : (algebraMap F ↥L) t ≠ 0 := by simpa using ht
      have hkey : x = -((algebraMap F ↥L t)⁻¹ * algebraMap F ↥L s) := by
        have h1 : (algebraMap F ↥L t)⁻¹ * (algebraMap F ↥L s + algebraMap F ↥L t * x) = 0 := by
          rw [hst', mul_zero]
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ht', one_mul] at h1
        calc x = ((algebraMap F ↥L t)⁻¹ * algebraMap F ↥L s + x) -
              (algebraMap F ↥L t)⁻¹ * algebraMap F ↥L s := by ring
          _ = 0 - (algebraMap F ↥L t)⁻¹ * algebraMap F ↥L s := by rw [h1]
          _ = -((algebraMap F ↥L t)⁻¹ * algebraMap F ↥L s) := by ring
      refine ⟨-(s / t), ?_⟩
      rw [hkey, ← map_inv₀, ← map_mul, ← map_neg]
      congr 1
      rw [div_eq_mul_inv, mul_comm]
  have hrange : (Set.range ![1, x] : Set ↥L) = {1, x} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hfr : Module.finrank F ↥(Submodule.span F (Set.range ![1, x])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have hspan : Submodule.span F ({1, x} : Set ↥L) = ⊤ := by
    rw [← hrange]
    exact Submodule.eq_top_of_finrank_eq (by rw [hfr, h])
  have hz : z ∈ Submodule.span F ({1, x} : Set ↥L) := by rw [hspan]; trivial
  obtain ⟨u, v, huv⟩ := (Submodule.mem_span_pair).mp hz
  exact ⟨u, v, by rw [← huv]; simp [Algebra.smul_def]⟩

/-- **The norm group of a quadratic extension is the value set of its norm form**:
`y ∈ N_{L/F} Lˣ` iff `y = u² - a v²` for some `u, v ∈ F`. -/
theorem quad_mem_normGroup_iff_valueSet {L : IntermediateField F E} [FiniteDimensional F ↥L]
    [IsGalois F ↥L] (h : Module.finrank F ↥L = 2) {x : ↥L} {a : F}
    (hx : x ∉ Set.range (algebraMap F ↥L)) (hsq : x ^ 2 = algebraMap F ↥L a) (y : Fˣ) :
    y ∈ NK.LocalReciprocity.normGroup F ↥L ↔ (y : F) ∈ twoValueSet a := by
  constructor
  · intro hy
    rw [NK.LocalReciprocity.mem_normGroup_iff] at hy
    obtain ⟨t, ht⟩ := hy
    obtain ⟨u, v, huv⟩ := quad_exists_eq_algebraMap_add_mul h hx hsq (t : ↥L)
    exact ⟨u, v, by
      rw [← ht, huv]
      exact NK.NUV2.QuadFaithful.norm_algebraMap_add_mul (F := F) (E := ↥L) h hx hsq u v⟩
  · rintro ⟨u, v, huv⟩
    rw [NK.LocalReciprocity.mem_normGroup_iff]
    have hnorm : Algebra.norm F (algebraMap F ↥L u + algebraMap F ↥L v * x) = u ^ 2 - a * v ^ 2 :=
      NK.NUV2.QuadFaithful.norm_algebraMap_add_mul (F := F) (E := ↥L) h hx hsq u v
    have hz : algebraMap F ↥L u + algebraMap F ↥L v * x ≠ 0 := by
      intro h0
      have h1 : Algebra.norm F (algebraMap F ↥L u + algebraMap F ↥L v * x) = 0 := by
        rw [h0, Algebra.norm_zero]
      rw [hnorm] at h1
      exact (Units.ne_zero y) (by rw [← huv] at h1; exact h1)
    refine ⟨Units.mk0 _ hz, ?_⟩
    rw [Units.val_mk0, hnorm, huv]

end Quad

/-
## The assembly

The lemmas proved above reduce the target to two facts, both of which are available in the
workspace:

* `NK.NUV2.eq_qLevel_of_gen` — a quadratic level `L ≤ F^{ab}` generated by `x` with
  `x² = a` for `a ∈ Fˣ` is the *canonical* level `F(√a) = NK.NUV2.qLevel Q a`;
* `NK.NUV2.qNorm_injective` — the norm group of the canonical level determines the square class
  of its generator: `N(F(√a)) = N(F(√b))` forces `a/b ∈ (Fˣ)²`.

Both rest on the description of the norm group as the value set of the norm form
(`NK.NUV2.quad_mem_normGroup_iff_valueSet` above, and `NK.NUV2.mem_qNorm_iff`), the symmetry
`twoValueSet.comm` of that value set, and the norm index theorem
(`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`), which makes the quadratic
norm-group correspondence non-degenerate.  The two-level version is
`NK.NUV2.normGroup_quadratic_injective`.

The target is therefore immediate: two distinct quadratic levels have distinct norm groups.
-/


/-- **The residue-characteristic-`2` case of the minimal Hasse Normensatz case.**

For `F = Q.adicCompletion K` a `2`-adic field (`2` not a unit of the ring of integers), two
distinct quadratic levels of `F^{ab}/F` have distinct norm groups.

The norm group of a quadratic level `L = F(√a)` is the value set `V_a ∩ Fˣ` of the norm form
(`quad_mem_normGroup_iff_valueSet`), the pairing `(a,b) ↦ [b ∈ V_a]` is symmetric
(`twoValueSet.comm`), and the norm index theorem
(`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`) makes it non-degenerate:
the general injectivity statement is `NK.NUV2.normGroup_quadratic_injective`, and the target
follows from it by contraposition.

The hypothesis `h2` (that `2` is not a unit of the ring of integers) selects the
residue-characteristic-`2` case of the statement; the argument below does not need it, and in fact
proves the statement at *every* finite place. -/
theorem normGroup_quadratic_faithful_two {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h2 : ¬ IsUnit (2 : Q.adicCompletionIntegers K))
    (L₁ L₂ : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) ↥L₁] [Normal (Q.adicCompletion K) ↥L₁]
    [FiniteDimensional (Q.adicCompletion K) ↥L₂] [Normal (Q.adicCompletion K) ↥L₂]
    (h₁ : Module.finrank (Q.adicCompletion K) ↥L₁ = 2)
    (h₂' : Module.finrank (Q.adicCompletion K) ↥L₂ = 2)
    (hne : L₁ ≠ L₂) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁
      ≠ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ := by
  intro h
  exact hne (NK.NUV2.normGroup_quadratic_injective Q h₁ h₂' h)

/-- **The same statement with the residue-characteristic hypothesis removed.**

The proof of `normGroup_quadratic_faithful_two` never uses `h2`: the norm index theorem
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion` holds at *every* finite place
of a number field, and the symmetry of the norm form is uniform in the residue characteristic.
Consequently distinct quadratic levels have distinct norm groups at every finite place, with no
hypothesis on `2`.

This is the statement needed by `NK.Summary.NUV2.normGroup_quadratic_faithful`, which carries no
`h2`: `exact NK.NUV2.normGroup_quadratic_faithful_anyPlace Q L₁ L₂ h₁ h₂ hne`. -/
theorem normGroup_quadratic_faithful_anyPlace {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L₁ L₂ : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) ↥L₁] [Normal (Q.adicCompletion K) ↥L₁]
    [FiniteDimensional (Q.adicCompletion K) ↥L₂] [Normal (Q.adicCompletion K) ↥L₂]
    (h₁ : Module.finrank (Q.adicCompletion K) ↥L₁ = 2)
    (h₂ : Module.finrank (Q.adicCompletion K) ↥L₂ = 2)
    (hne : L₁ ≠ L₂) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁
      ≠ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ := by
  intro h
  exact hne (NK.NUV2.normGroup_quadratic_injective Q h₁ h₂ h)
end NK.NUV2
