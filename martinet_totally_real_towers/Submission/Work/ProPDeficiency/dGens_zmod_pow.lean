import Mathlib
import Submission.Work.ProPDeficiency.Basic

/-!
# The elementary abelian `p`-group of rank `n` has exactly `n` generators

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.dGens_zmod_pow`.

The group `E_n = Fin n → Multiplicative (ZMod p)` (`p` prime) is the elementary abelian `p`-group
of rank `n`, i.e. the `n`-fold product of copies of `𝔽_p` written multiplicatively.  We prove

`dGens (Fin n → Multiplicative (ZMod p)) = n`,

where `dGens` is the minimal cardinality of a finite generating set
(`Submission.Work.ProPDeficiency.Basic`).

* **Upper bound** `dGens E_n ≤ n`: the `n` coordinate elements `e_i` (which are `ofAdd 1` in
  coordinate `i` and `1` elsewhere) generate, because every `x` is the pointwise product
  `∏ i, (e_i) ^ (toAdd (x i)).val`.
* **Lower bound** `n ≤ dGens E_n`: for every generating *finset* `S` of `E_n`, the map
  `c ↦ (x ↦ ofAdd (∑ i, toAdd (x i) * toAdd (c i)))` from `Fin n → 𝔽_p` to the hom group
  `Hom(E_n, 𝔽_p)` is injective, and restriction of a hom to the generating set `S` is injective;
  hence `p ^ n ≤ p ^ S.card`, and `1 < p` gives `n ≤ S.card`.  Taking the infimum over generating
  sets gives the bound.

This is the `d ≥ |S|` shape needed by the arithmetic side of the Golod--Shafarevich argument: a
multiquadratic extension of degree `p ^ n` surjects onto `E_n`, whence the pro-`p` group has at
least `n` generators.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ProPDeficiency

section ElementaryAbelian

variable {p n : ℕ} [Fact p.Prime]

/-! ## The coordinate generators -/

/-- The `i`-th coordinate element of `Fin n → Multiplicative (ZMod p)`: equal to
`Multiplicative.ofAdd 1` in coordinate `i` and to `1` in every other coordinate. -/
def zmodPowGen (i : Fin n) : Fin n → Multiplicative (ZMod p) :=
  Function.update 1 i (Multiplicative.ofAdd (1 : ZMod p))

lemma zmodPowGen_self (i : Fin n) :
    zmodPowGen (p := p) i i = Multiplicative.ofAdd (1 : ZMod p) := by
  simp [zmodPowGen]

lemma zmodPowGen_of_ne {i j : Fin n} (h : j ≠ i) : zmodPowGen (p := p) i j = 1 := by
  simp [zmodPowGen, h]

/-- The coordinate elements generate the whole elementary abelian group. -/
lemma zmodPow_closure_range_gen_eq_top :
    Subgroup.closure (Set.range (zmodPowGen (p := p) (n := n))) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : x = ∏ i : Fin n, (zmodPowGen (p := p) i) ^ (Multiplicative.toAdd (x i)).val := by
    funext j
    rw [Finset.prod_apply]
    simp only [Pi.pow_apply, zmodPowGen, Function.update_apply, Pi.one_apply]
    have h1 : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ≠ j →
        (if j = b then Multiplicative.ofAdd (1 : ZMod p) else 1) ^
          (Multiplicative.toAdd (x b)).val = 1 := by
      intro b _ hb
      simp [Ne.symm hb]
    rw [Finset.prod_eq_single_of_mem j (Finset.mem_univ j) h1]
    simp only [ite_true]
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [hx]
  refine Subgroup.prod_mem _ fun i _ => ?_
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

/-! ## Homs to `𝔽_p` are determined by their values on a generating set -/

/-- Two monoid homomorphisms agreeing on a generating finset are equal. -/
lemma eq_of_eq_on_generatingSet {M N : Type*} [Group M] [Group N] (f g : M →* N)
    (S : Finset M) (hS : IsGeneratingSet S) (h : ∀ s ∈ S, f s = g s) : f = g := by
  let K : Subgroup M :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : f a = g a := ha
        have hb' : f b = g b := hb
        change f (a * b) = g (a * b)
        rw [map_mul, map_mul, ha', hb']
      inv_mem' := by
        intro a ha
        have ha' : f a = g a := ha
        change f a⁻¹ = g a⁻¹
        rw [map_inv, map_inv, ha'] }
  have hle : Subgroup.closure (S : Set M) ≤ K := by
    rw [Subgroup.closure_le]
    intro s hs
    exact h s (by simpa using hs)
  ext x
  exact hle (by rw [(isGeneratingSet_iff S).mp hS]; trivial)

/-! ## The standard homs `E_n → 𝔽_p` -/

/-- The hom `E_n → Multiplicative (ZMod p)` whose value on `x` is
`ofAdd (∑ i, toAdd (x i) * toAdd (c i))`: the `𝔽_p`-linear form associated with the tuple `c`. -/
def zmodPowCoordHom (c : Fin n → Multiplicative (ZMod p)) :
    (Fin n → Multiplicative (ZMod p)) →* Multiplicative (ZMod p) where
  toFun x :=
    Multiplicative.ofAdd (∑ i : Fin n, Multiplicative.toAdd (x i) * Multiplicative.toAdd (c i))
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [Pi.mul_apply, add_mul, Finset.sum_add_distrib]

/-- On the `i`-th coordinate generator, `zmodPowCoordHom c` takes the value `c i`. -/
lemma zmodPowCoordHom_gen (c : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    zmodPowCoordHom (p := p) c (zmodPowGen (p := p) i) = c i := by
  have hsum : (∑ j : Fin n, Multiplicative.toAdd (zmodPowGen (p := p) i j) *
        Multiplicative.toAdd (c j)) = Multiplicative.toAdd (c i) := by
    rw [Finset.sum_eq_single i
      (fun b _ hb => by rw [zmodPowGen_of_ne hb, toAdd_one, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [zmodPowGen_self, toAdd_ofAdd, one_mul]
  show Multiplicative.ofAdd (∑ j : Fin n, Multiplicative.toAdd (zmodPowGen (p := p) i j) *
      Multiplicative.toAdd (c j)) = c i
  rw [hsum, ofAdd_toAdd]

/-- The tuple `c` is recovered from the hom `zmodPowCoordHom c`; the assignment is injective. -/
lemma zmodPowCoordHom_injective :
    Function.Injective (zmodPowCoordHom (p := p) (n := n)) := by
  intro c c' h
  funext i
  rw [← zmodPowCoordHom_gen (p := p) c i, ← zmodPowCoordHom_gen (p := p) c' i, h]

/-! ## The counting bound -/

/-- Any generating finset of `E_n` has at least `n` elements. -/
lemma zmodPow_card_le_of_generatingSet (S : Finset (Fin n → Multiplicative (ZMod p)))
    (hS : IsGeneratingSet S) : n ≤ S.card := by
  classical
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective
      (fun c : Fin n → Multiplicative (ZMod p) => fun s : ↥S => zmodPowCoordHom (p := p) c s) := by
    intro c c' h
    refine zmodPowCoordHom_injective (p := p) ?_
    refine eq_of_eq_on_generatingSet (zmodPowCoordHom (p := p) c)
      (zmodPowCoordHom (p := p) c') S hS ?_
    intro s hs
    exact congr_fun h ⟨s, hs⟩
  have hcard : Fintype.card (Fin n → Multiplicative (ZMod p)) ≤
      Fintype.card (↥S → Multiplicative (ZMod p)) :=
    Fintype.card_le_of_injective _ hinj
  have h1 : Fintype.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_multiplicative, ZMod.card]
  have h2 : Fintype.card (↥S → Multiplicative (ZMod p)) = p ^ S.card := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_multiplicative, ZMod.card]
  rw [h1, h2] at hcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard

end ElementaryAbelian

/-- **The elementary abelian `p`-group of rank `n` has exactly `n` generators.** -/
theorem dGens_zmod_pow (p n : ℕ) [Fact p.Prime] :
    dGens (Fin n → Multiplicative (ZMod p)) = n := by
  classical
  have hgen : IsGeneratingSet (Finset.univ.image (zmodPowGen (p := p) (n := n))) := by
    rw [isGeneratingSet_iff, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact zmodPow_closure_range_gen_eq_top
  refine le_antisymm ?_ ?_
  · calc dGens (Fin n → Multiplicative (ZMod p))
        ≤ (Finset.univ.image (zmodPowGen (p := p) (n := n))).card := dGens_le_card hgen
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  · obtain ⟨S, hSgen, hScard⟩ :=
      exists_generatingSet_card_dGens (G := Fin n → Multiplicative (ZMod p)) ⟨_, hgen⟩
    rw [← hScard]
    exact zmodPow_card_le_of_generatingSet S hSgen

end Work.ProPDeficiency
