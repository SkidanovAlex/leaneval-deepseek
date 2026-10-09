import Mathlib
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped commutatorElement IsMulCommutative

namespace Work.ProP

/-! ## The first quotient of the `p`-central filtration

We prove `Nat.card (FreePQuotient p n 1) = p ^ n`, i.e. the first generic kernel
`F^(n)/F^(n)(1) = F^(n)/Φ_p(F^(n))` is elementary abelian of rank `n`.

The proof goes through the `MulEquiv`
`FreeGroup (Fin n) ⧸ (F^p ⁅F,F⁆) ≃* Multiplicative (Fin n → ZMod p)`, obtained from the
canonical surjection `φ : F →* (ℤ/p)^n` (free generators ↦ standard basis).  The two sides
of `ker φ = F^p ⁅F,F⁆` are the easy and the hard direction:

* `F^p ⁅F,F⁆ ≤ ker φ`, because `(ℤ/p)^n` is commutative of exponent `p`;
* `ker φ ≤ F^p ⁅F,F⁆`, because the *inverse* map `(ℤ/p)^n →* F/Φ_p(F)` sending the `i`-th
  basis vector to the `i`-th free generator exists — `F/Φ_p(F)` is commutative of exponent
  `p`, i.e. a module over `ZMod p`, so the assignment of the basis extends.  Composing with
  `φ` recovers the quotient map, and this forces `ker φ = Φ_p(F)`.
-/

/-- `pCentralStep p ⊤ ≤ K` iff `K` contains all `p`-th powers and all commutators of `G`.
This is the "elementary" form of the description `pCentralStep p ⊤ = G^p ⁅G,G⁆` of the
Frattini subgroup. -/
theorem pCentralStep_top_le_iff {G : Type*} [Group G] (p : ℕ) (K : Subgroup G) :
    Work.Shrinking.pCentralStep p (⊤ : Subgroup G) ≤ K ↔
      (∀ x : G, x ^ p ∈ K) ∧ (∀ a b : G, ⁅a, b⁆ ∈ K) := by
  rw [Work.Shrinking.pCentralStep, sup_le_iff, Work.Shrinking.powSubgroup, Subgroup.closure_le,
    Subgroup.commutator_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 ⟨x, trivial, rfl⟩, fun a b => h2 a trivial b trivial⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun g₁ _ g₂ _ => h2 g₁ g₂⟩
    rintro y ⟨x, -, rfl⟩
    exact h1 x

/-- Every element of `Multiplicative (Fin n → ZMod p)` has `p`-th power `1`. -/
theorem mult_pi_pow_p_eq_one {n p : ℕ} (x : Multiplicative (Fin n → ZMod p)) : x ^ p = 1 := by
  have h : (p : ℕ) • Multiplicative.toAdd x = 0 := by
    funext i
    simp [nsmul_eq_mul]
  calc x ^ p = Multiplicative.ofAdd ((p : ℕ) • Multiplicative.toAdd x) := rfl
    _ = Multiplicative.ofAdd 0 := by rw [h]
    _ = 1 := rfl

/-- `Multiplicative (Fin n → ZMod p)` is commutative. -/
theorem mult_pi_commutator_eq_one {n p : ℕ} (a b : Multiplicative (Fin n → ZMod p)) :
    ⁅a, b⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm a b

/-- The canonical surjection `F^(n) → (ℤ/p)^n` sending the `i`-th free generator to the `i`-th
standard basis vector. -/
noncomputable def phi (p n : ℕ) : FreeGroup (Fin n) →* Multiplicative (Fin n → ZMod p) :=
  FreeGroup.lift (fun i => Multiplicative.ofAdd (Pi.single i 1))

@[simp]
theorem phi_apply_of (p n : ℕ) (i : Fin n) :
    phi p n (FreeGroup.of i) = Multiplicative.ofAdd (Pi.single i 1) :=
  FreeGroup.lift_apply_of

/-- The standard-basis expansion in `(ℤ/p)^n`, in multiplicative form. -/
theorem prod_single_eq {n p : ℕ} [NeZero p] (a : Fin n → ZMod p) :
    (∏ i, (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) ^ (ZMod.val (a i)))
      = Multiplicative.ofAdd a := by
  have h : (∑ i, (ZMod.val (a i)) • Pi.single i (1 : ZMod p)) = a := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb)]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [show (∏ i, (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) ^ (ZMod.val (a i)))
      = Multiplicative.ofAdd (∑ i, (ZMod.val (a i)) • Pi.single i (1 : ZMod p)) from rfl, h]

/-- `φ` is surjective: the images of the free generators form the standard basis of `(ℤ/p)^n`. -/
theorem phi_surjective (p n : ℕ) [NeZero p] : Function.Surjective (phi p n) := by
  rw [phi, FreeGroup.lift_surjective_iff_closure_range_eq_top, Subgroup.eq_top_iff']
  intro v
  rw [Subgroup.mem_closure]
  intro K hK
  have hv : v = ∏ i, (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) ^
      (ZMod.val (Multiplicative.toAdd v i)) := by
    rw [prod_single_eq, ofAdd_toAdd]
  rw [hv]
  exact Subgroup.prod_mem K (fun i _ => K.pow_mem (hK ⟨i, rfl⟩) _)

/-- The *inverse* assignment `(ℤ/p)^n →* F^(n)/F^(n)(1)` sending the `i`-th basis vector to the
image of the `i`-th free generator.  It exists because `F^(n)/F^(n)(1)` is commutative of
exponent `p`, hence a module over `ZMod p`. -/
theorem exists_chi (p n : ℕ) :
    ∃ χ : Multiplicative (Fin n → ZMod p) →* FreePQuotient p n 1,
      ∀ i : Fin n, χ (Multiplicative.ofAdd (Pi.single i 1))
        = freePQuotientMk p n 1 (FreeGroup.of i) := by
  have hcomm : IsMulCommutative (FreePQuotient p n 1) := by
    refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro g ⟨a, b, rfl⟩
    exact Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  haveI := hcomm
  have hnexp : ∀ y : FreePQuotient p n 1, y ^ p = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := freePQuotientMk_surjective p n 1 y
    rw [← map_pow, freePQuotientMk_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨x, trivial, rfl⟩)
  letI : Module (ZMod p) (Additive (FreePQuotient p n 1)) :=
    AddCommGroup.zmodModule (by
      intro x
      show Additive.ofMul ((Additive.toMul x) ^ p) = 0
      rw [hnexp (Additive.toMul x)]
      rfl)
  let f : Fin n → Additive (FreePQuotient p n 1) :=
    fun i => Additive.ofMul (freePQuotientMk p n 1 (FreeGroup.of i))
  let lin : (Fin n → ZMod p) →ₗ[ZMod p] Additive (FreePQuotient p n 1) :=
    Fintype.linearCombination (ZMod p) f
  refine ⟨AddMonoidHom.toMultiplicativeLeft lin.toAddMonoidHom, fun i => ?_⟩
  rw [AddMonoidHom.toMultiplicativeLeft_apply_apply, toAdd_ofAdd]
  rw [show lin.toAddMonoidHom (Pi.single i (1 : ZMod p)) = f i from by
    rw [show lin.toAddMonoidHom
        = (Fintype.linearCombination (ZMod p) f).toAddMonoidHom from rfl,
      LinearMap.toAddMonoidHom_coe, Fintype.linearCombination_apply_single, one_smul]]
  rfl

/-- The first quotient of the `p`-central filtration of the free group on `n` generators has
order `p ^ n`: `F^(n)/F^(n)(1) = F^(n)/Φ_p(F^(n)) ≅ (ℤ/p)^n`.

Proof: `FreePQuotient p n 1 = F ⧸ (F^p ⁅F, F⁆)`.  (a) Upper bound: this quotient is commutative
of exponent `p` and generated by the images of `Fin n` (the free generators generate `F`), so
`Nat.card ≤ p ^ n` by `card_le_pow_of_finset_closure` — if that result is not available, do the
same computation with `Group.rank`/`card_dvd_exponent_pow_rank` directly.  (b) Lower bound:
`FreeGroup.lift` sending the `i`-th generator to the `i`-th standard basis vector gives a
surjection `F →* Multiplicative (Fin n → ZMod p)` (`FreeGroup.lift`, `Pi.single`,
`Fintype.linearCombination`-style decomposition to see surjectivity) whose kernel contains
`F^p⁅F,F⁆` (the target is commutative of exponent `p`), so `(ℤ/p)^n` is a quotient of
`FreePQuotient p n 1` and `Nat.card (FreePQuotient p n 1) ≥ p ^ n`
(`Nat.card_le_card_of_surjective`, `Nat.card_pi`). -/
theorem card_freePQuotient_one {p : ℕ} [Fact p.Prime] (n : ℕ) :
    Nat.card (FreePQuotient p n 1) = p ^ n := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨χ, hχ⟩ := exists_chi p n
  -- The `p`-central step `N = F^p ⁅F,F⁆` lies in the kernel of `φ`.
  have hNle : Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) 1 ≤ (phi p n).ker := by
    show Work.Shrinking.pCentralStep p (⊤ : Subgroup (FreeGroup (Fin n))) ≤ (phi p n).ker
    rw [pCentralStep_top_le_iff]
    exact ⟨fun x => by rw [MonoidHom.mem_ker, map_pow, mult_pi_pow_p_eq_one],
      fun a b => by rw [MonoidHom.mem_ker, map_commutatorElement, mult_pi_commutator_eq_one]⟩
  -- `χ ∘ φ` agrees with the quotient map on generators, hence everywhere.
  have hcomp : χ.comp (phi p n) = freePQuotientMk p n 1 := by
    refine FreeGroup.ext_hom _ _ (fun i => ?_)
    rw [MonoidHom.comp_apply, phi_apply_of, hχ i]
  have hchi_phi : ∀ x : FreeGroup (Fin n), χ (phi p n x) = freePQuotientMk p n 1 x :=
    fun x => DFunLike.congr_fun hcomp x
  -- Hence the kernel of `φ` is contained in `N`.
  have hker_le : (phi p n).ker ≤ Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) 1 := by
    intro x hx
    have h1 : phi p n x = 1 := hx
    have h2 : freePQuotientMk p n 1 x = 1 := by rw [← hchi_phi x, h1, map_one]
    rwa [freePQuotientMk_apply, QuotientGroup.eq_one_iff] at h2
  have hker : (phi p n).ker = Work.Shrinking.pCentralSeries p (FreeGroup (Fin n)) 1 :=
    le_antisymm hker_le hNle
  have hsurj : Function.Surjective (QuotientGroup.kerLift (phi p n)) := by
    intro a
    obtain ⟨x, rfl⟩ := phi_surjective p n a
    exact ⟨QuotientGroup.mk x, QuotientGroup.kerLift_mk (phi p n) x⟩
  let e : FreePQuotient p n 1 ≃* Multiplicative (Fin n → ZMod p) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (MulEquiv.ofBijective (QuotientGroup.kerLift (phi p n))
        ⟨QuotientGroup.kerLift_injective (phi p n), hsurj⟩)
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin n → ZMod p) = p ^ n
  rw [Nat.card_pi]
  simp [Finset.prod_const, Fintype.card_fin]

end Work.ProP
