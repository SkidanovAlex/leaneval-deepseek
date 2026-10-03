import Mathlib
import Submission.Work.FIArea7.KStarDefs
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_irred_norm_prime
import Submission.Commons.NumberTheory.GaussianInt.irreducible_norm_prime_pow
import Submission.Commons.NumberTheory.GaussianInt.irreducible_norm_eq_prime_or_sq
import Submission.Commons.NumberTheory.GaussianInt.associated_of_dvd_of_normNatAbs_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7.KStarDivs

open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Basic facts about the Gaussian norm -/

/-- `Work.FIPlan.gnorm` is multiplicative. -/
lemma gnorm_mul' (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma gnorm_one' : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
  simp [Work.FIPlan.gnorm]

lemma gnorm_eq_zero_iff' (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  rw [Work.FIPlan.gnorm]
  constructor
  · intro h
    exact GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp h)
  · intro h; subst h; simp [Work.FIPlan.gnorm]

lemma gnorm_pos' {z : GaussianInt} (hz : z ≠ 0) : 0 < Work.FIPlan.gnorm z :=
  Nat.pos_of_ne_zero (fun h => hz ((gnorm_eq_zero_iff' z).mp h))

lemma gnorm_of_associated {z w : GaussianInt} (h : Associated z w) :
    Work.FIPlan.gnorm z = Work.FIPlan.gnorm w := by
  obtain ⟨u, rfl⟩ := h
  rw [gnorm_mul']
  have hu : Work.FIPlan.gnorm (↑u : GaussianInt) = 1 :=
    Zsqrtd.norm_eq_one_iff.mpr u.isUnit
  rw [hu, mul_one]

/-- The norm of a product of a multiset of Gaussian integers is the product of the norms. -/
lemma gnorm_multiset_prod (m : Multiset GaussianInt) :
    Work.FIPlan.gnorm m.prod = (m.map Work.FIPlan.gnorm).prod := by
  induction m using Multiset.induction_on with
  | empty => simp [gnorm_one']
  | cons a s ih => simp [gnorm_mul', ih]

/-- A primary Gaussian integer is nonzero. -/
lemma isPrimary_ne_zero {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) : z ≠ 0 := by
  rintro rfl
  have h0 : Odd (0 : ℤ) := h.1
  obtain ⟨k, hk⟩ := h0
  omega

/-- A primary Gaussian integer has odd norm. -/
lemma odd_gnorm_of_isPrimary' (z : GaussianInt) (h : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  rw [Work.FIPlan.gnorm]
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  have hre2 : Odd (z.re ^ 2) := by rw [Int.odd_pow]; exact Or.inl h.1
  have him2 : Even (z.im ^ 2) := Int.even_pow.mpr ⟨h.2.1, by norm_num⟩
  have : Odd z.norm := by rw [hnorm]; exact hre2.add_even him2
  exact Int.natAbs_odd.mpr this

/-- The `ZMod 4` form of primarity. -/
lemma isPrimary_iff (z : GaussianInt) :
    Work.FIPlan.IsPrimary z ↔ Odd z.re ∧ Even z.im ∧ (z.im : ZMod 4) = (z.re : ZMod 4) - 1 := by
  unfold Work.FIPlan.IsPrimary
  have hsub : ((z.re - 1 : ℤ) : ZMod 4) = (z.re : ZMod 4) - 1 := by push_cast; ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [← hsub]; exact (ZMod.intCast_eq_intCast_iff _ _ 4).mpr h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (ZMod.intCast_eq_intCast_iff _ _ 4).mp (by rw [hsub]; exact h3)⟩

/-- Two associated primary Gaussian integers are equal. -/
lemma eq_of_associated_of_isPrimary {z w : GaussianInt} (hzw : Associated z w)
    (hz : Work.FIPlan.IsPrimary z) (hw : Work.FIPlan.IsPrimary w) : z = w := by
  obtain ⟨u, rfl⟩ := hzw
  rw [isPrimary_iff] at hz hw
  have hu1 : (↑u : GaussianInt) = 1 :=
    Commons.NumberTheory.GaussianInt.unit_eq_one_of_primary hz.1 hz.2.1 hz.2.2
      hw.1 hw.2.2
  rw [hu1, mul_one]

/-! ### The prime classes of a Gaussian integer -/

/-- The finite set of irreducible associate classes dividing `z`. -/
def primeClasses (z : GaussianInt) : Finset (Associates GaussianInt) :=
  ((UniqueFactorizationMonoid.factors z).map Associates.mk).toFinset

lemma mem_primeClasses {z : GaussianInt} (hz : z ≠ 0) {p : GaussianInt} (hp : Irreducible p) :
    Associates.mk p ∈ primeClasses z ↔ p ∣ z := by
  rw [primeClasses, Multiset.mem_toFinset, Multiset.mem_map]
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [Associates.mk_eq_mk_iff_associated] at hqp
    exact hqp.symm.dvd.trans (UniqueFactorizationMonoid.dvd_of_mem_factors hq)
  · intro hdvd
    obtain ⟨q, hq, hqp⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hz hp hdvd
    exact ⟨q, hq, by rw [Associates.mk_eq_mk_iff_associated]; exact hqp.symm⟩

lemma mem_primeClasses' {z : GaussianInt} (hz : z ≠ 0) {p : Associates GaussianInt}
    (hp : Irreducible p) : p ∈ primeClasses z ↔ p ∣ Associates.mk z := by
  obtain ⟨π, hπ⟩ := Associates.exists_rep p
  have hp' : Irreducible π := Associates.irreducible_mk.mp (hπ.symm ▸ hp)
  rw [← hπ]
  rw [mem_primeClasses hz hp', Associates.mk_dvd_mk]

lemma primeClasses_mono {z w : GaussianInt} (hw : w ≠ 0) (h : z ∣ w) :
    primeClasses z ⊆ primeClasses w := by
  intro α hα
  rw [primeClasses, Multiset.mem_toFinset, Multiset.mem_map] at hα
  obtain ⟨q, hq, hqα⟩ := hα
  rw [← hqα]
  exact (mem_primeClasses hw (UniqueFactorizationMonoid.irreducible_of_factor q hq)).mpr
    ((UniqueFactorizationMonoid.dvd_of_mem_factors hq).trans h)

lemma mem_primeClasses_of_mem_factors {z : GaussianInt} {q : GaussianInt}
    (hq : q ∈ UniqueFactorizationMonoid.factors z) :
    Associates.mk q ∈ primeClasses z := by
  rw [primeClasses, Multiset.mem_toFinset, Multiset.mem_map]
  exact ⟨q, hq, rfl⟩

/-! ### Squarefree elements and their prime classes -/

lemma count_le_one_mk {e : GaussianInt} (he : Squarefree e) (he0 : e ≠ 0)
    {π : GaussianInt} (hπ : Irreducible π) :
    Associates.count (Associates.mk π) (Associates.mk e).factors ≤ 1 := by
  by_contra h
  push Not at h
  have hmk : Associates.mk e ≠ 0 := Associates.mk_ne_zero.mpr he0
  have hp2 : (Associates.mk π) ^ 2 ≤ Associates.mk e :=
    (Associates.prime_pow_dvd_iff_le hmk (Associates.irreducible_mk.mpr hπ)).mpr h
  have hdvd : π * π ∣ e := by
    have hlt : Associates.mk (π * π) ≤ Associates.mk e := by
      simpa [Associates.mk_mul_mk, pow_two] using hp2
    exact Associates.mk_le_mk_iff_dvd.mp hlt
  exact ((squarefree_iff_no_irreducibles he0).mp he π hπ) hdvd

lemma count_le_one_of_squarefree {e : GaussianInt} (he : Squarefree e) (he0 : e ≠ 0)
    {p : Associates GaussianInt} (hp : Irreducible p) :
    Associates.count p (Associates.mk e).factors ≤ 1 := by
  obtain ⟨π, hπ⟩ := Associates.exists_rep p
  rw [← hπ]
  exact count_le_one_mk he he0 (Associates.irreducible_mk.mp (hπ.symm ▸ hp))

lemma one_le_count_iff_dvd_mk {e : GaussianInt} (he0 : e ≠ 0) {π : GaussianInt}
    (hπ : Irreducible π) :
    1 ≤ Associates.count (Associates.mk π) (Associates.mk e).factors ↔ π ∣ e := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr he0)
    (Associates.irreducible_mk.mpr hπ), pow_one]
  exact Associates.mk_le_mk_iff_dvd

lemma one_le_count_iff_dvd {e : GaussianInt} (he0 : e ≠ 0) {p : Associates GaussianInt}
    (hp : Irreducible p) :
    1 ≤ Associates.count p (Associates.mk e).factors ↔ p ∣ Associates.mk e := by
  obtain ⟨π, hπ⟩ := Associates.exists_rep p
  rw [← hπ, Associates.mk_dvd_mk]
  exact one_le_count_iff_dvd_mk he0 (Associates.irreducible_mk.mp (hπ.symm ▸ hp))

lemma count_eq_ite {e : GaussianInt} (he : Squarefree e) (he0 : e ≠ 0)
    {p : Associates GaussianInt} (hp : Irreducible p) :
    Associates.count p (Associates.mk e).factors = if p ∣ Associates.mk e then 1 else 0 := by
  have hle := count_le_one_of_squarefree he he0 hp
  have hiff := one_le_count_iff_dvd he0 hp
  by_cases hd : p ∣ Associates.mk e
  · rw [if_pos hd]; exact le_antisymm hle (hiff.mpr hd)
  · rw [if_neg hd]
    exact Nat.lt_one_iff.mp (not_le.mp (fun hc => hd (hiff.mp hc)))

/-- A squarefree primary element is determined by its set of prime classes. -/
lemma primeClasses_inj {e e' : GaussianInt} (he : Squarefree e) (he' : Squarefree e')
    (hpe : Work.FIPlan.IsPrimary e) (hpe' : Work.FIPlan.IsPrimary e')
    (he0 : e ≠ 0) (he0' : e' ≠ 0) (h : primeClasses e = primeClasses e') : e = e' := by
  have hcount : ∀ p : Associates GaussianInt, Irreducible p →
      Associates.count p (Associates.mk e).factors
        = Associates.count p (Associates.mk e').factors := by
    intro p hp
    have hp1 : (p ∣ Associates.mk e) ↔ (p ∣ Associates.mk e') := by
      rw [← mem_primeClasses' he0 hp, ← mem_primeClasses' he0' hp, h]
    by_cases hd : p ∣ Associates.mk e
    · rw [count_eq_ite he he0 hp, count_eq_ite he' he0' hp, if_pos hd, if_pos (hp1.mp hd)]
    · rw [count_eq_ite he he0 hp, count_eq_ite he' he0' hp, if_neg hd,
        if_neg (fun hc => hd (hp1.mpr hc))]
  have hfac := Associates.eq_factors_of_eq_counts (Associates.mk_ne_zero.mpr he0)
    (Associates.mk_ne_zero.mpr he0') hcount
  have hmk : Associates.mk e = Associates.mk e' := Associates.eq_of_factors_eq_factors hfac
  exact eq_of_associated_of_isPrimary
    (Associates.mk_eq_mk_iff_associated.mp hmk) hpe hpe'

/-! ### The norm of a prime class -/

/-- A chosen representative of an associate class of Gaussian integers. -/
noncomputable def repAssoc (α : Associates GaussianInt) : GaussianInt :=
  Classical.choose (Associates.exists_rep α)

lemma mk_repAssoc (α : Associates GaussianInt) : Associates.mk (repAssoc α) = α :=
  Classical.choose_spec (Associates.exists_rep α)

/-- The norm of an associate class of Gaussian integers. -/
def qnorm (α : Associates GaussianInt) : ℕ := Work.FIPlan.gnorm (repAssoc α)

lemma qnorm_mk (z : GaussianInt) : qnorm (Associates.mk z) = Work.FIPlan.gnorm z := by
  unfold qnorm repAssoc
  exact gnorm_of_associated (Associates.mk_eq_mk_iff_associated.mp
    (Classical.choose_spec (Associates.exists_rep (Associates.mk z))))

/-! ### Auxiliary real / multiset lemmas -/

lemma sqrt_multiset_prod (m : Multiset ℕ) :
    Real.sqrt ((m.prod : ℕ) : ℝ) = (m.map (fun x : ℕ => Real.sqrt (x : ℝ))).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul,
        Real.sqrt_mul (by positivity), ih]

lemma inv_multiset_prod (m : Multiset ℝ) :
    (m.prod)⁻¹ = (m.map (fun x => x⁻¹)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, mul_inv_rev, ih, mul_comm]

lemma multiset_prod_nonneg {β : Type*} (m : Multiset β) (g : β → ℝ)
    (h0 : ∀ x ∈ m, 0 ≤ g x) : 0 ≤ (m.map g).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_nonneg (h0 a (Multiset.mem_cons_self a s))
        (ih (fun x hx => h0 x (Multiset.mem_cons_of_mem hx)))

lemma multiset_prod_le_toFinset_prod {β : Type*} [DecidableEq β] (m : Multiset β) (g : β → ℝ)
    (h0 : ∀ x ∈ m, 0 ≤ g x) (h1 : ∀ x ∈ m.toFinset, g x ≤ 1) :
    (m.map g).prod ≤ m.toFinset.prod g := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      have h0s : ∀ x ∈ s, 0 ≤ g x := fun x hx => h0 x (Multiset.mem_cons_of_mem hx)
      have h1s : ∀ x ∈ s.toFinset, g x ≤ 1 := fun x hx =>
        h1 x (by rw [Multiset.mem_toFinset] at hx ⊢; exact Multiset.mem_cons_of_mem hx)
      have ihs := ih h0s h1s
      rw [Multiset.toFinset_cons]
      by_cases ha : a ∈ s.toFinset
      · rw [Finset.insert_eq_of_mem ha]
        calc g a * (s.map g).prod ≤ 1 * (s.map g).prod :=
              mul_le_mul_of_nonneg_right
                (h1 a (Multiset.mem_toFinset.mpr (Multiset.mem_cons_self a s)))
                (multiset_prod_nonneg s g h0s)
          _ = (s.map g).prod := one_mul _
          _ ≤ s.toFinset.prod g := ihs
      · rw [Finset.prod_insert ha]
        exact mul_le_mul_of_nonneg_left ihs (h0 a (Multiset.mem_cons_self a s))

/-- The reciprocal of the root of the norm of a nonzero Gaussian integer is at most the product
of the reciprocals of the roots of the norms of its prime classes. -/
lemma inv_sqrt_gnorm_le_prod {e : GaussianInt} (he0 : e ≠ 0) :
    (Real.sqrt (Work.FIPlan.gnorm e))⁻¹ ≤
      ∏ α ∈ primeClasses e, (Real.sqrt (qnorm α))⁻¹ := by
  have hprod : Work.FIPlan.gnorm e
      = ((UniqueFactorizationMonoid.factors e).map Work.FIPlan.gnorm).prod := by
    rw [← gnorm_of_associated (UniqueFactorizationMonoid.factors_prod he0)]
    exact gnorm_multiset_prod _
  have h1 : (Real.sqrt (Work.FIPlan.gnorm e))⁻¹
      = ((UniqueFactorizationMonoid.factors e).map
          (fun x => (Real.sqrt (Work.FIPlan.gnorm x))⁻¹)).prod := by
    rw [hprod, sqrt_multiset_prod, inv_multiset_prod]
    congr 1
    simp only [Multiset.map_map, Function.comp_apply]
  rw [h1]
  have h2 : ((UniqueFactorizationMonoid.factors e).map
        (fun x => (Real.sqrt (Work.FIPlan.gnorm x))⁻¹))
      = (((UniqueFactorizationMonoid.factors e).map Associates.mk).map
          (fun α => (Real.sqrt (qnorm α))⁻¹)) := by
    rw [Multiset.map_map]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [qnorm_mk]
  rw [h2]
  refine multiset_prod_le_toFinset_prod ((UniqueFactorizationMonoid.factors e).map Associates.mk)
    (fun α => (Real.sqrt (qnorm α))⁻¹)
    (fun α _ => inv_nonneg.mpr (Real.sqrt_nonneg _)) ?_
  intro α hα
  rw [Multiset.mem_toFinset, Multiset.mem_map] at hα
  obtain ⟨x, hx, rfl⟩ := hα
  rw [qnorm_mk]
  refine inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr ?_)
  have hx0 : x ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_factor x hx).ne_zero
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (gnorm_pos' hx0).ne'

/-- Membership description of the squarefree primary divisors of a primary `w`. -/
lemma mem_gaussPrimDivs_ne {w e : GaussianInt} (hw0 : w ≠ 0) (he : e ∈ gaussPrimDivs w) :
    e ∣ w ∧ Work.FIPlan.IsPrimary e ∧ e ≠ 0 := by
  rw [gaussPrimDivs, Finset.mem_filter] at he
  obtain ⟨-, hdvd, hprim⟩ := he
  refine ⟨hdvd, hprim, ?_⟩
  rintro rfl
  exact hw0 (zero_dvd_iff.mp hdvd)

/-- **Step 3.** The squarefree-primary-divisor sum is bounded by the product over prime classes. -/
lemma sum_le_prod_primeClasses {w : GaussianInt} (hw : Work.FIPlan.IsPrimary w) :
    (∑ e ∈ (gaussPrimDivs w).filter Squarefree, (Real.sqrt (Work.FIPlan.gnorm e))⁻¹)
      ≤ ∏ α ∈ primeClasses w, (1 + (Real.sqrt (qnorm α))⁻¹) := by
  have hw0 : w ≠ 0 := isPrimary_ne_zero hw
  have hmem : ∀ e ∈ (gaussPrimDivs w).filter Squarefree,
      e ∣ w ∧ Work.FIPlan.IsPrimary e ∧ Squarefree e ∧ e ≠ 0 := by
    intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨hge, hsf⟩ := he
    obtain ⟨hdvd, hprim, he0⟩ := mem_gaussPrimDivs_ne hw0 hge
    exact ⟨hdvd, hprim, hsf, he0⟩
  calc (∑ e ∈ (gaussPrimDivs w).filter Squarefree, (Real.sqrt (Work.FIPlan.gnorm e))⁻¹)
      ≤ ∑ e ∈ (gaussPrimDivs w).filter Squarefree,
          ∏ α ∈ primeClasses e, (Real.sqrt (qnorm α))⁻¹ :=
        Finset.sum_le_sum (fun e he => inv_sqrt_gnorm_le_prod (hmem e he).2.2.2)
    _ = ∑ S ∈ ((gaussPrimDivs w).filter Squarefree).image primeClasses,
          ∏ α ∈ S, (Real.sqrt (qnorm α))⁻¹ := by
        rw [Finset.sum_image]
        intro e he e' he' h
        exact primeClasses_inj (hmem e he).2.2.1 (hmem e' he').2.2.1 (hmem e he).2.1
          (hmem e' he').2.1 (hmem e he).2.2.2 (hmem e' he').2.2.2 h
    _ ≤ ∑ S ∈ (primeClasses w).powerset, ∏ α ∈ S, (Real.sqrt (qnorm α))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          rw [Finset.mem_image] at hS
          obtain ⟨e, he, rfl⟩ := hS
          rw [Finset.mem_powerset]
          exact primeClasses_mono hw0 (hmem e he).1
        · intro S _ _
          exact Finset.prod_nonneg (fun α _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = ∏ α ∈ primeClasses w, (1 + (Real.sqrt (qnorm α))⁻¹) := by
        rw [Finset.prod_one_add]

/-! ### Step 4: the product over prime classes -/

lemma irreducible_repAssoc {α : Associates GaussianInt} (h : Irreducible α) :
    Irreducible (repAssoc α) :=
  Associates.irreducible_mk.mp ((mk_repAssoc α).symm ▸ h)

/-- A chosen rational prime attached to an irreducible class, with `qnorm α = p ∨ p ^ 2`. -/
noncomputable def pfac (α : Associates GaussianInt) : ℕ :=
  if h : Irreducible α then
    Classical.choose (Commons.NumberTheory.GaussianInt.irreducible_norm_eq_prime_or_sq
      (irreducible_repAssoc h))
  else 1

lemma pfac_prime {α : Associates GaussianInt} (h : Irreducible α) : (pfac α).Prime := by
  rw [pfac, dif_pos h]
  exact (Classical.choose_spec
    (Commons.NumberTheory.GaussianInt.irreducible_norm_eq_prime_or_sq
      (irreducible_repAssoc h))).1

lemma qnorm_eq_pfac_or_sq {α : Associates GaussianInt} (h : Irreducible α) :
    qnorm α = pfac α ∨ qnorm α = (pfac α) ^ 2 := by
  rw [pfac, dif_pos h]
  exact (Classical.choose_spec
    (Commons.NumberTheory.GaussianInt.irreducible_norm_eq_prime_or_sq
      (irreducible_repAssoc h))).2

lemma qnorm_le_pfac_sq {α : Associates GaussianInt} (h : Irreducible α) :
    pfac α ≤ qnorm α := by
  rcases qnorm_eq_pfac_or_sq h with h' | h'
  · rw [h']
  · rw [h']; exact Nat.le_self_pow (by norm_num : (2:ℕ) ≠ 0) (pfac α)

lemma qnorm_pos {α : Associates GaussianInt} (h : Irreducible α) : 0 < qnorm α := by
  rw [qnorm]
  exact gnorm_pos' (irreducible_repAssoc h).ne_zero

lemma gnorm_dvd_of_dvd {x y : GaussianInt} (h : x ∣ y) :
    Work.FIPlan.gnorm x ∣ Work.FIPlan.gnorm y := by
  obtain ⟨k, rfl⟩ := h
  rw [gnorm_mul']
  exact dvd_mul_right _ _

lemma gnorm_finset_prod {ι : Type*} (S : Finset ι) (f : ι → GaussianInt) :
    Work.FIPlan.gnorm (∏ x ∈ S, f x) = ∏ x ∈ S, Work.FIPlan.gnorm (f x) := by
  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  simpa [Multiset.map_map, Function.comp_def] using gnorm_multiset_prod (S.val.map f)

lemma dvd_self_natCast_gnorm (z : GaussianInt) :
    z ∣ ((Work.FIPlan.gnorm z : ℕ) : GaussianInt) :=
  ⟨star z, Commons.NumberTheory.GaussianInt.norm_natAbs_cast_eq z⟩

/-- An irreducible class of `primeClasses w` is irreducible. -/
lemma irreducible_of_mem_primeClasses {w : GaussianInt} {α : Associates GaussianInt}
    (hα : α ∈ primeClasses w) : Irreducible α := by
  rw [primeClasses, Multiset.mem_toFinset, Multiset.mem_map] at hα
  obtain ⟨q, hq, rfl⟩ := hα
  exact Associates.irreducible_mk.mpr (UniqueFactorizationMonoid.irreducible_of_factor q hq)

lemma repAssoc_dvd {w : GaussianInt} (hw0 : w ≠ 0) {α : Associates GaussianInt}
    (hα : α ∈ primeClasses w) : repAssoc α ∣ w := by
  have hirr : Irreducible α := irreducible_of_mem_primeClasses hα
  have h1 : α ∣ Associates.mk w := (mem_primeClasses' hw0 hirr).mp hα
  rw [← mk_repAssoc α] at h1
  exact Associates.mk_dvd_mk.mp h1

lemma pfac_dvd_qnorm {α : Associates GaussianInt} (h : Irreducible α) :
    pfac α ∣ qnorm α := by
  rcases qnorm_eq_pfac_or_sq h with h' | h'
  · rw [h']
  · rw [h', pow_two]; exact dvd_mul_right _ _

/-- For `α ∈ primeClasses w`, `repAssoc α` divides the rational prime `pfac α`. -/
lemma pfac_repAssoc_dvd {w : GaussianInt} (hw0 : w ≠ 0) {α : Associates GaussianInt}
    (hα : α ∈ primeClasses w) : repAssoc α ∣ (pfac α : GaussianInt) := by
  have hirr : Irreducible α := irreducible_of_mem_primeClasses hα
  have hπirr : Irreducible (repAssoc α) := irreducible_repAssoc hirr
  have hgn : repAssoc α ∣ ((Work.FIPlan.gnorm (repAssoc α) : ℕ) : GaussianInt) :=
    dvd_self_natCast_gnorm _
  rcases qnorm_eq_pfac_or_sq hirr with h' | h'
  · have hc : ((Work.FIPlan.gnorm (repAssoc α) : ℕ) : GaussianInt) = (pfac α : GaussianInt) := by
      rw [← h']; rfl
    rwa [hc] at hgn
  · have hc : ((Work.FIPlan.gnorm (repAssoc α) : ℕ) : GaussianInt)
        = (pfac α : GaussianInt) ^ 2 := by
      rw [← Nat.cast_pow, ← h']; rfl
    rw [hc] at hgn
    exact (UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr).dvd_of_dvd_pow hgn

lemma isRelPrime_of_irreducible_not_associated {x y : GaussianInt}
    (hx : Irreducible x) (hy : Irreducible y) (h : ¬ Associated x y) : IsRelPrime x y :=
  hx.isRelPrime_iff_not_dvd.mpr fun hxy => h (hx.associated_of_dvd hy hxy)

lemma pairwise_isRelPrime_filter {w : GaussianInt} {j : ℕ} :
    ∀ α ∈ (primeClasses w).filter (fun α => pfac α = j),
      ∀ β ∈ (primeClasses w).filter (fun α => pfac α = j), α ≠ β →
        IsRelPrime (repAssoc α) (repAssoc β) := by
  intro α hα β hβ hne
  rw [Finset.mem_filter] at hα hβ
  have hirrα : Irreducible α := irreducible_of_mem_primeClasses hα.1
  have hirrβ : Irreducible β := irreducible_of_mem_primeClasses hβ.1
  refine isRelPrime_of_irreducible_not_associated (irreducible_repAssoc hirrα)
    (irreducible_repAssoc hirrβ) ?_
  intro hassoc
  have h2 : Associates.mk (repAssoc α) = Associates.mk (repAssoc β) :=
    Associates.mk_eq_mk_iff_associated.mpr hassoc
  rw [mk_repAssoc α, mk_repAssoc β] at h2
  exact hne h2

/-- `j ^ #S` divides the norm of the product of the `repAssoc`s over a set `S` of classes all
attached to the prime `j`. -/
lemma pfac_pow_card_dvd_gnorm_prod {w : GaussianInt} {j : ℕ} :
    j ^ ((primeClasses w).filter (fun α => pfac α = j)).card
      ∣ Work.FIPlan.gnorm (∏ α ∈ (primeClasses w).filter (fun α => pfac α = j), repAssoc α) := by
  rw [gnorm_finset_prod, ← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro α hα
  rw [Finset.mem_filter] at hα
  rw [← hα.2, ← qnorm]
  exact pfac_dvd_qnorm (irreducible_of_mem_primeClasses hα.1)

/-- The number of prime classes attached to a fixed prime `j` is at most `2`. -/
lemma pfac_card_le_two {w : GaussianInt} (hw0 : w ≠ 0) {j : ℕ} (hj : j.Prime) :
    ((primeClasses w).filter (fun α => pfac α = j)).card ≤ 2 := by
  have hpair := pairwise_isRelPrime_filter (w := w) (j := j)
  have hdvd : ∀ α ∈ (primeClasses w).filter (fun α => pfac α = j),
      repAssoc α ∣ (j : GaussianInt) := by
    intro α hα
    rw [Finset.mem_filter] at hα
    rw [← hα.2]
    exact pfac_repAssoc_dvd hw0 hα.1
  have hprod : ∏ α ∈ (primeClasses w).filter (fun α => pfac α = j), repAssoc α
      ∣ (j : GaussianInt) :=
    Finset.prod_dvd_of_isRelPrime (z := (j : GaussianInt)) (s := repAssoc) hpair hdvd
  have hdvd2 := pfac_pow_card_dvd_gnorm_prod (w := w) (j := j)
  have hpos : 0 < Work.FIPlan.gnorm (∏ α ∈ (primeClasses w).filter (fun α => pfac α = j),
      repAssoc α) := by
    rw [gnorm_finset_prod]
    apply Finset.prod_pos
    intro α hα
    rw [Finset.mem_filter] at hα
    rw [← qnorm]
    exact qnorm_pos (irreducible_of_mem_primeClasses hα.1)
  have hle1 : j ^ ((primeClasses w).filter (fun α => pfac α = j)).card
      ≤ Work.FIPlan.gnorm (∏ α ∈ (primeClasses w).filter (fun α => pfac α = j), repAssoc α) :=
    Nat.le_of_dvd hpos hdvd2
  have hle2 : Work.FIPlan.gnorm (∏ α ∈ (primeClasses w).filter (fun α => pfac α = j), repAssoc α)
      ≤ j ^ 2 := by
    have hgnj : Work.FIPlan.gnorm (j : GaussianInt) = j ^ 2 := by
      rw [Work.FIPlan.gnorm, Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast]
      ring
    rw [← hgnj]
    exact Nat.le_of_dvd (gnorm_pos' (by exact_mod_cast hj.ne_zero))
      (gnorm_dvd_of_dvd hprod)
  exact (Nat.pow_le_pow_iff_right hj.one_lt).mp (le_trans hle1 hle2)

/-- The number of prime classes attached to a fixed prime `j` is at most the multiplicity of `j`
in `‖w‖`. -/
lemma pfac_card_le_factorization {w : GaussianInt} (hw0 : w ≠ 0) {j : ℕ} (hj : j.Prime) :
    ((primeClasses w).filter (fun α => pfac α = j)).card
      ≤ (Work.FIPlan.gnorm w).factorization j := by
  have hN0 : Work.FIPlan.gnorm w ≠ 0 := (gnorm_pos' hw0).ne'
  have hpair := pairwise_isRelPrime_filter (w := w) (j := j)
  have hdvd : ∀ α ∈ (primeClasses w).filter (fun α => pfac α = j), repAssoc α ∣ w := by
    intro α hα
    rw [Finset.mem_filter] at hα
    exact repAssoc_dvd hw0 hα.1
  have hprod : ∏ α ∈ (primeClasses w).filter (fun α => pfac α = j), repAssoc α ∣ w :=
    Finset.prod_dvd_of_isRelPrime (z := w) (s := repAssoc) hpair hdvd
  exact (hj.pow_dvd_iff_le_factorization hN0).mp
    ((pfac_pow_card_dvd_gnorm_prod (w := w) (j := j)).trans (gnorm_dvd_of_dvd hprod))

/-- The local factor bound: for a prime `j`, `M ≤ 2` and `M ≤ v` give
`(1 + 1/√j) ^ M ≤ v + 1`. -/
lemma pow_one_add_inv_sqrt_le {j M v : ℕ} (hj : j.Prime) (hM2 : M ≤ 2) (hMv : M ≤ v) :
    (1 + (Real.sqrt (j : ℝ))⁻¹) ^ M ≤ (v : ℝ) + 1 := by
  have hkey : (1 + (Real.sqrt 2)⁻¹) ^ 2 ≤ 3 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← sq, Real.sq_sqrt (by norm_num)]
    have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
    have hmul : (1 + (Real.sqrt 2)⁻¹) ^ 2 * (Real.sqrt 2) ^ 2 = (Real.sqrt 2 + 1) ^ 2 := by
      have hne : Real.sqrt 2 ≠ 0 := ne_of_gt h2pos
      have h1 : (1 + (Real.sqrt 2)⁻¹) * Real.sqrt 2 = Real.sqrt 2 + 1 := by
        rw [add_mul, one_mul, inv_mul_cancel₀ hne]
      rw [← mul_pow, h1]
    have hbound : (Real.sqrt 2 + 1) ^ 2 ≤ 3 * (Real.sqrt 2) ^ 2 := by
      have h3 : Real.sqrt 2 ≤ 3 / 2 := by
        nlinarith [h2, sq_nonneg (2 * Real.sqrt 2 - 3), Real.sqrt_nonneg 2]
      nlinarith [h3, Real.sqrt_nonneg 2]
    nlinarith [hmul, hbound, h2pos]
  have hsq : (1 + (Real.sqrt (j : ℝ))⁻¹) ^ 2 ≤ 3 := by
    have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.two_le
    have hspos : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos_of_pos (by linarith)
    have hmono : Real.sqrt 2 ≤ Real.sqrt (j : ℝ) := Real.sqrt_le_sqrt hj2
    have hinv : (Real.sqrt (j : ℝ))⁻¹ ≤ (Real.sqrt 2)⁻¹ :=
      (inv_le_inv₀ hspos (Real.sqrt_pos_of_pos (by norm_num))).mpr hmono
    have hstep : (1 + (Real.sqrt (j : ℝ))⁻¹) ^ 2 ≤ (1 + (Real.sqrt 2)⁻¹) ^ 2 := by
      nlinarith [hinv, inv_nonneg.mpr (Real.sqrt_nonneg (j : ℝ)),
        inv_nonneg.mpr (Real.sqrt_nonneg (2 : ℝ))]
    linarith
  interval_cases M
  · simp
  · rw [pow_one]
    have h1 : (Real.sqrt (j : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by exact_mod_cast hj.one_le))
    have h2 : (2 : ℝ) ≤ (v : ℝ) + 1 := by
      have : (1 : ℕ) ≤ v := by omega
      exact_mod_cast (by omega : (2 : ℕ) ≤ v + 1)
    linarith
  · have h2 : (3 : ℝ) ≤ (v : ℝ) + 1 := by
      have : (2 : ℕ) ≤ v := by omega
      exact_mod_cast (by omega : (3 : ℕ) ≤ v + 1)
    linarith

/-- **Step 4.** The product over prime classes is bounded by the divisor count of the norm. -/
lemma prod_primeClasses_le_tau {w : GaussianInt} (hw : Work.FIPlan.IsPrimary w) :
    ∏ α ∈ primeClasses w, (1 + (Real.sqrt (qnorm α))⁻¹)
      ≤ (((Work.FIPlan.gnorm w).divisors).card : ℝ) := by
  have hw0 : w ≠ 0 := isPrimary_ne_zero hw
  set N := Work.FIPlan.gnorm w with hN
  have hN0 : N ≠ 0 := by rw [hN]; exact (gnorm_pos' hw0).ne'
  set P := primeClasses w with hP
  have hA : ∏ α ∈ P, (1 + (Real.sqrt (qnorm α))⁻¹)
      ≤ ∏ α ∈ P, (1 + (Real.sqrt (pfac α))⁻¹) := by
    apply Finset.prod_le_prod₀
    · intro α _; positivity
    · intro α hα
      have hirr : Irreducible α := irreducible_of_mem_primeClasses (hP ▸ hα)
      have hle : pfac α ≤ qnorm α := qnorm_le_pfac_sq hirr
      have hqpos : (0 : ℝ) < (qnorm α : ℝ) := by
        rw [qnorm]; exact_mod_cast qnorm_pos hirr
      have hppos : (0 : ℝ) < (pfac α : ℝ) := by exact_mod_cast (pfac_prime hirr).pos
      have hinv : (Real.sqrt (qnorm α))⁻¹ ≤ (Real.sqrt (pfac α))⁻¹ :=
        (inv_le_inv₀ (Real.sqrt_pos_of_pos hqpos) (Real.sqrt_pos_of_pos hppos)).mpr
          (Real.sqrt_le_sqrt (by exact_mod_cast hle))
      linarith
  have hmap : ∀ α ∈ P, pfac α ∈ N.primeFactors := by
    intro α hα
    have hirr : Irreducible α := irreducible_of_mem_primeClasses (hP ▸ hα)
    rw [hN, Nat.mem_primeFactors]
    exact ⟨pfac_prime hirr, dvd_trans (pfac_dvd_qnorm hirr)
      (gnorm_dvd_of_dvd (repAssoc_dvd hw0 (hP ▸ hα))), (gnorm_pos' hw0).ne'⟩
  have hB : ∏ α ∈ P, (1 + (Real.sqrt (pfac α))⁻¹)
      = ∏ j ∈ N.primeFactors,
          (1 + (Real.sqrt (j : ℝ))⁻¹) ^ (P.filter (fun α => pfac α = j)).card := by
    rw [← Finset.prod_fiberwise_of_maps_to hmap (fun α => (1 + (Real.sqrt (pfac α))⁻¹))]
    apply Finset.prod_congr rfl
    intro j _
    rw [Finset.prod_congr rfl (fun α hα => by rw [(Finset.mem_filter.mp hα).2]),
      Finset.prod_const]
  have hC : ∏ j ∈ N.primeFactors,
        (1 + (Real.sqrt (j : ℝ))⁻¹) ^ (P.filter (fun α => pfac α = j)).card
      ≤ ∏ j ∈ N.primeFactors, (((N.factorization j + 1 : ℕ)) : ℝ) := by
    refine Finset.prod_le_prod₀ (s := N.primeFactors)
      (f := fun j : ℕ => (1 + (Real.sqrt (j : ℝ))⁻¹) ^ (P.filter (fun α => pfac α = j)).card)
      (g := fun j : ℕ => (((N.factorization j + 1 : ℕ)) : ℝ)) ?_ ?_
    · intro j _; positivity
    · intro j hj
      have hjprime : j.Prime := by rw [hN] at hj; exact (Nat.mem_primeFactors.mp hj).1
      have hM2 : (P.filter (fun α => pfac α = j)).card ≤ 2 := pfac_card_le_two hw0 hjprime
      have hMv : (P.filter (fun α => pfac α = j)).card ≤ N.factorization j :=
        pfac_card_le_factorization hw0 hjprime
      exact (pow_one_add_inv_sqrt_le hjprime hM2 hMv).trans (le_of_eq (by push_cast; ring))
  have hD : ∏ j ∈ N.primeFactors, (((N.factorization j + 1 : ℕ)) : ℝ)
      = ((N.divisors.card : ℕ) : ℝ) := by
    rw [Nat.card_divisors hN0, Nat.cast_prod]
  calc ∏ α ∈ P, (1 + (Real.sqrt (qnorm α))⁻¹)
      ≤ ∏ α ∈ P, (1 + (Real.sqrt (pfac α))⁻¹) := hA
    _ = ∏ j ∈ N.primeFactors,
          (1 + (Real.sqrt (j : ℝ))⁻¹) ^ (P.filter (fun α => pfac α = j)).card := hB
    _ ≤ ∏ j ∈ N.primeFactors, (((N.factorization j + 1 : ℕ)) : ℝ) := hC
    _ = ((N.divisors.card : ℕ) : ℝ) := hD

/-- **Friedlander–Iwaniec (22.4), norm bookkeeping.** The sum of `1/√‖e‖` over the squarefree
primary Gaussian divisors of a primary `w` is bounded by the number of divisors of `‖w‖`. -/
theorem sum_inv_sqrt_sqfree_gaussPrimDivs_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (w : GaussianInt), Work.FIPlan.IsPrimary w →
      (∑ e ∈ gaussPrimDivs w,
          (if Squarefree e then 1 / Real.sqrt (((Work.FIPlan.gnorm e : ℕ) : ℝ)) else 0))
        ≤ K * ((((Work.FIPlan.gnorm w)).divisors).card : ℝ) := by
  refine ⟨1, one_pos, ?_⟩
  intro w hw
  rw [← Finset.sum_filter]
  have h2 : (∑ e ∈ (gaussPrimDivs w).filter Squarefree,
        1 / Real.sqrt (((Work.FIPlan.gnorm e : ℕ) : ℝ)))
      = (∑ e ∈ (gaussPrimDivs w).filter Squarefree, (Real.sqrt (Work.FIPlan.gnorm e))⁻¹) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [one_div]
  rw [h2]
  have h1 : (∑ e ∈ (gaussPrimDivs w).filter Squarefree,
        (Real.sqrt (Work.FIPlan.gnorm e))⁻¹)
      ≤ ∏ α ∈ primeClasses w, (1 + (Real.sqrt (qnorm α))⁻¹) := sum_le_prod_primeClasses hw
  have h3 : ∏ α ∈ primeClasses w, (1 + (Real.sqrt (qnorm α))⁻¹)
      ≤ (((Work.FIPlan.gnorm w).divisors).card : ℝ) := prod_primeClasses_le_tau hw
  calc (∑ e ∈ (gaussPrimDivs w).filter Squarefree, (Real.sqrt (Work.FIPlan.gnorm e))⁻¹)
      ≤ ∏ α ∈ primeClasses w, (1 + (Real.sqrt (qnorm α))⁻¹) := h1
    _ ≤ (((Work.FIPlan.gnorm w).divisors).card : ℝ) := h3
    _ = 1 * ((((Work.FIPlan.gnorm w)).divisors).card : ℝ) := by ring

end

end Work.FIArea7.KStarDivs
