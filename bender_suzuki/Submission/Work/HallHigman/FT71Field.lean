import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.ModRep
import Submission.Work.HallHigman.map_invariants_le_of_normal
import Submission.Work.HallHigman.minpoly_eq_X_sub_one_sq_of_sq_eq_zero
import Submission.Work.HallHigman.exists_ne_zero_fixed_of_isPGroup_field

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

universe u v w

namespace Work.HallHigman

open Polynomial


/-! ## The modular representation layer over a general field -/

abbrev repKernelField {K : Type u} [Field K] {G V : Type*} [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) : Subgroup G := ρ.ker

lemma repKernelField_eq_bot_iff {K : Type u} [Field K] {G V : Type*} [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) :
    repKernelField ρ = ⊥ ↔ Function.Injective ρ :=
  MonoidHom.ker_eq_bot_iff ρ

lemma mem_repKernelField_iff {K : Type u} [Field K] {G V : Type*} [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (g : G) :
    g ∈ repKernelField ρ ↔ ∀ v : V, ρ g v = v := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v
    rw [LinearMap.congr_fun h v]
    rfl
  · intro h
    exact LinearMap.ext h

/-- The subspace of vectors fixed by a subgroup, over a general field. -/
noncomputable def fixedByField {K : Type u} [Field K] {G V : Type*} [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (P : Subgroup G) : Submodule K V :=
  Representation.invariants (ρ.comp P.subtype)

lemma mem_fixedByField_iff {K : Type u} [Field K] {G V : Type*} [Group G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (P : Subgroup G) (v : V) :
    v ∈ fixedByField ρ P ↔ ∀ g ∈ P, ρ g v = v := by
  rw [fixedByField, Representation.mem_invariants]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

/-- **The fixed space of `O_p(G)` is nonzero**: `O_p(G)` is a `p`-group, and a `p`-group acting
`K`-linearly on a nonzero module in characteristic `p` has a nonzero fixed vector
(`Work.HallHigman.exists_ne_zero_fixed_of_isPGroup_field`). -/
theorem fixedByField_pCore_ne_bot {K : Type u} [Field K] {p : ℕ} [CharP K p] [Fact p.Prime]
    {G : Type v} [Group G] [Finite G] {V : Type w} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (hV : Nontrivial V) : fixedByField ρ (pCore p G) ≠ ⊥ := by
  intro hbot
  obtain ⟨u, hu, hfix⟩ := exists_ne_zero_fixed_of_isPGroup_field ρ isPGroup_pCore hV
  have hmem : u ∈ fixedByField ρ (pCore p G) := (mem_fixedByField_iff ρ (pCore p G) u).mpr hfix
  rw [hbot] at hmem
  exact hu (by simpa using hmem)

/-- **The fixed space of `O_p(G)` is proper**: if it were everything, `O_p(G)` would act trivially,
hence lie in the kernel of a faithful representation, contradicting `O_p(G) ≠ 1`. -/
theorem fixedByField_pCore_ne_top {K : Type u} [Field K] {p : ℕ} [Fact p.Prime]
    {G : Type v} [Group G] [Finite G] {V : Type w} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (hfaith : Function.Injective ρ) (hP : pCore p G ≠ ⊥) :
    fixedByField ρ (pCore p G) ≠ ⊤ := by
  intro htop
  have hle : pCore p G ≤ repKernelField ρ := by
    intro g hg
    rw [mem_repKernelField_iff]
    intro v
    have : v ∈ fixedByField ρ (pCore p G) := by rw [htop]; trivial
    exact (mem_fixedByField_iff ρ (pCore p G) v).mp this g hg
  have hbot : pCore p G ≤ ⊥ := by
    rw [← (repKernelField_eq_bot_iff ρ).mpr hfaith]
    exact hle
  exact hP (le_bot_iff.mp hbot)

/-! ## Field-general versions of the auxiliary lemmas (independent universes) -/

/-- If a faithful representation of a finite group over a field `K` of characteristic `p` satisfies
`(ρ x - 1) ^ 2 = 0`, then `x` has `p`-power order.  Field-general, universe-general version of
`Work.HallHigman.orderOf_eq_prime_pow_of_sq_sub_one_eq_zero`. -/
theorem orderOf_eq_prime_pow_of_sq_sub_one_eq_zero_univ {K : Type u} [Field K] {p : ℕ}
    [CharP K p] [Fact p.Prime] {G : Type v} {V : Type w} [Group G] [Finite G] [AddCommGroup V]
    [Module K V] (ρ : Representation K G V) (hfaith : Function.Injective ρ) {x : G}
    (h : (ρ x - 1) ^ 2 = 0) : ∃ n : ℕ, orderOf x = p ^ n := by
  have hp0 : (p : Module.End K V) = 0 := by
    have : (p : K) • (1 : Module.End K V) = (p : Module.End K V) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [← this, CharP.cast_eq_zero K p, zero_smul]
  have hap : (ρ x - 1) ^ p = 0 := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    exact pow_eq_zero_of_le hp2 h
  have hxpow : ρ x ^ p = 1 := by
    have hc := Commute.add_pow_prime_eq' (p := p) (Fact.out : p.Prime)
      (x := ρ x - 1) (y := 1) (Commute.one_right _)
    rw [sub_add_cancel, hap, one_pow] at hc
    rw [hp0, zero_mul] at hc
    simpa using hc
  have hxp : x ^ p = 1 := by
    apply hfaith
    rw [map_pow, hxpow, map_one]
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [hp, pow_one]⟩

/-- **The minimal polynomial of an element acting unipotently of index two on an invariant
subrepresentation** (field-general, universe-general version of
`Work.HallHigman.minpoly_subrepresentation_eq_sq`). -/
theorem minpoly_subrepresentation_eq_sq_field_univ {K : Type u} [Field K] {G : Type v}
    {M : Type w} [Group G] [AddCommGroup M] [Module K M] (ρ : Representation K G M)
    (W : Submodule K M) (hW : ∀ g, W ≤ W.comap (ρ g)) (x : G) (hsq : (ρ x - 1) ^ 2 = 0)
    (hne : (Representation.subrepresentation ρ W hW) x ≠ 1) :
    minpoly K ((Representation.subrepresentation ρ W hW) x) = (Polynomial.X - 1) ^ 2 := by
  apply minpoly_eq_X_sub_one_sq_of_sq_eq_zero
  · have hf : Set.MapsTo (⇑(ρ x)) (W : Set M) (W : Set M) := hW x
    have hg : Set.MapsTo (⇑(1 : Module.End K M)) (W : Set M) (W : Set M) :=
      fun w hw => by simpa using hw
    have hfg : Set.MapsTo (⇑((ρ x) - (1 : Module.End K M))) (W : Set M) (W : Set M) :=
      fun w hw => W.sub_mem (hf hw) (hg hw)
    have hpz : (((ρ x) - (1 : Module.End K M)).restrict hfg) ^ 2 = 0 :=
      Module.End.submodule_pow_eq_zero_of_pow_eq_zero (N := W)
        (g := ((ρ x) - (1 : Module.End K M)).restrict hfg)
        (G := (ρ x) - (1 : Module.End K M))
        (LinearMap.subtype_comp_restrict hfg).symm hsq
    have hres := LinearMap.restrict_sub hf hg (f := ρ x) (g := (1 : Module.End K M))
    have hone : (1 : Module.End K M).restrict hg = 1 := by
      ext w; simp [LinearMap.restrict]
    have hsub : (Representation.subrepresentation ρ W hW) x - 1
        = ((ρ x) - (1 : Module.End K M)).restrict hfg := by
      rw [Representation.subrepresentation_apply, ← hone]
      exact hres
    rw [hsub, hpz]
  · exact hne

/-- **The minimal polynomial of the map induced on a quotient representation** (field-general,
universe-general version of `Work.HallHigman.minpoly_quotient_eq_sq`). -/
theorem minpoly_quotient_eq_sq_field_univ {K : Type u} [Field K] {G : Type v} {M : Type w}
    [Group G] [AddCommGroup M] [Module K M] (ρ : Representation K G M) (W : Submodule K M)
    (hW : ∀ g, W ≤ W.comap (ρ g)) (x : G) (hsq : (ρ x - 1) ^ 2 = 0)
    (hne : (Representation.quotient ρ W hW) x ≠ 1) :
    minpoly K ((Representation.quotient ρ W hW) x) = (Polynomial.X - 1) ^ 2 := by
  have hq : (Representation.quotient ρ W hW) x = W.mapQ W (ρ x) (hW x) :=
    Representation.quotient_apply ρ W hW x
  have hmid : (((Representation.quotient ρ W hW) x) - 1).comp W.mkQ = W.mkQ.comp (ρ x - 1) := by
    rw [hq, LinearMap.sub_comp, LinearMap.comp_sub]
    simp only [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
    rw [Submodule.mapQ_mkQ W W (ρ x)]
  have hsq' : (((Representation.quotient ρ W hW) x) - 1) ^ 2 = 0 := by
    have key : ((((Representation.quotient ρ W hW) x) - 1) ^ 2).comp W.mkQ = 0 := by
      rw [pow_two, Module.End.mul_eq_comp]
      rw [LinearMap.comp_assoc, hmid]
      rw [← LinearMap.comp_assoc, hmid]
      rw [LinearMap.comp_assoc]
      rw [show (ρ x - 1).comp (ρ x - 1) = (ρ x - 1) ^ 2 by rw [pow_two, Module.End.mul_eq_comp]]
      rw [hsq, LinearMap.comp_zero]
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W z
    have h := LinearMap.congr_fun key v
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h
  exact minpoly_eq_X_sub_one_sq_of_sq_eq_zero hsq' hne

/-- **The final step of the proof of Feit--Thompson's Lemma 7.1** (field-general, universe-general
version of `Work.HallHigman.isPGroup_of_forall_pow_trivial_univ`). -/
theorem isPGroup_of_forall_pow_trivial_field_univ {K : Type u} [Field K] {p : ℕ} [CharP K p]
    [Fact p.Prime] {H : Type v} [Group H] [Finite H] {V : Type w} [AddCommGroup V] [Module K V]
    (ρ : Representation K H V) (hfaith : Function.Injective ρ) {Z : Submodule K V}
    {P : Subgroup H}
    (hZinv : ∀ y ∈ P, ∀ v ∈ Z, ρ y v ∈ Z)
    (hZ : ∀ y ∈ P, ∃ k : ℕ, ∀ v ∈ Z, ρ (y ^ p ^ k) v = v)
    (hQ : ∀ y ∈ P, ∃ k : ℕ, ∀ v : V, ρ (y ^ p ^ k) v - v ∈ Z) :
    IsPGroup p P := by
  rw [IsPGroup.iff_orderOf]
  intro y
  obtain ⟨kZ, hkZ⟩ := hZ y y.2
  obtain ⟨kQ, hkQ⟩ := hQ y y.2
  have hpowZ : ∀ (g : P) (m : ℕ), (∀ v ∈ Z, ρ (g : H) v = v) →
      ∀ v ∈ Z, ρ ((g : H) ^ m) v = v := by
    intro g m
    induction m with
    | zero => intro _ v _; simp
    | succ j ih =>
      intro hg v hv
      rw [pow_succ', map_mul, Module.End.mul_apply, ih hg v hv]
      exact hg v hv
  have hpowQ : ∀ (g : P) (m : ℕ), (∀ v : V, ρ (g : H) v - v ∈ Z) →
      ∀ v : V, ρ ((g : H) ^ m) v - v ∈ Z := by
    intro g m
    induction m with
    | zero => intro _ v; simp
    | succ j ih =>
      intro hg v
      have h1 : ρ (g : H) (ρ ((g : H) ^ j) v) - ρ (g : H) v ∈ Z := by
        have := hZinv g g.2 (ρ ((g : H) ^ j) v - v) (ih hg v)
        simpa [map_sub] using this
      have h2 : ρ (g : H) v - v ∈ Z := hg v
      have hsum := Z.add_mem h1 h2
      rw [pow_succ', map_mul, Module.End.mul_apply]
      convert hsum using 1
      abel
  obtain ⟨k, hk⟩ : ∃ k, kZ ≤ k ∧ kQ ≤ k := ⟨max kZ kQ, le_max_left _ _, le_max_right _ _⟩
  have hgf : (y : H) ^ p ^ k = ((y : H) ^ p ^ kZ) ^ p ^ (k - kZ) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.1]
  have hgq : (y : H) ^ p ^ k = ((y : H) ^ p ^ kQ) ^ p ^ (k - kQ) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.2]
  have hZtriv : ∀ v ∈ Z, ρ ((y : H) ^ p ^ k) v = v := by
    intro v hv
    rw [hgf]
    exact hpowZ ⟨(y : H) ^ p ^ kZ, P.pow_mem y.2 _⟩ (p ^ (k - kZ))
      (fun w hw => hkZ w hw) v hv
  have hQtriv : ∀ v : V, ρ ((y : H) ^ p ^ k) v - v ∈ Z := by
    intro v
    rw [hgq]
    exact hpowQ ⟨(y : H) ^ p ^ kQ, P.pow_mem y.2 _⟩ (p ^ (k - kQ)) (fun w => hkQ w) v
  have hunip : ((ρ.comp P.subtype) ⟨(y : H) ^ p ^ k, P.pow_mem y.2 _⟩ - 1) ^ 2 = 0 := by
    rw [pow_two]
    change ((ρ ((y : H) ^ p ^ k) - 1) * (ρ ((y : H) ^ p ^ k) - 1)) = 0
    refine LinearMap.ext fun v => ?_
    have h1 : ρ ((y : H) ^ p ^ k) v - v ∈ Z := hQtriv v
    have h2 : ρ ((y : H) ^ p ^ k) (ρ ((y : H) ^ p ^ k) v - v)
        = ρ ((y : H) ^ p ^ k) v - v := hZtriv _ h1
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply]
    rw [h2, sub_self]
  have hfaith' : Function.Injective (ρ.comp P.subtype) :=
    fun a b hab => Subtype.coe_injective (hfaith hab)
  obtain ⟨n, hn⟩ := orderOf_eq_prime_pow_of_sq_sub_one_eq_zero_univ (ρ.comp P.subtype) hfaith' hunip
  have hge : (⟨(y : H) ^ p ^ k, P.pow_mem y.2 _⟩ : P) = y ^ p ^ k := rfl
  rw [hge, orderOf_pow] at hn
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (Nat.gcd_dvd_right (orderOf y) (p ^ k))
  refine ⟨n + j, ?_⟩
  have hdiv := Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf y) (p ^ k))
  rw [hn, hj] at hdiv
  rw [← hdiv, pow_add]

end Work.HallHigman
