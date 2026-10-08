import Mathlib
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Step 4: the number of elements of order three

Let `G` be a finite group acting doubly transitively by conjugation on its involutions
(`DTInv G`), with a four-group (`HasFourGroup G`), such that `V = invSubgroup hDT h4` has
order `4` and `C_G(V)` is a 2-group.  Then

`{g : G | orderOf g = 3}` has cardinality `2 * |C_G(V)|`.

The proof is the one of Peterfalvi I §2, Step 4.  Since `V = {1} ∪ Inv(G)` has four elements
we may view the conjugation action of `G` on `V` as a permutation of the four-element type
`Fin 4`.  An element `g` with `g ^ 3 ∈ C_G(V)` and with `g` acting non-trivially on `V` acts
as a permutation of `Fin 4` of order dividing `3`, i.e. as a 3-cycle, and then no involution
centralises `g` (an involution of `V` fixed by a 3-cycle would force the 3-cycle to be trivial,
by `perm_fin4_eq_one_of_two_fixed`).  Hence `|C_G(g)|` is odd and `g ^ 3 ∈ C_G(g) ∩ C_G(V)`
forces `g ^ 3 = 1`: such a `g` has order `3`.  Conversely an element of order `3` acts
non-trivially (as `C_G(V)` is a 2-group) and hence as a 3-cycle
(`perm_fin4_eq_or_inv`).  So the elements of order `3` are exactly the two cosets of
`C_G(V)` lying over the two 3-cycles, whence the count.
-/

set_option autoImplicit false

namespace Work.Hering.Step4

open LeanEval.GroupTheory.Defs Work.Hering

/-! ## Permutation lemmas on four points -/

/-- A permutation of `Fin 4` whose cube is `1` and which fixes two distinct points is trivial. -/
theorem perm_fin4_eq_one_of_two_fixed (p : Equiv.Perm (Fin 4)) :
    ∀ x y : Fin 4, x ≠ y → p x = x → p y = y → p ^ 3 = 1 → p = 1 := by
  decide +revert

/-- Two non-trivial permutations of `Fin 4` with cube `1` fixing a common point are equal or
inverse. -/
theorem perm_fin4_eq_or_inv (p q : Equiv.Perm (Fin 4)) :
    ∀ x : Fin 4, p x = x → q x = x → p ^ 3 = 1 → q ^ 3 = 1 → p ≠ 1 → q ≠ 1 →
      q = p ∨ q = p⁻¹ := by
  decide +revert

/-! ## The conjugation action on a normal subgroup -/

/-- Conjugation by `g` as a permutation of the normal subgroup `V`. -/
noncomputable def conjPermV {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal) (g : G) :
    Equiv.Perm ↥V where
  toFun v := ⟨g * (v : G) * g⁻¹, hVn.conj_mem (v : G) v.2 g⟩
  invFun v := ⟨g⁻¹ * (v : G) * g, by simpa using hVn.conj_mem (v : G) v.2 g⁻¹⟩
  left_inv v := by
    apply Subtype.ext
    group
  right_inv v := by
    apply Subtype.ext
    group

@[simp] theorem conjPermV_apply {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal) (g : G)
    (v : ↥V) :
    conjPermV V hVn g v = ⟨g * (v : G) * g⁻¹, hVn.conj_mem (v : G) v.2 g⟩ := rfl

theorem conjPermV_mul {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal) (g h : G) :
    conjPermV V hVn (g * h) = conjPermV V hVn g * conjPermV V hVn h := by
  ext v
  simp only [conjPermV_apply, Equiv.Perm.mul_apply]
  group

theorem conjPermV_one {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal) :
    conjPermV V hVn 1 = 1 := by
  ext v
  simp

/-- The conjugation action of `G` on a normal subgroup `V`, as a group homomorphism into the
permutation group of `V`. -/
noncomputable def conjPermHom {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal) :
    G →* Equiv.Perm ↥V where
  toFun := conjPermV V hVn
  map_one' := conjPermV_one V hVn
  map_mul' := conjPermV_mul V hVn

@[simp] theorem conjPermHom_apply {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal) (g : G)
    (v : ↥V) :
    conjPermHom V hVn g v = ⟨g * (v : G) * g⁻¹, hVn.conj_mem (v : G) v.2 g⟩ := rfl

theorem conjPermHom_eq_one_iff {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal) (g : G) :
    conjPermHom V hVn g = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 : (conjPermHom V hVn g) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [h]; rfl
    have h3 : g * y * g⁻¹ = y := congrArg (fun z : ↥V => (z : G)) h2
    have h4 : g * y = y * g := by
      have := congrArg (· * g) h3
      simpa [mul_assoc] using this
    exact h4.symm
  · intro h
    ext v
    change g * (v : G) * g⁻¹ = (v : G)
    rw [Subgroup.mem_centralizer_iff] at h
    rw [← h (v : G) v.2]
    simp

/-! ## Transporting the action to `Fin 4` -/

theorem permCongrHom_apply {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) (x : β) :
    e.permCongr p x = e (p (e.symm x)) := rfl

theorem permCongrHom_eq_one_iff {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) :
    e.permCongr p = 1 ↔ p = 1 := by
  constructor
  · intro h
    ext y
    have h2 : e (p y) = e y := by
      have := congrArg (fun q : Equiv.Perm β => q (e y)) h
      simpa [permCongrHom_apply] using this
    exact e.injective h2
  · intro h
    rw [h]
    ext x
    simp

/-- The action of `G` by conjugation on an (`e`-indexed copy of a) four-element normal
subgroup `V`. -/
noncomputable def actHom {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal)
    (e : ↥V ≃ Fin 4) : G →* Equiv.Perm (Fin 4) where
  toFun g := e.permCongr (conjPermV V hVn g)
  map_one' := by
    rw [conjPermV_one, Equiv.Perm.one_def, Equiv.Perm.one_def, Equiv.permCongr_refl]
  map_mul' := by
    intro g h
    show e.permCongr (conjPermV V hVn (g * h)) =
      e.permCongr (conjPermV V hVn g) * e.permCongr (conjPermV V hVn h)
    rw [conjPermV_mul, Equiv.Perm.mul_def, ← Equiv.permCongr_trans, Equiv.Perm.mul_def]

theorem actHom_apply {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal)
    (e : ↥V ≃ Fin 4) (g : G) (v : ↥V) :
    actHom V hVn e g (e v) = e ⟨g * (v : G) * g⁻¹, hVn.conj_mem (v : G) v.2 g⟩ := by
  show e.permCongr (conjPermV V hVn g) (e v) = e ⟨g * (v : G) * g⁻¹, hVn.conj_mem (v : G) v.2 g⟩
  rw [permCongrHom_apply, Equiv.symm_apply_apply, conjPermV_apply]

theorem actHom_eq_one_iff {G : Type*} [Group G] (V : Subgroup G) (hVn : V.Normal)
    (e : ↥V ≃ Fin 4) (g : G) :
    actHom V hVn e g = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) := by
  show e.permCongr (conjPermHom V hVn g) = 1 ↔ _
  rw [permCongrHom_eq_one_iff, conjPermHom_eq_one_iff]

/-! ## The key step -/

theorem notMem_of_isPGroup_two {G : Type*} [Group G] {H : Subgroup G} (hH : IsPGroup 2 ↥H)
    {x : G} (hx : orderOf x = 3) : x ∉ H := by
  intro hxH
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hH) ⟨x, hxH⟩
  have hcoe : orderOf x = orderOf (⟨x, hxH⟩ : ↥H) :=
    Subgroup.orderOf_coe (⟨x, hxH⟩ : ↥H)
  have h2 : orderOf x = 2 ^ n := hcoe.trans hn
  rw [hx] at h2
  have h3n : (3 : ℕ) ∣ 2 ^ n := by rw [← h2]
  have hdvd : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3n
  norm_num at hdvd

theorem odd_card_centralizer {G : Type*} [Group G] [Finite G] {x : G}
    (h : ∀ t : G, orderOf t = 2 → t * x ≠ x * t) :
    Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hodd
  have ht2 : orderOf ((t : ↥(Subgroup.centralizer ({x} : Set G))) : G) = 2 := by
    rw [Subgroup.orderOf_coe t, ht]
  have hmem : ((t : ↥(Subgroup.centralizer ({x} : Set G))) : G) ∈
      Subgroup.centralizer ({x} : Set G) := t.2
  rw [Subgroup.mem_centralizer_iff] at hmem
  exact h t ht2 (hmem x (Set.mem_singleton x)).symm

/-- If an element `x` acts non-trivially on a four-element normal subgroup `V` (through the
`e`-indexed action) and `x ^ 3` acts trivially, then `x` has order `3`.  This is the heart of
Step 4: an involution centralising `x` would be a fixed point of the order-three permutation
`actHom V hVn e x` different from `1`, which is impossible. -/
theorem orderOf_eq_three_of_actHom {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hVn : V.Normal) (e : ↥V ≃ Fin 4) (hinv : ∀ t : G, orderOf t = 2 → t ∈ V)
    (hCp : IsPGroup 2 ↥(Subgroup.centralizer (V : Set G)))
    (x : G) (h3 : (actHom V hVn e x) ^ 3 = 1) (h1 : actHom V hVn e x ≠ 1) :
    orderOf x = 3 := by
  have hker : ∀ g : G, actHom V hVn e g = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) :=
    fun g => actHom_eq_one_iff V hVn e g
  have hx3C : x ^ 3 ∈ Subgroup.centralizer (V : Set G) := by
    refine (hker (x ^ 3)).mp ?_
    show actHom V hVn e (x ^ 3) = 1
    rw [map_pow, h3]
  have hnoinv : ∀ t : G, orderOf t = 2 → t * x ≠ x * t := by
    intro t ht hcomm
    have htV : t ∈ V := hinv t ht
    have hvt : (⟨t, htV⟩ : ↥V) ≠ ⟨1, V.one_mem⟩ := by
      intro hc
      exact ne_one_of_mem_involutions (show t ∈ involutions G from ht) (congrArg Subtype.val hc)
    have hxt : x * (⟨t, htV⟩ : ↥V) * x⁻¹ = (⟨t, htV⟩ : ↥V) := by
      rw [← hcomm]
      group
    have hfix : actHom V hVn e x (e ⟨t, htV⟩) = e ⟨t, htV⟩ := by
      rw [actHom_apply]
      exact congrArg e (Subtype.ext hxt)
    have hfixi : actHom V hVn e x (e ⟨1, V.one_mem⟩) = e ⟨1, V.one_mem⟩ := by
      rw [actHom_apply]
      exact congrArg e (Subtype.ext (by simp))
    exact h1 (perm_fin4_eq_one_of_two_fixed (actHom V hVn e x) (e ⟨t, htV⟩)
      (e ⟨1, V.one_mem⟩) (fun hc => hvt (e.injective hc)) hfix hfixi h3)
  have hodd : Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) := odd_card_centralizer hnoinv
  have hx3x : x ^ 3 ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    group
  have hdvd : orderOf (x ^ 3) ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.orderOf_dvd_natCard _ hx3x
  have hodd3 : Odd (orderOf (x ^ 3)) := Odd.of_dvd_nat hodd hdvd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hCp) ⟨x ^ 3, hx3C⟩
  have hcoe : orderOf (x ^ 3) = orderOf (⟨x ^ 3, hx3C⟩ : ↥(Subgroup.centralizer (V : Set G))) :=
    Subgroup.orderOf_coe (⟨x ^ 3, hx3C⟩ : ↥(Subgroup.centralizer (V : Set G)))
  have hn' : orderOf (x ^ 3) = 2 ^ n := hcoe.trans hn
  have hoddn : Odd (2 ^ n) := hn' ▸ hodd3
  have hn0 : n = 0 := by
    rcases n with _ | k
    · rfl
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hoddn) ⟨2 ^ k, by rw [pow_succ]; ring⟩
  have hx3one : x ^ 3 = 1 := by
    rw [← orderOf_eq_one_iff, hn', hn0, pow_zero]
  refine orderOf_eq_prime hx3one ?_
  intro hx1
  exact h1 (by rw [hx1, map_one])

/-! ## Counting the fibres of a homomorphism -/

theorem card_order_three_fibers {G M : Type*} [Group G] [Group M] [Finite G]
    (f : G →* M) {x₀ : G} (hne : f x₀ ≠ (f x₀)⁻¹)
    (hiff : ∀ g : G, orderOf g = 3 ↔ f g = f x₀ ∨ f g = (f x₀)⁻¹) :
    Nat.card {g : G // orderOf g = 3} = 2 * Nat.card ↥(MonoidHom.ker f) := by
  classical
  have hmem : ∀ k : ↥(MonoidHom.ker f), f (k : G) = 1 := fun k => MonoidHom.mem_ker.mp k.2
  let ψ : ↥(MonoidHom.ker f) ⊕ ↥(MonoidHom.ker f) → {g : G // orderOf g = 3} := fun s =>
    match s with
    | Sum.inl k => ⟨x₀ * (k : G), (hiff _).mpr (Or.inl (by rw [map_mul, hmem k, mul_one]))⟩
    | Sum.inr k => ⟨x₀⁻¹ * (k : G), (hiff _).mpr (Or.inr (by rw [map_mul, map_inv, hmem k, mul_one]))⟩
  have hψinj : Function.Injective ψ := by
    intro u v huv
    rcases u with k | k <;> rcases v with k' | k'
    · have h1 : x₀ * (k : G) = x₀ * (k' : G) := congrArg Subtype.val huv
      have h2 : (k : G) = (k' : G) := mul_left_cancel h1
      exact congrArg Sum.inl (Subtype.ext h2)
    · have h1 : x₀ * (k : G) = x₀⁻¹ * (k' : G) := congrArg Subtype.val huv
      have h2 : f x₀ = (f x₀)⁻¹ := by
        have := congrArg f h1
        simpa [map_mul, map_inv, hmem k, hmem k'] using this
      exact absurd h2 hne
    · have h1 : x₀⁻¹ * (k : G) = x₀ * (k' : G) := congrArg Subtype.val huv
      have h2 : (f x₀)⁻¹ = f x₀ := by
        have := congrArg f h1
        simpa [map_mul, map_inv, hmem k, hmem k'] using this
      exact absurd h2.symm hne
    · have h1 : x₀⁻¹ * (k : G) = x₀⁻¹ * (k' : G) := congrArg Subtype.val huv
      have h2 : (k : G) = (k' : G) := mul_left_cancel h1
      exact congrArg Sum.inr (Subtype.ext h2)
  have hψsurj : Function.Surjective ψ := by
    intro g
    rcases (hiff g).mp g.2 with hg | hg
    · refine ⟨Sum.inl ⟨x₀⁻¹ * g, ?_⟩, Subtype.ext ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hg, inv_mul_cancel]
      · show x₀ * (x₀⁻¹ * g) = g
        group
    · refine ⟨Sum.inr ⟨x₀ * g, ?_⟩, Subtype.ext ?_⟩
      · rw [MonoidHom.mem_ker, map_mul, hg, mul_inv_cancel]
      · show x₀⁻¹ * (x₀ * g) = g
        group
  have hcard := Nat.card_congr (Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
  rw [← hcard, Nat.card_sum, two_mul]

/-! ## Enumerating a four-element `invSubgroup` -/

/-- If `a ≠ b` are involutions and `V = invSubgroup hDT h4` has four elements, then
`V = {1, a, b, a * b}`. -/
theorem invSubgroup_eq_four {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G} {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b)
    (hV : Nat.card ↥(invSubgroup hDT h4) = 4) :
    (invSubgroup hDT h4 : Set G) = {1, a, b, a * b} := by
  classical
  have ha' : a ∈ involutions G := ha
  have hb' : b ∈ involutions G := hb
  have hab' : a * b ∈ involutions G := mul_mem_involutions_of_dtinv hDT h4 ha' hb' hab
  have hsub : ({1, a, b, a * b} : Set G) ⊆ (invSubgroup hDT h4 : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (invSubgroup hDT h4).one_mem
    · exact involutions_subset_invSubgroup hDT h4 ha'
    · exact involutions_subset_invSubgroup hDT h4 hb'
    · exact involutions_subset_invSubgroup hDT h4 hab'
  have ha1 : a ≠ 1 := ne_one_of_mem_involutions ha'
  have hb1 : b ≠ 1 := ne_one_of_mem_involutions hb'
  have hab1 : a * b ≠ 1 := ne_one_of_mem_involutions hab'
  have haba : a * b ≠ a := mul_ne_left_of_dtinv hDT h4 ha' hb' hab
  have habb : a * b ≠ b := by
    have h := mul_ne_left_of_dtinv hDT h4 hb' ha' (Ne.symm hab)
    rwa [← comm_of_dtinv hDT h4 a b ha hb] at h
  have hcardS : ({1, a, b, a * b} : Set G).ncard = 4 := by
    have hF : ({1, a, b, a * b} : Finset G).card = 4 := by
      have h1 : (1 : G) ∉ ({a, b, a * b} : Finset G) := by
        simp [ha1.symm, hb1.symm, hab1.symm]
      have h2 : a ∉ ({b, a * b} : Finset G) := by
        simp [hab, haba.symm]
      have h3 : b ∉ ({a * b} : Finset G) := by
        simp [habb.symm]
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton]
    have hcoe : ({1, a, b, a * b} : Set G) = ↑({1, a, b, a * b} : Finset G) := by
      ext x
      simp
    rw [hcoe, Set.ncard_coe_finset, hF]
  have hcardV : (invSubgroup hDT h4 : Set G).ncard = 4 := hV
  exact (Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hcardV, hcardS]))).symm

/-! ## The auxiliary counting lemma -/

/-- The main content of Step 4, abstracted from `V = invSubgroup hDT h4`. -/
theorem count_order_three_aux {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hVn : V.Normal) (hinv : ∀ t : G, orderOf t = 2 → t ∈ V) (hVcard : Nat.card ↥V = 4)
    (hCp : IsPGroup 2 ↥(Subgroup.centralizer (V : Set G)))
    (x0 : G) (hx0 : orderOf x0 = 3) :
    Nat.card {g : G // orderOf g = 3} = 2 * Nat.card ↥(Subgroup.centralizer (V : Set G)) := by
  classical
  haveI : Fintype ↥V := Fintype.ofFinite ↥V
  have hcard4 : Fintype.card ↥V = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hVcard
  let e : ↥V ≃ Fin 4 := (Fintype.equivFin ↥V).trans (finCongr hcard4)
  let Ψ : G →* Equiv.Perm (Fin 4) := actHom V hVn e
  have hker : ∀ g : G, Ψ g = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) := fun g =>
    actHom_eq_one_iff V hVn e g
  have hfix : ∀ y : G, Ψ y (e ⟨1, V.one_mem⟩) = e ⟨1, V.one_mem⟩ := by
    intro y
    show actHom V hVn e y (e ⟨1, V.one_mem⟩) = e ⟨1, V.one_mem⟩
    rw [actHom_apply]
    exact congrArg e (Subtype.ext (by simp))
  have hx0p3 : x0 ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hx0])
  have hx0C : x0 ∉ Subgroup.centralizer (V : Set G) := notMem_of_isPGroup_two hCp hx0
  have hΨ0 : Ψ x0 ≠ 1 := fun h => hx0C ((hker x0).mp h)
  have hΨ03 : (Ψ x0) ^ 3 = 1 := by rw [← map_pow, hx0p3, map_one]
  have hiff : ∀ g : G, orderOf g = 3 ↔ Ψ g = Ψ x0 ∨ Ψ g = (Ψ x0)⁻¹ := by
    intro g
    constructor
    · intro hg
      have hg3 : g ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hg])
      have hgΨ : Ψ g ≠ 1 := fun h => notMem_of_isPGroup_two hCp hg ((hker g).mp h)
      have hg3' : (Ψ g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
      exact perm_fin4_eq_or_inv (Ψ x0) (Ψ g) (e ⟨1, V.one_mem⟩)
        (hfix x0) (hfix g) hΨ03 hg3' hΨ0 hgΨ
    · intro h
      rcases h with h | h
      · exact orderOf_eq_three_of_actHom hVn e hinv hCp g (by rw [h, hΨ03])
          (by rw [h]; exact hΨ0)
      · exact orderOf_eq_three_of_actHom hVn e hinv hCp g
          (by rw [h, inv_pow, hΨ03, inv_one])
          (by rw [h]; intro hc; exact hΨ0 (inv_eq_one.mp hc))
  have hne : Ψ x0 ≠ (Ψ x0)⁻¹ := by
    intro h
    have h2 : (Ψ x0) ^ 2 = 1 := by
      have hh : (Ψ x0) * (Ψ x0) = (Ψ x0) * (Ψ x0)⁻¹ := congrArg (fun t => (Ψ x0) * t) h
      rw [mul_inv_cancel] at hh
      rwa [pow_two]
    have hdvd2 : orderOf (Ψ x0) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hdvd3 : orderOf (Ψ x0) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hΨ03
    have hdvd1 : orderOf (Ψ x0) ∣ 1 := by
      have := Nat.dvd_gcd hdvd2 hdvd3
      simpa using this
    exact hΨ0 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1))
  have hcount := card_order_three_fibers Ψ hne hiff
  have hkereq : MonoidHom.ker Ψ = Subgroup.centralizer (V : Set G) := by
    ext g
    rw [MonoidHom.mem_ker, hker g]
  rw [hcount, hkereq]

/-! ## The theorem -/

/-- With `|V| = 4` and `C_G(V)` a 2-group, the elements of order `3` are exactly the two cosets of
`C_G(V)` consisting of the elements acting on `V` by a 3-cycle: such an element acts fixed-point
freely on `V`, so its centraliser has odd order, and then `g ^ 3 ∈ C_G(V)` forces `g ^ 3 = 1`.
Hence there are `2 * |C_G(V)|` elements of order `3`. -/
theorem count_order_three {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G}
    (hC : ∀ U : Subgroup G, U ≤ invSubgroup hDT h4 → Nat.card U = 4 →
      IsPGroup 2 ↥(Subgroup.centralizer (U : Set G)))
    (hV : Nat.card ↥(invSubgroup hDT h4) = 4) :
    Nat.card {g : G // orderOf g = 3}
      = 2 * Nat.card ↥(Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype ↥(invSubgroup hDT h4) := Fintype.ofFinite ↥(invSubgroup hDT h4)
  have h4c : HasFourGroup G := h4
  obtain ⟨a, b, ha, hb, hab, habc⟩ := h4c
  have haV : a ∈ (invSubgroup hDT h4 : Set G) :=
    involutions_subset_invSubgroup hDT h4 (show a ∈ involutions G from ha)
  have hbV : b ∈ (invSubgroup hDT h4 : Set G) :=
    involutions_subset_invSubgroup hDT h4 (show b ∈ involutions G from hb)
  have hVenum : ((invSubgroup hDT h4 : Subgroup G) : Set G) = {1, a, b, a * b} :=
    invSubgroup_eq_four ha hb hab hV
  have hcard4 : Fintype.card ↥(invSubgroup hDT h4) = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hV
  let e : ↥(invSubgroup hDT h4) ≃ Fin 4 :=
    (Fintype.equivFin ↥(invSubgroup hDT h4)).trans (finCongr hcard4)
  have hc : orderOf (a * b) = 2 := mul_mem_involutions_of_dtinv hDT h4 ha hb hab
  have hca : a * b ≠ a := mul_ne_left_of_dtinv hDT h4 ha hb hab
  have hcb : a * b ≠ b := by
    have h := mul_ne_left_of_dtinv hDT h4 hb ha (Ne.symm hab)
    rwa [← habc] at h
  obtain ⟨g, hga, hgb⟩ := hDT a b b (a * b) ha hb hb hc hab (Ne.symm hcb)
  have hgc : g * (a * b) * g⁻¹ = a := by
    have e1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e1, hga, hgb]
    rw [habc, ← mul_assoc, sq_eq_one_of_orderOf_eq_two hb, one_mul]
  have hg3a : g ^ 3 * a * (g ^ 3)⁻¹ = a := by
    have e1 : g ^ 3 * a * (g ^ 3)⁻¹ = g * (g * (g * a * g⁻¹) * g⁻¹) * g⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e1, hga, hgb, hgc]
  have hg3b : g ^ 3 * b * (g ^ 3)⁻¹ = b := by
    have e1 : g ^ 3 * b * (g ^ 3)⁻¹ = g * (g * (g * b * g⁻¹) * g⁻¹) * g⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e1, hgb, hgc, hga]
  have hg3c : g ^ 3 * (a * b) * (g ^ 3)⁻¹ = a * b := by
    have e1 : g ^ 3 * (a * b) * (g ^ 3)⁻¹ =
        g * (g * (g * (a * b) * g⁻¹) * g⁻¹) * g⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e1, hgc, hga, hgb]
  have hconj : ∀ v : G, v ∈ ({1, a, b, a * b} : Set G) → g ^ 3 * v * (g ^ 3)⁻¹ = v := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact hg3a
    · exact hg3b
    · exact hg3c
  have hg3C : g ^ 3 ∈ Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ ({1, a, b, a * b} : Set G) := hVenum ▸ hv
    have h := hconj v hv'
    have h1 : g ^ 3 * v * (g ^ 3)⁻¹ * g ^ 3 = g ^ 3 * v := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    exact (congrArg (· * g ^ 3) h).symm.trans h1
  have hΨ3 : (actHom (invSubgroup hDT h4) (invSubgroup_normal hDT h4) e g) ^ 3 = 1 := by
    rw [← map_pow]
    exact (actHom_eq_one_iff _ _ e (g ^ 3)).mpr hg3C
  have hΨne : actHom (invSubgroup hDT h4) (invSubgroup_normal hDT h4) e g ≠ 1 := by
    intro h1eq
    have happ : actHom (invSubgroup hDT h4) (invSubgroup_normal hDT h4) e g (e ⟨a, haV⟩) =
        e ⟨b, hbV⟩ := by
      rw [actHom_apply]
      exact congrArg e (Subtype.ext hga)
    have hcomp : actHom (invSubgroup hDT h4) (invSubgroup_normal hDT h4) e g (e ⟨a, haV⟩) =
        e ⟨a, haV⟩ := by
      have := congrArg (fun p : Equiv.Perm (Fin 4) => p (e ⟨a, haV⟩)) h1eq
      simpa using this
    have hne' : e ⟨a, haV⟩ ≠ e ⟨b, hbV⟩ := fun h =>
      hab (congrArg Subtype.val (e.injective h))
    exact hne' (hcomp.symm.trans happ)
  have hg3 : orderOf g = 3 :=
    orderOf_eq_three_of_actHom (invSubgroup_normal hDT h4) e
      (fun t ht => involutions_subset_invSubgroup hDT h4 ht)
      (hC (invSubgroup hDT h4) le_rfl hV) g hΨ3 hΨne
  exact count_order_three_aux (invSubgroup_normal hDT h4)
    (fun t ht => involutions_subset_invSubgroup hDT h4 ht) hV
    (hC (invSubgroup hDT h4) le_rfl hV) g hg3

end Work.Hering.Step4
