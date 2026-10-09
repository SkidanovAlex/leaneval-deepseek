import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `H²`-capture for a finite cyclic group

Let `N` be a finite cyclic group, `A, B : Rep ℤ N` and `Φ : A ⟶ B` a morphism of representations.
If every `N`-invariant element of `A` is mapped by `Φ` into the image of the norm endomorphism
`N_B = ∑_{n : N} ρ_B(n)` of `B`, then the induced map `H²(N, A) ⟶ H²(N, B)` is zero.

The proof is the classical description of `H²` of a cyclic group.  For a generator `g` of `N`,
the *transgression* of a `2`-cocycle `z` is `T(z) = ∑_{t<|N|} z(g^t, g)`; it is a `g`-invariant
element of the module, and `T` is compatible with morphisms of representations.  If
`T(z) ∈ range N_B` then the explicit cochain
`u ↦ z(1,1) - ∑_{t < idx u} (ρ(g^t) b + z(g^t, g))`
(where `b` is a preimage of `-T(z)` under the norm and `idx` is a canonical exponent of `u`)
has coboundary `z`, so that `Φ ∘ z` is a coboundary as soon as `Φ(T(z)) ∈ range N_B`.

## Main results

* `NK.Cohomology.transgression_mem_invariants`
* `NK.Cohomology.mem_coboundaries₂_of_transgression_mem_range`
* `NK.Cohomology.capture_two_map_eq_zero_of_cyclic`
-/

namespace NK.Cohomology

open CategoryTheory Representation groupCohomology Rep

-- Prefer the `Module`/`AddCommGroup` structures coming from a representation over the generic
-- `ℤ`-module structure, so that the `Rep ℤ G`-diamonds do not produce `isDefEq` failures.
attribute [local instance 5000] Rep.hV1 Rep.hV2
-- Prefer the specific `ℤ`-module structures (from a representation, a Pi type, a submodule, …) over
-- the generic `Module ℤ`-structure induced by `AddCommGroup`.
attribute [local instance 100] AddCommGroup.toIntModule

set_option maxHeartbeats 4000000

section CyclicAux

variable {G : Type} [Group G] [Fintype G]

/-- The powers of a generator of a finite cyclic group are injective on `{0, …, |G|-1}`. -/
private lemma pow_injOn (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Set.InjOn (fun t : ℕ => g ^ t) ↑(Finset.range (Fintype.card G)) := by
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  intro a ha b hb hab
  have h1 : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hab
  rw [hord] at h1
  exact Nat.ModEq.eq_of_lt_of_lt h1 (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)

/-- The powers of a generator of a finite cyclic group enumerate the group. -/
private lemma pow_image_eq_univ [DecidableEq G] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finset.image (fun t : ℕ => g ^ t) (Finset.range (Fintype.card G)) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn (pow_injOn g hg), Finset.card_range]

/-- Summation over the first `|G|` powers of a generator is summation over the group. -/
private lemma sum_range_pow_eq_sum (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {M : Type*} [AddCommMonoid M] (f : G → M) :
    (∑ t ∈ Finset.range (Fintype.card G), f (g ^ t)) = ∑ x : G, f x := by
  classical
  rw [← Finset.sum_image (pow_injOn g hg), pow_image_eq_univ g hg]

/-- Reindexing a sum over the group by left multiplication. -/
private lemma sum_mulLeft {M : Type*} [AddCommMonoid M] (a : G) (f : G → M) :
    (∑ x : G, f (a * x)) = ∑ x : G, f x := by
  simpa using Equiv.sum_comp (Equiv.mulLeft a) f

/-- A `n`-periodic sequence: shifting the range by one does not change the sum. -/
private lemma sum_range_shift {M : Type*} [AddCommGroup M] (f : ℕ → M) (n : ℕ)
    (h : f 0 = f n) :
    (∑ t ∈ Finset.range n, f (t + 1)) = ∑ t ∈ Finset.range n, f t := by
  have h1 : (∑ t ∈ Finset.range n, (f (t + 1) - f t)) = f n - f 0 := Finset.sum_range_sub f n
  rw [Finset.sum_sub_distrib, h, sub_self] at h1
  exact sub_eq_zero.mp h1

/-- **The transgression of a `2`-cocycle is invariant.** -/
theorem transgression_mem_invariants (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {k : Type} [CommRing k] (A : Rep k G) (z : cocycles₂ A) :
    (∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g)) ∈ A.ρ.invariants := by
  rw [Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg]
  have hgn : g ^ Fintype.card G = 1 := pow_card_eq_one
  have hcyc : ∀ t : ℕ, A.ρ g (z (g ^ t, g))
      = z (g ^ (t + 1), g) + z (g, g ^ t) - z (g, g ^ (t + 1)) := by
    intro t
    have h := (mem_cocycles₂_iff (⇑z)).mp z.2 g (g ^ t) g
    rw [← pow_succ', ← pow_succ] at h
    rw [eq_sub_iff_add_eq]
    exact h.symm
  have hshift1 : (∑ t ∈ Finset.range (Fintype.card G), z (g ^ (t + 1), g))
      = ∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g) :=
    sum_range_shift (fun t => z (g ^ t, g)) _ (by rw [hgn]; simp)
  have hshift2 : (∑ t ∈ Finset.range (Fintype.card G), z (g, g ^ (t + 1)))
      = ∑ t ∈ Finset.range (Fintype.card G), z (g, g ^ t) :=
    sum_range_shift (fun t => z (g, g ^ t)) _ (by rw [hgn]; simp)
  calc A.ρ g (∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g))
      = ∑ t ∈ Finset.range (Fintype.card G), A.ρ g (z (g ^ t, g)) := map_sum _ _ _
    _ = ∑ t ∈ Finset.range (Fintype.card G),
          (z (g ^ (t + 1), g) + z (g, g ^ t) - z (g, g ^ (t + 1))) :=
        Finset.sum_congr rfl (fun t _ => hcyc t)
    _ = ∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hshift1, hshift2]
        abel

end CyclicAux

section Crux

variable {G : Type} [Group G] [Fintype G]

/-- **The transgression criterion.**  For a finite cyclic group `G` with generator `g` and a
`2`-cocycle `z` of `A : Rep k G`, if the transgression `∑_{t<|G|} z (g^t, g)` lies in the image of
the norm endomorphism `A.ρ.norm = ∑_{γ : G} A.ρ γ`, then `z` is a coboundary. -/
theorem mem_coboundaries₂_of_transgression_mem_range
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {k : Type} [CommRing k] (A : Rep k G) (z : cocycles₂ A)
    (hT : (∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g)) ∈ LinearMap.range A.ρ.norm) :
    (⇑z : G × G → A.V) ∈ coboundaries₂ A := by
  classical
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hgn : g ^ Fintype.card G = 1 := pow_card_eq_one
  have hcyc := fun a b c : G => (mem_cocycles₂_iff (⇑z)).mp z.2 a b c
  -- invariance of the transgression
  have hTinv : (∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g)) ∈ A.ρ.invariants :=
    transgression_mem_invariants g hg A z
  have hTfix : ∀ m : ℕ, A.ρ (g ^ m) (∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g))
      = ∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g) :=
    fun m => (Representation.mem_invariants A.ρ _).mp hTinv (g ^ m)
  obtain ⟨b₀, hb₀⟩ := hT
  set b : A.V := -b₀ with hbdef
  have hb : A.ρ.norm b = -(∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g)) := by
    rw [hbdef, map_neg, hb₀]
  -- the auxiliary sequence
  set P : ℕ → A.V :=
    fun m => ∑ t ∈ Finset.range m, (A.ρ (g ^ t) b + z (g ^ t, g)) with hPdef
  -- `P` is periodic with period `|G|`
  have hPadd : ∀ m : ℕ, P (m + Fintype.card G) = P m := by
    intro m
    have hsplit : P (m + Fintype.card G)
        = P m + ∑ u ∈ Finset.range (Fintype.card G),
            (A.ρ (g ^ (m + u)) b + z (g ^ (m + u), g)) := by
      rw [hPdef]
      dsimp only
      rw [Finset.sum_range_add]
    rw [hsplit]
    have h1 : (∑ u ∈ Finset.range (Fintype.card G), A.ρ (g ^ (m + u)) b)
        = A.ρ (g ^ m) (A.ρ.norm b) := by
      have hstep : ∀ u : ℕ, A.ρ (g ^ (m + u)) b = A.ρ (g ^ m) (A.ρ (g ^ u) b) := by
        intro u
        rw [pow_add, Rep.ρ_mul, LinearMap.comp_apply]
      rw [Finset.sum_congr rfl (fun u _ => hstep u), ← map_sum]
      congr 1
      rw [show A.ρ.norm b = ∑ x : G, A.ρ x b from by
        rw [Representation.norm, LinearMap.sum_apply]]
      exact sum_range_pow_eq_sum g hg (fun x => A.ρ x b)
    have h2 : (∑ u ∈ Finset.range (Fintype.card G), z (g ^ (m + u), g))
        = ∑ t ∈ Finset.range (Fintype.card G), z (g ^ t, g) := by
      have hstep : ∀ u : ℕ, z (g ^ (m + u), g) = z (g ^ m * g ^ u, g) := by
        intro u
        rw [pow_add]
      rw [Finset.sum_congr rfl (fun u _ => hstep u),
        sum_range_pow_eq_sum g hg (fun x => z (g ^ m * x, g)),
        sum_mulLeft (g ^ m) (fun x : G => z (x, g)),
        ← sum_range_pow_eq_sum g hg (fun x => z (x, g))]
    rw [Finset.sum_add_distrib, h1, h2, hb, map_neg, hTfix m, neg_add_cancel, add_zero]
  -- periodicity in the form needed for exponents
  have hPmul : ∀ m k : ℕ, P (m + Fintype.card G * k) = P m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show m + Fintype.card G * (k + 1) = (m + Fintype.card G * k) + Fintype.card G by
          ring, hPadd, ih]
  have hPmod : ∀ a c : ℕ, a ≡ c [MOD Fintype.card G] → P a = P c := by
    intro a c h
    have hmod : a % Fintype.card G = c % Fintype.card G := h
    have ha : P a = P (a % Fintype.card G) := by
      conv_lhs => rw [show a = a % Fintype.card G + Fintype.card G * (a / Fintype.card G) from
        (Nat.mod_add_div a (Fintype.card G)).symm]
      exact hPmul (a % Fintype.card G) (a / Fintype.card G)
    have hc : P c = P (c % Fintype.card G) := by
      conv_lhs => rw [show c = c % Fintype.card G + Fintype.card G * (c / Fintype.card G) from
        (Nat.mod_add_div c (Fintype.card G)).symm]
      exact hPmul (c % Fintype.card G) (c / Fintype.card G)
    rw [ha, hc, hmod]
  -- canonical exponents
  have h_exists : ∀ x : G, ∃ i : ℕ, i < Fintype.card G ∧ g ^ i = x := by
    intro x
    have hmem : x ∈ Finset.image (fun t : ℕ => g ^ t) (Finset.range (Fintype.card G)) := by
      rw [pow_image_eq_univ g hg]
      exact Finset.mem_univ x
    obtain ⟨t, ht, ht'⟩ := Finset.mem_image.mp hmem
    exact ⟨t, Finset.mem_range.mp ht, ht'⟩
  let idx : G → ℕ := fun x => Classical.choose (h_exists x)
  have hpow_idx : ∀ x : G, g ^ idx x = x := fun x => (Classical.choose_spec (h_exists x)).2
  have hidxP : ∀ m : ℕ, P (idx (g ^ m)) = P m := by
    intro m
    have h1 : idx (g ^ m) ≡ m [MOD orderOf g] := pow_eq_pow_iff_modEq.mp (hpow_idx (g ^ m))
    rw [hord] at h1
    exact hPmod _ _ h1
  -- the coboundary
  let x : G → A.V := fun u => z (1, 1) - P (idx u)
  refine LinearMap.mem_range.mpr ⟨x, ?_⟩
  ext p
  obtain ⟨u, v⟩ := p
  rw [show (d₁₂ A).hom x (u, v) = A.ρ u (x v) - x (u * v) + x u from d₁₂_hom_apply A x (u, v)]
  have key : ∀ i j : ℕ, A.ρ (g ^ i) (x (g ^ j)) - x (g ^ i * g ^ j) + x (g ^ i)
      = z (g ^ i, g ^ j) := by
    intro i j
    -- the algebraic core
    have hPij : P (i + j)
        = P i + ∑ t ∈ Finset.range j, (A.ρ (g ^ (i + t)) b + z (g ^ (i + t), g)) := by
      rw [hPdef]
      dsimp only
      rw [Finset.sum_range_add]
    have hρPj : A.ρ (g ^ i) (P j)
        = ∑ t ∈ Finset.range j, (A.ρ (g ^ (i + t)) b + A.ρ (g ^ i) (z (g ^ t, g))) := by
      rw [hPdef]
      dsimp only
      rw [map_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [map_add]
      congr 1
      rw [← LinearMap.comp_apply, ← Rep.ρ_mul, pow_add]
    have hsub : A.ρ (g ^ i) (P j) - P (i + j) + P i
        = ∑ t ∈ Finset.range j, (A.ρ (g ^ i) (z (g ^ t, g)) - z (g ^ (i + t), g)) := by
      rw [Finset.sum_sub_distrib, hρPj, hPij, Finset.sum_add_distrib, Finset.sum_add_distrib]
      abel
    have hterm : ∀ t : ℕ, A.ρ (g ^ i) (z (g ^ t, g)) - z (g ^ (i + t), g)
        = z (g ^ i, g ^ t) - z (g ^ i, g ^ (t + 1)) := by
      intro t
      have h := hcyc (g ^ i) (g ^ t) g
      rw [← pow_add, ← pow_succ] at h
      have h' : A.ρ (g ^ i) (z (g ^ t, g))
          = z (g ^ (i + t), g) + z (g ^ i, g ^ t) - z (g ^ i, g ^ (t + 1)) := by
        rw [eq_sub_iff_add_eq]
        exact h.symm
      rw [h']
      abel
    have hzi : z (g ^ i, 1) = A.ρ (g ^ i) (z (1, 1)) := by
      have h := hcyc (g ^ i) 1 1
      simp only [mul_one] at h
      exact add_right_cancel h
    have htele : (∑ t ∈ Finset.range j, (A.ρ (g ^ i) (z (g ^ t, g)) - z (g ^ (i + t), g)))
        = z (g ^ i, 1) - z (g ^ i, g ^ j) := by
      rw [Finset.sum_congr rfl (fun t _ => hterm t),
        Finset.sum_range_sub' (fun t => z (g ^ i, g ^ t)) j]
      rw [pow_zero]
    have hmain : P (i + j) - P i - A.ρ (g ^ i) (P j)
        = z (g ^ i, g ^ j) - A.ρ (g ^ i) (z (1, 1)) := by
      have hneg : P (i + j) - P i - A.ρ (g ^ i) (P j)
          = -(A.ρ (g ^ i) (P j) - P (i + j) + P i) := by abel
      rw [hneg, hsub, htele, hzi]
      abel
    have h1 : x (g ^ j) = z (1, 1) - P j := by
      show z (1, 1) - P (idx (g ^ j)) = z (1, 1) - P j
      rw [hidxP j]
    have h2 : x (g ^ i * g ^ j) = z (1, 1) - P (i + j) := by
      rw [← pow_add]
      show z (1, 1) - P (idx (g ^ (i + j))) = z (1, 1) - P (i + j)
      rw [hidxP (i + j)]
    have h3 : x (g ^ i) = z (1, 1) - P i := by
      show z (1, 1) - P (idx (g ^ i)) = z (1, 1) - P i
      rw [hidxP i]
    rw [h1, h2, h3, map_sub]
    have key2 : A.ρ (g ^ i) (z (1, 1)) - A.ρ (g ^ i) (P j) - (z (1, 1) - P (i + j))
        + (z (1, 1) - P i)
        = -(A.ρ (g ^ i) (P j) - P (i + j) + P i) + A.ρ (g ^ i) (z (1, 1)) := by abel
    have hneg2 : -(A.ρ (g ^ i) (P j) - P (i + j) + P i)
        = z (g ^ i, g ^ j) - A.ρ (g ^ i) (z (1, 1)) := by
      rw [show -(A.ρ (g ^ i) (P j) - P (i + j) + P i)
          = P (i + j) - P i - A.ρ (g ^ i) (P j) from by abel, hmain]
    rw [key2, hneg2]
    abel
  have := key (idx u) (idx v)
  rwa [hpow_idx u, hpow_idx v] at this

end Crux

/-- **The `H²`-capture for a finite cyclic group.**  If every invariant element of `A` is mapped by
`Φ` into the norm group of `B`, then the induced map on second cohomology is zero. -/
theorem capture_two_map_eq_zero_of_cyclic
    {N : Type} [Group N] [Fintype N] [IsCyclic N]
    {A B : Rep ℤ N} (Φ : A ⟶ B)
    (h : ∀ a : A.V, (∀ g : N, A.ρ g a = a) → ∃ b : B.V, (Rep.norm B).hom b = Φ.hom a) :
    groupCohomology.map (MonoidHom.id N) Φ 2 = 0 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := N)
  have hcapture : ∀ z : cocycles₂ A, (fun p : N × N => Φ.hom (z p)) ∈ coboundaries₂ B := by
    intro z
    have hTinv : (∑ t ∈ Finset.range (Fintype.card N), z (g ^ t, g)) ∈ A.ρ.invariants :=
      transgression_mem_invariants g hg A z
    obtain ⟨b, hb⟩ := h (∑ t ∈ Finset.range (Fintype.card N), z (g ^ t, g))
      (fun g' => (Representation.mem_invariants A.ρ _).mp hTinv g')
    have hzB : (fun p : N × N => Φ.hom (z p)) ∈ cocycles₂ B := by
      rw [mem_cocycles₂_iff]
      intro a b c
      have h1 := (mem_cocycles₂_iff (⇑z)).mp z.2 a b c
      rw [← map_add, h1, map_add, Rep.hom_comm_apply]
    have hT : (∑ t ∈ Finset.range (Fintype.card N),
          (fun p : N × N => Φ.hom (z p)) (g ^ t, g))
        = Φ.hom (∑ t ∈ Finset.range (Fintype.card N), z (g ^ t, g)) := by
      rw [map_sum]
    refine mem_coboundaries₂_of_transgression_mem_range g hg B
      ⟨fun p => Φ.hom (z p), hzB⟩ ?_
    change (∑ t ∈ Finset.range (Fintype.card N),
          (fun p : N × N => Φ.hom (z p)) (g ^ t, g)) ∈ LinearMap.range B.ρ.norm
    rw [hT]
    exact ⟨b, by rw [← Rep.norm_apply]; exact hb⟩
  refine (cancel_epi (H2π A)).mp ?_
  rw [H2π_comp_map, Limits.comp_zero]
  apply ModuleCat.hom_ext
  ext z
  show (H2π B) ((mapCocycles₂ (MonoidHom.id N) Φ) z) = 0
  rw [H2π_eq_zero_iff, coe_mapCocycles₂]
  have hcoe : (cochainsMap₂ (MonoidHom.id N) Φ) ⇑z = fun p : N × N => Φ.hom (z p) := by
    funext p
    simp [cochainsMap₂]
  rw [hcoe]
  exact hcapture z

end NK.Cohomology
