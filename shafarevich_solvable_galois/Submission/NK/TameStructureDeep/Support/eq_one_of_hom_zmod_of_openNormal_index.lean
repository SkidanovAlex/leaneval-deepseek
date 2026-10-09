import Mathlib
import Submission.NK.TameStructureDeep.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.TameStructureDeep.Support

/-- **A pro-`p` group has no `ℓ`-torsion quotient, `ℓ ≠ p`.**

Let `A` be a compact, Hausdorff, totally disconnected topological abelian group in which every
open normal subgroup has index a power of `p`.  If `ℓ` is a prime different from `p`, then every
group homomorphism `A →* Multiplicative (ZMod ℓ)` is trivial.  In other words: the abstract group
`A` has no quotient of order `ℓ`.

The proof has two steps, neither of which uses continuity of `φ` (which is not assumed).

* **No `ℓ`-torsion in a finite quotient.**  Let `U` be an open normal subgroup, so that
  `B = A ⧸ U` is finite of order `p ^ k`.  If `x ∈ B` satisfied `x ^ ℓ = 1` and `x ≠ 1`, then
  `K = ⟨x⟩` would have order `ℓ`; pulling `K` back along `A ↠ B` gives an open normal subgroup
  `V ≤ A` with `[A : V] = [B : K]`, a power of `p`.  Lagrange's theorem reads
  `p ^ j * ℓ = p ^ k`, which — as `ℓ` is prime and `p ≥ 2` — forces `p = ℓ`, contradicting
  `ℓ ≠ p`.

* **Every element of `A` is an `ℓ`-th power.**  Since the `ℓ`-power map is injective on each
  finite quotient `B = A ⧸ U`, it is surjective there, i.e. for every `a : A` and every open
  normal `U` there is `b` with `b ^ ℓ ≡ a (mod U)`.  The image `R` of the continuous `ℓ`-power
  map `A → A` is closed (it is compact, `A` being Hausdorff), and meets every coset `aU`; hence
  `R = A`.

Finally `φ (b ^ ℓ) = φ b ^ ℓ = 1` because `Multiplicative (ZMod ℓ)` has exponent `ℓ`. -/
theorem eq_one_of_hom_zmod_of_openNormal_index {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    {p ℓ : ℕ} (hℓ : ℓ.Prime) (hpℓ : ℓ ≠ p)
    (h : ∀ U : OpenNormalSubgroup A, ∃ k : ℕ, U.toSubgroup.index = p ^ k)
    (φ : A →* Multiplicative (ZMod ℓ)) : φ = 1 := by
  classical
  -- **Arithmetic.**  `p ^ j * ℓ = p ^ k` with `ℓ` prime and `2 ≤ p` forces `p = ℓ`.
  have arith : ∀ {j k : ℕ}, 2 ≤ p → p ^ j * ℓ = p ^ k → p = ℓ := by
    intro j k hp2 hmain
    have hp1 : 1 < p := by omega
    have hkj : j ≤ k := by
      have h1 : p ^ j ≤ p ^ k := by
        calc p ^ j = p ^ j * 1 := (mul_one _).symm
          _ ≤ p ^ j * ℓ := Nat.mul_le_mul_left _ hℓ.one_le
          _ = p ^ k := hmain
      exact (Nat.pow_le_pow_iff_right hp1).mp h1
    have hpow : p ^ j * p ^ (k - j) = p ^ k := by rw [← pow_add, Nat.add_sub_cancel' hkj]
    have hℓeq : ℓ = p ^ (k - j) := by
      refine Nat.mul_left_cancel (pow_pos (by omega : 0 < p) j) ?_
      rw [hmain, hpow]
    have hkjpos : 1 ≤ k - j := by
      rcases Nat.eq_zero_or_pos (k - j) with h0 | hpos
      · rw [h0, pow_zero] at hℓeq
        exact absurd hℓeq hℓ.ne_one
      · exact hpos
    have hdvd : p ∣ ℓ := by rw [hℓeq]; exact dvd_pow_self p (by omega)
    rcases hℓ.eq_one_or_self_of_dvd p hdvd with h1 | h1
    · omega
    · exact h1
  -- **Step 1.**  No finite quotient of `A` has an element of order `ℓ`.
  have key : ∀ (U : OpenNormalSubgroup A) (x : A ⧸ (U : Subgroup A)), x ^ ℓ = 1 → x = 1 := by
    intro U x hx
    by_contra hx1
    haveI : Finite (A ⧸ (U : Subgroup A)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    haveI : Nontrivial (A ⧸ (U : Subgroup A)) := ⟨⟨x, 1, hx1⟩⟩
    have hcard2 : 2 ≤ Nat.card (A ⧸ (U : Subgroup A)) := by
      have := Finite.one_lt_card (α := A ⧸ (U : Subgroup A)); omega
    -- `x` has order exactly `ℓ`
    have hord : orderOf x = ℓ := by
      rcases hℓ.eq_one_or_self_of_dvd (orderOf x) (orderOf_dvd_iff_pow_eq_one.mpr hx) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx1
      · exact h1
    have hKcard : Nat.card ↥(Subgroup.zpowers x) = ℓ := by rw [Nat.card_zpowers, hord]
    -- pull the cyclic subgroup `⟨x⟩` back to `A`: an open normal subgroup `V`
    let q : A →* (A ⧸ (U : Subgroup A)) := QuotientGroup.mk' (U : Subgroup A)
    let V : Subgroup A := (Subgroup.zpowers x).comap q
    have hUV : (U : Subgroup A) ≤ V := by
      intro a ha
      change q a ∈ Subgroup.zpowers x
      have hqa : q a = 1 := MonoidHom.mem_ker.mp (by
        rw [show q.ker = (U : Subgroup A) from QuotientGroup.ker_mk' _]; exact ha)
      rw [hqa]; exact Subgroup.one_mem _
    have hVopen : IsOpen (V : Set A) := Subgroup.isOpen_mono hUV U.isOpen
    obtain ⟨j, hj⟩ := h ⟨⟨V, hVopen⟩, inferInstance⟩
    have hVidx : V.index = (Subgroup.zpowers x).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective (U : Subgroup A))
    obtain ⟨k, hk⟩ := h U
    have hBcard : Nat.card (A ⧸ (U : Subgroup A)) = p ^ k := by
      rw [← Subgroup.index_eq_card]; exact hk
    have hp2 : 2 ≤ p := by
      by_contra hcon
      have hp01 : p = 0 ∨ p = 1 := by omega
      rcases hp01 with h0 | h1
      · subst h0
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0, pow_zero] at hBcard; omega
        · rw [hBcard, zero_pow hkpos.ne'] at hcard2; omega
      · subst h1; rw [hBcard, one_pow] at hcard2; omega
    -- Lagrange in `B`, combined with `[B : ⟨x⟩] = p ^ j` and `|⟨x⟩| = ℓ`
    have hlag : (Subgroup.zpowers x).index * Nat.card ↥(Subgroup.zpowers x)
        = Nat.card (A ⧸ (U : Subgroup A)) := Subgroup.index_mul_card _
    have hmain : p ^ j * ℓ = p ^ k := by
      rw [← hj, hVidx, ← hKcard, hlag, hBcard]
    exact hpℓ (arith hp2 hmain).symm
  -- **Step 2.**  The `ℓ`-power map is surjective on every finite quotient of `A`.
  have hsurj' : ∀ (U : OpenNormalSubgroup A) (a : A), ∃ b : A,
      (QuotientGroup.mk' (U : Subgroup A) b) ^ ℓ = QuotientGroup.mk' (U : Subgroup A) a := by
    intro U a
    haveI : Finite (A ⧸ (U : Subgroup A)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    have hinj : Function.Injective (fun x : A ⧸ (U : Subgroup A) => x ^ ℓ) := by
      intro x z hxz
      change x ^ ℓ = z ^ ℓ at hxz
      have h1 : (x * z⁻¹) ^ ℓ = 1 := by rw [mul_pow, inv_pow, hxz, mul_inv_cancel]
      have h2 := key U (x * z⁻¹) h1
      rwa [mul_inv_eq_one] at h2
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj)
      (QuotientGroup.mk' (U : Subgroup A) a)
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup A) y
    exact ⟨b, hy⟩
  -- **Step 3.**  Every element of `A` is an `ℓ`-th power.
  have hroot : ∀ a : A, ∃ b : A, b ^ ℓ = a := by
    intro a
    by_contra hcon
    have hRcl : IsClosed (Set.range (fun x : A => x ^ ℓ)) :=
      (isCompact_range (continuous_pow ℓ)).isClosed
    have haR : a ∉ Set.range (fun x : A => x ^ ℓ) := by
      rintro ⟨b, hb⟩
      exact hcon ⟨b, hb⟩
    -- separate `a` from the closed image of the `ℓ`-power map by an open normal subgroup
    set W : Set A := {x : A | a * x ∉ Set.range (fun x : A => x ^ ℓ)} with hW
    have hWopen : IsOpen W := by
      have hWeq : W = (fun x : A => a * x) ⁻¹' (Set.range (fun x : A => x ^ ℓ))ᶜ := by
        ext x; simp [W]
      rw [hWeq]
      exact (continuous_const.mul continuous_id).isOpen_preimage _ hRcl.isOpen_compl
    have h1W : (1 : A) ∈ W := by
      simp only [W, Set.mem_ofPred_eq, mul_one]
      exact haR
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen h1W
    -- but the coset `a U` does meet the image, by Step 2
    obtain ⟨b, hb⟩ := hsurj' U a
    have hw : QuotientGroup.mk' (U : Subgroup A) (b ^ ℓ) = QuotientGroup.mk' (U : Subgroup A) a := by
      rw [map_pow]; exact hb
    have hmem : (b ^ ℓ)⁻¹ * a ∈ (U : Subgroup A) := QuotientGroup.eq.mp hw
    have hmem' : a⁻¹ * b ^ ℓ ∈ (U : Subgroup A) := by
      have hinv := Subgroup.inv_mem _ hmem
      simpa [mul_inv_rev, inv_inv] using hinv
    have hnot := hU hmem'
    simp only [W, Set.mem_ofPred_eq] at hnot
    rw [mul_inv_cancel_left] at hnot
    exact hnot ⟨b, rfl⟩
  -- **Conclusion.**  `Multiplicative (ZMod ℓ)` has exponent `ℓ`.
  have htop : ∀ x : Multiplicative (ZMod ℓ), x ^ ℓ = 1 := by
    intro x
    have hcard : Nat.card (Multiplicative (ZMod ℓ)) = ℓ := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have h' := pow_card_eq_one' (x := x)
    rwa [hcard] at h'
  ext a
  obtain ⟨b, hb⟩ := hroot a
  rw [← hb, map_pow]
  exact htop _

end NK.TameStructureDeep.Support
