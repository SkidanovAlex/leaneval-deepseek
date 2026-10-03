import Mathlib
import Submission.Work.OROneRel.hnnKernelForm

namespace Work.OROneRel

/-- **A normal subgroup with quotient `ℤ` realises `G` as an HNN extension, with the comparison
map pinned down on generators.**

If `φ : G →* Multiplicative ℤ` has `φ t = ofAdd 1`, kernel exactly `H`, and `G = ⟨H, t⟩`, then there
is an isomorphism `E : HNNExtension ↥H ⊤ ⊤ ψ ≃* G` (for `ψ` the conjugation automorphism of the base
`↥H` by `t`) which is the *canonical* one: it sends `HNNExtension.of h` to `(h : G)` and the stable
letter `HNNExtension.t` to `t`.  This is the sharpened form of `Work.OROneRel.hnnKernelForm` needed
to control the root tracking of a Magnus--Moldavanskii step: the class of the relator lies in `ker φ`
and its image under the step is the class of the vertex root precisely when the comparison map is
this canonical one.

Proof idea: the canonical map `HNNExtension.lift (Subgroup.subtype H) t _` is bijective; surjectivity
is `G = ⟨H, t⟩`, and injectivity is the argument of
`Work.OROneRel.exists_hnn_top_of_normal_vertex` (every element of the HNN extension with `A = B = ⊤`
is `of h * t ^ n`, and the hypothesis `t ^ m ∉ H` for `m ≠ 0` forces faithfulness). -/
theorem hnnKernelForm_tracking {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (φ : G →* Multiplicative ℤ) (hφt : φ t = Multiplicative.ofAdd 1)
    (hH : ∀ g : G, g ∈ H ↔ φ g = 1)
    (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤) :
    ∃ (ψ : (⊤ : Subgroup ↥H) ≃* (⊤ : Subgroup ↥H))
      (E : HNNExtension ↥H ⊤ ⊤ ψ ≃* G),
      (∀ h : ↥H, E (HNNExtension.of h) = (h : G)) ∧ E HNNExtension.t = t ∧
      (∀ a : (⊤ : Subgroup ↥H),
        (((ψ a : (⊤ : Subgroup ↥H)) : ↥H) : G) = t * (((a : (⊤ : Subgroup ↥H)) : ↥H) : G) * t⁻¹) := by
  -- `H` is the kernel of `φ`, hence normal.
  have hker : H = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker]
    exact hH g
  have hN : H.Normal := hker ▸ MonoidHom.normal_ker φ
  -- no nonzero power of `t` lies in `H`
  have ht : ∀ m : ℤ, m ≠ 0 → t ^ m ∉ H := by
    intro m hm hmem
    have h1 : φ (t ^ m) = 1 := (hH (t ^ m)).mp hmem
    rw [map_zpow, hφt] at h1
    have h2 : m = 0 := by
      have := congrArg Multiplicative.toAdd h1
      simpa using this
    exact hm h2
  -- ### the automorphism of `H` given by conjugation by `t`
  let ψ : (⊤ : Subgroup ↥H) ≃* (⊤ : Subgroup ↥H) :=
  { toFun := fun a =>
      ⟨⟨t * ((a : ↥H) : G) * t⁻¹, hN.conj_mem _ (a : ↥H).property t⟩, Subgroup.mem_top _⟩
    invFun := fun a =>
      ⟨⟨t⁻¹ * ((a : ↥H) : G) * t,
        by simpa using hN.conj_mem _ (a : ↥H).property t⁻¹⟩, Subgroup.mem_top _⟩
    left_inv := by intro a; ext; group
    right_inv := by intro a; ext; group
    map_mul' := by intro a b; ext; simp [mul_assoc] }
  have hψ : ∀ a : (⊤ : Subgroup ↥H),
      (((ψ a : (⊤ : Subgroup ↥H)) : ↥H) : G) = t * (((a : (⊤ : Subgroup ↥H)) : ↥H) : G) * t⁻¹ :=
    fun a => rfl
  -- ### the canonical comparison map `HNNExtension ↥H ⊤ ⊤ ψ →* G`
  have hcompat : ∀ a : ↥(⊤ : Subgroup ↥H),
      t * (Subgroup.subtype H) ↑a = (Subgroup.subtype H) ↑(ψ a) * t := by
    intro a
    change t * ((a : ↥H) : G) = (t * ((a : ↥H) : G) * t⁻¹) * t
    group
  let π : HNNExtension ↥H ⊤ ⊤ ψ →* G := HNNExtension.lift (Subgroup.subtype H) t hcompat
  have hπ_of : ∀ k : ↥H, π (HNNExtension.of k) = (k : G) :=
    fun k => HNNExtension.lift_of (Subgroup.subtype H) t hcompat k
  have hπ_t : π HNNExtension.t = t := HNNExtension.lift_t (Subgroup.subtype H) t hcompat
  -- ### surjectivity, from `G = ⟨H, t⟩`
  have hsurj : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top]
    have hle : Subgroup.closure ((H : Set G) ∪ {t}) ≤ π.range := by
      refine (Subgroup.closure_le π.range).mpr ?_
      rintro x (hx | hx)
      · exact MonoidHom.mem_range.mpr ⟨HNNExtension.of ⟨x, hx⟩, hπ_of ⟨x, hx⟩⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact MonoidHom.mem_range.mpr ⟨HNNExtension.t, hπ_t⟩
    rw [hgen] at hle
    exact le_antisymm le_top hle
  -- ### normal form: every element is `of k * t ^ n`
  have key : ∀ x : HNNExtension ↥H ⊤ ⊤ ψ,
      ∃ (k : ↥H) (n : ℤ), x = HNNExtension.of k * HNNExtension.t ^ n := by
    -- conjugation by an arbitrary power of the stable letter stays inside the base
    have keyConj : ∀ (n : ℤ) (k : ↥H), ∃ k' : ↥H,
        HNNExtension.t ^ n * (HNNExtension.of k : HNNExtension ↥H ⊤ ⊤ ψ) * HNNExtension.t ^ (-n)
          = HNNExtension.of k' := by
      intro n
      induction n using Int.induction_on with
      | zero => intro k; exact ⟨k, by simp⟩
      | succ i ih =>
          intro k
          obtain ⟨k', hk'⟩ := ih k
          refine ⟨((ψ ⟨k', Subgroup.mem_top k'⟩) : ↥H), ?_⟩
          calc HNNExtension.t ^ ((i : ℤ) + 1) *
                  (HNNExtension.of k : HNNExtension ↥H ⊤ ⊤ ψ) * HNNExtension.t ^ (-((i : ℤ) + 1))
              = HNNExtension.t * (HNNExtension.t ^ (i : ℤ) * HNNExtension.of k *
                  HNNExtension.t ^ (-(i : ℤ))) * HNNExtension.t⁻¹ := by group
            _ = HNNExtension.t * HNNExtension.of k' * HNNExtension.t⁻¹ := by rw [hk']
            _ = HNNExtension.of ((ψ ⟨k', Subgroup.mem_top k'⟩) : ↥H) :=
                  (HNNExtension.equiv_eq_conj (φ := ψ) ⟨k', Subgroup.mem_top k'⟩).symm
      | pred i ih =>
          intro k
          obtain ⟨k', hk'⟩ := ih k
          have hk'' : HNNExtension.t ^ (-(i : ℤ)) *
              (HNNExtension.of k : HNNExtension ↥H ⊤ ⊤ ψ) * HNNExtension.t ^ (i : ℤ)
                = HNNExtension.of k' := by
            rw [neg_neg] at hk'; exact hk'
          refine ⟨((ψ.symm ⟨k', Subgroup.mem_top k'⟩) : ↥H), ?_⟩
          calc HNNExtension.t ^ (-(i : ℤ) - 1) * HNNExtension.of k *
                  HNNExtension.t ^ (-(-(i : ℤ) - 1))
              = HNNExtension.t⁻¹ * (HNNExtension.t ^ (-(i : ℤ)) * HNNExtension.of k *
                  HNNExtension.t ^ (i : ℤ)) * HNNExtension.t := by group
            _ = HNNExtension.t⁻¹ * HNNExtension.of k' * HNNExtension.t := by rw [hk'']
            _ = HNNExtension.of ((ψ.symm ⟨k', Subgroup.mem_top k'⟩) : ↥H) :=
                  (HNNExtension.equiv_symm_eq_conj (φ := ψ) ⟨k', Subgroup.mem_top k'⟩).symm
    intro x
    refine HNNExtension.induction_on x ?_ ?_ ?_ ?_
    · intro g
      exact ⟨g, 0, by simp⟩
    · exact ⟨1, 1, by simp⟩
    · intro x y hx hy
      obtain ⟨k, n, rfl⟩ := hx
      obtain ⟨k', m, rfl⟩ := hy
      obtain ⟨k'', hk''⟩ := keyConj n k'
      refine ⟨k * k'', n + m, ?_⟩
      rw [map_mul, ← hk'']
      group
    · intro x hx
      obtain ⟨k, n, rfl⟩ := hx
      obtain ⟨k'', hk''⟩ := keyConj (-n) k⁻¹
      refine ⟨k'', -n, ?_⟩
      have h1 : ((HNNExtension.of k * HNNExtension.t ^ n : HNNExtension ↥H ⊤ ⊤ ψ))⁻¹
          = HNNExtension.t ^ (-n) * HNNExtension.of k⁻¹ := by
        rw [mul_inv_rev, map_inv]; group
      rw [h1, ← hk'']
      group
  -- ### injectivity, from the (HNN) normal form and `t ^ m ∉ H` for `m ≠ 0`
  have hinj : Function.Injective π := by
    intro x y hxy
    obtain ⟨k, n, rfl⟩ := key x
    obtain ⟨k', m, rfl⟩ := key y
    have hπk : ∀ (k : ↥H) (n : ℤ),
        π (HNNExtension.of k * HNNExtension.t ^ n) = (k : G) * t ^ n := by
      intro k n; rw [map_mul, map_zpow, hπ_of, hπ_t]
    have hxy' : (k : G) * t ^ n = (k' : G) * t ^ m := by
      rw [hπk k n, hπk k' m] at hxy; exact hxy
    have hnm : n = m := by
      by_contra hne
      have hmem : t ^ (n - m) ∈ H := by
        have h4 : t ^ (n - m) = ((k⁻¹ * k' : ↥H) : G) := by
          have h5 : (k : G)⁻¹ * (k' : G) = t ^ (n - m) := by
            calc (k : G)⁻¹ * (k' : G)
                = (k : G)⁻¹ * ((k' : G) * t ^ m) * t ^ (-m) := by group
              _ = (k : G)⁻¹ * ((k : G) * t ^ n) * t ^ (-m) := by rw [hxy']
              _ = t ^ (n - m) := by group
          rw [← h5]; simp
        rw [h4]; exact (k⁻¹ * k').property
      exact ht (n - m) (sub_ne_zero.mpr hne) hmem
    subst hnm
    have hkk : k = k' := by
      exact Subtype.ext (mul_right_cancel hxy')
    subst hkk
    rfl
  exact ⟨ψ, MulEquiv.ofBijective π ⟨hinj, hsurj⟩, hπ_of, hπ_t, hψ⟩

end Work.OROneRel
