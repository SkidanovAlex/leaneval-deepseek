import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CommutingInvolsCardSix
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal

/-!
# Counting the involutions of `A` centralizing `s` (Bender §3, `Ĥ = H`)

`Work.CORE3.NcardInvolsCentralizerEq`: in the configuration of Bender's §3 for the subcase
`V = O₂(Ĥ)` (`V` a four-group, `U` of odd order, `V ⊓ U = ⊥`, `U` centralizing `V`,
`|A : VU| = 6`), the involutions of `A` centralizing an involution `s ∈ A − V` are exactly

* the non-identity elements of `V ⊓ C_A(s)`, and
* the products `s · v` with `v ∈ V ⊓ C_A(s)`.

There are `|V ⊓ C_A(s)| − 1` of the first kind and `|V ⊓ C_A(s)|` of the second, whence the count
`2 · |V ⊓ C_A(s)| − 1`.  The key structural input is the quotient `A/VU` of order `6`: two
commuting involutions of a group of order `6` coincide unless one is trivial
(`Work.CORE3.CommutingInvolsCardSix`), so an involution `x ∈ A` centralizing `s` lies in the
coset `VU` or in the coset `s VU`.

The decomposition `VU = V · U` (every element of `V ⊔ U` is a product `v * u`) is
`Work.CORE3.exists_mul_of_mem_sup_of_normal`; `U` odd forces the `U`-part to be trivial.
-/

open Subgroup Work.GW2

namespace Work.CORE3

/-- `(v * u) ^ 2 = u ^ 2` when `v` has order dividing `2` and commutes with `u`. -/
private theorem sq_mul_eq_sq_of_comm {G : Type} [Group G] {v u : G}
    (hv2 : v * v = 1) (hvu : v * u = u * v) : (v * u) ^ 2 = u ^ 2 := by
  rw [pow_two, pow_two]
  calc v * u * (v * u) = v * (u * v) * u := by group
    _ = v * (v * u) * u := by rw [← hvu]
    _ = (v * v) * (u * u) := by group
    _ = u * u := by rw [hv2, one_mul]

/-- `N ◁ A` with `|A : N| = 6`; `s x ∈ A` involutions with `s ∉ N` commuting; then `x` lies in
the coset `N` or in the coset `s N`.

This is the order-`6` quotient step of the counting argument: pass to `A/N`, where the images of
`s` and `x` are commuting involutions, the image of `s` being non-trivial. -/
private theorem quotientSixMem {G : Type} [Group G] [Finite G] (A N : Subgroup G) (s x : G)
    (hNA : N ≤ A) (hNn : (N.subgroupOf A).Normal) (hq : N.relIndex A = 6)
    (hsA : s ∈ A) (hxA : x ∈ A) (hs2 : s ^ 2 = 1) (hx2 : x ^ 2 = 1)
    (hsN : s ∉ N) (hcomm : x * s = s * x) :
    x ∈ N ∨ s * x ∈ N := by
  have hNn' := hNn
  haveI := hNn'
  have hcard : Nat.card (↥A ⧸ (N.subgroupOf A)) = 6 := by
    rw [← Subgroup.index_eq_card]
    exact hq
  let s' : ↥A := ⟨s, hsA⟩
  let x' : ↥A := ⟨x, hxA⟩
  have hs'2 : s' ^ 2 = 1 := by
    apply Subtype.ext
    show s ^ 2 = 1
    exact hs2
  have hx'2 : x' ^ 2 = 1 := by
    apply Subtype.ext
    show x ^ 2 = 1
    exact hx2
  have hcomm' : x' * s' = s' * x' := by
    apply Subtype.ext
    show x * s = s * x
    exact hcomm
  let sbar : ↥A ⧸ (N.subgroupOf A) := QuotientGroup.mk' (N.subgroupOf A) s'
  let xbar : ↥A ⧸ (N.subgroupOf A) := QuotientGroup.mk' (N.subgroupOf A) x'
  have hsbar2 : sbar ^ 2 = 1 := by
    show (QuotientGroup.mk' (N.subgroupOf A) s') ^ 2 = 1
    rw [← map_pow, hs'2, map_one]
  have hxbar2 : xbar ^ 2 = 1 := by
    show (QuotientGroup.mk' (N.subgroupOf A) x') ^ 2 = 1
    rw [← map_pow, hx'2, map_one]
  have hcommbar : xbar * sbar = sbar * xbar := by
    show (QuotientGroup.mk' (N.subgroupOf A) x') * (QuotientGroup.mk' (N.subgroupOf A) s') =
      (QuotientGroup.mk' (N.subgroupOf A) s') * (QuotientGroup.mk' (N.subgroupOf A) x')
    rw [← map_mul, ← map_mul, hcomm']
  have hsbar_ne : sbar ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk' (N.subgroupOf A) s') = 1 := h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hsN (Subgroup.mem_subgroupOf.mp h1)
  rcases CommutingInvolsCardSix hcard sbar xbar hsbar2 hsbar_ne hxbar2 hcommbar.symm with h | h
  · left
    have h1 : (QuotientGroup.mk' (N.subgroupOf A) x') = 1 := h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  · right
    have h1 : (QuotientGroup.mk' (N.subgroupOf A) x') =
        (QuotientGroup.mk' (N.subgroupOf A) s') := h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have h2 : x⁻¹ * s ∈ N := by simpa using Subgroup.mem_subgroupOf.mp h1
    have h3 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rwa [pow_two] at hx2)
    rw [h3] at h2
    rw [← hcomm]
    exact h2

theorem NcardInvolsCentralizerEq {G : Type} [Group G] [Finite G] (A V U : Subgroup G) (s : G)
    (hVA : V ≤ A) (hUA : U ≤ A)
    (hVn : (V.subgroupOf A).Normal) (hUn : (U.subgroupOf A).Normal)
    (hV4 : Work.GW2.IsFourGroup V)
    (hUodd : Odd (Nat.card U)) (hdisj : V ⊓ U = ⊥)
    (hUV : U ≤ Subgroup.centralizer (V : Set G))
    (hq : (V ⊔ U).relIndex A = 6)
    (hsA : s ∈ A) (hs2 : orderOf s = 2) (hsV : s ∉ V) :
    (Work.GW2.involutionSet A ∩ Subgroup.centralizer ({s} : Set G)).ncard =
      2 * Nat.card (V ⊓ Subgroup.centralizer ({s} : Set G) : Subgroup G) - 1 := by
  have hs2p : s ^ 2 = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs2] at h
  have hs_mul : s * s = 1 := by rwa [pow_two] at hs2p
  -- elementwise normality of `V` and `U` under `A`
  have hVnorm : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V :=
    fun a ha v hv => (Subgroup.normal_subgroupOf_iff hVA).mp hVn v a hv ha
  have hUnorm : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U :=
    fun a ha u hu => (Subgroup.normal_subgroupOf_iff hUA).mp hUn u a hu ha
  have hNleA : V ⊔ U ≤ A := sup_le hVA hUA
  have hNn : ((V ⊔ U).subgroupOf A).Normal := by
    haveI := hVn
    haveI := hUn
    rw [Subgroup.subgroupOf_sup hVA hUA]
    exact Subgroup.sup_normal _ _
  -- `V` and `U` commute, so `(v * u)^2 = u^2` on `V × U`
  have hsq : ∀ v ∈ V, ∀ u ∈ U, (v * u) ^ 2 = u ^ 2 := by
    intro v hv u hu
    have hv2 : v * v = 1 := by have h := hV4.2 v hv; rwa [pow_two] at h
    have hvu : v * u = u * v := (Subgroup.mem_centralizer_iff.mp (hUV hu)) v hv
    exact sq_mul_eq_sq_of_comm hv2 hvu
  -- `U` is odd, so a square-one element of `U` is trivial
  have hUu : ∀ u ∈ U, u ^ 2 = 1 → u = 1 := by
    intro u hu hu2
    have hdvd2 : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
    have hdvdU : orderOf u ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hu
    have hcop : Nat.Coprime 2 (Nat.card U) := Nat.coprime_two_left.mpr hUodd
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdU)
  -- `s ∉ VU`
  have hsN : s ∉ V ⊔ U := by
    intro hs
    obtain ⟨v, hv, u, hu, hvu⟩ := exists_mul_of_mem_sup_of_normal hVA hUA hVnorm hUnorm s hs
    have hu1 : u = 1 := hUu u hu (by rw [← hsq v hv u hu, ← hvu, hs2p])
    have : s ∈ V := by rw [hvu, hu1, mul_one]; exact hv
    exact hsV this
  set C : Subgroup G := Subgroup.centralizer ({s} : Set G) with hCdef
  set T : Subgroup G := V ⊓ C with hTdef
  have hsC : s ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  have hT1 : (1 : G) ∈ (T : Set G) := by
    rw [hTdef]; exact ⟨V.one_mem, C.one_mem⟩
  -- the description of the involution set
  have hS_eq : (Work.GW2.involutionSet A ∩ (C : Set G)) =
      ((T : Set G) \ {1}) ∪ ((fun v : G => s * v) '' (T : Set G)) := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ A := hx.1.1
      have hxord : orderOf x = 2 := hx.1.2
      have hxC : x ∈ C := hx.2
      have hxC' : x ∈ Subgroup.centralizer ({s} : Set G) := by rw [← hCdef]; exact hxC
      have hx2 : x ^ 2 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      have hxs : x * s = s * x := ((Subgroup.mem_centralizer_iff.mp hxC') s (by simp)).symm
      by_cases hxN : x ∈ V ⊔ U
      · -- `x ∈ VU`: then `x ∈ V` (the `U`-part is trivial)
        left
        obtain ⟨v, hv, u, hu, hvu⟩ :=
          exists_mul_of_mem_sup_of_normal hVA hUA hVnorm hUnorm x hxN
        have hu1 : u = 1 := hUu u hu (by rw [← hsq v hv u hu, ← hvu, hx2])
        have hxv : x = v := by rw [hvu, hu1, mul_one]
        have hxV : x ∈ V := by rw [hxv]; exact hv
        refine ⟨?_, ?_⟩
        · rw [hTdef]; exact ⟨hxV, hxC⟩
        · rw [Set.mem_singleton_iff]
          intro h
          rw [h, orderOf_one] at hxord
          exact absurd hxord (by norm_num)
      · -- `x ∉ VU`: then `s x ∈ VU` (order-`6` quotient), and `x = s * v` with `v ∈ V ⊓ C`
        right
        have hsxN : s * x ∈ V ⊔ U :=
          (quotientSixMem A (V ⊔ U) s x hNleA hNn hq hsA hxA hs2p hx2 hsN hxs).resolve_left hxN
        obtain ⟨v, hv, u, hu, hvu⟩ :=
          exists_mul_of_mem_sup_of_normal hVA hUA hVnorm hUnorm (s * x) hsxN
        have hxeq : x = s * (s * x) := by rw [← mul_assoc, hs_mul, one_mul]
        have hnsn : s * (s * x) * s = s * x := by rw [← hxeq, hxs]
        have hn2 : (s * x) ^ 2 = 1 := by
          have h1 : (s * (s * x)) ^ 2 = 1 := by rw [← hxeq, hx2]
          have h2 : (s * (s * x)) ^ 2 = (s * x) ^ 2 := by
            calc (s * (s * x)) ^ 2 = (s * (s * x) * s) * (s * x) := by rw [pow_two]; group
              _ = (s * x) ^ 2 := by rw [hnsn, pow_two]
          rw [h2] at h1; exact h1
        have hu1 : u = 1 := hUu u hu (by rw [← hsq v hv u hu, ← hvu, hn2])
        have hnv : s * x = v := by rw [hvu, hu1, mul_one]
        have hsvs : s * v * s = v := by rw [← hnv, hnsn]
        have hvs : v * s = s * v := by
          have key : v * s * s = s * v * s := by rw [hsvs, mul_assoc, hs_mul, mul_one]
          exact mul_right_cancel key
        have hvC : v ∈ C := by
          rw [hCdef, Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hvs.symm
        refine ⟨v, ?_, ?_⟩
        · rw [hTdef]; exact ⟨hv, hvC⟩
        · show s * v = x
          rw [← hnv, ← mul_assoc, hs_mul, one_mul]
    · intro hx
      rcases hx with hx | hx
      · -- `v ∈ V ⊓ C`, `v ≠ 1`: an involution centralizing `s`
        obtain ⟨hxT, hxne⟩ := hx
        rw [hTdef] at hxT
        have hxV : x ∈ V := (Subgroup.mem_inf.mp hxT).1
        have hxC : x ∈ C := (Subgroup.mem_inf.mp hxT).2
        have hxne1 : x ≠ 1 := by simpa using hxne
        have hx2 : x ^ 2 = 1 := hV4.2 x hxV
        have hxord : orderOf x = 2 := by
          have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hxne1
          · exact h
        exact ⟨⟨hVA hxV, hxord⟩, hxC⟩
      · -- `s * v` with `v ∈ V ⊓ C`: an involution centralizing `s`
        obtain ⟨v, hvT, hvx⟩ := hx
        rw [hTdef] at hvT
        have hvV : v ∈ V := (Subgroup.mem_inf.mp hvT).1
        have hvC : v ∈ C := (Subgroup.mem_inf.mp hvT).2
        have hvC' : v ∈ Subgroup.centralizer ({s} : Set G) := by rw [← hCdef]; exact hvC
        have hvs : v * s = s * v := ((Subgroup.mem_centralizer_iff.mp hvC') s (by simp)).symm
        have hv2 : v ^ 2 = 1 := hV4.2 v hvV
        have hv2' : v * v = 1 := by rwa [pow_two] at hv2
        have hsq2 : (s * v) ^ 2 = 1 := by
          rw [pow_two]
          calc s * v * (s * v) = s * (v * s) * v := by group
            _ = s * (s * v) * v := by rw [← hvs]
            _ = (s * s) * (v * v) := by group
            _ = 1 := by rw [hs_mul, hv2', mul_one]
        have hne : s * v ≠ 1 := by
          intro h
          have hsv : s = v := by
            rw [mul_eq_one_iff_eq_inv] at h
            rw [h, inv_eq_of_mul_eq_one_right hv2']
          exact hsV (hsv ▸ hvV)
        have hord : orderOf (s * v) = 2 := by
          have hdvd : orderOf (s * v) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq2
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hne
          · exact h
        have hA : s * v ∈ A := A.mul_mem hsA (hVA hvV)
        have hC2 : s * v ∈ C := C.mul_mem hsC hvC
        rw [← hvx]
        exact ⟨⟨hA, hord⟩, hC2⟩
  rw [hS_eq]
  -- the two pieces are disjoint (`V ⊓ C ⊆ VU`, `s · (V ⊓ C) ∩ VU = ∅`)
  have hdisjS : Disjoint ((T : Set G) \ {1}) ((fun v : G => s * v) '' (T : Set G)) := by
    rw [Set.disjoint_left]
    intro x hxS hxI
    obtain ⟨hxT, _⟩ := hxS
    rw [hTdef] at hxT
    have hxV : x ∈ V := (Subgroup.mem_inf.mp hxT).1
    obtain ⟨v, hvT, hvx⟩ := hxI
    rw [hTdef] at hvT
    have hvV : v ∈ V := (Subgroup.mem_inf.mp hvT).1
    have hs_in : s ∈ V ⊔ U := by
      have h1 : x ∈ V ⊔ U := Subgroup.mem_sup_left hxV
      have h2 : v ∈ V ⊔ U := Subgroup.mem_sup_left hvV
      have h3 : s = x * v⁻¹ := by rw [← hvx]; group
      rw [h3]
      exact (V ⊔ U).mul_mem h1 ((V ⊔ U).inv_mem h2)
    exact hsN hs_in
  rw [Set.ncard_union_eq hdisjS]
  have h1 : ((T : Set G) \ {1}).ncard = Nat.card T - 1 := by
    rw [Set.ncard_sdiff (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hT1), Set.ncard_singleton]
    rfl
  have h2 : ((fun v : G => s * v) '' (T : Set G)).ncard = Nat.card T := by
    have hinj : Function.Injective (fun v : G => s * v) := fun a b h => mul_left_cancel h
    rw [Set.ncard_image_of_injective (f := fun v : G => s * v) (T : Set G) hinj]
    rfl
  rw [h1, h2]
  have hpos : 1 ≤ Nat.card T := by
    haveI : Nonempty ↥T := ⟨⟨1, hT1⟩⟩
    exact Nat.card_pos
  omega

end Work.CORE3
