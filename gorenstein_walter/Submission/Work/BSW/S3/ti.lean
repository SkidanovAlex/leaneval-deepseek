import Mathlib
import Submission.Work.BSW.Defs

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.BSW.S3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-! ## A counting lemma for semiregular actions

If a finite group `H` acts on a finite type `X` with a global fixed point `x₀` and every
non-identity element fixes nothing but `x₀`, then every `H`-orbit off `x₀` is regular, so
`|H|` divides `|X| - 1`. -/

theorem ti_semiregular_card_dvd {H X : Type*} [Group H] [Finite H] [MulAction H X] [Finite X]
    (x₀ : X) (hfix : ∀ h : H, h • x₀ = x₀)
    (hfree : ∀ h : H, h ≠ 1 → ∀ x : X, h • x = x → x = x₀) :
    Nat.card H ∣ Nat.card X - 1 := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Nonempty H := ⟨1⟩
  haveI : Nonempty X := ⟨x₀⟩
  have hall : ∀ h : H, h ≠ 1 → Nat.card ↑(MulAction.fixedBy X h) = 1 := by
    intro h hh
    refine Nat.card_eq_one_iff_exists.mpr ⟨⟨x₀, ?_⟩, fun y => Subtype.ext ?_⟩
    · rw [MulAction.mem_fixedBy]; exact hfix h
    · exact hfree h hh (y : X) (MulAction.mem_fixedBy.mp y.2)
  have hone : Nat.card ↑(MulAction.fixedBy X (1 : H)) = Nat.card X :=
    Nat.card_congr
      { toFun := fun x => (x : X)
        invFun := fun x => ⟨x, by rw [MulAction.mem_fixedBy]; exact one_smul H x⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => rfl }
  have h2 : ∑ x ∈ Finset.univ.erase (1 : H), Nat.card ↑(MulAction.fixedBy X x)
      = Nat.card H - 1 := by
    rw [Finset.sum_const_nat (fun x hx => hall x (Finset.mem_erase.mp hx).1), mul_one,
      Finset.card_erase_of_mem (Finset.mem_univ (1 : H)), Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hsum : (∑ h : H, Nat.card ↑(MulAction.fixedBy X h))
      = Nat.card X + (Nat.card H - 1) := by
    rw [← Finset.sum_erase_add Finset.univ (fun h : H => Nat.card ↑(MulAction.fixedBy X h))
      (Finset.mem_univ (1 : H))]
    rw [hone, h2, Nat.add_comm]
  have hburn : (∑ h : H, Nat.card ↑(MulAction.fixedBy X h))
      = Nat.card (Quotient (MulAction.orbitRel H X)) * Nat.card H := by
    rw [Finset.sum_congr rfl (fun h _ => Nat.card_eq_fintype_card),
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H X,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hmain : Nat.card X + (Nat.card H - 1)
      = Nat.card H * Nat.card (Quotient (MulAction.orbitRel H X)) := by
    rw [← hsum, hburn, Nat.mul_comm]
  have h1 : Nat.card H ∣ Nat.card X + (Nat.card H - 1) := by
    rw [hmain]; exact dvd_mul_right _ _
  have h3 := Nat.dvd_sub h1 (dvd_refl (Nat.card H))
  have heq : Nat.card X + (Nat.card H - 1) - Nat.card H = Nat.card X - 1 := by
    have hpos : 0 < Nat.card H := Nat.card_pos
    omega
  rwa [heq] at h3

/-! ## Conjugation helpers -/

/-- Membership in a conjugate subgroup. -/
theorem ti_mem_conjSub_iff {g : G} {H : Subgroup G} {a : G} :
    a ∈ Work.GW2.conjSub g H ↔ g⁻¹ * a * g ∈ H := by
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hh'⟩
    rw [show (MulEquiv.toMonoidHom (MulAut.conj g)) h = g * h * g⁻¹ from
      MulAut.conj_apply g h] at hh'
    rw [← hh']
    rwa [show g⁻¹ * (g * h * g⁻¹) * g = h from by group]
  · intro ha
    refine ⟨g⁻¹ * a * g, ha, ?_⟩
    rw [show (MulEquiv.toMonoidHom (MulAut.conj g)) (g⁻¹ * a * g) = g * (g⁻¹ * a * g) * g⁻¹ from
      MulAut.conj_apply g (g⁻¹ * a * g)]
    group

/-- Conjugation carries centralizers of singletons to centralizers of singletons. -/
theorem ti_conjSub_centralizer (g y : G) :
    Work.GW2.conjSub g (Subgroup.centralizer ({y} : Set G)) =
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
  ext z
  rw [ti_mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hz
    calc z * (g * y * g⁻¹) = g * (g⁻¹ * z * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [hz]
      _ = (g * y * g⁻¹) * z := by group
  · intro hz
    calc g⁻¹ * z * g * y = g⁻¹ * (z * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * z) * g := by rw [hz]
      _ = y * (g⁻¹ * z * g) := by group

/-- **Trivial intersection of `F` with the `N_G(F)`-conjugate.**

If every non-identity element `a` of `F` satisfies `C_G(a) = F`, then `F` meets no conjugate of
its normalizer `N_G(F)` except through `N_G(F)` itself.  Equivalently, if `x ∈ F` and
`g⁻¹ x g ∈ N_G(F)` for some `g`, then `g ∈ N_G(F)`.

This is Bender (1974), (3.1)(e). -/
theorem ti {G : Type} [Group G] [Finite G] {F : Subgroup G}
    (h : ∀ a ∈ F, a ≠ 1 → Subgroup.centralizer ({a} : Set G) = F) :
    ∀ g : G, g ∉ Subgroup.normalizer (F : Set G) →
      F ⊓ Work.GW2.conjSub g (Subgroup.normalizer (F : Set G)) = ⊥ := by
  intro g hg
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨hxF, hxN⟩ := Subgroup.mem_inf.mp hx
  set y : G := g⁻¹ * x * g with hy
  have hyN : y ∈ Subgroup.normalizer (F : Set G) := by
    rw [hy]; exact ti_mem_conjSub_iff.mp hxN
  have hxy : g * y * g⁻¹ = x := by rw [hy]; group
  -- Every power of `y` lying in `F` is trivial.
  have hA : ∀ k : ℤ, y ^ k ∈ F → y ^ k = 1 := by
    intro k hykF
    by_contra hyk1
    have hxkc : x ^ k = g * y ^ k * g⁻¹ := by
      have h1 : (MulAut.conj g) (y ^ k) = ((MulAut.conj g) y) ^ k :=
        map_zpow ((MulAut.conj g) : G →* G) y k
      rw [show (MulAut.conj g) y = x from by rw [MulAut.conj_apply]; exact hxy] at h1
      rw [MulAut.conj_apply] at h1
      exact h1.symm
    have hxk1 : x ^ k ≠ 1 := by
      intro hc
      apply hyk1
      calc y ^ k = g⁻¹ * x ^ k * g := by rw [hxkc]; group
        _ = 1 := by rw [hc]; group
    have hCx : Subgroup.centralizer ({x ^ k} : Set G) = F := h _ (F.zpow_mem hxF k) hxk1
    have hCy : Subgroup.centralizer ({y ^ k} : Set G) = F := h _ hykF hyk1
    have hconjF : Work.GW2.conjSub g F = F := by
      calc Work.GW2.conjSub g F
          = Work.GW2.conjSub g (Subgroup.centralizer ({y ^ k} : Set G)) := by rw [hCy]
        _ = Subgroup.centralizer ({g * y ^ k * g⁻¹} : Set G) := ti_conjSub_centralizer g (y ^ k)
        _ = Subgroup.centralizer ({x ^ k} : Set G) := by rw [← hxkc]
        _ = F := hCx
    exact hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjF)
  -- The cyclic group generated by `y` acts by conjugation on `F`.
  have hYle : Subgroup.zpowers y ≤ Subgroup.normalizer (F : Set G) :=
    Subgroup.zpowers_le.mpr hyN
  letI : MulAction ↥(Subgroup.zpowers y) ↥F :=
    MulAction.compHom ↥F (Subgroup.inclusion hYle)
  have hfix : ∀ u : ↥(Subgroup.zpowers y), u • (1 : ↥F) = 1 := by
    intro u
    apply Subtype.ext
    show ((u • (1 : ↥F) : ↥F) : G) = (1 : G)
    rw [show ((u • (1 : ↥F) : ↥F) : G) = (u : G) * ((1 : ↥F) : G) * (u : G)⁻¹ from rfl]
    simp
  have hfree : ∀ u : ↥(Subgroup.zpowers y), u ≠ 1 → ∀ c : ↥F, u • c = c → c = 1 := by
    intro u hu c hc
    by_contra hc1
    have hcne : (c : G) ≠ 1 := fun hh => hc1 (Subtype.ext hh)
    have hsm : (u : G) * (c : G) * (u : G)⁻¹ = (c : G) := by
      have h2 := congrArg (fun z : ↥F => (z : G)) hc
      rwa [show ((u • c : ↥F) : G) = (u : G) * (c : G) * (u : G)⁻¹ from rfl] at h2
    have hcomm : (u : G) * (c : G) = (c : G) * (u : G) := by
      calc (u : G) * (c : G) = ((u : G) * (c : G) * (u : G)⁻¹) * (u : G) := by group
        _ = (c : G) * (u : G) := by rw [hsm]
    have huF : (u : G) ∈ F := by
      have hmem : (u : G) ∈ Subgroup.centralizer ({(c : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]; exact hcomm
      rwa [h (c : G) c.2 hcne] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2
    have hkF : y ^ k ∈ F := by rw [hk]; exact huF
    have h1 : (u : G) = 1 := by
      rw [← hk]
      exact hA k hkF
    exact hu (Subtype.ext (by simpa using h1))
  have hcard : Nat.card ↥(Subgroup.zpowers y) ∣ Nat.card ↥F - 1 :=
    ti_semiregular_card_dvd (1 : ↥F) hfix hfree
  rw [Nat.card_zpowers] at hcard
  -- `x` and `y` are conjugate, hence have the same order.
  have hord : orderOf x = orderOf y := by
    have hconj : x = (MulAut.conj g) y := by
      rw [MulAut.conj_apply]; exact hxy.symm
    rw [hconj, MulEquiv.orderOf_eq]
  have hdiv : orderOf x ∣ Nat.card ↥F := by
    have hle : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hxF
    have hh := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers] at hh
  rw [← hord] at hcard
  have hone : orderOf x ∣ 1 := by
    have hsub : Nat.card ↥F - (Nat.card ↥F - 1) = 1 := by
      haveI : Nonempty ↥F := ⟨1, F.one_mem⟩
      have hpos : 0 < Nat.card ↥F := Nat.card_pos
      omega
    rw [← hsub]
    exact Nat.dvd_sub hdiv hcard
  exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone))

end Work.BSW.S3
