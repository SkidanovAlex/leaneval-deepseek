import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- **Z3 (blueprint §ZASS).** `u ↦ u • 0` is a bijection from `U` onto `X ∖ {∞}`: it is
injective because `u • 0 = u' • 0` forces `u⁻¹u' ∈ U ⊓ G_{∞0} = ⊥`, it lands in `X ∖ {∞}`
because `U ≤ B`, and both sides have `q = p^k` elements. -/
theorem equiv_unipotent_compl {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {p k : ℕ} {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (hUB : U ≤ Work.Zassenhaus.borel G inf) (hcardU : Nat.card U = p ^ k)
    (hcardH : Nat.card (Work.Zassenhaus.pairStab G inf zero) = (p ^ k - 1) / 2)
    (hdis : U ⊓ Work.Zassenhaus.pairStab G inf zero = ⊥) (hcardX : Nat.card X = p ^ k + 1) :
    ∃ Φ : U ≃ {x : X // x ≠ inf}, ∀ u : U, (Φ u : X) = (u : G) • zero := by
  classical
  -- The map `u ↦ u • zero` really lands in `X ∖ {inf}`: `u • zero = inf` would give
  -- `zero = u⁻¹ • inf = inf`, since `u⁻¹ ∈ U ≤ B = G_∞`.
  have hmem : ∀ u : U, (u : G) • zero ≠ inf := by
    intro u hu
    have huB : (u : G) ∈ Work.Zassenhaus.borel G inf := hUB u.2
    have hinvB : (u : G)⁻¹ ∈ Work.Zassenhaus.borel G inf :=
      (Work.Zassenhaus.borel G inf).inv_mem huB
    have h1 : (u : G)⁻¹ • ((u : G) • zero) = zero := by
      rw [← mul_smul, inv_mul_cancel, one_smul]
    have h2 : (u : G)⁻¹ • inf = inf := Work.Zassenhaus.mem_borel_iff.mp hinvB
    rw [hu] at h1
    rw [h2] at h1
    exact hne h1
  -- Injectivity: `u • zero = u' • zero` forces `u⁻¹u' ∈ U ⊓ G_{∞0} = ⊥`.
  have hinj : ∀ u u' : U, (u : G) • zero = (u' : G) • zero → u = u' := by
    intro u u' hz
    have hwU : ((u : G)⁻¹ * (u' : G)) ∈ U := U.mul_mem (U.inv_mem u.2) u'.2
    have hwB : ((u : G)⁻¹ * (u' : G)) ∈ Work.Zassenhaus.borel G inf := hUB hwU
    have hz' : ((u : G)⁻¹ * (u' : G)) • zero = zero := by
      rw [mul_smul, ← hz, inv_smul_smul]
    have hzw : ((u : G)⁻¹ * (u' : G)) • inf = inf := Work.Zassenhaus.mem_borel_iff.mp hwB
    have hwP : ((u : G)⁻¹ * (u' : G)) ∈ Work.Zassenhaus.pairStab G inf zero :=
      Work.Zassenhaus.mem_pairStab_iff.mpr ⟨hz', hzw⟩
    have hwbot : ((u : G)⁻¹ * (u' : G)) ∈ (⊥ : Subgroup G) := by
      rw [← hdis]
      exact ⟨hwU, hwP⟩
    have hw1 : ((u : G)⁻¹ * (u' : G)) = 1 := Subgroup.mem_bot.mp hwbot
    exact Subtype.ext (inv_mul_eq_one.mp hw1)
  let f : U → {x : X // x ≠ inf} := fun u => ⟨(u : G) • zero, hmem u⟩
  have hf_inj : Function.Injective f := by
    intro u u' h
    exact hinj u u' (congrArg Subtype.val h)
  -- Both sides have `p ^ k` elements, so the injection is a bijection.
  haveI : Fintype U := Fintype.ofFinite U
  haveI : Fintype {x : X // x ≠ inf} := Fintype.ofFinite _
  haveI : Fintype X := Fintype.ofFinite X
  have hcardt : Fintype.card {x : X // x ≠ inf} = p ^ k := by
    rw [Fintype.card_subtype_compl (fun x : X => x = inf)]
    rw [Fintype.card_subtype_eq inf]
    have hX : Fintype.card X = p ^ k + 1 := by
      rw [← Nat.card_eq_fintype_card]; exact hcardX
    rw [hX, Nat.add_sub_cancel]
  have hcardU' : Fintype.card U = p ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact hcardU
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf_inj, by rw [hcardU', hcardt]⟩
  exact ⟨Equiv.ofBijective f hbij, fun u => rfl⟩

end Work.ZASS
