import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec2.prop1a_exists
import Submission.Work.DoubleTransitivity.Alg.exists_involution_conjugating

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec2.prop1a_unique`

Peterfalvi I §2, Proposition 1 (a), uniqueness half: if `H` is a Bender subgroup of the finite
group `G` and `s`, `t` are involutions of `G` with no common fixed point on `Ω = G ⧸ H`, then
there is at most one involution `u` of `G` with `u⁻¹ * s * u = t`.

The argument is the one of the source (p. 151).  Let `ω` be the unique fixed point of `s` on
`Ω` (Peterfalvi I §1 (10)(a), `Sec1.unique_fixed`).  An involution `u` fixes `ω` if and only if
`u⁻¹ * s * u` does ("`H(u) = H(s)` iff `H(s^u) = H(s)`"), so conjugation by `s` restricts to a
map

`Φ : {u involution | u • ω ≠ ω} → {u involution | u • ω ≠ ω},  u ↦ u⁻¹ * s * u`.

`Φ` is surjective: given an involution `t'` with `t' • ω ≠ ω`, the elements `s` and `t'` have no
common fixed point, so `prop1a_exists` produces an involution `u` with `u⁻¹ * s * u = t'`, and
such a `u` cannot fix `ω` (else `t'` would).  As the source puts it, the map is "surjective, hence
bijective" — the domain is finite.  Injectivity of `Φ` is exactly the asserted uniqueness.
-/

set_option autoImplicit false

open Submission.Blueprint
open Work.DoubleTransitivity

namespace Work.DoubleTransitivity.Sec2

/-- Conjugation preserves the order, so it preserves order `2`. -/
private theorem orderOf_inv_mul_self_mul {G : Type} [Group G] {s u : G} (hs : orderOf s = 2) :
    orderOf (u⁻¹ * s * u) = 2 := by
  simpa [MulAut.conj_apply, hs] using MulEquiv.orderOf_eq (MulAut.conj u⁻¹) s

/-- An element fixing a point of `Ω` is fixed by its inverse as well. -/
private lemma inv_smul_eq_self_of_smul_eq_self {G : Type} [Group G] {H : Subgroup G} {u : G}
    {ω : Omega H} (h : u • ω = ω) : u⁻¹ • ω = ω := by
  have h1 := congrArg (fun x => u⁻¹ • x) h
  simpa using h1.symm

theorem prop1a_unique {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsBender H)
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hst : ¬ ∃ ω : Omega H, s • ω = ω ∧ t • ω = ω) :
    ∃! u : G, orderOf u = 2 ∧ u⁻¹ * s * u = t := by
  classical
  -- Existence (the other half of Prop. 1(a)).
  obtain ⟨u₀, hu₀, hconj₀, -, -⟩ := prop1a_exists hH hs ht hst
  -- The unique fixed point of `s` on `Ω`.
  obtain ⟨ω₀, hω₀, huniq⟩ := Sec1.unique_fixed hH hs
  -- `D`: the involutions not fixing `ω₀`.
  let D := {u : G // orderOf u = 2 ∧ u • ω₀ ≠ ω₀}
  haveI : Finite D := inferInstance
  -- Conjugating by an element that does not fix `ω₀` again gives an involution not fixing `ω₀`.
  have key : ∀ u : G, u • ω₀ ≠ ω₀ → (u⁻¹ * s * u) • ω₀ ≠ ω₀ := by
    intro u huω hconj
    apply huω
    apply huniq (u • ω₀)
    have h1 : u⁻¹ • (s • (u • ω₀)) = ω₀ := by
      rw [← mul_smul, ← mul_smul]
      exact hconj
    have h2 := congrArg (fun x => u • x) h1
    simpa using h2
  let F : D → D := fun u =>
    ⟨u.1⁻¹ * s * u.1, orderOf_inv_mul_self_mul hs, key u.1 u.2.2⟩
  -- `F` is surjective.
  have hsurj : Function.Surjective F := by
    intro t'
    -- `s` and `t'.1` have no common fixed point.
    have hno : ¬ ∃ ω : Omega H, s • ω = ω ∧ t'.1 • ω = ω := by
      rintro ⟨ω, hsω, htω⟩
      have hω : ω = ω₀ := huniq ω hsω
      exact t'.2.2 (hω ▸ htω)
    obtain ⟨u, hu2, hconj, -, -⟩ := prop1a_exists hH hs t'.2.1 hno
    have huω : u • ω₀ ≠ ω₀ := by
      intro hfx
      apply t'.2.2
      calc t'.1 • ω₀ = (u⁻¹ * s * u) • ω₀ := by rw [hconj]
        _ = u⁻¹ • (s • (u • ω₀)) := by rw [mul_smul, mul_smul]
        _ = u⁻¹ • (s • ω₀) := by rw [hfx]
        _ = u⁻¹ • ω₀ := by rw [hω₀]
        _ = ω₀ := inv_smul_eq_self_of_smul_eq_self hfx
    exact ⟨⟨u, hu2, huω⟩, Subtype.ext hconj⟩
  -- A surjective self-map of a finite type is injective.
  have hinj : Function.Injective F := Finite.injective_iff_surjective.mpr hsurj
  -- No involution conjugating `s` to `t` fixes `ω₀`.
  have notfix : ∀ u : G, orderOf u = 2 → u⁻¹ * s * u = t → u • ω₀ ≠ ω₀ := by
    intro u hu hconj hfx
    apply hst
    refine ⟨ω₀, hω₀, ?_⟩
    calc t • ω₀ = (u⁻¹ * s * u) • ω₀ := by rw [hconj]
      _ = u⁻¹ • (s • (u • ω₀)) := by rw [mul_smul, mul_smul]
      _ = u⁻¹ • (s • ω₀) := by rw [hfx]
      _ = u⁻¹ • ω₀ := by rw [hω₀]
      _ = ω₀ := inv_smul_eq_self_of_smul_eq_self hfx
  have hu₀ω : u₀ • ω₀ ≠ ω₀ := notfix u₀ hu₀ hconj₀
  refine ⟨u₀, ⟨hu₀, hconj₀⟩, fun v hv => ?_⟩
  have hvω : v • ω₀ ≠ ω₀ := notfix v hv.1 hv.2
  have hFeq : F ⟨u₀, hu₀, hu₀ω⟩ = F ⟨v, hv.1, hvω⟩ := by
    apply Subtype.ext
    show u₀⁻¹ * s * u₀ = v⁻¹ * s * v
    rw [hconj₀, hv.2]
  exact (Subtype.ext_iff.mp (hinj hFeq)).symm

end Work.DoubleTransitivity.Sec2
