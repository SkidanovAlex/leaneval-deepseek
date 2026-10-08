import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.aut_transitive
import Submission.Work.Hering.HardCore.SixtyfourSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# No normal subgroup of order `16` in the reduced configuration

`Work.Hering.HardCore.no_normal_order_sixteen`: in the reduced configuration of Peterfalvi I §2
there is no normal subgroup `E ⊴ G` of order `16` with `V ≤ E ≤ C_G(V)`.

Math.  `V` is elementary abelian of order `8`, `E ≤ C_G(V)` has order `16` and `|E/V| = 2`.  Pick
`t ∈ E \ V`.  Its square `t²` lies in `V` (it is a square of an element of `C_G(V)`) and is
non-trivial (`t² = 1` would make `t` an involution of `C_G(V)`, hence an element of `V`).  For
every `g ∈ G`, the conjugated element `g t g⁻¹` again lies in `E` but not in `V`, and since `V`
has index two in `E` the two elements `g t g⁻¹` and `t` lie in the same coset of `V`; so
`g t g⁻¹ = v t` with `v ∈ V` (and `v` commutes with `t`, as `E ≤ C_G(V)`).  Hence
`g t² g⁻¹ = (g t g⁻¹)² = (v t)² = v² t² = t²`, i.e. `t² ∈ V#` is fixed by `G`.  But `G` acts
transitively by conjugation on the non-identity elements of `V` (`conj_transitive_on_V`), and
`V#` has `7` elements, so `t²` cannot be fixed.  Contradiction.
-/

namespace Work.Hering.HardCore

set_option autoImplicit false

/-- A finite type with at least three elements has an element different from two given ones. -/
lemma exists_ne_ne_of_three_le_card {α : Type*} [Finite α] (hcard : 3 ≤ Nat.card α)
    (a b : α) : ∃ c : α, c ≠ a ∧ c ≠ b := by
  haveI : Fintype α := Fintype.ofFinite α
  by_contra h
  have h' : ∀ x : α, x = a ∨ x = b := by
    intro x
    by_cases hx : x = a
    · exact Or.inl hx
    · refine Or.inr ?_
      by_contra hxb
      exact h ⟨x, hx, hxb⟩
  have hsurj : Function.Surjective (![a, b] : Fin 2 → α) := by
    intro x
    rcases h' x with hx | hx
    · exact ⟨0, by simpa using hx.symm⟩
    · exact ⟨1, by simpa using hx.symm⟩
  have hle : Nat.card α ≤ 2 := by
    have h2 := Nat.card_le_card_of_surjective (![a, b] : Fin 2 → α) hsurj
    rwa [Nat.card_fin] at h2
  omega

theorem no_normal_order_sixteen {G : Type*} [Group G] [Finite G] (V C : Subgroup G) (hV : V.Normal)
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G)))
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) (hAut : Work.Hering.ActsAsAut V hV)
    (hsq : ∀ x ∈ C, x * x ∈ V)
    (E : Subgroup G) (hEn : E.Normal) (hVE : V ≤ E) (hEC : E ≤ C) (hcardE : Nat.card E = 16) :
    False := by
  classical
  -- (1) every element of `E` commutes with every element of `V`
  have hcen : ∀ e ∈ E, ∀ v ∈ V, e * v = v * e := by
    intro e he v hv
    have heC : e ∈ Subgroup.centralizer ((V : Set G)) := hC ▸ hEC he
    exact ((Subgroup.mem_centralizer_iff.mp heC) v hv).symm
  -- (2) an element `t ∈ E \ V`
  obtain ⟨t, htE, htV⟩ : ∃ t : G, t ∈ E ∧ t ∉ V := by
    by_contra h
    push Not at h
    have hVE' : E ≤ V := fun x hx => h x hx
    have hEq : E = V := le_antisymm hVE' hVE
    rw [hEq] at hcardE
    omega
  have ht1 : t ≠ 1 := fun h => htV (by rw [h]; exact V.one_mem)
  -- (3) `t ^ 2 ∈ V` and `t ^ 2 ≠ 1`
  have hzV : t * t ∈ V := hsq t (hEC htE)
  have hz1 : t * t ≠ 1 := by
    intro h
    have hpow : t ^ 2 = 1 := by rw [pow_two]; exact h
    have hord : orderOf t = 2 := orderOf_eq_prime hpow ht1
    exact htV (hinv t (hEC htE) hord)
  -- (4) `V.subgroupOf E` has index two in `↥E`
  set K : Subgroup ↥E := V.subgroupOf E with hKdef
  have hKcard : Nat.card K = 8 := by
    rw [hKdef]
    have hev := Subgroup.subgroupOfEquivOfLe hVE
    rw [Nat.card_congr hev.toEquiv]
    exact hcard
  have hKindex : K.index = 2 := by
    have h := Subgroup.card_mul_index K
    have hEcard : Nat.card ↥E = 16 := hcardE
    rw [hKcard, hEcard] at h
    omega
  have htK : (⟨t, htE⟩ : ↥E) ∉ K := by
    rw [hKdef, Subgroup.mem_subgroupOf]
    exact htV
  -- (5) `t ^ 2` is fixed by conjugation
  have hfix : ∀ g : G, g * (t * t) * g⁻¹ = t * t := by
    intro g
    have hgtgE : g * t * g⁻¹ ∈ E := hEn.conj_mem t htE g
    have hgtgV : g * t * g⁻¹ ∉ V := by
      intro h
      have h1 := hV.conj_mem (g * t * g⁻¹) h g⁻¹
      rw [show g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t from by group] at h1
      exact htV h1
    -- `(g t g⁻¹)` and `t` lie in the same coset of `V` inside `E`
    have hprodK : (⟨g * t * g⁻¹, hgtgE⟩ : ↥E) * (⟨t, htE⟩ : ↥E)⁻¹ ∈ K := by
      rw [Subgroup.mul_mem_iff_of_index_two hKindex]
      apply iff_of_false
      · intro hh
        exact hgtgV (by rwa [hKdef, Subgroup.mem_subgroupOf] at hh)
      · intro hh
        rw [Subgroup.inv_mem_iff] at hh
        exact htV (by rwa [hKdef, Subgroup.mem_subgroupOf] at hh)
    have hvV : (g * t * g⁻¹) * t⁻¹ ∈ V := by
      have h1 := (Subgroup.mem_subgroupOf (H := V) (K := E)).mp (hKdef ▸ hprodK)
      simpa using h1
    set v : G := (g * t * g⁻¹) * t⁻¹ with hvdef
    have hvV' : v ∈ V := hvV
    have hgtg : g * t * g⁻¹ = v * t := by rw [hvdef]; group
    have hcomm : v * t = t * v := (hcen t htE v hvV').symm
    have hvv : v * v = 1 := hexp v hvV'
    have key : (v * t) * (v * t) = t * t := by
      calc (v * t) * (v * t) = v * (t * v) * t := by group
        _ = v * (v * t) * t := by rw [← hcomm]
        _ = (v * v) * (t * t) := by group
        _ = t * t := by rw [hvv, one_mul]
    calc g * (t * t) * g⁻¹
        = (g * t * g⁻¹) * (g * t * g⁻¹) := by group
      _ = (v * t) * (v * t) := by rw [hgtg]
      _ = t * t := key
  -- (6) transitivity of `G` on `V#` gives the contradiction
  have htrans := conj_transitive_on_V V hV hcard hexp hAut
  obtain ⟨w, hw1, hwz⟩ := exists_ne_ne_of_three_le_card (α := ↥V)
    (by rw [hcard]; norm_num) (1 : ↥V) ⟨t * t, hzV⟩
  have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨g, hg⟩ := htrans (t * t) (w : G) hzV w.2 hz1 hw1'
  exact hwz (Subtype.ext (hg.symm.trans (hfix g)))

end Work.Hering.HardCore
