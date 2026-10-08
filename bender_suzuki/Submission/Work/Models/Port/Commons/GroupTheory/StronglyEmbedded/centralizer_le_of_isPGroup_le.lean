import Mathlib.GroupTheory.PGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Commons.GroupTheory.StronglyEmbedded

/-- If `M` is a proper subgroup of a finite group `G` with `Nat.card M` even and with
`Nat.card (M ⊓ M ^ g)` odd for every `g ∉ M`, then every nontrivial `2`-subgroup `T ≤ M`
has `C_G(T) ≤ M`.

Indeed, if `c ∈ C_G(T) \ M`, then `T ≤ M ⊓ M ^ c`, forcing `Nat.card (M ⊓ M ^ c)` to be
divisible by the even number `Nat.card T`, a contradiction. -/
theorem centralizer_le_of_isPGroup_le {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hM : M ≠ ⊤) (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTM : T ≤ M) (hTne : T ≠ ⊥) :
    Subgroup.centralizer (T : Set G) ≤ M := by
  intro c hc
  by_contra hcM
  have hodd : Odd (Nat.card ((M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G))) :=
    hOdd c hcM
  -- `T` is contained in the conjugate `M ^ c`
  have hTc : T ≤ M.map (MulAut.conj c).toMonoidHom := by
    intro t ht
    refine ⟨t, hTM ht, ?_⟩
    have hcomm : t * c = c * t := (Subgroup.mem_centralizer_iff.mp hc) t ht
    change c * t * c⁻¹ = t
    rw [← hcomm]
    simp
  have hle : T ≤ (M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G) :=
    le_inf hTM hTc
  have hdvd : Nat.card T ∣ Nat.card ((M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G)) :=
    Subgroup.card_dvd_of_le hle
  -- `Nat.card T` is even because `T` is a nontrivial `2`-group
  have hEvenT : Even (Nat.card T) := by
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
    have h2 : 2 ∣ Nat.card T :=
      (IsPGroup.dvd_orderOf hT ht).trans (orderOf_dvd_natCard t)
    exact even_iff_two_dvd.mpr h2
  have hEvenN : Even (Nat.card ((M ⊓ M.map (MulAut.conj c).toMonoidHom : Subgroup G))) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hEvenT).trans hdvd)
  exact (Nat.not_even_iff_odd.mpr hodd) hEvenN

end Commons.GroupTheory.StronglyEmbedded