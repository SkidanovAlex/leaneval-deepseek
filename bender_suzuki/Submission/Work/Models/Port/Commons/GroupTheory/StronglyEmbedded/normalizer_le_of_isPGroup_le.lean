import Mathlib.GroupTheory.PGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- If `M ≤ G` is a subgroup with `M ∩ Mᵍ` of odd order for every `g ∉ M`, and `T` is a
nontrivial 2-subgroup of `M`, then the normalizer of `T` lies in `M`.

Indeed, if `g ∈ N_G(T)` with `g ∉ M`, then `T ≤ M` and `T = Tᵍ ≤ Mᵍ`, so `T ⊆ M ∩ Mᵍ`;
a nontrivial 2-group has even order, whence `|M ∩ Mᵍ|` is even, contradicting the
hypothesis. -/
theorem normalizer_le_of_isPGroup_le {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hOdd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTM : T ≤ M) (hTne : T ≠ ⊥) :
    Subgroup.normalizer (T : Set G) ≤ M := by
  classical
  intro g hg
  by_contra hgM
  -- `g` normalizes `T`, and `T ≤ M`, so `T ≤ Mᵍ`.
  have hmap : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hle : T ≤ (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
    refine le_inf hTM ?_
    have h := Subgroup.map_mono hTM (f := (MulAut.conj g).toMonoidHom)
    rwa [hmap] at h
  -- Hence `|T| ∣ |M ⊓ Mᵍ|`, and `|T|` is even while `|M ⊓ Mᵍ|` is odd.
  have hdvd : Nat.card T ∣ Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
    Subgroup.card_dvd_of_le hle
  have hodd : Odd (Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)) :=
    hOdd g hgM
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  -- `T ≠ ⊥` forces `n ≠ 0`, so `|T| = 2 ^ n` is even.
  have hn0 : n = 0 := by
    by_contra hnz
    have h2 : 2 ∣ Nat.card T := by rw [hn]; exact dvd_pow_self 2 hnz
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  exact hTne (Subgroup.eq_bot_of_card_eq T (by rw [hn, hn0]; norm_num))

end Commons.GroupTheory.StronglyEmbedded