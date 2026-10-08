import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NormalComplement

/-- If `N ⊴ G` and `G/N` is abelian, then `N` acts transitively by conjugation on the
Sylow `p`-subgroups of `G`: any two Sylow `p`-subgroups are conjugate by an element of `N`.

The proof follows the standard Frattini argument.  Let `H = N_G(S)` be the normalizer of a Sylow
`p`-subgroup `S` and put `M = N ⊔ H`.  Because `G/N` is abelian, `M/N` is normal in `G/N`, hence
`M ⊴ G`; and `S ≤ M` is a Sylow `p`-subgroup of `M`.  Frattini's argument applied to the normal
subgroup `M ⊴ G` gives `G = M ⊔ N_G(S) = M ⊔ H = M`, i.e. `N ⊔ N_G(S) = ⊤`, so every element of
`G` is of the form `n * h` with `n ∈ N` and `h ∈ N_G(S)`.  Since `G` acts transitively on its
Sylow `p`-subgroups, any `T` is `g • S`, and writing `g = n * h` exhibits `T = n • S`. -/
theorem sylow_conj_of_commutative_quotient {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hcomm : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ N)
    (S T : Sylow p G) : ∃ n : N, (n : G) • S = T := by
  -- `H = N_G(S)` and `M = N ⊔ H`.
  let H : Subgroup G := Subgroup.normalizer (S : Set G)
  let M : Subgroup G := N ⊔ H
  -- `M ⊴ G`, because `M/N` is a subgroup of the abelian group `G/N`.
  have hMnorm : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    -- decompose `m = n * h` with `n ∈ N`, `h ∈ H`
    have hm' : m ∈ (N : Set G) * (H : Set G) := by
      rw [← Subgroup.normal_mul N H]
      exact hm
    obtain ⟨n, hn, h, hh, hnh⟩ := Set.mem_mul.mp hm'
    rw [← hnh]
    have hgn : g * n * g⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem n hn g
    have hgh : g * h * g⁻¹ ∈ M := by
      have hc : g * h * g⁻¹ * h⁻¹ ∈ N := hcomm g h
      have hmem : (g * h * g⁻¹ * h⁻¹) * h ∈ N ⊔ H :=
        Subgroup.mul_mem (N ⊔ H) (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hh)
      have heq : g * h * g⁻¹ = (g * h * g⁻¹ * h⁻¹) * h := by group
      rw [heq]
      exact hmem
    have hmul : (g * n * g⁻¹) * (g * h * g⁻¹) ∈ M :=
      Subgroup.mul_mem M (Subgroup.mem_sup_left hgn) hgh
    have heq2 : g * (n * h) * g⁻¹ = (g * n * g⁻¹) * (g * h * g⁻¹) := by group
    rw [heq2]
    exact hmul
  have hSleH : (S : Subgroup G) ≤ H := Subgroup.le_normalizer
  have hSleM : (S : Subgroup G) ≤ M := hSleH.trans le_sup_right
  -- Frattini's argument for the normal subgroup `M ⊴ G` and its Sylow subgroup `S`
  have hfratt : H ⊔ M = ⊤ :=
    @Sylow.normalizer_sup_eq_top' G _ p _ M hMnorm _ S hSleM
  have hMtop : M = ⊤ := by
    have h1 : H ⊔ M = M := sup_eq_right.mpr le_sup_right
    rw [h1] at hfratt
    exact hfratt
  -- `G` acts transitively on Sylow `p`-subgroups; write the conjugating element in `N * H`
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hgM : g ∈ M := by
    rw [hMtop]
    exact Subgroup.mem_top g
  have hg' : g ∈ (N : Set G) * (H : Set G) := by
    rw [← Subgroup.normal_mul N H]
    exact hgM
  obtain ⟨n, hn, h, hh, hnh⟩ := Set.mem_mul.mp hg'
  refine ⟨⟨n, hn⟩, ?_⟩
  have hhS : h • S = S := Sylow.smul_eq_iff_mem_normalizer.mpr hh
  have hthis : (n * h) • S = T := by rw [hnh]; exact hg
  rw [mul_smul, hhS] at hthis
  exact hthis

end Work.NormalComplement
