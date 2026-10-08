import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.irr_apply_eq_zero_of_centralizer_inf_eq_bot
import Submission.Work.Tame.mem_hatNp_iff
import Submission.Work.Tame.hatNp_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-- Feit–Thompson Lemma 9.2's first step, i.e. Lemma 4.3 applied to `𝔎_i ⊴ 𝔑_i`: an irreducible
character `θ` of `𝔑_i = N(𝔎_i)` which does not contain `𝔎_i` in its kernel (written
`∃ H ∈ 𝔎_i, θ H ≠ θ 1`) vanishes on `𝔑_i − Ñ_i − 𝔎_i`.

Indeed, if `N ∈ 𝔑_i`, `N ∉ Ñ_i` and `N ∉ 𝔎_i`, then `N ∉ hatNp (Hs i) = hatNCore (Hs i) \ 𝔎_i`, so
no non-identity element of `𝔎_i` commutes with `N`, i.e. `C(N) ∩ 𝔎_i = 1`; Lemma 4.3 (with
`𝔎_i ⊴ 𝔑_i`) then gives `θ N = 0`. -/
theorem irr_vanishes_off_hatN {X : Type*} [Group X] [Fintype X] {Lhat : Set X} {n : ℕ}
    {Hs : Fin n → Subgroup X} (h : IsTamelyImbedded Lhat n Hs)
    (hD : (Dset Lhat).Nonempty) (i : Fin n)
    {θ : ↥(Lgrp (Hs i : Set X)) → ℂ} (hθ : θ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)))
    (hk : ∃ H : ↥(Hs i), θ ⟨(H : X), (Hs i).le_normalizer H.2⟩ ≠ θ 1)
    {N : ↥(Lgrp (Hs i : Set X))} (hN : (N : X) ∉ hatN (Hs i))
    (hNK : (N : X) ∉ (Hs i : Set X)) : θ N = 0 := by
  classical
  -- `N ∉ Ñ_i = hatNCore i \ 𝔎_i^#` together with `N ∉ 𝔎_i` gives `N ∉ hatNCore i`.
  have hpunct : (N : X) ∉ punct ((Hs i : Set X)) := by
    rw [mem_punct]
    intro hh
    exact hNK hh.1
  have hNcore : (N : X) ∉ hatNCore (Hs i) := by
    intro hmem
    apply hN
    simp only [hatN, Set.mem_sdiff]
    exact ⟨hmem, hpunct⟩
  -- Hence every element of `𝔎_i` commuting with `N` is trivial.
  have hcomm : ∀ H : X, H ∈ (Hs i) → (N : X) * H = H * (N : X) → H = 1 := by
    intro H hHK hHc
    by_contra hHne
    have : (N : X) ∈ hatNCore (Hs i) := by
      rw [mem_hatNCore_iff_local]
      exact ⟨N.2, H, hHK, hHne, hHc⟩
    exact hNcore this
  -- `𝔎_i` is normal in its normalizer `𝔑_i`.
  have hnorm : ((Hs i).subgroupOf (Lgrp (Hs i : Set X))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := Lgrp (Hs i : Set X)) (N := Hs i) le_rfl
  -- `θ` does not contain `𝔎_i` in its kernel.
  have hk' : ∃ h : ↥(Lgrp (Hs i : Set X)),
      h ∈ (Hs i).subgroupOf (Lgrp (Hs i : Set X)) ∧ θ h ≠ θ 1 := by
    obtain ⟨H, hH⟩ := hk
    exact ⟨⟨(H : X), (Hs i).le_normalizer H.2⟩,
      by rw [Subgroup.mem_subgroupOf]; exact H.2, hH⟩
  -- `C_{𝔑_i}(N) ∩ 𝔎_i = 1`.
  have hx : Subgroup.centralizer ({N} : Set ↥(Lgrp (Hs i : Set X))) ⊓
      ((Hs i).subgroupOf (Lgrp (Hs i : Set X))) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgcent, hgK⟩ := hg
    rw [Subgroup.mem_subgroupOf] at hgK
    have hcommG : (g : X) * (N : X) = (N : X) * (g : X) := by
      have h1 := hgcent
      rw [Subgroup.mem_centralizer_singleton_iff] at h1
      simpa using congrArg Subtype.val h1
    have hg1 : (g : X) = 1 := hcomm (g : X) hgK hcommG.symm
    exact Subtype.ext (by rw [hg1]; rfl)
  -- Lemma 4.3 (with `𝔎_i ⊴ 𝔑_i`).
  exact irr_apply_eq_zero_of_centralizer_inf_eq_bot hnorm hθ hk' hx

end Work.Tame
