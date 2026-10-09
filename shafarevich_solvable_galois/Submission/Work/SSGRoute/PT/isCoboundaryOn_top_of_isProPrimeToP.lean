import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.descentInflationFinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹` of a pro-prime-to-`p` compact group with finite `𝔽_p`-coefficients vanishes

`Work.SSGRoute.PT.isCoboundaryOn_top_of_isProPrimeToP`: if `Γ` is a compact topological group all
of whose finite-index normal subgroups have index prime to `p` (`IsProPrimeToP`), acting on a
finite `𝔽_p`-module `N` with an open kernel, then every locally constant crossed homomorphism
(`IsCocycleOn`) is a coboundary (`IsCoboundaryOn`).

Route: let `W ⊴ Γ` be an open normal subgroup contained in the local-constancy subgroup of `f` and
in the open subgroup acting trivially on `N`.  Then `f` is right-`W`-invariant and descends to the
finite group `Γ ⧸ W`, of order coprime to `p` (by `IsProPrimeToP`), where the averaging lemma
`Work.SSGRoute.crossed_hom_average` produces the primitive.
-/

namespace Work.SSGRoute.PT

open _root_.SSGRoute

theorem isCoboundaryOn_top_of_isProPrimeToP
    (p : ℕ) [Fact p.Prime] {Γ N : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction Γ N]
    [SMulCommClass Γ (ZMod p) N] [Finite N]
    (hpro : Work.SSGRoute.IsProPrimeToP p Γ)
    (hker : ∃ U₀ : Subgroup Γ, IsOpen (U₀ : Set Γ) ∧ ∀ g ∈ U₀, ∀ n : N, g • n = n)
    (f : Γ → N) (hf : SSGRoute.IsCocycleOn (MonoidHom.id Γ) ⊤ f)
    (hlc : SSGRoute.IsLocConstOn (⊤ : Subgroup Γ) f) :
    SSGRoute.IsCoboundaryOn (MonoidHom.id Γ) ⊤ f := by
  classical
  obtain ⟨U, hUopen, hUinv⟩ := hlc
  obtain ⟨U₀, hU₀open, hU₀triv⟩ := hker
  set K : Subgroup Γ := U ⊓ U₀ with hK
  have hKopen : IsOpen (K : Set Γ) := by
    rw [hK, Subgroup.coe_inf]; exact hUopen.inter hU₀open
  have hKclosed : IsClosed (K : Set Γ) := Subgroup.isClosed_of_isOpen K hKopen
  set W : Subgroup Γ := K.normalCore with hW
  haveI hWn : W.Normal := by rw [hW]; exact Subgroup.normalCore_normal K
  have hWle : W ≤ K := by rw [hW]; exact Subgroup.normalCore_le K
  have hWclosed : IsClosed (W : Set Γ) := by
    rw [hW]; exact Subgroup.normalCore_isClosed K hKclosed
  haveI hKfin : K.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    exact Subgroup.quotient_finite_of_isOpen K hKopen
  have hWfin : W.FiniteIndex := by rw [hW]; infer_instance
  have hWopen : IsOpen (W : Set Γ) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex W hWclosed
  haveI : Finite (Γ ⧸ W) := Subgroup.quotient_finite_of_isOpen W hWopen
  haveI : Fintype (Γ ⧸ W) := Fintype.ofFinite _
  have hcop : Nat.Coprime (Fintype.card (Γ ⧸ W)) p := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index_eq_card W]
    exact (hpro W hWfin).symm
  -- `f 1 = 0`
  have hf1 : f 1 = 0 := by
    have h := hf 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    simp only [MonoidHom.id_apply, one_mul, one_smul] at h
    have h3 : f 1 + (0 : N) = f 1 + f 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h3).symm
  -- `f` is right-`W`-invariant
  have hWinv : ∀ g : Γ, ∀ w ∈ W, f (g * w) = f g := by
    intro g w hw
    exact hUinv g (Subgroup.mem_top g) w (hWle hw).1 (Subgroup.mem_top w)
  -- the descended function
  let F : Γ ⧸ W → N := fun q => f (Quotient.out q)
  have hFmk : ∀ g : Γ, F (QuotientGroup.mk' W g) = f g := by
    intro g
    let q : Γ ⧸ W := QuotientGroup.mk' W g
    have hq : q = QuotientGroup.mk' W g := rfl
    have hw : g⁻¹ * Quotient.out q ∈ W := by
      refine (QuotientGroup.eq).mp ?_
      have h1 : ((Quotient.out q : Γ) : Γ ⧸ W) = (g : Γ ⧸ W) := by
        rw [QuotientGroup.out_eq', hq, QuotientGroup.mk'_apply]
      exact h1.symm
    show f (Quotient.out q) = f g
    rw [show Quotient.out q = g * (g⁻¹ * Quotient.out q) from by group]
    exact hWinv g _ hw
  -- the action of `Γ ⧸ W` on `N`
  let actEnd : Γ →* AddMonoid.End N := DistribMulAction.toAddMonoidEnd Γ N
  have hWker : W ≤ actEnd.ker := by
    intro w hw
    ext n
    show w • n = n
    exact hU₀triv w (hWle hw).2 n
  let ρ : Γ ⧸ W →* AddMonoid.End N := QuotientGroup.lift W actEnd hWker
  letI : DistribMulAction (Γ ⧸ W) N := DistribMulAction.compHom N ρ
  haveI : SMulCommClass (Γ ⧸ W) (ZMod p) N :=
    ⟨fun q c n => by
      induction q using QuotientGroup.induction_on with
      | _ g =>
        show ρ (QuotientGroup.mk' W g) (c • n) = c • ρ (QuotientGroup.mk' W g) n
        rw [show ρ (QuotientGroup.mk' W g) = actEnd g from QuotientGroup.lift_mk' W hWker g]
        exact smul_comm g c n⟩
  have hsmul_mk : ∀ (g : Γ) (n : N), (QuotientGroup.mk' W g) • n = g • n := by
    intro g n
    show ρ (QuotientGroup.mk' W g) n = g • n
    rw [show ρ (QuotientGroup.mk' W g) = actEnd g from QuotientGroup.lift_mk' W hWker g]
    rfl
  -- `F` is a crossed homomorphism
  have hF : ∀ q q' : Γ ⧸ W, F (q * q') = q • F q' + F q := by
    intro q q'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective W q'
    rw [← map_mul, hFmk, hFmk, hFmk]
    have h1 := hf g (Subgroup.mem_top g) h (Subgroup.mem_top h)
    simp only [MonoidHom.id_apply] at h1
    rw [h1, hsmul_mk]
    abel
  obtain ⟨γ, -, hγ⟩ := crossed_hom_average hcop F hF
  refine ⟨γ, ?_⟩
  intro g _
  rw [show f g = F (QuotientGroup.mk' W g) from (hFmk g).symm, hγ (QuotientGroup.mk' W g)]
  show (QuotientGroup.mk' W g) • γ - γ = (MonoidHom.id Γ) g • γ - γ
  rw [MonoidHom.id_apply, hsmul_mk]

end Work.SSGRoute.PT
