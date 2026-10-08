import Mathlib
import Submission.Work.CORE2B.HallPerPrime_case2
import Submission.Work.CORE2B.HallPerPrime_aux
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.API

namespace Work.CORE2B

set_option linter.unusedVariables false

-- GW design pass 18, item A′, leaf H2 (copied from `Core18PairNormalizerLeNormalizerPX.lean`):
-- Bender p. 222, "Clearly, `N_S(⟨t,s⟩) ≤ M`" — the `S`-normalizer of the four-group `⟨t,s⟩`
-- normalizes `X = O_p(U) ∩ C_G(s)`.
-- Sketch: let `σ ∈ S` normalize `V = ⟨t,s⟩`.  `σ` normalizes `O_p(U)` (`S` normalizes `U`, hence
-- its `p`-core); `σ t σ⁻¹ = t` (`t` is central in `S`), so `σ s σ⁻¹ ∈ V` is an involution `≠ t`,
-- hence `∈ {s, ts}`; conjugation maps `O_p(U) ∩ C(s)` to `O_p(U) ∩ C(σsσ⁻¹)`, and
-- `O_p(U) ∩ C(ts) = O_p(U) ∩ C(s)` since `t` centralizes `U`.
--
-- The proof below is organised slightly differently (and uses less than the sketch): if
-- `x ∈ O_p(U)` commutes with `t` (true for all `x ∈ U`, `t_commutes_U`) then
--   `x` commutes with `s`  ⟺  `x` commutes with `σ s σ⁻¹`,
-- because `x t x⁻¹ = t` and `σ t σ⁻¹ = t`, so `⟨t, σ s σ⁻¹⟩ = σ⟨t,s⟩σ⁻¹ = ⟨t,s⟩`
-- (`σ` normalises `V = ⟨t,s⟩`).  Hence `σ` carries `O_p(U) ∩ C(s)` onto
-- `O_p(U) ∩ C(σ s σ⁻¹) = O_p(U) ∩ C(s)`.
theorem C18PairNormalizerLeNormalizerPX_proved {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (s : G)
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) (p : ℕ) [Fact p.Prime] :
    (B.S : Subgroup G) ⊓
        Subgroup.normalizer ((Subgroup.closure ({B.t, s} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Work.CORE2B.pX B s p : Subgroup G) : Set G) := by
  intro σ hσ
  obtain ⟨hσS, hσN⟩ := Subgroup.mem_inf.mp hσ
  set V : Subgroup G := Subgroup.closure ({B.t, s} : Set G) with hVdef
  -- `t` is central in `S`, hence fixed by conjugation by `σ`.
  have hσt : σ * B.t * σ⁻¹ = B.t := by
    rw [t_central_in_S B σ hσS, mul_assoc, mul_inv_cancel, mul_one]
  -- `σ` normalises `V`.
  have hVσ : V.map (MulAut.conj σ).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hσN
  have hs_mem_V : s ∈ V := Subgroup.subset_closure (by simp)
  have hv_mem_V : σ * s * σ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hσN s).mp hs_mem_V
  -- `(conj σ) '' {t,s} = {t, σsσ⁻¹}`
  have himg : (MulAut.conj σ) '' ({B.t, s} : Set G) = ({B.t, σ * s * σ⁻¹} : Set G) := by
    rw [Set.image_pair]
    simp only [MulAut.conj_apply]
    rw [hσt]
  -- hence `⟨t, σ s σ⁻¹⟩ = σ⟨t,s⟩σ⁻¹ = ⟨t,s⟩ = V`.
  have hVtv : Subgroup.closure ({B.t, σ * s * σ⁻¹} : Set G) = V := by
    rw [← hVσ, hVdef, MonoidHom.map_closure]
    erw [himg]
  -- Key point: an element `x` commuting with `t` commutes with `s` iff it commutes with
  -- `σ s σ⁻¹`.
  have key : ∀ x : G, x * B.t = B.t * x →
      (x * s = s * x ↔ x * (σ * s * σ⁻¹) = (σ * s * σ⁻¹) * x) := by
    intro x hxt
    constructor
    · intro hxs
      -- `x` commutes with both generators `t`, `s` of `V`, hence with all of `V`,
      -- in particular with `σ s σ⁻¹ ∈ V`.
      have hle : V ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [hVdef]
        refine (Subgroup.closure_le _).mpr ?_
        intro y hy
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        rcases hy with rfl | hy
        · exact hxt
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hxs
      exact (Subgroup.mem_centralizer_iff.mp (hle hv_mem_V) x (Set.mem_singleton x))
    · intro hxv
      -- `x` commutes with both generators `t`, `σ s σ⁻¹` of `⟨t, σ s σ⁻¹⟩ = V`,
      -- in particular with `s ∈ V`.
      have hle : V ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [← hVtv]
        refine (Subgroup.closure_le _).mpr ?_
        intro y hy
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        rcases hy with rfl | hy
        · exact hxt
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hxv
      exact (Subgroup.mem_centralizer_iff.mp (hle hs_mem_V) x (Set.mem_singleton x))
  -- Comparison of the centralizers inside `O_p(U)`.
  have hXeq : Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({σ * s * σ⁻¹} : Set G)
      = Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hxt : x * B.t = B.t * x :=
        (t_commutes_U B x ((in_le_self B.U p ∅).2.1 hx1)).symm
      have hxv : x * (σ * s * σ⁻¹) = (σ * s * σ⁻¹) * x :=
        (Subgroup.mem_centralizer_iff.mp hx2 (σ * s * σ⁻¹) (Set.mem_singleton _)).symm
      refine Subgroup.mem_inf.mpr ⟨hx1, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((key x hxt).mpr hxv).symm
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hxt : x * B.t = B.t * x :=
        (t_commutes_U B x ((in_le_self B.U p ∅).2.1 hx1)).symm
      have hxs : x * s = s * x :=
        (Subgroup.mem_centralizer_iff.mp hx2 s (Set.mem_singleton s)).symm
      refine Subgroup.mem_inf.mpr ⟨hx1, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact ((key x hxt).mp hxs).symm
  -- Conjugation by `σ` fixes `X = O_p(U) ∩ C(s)`.
  have hmap : (Work.CORE2B.pX B s p : Subgroup G).map (MulAut.conj σ).toMonoidHom
      = Work.CORE2B.pX B s p := by
    change (Work.GW2.pCoreIn p B.U ⊓ Subgroup.centralizer ({s} : Set G)).map
        (MulAut.conj σ).toMonoidHom = _
    rw [Subgroup.map_inf (Work.GW2.pCoreIn p B.U) (Subgroup.centralizer ({s} : Set G))
      (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective]
    erw [map_conj_pCoreIn (U := B.U) (p := p) (mem_normalizer_U_of_mem_S B hσS),
        hallXodd_map_centralizer (MulAut.conj σ) ({s} : Set G), Set.image_singleton, hXeq]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

end Work.CORE2B
