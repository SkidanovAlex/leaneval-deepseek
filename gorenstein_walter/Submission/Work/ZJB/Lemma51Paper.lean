import Submission.Work.ZJB.DefsPaper
import Submission.Work.ZJB.ZJBasic
import Submission.Work.ZJB.NormalizerConj

/-!
# ZJB — Glauberman 1968, Lemma 5.1, in the paper's own convention

`(C_p) ⇔ (C_p*)` for a Sylow `p`-subgroup `S` and the characteristic functor `K = Z(J(·))`
(paper, p. 1117).  The two statements are `ControlsStrongFusionPaper` and
`ControlsStrongFusionPaperStar` (`DefsPaper.lean`), i.e. the printed conditions with the paper's
convention `x^g = g⁻¹xg`; see `NOTES_ZJB.md` §5 for why that matters.

* `(C_p*) ⟹ (C_p)`: a nonempty `W ⊆ S` generates `⟨W⟩ ≤ S ≤ N_G(K)`.
* `(C_p) ⟹ (C_p*)`: with `N = N_G(K)` and `W ≤ N` a `p`-subgroup, use
  `exists_mem_normalizer_inv_mul_mem` to find `m, k ∈ N` with `W^m ⊆ S` and `(W^g)^k ⊆ S`; then
  `(W^m)^{m⁻¹gk} = W^{gk} ⊆ S`, so `(C_p)` at the pair `(W^m, m⁻¹gk)` gives `m⁻¹gk = c·n`, and
  `g = (m c m⁻¹)·(m n k⁻¹)` is the required decomposition.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup
open Pointwise

variable {G : Type*} [Group G] [Finite G]

/-- **Glauberman 1968, Lemma 5.1** (paper's convention): `(C_p) ⇔ (C_p*)` for `K = Z(J(·))`. -/
theorem controlsStrongFusionPaper_iff_starPaper (p : ℕ) [Fact p.Prime] (S : Sylow p G) :
    ControlsStrongFusionPaper (S : Subgroup G) (ZJ (S : Subgroup G)) ↔
      ControlsStrongFusionPaperStar p (ZJ (S : Subgroup G)) := by
  set K : Subgroup G := ZJ (S : Subgroup G) with hK
  have hSN : (S : Subgroup G) ≤ normalizer (K : Set G) := le_normalizer_ZJ _
  constructor
  · -- `(C_p) ⟹ (C_p*)`
    intro h W hWN hWp g hgN
    obtain ⟨m, hmN, hmW⟩ := exists_mem_normalizer_inv_mul_mem (N := normalizer (K : Set G))
      (V := W) S hSN hWN hWp
    have hWgp : IsPGroup p (W.map (MulAut.conj g⁻¹).toMonoidHom) :=
      hWp.of_equiv (Subgroup.equivMapOfInjective W (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective)
    have hWgN : W.map (MulAut.conj g⁻¹).toMonoidHom ≤ normalizer (K : Set G) := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hgN w hw
    obtain ⟨k, hkN, hkWg⟩ := exists_mem_normalizer_inv_mul_mem
      (N := normalizer (K : Set G)) (V := W.map (MulAut.conj g⁻¹).toMonoidHom)
      S hSN hWgN hWgp
    -- `(C_p)` at the pair `(W^m, m⁻¹gk)`
    obtain ⟨c, n, hc, hn, hx⟩ :=
      h (W.map (MulAut.conj m⁻¹).toMonoidHom)
        ⟨(MulAut.conj m⁻¹).toMonoidHom 1,
          Subgroup.mem_map.mpr ⟨1, W.one_mem, rfl⟩⟩
        (by
          intro x hx
          obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
          have h1 : (MulAut.conj m⁻¹).toMonoidHom w = m⁻¹ * w * m := by
            simp [MulAut.conj_apply]
          rw [h1]
          exact hmW w hw)
        (m⁻¹ * g * k)
        (by
          intro v hv
          obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
          have hkey : (m⁻¹ * g * k)⁻¹ * ((MulAut.conj m⁻¹).toMonoidHom w) * (m⁻¹ * g * k)
              = k⁻¹ * ((MulAut.conj g⁻¹).toMonoidHom w) * k := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
            group
          rw [hkey]
          exact hkWg _ (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩))
    refine ⟨m * c * m⁻¹, m * n * k⁻¹, ?_, ?_, ?_⟩
    · -- `m * c * m⁻¹ ∈ C_G(W)`
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hcomm : ((MulAut.conj m⁻¹).toMonoidHom w) * c
          = c * ((MulAut.conj m⁻¹).toMonoidHom w) :=
        (Subgroup.mem_centralizer_iff.mp hc) _
          (Subgroup.mem_map.mpr ⟨w, hw, by simp [MulAut.conj_apply]⟩)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hcomm
      calc w * (m * c * m⁻¹) = m * ((m⁻¹ * w * m) * c) * m⁻¹ := by group
        _ = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by rw [hcomm]
        _ = (m * c * m⁻¹) * w := by group
    · exact (normalizer (K : Set G)).mul_mem ((normalizer (K : Set G)).mul_mem hmN hn)
        ((normalizer (K : Set G)).inv_mem hkN)
    · -- `g = (m * c * m⁻¹) * (m * n * k⁻¹)`
      calc g = m * (m⁻¹ * g * k) * k⁻¹ := by group
        _ = m * (c * n) * k⁻¹ := by rw [hx]
        _ = (m * c * m⁻¹) * (m * n * k⁻¹) := by group
  · -- `(C_p*) ⟹ (C_p)`
    intro h W hWne hWS g hgS
    set U : Subgroup G := Subgroup.closure W with hU
    have hUS : U ≤ (S : Subgroup G) := (Subgroup.closure_le _).mpr hWS
    have hUN : U ≤ normalizer (K : Set G) := hUS.trans hSN
    have hUp : IsPGroup p U := S.isPGroup'.to_le hUS
    have hUmap : U.map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
      rw [hU, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨w, hw, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hgS w hw
    have hUNg : ∀ u ∈ U, g⁻¹ * u * g ∈ normalizer (K : Set G) := by
      intro u hu
      have := hUmap (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
      exact hSN (by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this)
    obtain ⟨c, n, hc, hn, hgn⟩ := h U hUN hUp g hUNg
    exact ⟨c, n, (Subgroup.centralizer_le Subgroup.subset_closure) hc, hn, hgn⟩

end Work.ZJB
