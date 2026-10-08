import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB.Lemma51Paper
import Submission.Work.ZJB.NormalizerConj
import Submission.Work.ZJB2.Step1.exists_mem_inv_mul_mem_of_isSylowIn
import Submission.Work.ZJB2.Step1.conj_mem_centralizer_of_mem_centralizer_map_conj

/-!
# ZJB2, step (I) — Glauberman's Lemma 5.1 inside a subgroup `M`

The leaf `CpStarInOfCpInProp p G` of `Submission/Work/ZJB/Step1/Defs.lean`: `(C_p)` implies
`(C_p*)` inside every subgroup `M ≤ G`.

This is the relativised copy of `Work.ZJB.controlsStrongFusionPaper_iff_starPaper`
(`Submission/Work/ZJB/Lemma51Paper.lean`), with `T` a Sylow `p`-subgroup of `M` instead of a
Sylow `p`-subgroup of `G` and everything tested inside `M`.

**Route.** Put `N₀ = N_G(Z(J(T))) ∩ M`. Since `T ≤ N_G(Z(J(T)))` (`le_normalizer_ZJ`) and
`N₀ ≤ M`, the subgroup `T` is Sylow in `N₀`.  Given a `p`-subgroup `W ≤ N₀` and `g ∈ M` with
`g⁻¹Wg ≤ N₀`, Sylow conjugacy inside `N₀` (`exists_mem_inv_mul_mem_of_isSylowIn`) supplies
`m, k ∈ N₀` with `m⁻¹Wm ≤ T` and `k⁻¹(g⁻¹Wg)k ≤ T`.  Then `(m⁻¹Wm)^{m⁻¹gk} = k⁻¹(g⁻¹Wg)k ≤ T`,
so `(C_p)` applied in `M` to the nonempty set `m⁻¹Wm ⊆ T` and the element `m⁻¹gk` gives
`m⁻¹gk = c·n` with `c ∈ M ∩ C_G(m⁻¹Wm)` and `n ∈ M ∩ N_G(Z(J(T)))`.  The required decomposition
of `g` is

`g = (m c m⁻¹) · (m n k⁻¹)`,

with `m c m⁻¹ ∈ C_G(W)` (`conj_mem_centralizer_of_mem_centralizer_map_conj`) and
`m n k⁻¹ ∈ M ∩ N_G(Z(J(T)))`.
-/

namespace Work.ZJB2.Step1

open Subgroup Pointwise Work.GW2

set_option linter.unusedSimpArgs false in
/-- **Glauberman 1968, Lemma 5.1, inside a subgroup `M`:** `(C_p) ⟹ (C_p*)` in `M`. -/
theorem cpStarInOfCpInProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.CpStarInOfCpInProp p G := by
  intro M hCp T hT W hWM hWN hWp g hgM hgN
  -- `N₀ = N_G(Z(J(T))) ∩ M`; `T` is Sylow in `N₀`.
  set N₀ : Subgroup G := normalizer (Work.GW2.ZJ T : Set G) ⊓ M with hN₀
  have hN₀M : N₀ ≤ M := by rw [hN₀]; exact inf_le_right
  have hTN₀ : T ≤ N₀ := by
    rw [hN₀]; exact le_inf (Work.ZJB.le_normalizer_ZJ T) hT.1
  have hTN : Work.ZJB.IsSylowIn p T N₀ :=
    ⟨hTN₀, hT.2.1, fun Q hTQ hQN hQp => hT.2.2 Q hTQ (hQN.trans hN₀M) hQp⟩
  have hWN₀ : W ≤ N₀ := by rw [hN₀]; exact le_inf hWN hWM
  -- conjugate `W` into `T` by `m ∈ N₀`, and `g⁻¹Wg` into `T` by `k ∈ N₀`
  obtain ⟨m, hmN₀, hmW⟩ := exists_mem_inv_mul_mem_of_isSylowIn (N := N₀) (V := W) hTN hWN₀ hWp
  set Vg : Subgroup G := W.map (MulAut.conj g⁻¹).toMonoidHom with hVg
  have hVgp : IsPGroup p Vg :=
    hWp.of_equiv (Subgroup.equivMapOfInjective W (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)
  have hVgN₀ : Vg ≤ N₀ := by
    rw [hVg, hN₀]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨?_, ?_⟩
    · have hx : ((MulAut.conj g⁻¹).toMonoidHom w : G) = g⁻¹ * w * g := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hx]
      exact hgN w hw
    · have hx : ((MulAut.conj g⁻¹).toMonoidHom w : G) = g⁻¹ * w * g := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hx]
      exact M.mul_mem (M.mul_mem (M.inv_mem hgM) (hWM hw)) hgM
  obtain ⟨k, hkN₀, hkV⟩ :=
    exists_mem_inv_mul_mem_of_isSylowIn (N := N₀) (V := Vg) hTN hVgN₀ hVgp
  -- `(C_p)` in `M`, applied to the nonempty set `m⁻¹Wm ⊆ T` and the element `m⁻¹gk`
  obtain ⟨c, n, hcM, hcW₁, hnM, hnN, hgcn⟩ :=
    hCp T hT ((W.map (MulAut.conj m⁻¹).toMonoidHom : Subgroup G) : Set G)
      ⟨(MulAut.conj m⁻¹).toMonoidHom 1, ⟨1, W.one_mem, rfl⟩⟩
      (by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
        have hx : ((MulAut.conj m⁻¹).toMonoidHom w : G) = m⁻¹ * w * m := by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rw [hx]
        exact hmW w hw)
      (m⁻¹ * g * k)
      (M.mul_mem (M.mul_mem (M.inv_mem (hN₀M hmN₀)) hgM) (hN₀M hkN₀))
      (by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
        have hkey : (m⁻¹ * g * k)⁻¹ * ((MulAut.conj m⁻¹).toMonoidHom w) * (m⁻¹ * g * k)
            = k⁻¹ * ((MulAut.conj g⁻¹).toMonoidHom w) * k := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          group
        rw [hkey]
        exact hkV _ (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩))
  -- assemble: `g = (m c m⁻¹) * (m n k⁻¹)`
  refine ⟨m * c * m⁻¹, m * n * k⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.mul_mem (M.mul_mem (hN₀M hmN₀) hcM) (M.inv_mem (hN₀M hmN₀))
  · exact conj_mem_centralizer_of_mem_centralizer_map_conj hcW₁
  · exact M.mul_mem (M.mul_mem (hN₀M hmN₀) hnM) (M.inv_mem (hN₀M hkN₀))
  · have hmN : m ∈ normalizer (ZJ T : Set G) :=
      (Subgroup.mem_inf.mp (by rw [← hN₀]; exact hmN₀)).1
    have hkN : k ∈ normalizer (ZJ T : Set G) :=
      (Subgroup.mem_inf.mp (by rw [← hN₀]; exact hkN₀)).1
    exact (normalizer (ZJ T : Set G)).mul_mem
      ((normalizer (ZJ T : Set G)).mul_mem hmN hnN) ((normalizer (ZJ T : Set G)).inv_mem hkN)
  · calc g = m * (m⁻¹ * g * k) * k⁻¹ := by group
      _ = m * (c * n) * k⁻¹ := by rw [hgcn]
      _ = (m * c * m⁻¹) * (m * n * k⁻¹) := by group

end Work.ZJB2.Step1
