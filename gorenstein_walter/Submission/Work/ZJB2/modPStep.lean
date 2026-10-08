import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.isSylowInOfLe
import Submission.Work.ZJB2.zjMap
import Submission.Work.GLUE.PcoreApi
import Submission.Work.ZJB.ZJApi.ZJ_ne_bot

/-!
# GW design 17, item B (ZJB2) — leaf `modPStep` (T52.mod) — PROVED

Source: Glauberman 1968, pp. 1121–1122, (5.6)–(5.8).

**Route.**  Write `P = O_p(G)`, `Ḡ = G/P`, `mk : G →* G ⧸ P`, and let `S̄` be the image of
the Sylow subgroup `S`.  Hypothesis (b) at `G/P` — `SatisfiesCpPaper p (G ⧸ P)` — applies at
`S̄` and `W̄ = V.map mk`: since `g⁻¹Vg ⊆ S`, the image `ḡ = mk g` satisfies
`ḡ = c̄ · n̄` with `c̄ ∈ C_{Ḡ}(W̄)`, `n̄ ∈ N_{Ḡ}(Z(J(S̄)))`.  Lifting `c̄` to `c` and `n̄` to `n`:
(5.6) `ḡ = c̄ n̄` and `mk n = n̄`.

Now `T := (Z(J(S̄))).comap mk` (5.7).  Because `mk(T) = Z(J(S̄)) ≤ S̄ = mk(S)`, we have
`P ≤ T ≤ S`, so `T` is a `p`-group; `T ≠ P` because `Z(J(S̄)) ≠ 1` (as `V ⊄ P` forces
`S̄ ≠ 1`, and `Z(J(·))` of a nontrivial `p`-group is nontrivial); `S ≤ N_G(T)` because `S̄`
normalizes `Z(J(S̄))`; `n ∈ N_G(T)` since `n̄ ∈ N_{Ḡ}(Z(J(S̄)))`.  If `N_G(T) = ⊤` then
`T ⊴ G` and `T ≤ O_p(G) = P`, a contradiction, so `N_G(T) ≠ ⊤` and hypothesis (b) inside
the proper subgroup `N_G(T)` applies: `CpIn p (N_G(T))`.

Since `S` is Sylow in `G` it is Sylow in `N_G(T)`, and `n⁻¹Vn ⊆ S` (because
`n̄⁻¹ W̄ n̄ = (c̄ n̄)⁻¹ W̄ (c̄ n̄) = ḡ⁻¹ W̄ ḡ` and `P ≤ S`), so (G3) + `CpIn p (N_G(T))` at
`T₀ = S`, `W = V` give `n = d · m` with `d ∈ N_G(T) ∩ C_G(V)` and
`m ∈ N_G(T) ∩ N_G(Z(J(S)))`.  Finally `y := g m⁻¹ = (g n⁻¹) · d` lies in
`C_G(V̄) = Cbar P V` as the product of `g n⁻¹` (which maps to `c̄ ∈ C_{Ḡ}(W̄)`) and of
`d` (which centralizes `V`), and `g = y · m`.
-/

namespace Work.ZJB2

open Subgroup Work.GW2 Work.ZJB

theorem modPStep (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.ModPStepProp p G := by
  intro hBsub hBq S V hVS hVP g hg
  set P : Subgroup G := pCore p G with hPdef
  haveI hPn : P.Normal := hPdef ▸ Work.GW2.pCore_normal p G
  set mk : G →* G ⧸ P := QuotientGroup.mk' P with hmkdef
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective P
  have hker : mk.ker = P := QuotientGroup.ker_mk' P
  have hPtS : P ≤ (S : Subgroup G) := hPdef ▸ Work.GW2.pCore_le_sylow S
  -- the image of `S` in `G/P`
  obtain ⟨Sbar, hSbar⟩ : ∃ Sbar : Sylow p (G ⧸ P),
      (Sbar : Subgroup (G ⧸ P)) = (S : Subgroup G).map mk :=
    ⟨Sylow.mapSurjective (f := mk) hsurj S, Sylow.coe_mapSurjective hsurj S⟩
  have hSbarP : IsPGroup p (Sbar : Subgroup (G ⧸ P)) := Sbar.isPGroup'
  have hSbarNe : (Sbar : Subgroup (G ⧸ P)) ≠ ⊥ := by
    intro hbot
    have hSP : (S : Subgroup G) ≤ P := by
      intro x hx
      have h1 : mk x ∈ (Sbar : Subgroup (G ⧸ P)) := by
        rw [hSbar]; exact Subgroup.mem_map_of_mem mk hx
      rw [hbot] at h1
      have h2 : mk x = 1 := Subgroup.mem_bot.mp h1
      have h3 : x ∈ mk.ker := MonoidHom.mem_ker.mpr h2
      rwa [hker] at h3
    exact hVP (hVS.trans hSP)
  have hZJne : Work.GW2.ZJ (Sbar : Subgroup (G ⧸ P)) ≠ ⊥ :=
    Work.ZJB.ZJApi.ZJ_ne_bot hSbarP hSbarNe
  -- (5.6): `(C_p)` in `G/P` at `S̄` and `W̄ = V̄`
  obtain ⟨cbar, nbar, hcbar, hnbar, hgn⟩ :=
    hBq Sbar ((V.map mk : Subgroup (G ⧸ P)) : Set (G ⧸ P))
      ⟨1, (V.map mk).one_mem⟩
      (by
        intro w hw
        rw [hSbar]
        exact Subgroup.map_mono hVS hw)
      (mk g)
      (by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
        have he : (mk g)⁻¹ * mk v * mk g = mk (g⁻¹ * v * g) := by simp [map_mul]
        rw [he, hSbar]
        exact Subgroup.mem_map_of_mem mk (hg v hv))
  obtain ⟨c, hc⟩ := hsurj cbar
  obtain ⟨n, hn⟩ := hsurj nbar
  -- (5.7): `T = Z(J(S̄)).comap mk`
  set T : Subgroup G := Subgroup.comap mk (Work.GW2.ZJ (Sbar : Subgroup (G ⧸ P))) with hTdef
  have hPT : P ≤ T := by
    intro x hx
    rw [hTdef, Subgroup.mem_comap]
    have h2 : mk x = 1 := by
      have h3 : x ∈ mk.ker := by rwa [hker]
      exact MonoidHom.mem_ker.mp h3
    rw [h2]
    exact Subgroup.one_mem _
  have hTS : T ≤ (S : Subgroup G) := by
    have hcomap : Subgroup.comap mk (Subgroup.map mk (S : Subgroup G)) = (S : Subgroup G) :=
      Subgroup.comap_map_eq_self (f := mk) (by rw [hker]; exact hPtS)
    calc T = Subgroup.comap mk (Work.GW2.ZJ (Sbar : Subgroup (G ⧸ P))) := hTdef
      _ ≤ Subgroup.comap mk (Sbar : Subgroup (G ⧸ P)) :=
          Subgroup.comap_mono (Work.GW2.ZJ_le _)
      _ = Subgroup.comap mk (Subgroup.map mk (S : Subgroup G)) := by rw [hSbar]
      _ = (S : Subgroup G) := hcomap
  have hTne : T ≠ P := by
    intro hTP
    have hmap : Subgroup.map mk T = Work.GW2.ZJ (Sbar : Subgroup (G ⧸ P)) := by
      rw [hTdef]
      exact Subgroup.map_comap_eq_self (f := mk)
        (by rw [MonoidHom.range_eq_top.mpr hsurj]; exact le_top)
    have hkerbot : Subgroup.map mk P = ⊥ := by
      apply le_bot_iff.mp
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have h2 : mk x = 1 := MonoidHom.mem_ker.mp (by rwa [hker])
      rw [h2]
      exact Subgroup.mem_bot.mpr rfl
    exact hZJne (by rw [← hmap, hTP, hkerbot])
  have hSleN : (S : Subgroup G) ≤ Subgroup.normalizer (T : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro t
    simp only [hTdef, Subgroup.mem_comap]
    have he : mk (s * t * s⁻¹) = mk s * mk t * (mk s)⁻¹ := by simp [map_mul]
    rw [he]
    have hsbar : mk s ∈ (Sbar : Subgroup (G ⧸ P)) := by
      rw [hSbar]; exact Subgroup.mem_map_of_mem mk hs
    exact Subgroup.mem_normalizer_iff.mp
      (Work.ZJB.le_normalizer_ZJ (Sbar : Subgroup (G ⧸ P)) hsbar) (mk t)
  have hNTne : Subgroup.normalizer (T : Set G) ≠ ⊤ := by
    intro htop
    haveI : T.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hTp : IsPGroup p T := (S.isPGroup').to_le hTS
    have hle : T ≤ pCore p G := Work.GW2.le_pCore_of_normal_isPGroup hTp
    have hle' : T ≤ P := hPdef ▸ hle
    exact hTne (le_antisymm hle' hPT)
  have hnN : n ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    simp only [hTdef, Subgroup.mem_comap]
    have he : mk (n * t * n⁻¹) = nbar * mk t * nbar⁻¹ := by
      have h0 : mk (n * t * n⁻¹) = mk n * mk t * (mk n)⁻¹ := by simp [map_mul]
      rw [h0, hn]
    rw [he]
    exact Subgroup.mem_normalizer_iff.mp hnbar (mk t)
  -- `n⁻¹ V n ⊆ S`
  have hVn : ∀ v ∈ V, n⁻¹ * v * n ∈ (S : Subgroup G) := by
    intro v hv
    have hcv : cbar * mk v = mk v * cbar :=
      (Subgroup.mem_centralizer_iff.mp hcbar (mk v) (Subgroup.mem_map_of_mem mk hv)).symm
    have heq : mk (n⁻¹ * v * n) = mk (g⁻¹ * v * g) := by
      have hcancel : cbar * mk v * cbar⁻¹ = mk v := by rw [hcv]; group
      calc mk (n⁻¹ * v * n) = (mk n)⁻¹ * mk v * mk n := by simp [map_mul]
        _ = nbar⁻¹ * mk v * nbar := by rw [hn]
        _ = (cbar⁻¹ * mk g)⁻¹ * mk v * (cbar⁻¹ * mk g) := by
              rw [show nbar = cbar⁻¹ * mk g by rw [hgn]; group]
        _ = (mk g)⁻¹ * (cbar * mk v * cbar⁻¹) * mk g := by group
        _ = (mk g)⁻¹ * mk v * mk g := by rw [hcancel]
        _ = mk (g⁻¹ * v * g) := by simp [map_mul]
    have hmem : mk (n⁻¹ * v * n) ∈ Subgroup.map mk (S : Subgroup G) := by
      rw [heq]; exact Subgroup.mem_map_of_mem mk (hg v hv)
    have hcomap : Subgroup.comap mk (Subgroup.map mk (S : Subgroup G)) = (S : Subgroup G) :=
      Subgroup.comap_map_eq_self (f := mk) (by rw [hker]; exact hPtS)
    exact hcomap ▸ Subgroup.mem_comap.mpr hmem
  -- (5.8): hypothesis (b) inside `N_G(T)` (G3 makes `S` Sylow there)
  have hSylN : Work.ZJB.IsSylowIn p (S : Subgroup G) (Subgroup.normalizer (T : Set G)) :=
    isSylowInOfLe p G S _ hSleN
  obtain ⟨d, m, _hdM, hdC, _hmM, hmN, hnm⟩ :=
    (hBsub (Subgroup.normalizer (T : Set G)) hNTne) (S : Subgroup G) hSylN
      (V : Set G) ⟨1, V.one_mem⟩ hVS n hnN hVn
  have hCb1 : g * n⁻¹ ∈ Work.ZJB.Cbar P V := by
    rw [Work.ZJB.Cbar, Subgroup.mem_comap]
    change mk (g * n⁻¹) ∈ Subgroup.centralizer ((V.map mk : Subgroup (G ⧸ P)) : Set (G ⧸ P))
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    have hmkgn : mk (g * n⁻¹) = cbar := by
      rw [show mk (g * n⁻¹) = mk g * (mk n)⁻¹ by simp [map_mul], hgn, hn]
      group
    rw [hmkgn]
    exact Subgroup.mem_centralizer_iff.mp hcbar (mk v) (Subgroup.mem_map_of_mem mk hv)
  have hCb2 : d ∈ Work.ZJB.Cbar P V := by
    rw [Work.ZJB.Cbar, Subgroup.mem_comap]
    change mk d ∈ Subgroup.centralizer ((V.map mk : Subgroup (G ⧸ P)) : Set (G ⧸ P))
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hdC v hv]
  refine ⟨g * m⁻¹, ?_, m, hmN, by group⟩
  have h1 : g * m⁻¹ = g * n⁻¹ * d := by rw [hnm]; group
  rw [h1]
  exact Subgroup.mul_mem _ hCb1 hCb2

end Work.ZJB2
