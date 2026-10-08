import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB2.sylowInConj
import Submission.Work.ZJB2.isSylowInOfLe
import Submission.Work.ZJB.ThompsonWeakClosed

/-!
# GW design 17, item B (ZJB2) — leaf `step3` (T51.III) — PROVED

Source: Glauberman 1968, p. 1119, step (III).

**Route.** `g⁻¹Wg ≤ S` ⇒ `Z(S)^g ≤ C(W)` (`Z(S)` centralizes `g⁻¹Wg`).  G1 in `C(W)` with
`T = C(W) ⊓ S`: `a ∈ C(W)` with `(g⁻¹a)⁻¹ Z(S) (g⁻¹a) ≤ S`.  Apply `GoodFor S Z(S)` to `g⁻¹a`:
`g⁻¹a = c n`.  `M = N(Z(S))`, `S` Sylow in `M` (G3); `CpStarIn p M` at `T = S`, subgroup
`g⁻¹Wg`, element `c ∈ C(Z(S)) ≤ M`: `c = d m`, `d ∈ C(g⁻¹Wg)`, `m ∈ M ∩ N(Z(J))`.  Then
`g m n ∈ C(W)`, `m n ∈ N(Z(J))`, `g = (g m n)(m n)⁻¹`.
-/

namespace Work.ZJB2

open Work.GW2 Work.ZJB Subgroup

theorem step3 (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.Step3Prop p G := by
  intro S hgood hstar W hWS hWsy g hg
  -- `Z(S)` is normalized by `S`, `Z(J(S))` is normalized by `S`.
  have hSleZS : (S : Subgroup G) ≤ normalizer (Work.ZJB.ZS (S : Subgroup G) : Set G) := by
    intro s hs
    rw [Work.ZJB.ZS]
    exact mem_normalizer_inf (mem_normalizer_centralizer (le_normalizer hs)) (le_normalizer hs)
  have hSleZJ : (S : Subgroup G) ≤ normalizer (ZJ (S : Subgroup G) : Set G) := by
    rw [ZJ_eq_thompsonJAbelian]
    exact le_normalizer_zCenter_thompsonJAbelian (S : Subgroup G)
  -- `Z(S)^g ≤ C(W)`.
  set V := (Work.ZJB.ZS (S : Subgroup G)).map (MulAut.conj g).toMonoidHom with hVdef
  have hVleC : V ≤ centralizer (W : Set G) := by
    intro v hv
    rw [hVdef] at hv
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Work.ZJB.ZS] at hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hcomm := (Subgroup.mem_centralizer_iff.mp hz.1) (g⁻¹ * w * g) (hg w hw)
    have h1 : w * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
    rw [h1, hcomm]
    group
  have hVp : IsPGroup p ↥V := by
    rw [hVdef]
    exact (S.isPGroup'.to_le
      (show Work.ZJB.ZS (S : Subgroup G) ≤ (S : Subgroup G) from inf_le_right)).map
      (MulAut.conj g).toMonoidHom
  -- G1 in `C(W)`, with `T = C(W) ⊓ S`: conjugate `Z(S)^g` into `T`.
  obtain ⟨a, haC, haV⟩ :=
    Work.ZJB2.sylowInConj p G ((centralizer (W : Set G)) ⊓ (S : Subgroup G))
      (centralizer (W : Set G)) V hWsy hVleC hVp
  -- (II) applied to `g⁻¹ a`.
  have hconj : ∀ z ∈ Work.ZJB.ZS (S : Subgroup G),
      (g⁻¹ * a)⁻¹ * z * (g⁻¹ * a) ∈ (S : Subgroup G) := by
    intro z hz
    have hzV : g * z * g⁻¹ ∈ V := by
      rw [hVdef]
      exact Subgroup.mem_map.mpr ⟨z, hz, by simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have h := haV _ hzV
    rw [Subgroup.mem_inf] at h
    have heq : a⁻¹ * (g * z * g⁻¹) * a = (g⁻¹ * a)⁻¹ * z * (g⁻¹ * a) := by group
    rw [← heq]
    exact h.2
  obtain ⟨c, n, hcC, hnN, hx⟩ := hgood (g⁻¹ * a) hconj
  have hcM : c ∈ normalizer (Work.ZJB.ZS (S : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcC
  have hc' : c = g⁻¹ * a * n⁻¹ := by rw [hx]; group
  -- (C_p*) in `M = N(Z(S))` applied to `W^g` and the element `c`.
  set W' := Work.ZJB.pconj W g with hW'def
  have hW'S : W' ≤ (S : Subgroup G) := by
    intro x hx'
    rw [hW'def, Work.ZJB.mem_pconj] at hx'
    have hmem := hg (g * x * g⁻¹) hx'
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hmem
  have hST : IsSylowIn p (S : Subgroup G)
      (normalizer (Work.ZJB.ZS (S : Subgroup G) : Set G)) :=
    Work.ZJB2.isSylowInOfLe p G S _ hSleZS
  have hW'M : W' ≤ normalizer (Work.ZJB.ZS (S : Subgroup G) : Set G) := hW'S.trans hSleZS
  have hW'N : W' ≤ normalizer (ZJ (S : Subgroup G) : Set G) := hW'S.trans hSleZJ
  have hW'p : IsPGroup p ↥W' := S.isPGroup'.to_le hW'S
  have hc_conj : ∀ w ∈ W', c⁻¹ * w * c ∈ normalizer (ZJ (S : Subgroup G) : Set G) := by
    intro w hw
    have hxW : g * w * g⁻¹ ∈ W := by
      rw [hW'def, Work.ZJB.mem_pconj] at hw
      exact hw
    have hxN : g * w * g⁻¹ ∈ normalizer (ZJ (S : Subgroup G) : Set G) := hSleZJ (hWS hxW)
    have haw : a⁻¹ * (g * w * g⁻¹) * a = g * w * g⁻¹ := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp haC) (g * w * g⁻¹) hxW
      have h1 : a⁻¹ * (g * w * g⁻¹) * a = a⁻¹ * ((g * w * g⁻¹) * a) := by group
      rw [h1, hcomm]
      group
    have hcw : c⁻¹ * w * c = n * (g * w * g⁻¹) * n⁻¹ := by
      rw [hc']
      have h1 : (g⁻¹ * a * n⁻¹)⁻¹ * w * (g⁻¹ * a * n⁻¹)
          = n * (a⁻¹ * (g * w * g⁻¹) * a) * n⁻¹ := by group
      rw [h1, haw]
    rw [hcw]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN hxN) (Subgroup.inv_mem _ hnN)
  obtain ⟨d, m', _hdM, hdC', _hm'M, hm'N, hcdm⟩ :=
    hstar (S : Subgroup G) hST W' hW'M hW'N hW'p c hcM hc_conj
  -- Assemble: `g = (g m n) (m n)⁻¹` with `g m n ∈ C(W)` and `m n ∈ N(Z(J))`.
  refine ⟨g * m' * n, (m' * n)⁻¹, ?_, ?_, by group⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have haw : a⁻¹ * w * a = w := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp haC) w hw
      have h1 : a⁻¹ * w * a = a⁻¹ * (w * a) := by group
      rw [h1, hcomm]
      group
    have hcu : c⁻¹ * (g⁻¹ * w * g) * c = n * w * n⁻¹ := by
      rw [hc']
      have h1 : (g⁻¹ * a * n⁻¹)⁻¹ * (g⁻¹ * w * g) * (g⁻¹ * a * n⁻¹)
          = n * (a⁻¹ * w * a) * n⁻¹ := by group
      rw [h1, haw]
    have hd_comm : d * (g⁻¹ * w * g) * d⁻¹ = g⁻¹ * w * g := by
      have huW' : g⁻¹ * w * g ∈ W' := by
        rw [hW'def, Work.ZJB.mem_pconj]
        rw [show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
        exact hw
      have hcomm := (Subgroup.mem_centralizer_iff.mp hdC') (g⁻¹ * w * g) huW'
      have h1 : d * (g⁻¹ * w * g) * d⁻¹ = ((g⁻¹ * w * g) * d) * d⁻¹ := by rw [← hcomm]
      rw [h1]
      group
    have hm' : m' = d⁻¹ * c := by rw [hcdm]; group
    have hkey : (g * m' * n)⁻¹ * w * (g * m' * n) = w := by
      have h1 : (g * m' * n)⁻¹ * w * (g * m' * n)
          = n⁻¹ * (m'⁻¹ * (g⁻¹ * w * g) * m') * n := by group
      rw [h1, hm']
      have h2 : (d⁻¹ * c)⁻¹ * (g⁻¹ * w * g) * (d⁻¹ * c)
          = c⁻¹ * (d * (g⁻¹ * w * g) * d⁻¹) * c := by group
      rw [h2, hd_comm, hcu]
      group
    have h3 : w * (g * m' * n)
        = (g * m' * n) * ((g * m' * n)⁻¹ * w * (g * m' * n)) := by group
    rw [h3, hkey]
  · exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hm'N hnN)

end Work.ZJB2
