/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Thm26bVocab
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.c14_lift
import Submission.Work.CORE2A.c14_mul_mem_layer
import Submission.Work.CORE2A.c14_kE_card
import Submission.Work.CORE2A.c14_k_two_n
import Submission.Work.CORE2A.c14_k_four_inf

/-!
# CORE2A, pass 14, leaf **P5** (`c14_k`): `k = |C_E(t) : Z(E)| = q ∓ 1`

Design leaf **P5** of `Submission/Work/_design_gw/Core14.lean` §2 (Bender 1981, p. 220,
"`|C_E(t) : Z(E)| = q ± 1`").  With `E := E(Ĥ) = layerIn B.Hhat`, `Z := Z(E) = zE B`,
`t = B.t ∈ E` and `q := p ^ k`, the claim is

`kE B = kTor (p ^ k)`,

i.e. `|C_E(t) : Z(E)|` is the *even* one of the two numbers `q ± 1` — the value `q − ε`
where `ε = 1` for `q ≡ 1 (mod 4)` and `ε = -1` otherwise.

Assembly (the three ingredients are the sibling files `c14_kE_card`, `c14_k_two_n`,
`c14_k_four_inf`; all of them are unproved-free):

* `c14_kE_card` reduces `kE B` to the order of the centralizer of `y := φ⟨t⟩` inside
  `L₂(q) = Lsub p k ≤ PGL₂(q)`, using the `PGL₂(q)`-quotient `D : PGLData B p k`
  (kernel `Z(E)`, `φ(E) = L₂(q)`) and the lifting lemma `c14_lift` (`P2`);
* `c14_k_two_n` identifies that centralizer with `C_{PSL(2,q)}(t') ≅ DihedralGroup n` and
  gives `2n = q - 1` or `q + 1` (`T.l2cent`, `Work.L2F.l2InvolutionCentralizer`);
* `c14_k_four_inf` shows `4 ∣ |S ⊓ E|`, whence (here) `4 ∣ kE B`: `|S ⊓ E|` divides `kE B`
  because `S ≤ C_G(t)`, `Z(E)` has odd order and `kE B · |Z(E)| = |E ⊓ C_G(t)| ≥ |S ⊓ E|`;
* the arithmetic `c14_kTor_eq` closes: exactly one of `q - 1`, `q + 1` is divisible by `4`,
  namely `q - ε = kTor q`, and `4 ∣ 2n`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

noncomputable section

/-! ## Arithmetic: `4 ∣ 2n` and `2n ∈ {q - 1, q + 1}` force `kTor q = 2n` -/

theorem c14_kTor_eq {q n : ℕ} (hq : Odd q) (h4 : 4 ∣ 2 * n)
    (hn : 2 * n = q - 1 ∨ 2 * n = q + 1) : Work.GW2.kTor q = 2 * n := by
  have hcases : q % 4 = 1 ∨ q % 4 = 3 := by
    have h2 : q % 2 = 1 := Nat.odd_iff.mp hq
    omega
  rcases hcases with h4q | h4q
  · have hk : Work.GW2.kTor q = q - 1 := by rw [Work.GW2.kTor, h4q]; simp
    rw [hk]
    rcases hn with h | h
    · omega
    · exfalso
      have hmod : (q + 1) % 4 = 2 := by omega
      have h0 : (q + 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp (h ▸ h4)
      omega
  · have hk : Work.GW2.kTor q = q + 1 := by rw [Work.GW2.kTor, h4q]; norm_num
    rw [hk]
    rcases hn with h | h
    · exfalso
      have hmod : (q - 1) % 4 = 2 := by omega
      have h0 : (q - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp (h ▸ h4)
      omega
    · omega

/-! ## `φ t` is an involution -/

theorem c14_k_orderOf_phi {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G}
    {p k : ℕ} [Fact p.Prime] (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hbc : Work.GW2.BenderCtx G) (D : Work.GW2.PGLData B p k) (htSE : B.t ∈ Work.GW2.SE B)
    (ht : B.t ∈ Work.GW2.layerIn B.Hhat) :
    orderOf (D.φ ⟨B.t, htSE⟩) = 2 := by
  have hE : Work.GW2.layerIn B.Hhat ≠ ⊥ := by
    intro h
    have h1 : B.t = 1 := by simpa [h] using ht
    have h2 : orderOf B.t = 1 := by rw [h1, orderOf_one]
    rw [B.t_order] at h2
    omega
  have hZodd : Odd (Nat.card (Work.GW2.zE B)) := zE_odd T hFT hbc B hE
  have h2t : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  have hsq : D.φ ⟨B.t, htSE⟩ * D.φ ⟨B.t, htSE⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨B.t, htSE⟩ : ↥(Work.GW2.SE B)) * ⟨B.t, htSE⟩ = 1 := Subtype.ext h2t
    rw [h1, map_one]
  have hne : D.φ ⟨B.t, htSE⟩ ≠ 1 := by
    intro h
    have hmem : (⟨B.t, htSE⟩ : ↥(Work.GW2.SE B)) ∈ D.φ.ker := MonoidHom.mem_ker.mpr h
    rw [D.ker] at hmem
    have hz : B.t ∈ Work.GW2.zE B := Subgroup.mem_subgroupOf.mp hmem
    have hdvd : orderOf B.t ∣ Nat.card ↥(Work.GW2.zE B) :=
      Subgroup.orderOf_dvd_natCard (Work.GW2.zE B) hz
    rw [B.t_order] at hdvd
    exact hZodd.not_two_dvd_nat hdvd
  have h2 : D.φ ⟨B.t, htSE⟩ ^ 2 = 1 := by rw [pow_two]; exact hsq
  exact orderOf_eq_prime h2 hne

/-! ## `|S ⊓ E|` divides `kE B` -/

theorem c14_k_dvd_kE {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G}
    (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hbc : Work.GW2.BenderCtx G) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) :
    Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat) ∣ Work.GW2.kE B := by
  have hE : Work.GW2.layerIn B.Hhat ≠ ⊥ := by
    intro h
    have h1 : B.t = 1 := by simpa [h] using ht
    have h2 : orderOf B.t = 1 := by rw [h1, orderOf_one]
    rw [B.t_order] at h2
    omega
  have hZodd : Odd (Nat.card (Work.GW2.zE B)) := zE_odd T hFT hbc B hE
  -- `Z(E) ≤ E ⊓ C_G(t)`
  have hzEleE : Work.GW2.zE B ≤ Work.GW2.layerIn B.Hhat := zE_le
  have hzEleC : Work.GW2.zE B ≤ Subgroup.centralizer ({B.t} : Set G) := by
    rintro z ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (⟨B.t, ht⟩ : ↥(Work.GW2.layerIn B.Hhat)) * c = c * ⟨B.t, ht⟩ :=
      Subgroup.mem_center_iff.mp hc ⟨B.t, ht⟩
    exact (congrArg Subtype.val hcomm).symm
  have hzEleM : Work.GW2.zE B ≤ Work.GW2.layerIn B.Hhat ⊓
      Subgroup.centralizer ({B.t} : Set G) := le_inf hzEleE hzEleC
  -- `kE B * |Z(E)| = |E ⊓ C_G(t)|`
  have hkEz : Work.GW2.kE B * Nat.card ↥(Work.GW2.zE B) =
      Nat.card ↥(Work.GW2.layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) := by
    have h := Subgroup.relIndex_mul_card (Work.GW2.zE B)
      (Work.GW2.layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G))
    rw [inf_eq_left.mpr hzEleM] at h
    exact h
  -- `S ⊓ E ≤ E ⊓ C_G(t)` (`S ≤ C_G(t)` is `bSetup_S_le_H`)
  have hSM : (B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat ≤
      Work.GW2.layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (bSetup_S_le_H B))
  have hdvd : Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat) ∣
      Work.GW2.kE B * Nat.card ↥(Work.GW2.zE B) := by
    rw [hkEz]
    exact Subgroup.card_dvd_of_le hSM
  -- coprimality: `|S ⊓ E|` is a power of `2`, `|Z(E)|` is odd
  have hcop : Nat.Coprime (Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat))
      (Nat.card ↥(Work.GW2.zE B)) := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (B.S.isPGroup'.to_le (inf_le_left :
      (B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat ≤ (B.S : Subgroup G)))
    rw [ha]
    exact (Nat.coprime_two_right.mpr hZodd).pow_right a |>.symm
  exact hcop.dvd_of_dvd_mul_right hdvd

/-! ## P5 -/

theorem c14_k (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {p k : ℕ} [Fact p.Prime] (D : Work.GW2.PGLData B p k) (hp : Odd p) (hk : 5 ≤ p ^ k) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) (hS8 : 8 ≤ Nat.card (B.S : Subgroup G)) : Work.GW2.kE B = Work.GW2.kTor (p ^ k) := by
  have htSE : B.t ∈ Work.GW2.SE B := Work.CORE2A.layerIn_le_SE ht
  set y : Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k) := D.φ ⟨B.t, htSE⟩ with hy
  have hy2 : orderOf y = 2 := c14_k_orderOf_phi T hFT hbc D htSE ht
  have hyL : y ∈ Work.GW2.Lsub p k := by
    rw [hy]
    exact (D.mem_layer_iff ⟨B.t, htSE⟩).mp ht
  obtain ⟨n, hn, hcard⟩ := c14_k_two_n T p k hp hk y hyL hy2
  have hA := c14_kE_card T hFT hbc D htSE ht
  rw [hy] at hcard
  have hkE : Work.GW2.kE B = 2 * n := by rw [hA, hcard]
  have h4e : 4 ∣ Work.GW2.kE B :=
    dvd_trans (c14_k_four_inf T hFT hbc D hp hk ht hS8) (c14_k_dvd_kE T hFT hbc ht)
  have h4 : 4 ∣ 2 * n := by rw [← hkE]; exact h4e
  have hq : Odd (p ^ k) := hp.pow
  rw [hkE, c14_kTor_eq hq h4 hn]

end

end Work.CORE2A
