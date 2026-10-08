import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Thm26bVocab
import Submission.Work.CORE2A.c14_mul_mem_layer
import Submission.Work.CORE2A.Basic

/-!
# CORE2A, pass 14: `4 ∣ |S ⊓ E(Ĥ)|` (the arithmetic input of `kE = kTor q`)

`Work.CORE2A.c14_k_four_inf` is the leaf of the design pass 14 (see
`Submission/Work/CORE2A/_scratch_c14k/dev.lean`, where it is used with `c14_k_dvd_kE` and
`c14_k_two_n` to compute `kE B = kTor (p ^ k)`).

Setting: `G` is a minimal counterexample (`BenderCtx G`), `B : BenderSetup G` its Bender data,
`E := E(Ĥ) = layerIn B.Hhat` the layer of the coatom `Ĥ = B.Hhat`, `S := (B.S : Subgroup G)` a
Sylow 2-subgroup of `G` (dihedral, of order `≥ 8` by `hS8`), and `D : PGLData B p k` the
recognition isomorphism `SE/Z(E) ≅ PGL₂(q)`, `q = p ^ k` odd, `q ≥ 5`, with `φ := D.φ`
surjective, `φ.ker = Z(E)` and `D.mem_layer_iff : (x ∈ E) ↔ (φ x ∈ L₂(q))`.

The claim is `4 ∣ |S ⊓ E|`.  Since `S` is a 2-group, `|S ⊓ E|` is a power of `2`, so it suffices
to know `|S ⊓ E| ≥ 4`; and since `S ≤ SE`, the elements of `S` inside `E` are exactly those
whose `φ`-image lies in `L₂(q) = Lsub p k` (`D.mem_layer_iff`).  Hence the composite

`Φ : S →* PGL₂(q) ⧸ L₂(q)`  (restriction of `φ` to `S`, then the quotient map)

has kernel `S ⊓ E` and image of order `≤ |PGL₂(q) ⧸ L₂(q)| = [PGL₂(q) : L₂(q)] = 2`
(`index_Lsub_eq_two`).  By Lagrange in `↥S` (`Subgroup.index_mul_card`, `Subgroup.index_ker`),

`|S| = |S ⊓ E| · |Φ.range| ≤ 2 · |S ⊓ E|`,

so `4 ≤ |S| / 2 ≤ |S ⊓ E|` by `hS8 : 8 ≤ |S|`.  Together with `|S ⊓ E|` being a power of `2`
this gives `4 ∣ |S ⊓ E|`.

The hypothesis `ht : B.t ∈ E` is not needed by this counting argument (it is part of the ambient
design configuration); the result holds for the given `D`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

theorem c14_k_four_inf (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {p k : ℕ} [Fact p.Prime] (D : Work.GW2.PGLData B p k) (hp : Odd p) (hk : 5 ≤ p ^ k) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) (hS8 : 8 ≤ Nat.card (B.S : Subgroup G)) :
    4 ∣ Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat) := by
  -- `5 ≤ p ^ k` excludes `k = 0`, so `L₂(q)` has index `2` in `PGL₂(q)`.
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have hLidx : (Work.GW2.Lsub p k).index = 2 := Work.CORE2A.index_Lsub_eq_two hp hk0
  haveI hLnorm : (Work.GW2.Lsub p k).Normal := Subgroup.normal_of_index_eq_two hLidx
  have hSleSE : (B.S : Subgroup G) ≤ Work.GW2.SE B := Work.CORE2A.S_le_SE
  -- The composite `Φ : S →* PGL₂(q) ⧸ L₂(q)`.
  let Φ : ↥(B.S : Subgroup G) →*
      (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k) ⧸ Work.GW2.Lsub p k) :=
    (QuotientGroup.mk' (Work.GW2.Lsub p k)).comp
      (D.φ.comp (Subgroup.inclusion hSleSE))
  -- Membership in the kernel of `Φ` is membership in `E` (`D.mem_layer_iff`).
  have hkey : ∀ x : ↥(B.S : Subgroup G), Φ x = 1 ↔ (x : G) ∈ Work.GW2.layerIn B.Hhat := by
    intro x
    have h1 : Φ x = 1 ↔ (D.φ.comp (Subgroup.inclusion hSleSE)) x ∈ Work.GW2.Lsub p k := by
      change (QuotientGroup.mk' (Work.GW2.Lsub p k))
          ((D.φ.comp (Subgroup.inclusion hSleSE)) x) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [h1]
    exact (D.mem_layer_iff (Subgroup.inclusion hSleSE x)).symm
  -- Hence `Φ.ker = (S ⊓ E).subgroupOf S`.
  have hker : Φ.ker = ((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat).subgroupOf (B.S : Subgroup G) := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf]
    simp only [x.2, true_and]
    exact hkey x
  have hcardker : Nat.card ↥Φ.ker =
      Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : _ ≤ (B.S : Subgroup G))).toEquiv
  -- `|PGL₂(q) ⧸ L₂(q)| = 2`.
  have hQcard : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k) ⧸ Work.GW2.Lsub p k) = 2 := by
    rw [← Subgroup.index_eq_card (Work.GW2.Lsub p k)]
    exact hLidx
  have hrange : Nat.card ↥Φ.range ≤ 2 := by
    have hdvd : Nat.card ↥Φ.range ∣
        Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k) ⧸ Work.GW2.Lsub p k) :=
      Subgroup.card_subgroup_dvd_card Φ.range
    rw [hQcard] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  -- Lagrange in `↥S`: `|S| = |Φ.ker| * |Φ.range|`.
  have hcardS : Nat.card ↥(B.S : Subgroup G) = Nat.card ↥Φ.ker * Nat.card ↥Φ.range := by
    have h2 : Φ.ker.index * Nat.card ↥Φ.ker = Nat.card ↥(B.S : Subgroup G) :=
      Subgroup.index_mul_card Φ.ker
    rw [Subgroup.index_ker Φ] at h2
    rw [mul_comm] at h2
    exact h2.symm
  -- So `|S| ≤ 2 * |S ⊓ E|`, and `|S| ≥ 8` forces `|S ⊓ E| ≥ 4`.
  have hKge : 4 ≤ Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat) := by
    have hcomb : Nat.card ↥(B.S : Subgroup G) ≤
        Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat) * 2 := by
      rw [hcardS, hcardker]
      exact Nat.mul_le_mul_left _ hrange
    omega
  -- `|S ⊓ E|` is a power of `2`, hence `2^2 ∣ 2^m` once `m ≥ 2`.
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp
    (IsPGroup.to_le (B.S.isPGroup')
      (inf_le_left : (B.S : Subgroup G) ⊓ Work.GW2.layerIn B.Hhat ≤ (B.S : Subgroup G)))
  have hm2 : 2 ≤ m := by
    have h : (2:ℕ)^2 ≤ 2^m := by
      rw [hm] at hKge
      calc (2:ℕ)^2 = 4 := by norm_num
        _ ≤ 2^m := hKge
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  rw [hm]
  exact dvd_trans (by norm_num : (4:ℕ) ∣ 2^2) (pow_dvd_pow 2 hm2)

end Work.CORE2A
