import Mathlib
import Submission.Work.CORE3.Defs

/-!
# CORE3: the centralizer of an involution normalizing a four-group

`Work.CORE3.CardCentralizerInfFourGroup`: if `V` is a Klein four-group (`|V| = 4`, every
element of `V` an involution) and `s` is an involution normalizing `V` which does **not**
centralize `V`, then exactly two elements of `V` are centralized by `s`.

Proof sketch.  Conjugation by `s` is an automorphism `φ` of the abelian group `V` with
`φ² = 1`.  Since `φ ≠ 1`, choose `v ∈ V` with `s v s⁻¹ ≠ v`.  Then `w = v · (s v s⁻¹)` is a
nontrivial element of `V` fixed by `φ` (because `φ(v·φ v) = φ v · v = v · φ v` and `V` is
abelian), so the fixed subgroup `K = V ⊓ C_X(s)` has at least two elements.  On the other
hand `K ≤ V` with `|V| = 4`, so `|K| ∣ 4` (Lagrange, via `Subgroup.card_mul_index`), while
`|K| ≠ 4` because `K = V` would force `V ≤ C_X(s)`.  Hence `|K| = 2`.

The file is self-contained: it uses only `Mathlib` and the shared CORE3 definitions
(`Work.GW2.IsFourGroup`).
-/

namespace Work.CORE3

open Subgroup

theorem CardCentralizerInfFourGroup {X : Type} [Group X] (V : Subgroup X) (s : X)
    (hV4 : Work.GW2.IsFourGroup V)
    (hsN : s ∈ Subgroup.normalizer (V : Set X)) (hs2 : orderOf s = 2)
    (hnot : ¬ V ≤ Subgroup.centralizer ({s} : Set X)) :
    Nat.card (V ⊓ Subgroup.centralizer ({s} : Set X) : Subgroup X) = 2 := by
  -- `s` is an involution.
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  -- `V` is finite (it has 4 elements, and `Nat.card` vanishes on infinite types).
  have hVfin : Finite V := by
    rw [← not_infinite_iff_finite]
    intro hinf
    have h0 : Nat.card (↥V) = 0 := @Nat.card_eq_zero_of_infinite V hinf
    have h4 : Nat.card (↥V) = 4 := hV4.1
    exact absurd (h4.symm.trans h0) (by norm_num)
  -- `C` is the centralizer of `s` and `K = V ⊓ C` the subgroup we count.
  let C : Subgroup X := Subgroup.centralizer ({s} : Set X)
  let K : Subgroup X := V ⊓ C
  change Nat.card K = 2
  have hKle : K ≤ V := inf_le_left
  -- conjugation by `s` preserves `V`.
  have hconj : ∀ v ∈ V, s * v * s⁻¹ ∈ V :=
    fun v hv => (Subgroup.mem_normalizer_iff.mp hsN v).mp hv
  -- a witness `v ∈ V` moved by `s`.
  have hex : ∃ v, v ∈ V ∧ v ∉ C := by
    by_contra h
    refine hnot fun x hx => ?_
    by_contra hxC
    exact h ⟨x, hx, hxC⟩
  obtain ⟨v, hvV, hvC⟩ := hex
  have hvs : v * s ≠ s * v := by
    intro heq
    exact hvC (Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact heq.symm))
  have hconjv : s * v * s⁻¹ ≠ v := by
    intro heq
    have hsv : s * v = v * s := by
      calc s * v = (s * v * s⁻¹) * s := by group
        _ = v * s := by rw [heq]
    exact hvs hsv.symm
  have huV : s * v * s⁻¹ ∈ V := hconj v hvV
  have hwV : v * (s * v * s⁻¹) ∈ V := mul_mem hvV huV
  -- `w = v * (s v s⁻¹)` is nontrivial ...
  have hw1 : v * (s * v * s⁻¹) ≠ 1 := by
    intro h
    apply hconjv
    have h2 : s * v * s⁻¹ = v⁻¹ := eq_inv_of_mul_eq_one_right h
    have hv2 : v ^ 2 = 1 := hV4.2 v hvV
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hv2)
    rw [h2, hvinv]
  -- ... and `V` is abelian, so `u v = v u` for `u = s v s⁻¹`.
  have huv : (s * v * s⁻¹) * v = v * (s * v * s⁻¹) := by
    have hsq : ((s * v * s⁻¹) * v) ^ 2 = 1 := hV4.2 _ (mul_mem huV hvV)
    have hmul : ((s * v * s⁻¹) * v) * ((s * v * s⁻¹) * v) = 1 := by
      simpa [pow_two] using hsq
    have hinv : ((s * v * s⁻¹) * v)⁻¹ = (s * v * s⁻¹) * v :=
      inv_eq_of_mul_eq_one_left hmul
    have hu_inv : (s * v * s⁻¹)⁻¹ = s * v * s⁻¹ :=
      inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hV4.2 _ huV)
    have hv_inv : v⁻¹ = v :=
      inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hV4.2 v hvV)
    rw [← hinv, mul_inv_rev, hu_inv, hv_inv]
  have hss2 : s⁻¹ * s⁻¹ = 1 := by rw [hsinv, hss]
  -- `φ(v) = v`, i.e. `s (s v s⁻¹) s⁻¹ = v` (`φ² = 1`).
  have he2 : s * (s * v * s⁻¹) * s⁻¹ = v := by
    have h : s * (s * v * s⁻¹) * s⁻¹ = (s * s) * (v * (s⁻¹ * s⁻¹)) := by group
    rw [h, hss, hss2, mul_one, one_mul]
  -- hence `w` is fixed by conjugation by `s`.
  have hfix : s * (v * (s * v * s⁻¹)) * s⁻¹ = v * (s * v * s⁻¹) := by
    calc s * (v * (s * v * s⁻¹)) * s⁻¹
        = (s * v * s⁻¹) * (s * (s * v * s⁻¹) * s⁻¹) := by group
      _ = (s * v * s⁻¹) * v := by rw [he2]
      _ = v * (s * v * s⁻¹) := huv
  have hwC : v * (s * v * s⁻¹) ∈ C := by
    show v * (s * v * s⁻¹) ∈ Subgroup.centralizer ({s} : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc s * (v * (s * v * s⁻¹)) = (s * (v * (s * v * s⁻¹)) * s⁻¹) * s := by group
      _ = (v * (s * v * s⁻¹)) * s := by rw [hfix]
  have hwK : v * (s * v * s⁻¹) ∈ K := Subgroup.mem_inf.mpr ⟨hwV, hwC⟩
  -- `|K|` divides `|V| = 4` (Lagrange).
  have hdvd : Nat.card K ∣ 4 := by
    have hcard := Subgroup.card_mul_index (K.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv, hV4.1] at hcard
    exact ⟨(K.subgroupOf V).index, hcard.symm⟩
  have hne0 : Nat.card K ≠ 0 := by
    intro h
    have hd := hdvd
    rw [h] at hd
    norm_num at hd
  have hge : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr hne0
  have hne1 : Nat.card K ≠ 1 := by
    intro h
    rw [Subgroup.card_eq_one] at h
    rw [h] at hwK
    exact hw1 (by simpa using hwK)
  have hne4 : Nat.card K ≠ 4 := by
    intro h
    have hKV : K = V :=
      @Subgroup.eq_of_le_of_card_ge X _ K V hVfin hKle (by rw [hV4.1, h])
    exact hnot (by rw [← hKV]; exact inf_le_right)
  have hne3 : Nat.card K ≠ 3 := by
    intro h
    rw [h] at hdvd
    norm_num at hdvd
  have hle : Nat.card K ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  -- `1 ≤ |K| ≤ 4`, `|K| ∣ 4`, `|K| ≠ 1, 4`: so `|K| = 2`.
  have hcases : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 4 := by
    omega
  rcases hcases with h | h | h | h
  · exact absurd h hne1
  · exact h
  · exact absurd h hne3
  · exact absurd h hne4

end Work.CORE3
