import Mathlib
import Submission.Work.ORHughesFree.Rat.Source.Setup
import Submission.Work.ORHughesFree.Rat.Source.SplitWords
import Submission.Work.ORHughesFree.Rat.Source.A_conj_mem
import Submission.Work.ORHughesFree.Rat.Source.F_mul2

namespace Work.ORHughesFree.Rat.Source.SF

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- **Right translation of the left source family `Rat.FL`.**

For `x : U` and `y : Rat(U)` the family of subgroups `V` with some left translate of `y · φx`
lying in `Rat(V)` is the family of `V` such that `V.map (MulAut.conj x) ∈ Rat.FL y`:

  `Rat.FL (y · φx) = { V | V.map (MulAut.conj x) ∈ Rat.FL y }`.

The proof is the pointwise statement that conjugation by `ofGroup x` intertwines `Rat.A V` and
`Rat.A (V.map (MulAut.conj x))` (`Rat.Source.A_conj_mem`). -/
theorem FL_conj_iff (y : RatU U) (x : U) (V : Subgroup U) :
    V ∈ Rat.FL (y * RatU.ofGroup x) ↔ V.map (MulAut.conj x) ∈ Rat.FL y := by
  constructor
  · intro hV
    obtain ⟨u, hu⟩ := Rat.mem_BL_iff_ofGroup_mul.mp hV
    refine Rat.mem_BL_iff_ofGroup_mul.mpr ⟨x * u, ?_⟩
    have h := A_conj_mem (V := V) (a := x)
      (x := RatU.ofGroup u * (y * RatU.ofGroup x)) hu
    have hxx : RatU.ofGroup x * RatU.ofGroup x⁻¹ = (1 : RatU U) := by
      rw [← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one]
    have key : RatU.ofGroup x * (RatU.ofGroup u * (y * RatU.ofGroup x)) * RatU.ofGroup x⁻¹
        = RatU.ofGroup (x * u) * y := by
      rw [RatU.ofGroup_mul]
      rw [show RatU.ofGroup x * (RatU.ofGroup u * (y * RatU.ofGroup x)) * RatU.ofGroup x⁻¹
          = RatU.ofGroup x * RatU.ofGroup u * y * (RatU.ofGroup x * RatU.ofGroup x⁻¹) from by
            noncomm_ring]
      rw [hxx, mul_one]
    rwa [key] at h
  · intro hV
    obtain ⟨w, hw⟩ := Rat.mem_BL_iff_ofGroup_mul.mp hV
    refine Rat.mem_BL_iff_ofGroup_mul.mpr ⟨x⁻¹ * w, ?_⟩
    have h := A_conj_mem (V := V.map (MulAut.conj x)) (a := x⁻¹)
      (x := RatU.ofGroup w * y) hw
    rw [map_conj_conj x V, inv_inv] at h
    have key : RatU.ofGroup x⁻¹ * (RatU.ofGroup w * y) * RatU.ofGroup x
        = RatU.ofGroup (x⁻¹ * w) * (y * RatU.ofGroup x) := by
      rw [RatU.ofGroup_mul]
      noncomm_ring
    rwa [key] at h

/-- The set form of `FL_conj_iff`. -/
theorem FL_conj (y : RatU U) (x : U) :
    Rat.FL (y * RatU.ofGroup x) =
      { V : Subgroup U | V.map (MulAut.conj x) ∈ Rat.FL y } :=
  Set.ext (FL_conj_iff y x)

theorem FL_mul {U : Type} [Group U] {y z : Work.ORHughesFree.RatU U} {Sy Sz : Subgroup U} {uz : U}
    (hy : Work.ORHughesFree.RatU.IsWord y) (hz : Work.ORHughesFree.RatU.IsWord z)
    (hSy : Work.ORHughesFree.Rat.IsLeastL y Sy)
    (hSz : Work.ORHughesFree.Rat.IsLeastL z Sz)
    (huz : Work.ORHughesFree.RatU.ofGroup uz * z ∈ Work.ORHughesFree.Rat.A Sz) :
    ∀ V : Subgroup U, V ∈ Work.ORHughesFree.Rat.FL (y * z) ↔
      Sz ≤ V ∧ Sy.map (MulAut.conj uz) ≤ V := by
  intro V
  constructor
  · -- Forward: a left translate of `y·z` lies in `A V`; split at the word `y`.
    intro hV
    obtain ⟨u, hu⟩ := Rat.mem_BL_iff_ofGroup_mul.mp hV
    have hmem : V ∈ Weak.FA ((RatU.ofGroup u * y) * z) := by
      show (RatU.ofGroup u * y) * z ∈ Rat.A V
      rw [mul_assoc]
      exact hu
    rw [Work.ORHughesFree.Rat.Source.SW.hsplit_words (RatU.IsWord.mul (RatU.IsWord.ofGroup u) hy) hz,
      Set.mem_iUnion] at hmem
    obtain ⟨x, hx1, hx2⟩ := hmem
    have hx1A : (RatU.ofGroup u * y) * RatU.ofGroup x ∈ Rat.A V := hx1
    have hx2A : RatU.ofGroup x⁻¹ * z ∈ Rat.A V := hx2
    -- `V ∈ Rat.FL z`, hence `Sz ≤ V`.
    have hVz : V ∈ Rat.FL z := Rat.mem_BL_iff_ofGroup_mul.mpr ⟨x⁻¹, hx2A⟩
    have hSzV : Sz ≤ V := hSz.le hVz
    -- `V ∈ Rat.FL (y·φx)`, hence `V.map (conj x) ∈ Rat.FL y`, so `Sy ≤ V.map (conj x)`.
    have hVyx : V ∈ Rat.FL (y * RatU.ofGroup x) :=
      Rat.mem_BL_iff_ofGroup_mul.mpr ⟨u, by rw [← mul_assoc]; exact hx1A⟩
    have hVxL : V.map (MulAut.conj x) ∈ Rat.FL y := (FL_conj_iff y x V).mp hVyx
    have hSyVx : Sy ≤ V.map (MulAut.conj x) := hSy.le hVxL
    -- The left translate set of `z` at `V` is the coset `V·uz`; `x⁻¹` lies in it.
    have huzV : RatU.ofGroup uz * z ∈ Rat.A V := Rat.A_mono hSzV huz
    have hz0 : z ≠ 0 := RatU.isWord_ne_zero' hz
    have hcoset := Rat.TL_eq_coset hz0 hVz huzV
    have hxin : x⁻¹ ∈ {u : U | RatU.ofGroup u * z ∈ Rat.A V} := hx2A
    rw [hcoset] at hxin
    obtain ⟨v, hv, hveq⟩ := hxin
    refine ⟨hSzV, ?_⟩
    intro t ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    change uz * s * uz⁻¹ ∈ V
    -- `x = uz⁻¹·v⁻¹`, and `x⁻¹·s·x = v·(uz·s·uz⁻¹)·v⁻¹ ∈ V`, so `uz·s·uz⁻¹ ∈ V`.
    have hsVx : s ∈ V.map (MulAut.conj x) := hSyVx hs
    rw [Subgroup.mem_map] at hsVx
    obtain ⟨w', hw', hws⟩ := hsVx
    have hconjV : x⁻¹ * s * x ∈ V := by
      rw [← hws]
      change x⁻¹ * (x * w' * x⁻¹) * x ∈ V
      have hgrp : x⁻¹ * (x * w' * x⁻¹) * x = w' := by group
      rw [hgrp]; exact hw'
    have hxeq : x⁻¹ = v * uz := hveq
    have hxinv : x = (v * uz)⁻¹ := by rw [← hxeq, inv_inv]
    have key : uz * s * uz⁻¹ = v⁻¹ * (x⁻¹ * s * x) * v := by
      rw [hxeq, hxinv]
      group
    rw [key]
    exact V.mul_mem (V.mul_mem (V.inv_mem hv) hconjV) hv
  · -- Backward: `Sz ≤ V` and `Sy.map (conj uz) ≤ V`.
    rintro ⟨hSzV, hSyV⟩
    have hSy_le : Sy ≤ V.map (MulAut.conj uz⁻¹) := by
      apply (map_conj_le_iff uz⁻¹ Sy V).mp
      simpa only [inv_inv] using hSyV
    obtain ⟨u, hu⟩ := Rat.mem_BL_iff_ofGroup_mul.mp hSy.mem
    have huV : RatU.ofGroup u * y ∈ Rat.A (V.map (MulAut.conj uz⁻¹)) :=
      Rat.A_mono hSy_le hu
    have hVxL : V.map (MulAut.conj uz⁻¹) ∈ Rat.FL y :=
      Rat.mem_BL_iff_ofGroup_mul.mpr ⟨u, huV⟩
    have hVyx : V ∈ Rat.FL (y * RatU.ofGroup uz⁻¹) := (FL_conj_iff y uz⁻¹ V).mpr hVxL
    obtain ⟨w, hw⟩ := Rat.mem_BL_iff_ofGroup_mul.mp hVyx
    -- `hw : φw·(y·φ(uz⁻¹)) ∈ A V`; split and take `x = uz⁻¹`.
    refine Rat.mem_BL_iff_ofGroup_mul.mpr ⟨w, ?_⟩
    have hzA : RatU.ofGroup uz * z ∈ Rat.A V := Rat.A_mono hSzV huz
    have hmem : V ∈ Weak.FA ((RatU.ofGroup w * y) * z) := by
      rw [Work.ORHughesFree.Rat.Source.SW.hsplit_words (RatU.IsWord.mul (RatU.IsWord.ofGroup w) hy) hz,
        Set.mem_iUnion]
      refine ⟨uz⁻¹, ?_, ?_⟩
      · show (RatU.ofGroup w * y) * RatU.ofGroup uz⁻¹ ∈ Rat.A V
        rw [mul_assoc]; exact hw
      · show RatU.ofGroup uz⁻¹⁻¹ * z ∈ Rat.A V
        rw [inv_inv]; exact hzA
    have hmemA : (RatU.ofGroup w * y) * z ∈ Rat.A V := hmem
    rw [mul_assoc] at hmemA
    exact hmemA

end Work.ORHughesFree.Rat.Source.SF
