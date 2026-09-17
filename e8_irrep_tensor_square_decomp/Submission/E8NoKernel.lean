import Submission.WCFSetup
import Submission.E8Character
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_rho_sub_wact_rho_eq_sum
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_small_height_length

/-!
# The no-kernel lemma for the Weyl sum `A_ρ`

`WSum f x = ∑_{w ∈ W} ε(w) f (x - wρ)` is "multiplication by the Weyl denominator `A_ρ`" in the
group algebra of the weight lattice.  This file proves the fundamental injectivity statement

  **`A_ρ f = 0` forces `f = 0`** whenever `f` is supported on a set of *bounded height*,

and its corollary that the map `A_ρ` is injective on such functions (`eq_of_WSum_eq`).

The proof is the standard one: take `ν` in the support of `f` of *maximal height*; then in
`WSum f (ν + ρ)` the term `w = 1` contributes `f ν`, while for `w ≠ 1` the argument
`ν + ρ - wρ = ν + (ρ - wρ)` has strictly larger height (`ρ - wρ` is a nonempty sum of positive
roots), so that term vanishes by maximality; hence `f ν = 0`, a contradiction.

These lemmas are the uniqueness half of the Weyl character formula: they turn an identity between
Weyl sums of functions into an identity of the functions themselves, and are what makes the
`A_ρ`-argument (`A_ρ m = A_{μ+ρ}` plus support ⟹ `m` is the character) work.
-/

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

noncomputable section
open scoped BigOperators

namespace Submission.E8NoKernel

open Submission.WCFSetup
open Commons.LinearAlgebra.Matrix.Cartan
open Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo

local notation "ht" => Submission.E8Character.htOf

/-- The height agrees with the commons `e8ht`. -/
lemma ht_eq_e8ht (v : Fin 8 → ℤ) : ht v = e8ht v := rfl

/-- The height is additive over finite sums. -/
lemma ht_sum {ι : Type*} (s : Finset ι) (g : ι → Fin 8 → ℤ) :
    ht (∑ i ∈ s, g i) = ∑ i ∈ s, ht (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submission.E8Character.htOf_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Submission.E8Character.htOf_add, ih]

/-- **`ρ - wρ` has strictly positive height for `w ≠ 1`.** -/
theorem ht_rho_sub_ap_pos {M : Matrix (Fin 8) (Fin 8) ℤ} (hM : M ∈ WG) (hne : M ≠ 1) :
    0 < ht (rhoV - ap M rhoV) := by
  obtain ⟨L, rfl⟩ := mem_WG.mp hM
  have hap : ap (wactMat L) rhoV = wact L rhoV := by
    rw [rhoV_eq, wactMat_ap]
  rw [hap, rhoV_eq]
  have h := E8_rho_sub_wact_rho_eq_sum L
  rw [h, ht_sum]
  have hne' : (E8posRoots.P.filter
      (fun y => -(wact L.reverse y) ∈ E8posRoots.P)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    have hz : (rhoZ - wact L rhoZ) = 0 := by rw [h, hempty]; simp
    have hfix : wact L rhoZ = rhoZ := (sub_eq_zero.mp hz).symm
    have h2 := wactMat_eq_of_rho_eq (L := L) (L' := []) (by simpa using hfix)
    rw [wactMat_nil] at h2
    exact h2
  obtain ⟨y, hy⟩ := hne'
  have hyP : y ∈ E8posRoots.P := (Finset.mem_filter.mp hy).1
  have h1 : 1 ≤ ht y := by
    rw [ht_eq_e8ht]; exact one_le_e8ht_of_mem_P hyP
  have hnn : ∀ z ∈ E8posRoots.P.filter
      (fun y => -(wact L.reverse y) ∈ E8posRoots.P), (0 : ℤ) ≤ ht z := by
    intro z hz
    have hzP : z ∈ E8posRoots.P := (Finset.mem_filter.mp hz).1
    have := one_le_e8ht_of_mem_P hzP
    rw [ht_eq_e8ht]; linarith
  have := Finset.single_le_sum (f := fun z => ht z) hnn hy
  linarith

/-- **The no-kernel lemma for the Weyl sum.**  A function whose support has *bounded height*
(which is the case for a support contained in a cone-translate `{ν : ν ⪯ x}`, since
`ht ν ≤ ht x` there) and whose Weyl sum vanishes identically is zero. -/
theorem WSum_eq_zero_of_bounded (f : (Fin 8 → ℤ) → ℚ) (N : ℤ)
    (hsupp : ∀ ν, f ν ≠ 0 → ht ν ≤ N)
    (h0 : ∀ x, WSum f x = 0) : f = 0 := by
  classical
  by_contra hf
  -- a point of the support, and then a point of maximal height
  obtain ⟨ν₀, hν₀⟩ : ∃ ν, f ν ≠ 0 := by
    by_contra hc
    exact hf (funext fun ν => by by_contra hν; exact hc ⟨ν, hν⟩)
  have hN0 : ht ν₀ ≤ N := hsupp ν₀ hν₀
  obtain ⟨ν, hνnz, hνmax⟩ : ∃ ν, f ν ≠ 0 ∧ ∀ μ, f μ ≠ 0 → ht μ ≤ ht ν := by
    set S : Finset ℤ := (Finset.Icc (ht ν₀) N).filter
      (fun n => ∃ μ, f μ ≠ 0 ∧ ht μ = n) with hSdef
    have hne : S.Nonempty := ⟨ht ν₀, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_refl _, hN0⟩, ⟨ν₀, hν₀, rfl⟩⟩⟩
    have hmS : S.max' hne ∈ S := Finset.max'_mem S hne
    obtain ⟨ν, hνnz, hνm⟩ := (Finset.mem_filter.mp hmS).2
    refine ⟨ν, hνnz, fun μ hμ => ?_⟩
    by_cases hcase : ht ν₀ ≤ ht μ
    · have hmem : ht μ ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hcase, hsupp μ hμ⟩, ⟨μ, hμ, rfl⟩⟩
      have h3 := Finset.le_max' S (ht μ) hmem
      rw [hνm]; exact h3
    · have hle' : ht ν₀ ≤ S.max' hne := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmS).1).1
      have hle : ht ν₀ ≤ ht ν := by rw [hνm]; exact hle'
      have h3 : ht ν ≤ N := hsupp ν hνnz
      omega
  have h1 : WSum f (ν + rhoV) = f ν := by
    rw [WSum, Finset.sum_eq_single (1 : Matrix (Fin 8) (Fin 8) ℤ)]
    · simp
    · intro M hM hMne
      have hz : f (ν + rhoV - ap M rhoV) = 0 := by
        by_contra hcon
        have hle := hνmax _ hcon
        have hsplit : ν + rhoV - ap M rhoV = ν + (rhoV - ap M rhoV) := by abel
        have hpos := ht_rho_sub_ap_pos hM hMne
        rw [hsplit, Submission.E8Character.htOf_add] at hle
        linarith
      rw [hz, mul_zero]
    · intro hnot
      exact absurd WG_one hnot
  exact hνnz (by rw [← h1]; exact h0 _)

/-- **Injectivity of the Weyl sum on functions of bounded height.** -/
theorem eq_of_WSum_eq {f g : (Fin 8 → ℤ) → ℚ} (Nf Ng : ℤ)
    (hf : ∀ ν, f ν ≠ 0 → ht ν ≤ Nf)
    (hg : ∀ ν, g ν ≠ 0 → ht ν ≤ Ng)
    (h : ∀ x, WSum f x = WSum g x) : f = g := by
  have hfg : f - g = 0 := by
    refine WSum_eq_zero_of_bounded (f - g) (max Nf Ng) ?_ ?_
    · intro ν hν
      have hfgν : f ν ≠ 0 ∨ g ν ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hν (by show f ν - g ν = 0; rw [hc.1, hc.2, sub_self])
      rcases hfgν with hfν | hgν
      · exact le_trans (hf ν hfν) (le_max_left _ _)
      · exact le_trans (hg ν hgν) (le_max_right _ _)
    · intro x
      have : WSum (f - g) x = WSum f x - WSum g x := by
        simp only [WSum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [this, h x, sub_self]
  exact sub_eq_zero.mp hfg

end Submission.E8NoKernel
