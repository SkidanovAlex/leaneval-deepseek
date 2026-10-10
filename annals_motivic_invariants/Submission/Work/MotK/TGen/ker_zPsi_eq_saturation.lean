import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.MotK.TGen.zpA_notMem_span

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# The kernel of `zPsi` is the `zA`-saturation of `(zg, zB)`

`zPsi : K[x₀,x₁,x₂] → ZF = Frac (K[y₀,y₁]/(ZElim2))` is the graph map
`x₀ ↦ C₁/A₁`, `x₁ ↦ y₀`, `x₂ ↦ y₁`.  In the plane model the graph sits inside the affine plane
curve cut out by `zB = zA·x₀ − zC`, and `zA, zC, zg` involve only `x₁, x₂`.  The classical
"clear denominators" statement is

  `k = { f : ∃ N, zA^N · f ∈ (zg, zB) }`,

i.e. `ker zPsi` is exactly the saturation of `(zg, zB)` at `zA`; this is step 1 of the route
recorded in `GUIDE_ker_zPsi.md`.

The two inclusions:
* `⊇`: `zg` and `zB` are killed by `zPsi` (for `zB` this uses `zA ↦ za1 ≠ 0`, which follows from
  `Work.MotK.TGen.zpA_notMem_span`, i.e. `deg zpA = 2 < 5 = deg ZElim2`), hence `zA^N f ∈ ker zPsi`
  gives `za1^N · zPsi f = 0` and `zPsi f = 0`.
* `⊆`: iterate the "clear denominators" reduction `zA^N f ≡ rename h (mod zB)`; applying `zPsi`
  shows `h ∈ (ZElim2)`, whence `rename h ∈ (zg)`.
-/

namespace Work.MotK.TGen

open MvPolynomial

/-- The class of `zpA` is nonzero in the quotient, i.e. `za1 ≠ 0`.  (`zpA ∉ (ZElim2)` is
`Work.MotK.TGen.zpA_notMem_span`.) -/
private lemma aux_za1_ne_zero (K : Type) [Field K] (a b h : K) [IsDomain (ZD K a b h)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) : za1 K a b h ≠ 0 := by
  intro h0
  have h0' : algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (zpA K a b h)) = 0 := h0
  have h1 : Ideal.Quotient.mk
      (Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K)))
      (zpA K a b h) = 0 :=
    IsFractionRing.injective (ZD K a b h) (ZF K a b h) (by rw [h0', map_zero])
  exact zpA_notMem_span K a b h ha hb hh (Ideal.Quotient.eq_zero_iff_mem.mp h1)

/-- `zPsi` kills the affine relation `zB = zA·x₀ − zC`. -/
private lemma aux_zPsi_zB (K : Type) [Field K] (a b h : K) [IsDomain (ZD K a b h)]
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) : zPsi K a b h (zB K a b h) = 0 := by
  rw [zB_eq, map_sub, map_mul, zPsi_rename, zPsi_rename, zPsi_X0]
  rw [show zc1 K a b h = algebraMap (ZD K a b h) (ZF K a b h)
        (Ideal.Quotient.mk _ (zpC K a b h)) from rfl,
      show za1 K a b h = algebraMap (ZD K a b h) (ZF K a b h)
        (Ideal.Quotient.mk _ (zpA K a b h)) from rfl]
  rw [← mul_assoc,
    mul_comm (algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (zpA K a b h)))
      (algebraMap (ZD K a b h) (ZF K a b h) (Ideal.Quotient.mk _ (zpC K a b h))),
    mul_assoc,
    mul_inv_cancel₀ (show algebraMap (ZD K a b h) (ZF K a b h)
        (Ideal.Quotient.mk _ (zpA K a b h)) ≠ 0 from aux_za1_ne_zero K a b h ha hb hh),
    mul_one, sub_self]

/-- **Clear denominators.**  For every `f` there are `N` and `h` with
`zA^N·f − rename h ∈ (zB)`: substitute `x₀ ↦ zC/zA` modulo `zB`. -/
private lemma aux_reduce (K : Type) [Field K] (a b h : K) :
    ∀ f : MvPolynomial (Fin 3) K,
      ∃ N : ℕ, ∃ g : MvPolynomial (Fin 2) K,
        zA K a b h ^ N * f - MvPolynomial.rename zEmb g
          ∈ Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K)) := by
  have hrenA : MvPolynomial.rename zEmb (zpA K a b h) = zA K a b h := (zA_eq_rename a b h).symm
  have hrenC : MvPolynomial.rename zEmb (zpC K a b h) = zC K a b h := (zC_eq_rename a b h).symm
  intro f
  induction f using MvPolynomial.induction_on with
  | C r => exact ⟨0, MvPolynomial.C r, by simp⟩
  | add p q hp hq =>
    obtain ⟨N1, g1, h1⟩ := hp
    obtain ⟨N2, g2, h2⟩ := hq
    refine ⟨N1 + N2, zpA K a b h ^ N2 * g1 + zpA K a b h ^ N1 * g2, ?_⟩
    rw [show zA K a b h ^ (N1 + N2) * (p + q)
          - MvPolynomial.rename zEmb (zpA K a b h ^ N2 * g1 + zpA K a b h ^ N1 * g2)
        = zA K a b h ^ N2 * (zA K a b h ^ N1 * p - MvPolynomial.rename zEmb g1)
          + zA K a b h ^ N1 * (zA K a b h ^ N2 * q - MvPolynomial.rename zEmb g2) from by
      simp only [map_add, map_mul, map_pow, hrenA]
      ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  | mul_X p n hp =>
    obtain ⟨N, g, hN⟩ := hp
    fin_cases n <;> simp only []
    · refine ⟨N + 1, g * zpC K a b h, ?_⟩
      show zA K a b h ^ (N + 1) * (p * X (0 : Fin 3)) - MvPolynomial.rename zEmb (g * zpC K a b h)
        ∈ Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K))
      have hBX : zA K a b h * X 0 = zB K a b h + zC K a b h := by rw [zB]; ring
      rw [show zA K a b h ^ (N + 1) * (p * X 0) - MvPolynomial.rename zEmb (g * zpC K a b h)
          = zA K a b h ^ N * p * zB K a b h
            + (zA K a b h ^ N * p - MvPolynomial.rename zEmb g) * zC K a b h from by
        simp only [map_mul, hrenC]
        rw [pow_succ, show zA K a b h ^ N * zA K a b h * (p * X 0)
            = zA K a b h ^ N * p * (zA K a b h * X 0) from by ring, hBX]
        ring]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right (zC K a b h) _ hN)
    · refine ⟨N, g * X 0, ?_⟩
      show zA K a b h ^ N * (p * X (1 : Fin 3)) - MvPolynomial.rename zEmb (g * X 0)
        ∈ Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K))
      rw [show zA K a b h ^ N * (p * X 1) - MvPolynomial.rename zEmb (g * X 0)
          = (zA K a b h ^ N * p - MvPolynomial.rename zEmb g) * X 1 from by
        simp only [map_mul, MvPolynomial.rename_X]
        norm_num
        ring]
      exact Ideal.mul_mem_right (X 1 : MvPolynomial (Fin 3) K) _ hN
    · refine ⟨N, g * X 1, ?_⟩
      show zA K a b h ^ N * (p * X (2 : Fin 3)) - MvPolynomial.rename zEmb (g * X 1)
        ∈ Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K))
      rw [show zA K a b h ^ N * (p * X 2) - MvPolynomial.rename zEmb (g * X 1)
          = (zA K a b h ^ N * p - MvPolynomial.rename zEmb g) * X 2 from by
        simp only [map_mul, MvPolynomial.rename_X]
        norm_num
        ring]
      exact Ideal.mul_mem_right (X 2 : MvPolynomial (Fin 3) K) _ hN

theorem ker_zPsi_eq_saturation (K : Type) [Field K] (a b h : K) [IsDomain (Work.MotK.TGen.ZD K a b h)] (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (f : MvPolynomial (Fin 3) K) : f ∈ RingHom.ker (Work.MotK.TGen.zPsi K a b h) ↔ ∃ N : ℕ, (Work.MotK.TGen.zA K a b h)^N * f ∈ Ideal.span ({Work.MotK.TGen.zg K a b h, Work.MotK.TGen.zB K a b h} : Set (MvPolynomial (Fin 3) K)) := by
  constructor
  · intro hf
    rw [RingHom.mem_ker] at hf
    obtain ⟨N, g, hN⟩ := aux_reduce K a b h f
    refine ⟨N, ?_⟩
    have hzB : zB K a b h ∈ RingHom.ker (zPsi K a b h) :=
      RingHom.mem_ker.mpr (aux_zPsi_zB K a b h ha hb hh)
    have hle : Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K)) ≤
        RingHom.ker (zPsi K a b h) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hzB)
    have hmem := hle hN
    rw [RingHom.mem_ker, map_sub, map_mul, map_pow, zPsi_zA, zPsi_rename, hf, mul_zero,
      zero_sub] at hmem
    have hg0 : Ideal.Quotient.mk
        (Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K))) g = 0 :=
      IsFractionRing.injective (ZD K a b h) (ZF K a b h)
        (by rw [map_zero]; exact neg_eq_zero.mp hmem)
    have hgm : g ∈ Ideal.span ({Work.MotK.TwCensus.ZElim2 a b h} : Set (MvPolynomial (Fin 2) K)) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hg0
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hgm
    have hrg : MvPolynomial.rename zEmb g = zg K a b h * MvPolynomial.rename zEmb r := by
      rw [hr, map_mul]; rfl
    have hgspan : MvPolynomial.rename zEmb g ∈
        Ideal.span ({zg K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) := by
      rw [hrg]
      exact Ideal.mul_mem_right (MvPolynomial.rename zEmb r) _ (Ideal.subset_span (by simp))
    have hsub : Ideal.span ({zB K a b h} : Set (MvPolynomial (Fin 3) K)) ≤
        Ideal.span ({zg K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr (by simp))
    have heq : zA K a b h ^ N * f
        = (zA K a b h ^ N * f - MvPolynomial.rename zEmb g) + MvPolynomial.rename zEmb g := by
      rw [sub_add_cancel]
    rw [heq]
    exact Ideal.add_mem _ (hsub hN) hgspan
  · rintro ⟨N, hN⟩
    rw [RingHom.mem_ker]
    have hle : Ideal.span ({zg K a b h, zB K a b h} : Set (MvPolynomial (Fin 3) K)) ≤
        RingHom.ker (zPsi K a b h) := by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact zPsi_zg K a b h
      · exact aux_zPsi_zB K a b h ha hb hh
    have hmem : zA K a b h ^ N * f ∈ RingHom.ker (zPsi K a b h) := hle hN
    rw [RingHom.mem_ker, map_mul, map_pow, zPsi_zA, mul_eq_zero] at hmem
    rcases hmem with hz | hz
    · exact absurd hz (pow_ne_zero N (aux_za1_ne_zero K a b h ha hb hh))
    · exact hz

end Work.MotK.TGen
