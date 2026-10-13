import Mathlib
import Submission.Work.DSM4p.chartComp_modPow

/-!
# `Work.DSM4p.adicCompletion_frobInj`

Frobenius injectivity modulo `p` (in the `ϖ`-form `x ^ p ∈ (ϖ ^ p) → x ∈ (ϖ)`) is inherited by
the `p`-adic completion.

Let `E` be a commutative ring, `p` a prime, `w : E` with `w ^ p = p · v` for a unit `v` of `E`
(so that `(p) ⊆ (w)`: indeed `p = w ^ p · v⁻¹ = w · (w ^ (p - 1) v⁻¹)`), and assume the mod-`p`
hypothesis

  `∀ u : E ⧸ (p),  u ^ p = 0 → u ∈ (w̄)`.

Then for `y` in the `p`-adic completion `Ê = AdicCompletion (p) E`,

  `y ^ p ∈ (p)  →  y ∈ (w_Ê)`,  `w_Ê = algebraMap E Ê w`.

## The argument

The mod-`p` hypothesis is *equivalent* to the level-`E` Frobenius statement

  `(⋆)`  `∀ a : E,  a ^ p ∈ (p) → a ∈ (w)`,

because for `a ∈ E` with `a ^ p ∈ (p)`, the class `ā ∈ E / (p)` satisfies `ā ^ p = 0`, hence
`ā ∈ (w̄)`, i.e. `a = w·d + p·e`, and `p·e = w ^ p · v⁻¹ · e = w · (w ^ (p-1) v⁻¹ e) ∈ (w)`.

The transfer to `Ê` uses only the *first* component `θ = AdicCompletion.evalOneₐ (p) : Ê → E ⧸ (p)`,
together with Mathlib's `AdicCompletion.ker_evalOneₐ_eq_map` (`(p)` is finitely generated):

* `y ^ p ∈ (p) ⊆ ker θ`, so `θ y ^ p = θ (y ^ p) = 0`;
* lift `θ y` to `a ∈ E`: then `a ^ p ∈ (p)`, so `a ∈ (w)` by `(⋆)`, i.e. `algebraMap a ∈ (w_Ê)`;
* `y - algebraMap a ∈ ker θ = (p)_Ê ⊆ (w_Ê)`, since `p ∈ (w)` also in `Ê`.

Hence `y ∈ (w_Ê)`.
-/

namespace Work.DSM4p

universe a

theorem adicCompletion_frobInj {E : Type a} [CommRing E] {p : ℕ} [Fact p.Prime] (w : E)
    (hunit : ∃ v : Eˣ, w ^ p = (p : E) * (v : E))
    (hmodp : ∀ u : E ⧸ Ideal.span {(p : E)},
      u ^ p = 0 → u ∈ Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : E)}) w)}) :
    ∀ y : AdicCompletion (Ideal.span {(p : E)}) E,
      y ^ p ∈ Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)} →
      y ∈ Ideal.span {algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) w} := by
  classical
  obtain ⟨v, hv⟩ := hunit
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hFG : (Ideal.span {(p : E)}).FG := Submodule.fg_span_singleton (p : E)
  -- `p = w ^ p * v⁻¹`, hence `p ∈ (w)`
  have hpe : (p : E) = w ^ p * ((v⁻¹ : Eˣ) : E) := by
    have h : (p : E) * ((v : Eˣ) : E) = w ^ p := hv.symm
    have h2 := congrArg (fun t : E => t * ((v⁻¹ : Eˣ) : E)) h
    simpa [mul_assoc] using h2
  have hp_div : (p : E) ∈ Ideal.span {w} := by
    rw [hpe]
    exact Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton w)) p hp_pos)
  have hle : Ideal.span {(p : E)} ≤ Ideal.span {w} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp_div)
  -- the mod-`p` hypothesis, in the level-`E` Frobenius form `(⋆)`
  have hE : ∀ a : E, a ^ p ∈ Ideal.span {(p : E)} → a ∈ Ideal.span {w} := by
    intro a ha
    have hu : (Ideal.Quotient.mk (Ideal.span {(p : E)}) a) ^ p = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    have hmem := hmodp (Ideal.Quotient.mk (Ideal.span {(p : E)}) a) hu
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hsub : a - w * d ∈ Ideal.span {(p : E)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
    have h1 : a - w * d ∈ Ideal.span {w} := hle hsub
    have h2 : w * d ∈ Ideal.span {w} :=
      Ideal.mul_mem_right d _ (Ideal.subset_span (Set.mem_singleton w))
    have : a = (a - w * d) + w * d := by ring
    rw [this]
    exact add_mem h1 h2
  -- the same divisibility inside the completion
  have hp_div' : (p : AdicCompletion (Ideal.span {(p : E)}) E)
      ∈ Ideal.span {algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) w} := by
    rw [← map_natCast (algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E)) p, hpe, map_mul,
      map_pow]
    exact Ideal.mul_mem_right _ _
      (Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) p hp_pos)
  have hle' : Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)}
      ≤ Ideal.span {algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) w} :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp_div')
  -- the kernel of the first-component map is `(p)` in the completion
  have hker : RingHom.ker (AdicCompletion.evalOneₐ (Ideal.span {(p : E)})).toRingHom
      = Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)} := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map (Ideal.span {(p : E)}) hFG, Ideal.map_span,
      Set.image_singleton, map_natCast]
  intro y hy
  have hθ : (AdicCompletion.evalOneₐ (Ideal.span {(p : E)})).toRingHom y ^ p = 0 := by
    have hy0 : y ^ p ∈ RingHom.ker (AdicCompletion.evalOneₐ (Ideal.span {(p : E)})).toRingHom := by
      rw [hker]
      exact hy
    rw [← map_pow, RingHom.mem_ker.mp hy0]
  obtain ⟨a, ha⟩ :=
    Ideal.Quotient.mk_surjective ((AdicCompletion.evalOneₐ (Ideal.span {(p : E)})).toRingHom y)
  have hap : a ^ p ∈ Ideal.span {(p : E)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ha]
    exact hθ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hE a hap)
  have hcoe : ∀ b : E, (AdicCompletion.evalOneₐ (Ideal.span {(p : E)})).toRingHom
        (algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) b)
      = Ideal.Quotient.mk (Ideal.span {(p : E)}) b := by
    intro b
    show AdicCompletion.evalOneₐ (Ideal.span {(p : E)})
      (algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) b)
      = Ideal.Quotient.mk (Ideal.span {(p : E)}) b
    rw [AdicCompletion.algebraMap_apply]
    show AdicCompletion.evalOneₐ (Ideal.span {(p : E)})
      (AdicCompletion.of (Ideal.span {(p : E)}) E (algebraMap E E b))
      = Ideal.Quotient.mk (Ideal.span {(p : E)}) b
    rw [AdicCompletion.evalOneₐ_of]
    exact congrArg (Ideal.Quotient.mk (Ideal.span {(p : E)})) (Algebra.algebraMap_self_apply b)
  have hdiff : y - algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) a
      ∈ Ideal.span {(p : AdicCompletion (Ideal.span {(p : E)}) E)} := by
    rw [← hker, RingHom.mem_ker, map_sub, hcoe a, ha, sub_self]
  have hmem2 : algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) a
      ∈ Ideal.span {algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) w} := by
    rw [hb, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  have hmem3 : y - algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) a
      ∈ Ideal.span {algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) w} := hle' hdiff
  have hsum : y = (y - algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) a)
      + algebraMap E (AdicCompletion (Ideal.span {(p : E)}) E) a := by ring
  rw [hsum]
  exact add_mem hmem3 hmem2

end Work.DSM4p
