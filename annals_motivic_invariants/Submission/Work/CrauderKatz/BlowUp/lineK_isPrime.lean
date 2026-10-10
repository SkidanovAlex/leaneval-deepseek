/-
Copyright (c) 2026 the annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.CrauderKatz
-/
import Mathlib
import Submission.Work.CrauderKatz.BlowUp.LineDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CrauderKatz.BlowUp.lineK_isPrime`

The generic point `lineK 𝕜 = (x, ε)` of the exceptional surface of the thickened blow-up of `𝔸³`
along a line is a *prime* ideal, hence defines a point of `Spec (lineRing 𝕜)`.

The chart ring is `R = 𝕜[x,t,z,ε]/(ε², x·ε)` and `lineK = (x, ε)`; its quotient is
`R ⧸ (x,ε) ≅ 𝕜[t,z]`, a polynomial ring, hence a domain.  Rather than build that isomorphism we
realise `lineK` as the image of the prime ideal `(X 0, X 3) ⊆ 𝕜[X₀,X₁,X₂,X₃]` under the surjection
`𝕜[X₀,X₁,X₂,X₃] ↠ R`, and prove the latter prime by identifying it with the kernel of the
substitution `𝕜[X₀,X₁,X₂,X₃] →ₐ[𝕜] 𝕜[T,Z]`, `X₀ ↦ 0`, `X₁ ↦ T`, `X₂ ↦ Z`, `X₃ ↦ 0` — a ring
map into a domain.

The kernel computation is the only real content: `p` is killed by the substitution iff `p` is a
combination of `X₀` and `X₃`.  The inclusion `⊇` is immediate; for `⊆` we use that the
"projection" `ψ = ι ∘ φ` onto the `(X₁,X₂)`-plane (with `ι : 𝕜[T,Z] → 𝕜[X₀,X₁,X₂,X₃]`, a section
of `φ`) satisfies `p - ψ p ∈ (X₀, X₃)` for every `p`, which is proved by
`MvPolynomial.induction_on`.  This mirrors the plane case `thickK_isPrime`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

namespace Work.CrauderKatz.BlowUp

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The ideal `(X₀, X₃) ⊆ 𝕜[X₀,X₁,X₂,X₃]`, the preimage of `lineK` in the chart coordinates. -/
private abbrev lineSpanX03 : Ideal (MvPolynomial (Fin 4) 𝕜) :=
  Ideal.span {MvPolynomial.X (0 : Fin 4), MvPolynomial.X 3}

/-- The `𝕜`-algebra map `𝕜[X₀,X₁,X₂,X₃] → 𝕜[T,Z]` with `X₀ ↦ 0`, `X₁ ↦ T`, `X₂ ↦ Z`, `X₃ ↦ 0`. -/
private def linePhi : MvPolynomial (Fin 4) 𝕜 →ₐ[𝕜] MvPolynomial (Fin 2) 𝕜 :=
  MvPolynomial.aeval ![0, MvPolynomial.X 0, MvPolynomial.X 1, 0]

/-- The section `𝕜[T,Z] → 𝕜[X₀,X₁,X₂,X₃]`, `T ↦ X₁`, `Z ↦ X₂`, of `linePhi`. -/
private def lineIota : MvPolynomial (Fin 2) 𝕜 →ₐ[𝕜] MvPolynomial (Fin 4) 𝕜 :=
  MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 2]

/-- The projection `ψ = ι ∘ φ` onto the `(X₁,X₂)`-plane. -/
private def linePsi : MvPolynomial (Fin 4) 𝕜 →ₐ[𝕜] MvPolynomial (Fin 4) 𝕜 :=
  (lineIota 𝕜).comp (linePhi 𝕜)

/-- Each variable differs from its projection onto the `(X₁,X₂)`-plane by an element of
`(X₀, X₃)`. -/
private lemma linePsi_X (n : Fin 4) :
    MvPolynomial.X n - linePsi 𝕜 (MvPolynomial.X n) ∈ lineSpanX03 𝕜 := by
  fin_cases n
  · simpa [linePsi, linePhi, lineIota, lineSpanX03] using
      Ideal.subset_span (Set.mem_insert _ _)
  · simp [linePsi, linePhi, lineIota, lineSpanX03]
  · simp [linePsi, linePhi, lineIota, lineSpanX03]
  · simpa [linePsi, linePhi, lineIota, lineSpanX03] using
      Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Every polynomial differs from its projection onto the `(X₁,X₂)`-plane by an element of
`(X₀, X₃)`. -/
private lemma sub_linePsi_mem (p : MvPolynomial (Fin 4) 𝕜) :
    p - linePsi 𝕜 p ∈ lineSpanX03 𝕜 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [linePsi, linePhi, lineIota, lineSpanX03]
  | add p q hp hq =>
      have h : p + q - linePsi 𝕜 (p + q)
          = (p - linePsi 𝕜 p) + (q - linePsi 𝕜 q) := by
        rw [map_add]; ring
      rw [h]
      exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
      have hψn := linePsi_X 𝕜 n
      have h : p * MvPolynomial.X n - linePsi 𝕜 (p * MvPolynomial.X n)
          = (p - linePsi 𝕜 p) * MvPolynomial.X n
            + linePsi 𝕜 p * (MvPolynomial.X n - linePsi 𝕜 (MvPolynomial.X n)) := by
        rw [map_mul]; ring
      rw [h]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hψn)

/-- `(X₀, X₃)` is the kernel of the substitution `X₀ ↦ 0`, `X₁ ↦ T`, `X₂ ↦ Z`, `X₃ ↦ 0`. -/
private lemma lineSpanX03_eq_ker :
    lineSpanX03 𝕜 = RingHom.ker (linePhi 𝕜) := by
  refine le_antisymm ?_ ?_
  · rw [lineSpanX03, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor <;> simp [linePhi]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    simpa [linePsi, hp] using sub_linePsi_mem 𝕜 p

/-- `(X₀, X₃)` is prime: it is the kernel of a ring map into the domain `𝕜[T,Z]`. -/
private lemma lineSpanX03_isPrime : (lineSpanX03 𝕜).IsPrime := by
  rw [lineSpanX03_eq_ker 𝕜]
  exact RingHom.ker_isPrime (linePhi 𝕜)

/-- `lineK` is the image of `(X₀, X₃)` under the quotient surjection `𝕜[X₀,X₁,X₂,X₃] ↠ R`. -/
private lemma lineK_eq_map :
    lineK 𝕜 = Ideal.map (Ideal.Quotient.mk (lineI 𝕜)) (lineSpanX03 𝕜) := by
  simp [lineK, lineSpanX03, lineX, lineE, Ideal.map_span]

/-- **The generic point of the exceptional surface of the thickened blow-up along a line is a
point.**  The ideal `(x, ε) ⊆ 𝕜[x,t,z,ε]/(ε², x·ε)` is prime: its quotient is `𝕜[t,z]`, and it is
the image of the prime ideal `(X₀, X₃)` of the polynomial ring under the surjection
`𝕜[X₀,X₁,X₂,X₃] ↠ R`. -/
theorem lineK_isPrime (𝕜 : Type) [Field 𝕜] :
    (Work.CrauderKatz.BlowUp.lineK 𝕜).IsPrime := by
  rw [lineK_eq_map 𝕜]
  refine Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk (lineI 𝕜))
    (I := lineSpanX03 𝕜) (H := lineSpanX03_isPrime 𝕜) (Ideal.Quotient.mk_surjective) ?_
  rw [Ideal.mk_ker]
  exact lineI_le_span 𝕜

end

end Work.CrauderKatz.BlowUp
