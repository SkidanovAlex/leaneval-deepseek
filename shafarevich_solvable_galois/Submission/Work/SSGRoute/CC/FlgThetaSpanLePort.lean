import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.CC.FlgThetaDefs
import Submission.Work.SSGRoute.CC.FlgFourLettersLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Port of `Submission/Work/SSGRoute/flgThetaSpan_le.lean`

The chain-`B` file `flgThetaSpan_le.lean` invokes `Work.SSGRoute.flgBilin_gen_gen`, whose proof in
`flgBilin_gen_gen.lean` was replaced by a `sorry` stub (`_flgBilinStub.lean`).  This module is a
copy wrapped in the fresh namespace `Work.SSGRoute.LNS3B` in which that generator-generator case
is proved directly (from the degree-four identities of `flgThetaDefs`/`flg_defs`), so that the
`(4,4)` graded step does not inherit the stub's `sorry`.
-/

namespace Work.SSGRoute.CC.LNS3B

/-- **Generator-generator case of the bilinear form.**

Write `g_{xy} = x² + ⁅x,y⁆` (`flgGen`), so that `flgGen` is the sum of a square (`flgSq`) and a
bracket.  For letters `p.1, p.2` and `q.1, q.2` the anti-commutator
`flgBilin σ g_p (g_q) = g_p * σA g_q + σA g_q * g_p` splits into the four anti-commutators

`{x², (σz)²}`, `{x², ⁅σz,σw⁆}`, `{⁅x,y⁆, (σz)²}`, `{⁅x,y⁆, ⁅σz,σw⁆}`,

each of which is expressed by `flgSq_sq_identity`, `flgSq_brk_identity` (twice) and
`flg_brk4_outer` as a sum of degree-`4` left-nested brackets `brk4`, hence lies in `Wsub X`. -/
theorem flgBilin_gen_gen (X : Type) (σ : X → X) (p q : X × X) :
    Work.SSGRoute.CC.flgBilin X σ (Work.SSGRoute.CC.flgGen X p) (Work.SSGRoute.CC.flgGen X q)
      ∈ Work.SSGRoute.Wsub X := by
  have hv : sigA X σ (flgGen X q)
      = flgSq X (σ q.1) + brk X (flg_ltr X (σ q.1)) (flg_ltr X (σ q.2)) := by
    rw [flgGen_eq X q, map_add, sigA_flgSq_fact X σ q.1, sigA_brk_fact X σ q.1 q.2]
  have h11 : flgSq X p.1 * flgSq X (σ q.1) + flgSq X (σ q.1) * flgSq X p.1 ∈ Wsub X := by
    rw [flgSq_sq_identity X p.1 (σ q.1)]
    exact Submodule.subset_span ⟨(p.1, σ q.1, p.1, σ q.1), rfl⟩
  have h12 : flgSq X p.1 * brk X (flg_ltr X (σ q.1)) (flg_ltr X (σ q.2))
      + brk X (flg_ltr X (σ q.1)) (flg_ltr X (σ q.2)) * flgSq X p.1 ∈ Wsub X := by
    rw [flgSq_brk_identity X p.1 (σ q.1) (σ q.2)]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨(p.1, σ q.1, σ q.2, p.1), rfl⟩)
      (Submodule.subset_span ⟨(p.1, σ q.2, σ q.1, p.1), rfl⟩)
  have h21 : brk X (flg_ltr X p.1) (flg_ltr X p.2) * flgSq X (σ q.1)
      + flgSq X (σ q.1) * brk X (flg_ltr X p.1) (flg_ltr X p.2) ∈ Wsub X := by
    rw [add_comm (brk X (flg_ltr X p.1) (flg_ltr X p.2) * flgSq X (σ q.1))
      (flgSq X (σ q.1) * brk X (flg_ltr X p.1) (flg_ltr X p.2))]
    rw [flgSq_brk_identity X (σ q.1) p.1 p.2]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨(σ q.1, p.1, p.2, σ q.1), rfl⟩)
      (Submodule.subset_span ⟨(σ q.1, p.2, p.1, σ q.1), rfl⟩)
  have h22 : brk X (brk X (flg_ltr X p.1) (flg_ltr X p.2))
      (brk X (flg_ltr X (σ q.1)) (flg_ltr X (σ q.2))) ∈ Wsub X := by
    rw [← flg_brk4_outer X p.1 p.2 (σ q.1) (σ q.2)]
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨(p.1, p.2, σ q.1, σ q.2), rfl⟩)
      (Submodule.subset_span ⟨(p.1, p.2, σ q.2, σ q.1), rfl⟩)
  have hexp : flgBilin X σ (flgGen X p) (flgGen X q)
      = (flgSq X p.1 * flgSq X (σ q.1) + flgSq X (σ q.1) * flgSq X p.1)
        + (flgSq X p.1 * brk X (flg_ltr X (σ q.1)) (flg_ltr X (σ q.2))
            + brk X (flg_ltr X (σ q.1)) (flg_ltr X (σ q.2)) * flgSq X p.1)
        + (brk X (flg_ltr X p.1) (flg_ltr X p.2) * flgSq X (σ q.1)
            + flgSq X (σ q.1) * brk X (flg_ltr X p.1) (flg_ltr X p.2))
        + brk X (brk X (flg_ltr X p.1) (flg_ltr X p.2))
            (brk X (flg_ltr X (σ q.1)) (flg_ltr X (σ q.2))) := by
    rw [flgBilin, hv, flgGen_eq X p]
    simp only [brk]
    noncomm_ring
  rw [hexp]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.add_mem _ h11 h12) h21) h22


noncomputable section

variable {X : Type}

/-- **The bilinear form on `Tsub` lands in `Wsub`.**

Given the case computation on the generators `flgGen X p`, the form
`flgBilin X σ u v = u * σA v + σA v * u` maps `Tsub X × Tsub X` into `Wsub X`: both variables
range over the span of the `flgGen X p`, and `flgBilin` is additive in each of them. -/
theorem flgBilin_mem_Wsub_of_gen_gen (X : Type) (σ : X → X)
    (h : ∀ p q : X × X, flgBilin X σ (flgGen X p) (flgGen X q) ∈ Wsub X)
    (u v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hu : u ∈ Tsub X) (hv : v ∈ Tsub X) :
    flgBilin X σ u v ∈ Wsub X := by
  have h1 : ∀ q : X × X, ∀ u ∈ Tsub X, flgBilin X σ u (flgGen X q) ∈ Wsub X := by
    intro q u hu
    rw [Tsub_eq_span_flgGen] at hu
    refine Submodule.span_induction
      (p := fun u _ => flgBilin X σ u (flgGen X q) ∈ Wsub X) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨q', rfl⟩
      exact h q' q
    · simp [flgBilin]
    · intro a b _ _ ha hb
      rw [flgBilin_add_left]
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl
      · simpa [flgBilin] using ha
      · simpa using ha
  rw [Tsub_eq_span_flgGen] at hv
  refine Submodule.span_induction (p := fun v _ => flgBilin X σ u v ∈ Wsub X) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨q, rfl⟩
    exact h1 q u hu
  · simp [flgBilin]
  · intro a b _ _ ha hb
    rw [flgBilin_add_right]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simpa [flgBilin] using ha
    · simpa using ha

/-- `σA w + w` lies in `(σA + id)(Wsub X)` for `w ∈ Wsub X`. -/
theorem flgDeltaW_mem (X : Type) (σ : X → X) {w : MonoidAlgebra (ZMod 2) (FreeMonoid X)}
    (hw : w ∈ Wsub X) : sigA X σ w + w ∈ flgDeltaW X (sigAL X σ) := by
  rw [← flgDeltaL_apply X σ w, flgDeltaW_eq_map]
  exact Submodule.mem_map_of_mem hw

/-- **The `φ`-value at a sum**, given the two values and membership in `Tsub`. -/
theorem phi_add_mem (X : Type) (σ : X → X) (hσ : ∀ x, σ (σ x) = x)
    {u v : MonoidAlgebra (ZMod 2) (FreeMonoid X)} (hu : u ∈ Tsub X) (hv : v ∈ Tsub X)
    (huD : phi X σ u ∈ flgDeltaW X (sigAL X σ) + selfSpan X σ + brkSpan X σ)
    (hvD : phi X σ v ∈ flgDeltaW X (sigAL X σ) + selfSpan X σ + brkSpan X σ) :
    phi X σ (u + v) ∈ flgDeltaW X (sigAL X σ) + selfSpan X σ + brkSpan X σ := by
  have hw : flgBilin X σ u v ∈ Wsub X :=
    flgBilin_mem_Wsub_of_gen_gen X σ (flgBilin_gen_gen X σ) u v hu hv
  rw [phi_add_phi X σ hσ u v]
  refine Submodule.add_mem _ (Submodule.add_mem _ huD hvD) ?_
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (flgDeltaW_mem X σ hw))

/-- **The residual span of `φ` on `Tsub` is spanned by the realisable pieces.** -/
theorem phi_mem_D (X : Type) [DecidableEq X] (σ : X → X) (hσ : ∀ x, σ (σ x) = x)
    (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hu : u ∈ Tsub X) :
    phi X σ u ∈ flgDeltaW X (sigAL X σ) + selfSpan X σ + brkSpan X σ := by
  rw [Tsub_eq_span_flgGen] at hu
  refine Submodule.span_induction
    (p := fun u _ => phi X σ u ∈ flgDeltaW X (sigAL X σ) + selfSpan X σ + brkSpan X σ)
    ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨q, rfl⟩
    rw [flgGen_eq X q]
    refine phi_add_mem X σ hσ (flgSq_mem_Tsub X q.1) (flg_brk_mem_Tsub X q.1 q.2) ?_ ?_
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_right (Submodule.subset_span ⟨q.1, rfl⟩))
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨(q.1, q.2), rfl⟩)
  · simp [phi]
  · intro a b ha hb haD hbD
    refine phi_add_mem X σ hσ ?_ ?_ haD hbD
    · rwa [Tsub_eq_span_flgGen]
    · rwa [Tsub_eq_span_flgGen]
  · intro c a ha haD
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp [phi]
    · simpa using haD

/-- **The residual span of the abstract degree-`4` statement is generated by the realisable
families.**

Let `X` be a type, `σ : X → X` an involution (`hσ`), `A = MonoidAlgebra (ZMod 2) (FreeMonoid X)`,
`σA = sigA X σ` the induced algebra endomorphism, `φ(u) = u * σA u + σA u * u` (`phi`), and

* `selfSpan X σ = span{φ(x*x) : x : X}`,
* `brkSpan X σ = span{φ([x,y]) : x y : X}`   (`[x,y] = x*y + y*x`),
* `flgThetaSpan X σA = span{φ(u) : u ∈ Tsub X}`, the residual span of `flg_assembly`
  (`free_lie_four_defs.lean`, `flg_defs.lean`),
* `flgDeltaW X σA = (σA + id)(Wsub X)`.

Claim: `flgThetaSpan X σA ≤ flgDeltaW X σA + selfSpan X σ + brkSpan X σ`.

Proof route.  `Tsub X` is spanned by the elements `g_{xy} = x*x + (y*x + x*y)`, `x y : X`; note
`g_{xx} = x*x` and `g_{xy} + g_{xx} = [x,y]`, so the family `{x*x} ∪ {[x,y]}` is contained in
`Tsub`.  For `u, v` in `A` one has the polarisation identity

  `φ(u+v) = φ(u) + φ(v) + (σA + id)(u * σA v + σA v * u)`,

using `σA (σA v) = v`.  Hence it suffices (a) that `u * σA v + σA v * u ∈ Wsub X` for
`u, v ∈ Tsub X`, and (b) that `φ(g) ∈ selfSpan + brkSpan` for the generators `g ∈ {x*x} ∪ {[x,y]}`,
which is immediate from the definitions.  Part (a) is bilinear in `(u,v)`, so it reduces to the
cases `u, v ∈ {x*x, [x,y]}` for letters:

* `[x,y] * [z,w] + [z,w] * [x,y] = brk4(x,y,z,w) + brk4(x,y,w,z)` (`flg_brk4_outer`);
* `x*x * (z*w+w*z) + (z*w+w*z) * x*x = brk4(x,z,w,x) + brk4(x,w,z,x)` (use
  `u * x + x * u = brk(u,x)` and the Jacobi identity `flg_brk_brk`);
* `x*x * (z*z) + (z*z) * x*x = brk4(x,z,x,z)` (compute `[[[x,z],x],z] = x*x*z*z + z*z*x*x`);
* the remaining mixed cases follow by symmetry of `brk`. -/
theorem flgThetaSpan_le (X : Type) [DecidableEq X] (σ : X → X) (hσ : ∀ x, σ (σ x) = x) :
    flgThetaSpan X (sigAL X σ) ≤
      flgDeltaW X (sigAL X σ) + selfSpan X σ + brkSpan X σ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, rfl⟩
  exact phi_mem_D X σ hσ (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) u.2

end

end Work.SSGRoute.CC.LNS3B
