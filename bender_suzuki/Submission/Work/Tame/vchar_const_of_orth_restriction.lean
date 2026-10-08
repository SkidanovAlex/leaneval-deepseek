import Mathlib
import Submission.Work.Tame.Defs
import Submission.Work.Tame.Tau
import Submission.Work.Tame.Hyp
import Submission.Work.Tame.irr_vanishes_off_hatN
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.Induction.All
import Submission.Work.Clifford.All
import Submission.Work.Tame.ft10_2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame.vchar_const_of_orth_restriction`

Feit–Thompson Lemma 10.2 (p. 814), in the "restriction" form: the orthogonality hypothesis is
phrased as `⟨Θ|_𝔑_i, θ₁ - θ₂⟩ = 0` (inner product of the *restriction* of `Θ` to
`𝔑_i = N(𝔎_i)`) rather than as `⟨Θ, (θ₁ - θ₂)^*⟩ = 0` (inner product of `Θ` with the induced
character).  The two are the same by Frobenius reciprocity, so the result is an immediate
consequence of `Work.Tame.ft10_2`.
-/

namespace Work.Tame

open Classical

theorem vchar_const_of_orth_restriction {X : Type*} [Group X] [Fintype X] {Lhat : Set X}
    {n : ℕ} {Hs : Fin n → Subgroup X} {i : Fin n} (h : Hyp10_2 Lhat n Hs i) {Θ : X → ℂ}
    (hΘ : CharCore.IsVChar Θ)
    (horth : ∀ (α : ↥(Hs i) → ℂ), Coherence.cfInner α (1 : ↥(Hs i) → ℂ) = 0 →
      ∀ θ₁ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)),
      ∀ θ₂ ∈ CharCore.Irr ↥(Lgrp (Hs i : Set X)),
        (∀ hh : ↥(Hs i), θ₁ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh) →
        (∀ hh : ↥(Hs i), θ₂ ⟨(hh : X), (Hs i).le_normalizer hh.2⟩ = α hh) →
        Coherence.cfInner (fun N : ↥(Lgrp (Hs i : Set X)) => Θ (N : X)) (θ₁ - θ₂) = 0) :
    ∀ N : X, N ∈ Lgrp (Hs i : Set X) → N ∉ (Hs i : Set X) →
      ∀ H : X, H ∈ Hs i → Θ (N * H) = Θ N := by
  refine ft10_2 h hΘ ?_
  intro α hα θ₁ hθ₁ θ₂ hθ₂ hres₁ hres₂
  have hkey := horth α hα θ₁ hθ₁ θ₂ hθ₂ hres₁ hres₂
  have hfr := Induction.frobenius_reciprocity_transposed (Lgrp (Hs i : Set X)) Θ
      (fun y => θ₁ y - θ₂ y) hΘ.isClassFun
  change CharCore.cfInner Θ
      (Induction.indFun (Lgrp (Hs i : Set X)) (fun y => θ₁ y - θ₂ y)) = 0
  rw [hfr]
  exact hkey

end Work.Tame
