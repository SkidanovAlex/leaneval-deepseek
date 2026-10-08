import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.pCoreSeries_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_p(G) = 1` and `O_{p'}(G) = 1` force `G = 1` for `p`-solvable `G`

If `G` is a finite `p`-solvable group with trivial `p`-core and trivial `p'`-core, then `G`
is trivial.

The point is that the upper `p`-series
`1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ O_{p',p,p'}(G) ≤ ⋯`
is obtained by pulling back `O_π` of a quotient along `G ↠ G/O_{…}(G)`.  Once a term of the
series is trivial, the next term is the pullback of `O_π(G/1) ≅ O_π(G)` along a bijection,
i.e. it is `O_{p'}(G) = 1` when the step is a `p'`-step and `O_p(G) = 1` when the step is a
`p`-step.  Hence every term of the series is trivial, and `p`-solvability — which says that
some term is `⊤` — forces `⊤ = ⊥`, i.e. `G` is trivial.
-/

noncomputable section

open Classical

namespace Work.Fitting

/-- If `O_p(G) = 1` and `O_{p'}(G) = 1` then every term of the upper `p`-series of `G`
is trivial. -/
theorem pCoreSeries_eq_bot_of_pCore_eq_bot_of_pPrimeCore_eq_bot (p : ℕ) (G : Type*) [Group G]
    [Finite G] (h1 : Work.Fitting.pCore p G = ⊥) (h2 : Work.Fitting.pPrimeCore p G = ⊥) :
    ∀ n, Work.Fitting.pCoreSeries p G n = ⊥ := by
  intro n
  induction n with
  | zero => exact pCoreSeries_zero p G
  | succ n ih =>
    rw [pCoreSeries_succ p G n]
    have hinj : Function.Injective (QuotientGroup.mk' (pCoreSeries p G n)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', ih]
    have hsurj : Function.Surjective (QuotientGroup.mk' (pCoreSeries p G n)) :=
      QuotientGroup.mk'_surjective _
    haveI : Finite (G ⧸ pCoreSeries p G n) := Finite.of_surjective _ hsurj
    rw [piCore_comap_of_bijective (π := fun q => if Even n then q ≠ p else q = p)
      (QuotientGroup.mk' (pCoreSeries p G n)) hinj hsurj]
    by_cases hn : Even n
    · have hfun : (fun q : ℕ => (if Even n then q ≠ p else q = p)) = (fun q => q ≠ p) := by
        funext q; simp only [hn, ↓reduceIte]
      rw [hfun]
      exact h2
    · have hfun : (fun q : ℕ => (if Even n then q ≠ p else q = p)) = (fun q => q = p) := by
        funext q; simp only [hn, ↓reduceIte]
      rw [hfun]
      exact h1

theorem subsingleton_of_pCore_eq_bot_of_pPrimeCore_eq_bot (p : ℕ) (G : Type*) [Group G]
    [Finite G] [Work.Fitting.IsPSolvable p G] (h1 : Work.Fitting.pCore p G = ⊥)
    (h2 : Work.Fitting.pPrimeCore p G = ⊥) : Subsingleton G := by
  obtain ⟨n, hn⟩ := Work.Fitting.IsPSolvable.out (p := p) (G := G)
  have hbot := pCoreSeries_eq_bot_of_pCore_eq_bot_of_pPrimeCore_eq_bot p G h1 h2 n
  rw [hn] at hbot
  refine ⟨fun a b => ?_⟩
  have hle : (⊤ : Subgroup G) ≤ ⊥ := le_of_eq hbot
  have ha : a = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_top a))
  have hb : b = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_top b))
  rw [ha, hb]

end Work.Fitting
