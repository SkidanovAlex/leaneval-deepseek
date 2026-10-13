import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.perfChartCoaug_kernel
import Submission.Work.DSM5b.perfChartH0_root_killing
import Submission.Work.DSM5b.perfectedRootKilling

/-!
# DSM5b — `DSMap.Mix2.area_M5b_proved`

Assembly of the frozen node `DSMap.Mix2.area_M5b` from its three conjuncts, which are the three
delegated results of this area:

* `Work.DSM5b.perfChartCoaug_kernel` — the coaugmentation is almost injective,
* `Work.DSM5b.perfChartH0_root_killing` — it is almost surjective on `0`-cycles,
* `Work.DSM5b.perfectedRootKilling` — positive-degree cohomology is killed by `ϖ k`.

With `I = ⊥` all three conditions of `DSMap.Mix2.AlmostAcyc` reduce to the identities
`⊥ • ⊤ = ⊥` and `a - b ∈ ⊥ ↔ a = b`, so the assembly is the identity.  The route is documented in
`Submission/Work/DSM5b/DESIGN.md`.
-/

universe a

namespace DSMap.Mix2

open CategoryTheory DSMap DSMap.Mix

/-- **M5b** (char-`p` blowup almost acyclicity), proved: `R` perfect of characteristic `p`,
`J = (t_i) ∋ T^e`, and `R → Č(perfected charts of Bl_J R)` is a `T^(1/p^∞)`-almost
quasi-isomorphism. -/
theorem area_M5b_proved (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = T ^ e) :
    AlmostAcyc (fun k => (frobeniusEquiv R p).symm^[k] T) ⊥
      ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)) (perfChartCoaug p t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw k
    simp only [Submodule.bot_smul, Submodule.mem_bot] at hw
    exact Work.DSM5b.perfChartCoaug_kernel p R t T j₀ e hj₀ w hw k
  · intro z hz k
    simp only [Submodule.bot_smul, Submodule.mem_bot] at hz
    obtain ⟨w, hw⟩ := Work.DSM5b.perfChartH0_root_killing p R t T j₀ e hj₀ k z hz
    exact ⟨w, by simpa only [Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] using hw⟩
  · intro q z hz k
    simp only [Submodule.bot_smul, Submodule.mem_bot] at hz
    obtain ⟨y, hy⟩ := Work.DSM5b.perfectedRootKilling p R t T j₀ e hj₀ k q z hz
    exact ⟨y, by simpa only [Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] using hy⟩

/-- the assembled node has exactly the frozen statement -/
example : @area_M5b_proved.{a} = @area_M5b.{a} := rfl

end DSMap.Mix2
