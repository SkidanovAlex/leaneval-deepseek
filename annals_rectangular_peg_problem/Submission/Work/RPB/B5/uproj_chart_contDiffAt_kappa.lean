import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPV.Defs
namespace Work.RPB.B5
open Work.RPV
open scoped ContDiff
set_option autoImplicit false
noncomputable section
private lemma uproj_contDiff_twelve : ContDiff ℝ 12 (fun p : Work.RPV.PS => Work.RPV.uproj p) := by
  unfold Work.RPV.uproj
  have h12 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.1.2 : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.snd)
  have h11 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.1.1 : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp (contDiff_id.fst.fst)
  have h21 : ContDiff ℝ 12 (fun p : Work.RPV.PS => ((p.2.1 : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp (contDiff_id.snd.fst)
  exact ((Complex.contDiff_exp.comp (h12.mul contDiff_const))).mul (h21.add (h11.mul contDiff_const))
private lemma q₂_contDiff_twelve : ContDiff ℝ 12 (fun p : Work.RPV.PS => p.1.2) := by fun_prop
theorem uproj_chart_contDiffAt_kappa {ρ₀ : ℝ} {W : ℝ → ℝ → ℝ → Work.RPV.PS}
    {ρh : ℝ → ℝ → ℝ → ℝ}
    (hW : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {κ : ℝ} (hκ : 0 < κ)
    (hρh : ContDiffOn ℝ 12 (fun z : ℝ × (ℝ × ℝ) => ρh z.1 z.2.1 z.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-κ) κ))
    (hρhv : ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ t:ℝ, ∀ σ ∈ Set.Ioo (-κ) κ, ρh τ t σ ∈ Set.Ioo (-ρ₀) ρ₀)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) 1) {σ t : ℝ} (hσ : σ ∈ Set.Ioo (-κ) κ) :
    ContDiffAt ℝ 12 (fun p : ℝ × ℝ => Work.RPV.uproj (W τ p.2 (ρh τ p.2 p.1))) (σ, t) ∧
    ContDiffAt ℝ 12 (fun p : ℝ × ℝ => (W τ p.2 (ρh τ p.2 p.1)).1.2) (σ, t) := by
  have hTopen : IsOpen (Set.Ioo (-κ:ℝ) κ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hpt : (σ, t) ∈ Set.Ioo (-κ:ℝ) κ ×ˢ (Set.univ : Set ℝ) := ⟨hσ, trivial⟩
  have hρhst : ContDiffOn ℝ 12 (fun z : ℝ × ℝ => ρh τ z.2 z.1) (Set.Ioo (-κ:ℝ) κ ×ˢ (Set.univ : Set ℝ)) :=
    hρh.comp ((by fun_prop : ContDiff ℝ 12 (fun z : ℝ × ℝ => (((τ : ℝ), (z.2, z.1)) : ℝ × (ℝ × ℝ)))).contDiffOn)
      (fun z hz => ⟨hτ, trivial, hz.1⟩)
  have hΦcd : ContDiffOn ℝ 12 (fun z : ℝ × ℝ => (((τ : ℝ), (z.2, ρh τ z.2 z.1)) : ℝ × (ℝ × ℝ))) (Set.Ioo (-κ:ℝ) κ ×ˢ (Set.univ : Set ℝ)) :=
    contDiffOn_const.prodMk (contDiff_snd.contDiffOn.prodMk hρhst)
  have hmap : Set.MapsTo (fun z : ℝ × ℝ => (((τ : ℝ), (z.2, ρh τ z.2 z.1)) : ℝ × (ℝ × ℝ)))
      (Set.Ioo (-κ:ℝ) κ ×ˢ (Set.univ : Set ℝ)) (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) :=
    fun z hz => ⟨hτ, trivial, hρhv τ hτ z.2 z.1 hz.1⟩
  have hWcd : ContDiffOn ℝ 12 (fun z : ℝ × ℝ => W τ z.2 (ρh τ z.2 z.1)) (Set.Ioo (-κ:ℝ) κ ×ˢ (Set.univ : Set ℝ)) :=
    hW.comp hΦcd hmap
  have hu : ContDiffAt ℝ 12 (fun z : ℝ × ℝ => W τ z.2 (ρh τ z.2 z.1)) (σ, t) :=
    hWcd.contDiffAt (hTopen.mem_nhds hpt)
  refine ⟨?_, ?_⟩
  · exact ContDiffAt.comp (σ, t) uproj_contDiff_twelve.contDiffAt hu
  · exact ContDiffAt.comp (σ, t) (f := fun z : ℝ × ℝ => W τ z.2 (ρh τ z.2 z.1))
      (g := fun p : Work.RPV.PS => p.1.2) q₂_contDiff_twelve.contDiffAt hu
end
end Work.RPB.B5
