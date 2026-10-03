import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_asm
import Submission.Work.L62.head_stability
import Submission.Work.L62.head_package
import Submission.Work.L62.tail_uniform3

/-!
# L62 (c) — Shishikura's Lemma 6.2, lifted `ℂ/ℤ` model: `Work.L62.l62c`

`Work.L62.l62c : L62Statement` is obtained by feeding the two geometric inputs into the assembly
`Work.L62.l62c_aux` (`Submission/Work/L62/l62c_asm.lean`):

* `Work.L62.tail_uniform3` — the deep tail of the chain, at both ends, with β-uniform constants;
* `Work.L62.head_package` — the finite head of the chain, uniformly in a neighbourhood of each
  parameter `β`; it consumes `Work.L62.head_stability` (the disc-shadowing step of Lemma 6.2)
  through the interface `Work.L62.StabHyp`.

Everything else — the end choice (`exists_uniform_drift`), the finite cover of the parameter box
(`cover_extract`), the splicing of the head and the tail and the contract's conjunction — is in
`l62c_asm.lean`.  See `NOTES_L62_FINAL.md`.
-/

namespace Work.L62

open MandelDim

theorem l62c : L62Statement := by
  intro g₀ D hF0 d hd b hb ζa ζb hζa hζb hsepab
  have hhead : HeadHyp d hd b ζa ζb := by
    intro κ Y cl hκ hY hcl β hβ0 hβ1 hβb s hav
    have hstab : StabHyp d := by
      intro β₀ j₀ hj₀ ζ z hz0 hz r hr hr8 hcollar
      exact head_stability d hd hj₀ hz0 hz hr hr8 hcollar
    obtain ⟨ζ, j₀, ρ₁, ε, δ, C, C', A, hζ, hj₀, hρ₁, hε, hδ, hC, hC', hρκ, hρ48, hAc, hADE,
      hmain⟩ :=
      head_package d hd hb hκ hY hstab hcl hζa hζb hsepab β hβ0 hβ1 hβb s hav
    exact ⟨⟨ζ, j₀, ρ₁, ε, δ, C, C', A, hζ, hj₀, hρ₁, hρκ, hρ48, hε, hδ, hC, hC', hAc, hADE,
      hmain⟩⟩
  have htail : TailHyp d hd b := fun κ cl hκ hcl => tail_uniform3 d hd hb hκ hcl
  exact l62c_aux d hd b hb ζa ζb hζa hζb hsepab hhead htail

end Work.L62
