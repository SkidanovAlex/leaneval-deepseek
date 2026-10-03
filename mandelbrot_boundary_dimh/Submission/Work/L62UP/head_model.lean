import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.head_compact
import Submission.Work.L62.l62c_mid
import Submission.Work.L62.avail_horn_section_up
import Submission.Work.L62.cylinder_model
import Submission.Work.L62.uniform_escape2
import Submission.Work.L62.local_ratio_contraction
import Submission.Work.L62.head_confine
import Submission.Work.L62.chain
import Submission.Work.L62.l62c_end
import Submission.Work.L62.avail_up
import Submission.Work.L62.lift_exists_unique
import Submission.Work.L62.lift_family_continuous
import Submission.Work.L62.head_escape_J

/-!
# `Work.L62UP.head_model_up` — the upper-end model head of Lemma 6.2 at a prescribed depth

This is `Work.L62.head_compact_ext` with the three "stub" lemmas of its development file replaced
by the real ones (`Work.L62.lift_exists_unique`, `Work.L62.lift_family_continuous`,
`Work.L62.head_escape_J`, all sorry-free) and with the escape depth **as a parameter** `Y`.

`head_model_up d hd hb hζa hζb hsep hY` returns `ρ₀ > 0`, a compact `K ⊆ hd.Bu` and `J > 0`
such that for every admissible `β` (`0 ≤ Re β ≤ 1`, `|Im β| ≤ b`, `AvailableUp`) and every
`0 < ρ ≤ ρ₀` the *model* map `ĥ = d.E - β` has a chain `W 0 = ball ζa ρ` (or `ball ζb ρ`),
`ĥ '' W (j+1) = W j` bijectively, all discs `W j ⊆ K` for `1 ≤ j ≤ J`, and `W J` deeper than `Y`.

The construction is the one of Shishikura's stability step: `head_compact` gives the first disc
`W 1 ⊆ K₀`, the global `T`-equivariant section `σ_β` of `ĥ` over the horn `Bu`
(`Work.L62.avail_horn_section_up` / the cylinder model `Work.L62.cylinder_model` with its uniform
escape) generates the rest of the chain `W j = σ_β^{j-1} '' W 1`, the confinement in one fixed
compact is `Work.L62.chain_in_compact` fed by the joint continuity of the section family
(`Work.L62.lift_family_continuous`), and the uniform depth is `Work.L62.head_escape_J`.
-/

namespace Work.L62
namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

private theorem isCompact_box_ext (b : ℝ) :
    IsCompact {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
  have himg : ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
      (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (-b) b))
      = {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} := by
    ext β
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := hp
      refine ⟨by simpa using hp1.1, by simpa using hp1.2, ?_⟩
      have h2 : ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I).im = p.2 := by simp
      rw [h2]
      exact abs_le.mpr ⟨hp2.1, hp2.2⟩
    · intro hβ
      refine ⟨(β.re, β.im), ⟨⟨hβ.1, hβ.2.1⟩, ?_⟩, ?_⟩
      · exact abs_le.mp hβ.2.2
      · simp
  rw [← himg]
  exact (isCompact_Icc.prod isCompact_Icc).image (by continuity)

/-- The chain iterate relation for `secChain`. -/
private theorem secChain_eq_iterate (σ : ℂ → ℂ) (W₀ W₁ : Set ℂ) {j : ℕ} (hj : 1 ≤ j) :
    secChain σ W₀ W₁ j = (σ)^[j - 1] '' W₁ := by
  conv_lhs => rw [show j = (j - 1) + 1 from (Nat.sub_add_cancel hj).symm]
  rw [secChain_succ]

/-- The π-relation along the section iterates. -/
private theorem piExp_iterate_section {S : Set ℂ} {Hσ : ℂ → ℂ} {σ : ℂ → ℂ}
    (hπ : ∀ w ∈ S, MandelDim.piExp (σ w) = Hσ (MandelDim.piExp w))
    (hmem : ∀ w ∈ S, σ w ∈ S) :
    ∀ (n : ℕ) {w : ℂ}, w ∈ S → MandelDim.piExp ((σ^[n]) w) = (Hσ^[n]) (MandelDim.piExp w) := by
  have hmem_iter : ∀ t : ℕ, ∀ w ∈ S, (σ^[t]) w ∈ S := by
    intro t
    induction t with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply']
        exact hmem _ (ih w hw)
  intro n
  induction n with
  | zero => intro w _; simp
  | succ k ih =>
      intro w hw
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        hπ _ (hmem_iter k w hw), ih hw]

/-- Depth bridge: small `‖piExp w‖` gives large `Im w`. -/
private theorem im_gt_of_norm_piExp_lt {w : ℂ} {y : ℝ}
    (h : ‖MandelDim.piExp w‖ < Real.exp (-(2 * Real.pi) * y)) : y < w.im := by
  rw [norm_piExp] at h
  have h2 := Real.exp_lt_exp.mp h
  nlinarith [Real.pi_pos]

/-- **The *extended* head chain lies in a fixed compact subset of the upper horn.**  Piece (i) of
`NOTES_L62_head_up.md` §4.  `W.L62.head_compact` supplies the one-step chain (`W 0 = ball ζ ρ`,
`W 1 ⊆ K₀ ⊆ hd.Bu`, `K₀` fixed); extending it by the global `T`-equivariant section `σ_β` of
`ĥ_β = d.E - β` over `hd.Bu` (`Work.L62.avail_horn_section_up`, hypothesis literally
`AvailableUp d hd β`) via `W (j+1) = σ_β^[j] '' W 1` (`Work.L62.secChain`/`secChain_spec`), the
whole chain up to a *uniform* step count `J` stays in **one fixed compact** `K ⊆ hd.Bu`.

Ingredients: `Work.L62.cylinder_model` (joint continuity of `(β,ζ) ↦ H β ζ = pushdown σ_β` on
`Λ × upOmega`, `H β 0 = 0`, `H β : upOmega → upOmega`, `π (σ_β u) = H β (π u)`);
`Work.L62.local_ratio_contraction` + `Work.L62.uniform_escape2` for the uniform escape of the
fixed compactum `π '' K₀` (with `J_esc`, `ε` free); and the *lift*-level control of the section
(a parametric version of `Work.L62.branch_translate_image`: for `β'` near `β`,
`σ_{β'} = σ_β (· + β' - β)` wherever both are defined, transported along the fixed horn `Bu`).
Note `pushdown` applies `π`, so the real part of the correction `σ_β - id - β` is NOT obtained
from `cylinder_model`; that is the one genuinely new component. -/
theorem head_model_up {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b : ℝ} (hb : 0 < b) {ζa ζb : ℂ} (hζa : ζa ∉ d.DE)
    (hζb : ζb ∉ d.DE) (hsep : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ)) {Y : ℝ} (hY : d.η₀ < Y) :
    ∃ (ρ₀ : ℝ) (K : Set ℂ) (J : ℕ) (σ : ℂ → ℂ → ℂ) (H : ℂ → ℂ → ℂ),
      0 < ρ₀ ∧ IsCompact K ∧ K ⊆ hd.Bu ∧ 0 < J ∧
      (∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → Work.L62.AvailableUp d hd β →
        DifferentiableOn ℂ (σ β) hd.Bu) ∧
      ContinuousOn (fun p : ℂ × ℂ => σ p.1 p.2)
        (({β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
          {β : ℂ | Work.L62.AvailableUp d hd β}) ×ˢ hd.Bu) ∧
      (∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → Work.L62.AvailableUp d hd β →
        ∀ w ∈ hd.Bu, σ β w ∈ hd.Bu ∧ d.E (σ β w) - β = w ∧
          MandelDim.piExp (σ β w) = H β (MandelDim.piExp w)) ∧
      (∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → Work.L62.AvailableUp d hd β →
        DifferentiableOn ℂ (H β) (Work.L62.upOmega d hd) ∧
          Set.MapsTo (H β) (Work.L62.upOmega d hd) (Work.L62.upOmega d hd) ∧
          H β 0 = 0 ∧ deriv (H β) 0 = MandelDim.piExp β) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b →
        Work.L62.AvailableUp d hd β →
        ∃ W : ℕ → Set ℂ,
          (W 0 = Metric.ball ζa ρ ∨ W 0 = Metric.ball ζb ρ) ∧
          (∀ j, j ≤ J → IsOpen (W j) ∧ IsConnected (W j)) ∧
          (∀ j, j < J → Set.InjOn (fun w => d.E w - β) (W (j + 1)) ∧
            (fun w => d.E w - β) '' W (j + 1) = W j) ∧
          (∀ j, 1 ≤ j → j ≤ J → W j ⊆ K) ∧
          (∀ j, 1 ≤ j → j ≤ J → W j = ((σ β)^[j - 1]) '' W 1) ∧
          (∀ j, j ≤ J → Bornology.IsBounded (W j)) ∧
          (∀ w ∈ W J, Y < w.im) := by

  classical
  obtain ⟨H, hH1, hHesc, hHcont⟩ := cylinder_model (b := b) d hd hb
  have hHdiff : ∀ β : ℂ, AvailableUp d hd β → DifferentiableOn ℂ (H β) (upOmega d hd) :=
    fun β hβ => (hH1 β hβ).1
  have hHmem : ∀ β : ℂ, AvailableUp d hd β → Set.MapsTo (H β) (upOmega d hd) (upOmega d hd) :=
    fun β hβ => (hH1 β hβ).2.1
  have hH0 : ∀ β : ℂ, AvailableUp d hd β → H β 0 = 0 := fun β hβ => (hH1 β hβ).2.2.1
  have hHder : ∀ β : ℂ, AvailableUp d hd β → deriv (H β) 0 = MandelDim.piExp β :=
    fun β hβ => by simpa [MandelDim.piExp] using (hH1 β hβ).2.2.2.1
  have hHsec : ∀ β : ℂ, AvailableUp d hd β → ∀ ζ ∈ upOmega d hd, ζ ≠ 0 →
      MandelDim.pushdown d.E (H β ζ) = MandelDim.piExp β * ζ :=
    fun β hβ => (hH1 β hβ).2.2.2.2
  have hHsec' : ∀ β : ℂ, AvailableUp d hd β → ∀ ζ ∈ upOmega d hd,
      MandelDim.pushdown (fun u => d.E u - β) (H β ζ) = ζ := by
    intro β hβ ζ hζ
    rcases eq_or_ne ζ 0 with rfl | hne
    · rw [hH0 β hβ, Work.Horn.MandelDim.pushdown_zero]
    · rw [Work.L62.pushdown_sub d.E β (H β ζ), hHsec β hβ ζ hζ hne, ← mul_assoc,
        Work.L62.piExp_neg_mul, one_mul]
  have hG_of : ∀ (β w : ℂ) (hβ : AvailableUp d hd β), w ∈ hd.Bu →
      MandelDim.pushdown (fun u => d.E u - β) (H β (MandelDim.piExp w)) = MandelDim.piExp w := by
    intro β w hβ hw
    exact hHsec' β hβ (MandelDim.piExp w) (Or.inr ⟨w, hw, rfl⟩)
  have hex : ∀ (β : ℂ), AvailableUp d hd β → ∀ w ∈ hd.Bu,
      ∃ u : ℂ, u ∈ hd.Bu ∧ MandelDim.piExp u = H β (MandelDim.piExp w) ∧ d.E u = w + β := by
    intro β hβ w hw
    obtain ⟨u, hu, -⟩ :=
      lift_exists_unique d hd hw (hHmem β hβ (Or.inr ⟨w, hw, rfl⟩)) (hG_of β w hβ hw)
    exact ⟨u, hu.1, hu.2.1, hu.2.2⟩
  let σ : ℂ → ℂ → ℂ := fun β w =>
    if h : AvailableUp d hd β ∧ w ∈ hd.Bu then Classical.choose (hex β h.1 w h.2) else 0
  have hσeq : ∀ (β : ℂ) (hβ : AvailableUp d hd β) (w : ℂ) (hw : w ∈ hd.Bu),
      σ β w = Classical.choose (hex β hβ w hw) := by
    intro β hβ w hw
    simp only [σ]
    rw [dif_pos ⟨hβ, hw⟩]
  have hσ : ∀ β : ℂ, AvailableUp d hd β → ∀ w ∈ hd.Bu,
      σ β w ∈ hd.Bu ∧ d.E (σ β w) = w + β ∧
        MandelDim.piExp (σ β w) = H β (MandelDim.piExp w) := by
    intro β hβ w hw
    obtain ⟨hu1, hu2, hu3⟩ := Classical.choose_spec (hex β hβ w hw)
    rw [hσeq β hβ w hw]
    exact ⟨hu1, hu3, hu2⟩
  have huniq : ∀ β : ℂ, AvailableUp d hd β → ∀ w ∈ hd.Bu, ∀ u : ℂ,
      u ∈ hd.Bu → MandelDim.piExp u = H β (MandelDim.piExp w) → d.E u = w + β → u = σ β w := by
    intro β hβ w hw u hu huπ huE
    obtain ⟨u₀, -, huniq₀⟩ :=
      lift_exists_unique d hd hw (hHmem β hβ (Or.inr ⟨w, hw, rfl⟩)) (hG_of β w hβ hw)
    have h1 : u = u₀ := huniq₀ u ⟨hu, huπ, huE⟩
    have h2 : σ β w = u₀ := by
      rw [hσeq β hβ w hw]
      exact huniq₀ (Classical.choose (hex β hβ w hw)) (Classical.choose_spec (hex β hβ w hw))
    rw [h1, h2]
  obtain ⟨hσdiff, hσcont⟩ :=
    lift_family_continuous d hd hb H hHdiff hHsec hHcont σ hσ huniq
  set Λ : Set ℂ := {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩
    {β : ℂ | AvailableUp d hd β} with hΛdef
  have hΛc : IsCompact Λ := (isCompact_box_ext b).inter_right (isClosed_availableUp d hd)
  obtain ⟨ρ₁, K₀, J₁, hρ₁, hK₀c, hK₀Bu, hJ₁, hhead⟩ :=
    head_compact (b := b) d hd hb hζa hζb hsep
  obtain ⟨Jc, hJcpos, hescJ⟩ :=
    head_escape_J d hd hb (y₁ := Y) H hHdiff hHmem hH0 hHder hHesc hHcont hK₀c hK₀Bu
  have hmapσ : ∀ β ∈ Λ, Set.MapsTo (σ β) hd.Bu hd.Bu := by
    intro β hβ w hw
    exact (hσ β hβ.2 w hw).1
  have hσcont' : ContinuousOn (fun p : ℂ × ℂ => σ p.1 p.2) (Λ ×ˢ hd.Bu) := by
    rw [hΛdef]
    exact hσcont
  obtain ⟨K, hKc, hKBu, hKchain⟩ := chain_in_compact (Ω := hd.Bu) (Λ := Λ) (K₁ := K₀)
      (σ := σ) (W₁ := fun _ => K₀) (J := Jc - 1) hΛc hK₀c hK₀Bu hσcont' hmapσ
      (fun β _ => subset_rfl)
  refine ⟨ρ₁, K, Jc, σ, H, hρ₁, hKc, hKBu, hJcpos,
    (fun β hβ0 hβ1 hβim hav => hσdiff β hav),
    hσcont,
    (fun β hβ0 hβ1 hβim hav w hw => ⟨(hσ β hav w hw).1, by
      have h := (hσ β hav w hw).2.1; rw [h]; ring, (hσ β hav w hw).2.2⟩),
    (fun β hβ0 hβ1 hβim hav =>
      ⟨hHdiff β hav, hHmem β hav, hH0 β hav, hHder β hav⟩), ?_⟩
  intro ρ hρ hρρ₁ β hβ0 hβ1 hβim hav
  obtain ⟨W, hW0, hWoc, hWchain, hWsub, hWbdd⟩ := hhead ρ hρ hρρ₁ β hβ0 hβ1 hβim hav
  have hW0o : IsOpen (W 0) := (hWoc 0 (Nat.zero_le J₁)).1
  have hW0c : IsConnected (W 0) := (hWoc 0 (Nat.zero_le J₁)).2
  have hW1o : IsOpen (W 1) := (hWoc 1 hJ₁).1
  have hW1c : IsConnected (W 1) := (hWoc 1 hJ₁).2
  have hW1K₀ : W 1 ⊆ K₀ := hWsub 1 le_rfl hJ₁
  have hW1sub : W 1 ⊆ hd.Bu := fun z hz => hK₀Bu (hW1K₀ hz)
  have hWimg : (fun w => d.E w - β) '' W 1 = W 0 := by
    have h := (hWchain 0 hJ₁).2
    simpa using h
  have hWinj : Set.InjOn (fun w => d.E w - β) (W 1) := by
    have h := (hWchain 0 hJ₁).1
    simpa using h
  obtain ⟨hoc, -, hchain⟩ := secChain_spec d hd (hσdiff β hav)
      (fun w hw => (hσ β hav w hw).1)
      (fun w hw => by have h := (hσ β hav w hw).2.1; rw [h]; ring)
      hW0o hW0c hW1sub hW1o hW1c hWimg hWinj
  have hβΛ : β ∈ Λ := by rw [hΛdef]; exact ⟨⟨hβ0, hβ1, hβim⟩, hav⟩
  have hKbound : ∀ j, j ≤ Jc - 1 → (σ β)^[j] '' K₀ ⊆ K := fun j hj => hKchain β hβΛ j hj
  refine ⟨secChain (σ β) (W 0) (W 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [secChain_zero]; exact hW0
  · intro j _; exact hoc j
  · intro j _; exact hchain j
  · intro j hj1 hjJ
    rw [secChain_eq_iterate (σ β) (W 0) (W 1) hj1]
    exact subset_trans (Set.image_mono hW1K₀) (hKbound (j - 1) (by omega))
  · intro j hj1 hjJ
    rw [secChain_eq_iterate (σ β) (W 0) (W 1) hj1,
      secChain_eq_iterate (σ β) (W 0) (W 1) (j := 1) le_rfl]
    simp
  · intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, secChain_zero]; exact hWbdd 0 (Nat.zero_le J₁)
    · have hjeq := secChain_eq_iterate (σ β) (W 0) (W 1) hjpos
      rw [hjeq]
      exact hKc.isBounded.subset
        (subset_trans (Set.image_mono hW1K₀) (hKbound (j - 1) (by omega)))
  · intro w hw
    have hjeq := secChain_eq_iterate (σ β) (W 0) (W 1) (j := Jc) hJcpos
    rw [hjeq] at hw
    obtain ⟨w₁, hw₁, rfl⟩ := hw
    have hπrel := piExp_iterate_section (S := hd.Bu) (Hσ := H β) (σ := σ β)
      (fun w hw => (hσ β hav w hw).2.2) (fun w hw => (hσ β hav w hw).1)
      (Jc - 1) (w := w₁) (hW1sub hw₁)
    have hbound := hescJ β hβ0 hβ1 hβim hav w₁ (hW1K₀ hw₁)
    rw [← hπrel] at hbound
    exact im_gt_of_norm_piExp_lt hbound



end

end Work.L62
